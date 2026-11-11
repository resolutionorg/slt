/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Laplace.Scale
import SLT.VolumeScaling.Basic
public import SLT.VolumeScaling.Defs
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# The Laplace representation: `∫_K e^{−s·f} dμ = s ∫_0^∞ e^{−s·ε} V(ε) dε`

The layer-cake/Tonelli representation of the Laplace integral of a
nonnegative function through its localized sublevel volumes
`V(ε) = sublevelVol μ K f ε`, plus the tail estimate.

The proof factors through a
**Laplace–Stieltjes core** for finite Borel measures `ν` on `ℝ` supported
on `[0, ∞)`:

  `∫⁻ t, ofReal (e^{−s·t}) ∂ν
     = ofReal s * ∫⁻ ε in Ioi 0, ofReal (e^{−s·ε}) * ν (Iic ε)`,

proved by writing `e^{−s·t} = s ∫_{Ioi t} e^{−s·ε} dε` for `t ≥ 0` and
swapping the two integrals (Tonelli); the closed sublevel sets of
`sublevelVol` come out directly, with no open/closed boundary bookkeeping.
The statement for `f` follows by instantiating `ν` with the pushforward of
`μ.restrict K` under a measurable nonnegative representative of `f`.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f : α → ℝ}

/-! ## Elementary integrals and `sublevelVol` plumbing -/

/-- `∫_{Ioi t} e^{−s·ε} dε = s⁻¹ e^{−s·t}`. -/
theorem _root_.integral_exp_neg_mul_Ioi {s : ℝ} (hs : 0 < s) (t : ℝ) :
    ∫ ε in Ioi t, Real.exp (-(s * ε)) = s⁻¹ * Real.exp (-(s * t)) := by
  have h := integral_comp_mul_left_Ioi (fun x => Real.exp (-x)) t hs
  rw [h, smul_eq_mul, integral_exp_neg_Ioi]

/-- Sublevel volumes are monotone in the level (under finite `K`-mass). -/
private theorem sublevelVol_mono (hfin : μ K ≠ ⊤) : Monotone (sublevelVol μ K f) :=
  fun _ _ hab =>
    ENNReal.toReal_mono (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))
      (measure_mono (inter_subset_inter Subset.rfl fun _ hx => le_trans hx hab))

/-- Sublevel volumes are bounded by the `K`-mass. -/
theorem sublevelVol_le (hfin : μ K ≠ ⊤) (ε : ℝ) :
    sublevelVol μ K f ε ≤ (μ K).toReal :=
  ENNReal.toReal_mono hfin (measure_mono inter_subset_left)

theorem measurable_sublevelVol (hfin : μ K ≠ ⊤) :
    Measurable (sublevelVol μ K f) :=
  (sublevelVol_mono hfin).measurable

/-- The Laplace kernel against the sublevel volume is integrable on every
right ray. -/
theorem integrableOn_exp_mul_sublevelVol (hfin : μ K ≠ ⊤) {s : ℝ}
    (hs : 0 < s) (a : ℝ) :
    IntegrableOn (fun ε => Real.exp (-(s * ε)) * sublevelVol μ K f ε)
      (Ioi a) := by
  refine Integrable.mono' ((exp_neg_integrableOn_Ioi a hs).mul_const
    (μ K).toReal) ?_ ?_
  · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id').neg).measurable.mul
      (measurable_sublevelVol hfin)).aestronglyMeasurable
  · filter_upwards with ε
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.exp_nonneg _) (sublevelVol_nonneg μ K f ε))]
    calc Real.exp (-(s * ε)) * sublevelVol μ K f ε
        ≤ Real.exp (-(s * ε)) * (μ K).toReal :=
          mul_le_mul_of_nonneg_left (sublevelVol_le hfin ε) (Real.exp_nonneg _)
      _ = Real.exp (-s * ε) * (μ K).toReal := by rw [neg_mul]

/-! ## The Laplace–Stieltjes core -/

/-- The inner layer-cake identity: for `t ≥ 0`, integrating the kernel
`s·e^{−s·ε}` over the levels `ε > 0` above `t` recovers `e^{−s·t}`. -/
private theorem lintegral_exp_kernel_inner {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t) :
    ∫⁻ ε in Ioi (0 : ℝ),
        ENNReal.ofReal (s * Real.exp (-(s * ε)))
          * (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε
      = ENNReal.ofReal (Real.exp (-(s * t))) := by
  have h1 : ∀ ε : ℝ,
      ENNReal.ofReal (s * Real.exp (-(s * ε)))
          * (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε
        = (Ici t).indicator
            (fun ε => ENNReal.ofReal (s * Real.exp (-(s * ε)))) ε := by
    intro ε
    by_cases hε : ε ∈ Ici t <;> simp [hε]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici]
  have hset : (Ici t ∩ Ioi 0 : Set ℝ) =ᵐ[volume] (Ioi t : Set ℝ) := by
    have h2 : (Ici t ∩ Ioi 0 : Set ℝ) =ᵐ[volume] (Ioi t ∩ Ioi 0 : Set ℝ) :=
      MeasureTheory.ae_eq_set_inter (Ioi_ae_eq_Ici (a := t)).symm
        Filter.EventuallyEq.rfl
    rwa [Ioi_inter_Ioi, sup_eq_left.mpr ht] at h2
  have hint : IntegrableOn (fun ε => s * Real.exp (-(s * ε))) (Ioi t) := by
    simpa [IntegrableOn, neg_mul] using (exp_neg_integrableOn_Ioi t hs).const_mul s
  rw [setLIntegral_congr hset,
    ← ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun ε => by positivity),
    integral_const_mul, integral_exp_neg_mul_Ioi hs,
    ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]

/-- **The Laplace–Stieltjes core.** For a finite Borel measure `ν` on `ℝ`
supported on `[0, ∞)` and `s > 0`:

  `∫⁻ t, ofReal (e^{−s·t}) ∂ν
     = ofReal s * ∫⁻ ε in Ioi 0, ofReal (e^{−s·ε}) * ν (Iic ε)`. -/
private theorem lintegral_exp_neg_mul_eq_stieltjes (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hsupp : ν (Iio 0) = 0) {s : ℝ} (hs : 0 < s) :
    ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂ν
      = ENNReal.ofReal s
          * ∫⁻ ε in Ioi (0 : ℝ),
              ENNReal.ofReal (Real.exp (-(s * ε))) * ν (Iic ε) := by
  have hae : ∀ᵐ t ∂ν, 0 ≤ t := by
    rw [ae_iff]
    refine measure_mono_null (fun t ht => ?_) hsupp
    exact mem_Iio.mpr (not_le.mp ht)
  have hswap :
      ∫⁻ t, (∫⁻ ε in Ioi (0 : ℝ),
          ENNReal.ofReal (s * Real.exp (-(s * ε)))
            * (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε) ∂ν
        = ∫⁻ ε in Ioi (0 : ℝ),
            (∫⁻ t, ENNReal.ofReal (s * Real.exp (-(s * ε)))
              * (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε ∂ν) := by
    refine lintegral_lintegral_swap ?_
    have hker : Measurable fun p : ℝ × ℝ =>
        ENNReal.ofReal (s * Real.exp (-(s * p.2))) :=
      ((measurable_snd.const_mul s).neg.exp.const_mul s).ennreal_ofReal
    have hind : Measurable fun p : ℝ × ℝ =>
        ({q : ℝ × ℝ | q.1 ≤ q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)) p :=
      measurable_one.indicator (measurableSet_le measurable_fst measurable_snd)
    have heq : (Function.uncurry fun t ε =>
        ENNReal.ofReal (s * Real.exp (-(s * ε)))
          * (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε)
        = fun p : ℝ × ℝ => ENNReal.ofReal (s * Real.exp (-(s * p.2)))
            * ({q : ℝ × ℝ | q.1 ≤ q.2}.indicator (1 : ℝ × ℝ → ℝ≥0∞)) p := by
      funext p
      by_cases hp : p.1 ≤ p.2 <;>
        simp [Function.uncurry, hp]
    rw [heq]
    exact (hker.mul hind).aemeasurable
  calc ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂ν
      = ∫⁻ t, (∫⁻ ε in Ioi (0 : ℝ),
          ENNReal.ofReal (s * Real.exp (-(s * ε)))
            * (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε) ∂ν := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with t ht
        exact (lintegral_exp_kernel_inner hs ht).symm
    _ = ∫⁻ ε in Ioi (0 : ℝ),
          (∫⁻ t, ENNReal.ofReal (s * Real.exp (-(s * ε)))
            * (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε ∂ν) := hswap
    _ = ∫⁻ ε in Ioi (0 : ℝ),
          ENNReal.ofReal (s * Real.exp (-(s * ε))) * ν (Iic ε) := by
        refine lintegral_congr fun ε => ?_
        have hflip : ∀ t : ℝ, (Ici t).indicator (1 : ℝ → ℝ≥0∞) ε
            = (Iic ε).indicator (1 : ℝ → ℝ≥0∞) t := by
          intro t
          by_cases h : t ≤ ε <;> simp [h]
        simp_rw [hflip]
        rw [lintegral_const_mul _ (measurable_one.indicator measurableSet_Iic),
          lintegral_indicator_one measurableSet_Iic]
    _ = ENNReal.ofReal s
          * ∫⁻ ε in Ioi (0 : ℝ),
              ENNReal.ofReal (Real.exp (-(s * ε))) * ν (Iic ε) := by
        have hVmeas : Measurable fun ε : ℝ => ν (Iic ε) :=
          Monotone.measurable fun a b hab => measure_mono (Iic_subset_Iic.mpr hab)
        have hmeas : Measurable fun ε : ℝ =>
            ENNReal.ofReal (Real.exp (-(s * ε))) * ν (Iic ε) := by
          exact (((measurable_id.const_mul s).neg.exp).ennreal_ofReal).mul hVmeas
        rw [← lintegral_const_mul _ hmeas]
        refine lintegral_congr fun ε => ?_
        rw [ENNReal.ofReal_mul hs.le, mul_assoc]

/-! ## Pushforward instantiation to `sublevelVol` -/

/-- The pushforward of `μ.restrict K` under `g` reads the closed sublevel
masses: `(map g (μ.restrict K)) (Iic ε) = μ (K ∩ {g ≤ ε})`. -/
private theorem map_restrict_Iic {g : α → ℝ} (hg : Measurable g) (ε : ℝ) :
    (μ.restrict K).map g (Iic ε) = μ (K ∩ {x | g x ≤ ε}) := by
  rw [Measure.map_apply hg measurableSet_Iic,
    Measure.restrict_apply (hg measurableSet_Iic), Set.inter_comm]
  rfl

/-- The lintegral form of the representation, for measurable nonnegative
`g`. -/
private theorem lintegral_exp_neg_mul_eq_sublevel {g : α → ℝ} (hg : Measurable g)
    (hg0 : ∀ x, 0 ≤ g x) (hfin : μ K ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x in K, ENNReal.ofReal (Real.exp (-(s * g x))) ∂μ
      = ENNReal.ofReal s
          * ∫⁻ ε in Ioi (0 : ℝ),
              ENNReal.ofReal (Real.exp (-(s * ε))) * μ (K ∩ {x | g x ≤ ε}) := by
  have : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rwa [Measure.restrict_apply_univ, lt_top_iff_ne_top]⟩
  have hsupp : (μ.restrict K).map g (Iio 0) = 0 := by
    rw [Measure.map_apply hg measurableSet_Iio]
    have : g ⁻¹' Iio 0 = ∅ :=
      eq_empty_iff_forall_notMem.mpr fun x hx => absurd (hg0 x) (not_le.mpr hx)
    rw [this]
    exact measure_empty
  calc ∫⁻ x in K, ENNReal.ofReal (Real.exp (-(s * g x))) ∂μ
      = ∫⁻ t, ENNReal.ofReal (Real.exp (-(s * t))) ∂((μ.restrict K).map g) :=
        (lintegral_map ((measurable_id.const_mul s).neg.exp.ennreal_ofReal) hg).symm
    _ = ENNReal.ofReal s
          * ∫⁻ ε in Ioi (0 : ℝ),
              ENNReal.ofReal (Real.exp (-(s * ε)))
                * (μ.restrict K).map g (Iic ε) :=
        lintegral_exp_neg_mul_eq_stieltjes _ hsupp hs
    _ = ENNReal.ofReal s
          * ∫⁻ ε in Ioi (0 : ℝ),
              ENNReal.ofReal (Real.exp (-(s * ε))) * μ (K ∩ {x | g x ≤ ε}) := by
        congr 1
        exact lintegral_congr fun ε => by rw [map_restrict_Iic hg]

/-! ## The a.e. bridge and the real-valued representation -/

/-- `sublevelVol` only depends on the `μ.restrict K`-a.e. class of the
loss. -/
private theorem sublevelVol_congr_ae {g : α → ℝ} (h : f =ᵐ[μ.restrict K] g) (ε : ℝ) :
    sublevelVol μ K f ε = sublevelVol μ K g ε := by
  have hnull : μ (toMeasurable (μ.restrict K) {x | f x ≠ g x} ∩ K) = 0 := by
    rw [← Measure.restrict_apply (measurableSet_toMeasurable _ _),
      measure_toMeasurable]
    exact h
  unfold sublevelVol
  congr 1
  refine measure_congr (MeasureTheory.ae_eq_set.mpr ⟨?_, ?_⟩)
  · refine measure_mono_null (fun x hx => ?_) hnull
    rcases hx with ⟨⟨hxK, hxf⟩, hnot⟩
    have hne : f x ≠ g x := fun heq =>
      hnot ⟨hxK, by rwa [mem_ofPred_eq, ← heq]⟩
    exact ⟨subset_toMeasurable _ _ hne, hxK⟩
  · refine measure_mono_null (fun x hx => ?_) hnull
    rcases hx with ⟨⟨hxK, hxg⟩, hnot⟩
    have hne : f x ≠ g x := fun heq =>
      hnot ⟨hxK, by rwa [mem_ofPred_eq, heq]⟩
    exact ⟨subset_toMeasurable _ _ hne, hxK⟩

/-- **The Laplace representation** (real form). For `f`
a.e.-measurable and a.e.-nonnegative on `K` with `μ K ≠ ∞` and `s > 0`:

  `∫_K e^{−s·f} dμ = s ∫_{Ioi 0} e^{−s·ε} V(ε) dε`,

with `V = sublevelVol μ K f` the closed localized sublevel volume. -/
theorem setIntegral_exp_neg_mul_eq (hf : AEMeasurable f (μ.restrict K))
    (hf0 : 0 ≤ᵐ[μ.restrict K] f) (hfin : μ K ≠ ⊤) {s : ℝ} (hs : 0 < s) :
    ∫ x in K, Real.exp (-(s * f x)) ∂μ
      = s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * sublevelVol μ K f ε := by
  set g : α → ℝ := fun x => max (hf.mk f x) 0 with hgdef
  have hg : Measurable g := hf.measurable_mk.max measurable_const
  have hg0 : ∀ x, 0 ≤ g x := fun x => le_max_right _ _
  have hfg : f =ᵐ[μ.restrict K] g := by
    filter_upwards [hf.ae_eq_mk, hf0] with x hx h0
    have h0' : (0 : ℝ) ≤ f x := h0
    change f x = max (hf.mk f x) 0
    rw [← hx]
    exact (max_eq_left h0').symm
  have hLHS : ∫ x in K, Real.exp (-(s * f x)) ∂μ
      = ∫ x in K, Real.exp (-(s * g x)) ∂μ :=
    integral_congr_ae (hfg.mono fun x hx => by simp only [hx])
  have hVcongr : (fun ε => Real.exp (-(s * ε)) * sublevelVol μ K f ε)
      = fun ε => Real.exp (-(s * ε)) * sublevelVol μ K g ε := by
    funext ε
    rw [sublevelVol_congr_ae hfg]
  rw [hLHS, hVcongr]
  -- Both sides via `toReal` of the lintegral identity.
  have hmeasL : AEStronglyMeasurable (fun x => Real.exp (-(s * g x)))
      (μ.restrict K) := by
    exact (Real.measurable_exp.comp ((hg.const_mul s).neg)).aestronglyMeasurable
  have hl : ∫ x in K, Real.exp (-(s * g x)) ∂μ
      = (∫⁻ x in K, ENNReal.ofReal (Real.exp (-(s * g x))) ∂μ).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun x => Real.exp_nonneg _) hmeasL
  have hmeasR : AEStronglyMeasurable
      (fun ε : ℝ => Real.exp (-(s * ε)) * sublevelVol μ K g ε)
      (volume.restrict (Ioi 0)) := by
    exact ((Real.measurable_exp.comp ((measurable_id.const_mul s).neg)).mul
      (measurable_sublevelVol hfin)).aestronglyMeasurable
  have hr : ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * sublevelVol μ K g ε
      = (∫⁻ ε in Ioi (0 : ℝ),
          ENNReal.ofReal (Real.exp (-(s * ε)) * sublevelVol μ K g ε)).toReal :=
    integral_eq_lintegral_of_nonneg_ae
      (Eventually.of_forall fun ε =>
        mul_nonneg (Real.exp_nonneg _) (sublevelVol_nonneg μ K g ε)) hmeasR
  rw [hl, hr]
  have hinner : ∫⁻ ε in Ioi (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(s * ε)) * sublevelVol μ K g ε)
        = ∫⁻ ε in Ioi (0 : ℝ),
            ENNReal.ofReal (Real.exp (-(s * ε))) * μ (K ∩ {x | g x ≤ ε}) := by
    refine lintegral_congr fun ε => ?_
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _)]
    congr 1
    exact ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))
  rw [hinner, lintegral_exp_neg_mul_eq_sublevel hg hg0 hfin hs,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hs.le]

/-! ## The bounded-volume tail estimate, and the head/tail split -/

theorem setIntegral_exp_mul_sublevelVol_nonneg {s : ℝ} (S : Set ℝ) :
    0 ≤ ∫ ε in S, Real.exp (-(s * ε)) * sublevelVol μ K f ε :=
  integral_nonneg fun ε =>
    mul_nonneg (Real.exp_nonneg _) (sublevelVol_nonneg μ K f ε)

/-- **Tail estimate**: the tail of the representation integral is
exponentially small, uniformly in the volume data. -/
theorem mul_setIntegral_exp_sublevelVol_tail_le (hfin : μ K ≠ ⊤)
    {s : ℝ} (hs : 0 < s) (ε₀ : ℝ) :
    s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * sublevelVol μ K f ε
      ≤ (μ K).toReal * Real.exp (-(s * ε₀)) := by
  have hmono : ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * sublevelVol μ K f ε
      ≤ ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * (μ K).toReal := by
    have hgint : IntegrableOn (fun ε => Real.exp (-(s * ε)) * (μ K).toReal)
        (Ioi ε₀) := by
      simpa [IntegrableOn, neg_mul] using
        (exp_neg_integrableOn_Ioi ε₀ hs).mul_const (μ K).toReal
    refine setIntegral_mono_on (integrableOn_exp_mul_sublevelVol hfin hs ε₀)
      hgint measurableSet_Ioi fun ε _ => ?_
    exact mul_le_mul_of_nonneg_left (sublevelVol_le hfin ε) (Real.exp_nonneg _)
  calc s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * sublevelVol μ K f ε
      ≤ s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * (μ K).toReal :=
        mul_le_mul_of_nonneg_left hmono hs.le
    _ = (μ K).toReal * Real.exp (-(s * ε₀)) := by
        rw [integral_mul_const, integral_exp_neg_mul_Ioi hs]
        field_simp

/-- The head/tail split of the representation integral at a level
`ε₀ > 0`. -/
theorem setIntegral_exp_sublevelVol_split (hfin : μ K ≠ ⊤) {s : ℝ}
    (hs : 0 < s) {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * sublevelVol μ K f ε
      = (∫ ε in Ioc (0 : ℝ) ε₀, Real.exp (-(s * ε)) * sublevelVol μ K f ε)
        + ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * sublevelVol μ K f ε := by
  rw [← Ioc_union_Ioi_eq_Ioi hε₀.le]
  exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    ((integrableOn_exp_mul_sublevelVol hfin hs 0).mono_set Ioc_subset_Ioi_self)
    (integrableOn_exp_mul_sublevelVol hfin hs ε₀)

end SingularLearningTheory
