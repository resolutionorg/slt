/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.Comparison
import SLT.VolumeScaling.Invariance
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Peeling product factors

Two lemmas for peeling a factor off a product loss:

* `HasLLCExponentsOn.drop_indep_factor_iff` — a function independent of a factor has the same
  exponents with the factor dropped, on product sets with positive finite factor measure (exact
  sublevel identity; the measure multiplies by a constant).
* the two `d`-dimensional add-square lemmas (`HasLLCExponentsOn.add_sqSum`,
  `HasLLCExponentsOn.of_add_sqSum`) — for `f ≥ 0` on `K` and a cube `[-R, R]^d` of `d ≥ 1`
  fresh coordinates with `R > 0`, adding `‖u‖²` shifts `λ` by `d/2` and preserves `θ`, in both
  directions, via the sublevel sandwich between product rectangles; this is the `d`-coordinate
  form of `AddVariables`.

Not used elsewhere in this library.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β} [SFinite ν]
  {K : Set α} {Lset : Set β} {f : α → ℝ}

/-- The sublevel volume of a first-factor function on a product set is
the first-factor sublevel volume times the second factor's measure. -/
theorem sublevelVol_indep_factor (ε : ℝ) :
    sublevelVol (μ.prod ν) (K ×ˢ Lset) (fun p => f p.1) ε
      = (ν Lset).toReal * sublevelVol μ K f ε := by
  unfold sublevelVol
  have hset : (K ×ˢ Lset) ∩ {p : α × β | f p.1 ≤ ε}
      = (K ∩ {x | f x ≤ ε}) ×ˢ Lset := by
    ext ⟨x, y⟩
    simp only [Set.mem_inter_iff, Set.mem_prod, Set.mem_ofPred_eq]
    tauto
  rw [hset, Measure.prod_prod, ENNReal.toReal_mul, mul_comm]

/-- **Dropping an independent factor** preserves the exponents, both
directions, when the factor has positive finite measure. -/
theorem HasLLCExponentsOn.drop_indep_factor_iff {lam theta : ℝ}
    (hL0 : ν Lset ≠ 0) (hLtop : ν Lset ≠ ⊤) :
    HasLLCExponentsOn (μ.prod ν) (K ×ˢ Lset) (fun p => f p.1) lam theta
      ↔ HasLLCExponentsOn μ K f lam theta := by
  have hpos : 0 < (ν Lset).toReal :=
    ENNReal.toReal_pos hL0 hLtop
  have hfun : (sublevelVol (μ.prod ν) (K ×ˢ Lset) (fun p => f p.1))
      = fun ε => (ν Lset).toReal * sublevelVol μ K f ε := by
    funext ε
    exact sublevelVol_indep_factor ε
  unfold HasLLCExponentsOn
  rw [hfun]
  constructor
  · intro h
    have h2 := (Asymptotics.isTheta_const_mul_left hpos.ne'
      (l := 𝓝[>] (0 : ℝ)) (f := sublevelVol μ K f)
      (g := llcScale lam theta)).mp ?_
    · exact h2
    · exact h
  · intro h
    exact (Asymptotics.isTheta_const_mul_left hpos.ne'
      (l := 𝓝[>] (0 : ℝ))).mpr h

section CubeVolume

variable {ι : Type*} [Fintype ι]

/-- Exponent-shift factorization of the model scale. -/
theorem llcScale_add_left {lam c theta ε : ℝ} (hε : 0 < ε) :
    llcScale (lam + c) theta ε = ε ^ c * llcScale lam theta ε := by
  unfold llcScale
  rw [Real.rpow_add hε]
  ring

/-- The volume of the symmetric `ρ`-cube is `(2ρ)^d`. -/
private theorem volume_symmCube {ρ : ℝ} (hρ : 0 ≤ ρ) :
    volume (Set.pi Set.univ fun _ : ι => Icc (-ρ) ρ)
      = ENNReal.ofReal ((2 * ρ) ^ Fintype.card ι) := by
  rw [volume_pi_pi, Finset.prod_const]
  have h1 : volume (Icc (-ρ) ρ) = ENNReal.ofReal (2 * ρ) := by
    rw [Real.volume_Icc]
    congr 1
    ring
  rw [h1, ← ENNReal.ofReal_pow (by positivity), Finset.card_univ]

/-- The `√(s/d)`-cube sits inside the sum-of-squares sublevel set. -/
private theorem innerCube_subset_sqSum [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    Set.pi Set.univ (fun _ : ι =>
        Icc (-Real.sqrt (s / Fintype.card ι)) (Real.sqrt (s / Fintype.card ι)))
      ⊆ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s} := by
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact_mod_cast Fintype.card_pos
  intro u hu
  have hbound : ∀ i, u i ^ 2 ≤ s / d := by
    intro i
    have h1 := hu i (Set.mem_univ i)
    rw [Set.mem_Icc, ← abs_le] at h1
    have h2 : |u i| ^ 2 ≤ Real.sqrt (s / d) ^ 2 := by
      have h3 : (0 : ℝ) ≤ Real.sqrt (s / d) := Real.sqrt_nonneg _
      nlinarith [abs_nonneg (u i)]
    rwa [sq_abs, Real.sq_sqrt (by positivity)] at h2
  change ∑ i, u i ^ 2 ≤ s
  calc ∑ i, u i ^ 2 ≤ ∑ _i : ι, s / d :=
        Finset.sum_le_sum fun i _ => hbound i
    _ = d * (s / d) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hd]
    _ = s := by
        field_simp

/-- Upper cube bound: the sum-of-squares sublevel set sits inside the
`√s`-cube. -/
theorem volume_sqSum_le_le {s : ℝ} (_hs : 0 ≤ s) :
    volume {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s}
      ≤ ENNReal.ofReal ((2 * Real.sqrt s) ^ Fintype.card ι) := by
  have hsub : {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s}
      ⊆ Set.pi Set.univ fun _ => Icc (-Real.sqrt s) (Real.sqrt s) := by
    intro u hu i _
    have h1 : u i ^ 2 ≤ s := by
      refine le_trans ?_ hu
      exact Finset.single_le_sum (fun j _ => sq_nonneg (u j))
        (Finset.mem_univ i)
    rw [Set.mem_Icc, ← abs_le]
    have := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq_eq_abs] at this
  refine le_trans (measure_mono hsub) ?_
  exact (volume_symmCube (Real.sqrt_nonneg s)).le

/-- Lower cube bound: the `√(s/d)`-cube sits inside the sum-of-squares
sublevel set. -/
theorem le_volume_sqSum_le [Nonempty ι] {s : ℝ} (hs : 0 ≤ s) :
    ENNReal.ofReal ((2 * Real.sqrt (s / Fintype.card ι)) ^ Fintype.card ι)
      ≤ volume {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s} := by
  refine le_trans ?_ (measure_mono (innerCube_subset_sqSum hs))
  exact (volume_symmCube (Real.sqrt_nonneg _)).ge

end CubeVolume

section AddSq

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α}
  {f : α → ℝ} {ι : Type*} [Fintype ι]

/-- The product-rectangle sandwich for the added sum of squares. -/
theorem sublevelVol_add_sqSum_sandwich {R : ℝ}
    (hf : ∀ x ∈ K, 0 ≤ f x) (t : ℝ)
    (hfin : μ (K ∩ {x | f x ≤ t}) ≠ ⊤) :
    sublevelVol μ K f (t / 2)
        * (volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
            ∩ {u | ∑ i, u i ^ 2 ≤ t / 2})).toReal
      ≤ sublevelVol (μ.prod volume)
          (K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
          (fun p => f p.1 + ∑ i, p.2 i ^ 2) t
    ∧ sublevelVol (μ.prod volume)
          (K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
          (fun p => f p.1 + ∑ i, p.2 i ^ 2) t
      ≤ sublevelVol μ K f t
        * (volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
            ∩ {u | ∑ i, u i ^ 2 ≤ t})).toReal := by
  set Q := Set.pi Set.univ fun _ : ι => Icc (-R) R with hQ
  have hlowset : (K ∩ {x | f x ≤ t / 2}) ×ˢ (Q ∩ {u | ∑ i, u i ^ 2 ≤ t / 2})
      ⊆ (K ×ˢ Q) ∩ {p : α × (ι → ℝ) | f p.1 + ∑ i, p.2 i ^ 2 ≤ t} := by
    rintro ⟨x, u⟩ ⟨⟨hxK, hxf⟩, huQ, huS⟩
    refine ⟨⟨hxK, huQ⟩, ?_⟩
    simp only [Set.mem_ofPred_eq] at hxf huS ⊢
    linarith
  have hupset : (K ×ˢ Q) ∩ {p : α × (ι → ℝ) | f p.1 + ∑ i, p.2 i ^ 2 ≤ t}
      ⊆ (K ∩ {x | f x ≤ t}) ×ˢ (Q ∩ {u | ∑ i, u i ^ 2 ≤ t}) := by
    rintro ⟨x, u⟩ ⟨⟨hxK, huQ⟩, hsum⟩
    simp only [Set.mem_ofPred_eq] at hsum
    have hsq : 0 ≤ ∑ i, u i ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg (u i)
    have hfx := hf x hxK
    exact ⟨⟨hxK, by simp only [Set.mem_ofPred_eq]; linarith⟩,
      huQ, by simp only [Set.mem_ofPred_eq]; linarith⟩
  have hQtop : volume Q ≠ ⊤ := by
    rw [hQ, volume_pi_pi]
    simp only [Real.volume_Icc]
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  have hQfin : ∀ s : ℝ, volume (Q ∩ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s}) ≠ ⊤ :=
    fun s => ne_top_of_le_ne_top hQtop (measure_mono Set.inter_subset_left)
  constructor
  · unfold sublevelVol
    rw [← ENNReal.toReal_mul, ← Measure.prod_prod]
    refine ENNReal.toReal_mono ?_ (measure_mono hlowset)
    intro htop
    exact absurd (top_le_iff.mp (htop ▸ measure_mono hupset))
      (by
        rw [Measure.prod_prod]
        exact ENNReal.mul_ne_top hfin (hQfin t))
  · unfold sublevelVol
    rw [← ENNReal.toReal_mul, ← Measure.prod_prod]
    refine ENNReal.toReal_mono ?_ (measure_mono hupset)
    rw [Measure.prod_prod]
    exact ENNReal.mul_ne_top hfin (hQfin t)

end AddSq

section CubeBounds

variable {ι : Type*} [Fintype ι]

/-- Upper `w`-bound: the cube-restricted sum-of-squares volume is at most
`2^d s^{d/2}`. -/
theorem cubeVol_le {R s : ℝ} (hs : 0 ≤ s) :
    (volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
        ∩ {u | ∑ i, u i ^ 2 ≤ s})).toReal
      ≤ (2 * Real.sqrt s) ^ Fintype.card ι := by
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  refine le_trans (measure_mono Set.inter_subset_right) ?_
  exact volume_sqSum_le_le hs

/-- Lower `w`-bound: for `√(s/d) ≤ R`, the cube-restricted volume is at
least `(2√(s/d))^d`. -/
theorem le_cubeVol [Nonempty ι] {R s : ℝ} (hs : 0 ≤ s)
    (hsR : Real.sqrt (s / Fintype.card ι) ≤ R) :
    (2 * Real.sqrt (s / Fintype.card ι)) ^ Fintype.card ι
      ≤ (volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
          ∩ {u | ∑ i, u i ^ 2 ≤ s})).toReal := by
  have hsubQ : Set.pi Set.univ
      (fun _ : ι => Icc (-Real.sqrt (s / Fintype.card ι))
        (Real.sqrt (s / Fintype.card ι)))
      ⊆ Set.pi Set.univ fun _ : ι => Icc (-R) R := by
    intro u hu i _
    have h1 := hu i (Set.mem_univ i)
    rw [Set.mem_Icc] at h1 ⊢
    constructor
    · linarith [h1.1]
    · linarith [h1.2]
  have hmono := measure_mono (μ := (volume : Measure (ι → ℝ)))
    (Set.subset_inter hsubQ (innerCube_subset_sqSum hs))
  rw [volume_symmCube (Real.sqrt_nonneg _)] at hmono
  have hfin : volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
      ∩ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)
    rw [volume_pi_pi]
    simp only [Real.volume_Icc]
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top
  have h2 := ENNReal.toReal_mono hfin hmono
  rwa [ENNReal.toReal_ofReal (by positivity)] at h2

end CubeBounds

section AddSqTheta

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α}
  {f : α → ℝ} {ι : Type*} [Fintype ι] [Nonempty ι]

omit [Nonempty ι] in
/-- `(2√s)^d = 2^d · s^(d/2)` (real powers). -/
theorem two_sqrt_pow {s : ℝ} (hs : 0 ≤ s) :
    (2 * Real.sqrt s) ^ Fintype.card ι
      = 2 ^ Fintype.card ι * s ^ ((Fintype.card ι : ℝ) / 2) := by
  rw [mul_pow]
  congr 1
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (s ^ ((1 : ℝ) / 2)),
    ← Real.rpow_mul hs]
  congr 1
  ring

/-- **Forward peel**: for `f ≥ 0` on `K`, adding `‖u‖²` on a cube `[-R, R]^d` (`R > 0`) of
`d ≥ 1` fresh coordinates shifts `λ` by `d/2` and preserves `θ`. -/
theorem HasLLCExponentsOn.add_sqSum {lam theta R : ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ K, 0 ≤ f x)
    (h : HasLLCExponentsOn μ K f lam theta) :
    HasLLCExponentsOn (μ.prod volume)
      (K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
      (fun p => f p.1 + ∑ i, p.2 i ^ 2)
      (lam + (Fintype.card ι : ℝ) / 2) theta := by
  classical
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact_mod_cast Fintype.card_pos
  obtain ⟨c₁, hc₁, c₂, hc₂, hb⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp h
  have hfin : ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (K ∩ {x | f x ≤ t}) ≠ ⊤ := by
    filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with t hbt ht
    intro htop
    have h0 : sublevelVol μ K f t = 0 := by
      unfold sublevelVol
      rw [htop, ENNReal.toReal_top]
    have h1 := hbt.1
    rw [h0] at h1
    have h2 : 0 < c₁ * llcScale lam theta t :=
      mul_pos hc₁ (llcScale_pos (lam := lam) (theta := theta) ht)
    linarith
  set w : ℝ → ℝ := fun s =>
    (volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
      ∩ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s})).toReal with hw
  set VF : ℝ → ℝ := sublevelVol (μ.prod volume)
    (K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
    (fun p => f p.1 + ∑ i, p.2 i ^ 2) with hVF
  have hwnonneg : ∀ s, 0 ≤ w s := fun s => ENNReal.toReal_nonneg
  have hhalf2 : Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    have hh := tendsto_const_mul_nhdsGT_zero
      (show (0 : ℝ) < 1/2 by norm_num)
    have heq : (fun t : ℝ => (1 : ℝ)/2 * t) = fun t : ℝ => t / 2 := by
      funext t
      ring
    rwa [heq] at hh
  -- the scale factorization, as an eventual equality
  have hsplit : (fun t : ℝ => llcScale lam theta t * t ^ (d / 2))
      =ᶠ[𝓝[>] (0 : ℝ)] llcScale (lam + d / 2) theta := by
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [llcScale_add_left ht]
    ring
  constructor
  · -- VF =O scale(λ) · t^{d/2}
    have h1 : VF =O[𝓝[>] (0 : ℝ)]
        fun t => sublevelVol μ K f t * t ^ (d / 2) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨2 ^ Fintype.card ι, ?_⟩
      filter_upwards [hfin, self_mem_nhdsWithin] with t hfint (ht : 0 < t)
      rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
        Real.norm_of_nonneg (mul_nonneg (sublevelVol_nonneg _ _ _ _)
          (by positivity))]
      refine le_trans (sublevelVol_add_sqSum_sandwich hf t hfint).2 ?_
      have hcb : w t ≤ 2 ^ Fintype.card ι * t ^ (d / 2) := by
        rw [hw]
        refine le_trans (cubeVol_le ht.le) ?_
        rw [two_sqrt_pow ht.le]
      calc sublevelVol μ K f t * w t
          ≤ sublevelVol μ K f t * (2 ^ Fintype.card ι * t ^ (d / 2)) :=
            mul_le_mul_of_nonneg_left hcb (sublevelVol_nonneg _ _ _ _)
        _ = 2 ^ Fintype.card ι * (sublevelVol μ K f t * t ^ (d / 2)) := by
            ring
    have h2 : (fun t => sublevelVol μ K f t * t ^ (d / 2))
        =O[𝓝[>] (0 : ℝ)] fun t => llcScale lam theta t * t ^ (d / 2) :=
      h.1.mul (Asymptotics.isBigO_refl _ _)
    exact (h1.trans h2).congr' Filter.EventuallyEq.rfl hsplit
  · -- scale(λ+d/2) =O VF
    -- chain: scale(λ+d/2) =ᶠ scale(λ)·t^{d/2} =O scale(λ)(t/2)·w(t/2)
    --        =O V_f(t/2)·w(t/2) =O VF
    have h3 : (fun t : ℝ => llcScale lam theta t) =O[𝓝[>] (0 : ℝ)]
        fun t => llcScale lam theta (t / 2) := by
      exact (isTheta_llcScale_comp_div (lam := lam) (theta := theta)
        (c := (2 : ℝ)) two_pos).symm.1
    have h4 : (fun t : ℝ => t ^ (d / 2)) =O[𝓝[>] (0 : ℝ)]
        fun t => w (t / 2) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨(2 * d) ^ (d / 2) / 2 ^ Fintype.card ι, ?_⟩
      have hcap : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 2 * d * R ^ 2 := by
        refine eventually_nhdsWithin_of_eventually_nhds ?_
        exact eventually_le_nhds (by positivity)
      filter_upwards [self_mem_nhdsWithin, hcap] with t (ht : 0 < t) hcapt
      have hsR : Real.sqrt (t / 2 / d) ≤ R := by
        rw [show t / 2 / d = t / (2 * d) by ring]
        rw [show R = Real.sqrt (R ^ 2) from (Real.sqrt_sq hR.le).symm]
        refine Real.sqrt_le_sqrt ?_
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      have hlow := le_cubeVol (R := R) (s := t / 2) (ι := ι)
        (by positivity) (by rw [hd] at hsR; exact hsR)
      rw [two_sqrt_pow (by positivity), ← hd] at hlow
      have hpow : (t / 2 / d) ^ (d / 2)
          = t ^ (d / 2) / (2 * d) ^ (d / 2) := by
        rw [show t / 2 / d = t / (2 * d) by ring,
          Real.div_rpow ht.le (by positivity)]
      rw [hpow] at hlow
      rw [Real.norm_of_nonneg (by positivity),
        Real.norm_of_nonneg (hwnonneg _)]
      have key : t ^ (d / 2)
          = ((2 * d) ^ (d / 2) / 2 ^ Fintype.card ι)
            * (2 ^ Fintype.card ι * (t ^ (d / 2) / (2 * d) ^ (d / 2))) := by
        have hp1 : (0 : ℝ) < (2 * d) ^ (d / 2) := by positivity
        have hp2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
        field_simp
      rw [key]
      exact mul_le_mul_of_nonneg_left hlow (by positivity)
    have h5 : (fun t : ℝ => llcScale lam theta (t / 2))
        =O[𝓝[>] (0 : ℝ)] fun t => sublevelVol μ K f (t / 2) :=
      h.symm.1.comp_tendsto hhalf2
    have h6 : (fun t : ℝ => sublevelVol μ K f (t / 2) * w (t / 2))
        =O[𝓝[>] (0 : ℝ)] VF := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [hfin, self_mem_nhdsWithin] with t hfint (ht : 0 < t)
      rw [Real.norm_of_nonneg (mul_nonneg (sublevelVol_nonneg _ _ _ _)
          (hwnonneg _)), one_mul,
        Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
      exact (sublevelVol_add_sqSum_sandwich hf t hfint).1
    have hchain : llcScale (lam + d / 2) theta =O[𝓝[>] (0 : ℝ)] VF :=
      (hsplit.symm.trans_isBigO (((h3.mul h4).trans
        (h5.mul (Asymptotics.isBigO_refl _ _))).trans h6))
    exact hchain

end AddSqTheta

section AddSqConverse

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α}
  {f : α → ℝ} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Cancel a common positive power from a big-O on `𝓝[>] 0`. -/
theorem _root_.isBigO_of_mul_rpow {g h : ℝ → ℝ} {c : ℝ}
    (hg : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ g t)
    (hh : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ h t)
    (hO : (fun t => g t * t ^ c) =O[𝓝[>] (0 : ℝ)]
      fun t => h t * t ^ c) :
    g =O[𝓝[>] (0 : ℝ)] h := by
  rw [Asymptotics.isBigO_iff] at hO ⊢
  obtain ⟨C, hC⟩ := hO
  refine ⟨C, ?_⟩
  filter_upwards [hC, hg, hh, self_mem_nhdsWithin] with t hCt hgt hht
    (ht : 0 < t)
  have hpow : (0 : ℝ) < t ^ c := Real.rpow_pos_of_pos ht c
  rw [Real.norm_of_nonneg (by positivity),
    Real.norm_of_nonneg (by positivity)] at hCt
  rw [Real.norm_of_nonneg hgt, Real.norm_of_nonneg hht]
  have h2 : C * (h t * t ^ c) = (C * h t) * t ^ c := by ring
  rw [h2] at hCt
  exact le_of_mul_le_mul_right hCt hpow

/-- **Converse peel**, the converse of `HasLLCExponentsOn.add_sqSum` under the same
hypotheses: exponents of the augmented function recover those of `f`. -/
theorem HasLLCExponentsOn.of_add_sqSum {lam theta R : ℝ} (hR : 0 < R)
    (hf : ∀ x ∈ K, 0 ≤ f x)
    (h : HasLLCExponentsOn (μ.prod volume)
      (K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
      (fun p => f p.1 + ∑ i, p.2 i ^ 2)
      (lam + (Fintype.card ι : ℝ) / 2) theta) :
    HasLLCExponentsOn μ K f lam theta := by
  classical
  set d : ℝ := (Fintype.card ι : ℝ) with hd
  have hdpos : 0 < d := by
    rw [hd]
    exact_mod_cast Fintype.card_pos
  set w : ℝ → ℝ := fun s =>
    (volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
      ∩ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ s})).toReal with hw
  set VF : ℝ → ℝ := sublevelVol (μ.prod volume)
    (K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
    (fun p => f p.1 + ∑ i, p.2 i ^ 2) with hVF
  have hwnonneg : ∀ s, 0 ≤ w s := fun s => ENNReal.toReal_nonneg
  obtain ⟨c₁, hc₁, c₂, hc₂, hb⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp h
  -- the lower w-bound, eventually
  have hwlow : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      2 ^ Fintype.card ι * (t ^ (d / 2) / (2 * d) ^ (d / 2)) ≤ w (t / 2) := by
    have hcap : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ≤ 2 * d * R ^ 2 := by
      refine eventually_nhdsWithin_of_eventually_nhds ?_
      exact eventually_le_nhds (by positivity)
    filter_upwards [self_mem_nhdsWithin, hcap] with t (ht : 0 < t) hcapt
    have hsR : Real.sqrt (t / 2 / d) ≤ R := by
      rw [show t / 2 / d = t / (2 * d) by ring]
      rw [show R = Real.sqrt (R ^ 2) from (Real.sqrt_sq hR.le).symm]
      refine Real.sqrt_le_sqrt ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have hlow := le_cubeVol (R := R) (s := t / 2) (ι := ι)
      (by positivity) (by rw [hd] at hsR; exact hsR)
    rw [two_sqrt_pow (by positivity), ← hd] at hlow
    have hpow : (t / 2 / d) ^ (d / 2)
        = t ^ (d / 2) / (2 * d) ^ (d / 2) := by
      rw [show t / 2 / d = t / (2 * d) by ring,
        Real.div_rpow ht.le (by positivity)]
    rwa [hpow] at hlow
  -- eventual finiteness of the F-side measure (from its lower Θ-bound)
  have hVFfin : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      (μ.prod volume) ((K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
        ∩ {p : α × (ι → ℝ) | f p.1 + ∑ i, p.2 i ^ 2 ≤ t}) ≠ ⊤ := by
    filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with t hbt ht htop
    have h0 : VF t = 0 := by
      rw [hVF]
      unfold sublevelVol
      rw [htop, ENNReal.toReal_top]
    rw [hVF] at h0
    have h1 := hbt.1
    rw [h0] at h1
    have h2 : 0 < c₁ * llcScale (lam + d / 2) theta t :=
      mul_pos hc₁ (llcScale_pos (lam := lam + d / 2) (theta := theta) ht)
    linarith
  have hdouble : Tendsto (fun t : ℝ => 2 * t) (𝓝[>] (0 : ℝ))
      (𝓝[>] (0 : ℝ)) := tendsto_const_mul_nhdsGT_zero two_pos
  -- eventual finiteness of the f-side measure (lower rectangle inside S_F(2t))
  have hfin : ∀ᶠ t in 𝓝[>] (0 : ℝ), μ (K ∩ {x | f x ≤ t}) ≠ ⊤ := by
    filter_upwards [hdouble.eventually hVFfin, hdouble.eventually hwlow,
      self_mem_nhdsWithin] with t hVFt hwt (ht : 0 < t)
    intro htop
    have hsub : (K ∩ {x | f x ≤ t})
        ×ˢ ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
          ∩ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ t})
        ⊆ (K ×ˢ Set.pi Set.univ fun _ : ι => Icc (-R) R)
          ∩ {p : α × (ι → ℝ) | f p.1 + ∑ i, p.2 i ^ 2 ≤ 2 * t} := by
      rintro ⟨x, u⟩ ⟨⟨hxK, hxf⟩, huQ, huS⟩
      refine ⟨⟨hxK, huQ⟩, ?_⟩
      simp only [Set.mem_ofPred_eq] at hxf huS ⊢
      linarith
    have hwpos : 0 < w t := by
      have h4 := hwt
      rw [show 2 * t / 2 = t by ring] at h4
      refine lt_of_lt_of_le ?_ h4
      positivity
    have hmeas := measure_mono (μ := μ.prod volume) hsub
    rw [Measure.prod_prod, htop] at hmeas
    have hwne : volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
        ∩ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ t}) ≠ 0 := by
      intro h0
      have hzero : w t = 0 := by
        change (volume ((Set.pi Set.univ fun _ : ι => Icc (-R) R)
          ∩ {u : ι → ℝ | ∑ i, u i ^ 2 ≤ t})).toReal = 0
        rw [h0, ENNReal.toReal_zero]
      linarith
    rw [ENNReal.top_mul hwne] at hmeas
    exact hVFt (top_le_iff.mp hmeas)
  constructor
  · -- V_f =O scale(λ): V_f·t^{d/2} =O VF(2t) =O scale(λ+d/2)(2t)
    -- =Θ scale(λ+d/2) =ᶠ scale(λ)·t^{d/2}, cancel
    refine isBigO_of_mul_rpow (c := d / 2)
      (Filter.Eventually.of_forall fun t => sublevelVol_nonneg _ _ _ _)
      (by
        filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with t ht
        exact (llcScale_pos (lam := lam) (theta := theta) ht).le) ?_
    have h1 : (fun t => sublevelVol μ K f t * t ^ (d / 2))
        =O[𝓝[>] (0 : ℝ)] fun t => VF (2 * t) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨(2 * d) ^ (d / 2) / 2 ^ Fintype.card ι, ?_⟩
      filter_upwards [hdouble.eventually hfin, hdouble.eventually hwlow,
        self_mem_nhdsWithin, hfin] with t hfin2t hw2t (ht : 0 < t) hfint
      have h2t : 2 * t / 2 = t := by ring
      rw [h2t] at hw2t
      have hw2t' : 2 ^ Fintype.card ι * (t ^ (d / 2) / (2 * d) ^ (d / 2))
          ≤ w t := by
        refine le_trans ?_ hw2t
        have hmono : t ^ (d / 2) ≤ (2 * t) ^ (d / 2) :=
          Real.rpow_le_rpow ht.le (by linarith) (by positivity)
        have hp : (0 : ℝ) < (2 * d) ^ (d / 2) := by positivity
        have hq : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
        gcongr
      have hsand := (sublevelVol_add_sqSum_sandwich (μ := μ) (ι := ι)
        (R := R) hf (2 * t) hfin2t).1
      rw [h2t] at hsand
      rw [Real.norm_of_nonneg (mul_nonneg (sublevelVol_nonneg _ _ _ _)
        (by positivity)), Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
      refine le_trans ?_ (mul_le_mul_of_nonneg_left hsand (by positivity))
      have hkey : sublevelVol μ K f t * t ^ (d / 2)
          = ((2 * d) ^ (d / 2) / 2 ^ Fintype.card ι)
            * (sublevelVol μ K f t
              * (2 ^ Fintype.card ι * (t ^ (d / 2) / (2 * d) ^ (d / 2)))) := by
        have hp1 : (0 : ℝ) < (2 * d) ^ (d / 2) := by positivity
        have hp2 : (0 : ℝ) < (2 : ℝ) ^ Fintype.card ι := by positivity
        field_simp
      rw [hkey]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hw2t' (sublevelVol_nonneg _ _ _ _)
    have h2 : (fun t : ℝ => VF (2 * t)) =O[𝓝[>] (0 : ℝ)]
        fun t => llcScale (lam + d / 2) theta (2 * t) :=
      h.1.comp_tendsto hdouble
    have h3 : (fun t : ℝ => llcScale (lam + d / 2) theta (2 * t))
        =O[𝓝[>] (0 : ℝ)] llcScale (lam + d / 2) theta := by
      have hth := isTheta_llcScale_comp_div (lam := lam + d / 2)
        (theta := theta) (c := (2 : ℝ)⁻¹) (by norm_num)
      have heq : (fun ε : ℝ => llcScale (lam + d / 2) theta (ε / 2⁻¹))
          = fun ε : ℝ => llcScale (lam + d / 2) theta (2 * ε) := by
        funext ε
        rw [div_inv_eq_mul, mul_comm]
      rw [heq] at hth
      exact hth.1
    have h4 : llcScale (lam + d / 2) theta =ᶠ[𝓝[>] (0 : ℝ)]
        fun t => llcScale lam theta t * t ^ (d / 2) := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [llcScale_add_left ht]
      ring
    exact ((h1.trans h2).trans h3).congr' Filter.EventuallyEq.rfl h4
  · -- scale(λ) =O V_f: scale(λ)·t^{d/2} =ᶠ scale(λ+d/2) =O VF =O V_f·w ≤ 2^d V_f t^{d/2}, cancel
    refine isBigO_of_mul_rpow (c := d / 2)
      (by
        filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with t ht
        exact (llcScale_pos (lam := lam) (theta := theta) ht).le)
      (Filter.Eventually.of_forall fun t => sublevelVol_nonneg _ _ _ _) ?_
    have h4 : (fun t : ℝ => llcScale lam theta t * t ^ (d / 2))
        =ᶠ[𝓝[>] (0 : ℝ)] llcScale (lam + d / 2) theta := by
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      rw [llcScale_add_left ht]
      ring
    have h5 : VF =O[𝓝[>] (0 : ℝ)]
        fun t => sublevelVol μ K f t * t ^ (d / 2) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨2 ^ Fintype.card ι, ?_⟩
      filter_upwards [hfin, self_mem_nhdsWithin] with t hfint (ht : 0 < t)
      rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
        Real.norm_of_nonneg (mul_nonneg (sublevelVol_nonneg _ _ _ _)
          (by positivity))]
      refine le_trans (sublevelVol_add_sqSum_sandwich hf t hfint).2 ?_
      have hcb : w t ≤ 2 ^ Fintype.card ι * t ^ (d / 2) := by
        rw [hw]
        refine le_trans (cubeVol_le ht.le) ?_
        rw [two_sqrt_pow ht.le]
      calc sublevelVol μ K f t * w t
          ≤ sublevelVol μ K f t * (2 ^ Fintype.card ι * t ^ (d / 2)) :=
            mul_le_mul_of_nonneg_left hcb (sublevelVol_nonneg _ _ _ _)
        _ = 2 ^ Fintype.card ι * (sublevelVol μ K f t * t ^ (d / 2)) := by
            ring
    exact h4.trans_isBigO (h.symm.1.trans h5)

end AddSqConverse

end SingularLearningTheory
