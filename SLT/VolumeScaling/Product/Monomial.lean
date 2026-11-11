/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# The two-dimensional product monomial: exact sublevel volume

The analytic core of the first instance with multiplicity `θ = 2` (the `L = 2` case of the
product `(∏ᵢ xᵢ)²`, `LFoldProduct`): for `δ ∈ (0, 1)`,

  `vol {(x, y) ∈ [-1,1]² : |x·y| ≤ δ} = 4δ(1 − log δ)`.

This is the first genuine slice integral of the library — the log factor cannot be produced by
rectangle bounds. The slice over `x` is the closed interval `[-m x, m x]` with half-length

  `sliceHalfLen δ x = δ / max δ |x|`,

a formulation that is junk-free at `x = 0`, needs no case split in the definition, and is
continuous — so every integrability obligation comes from continuity on a compact interval.

The volume is computed by Mathlib's `regionBetween` machinery: the closed region differs from the
open `regionBetween` by two graphs, each null; the open region's volume is `∫ 2·m`; and the
integral splits over `[-1,-δ] ∪ [-δ,δ] ∪ [δ,1]` with `integral_inv` producing the logarithm. The
file ends with the `HasLLCOn (½, 2, 2)` instance; `LFoldProduct` generalizes it to `L` factors.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory

/-- Half-length of the `y`-slice of `{|x·y| ≤ δ}` within `[-1,1]`:
`δ / max δ |x|`. Equals `1` for `|x| ≤ δ` (including `x = 0`) and `δ/|x|`
beyond; the denominator never vanishes for `δ > 0`. -/
noncomputable def sliceHalfLen (δ x : ℝ) : ℝ := δ / max δ |x|

section sliceHalfLen

variable {δ : ℝ}

theorem sliceHalfLen_pos (hδ : 0 < δ) (x : ℝ) : 0 < sliceHalfLen δ x :=
  div_pos hδ (lt_of_lt_of_le hδ (le_max_left _ _))

theorem sliceHalfLen_le_one (hδ : 0 < δ) (x : ℝ) : sliceHalfLen δ x ≤ 1 :=
  (div_le_one (lt_of_lt_of_le hδ (le_max_left _ _))).mpr (le_max_left _ _)

theorem sliceHalfLen_of_abs_le {x : ℝ} (hδ : 0 < δ) (hx : |x| ≤ δ) :
    sliceHalfLen δ x = 1 := by
  rw [sliceHalfLen, max_eq_left hx, div_self hδ.ne']

theorem sliceHalfLen_of_le_abs {x : ℝ} (hx : δ ≤ |x|) : sliceHalfLen δ x = δ / |x| := by
  rw [sliceHalfLen, max_eq_right hx]

theorem continuous_sliceHalfLen (hδ : 0 < δ) : Continuous (sliceHalfLen δ) :=
  continuous_const.div (continuous_const.max continuous_abs)
    fun _ => (lt_of_lt_of_le hδ (le_max_left _ _)).ne'

/-- The slice characterization: membership of `y` in the ambient interval
together with `|x·y| ≤ δ` is exactly `|y| ≤ m x` (for any `x`, in fact). -/
theorem abs_le_sliceHalfLen_iff {x : ℝ} (hδ : 0 < δ) (y : ℝ) :
    |y| ≤ 1 ∧ |x * y| ≤ δ ↔ |y| ≤ sliceHalfLen δ x := by
  rcases le_total |x| δ with h | h
  · rw [sliceHalfLen_of_abs_le hδ h]
    constructor
    · exact fun hy => hy.1
    · intro hy
      refine ⟨hy, ?_⟩
      calc |x * y| = |x| * |y| := abs_mul x y
        _ ≤ δ * 1 := mul_le_mul h hy (abs_nonneg y) hδ.le
        _ = δ := mul_one δ
  · have hx0 : 0 < |x| := lt_of_lt_of_le hδ h
    rw [sliceHalfLen_of_le_abs h]
    constructor
    · rintro ⟨_, hxy⟩
      rw [le_div_iff₀ hx0, mul_comm]
      rwa [abs_mul] at hxy
    · intro hy
      have hm1 : δ / |x| ≤ 1 := (div_le_one hx0).mpr h
      refine ⟨le_trans hy hm1, ?_⟩
      rw [abs_mul]
      calc |x| * |y| ≤ |x| * (δ / |x|) :=
            mul_le_mul_of_nonneg_left hy (abs_nonneg x)
        _ = δ := by field_simp

end sliceHalfLen

section ClosedRegion

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}

/-- The graph of a measurable function over a base set is null for the
product with Lebesgue measure. -/
theorem _root_.prod_volume_graph_eq_zero {h : α → ℝ} (hs : MeasurableSet s)
    (hh : Measurable h) :
    μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 = h p.1} = 0 := by
  have hmeas : MeasurableSet {p : α × ℝ | p.1 ∈ s ∧ p.2 = h p.1} := by
    have := measurableSet_region_between_cc hh hh hs
    simpa [Set.Icc_self] using this
  rw [Measure.prod_apply hmeas]
  have hzero : ∀ x : α, volume {a : ℝ | x ∈ s ∧ a = h x} = 0 := by
    intro x
    refine measure_mono_null (fun y hy => ?_) (Real.volume_singleton (a := h x))
    exact hy.2
  simp [hzero]

/-- Closed-region volume: like `volume_regionBetween_eq_integral` but with
closed vertical slices `[f x, g x]` (the two graph boundaries are null). -/
theorem _root_.volume_region_between_cc_eq_integral [SigmaFinite μ] {f g : α → ℝ}
    (f_int : IntegrableOn f s μ) (g_int : IntegrableOn g s μ)
    (hf : Measurable f) (hg : Measurable g) (hs : MeasurableSet s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}
      = ENNReal.ofReal (∫ x in s, (g - f) x ∂μ) := by
  rw [← volume_regionBetween_eq_integral f_int g_int hs hfg]
  apply le_antisymm
  · have hsub : {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}
        ⊆ regionBetween f g s
          ∪ ({p : α × ℝ | p.1 ∈ s ∧ p.2 = f p.1}
            ∪ {p : α × ℝ | p.1 ∈ s ∧ p.2 = g p.1}) := by
      rintro ⟨x, y⟩ ⟨hxs, hy1, hy2⟩
      rcases eq_or_lt_of_le hy1 with hl | hl
      · exact Or.inr (Or.inl ⟨hxs, hl.symm⟩)
      rcases eq_or_lt_of_le hy2 with hr | hr
      · exact Or.inr (Or.inr ⟨hxs, hr⟩)
      exact Or.inl ⟨hxs, hl, hr⟩
    calc μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 ∈ Icc (f p.1) (g p.1)}
        ≤ μ.prod volume (regionBetween f g s
            ∪ ({p : α × ℝ | p.1 ∈ s ∧ p.2 = f p.1}
              ∪ {p : α × ℝ | p.1 ∈ s ∧ p.2 = g p.1})) := measure_mono hsub
      _ ≤ μ.prod volume (regionBetween f g s)
            + μ.prod volume ({p : α × ℝ | p.1 ∈ s ∧ p.2 = f p.1}
              ∪ {p : α × ℝ | p.1 ∈ s ∧ p.2 = g p.1}) := measure_union_le _ _
      _ ≤ μ.prod volume (regionBetween f g s)
            + (μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 = f p.1}
              + μ.prod volume {p : α × ℝ | p.1 ∈ s ∧ p.2 = g p.1}) := by
            gcongr
            exact measure_union_le _ _
      _ = μ.prod volume (regionBetween f g s) := by
            rw [prod_volume_graph_eq_zero hs hf, prod_volume_graph_eq_zero hs hg,
              add_zero, add_zero]
  · refine measure_mono fun p hp => ?_
    exact ⟨hp.1, le_of_lt hp.2.1, le_of_lt hp.2.2⟩

end ClosedRegion

section ProductMonomial2D

/-- The exact 2D product-monomial sublevel volume: for `δ ∈ (0,1)`,
`vol {(x,y) ∈ [-1,1]² : |x·y| ≤ δ} = 4δ(1 − log δ)`. The log factor is the
genuinely two-dimensional contribution that makes `θ = 2`. -/
theorem sublevelVol_abs_mul_Icc {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    sublevelVol volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        (fun p : ℝ × ℝ => |p.1 * p.2|) δ
      = 4 * δ * (1 - Real.log δ) := by
  have hm_cont := continuous_sliceHalfLen hδ0
  -- the sublevel set is the closed region under ±sliceHalfLen
  have hset : (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        ∩ {p : ℝ × ℝ | |p.1 * p.2| ≤ δ}
      = {p : ℝ × ℝ | p.1 ∈ Icc (-1 : ℝ) 1
          ∧ p.2 ∈ Icc (-(sliceHalfLen δ p.1)) (sliceHalfLen δ p.1)} := by
    ext ⟨x, y⟩
    simp only [mem_inter_iff, mem_prod, mem_ofPred_eq, mem_Icc, ← abs_le]
    constructor
    · rintro ⟨⟨hx, hy⟩, hxy⟩
      exact ⟨hx, (abs_le_sliceHalfLen_iff hδ0 y).mp ⟨hy, hxy⟩⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨h1, h2⟩ := (abs_le_sliceHalfLen_iff hδ0 y).mpr hy
      exact ⟨⟨hx, h1⟩, h2⟩
  unfold sublevelVol
  rw [hset, Measure.volume_eq_prod]
  simp only [← Pi.neg_apply (f := sliceHalfLen δ)]
  rw [volume_region_between_cc_eq_integral
      (hm_cont.neg.integrableOn_Icc) (hm_cont.integrableOn_Icc)
      hm_cont.neg.measurable hm_cont.measurable measurableSet_Icc
      (fun x _ => by
        have := (sliceHalfLen_pos hδ0 x).le
        rw [Pi.neg_apply]
        linarith)]
  -- the slice-width integral
  have hwidth : ∀ x : ℝ, (sliceHalfLen δ - -sliceHalfLen δ) x
      = 2 * sliceHalfLen δ x := by
    intro x
    simp [Pi.sub_apply]
    ring
  rw [setIntegral_congr_fun measurableSet_Icc fun x _ => hwidth x]
  -- Icc → interval integral
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ 1)]
  -- split at -δ and δ
  have hδle : -δ ≤ δ := by linarith
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun x => 2 * sliceHalfLen δ x) volume a b :=
    fun a b => (hm_cont.const_mul 2 |>.intervalIntegrable a b)
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := (-1 : ℝ)) (b := -δ)
      (c := 1) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (-δ : ℝ)) (b := δ)
      (c := 1) (hi _ _) (hi _ _)]
  -- middle piece: m = 1
  have hmid : ∫ x in (-δ : ℝ)..δ, 2 * sliceHalfLen δ x = 4 * δ := by
    rw [intervalIntegral.integral_congr (g := fun _ => (2 : ℝ)) ?_]
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    · intro x hx
      rw [uIcc_of_le hδle, mem_Icc] at hx
      dsimp only
      rw [sliceHalfLen_of_abs_le hδ0 (abs_le.mpr ⟨hx.1, hx.2⟩), mul_one]
  -- right piece: m = δ/x
  have hright : ∫ x in (δ : ℝ)..1, 2 * sliceHalfLen δ x = 2 * δ * (-Real.log δ) := by
    rw [intervalIntegral.integral_congr (g := fun x => (2 * δ) * x⁻¹) ?_]
    · rw [intervalIntegral.integral_const_mul, integral_inv
        (by rw [uIcc_of_le hδ1.le]; exact fun h => absurd h.1 (by linarith) : (0:ℝ) ∉ uIcc δ 1)]
      rw [Real.log_div one_ne_zero hδ0.ne', Real.log_one]
      ring
    · intro x hx
      rw [uIcc_of_le hδ1.le, mem_Icc] at hx
      have hx0 : 0 < x := lt_of_lt_of_le hδ0 hx.1
      dsimp only
      rw [sliceHalfLen_of_le_abs (by rw [abs_of_pos hx0]; exact hx.1), abs_of_pos hx0]
      field_simp
  -- left piece: m = δ/(-x)
  have hleft : ∫ x in (-1 : ℝ)..(-δ), 2 * sliceHalfLen δ x = 2 * δ * (-Real.log δ) := by
    rw [intervalIntegral.integral_congr (g := fun x => (-(2 * δ)) * x⁻¹) ?_]
    · rw [intervalIntegral.integral_const_mul, integral_inv
        (by rw [uIcc_of_le (by linarith : (-1:ℝ) ≤ -δ)]
            exact fun h => absurd h.2 (by linarith) : (0:ℝ) ∉ uIcc (-1 : ℝ) (-δ))]
      rw [show (-δ : ℝ) / -1 = δ by ring]
      ring
    · intro x hx
      rw [uIcc_of_le (by linarith : (-1:ℝ) ≤ -δ), mem_Icc] at hx
      have hx0 : x < 0 := lt_of_le_of_lt hx.2 (by linarith)
      dsimp only
      rw [sliceHalfLen_of_le_abs (by rw [abs_of_neg hx0]; linarith [hx.1, hx.2]), abs_of_neg hx0]
      field_simp
  rw [hmid, hright, hleft, ENNReal.toReal_ofReal (by nlinarith [Real.log_neg hδ0 hδ1])]
  nlinarith [Real.log_neg hδ0 hδ1]

/-- Squared form: for `ε ∈ (0,1)`,
`vol {(x,y) ∈ [-1,1]² : (x·y)² ≤ ε} = 2√ε(2 − log ε)`. -/
theorem sublevelVol_mul_sq_Icc {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    sublevelVol volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        (fun p : ℝ × ℝ => (p.1 * p.2) ^ 2) ε
      = 2 * ε ^ ((2 : ℝ))⁻¹ * (2 - Real.log ε) := by
  have hδ0 : 0 < ε ^ ((2 : ℝ))⁻¹ := Real.rpow_pos_of_pos hε0 _
  have hδ1 : ε ^ ((2 : ℝ))⁻¹ < 1 :=
    Real.rpow_lt_one hε0.le hε1 (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)
  have hset : {p : ℝ × ℝ | (p.1 * p.2) ^ 2 ≤ ε}
      = {p : ℝ × ℝ | |p.1 * p.2| ≤ ε ^ ((2 : ℝ))⁻¹} := by
    ext p
    rw [mem_ofPred_eq, mem_ofPred_eq,
      Real.le_rpow_inv_iff_of_pos (abs_nonneg _) hε0.le (by norm_num : (0:ℝ) < 2),
      show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  unfold sublevelVol
  rw [hset]
  have := sublevelVol_abs_mul_Icc hδ0 hδ1
  unfold sublevelVol at this
  rw [this, Real.log_rpow hε0]
  ring

end ProductMonomial2D



section Instance2D

/-- **The first θ = 2 instance**: `(xy)²` on `[-1,1]²` has
`(λ, θ, c) = (1/2, 2, 2)`, the `L = 2` case of the `L`-fold product
`(∏ᵢ xᵢ)²` with `(λ, θ) = (1/2, L)`. -/
theorem hasLLCOn_mul_sq :
    HasLLCOn volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      (fun p : ℝ × ℝ => (p.1 * p.2) ^ 2) (1 / 2) 2 2 := by
  have hlim : Tendsto (fun ε : ℝ => 2 + 4 * (-Real.log ε)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    have h0 : Tendsto (fun ε : ℝ => 4 * (-Real.log ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_neg_log_nhdsGT_zero.inv_tendsto_atTop).const_mul (4 : ℝ)
    simpa using (tendsto_const_nhds (x := (2 : ℝ))).add h0
  refine Tendsto.congr' ?_ hlim
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  have hε0 : (0 : ℝ) < ε := hε.1
  have hlog : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε.1 hε.2)
  have hlogne : Real.log ε ≠ 0 := (neg_pos.mp hlog).ne
  have hrpow : (0 : ℝ) < ε ^ ((2 : ℝ))⁻¹ := Real.rpow_pos_of_pos hε0 _
  rw [sublevelVol_mul_sq_Icc hε.1 hε.2]
  unfold llcScale
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one,
    show (1 : ℝ) / 2 = ((2 : ℝ))⁻¹ by norm_num]
  field_simp
  ring

/-- Exponent-level form of the first θ = 2 instance. -/
theorem hasLLCExponentsOn_mul_sq :
    HasLLCExponentsOn volume (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      (fun p : ℝ × ℝ => (p.1 * p.2) ^ 2) (1 / 2) 2 :=
  hasLLCOn_mul_sq.hasLLCExponentsOn two_pos

end Instance2D

end SingularLearningTheory
