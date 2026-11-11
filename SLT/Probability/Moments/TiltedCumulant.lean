/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Tilted Cumulant
-/

public section

open MeasureTheory Real Filter Topology

namespace ProbabilityTheory

section Tilt

variable {W : Type*} [MeasurableSpace W] (ρ : Measure W) (f : W → ℝ)

/-- Tilted partition `P(t) = ∫ e^{−tf} dρ`. -/
@[expose] noncomputable def tiltPartition (t : ℝ) : ℝ := ∫ w, Real.exp (-(t * f w)) ∂ρ

/-- Tilted first moment `∫ f e^{−tf} dρ`. -/
@[expose] noncomputable def tiltNum (t : ℝ) : ℝ := ∫ w, f w * Real.exp (-(t * f w)) ∂ρ

/-- Tilted second moment `∫ f² e^{−tf} dρ`. -/
@[expose] noncomputable def tiltNum2 (t : ℝ) : ℝ := ∫ w, f w ^ 2 * Real.exp (-(t * f w)) ∂ρ

/-- Tilted log-partition `L(t) = log P(t)`. -/
@[expose] noncomputable def tiltLogPartition (t : ℝ) : ℝ := Real.log (tiltPartition ρ f t)

/-- Tilted mean `M(t) = E_{ρ_t} f`. -/
@[expose] noncomputable def tiltMean (t : ℝ) : ℝ := tiltNum ρ f t / tiltPartition ρ f t

/-- Tilted variance `V(t) = Var_{ρ_t} f`. -/
@[expose] noncomputable def tiltVar
    (t : ℝ) : ℝ := tiltNum2 ρ f t / tiltPartition ρ f t - tiltMean ρ f t ^ 2

variable {ρ f}

omit [MeasurableSpace W] in
/-- Pointwise derivative of the tilted weight. -/
private theorem hasDerivAt_exp_neg_mul (w : W) (t : ℝ) :
    HasDerivAt (fun t ↦ Real.exp (-(t * f w))) (-(f w * Real.exp (-(t * f w)))) t := by
  have h1 : HasDerivAt (fun y ↦ -(y * f w)) (-(1 * f w)) t :=
    ((hasDerivAt_id' t).mul_const (f w)).neg
  exact h1.exp.congr_deriv (by ring)

/-- `|f| ≤ 1 + f²`. -/
private theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]; nlinarith
  · rw [abs_of_nonpos h]; nlinarith

section Dominated

variable [IsProbabilityMeasure ρ] (hf : Measurable f) {I : Set ℝ} (hI : IsOpen I)
  {B : W → ℝ} (hB : Integrable B ρ)
  (hbound : ∀ t ∈ I, ∀ w, (1 + f w ^ 2) * Real.exp (-(t * f w)) ≤ B w)

omit [IsProbabilityMeasure ρ] in
include hf hbound hB in
private theorem integrable_tilt_weight {t : ℝ} (ht : t ∈ I) :
    Integrable (fun w ↦ Real.exp (-(t * f w))) ρ := by
  refine hB.mono' ((Real.measurable_exp.comp (hf.const_mul t).neg).aestronglyMeasurable)
    (ae_of_all _ fun w ↦ ?_)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le]
  have := hbound t ht w
  nlinarith [Real.exp_pos (-(t * f w)), sq_nonneg (f w)]

omit [IsProbabilityMeasure ρ] in
include hf hbound hB in
private theorem integrable_tilt_num {t : ℝ} (ht : t ∈ I) :
    Integrable (fun w ↦ f w * Real.exp (-(t * f w))) ρ := by
  refine hB.mono' ((hf.mul (Real.measurable_exp.comp (hf.const_mul t).neg)).aestronglyMeasurable)
    (ae_of_all _ fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have := hbound t ht w
  have := abs_le_one_add_sq (f w)
  nlinarith [Real.exp_pos (-(t * f w))]

omit [IsProbabilityMeasure ρ] in
omit [IsProbabilityMeasure ρ] in
include hf hbound hB in
private theorem integrable_tilt_num2 {t : ℝ} (ht : t ∈ I) :
    Integrable (fun w ↦ f w ^ 2 * Real.exp (-(t * f w))) ρ := by
  refine hB.mono' (((hf.pow_const 2).mul
    (Real.measurable_exp.comp (hf.const_mul t).neg)).aestronglyMeasurable)
    (ae_of_all _ fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
  have := hbound t ht w
  nlinarith [Real.exp_pos (-(t * f w))]

include hf hbound hB in
private theorem tiltPartition_pos {t : ℝ} (ht : t ∈ I) : 0 < tiltPartition ρ f t := by
  refine (integral_pos_iff_support_of_nonneg (fun w ↦ (Real.exp_pos _).le)
    (integrable_tilt_weight hf hB hbound ht)).mpr ?_
  have hs : Function.support (fun w ↦ Real.exp (-(t * f w))) = Set.univ :=
    Set.eq_univ_of_forall fun w ↦ (Real.exp_pos _).ne'
  rw [hs, measure_univ]
  exact zero_lt_one

omit [IsProbabilityMeasure ρ] in
include hf hI hbound hB in
/-- `P' = −N`. -/
private theorem hasDerivAt_tiltPartition {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (tiltPartition ρ f) (-tiltNum ρ f t) t := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ)
    (F := fun t w ↦ Real.exp (-(t * f w)))
    (F' := fun t w ↦ -(f w * Real.exp (-(t * f w)))) (hI.mem_nhds ht)
    (Eventually.of_forall fun t ↦
      (Real.measurable_exp.comp (hf.const_mul t).neg).aestronglyMeasurable)
    (integrable_tilt_weight hf hB hbound ht)
    ((hf.mul (Real.measurable_exp.comp (hf.const_mul t).neg)).neg.aestronglyMeasurable)
    (ae_of_all _ fun w t' ht' ↦ by
      rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _)]
      have := hbound t' ht' w
      have := abs_le_one_add_sq (f w)
      nlinarith [Real.exp_pos (-(t' * f w))]) hB
    (ae_of_all _ fun w t' _ ↦ hasDerivAt_exp_neg_mul w t')
  rw [tiltNum, ← integral_neg]
  exact h.2

omit [IsProbabilityMeasure ρ] in
include hf hI hbound hB in
/-- `N' = −N₂`. -/
private theorem hasDerivAt_tiltNum {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (tiltNum ρ f) (-tiltNum2 ρ f t) t := by
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ρ)
    (F := fun t w ↦ f w * Real.exp (-(t * f w)))
    (F' := fun t w ↦ -(f w ^ 2 * Real.exp (-(t * f w)))) (hI.mem_nhds ht)
    (Eventually.of_forall fun t ↦
      (hf.mul (Real.measurable_exp.comp (hf.const_mul t).neg)).aestronglyMeasurable)
    (integrable_tilt_num hf hB hbound ht)
    (((hf.pow_const 2).mul
      (Real.measurable_exp.comp (hf.const_mul t).neg)).neg.aestronglyMeasurable)
    (ae_of_all _ fun w t' ht' ↦ by
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      have := hbound t' ht' w
      nlinarith [Real.exp_pos (-(t' * f w))]) hB
    (ae_of_all _ fun w t' _ ↦ ((hasDerivAt_exp_neg_mul w t').const_mul (f w)).congr_deriv
      (by ring))
  rw [tiltNum2, ← integral_neg]
  exact h.2

include hf hI hbound hB in
/-- `L' = −M`. -/
private theorem hasDerivAt_tiltLogPartition {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (tiltLogPartition ρ f) (-tiltMean ρ f t) t := by
  have h := (hasDerivAt_tiltPartition hf hI hB hbound ht).log
    (tiltPartition_pos hf hB hbound ht).ne'
  rw [tiltMean, ← neg_div]
  exact h

include hf hI hbound hB in
/-- `M' = −V`. -/
theorem hasDerivAt_tiltMean {t : ℝ} (ht : t ∈ I) :
    HasDerivAt (tiltMean ρ f) (-tiltVar ρ f t) t := by
  have hP := tiltPartition_pos hf hB hbound ht
  have h := (hasDerivAt_tiltNum hf hI hB hbound ht).div
    (hasDerivAt_tiltPartition hf hI hB hbound ht) hP.ne'
  refine h.congr_deriv ?_
  rw [tiltVar, tiltMean]
  field_simp
  ring

include hf hbound hB in
/-- `V ≥ 0`: the tilted variance is nonnegative. -/
theorem tiltVar_nonneg {t : ℝ} (ht : t ∈ I) : 0 ≤ tiltVar ρ f t := by
  have hP := tiltPartition_pos hf hB hbound ht
  set m := tiltMean ρ f t with hm
  have hi0 := integrable_tilt_weight hf hB hbound ht
  have hi1 := integrable_tilt_num hf hB hbound ht
  have hi2 := integrable_tilt_num2 hf hB hbound ht
  have hpt : ∀ w, (f w - m) ^ 2 * Real.exp (-(t * f w))
      = f w ^ 2 * Real.exp (-(t * f w)) - 2 * m * (f w * Real.exp (-(t * f w)))
        + m ^ 2 * Real.exp (-(t * f w)) := fun w ↦ by ring
  have hI1 : Integrable (fun w ↦ f w ^ 2 * Real.exp (-(t * f w))
      - 2 * m * (f w * Real.exp (-(t * f w)))) ρ := hi2.sub (hi1.const_mul _)
  have hnn : 0 ≤ ∫ w, (f w - m) ^ 2 * Real.exp (-(t * f w)) ∂ρ :=
    integral_nonneg fun w ↦ mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [integral_congr_ae (Eventually.of_forall hpt), integral_add hI1 (hi0.const_mul _),
    integral_sub hi2 (hi1.const_mul _), integral_const_mul, integral_const_mul] at hnn
  -- `hnn : 0 ≤ N₂ − 2 m N + m² P` with `m = N / P`
  have hN : tiltNum ρ f t = m * tiltPartition ρ f t := by
    rw [hm, tiltMean, div_mul_cancel₀ _ hP.ne']
  rw [tiltVar, ← hm, sub_nonneg, le_div_iff₀ hP]
  change (∫ w, f w * Real.exp (-(t * f w)) ∂ρ) = _ at hN
  rw [hN] at hnn
  change 0 ≤ (∫ w, f w ^ 2 * Real.exp (-(t * f w)) ∂ρ) - 2 * m * (m * tiltPartition ρ f t)
    + m ^ 2 * ∫ w, Real.exp (-(t * f w)) ∂ρ at hnn
  change m ^ 2 * tiltPartition ρ f t ≤ ∫ w, f w ^ 2 * Real.exp (-(t * f w)) ∂ρ
  change 0 ≤ (∫ w, f w ^ 2 * Real.exp (-(t * f w)) ∂ρ) - 2 * m * (m * tiltPartition ρ f t)
    + m ^ 2 * tiltPartition ρ f t at hnn
  nlinarith

include hf hI hbound hB in
/-- `V` is continuous on `I` (dominated convergence for the three tilted moments). -/
theorem continuousOn_tiltVar : ContinuousOn (tiltVar ρ f) I := by
  have hP : ∀ t ∈ I, ContinuousAt (tiltPartition ρ f) t := fun t ht ↦
    (hasDerivAt_tiltPartition hf hI hB hbound ht).continuousAt
  have hM : ∀ t ∈ I, ContinuousAt (tiltMean ρ f) t := fun t ht ↦
    (hasDerivAt_tiltMean hf hI hB hbound ht).continuousAt
  have hN2 : ∀ t ∈ I, ContinuousAt (tiltNum2 ρ f) t := by
    intro t ht
    refine continuousAt_of_dominated (μ := ρ) (F := fun t w ↦ f w ^ 2 * Real.exp (-(t * f w)))
      (bound := B) (Eventually.of_forall fun t ↦ ((hf.pow_const 2).mul
        (Real.measurable_exp.comp (hf.const_mul t).neg)).aestronglyMeasurable) ?_ hB
      (ae_of_all _ fun w ↦ ?_)
    · filter_upwards [hI.mem_nhds ht] with t' ht'
      refine ae_of_all _ fun w ↦ ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
      have := hbound t' ht' w
      nlinarith [Real.exp_pos (-(t' * f w))]
    · exact ((hasDerivAt_exp_neg_mul w t).const_mul (f w ^ 2)).continuousAt
  intro t ht
  refine ContinuousAt.continuousWithinAt ?_
  have hPne : tiltPartition ρ f t ≠ 0 := (tiltPartition_pos hf hB hbound ht).ne'
  exact ((hN2 t ht).div (hP t ht) hPne).sub ((hM t ht).pow 2)

variable (hIc : Convex ℝ I)

include hf hI hIc hbound hB in
/-- `L(b) − L(a) = −∫_a^b M`. -/
theorem tiltLogPartition_sub_eq {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    tiltLogPartition ρ f b - tiltLogPartition ρ f a = -∫ t in a..b, tiltMean ρ f t := by
  have hsub : Set.uIcc a b ⊆ I := hIc.ordConnected.uIcc_subset ha hb
  have hM : ContinuousOn (tiltMean ρ f) (Set.uIcc a b) := fun t ht ↦
    (hasDerivAt_tiltMean hf hI hB hbound (hsub ht)).continuousAt.continuousWithinAt
  rw [← intervalIntegral.integral_neg]
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_tiltLogPartition hf hI hB hbound (hsub ht))
    (hM.intervalIntegrable (μ := volume)).neg).symm

include hf hI hIc hbound hB in
/-- `M(a) − M(b) = ∫_a^b V`. -/
theorem tiltMean_sub_eq {a b : ℝ} (ha : a ∈ I) (hb : b ∈ I) :
    tiltMean ρ f a - tiltMean ρ f b = ∫ t in a..b, tiltVar ρ f t := by
  have hsub : Set.uIcc a b ⊆ I := hIc.ordConnected.uIcc_subset ha hb
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht ↦ hasDerivAt_tiltMean hf hI hB hbound (hsub ht))
    (((continuousOn_tiltVar hf hI hB hbound).mono hsub).intervalIntegrable (μ := volume)).neg
  rw [intervalIntegral.integral_neg] at h
  linarith

include hf hI hIc hbound hB in
/-- **The rectangle identity**:
`(L(β+1) − L(β)) − (L(1) − L(0)) = ∫_0^β (M(s) − M(s+1)) ds`. -/
private theorem tiltLogPartition_rectangle {β : ℝ} (h0 : (0 : ℝ) ∈ I) (hβ1 : β + 1 ∈ I)
    (hβ0 : 0 ≤ β) :
    (tiltLogPartition ρ f (β + 1) - tiltLogPartition ρ f β)
      - (tiltLogPartition ρ f 1 - tiltLogPartition ρ f 0)
      = ∫ s in (0 : ℝ)..β, (tiltMean ρ f s - tiltMean ρ f (s + 1)) := by
  have hsub : Set.uIcc 0 (β + 1) ⊆ I := hIc.ordConnected.uIcc_subset h0 hβ1
  have hβ : β ∈ I := hsub (Set.mem_uIcc.mpr (Or.inl ⟨hβ0, by linarith⟩))
  have h1 : (1 : ℝ) ∈ I := hsub (Set.mem_uIcc.mpr (Or.inl ⟨by norm_num, by linarith⟩))
  have hM : ContinuousOn (tiltMean ρ f) I := fun t ht ↦
    (hasDerivAt_tiltMean hf hI hB hbound ht).continuousAt.continuousWithinAt
  have e1 : tiltLogPartition ρ f (β + 1) - tiltLogPartition ρ f 1
      = -∫ s in (0 : ℝ)..β, tiltMean ρ f (s + 1) := by
    rw [tiltLogPartition_sub_eq hf hI hB hbound hIc h1 hβ1,
      intervalIntegral.integral_comp_add_right (fun s ↦ tiltMean ρ f s) 1, zero_add]
  have e2 : tiltLogPartition ρ f β - tiltLogPartition ρ f 0 = -∫ s in (0 : ℝ)..β, tiltMean ρ f s :=
    tiltLogPartition_sub_eq hf hI hB hbound hIc h0 hβ
  have hi1 : IntervalIntegrable (fun s ↦ tiltMean ρ f s) volume 0 β :=
    (hM.mono (hIc.ordConnected.uIcc_subset h0 hβ)).intervalIntegrable
  have hi2 : IntervalIntegrable (fun s ↦ tiltMean ρ f (s + 1)) volume 0 β := by
    have h' : IntervalIntegrable (tiltMean ρ f) volume 1 (β + 1) :=
      (hM.mono (hIc.ordConnected.uIcc_subset h1 hβ1)).intervalIntegrable
    have h'' := h'.comp_add_right 1
    simpa using h''
  rw [intervalIntegral.integral_sub hi1 hi2]
  linarith

include hf hI hIc hbound hB in
/-- Each rectangle integrand is itself an integral of the tilted variance:
`M(s) − M(s+1) = ∫_s^{s+1} V`. -/
private theorem tiltMean_sub_succ_eq {s : ℝ} (hs : s ∈ I) (hs1 : s + 1 ∈ I) :
    tiltMean ρ f s - tiltMean ρ f (s + 1) = ∫ u in s..(s + 1), tiltVar ρ f u :=
  tiltMean_sub_eq hf hI hB hbound hIc hs hs1

include hf hI hIc hbound hB in
/-- **The rectangle is nonnegative**: `L(β+1) − L(β) ≥ L(1) − L(0)` for `β ≥ 0`. -/
private theorem tiltLogPartition_rectangle_nonneg {β : ℝ} (h0 : (0 : ℝ) ∈ I) (hβ1 : β + 1 ∈ I)
    (hβ0 : 0 ≤ β) :
    0 ≤ (tiltLogPartition ρ f (β + 1) - tiltLogPartition ρ f β)
      - (tiltLogPartition ρ f 1 - tiltLogPartition ρ f 0) := by
  rw [tiltLogPartition_rectangle hf hI hB hbound hIc h0 hβ1 hβ0]
  have hsub : Set.uIcc 0 (β + 1) ⊆ I := hIc.ordConnected.uIcc_subset h0 hβ1
  refine intervalIntegral.integral_nonneg hβ0 fun s hs ↦ ?_
  have hs' : s ∈ I := hsub (Set.mem_uIcc.mpr (Or.inl ⟨hs.1, by linarith [hs.2]⟩))
  have hs1 : s + 1 ∈ I := hsub (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [hs.1], by linarith [hs.2]⟩))
  rw [tiltMean_sub_succ_eq hf hI hB hbound hIc hs' hs1]
  refine intervalIntegral.integral_nonneg (by linarith) fun u hu ↦ ?_
  exact tiltVar_nonneg hf hB hbound
    (hsub (Set.mem_uIcc.mpr (Or.inl ⟨by linarith [hu.1, hs.1], by linarith [hu.2, hs.2]⟩)))

end Dominated

end Tilt

end ProbabilityTheory
