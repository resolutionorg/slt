/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Third Absolute Moment
-/

public section

open MeasureTheory Filter

namespace MeasureTheory

variable {W : Type*} [MeasurableSpace W] {Q : Measure W} [IsProbabilityMeasure Q]

/-- The weighted AM-GM bound `3 a² |s| ≤ |s|³ + 2 a³` for `a ≥ 0`. -/
private theorem three_mul_sq_mul_le {a s : ℝ}
    (ha : 0 ≤ a) : 3 * a ^ 2 * |s| ≤ |s| ^ 3 + 2 * a ^ 3 := by
  have h0 : 0 ≤ |s| := abs_nonneg s
  nlinarith [mul_nonneg (sq_nonneg (|s| - a))
    (add_nonneg h0 (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) ha))]

/-- The weighted AM-GM bound `3 δ s² ≤ 2 |s|³ + δ³` for `δ ≥ 0`. -/
theorem _root_.three_mul_mul_sq_le {δ s : ℝ}
    (hδ : 0 ≤ δ) : 3 * δ * s ^ 2 ≤ 2 * |s| ^ 3 + δ ^ 3 := by
  have h0 : 0 ≤ |s| := abs_nonneg s
  have hs : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
  rw [hs]
  nlinarith [mul_nonneg (sq_nonneg (|s| - δ))
    (add_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) h0) hδ)]


theorem integral_const_prob (c : ℝ) : ∫ _ : W, c ∂Q = c := by
  rw [integral_const, probReal_univ, one_smul]

/-- Integrability of `|s|` from integrability of `|s|³` on a probability space. -/
private theorem integrable_abs_of_cube {s : W → ℝ} (hs : AEStronglyMeasurable s Q)
    (h3 : Integrable (fun w ↦ |s w| ^ 3) Q) : Integrable (fun w ↦ |s w|) Q := by
  have hI : Integrable (fun w ↦ (|s w| ^ 3 + 2) / 3) Q := (h3.add (integrable_const 2)).div_const 3
  refine Integrable.mono' hI hs.norm (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_abs]
  have := three_mul_sq_mul_le (a := 1) (s := s w) zero_le_one
  norm_num at this
  linarith

private theorem integrable_of_cube {s : W → ℝ} (hs : AEStronglyMeasurable s Q)
    (h3 : Integrable (fun w ↦ |s w| ^ 3) Q) : Integrable s Q :=
  (integrable_norm_iff hs).mp (by simpa only [Real.norm_eq_abs] using integrable_abs_of_cube hs h3)

theorem integrable_sq_of_cube {s : W → ℝ} (hs : AEStronglyMeasurable s Q)
    (h3 : Integrable (fun w ↦ |s w| ^ 3) Q) : Integrable (fun w ↦ s w ^ 2) Q := by
  have hI : Integrable (fun w ↦ (2 * |s w| ^ 3 + 1) / 3) Q :=
    ((h3.const_mul 2).add (integrable_const 1)).div_const 3
  refine Integrable.mono' hI (hs.pow 2) (Eventually.of_forall fun w ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := three_mul_mul_sq_le (δ := 1) (s := s w) zero_le_one
  norm_num at this
  linarith

/-- `(E|s|)³ ≤ E|s|³` on a probability space (weighted AM-GM, no convexity API). -/
theorem integral_abs_pow_three_le {s : W → ℝ} (hs : AEStronglyMeasurable s Q)
    (h3 : Integrable (fun w ↦ |s w| ^ 3) Q) :
    (∫ w, |s w| ∂Q) ^ 3 ≤ ∫ w, |s w| ^ 3 ∂Q := by
  set a := ∫ w, |s w| ∂Q with ha
  have ha0 : 0 ≤ a := integral_nonneg fun w ↦ abs_nonneg _
  have hI1 : Integrable (fun w ↦ 3 * a ^ 2 * |s w|) Q := (integrable_abs_of_cube hs h3).const_mul _
  have hI2 : Integrable (fun w ↦ |s w| ^ 3 + 2 * a ^ 3) Q := h3.add (integrable_const _)
  have h1 := integral_mono hI1 hI2 fun w ↦ three_mul_sq_mul_le (s := s w) ha0
  rw [integral_const_mul, integral_add h3 (integrable_const _), integral_const_prob] at h1
  rw [← ha] at h1
  nlinarith

/-- `|E s|³ ≤ E |s|³` on a probability space. -/
theorem abs_integral_pow_three_le {s : W → ℝ} (hs : AEStronglyMeasurable s Q)
    (h3 : Integrable (fun w ↦ |s w| ^ 3) Q) :
    |∫ w, s w ∂Q| ^ 3 ≤ ∫ w, |s w| ^ 3 ∂Q := by
  have h1 : |∫ w, s w ∂Q| ≤ ∫ w, |s w| ∂Q := by
    rw [← Real.norm_eq_abs]
    exact (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae
      (Eventually.of_forall fun w ↦ Real.norm_eq_abs _)))
  exact (pow_le_pow_left₀ (abs_nonneg _) h1 3).trans (integral_abs_pow_three_le hs h3)


end MeasureTheory
