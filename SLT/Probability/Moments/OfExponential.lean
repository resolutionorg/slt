/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.SpecialFunctions.Pow.LogBounds
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Power moments from exponential moments

`x^r ≤ C e^{x/2}` (`Real.exists_rpow_le_exp_half`), and the resulting bound of an integral of
`|f|^r` by an exponential moment (`MeasureTheory.integral_rpow_le_of_exponential_moment`).
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- The deterministic polynomial/exponential comparison uses the existing
Watanabe scalar bound. -/
theorem _root_.Real.exists_rpow_le_exp_half {r : ℝ} (hr : 0 ≤ r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 0 ≤ y → y ^ r ≤ C * Real.exp (y / 2) := by
  obtain ⟨C₀, hC₀⟩ := Real.exists_rpow_mul_exp_neg_le
    (lam := r) (c := (1 / 2 : ℝ)) (by norm_num)
  refine ⟨max 1 C₀, le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro y hy
  by_cases hy1 : 1 ≤ y
  · have h := hC₀ y hy1
    rw [Real.exp_neg, ← div_eq_mul_inv] at h
    have h' := (div_le_iff₀ (Real.exp_pos _)).mp h
    calc y ^ r ≤ C₀ * Real.exp ((1 / 2 : ℝ) * y) := h'
      _ ≤ max 1 C₀ * Real.exp ((1 / 2 : ℝ) * y) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
      _ = _ := by congr 2; ring
  · have hp := Real.rpow_le_one hy (le_of_not_ge hy1) hr
    have he : 1 ≤ Real.exp (y / 2) := Real.one_le_exp_iff.mpr (by positivity)
    calc y ^ r ≤ 1 := hp
      _ ≤ max 1 C₀ * Real.exp (y / 2) :=
        one_le_mul_of_one_le_of_one_le (le_max_left _ _) he

/-- An exponential-moment bound `E exp(Y) ≤ exp(B)` gives polynomial moment
bounds growing polynomially in B. This avoids needing exponential moments of
the random empirical-process envelope outside the posterior expectation. -/
theorem _root_.MeasureTheory.integral_rpow_le_of_exponential_moment
    {W : Type*} [MeasurableSpace W] {ρ : Measure W} [IsProbabilityMeasure ρ]
    {Y : W → ℝ} (hYm : AEStronglyMeasurable Y ρ) (hY : ∀ᵐ w ∂ρ, 0 ≤ Y w)
    {r : ℝ} (hr : 0 ≤ r) {B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hscalar : ∀ y : ℝ, 0 ≤ y → y ^ r ≤ C * Real.exp (y / 2))
    (he : Integrable (fun w ↦ Real.exp (Y w)) ρ)
    (hbound : ∫ w, Real.exp (Y w) ∂ρ ≤ Real.exp B) :
    Integrable (fun w ↦ (Y w) ^ r) ρ ∧
      (∫ w, (Y w) ^ r ∂ρ) ≤ (2 * B) ^ r + C := by
  have hshift : Integrable (fun w ↦ Real.exp (Y w - B)) ρ := by
    have h := he.const_mul (Real.exp (-B))
    refine h.congr (Eventually.of_forall fun w ↦ ?_)
    dsimp only
    rw [← Real.exp_add]
    congr 1
    ring
  have heq : (∫ w, Real.exp (Y w - B) ∂ρ) =
      Real.exp (-B) * ∫ w, Real.exp (Y w) ∂ρ := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with w
    rw [← Real.exp_add]
    congr 1
    ring
  have hshift_le : (∫ w, Real.exp (Y w - B) ∂ρ) ≤ 1 := by
    rw [heq]
    calc Real.exp (-B) * (∫ w, Real.exp (Y w) ∂ρ)
        ≤ Real.exp (-B) * Real.exp B :=
          mul_le_mul_of_nonneg_left hbound (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add]; simp
  have hpt : ∀ᵐ w ∂ρ, (Y w) ^ r ≤ (2 * B) ^ r + C * Real.exp (Y w - B) := by
    filter_upwards [hY] with w hw
    by_cases hcut : Y w ≤ 2 * B
    · exact (Real.rpow_le_rpow hw hcut hr).trans
        (le_add_of_nonneg_right (mul_nonneg hC (Real.exp_pos _).le))
    · have he' : Real.exp (Y w / 2) ≤ Real.exp (Y w - B) :=
        Real.exp_le_exp.mpr (by linarith [lt_of_not_ge hcut])
      exact ((hscalar _ hw).trans (mul_le_mul_of_nonneg_left he' hC)).trans
        (le_add_of_nonneg_left (Real.rpow_nonneg (by positivity) _))
  have hdom : Integrable (fun w ↦ (2 * B) ^ r + C * Real.exp (Y w - B)) ρ :=
    (integrable_const _).add (hshift.const_mul _)
  have hi : Integrable (fun w ↦ (Y w) ^ r) ρ :=
    hdom.mono' ((Real.continuous_rpow_const hr).comp_aestronglyMeasurable hYm) (by
      filter_upwards [hY, hpt] with w hw h
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hw r)] using h)
  refine ⟨hi, ?_⟩
  calc (∫ w, (Y w) ^ r ∂ρ)
      ≤ ∫ w, ((2 * B) ^ r + C * Real.exp (Y w - B)) ∂ρ := integral_mono_ae hi hdom hpt
    _ = (2 * B) ^ r + C * ∫ w, Real.exp (Y w - B) ∂ρ := by
      rw [integral_add (integrable_const _) (hshift.const_mul _), integral_const_mul]
      simp
    _ ≤ (2 * B) ^ r + C := by nlinarith

end SingularLearningTheory.BayesGibbs
