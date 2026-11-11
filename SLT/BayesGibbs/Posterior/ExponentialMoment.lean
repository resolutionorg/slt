/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.LaplaceDoubling.Basic

/-!
# Exponential moments of the posterior

A bound on the posterior expectation of `exp G`, from the prior and the loss, used for the
relatively-finite-variance posterior bounds and the Taylor remainders.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/- Extracted from the intermediate hratio proof in QuartetMomentBounds:230–326.
   The K-integrability parameter is retained to keep the donor call shape. -/
theorem posterior_exponential_moment_le {K G : W → ℝ} (hKm : Measurable K) (hGm : Measurable G)
    (hK0 : ∀ w, 0 ≤ K w) {n β c D : ℝ} (hn : 0 < n) (hβ : 0 < β) (hD : 1 ≤ D)
    (hlow : ∀ᵐ w ∂ν, n * β * (K w / 2) - c ≤ G w)
    (hup : ∀ᵐ w ∂ν, G w ≤ n * β * (3 / 2 * K w) + c)
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν
      ≤ D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν)
    (hZ : 0 < ∫ w, Real.exp (-G w) ∂ν) (hint : Integrable (fun w ↦ K w * Real.exp (-G w)) ν)
    (hintG : Integrable (fun w ↦ Real.exp (-G w)) ν)
    (hintE : Integrable (fun w ↦ Real.exp (n * β / 4 * K w) * Real.exp (-G w)) ν) :
    (∫ w, Real.exp (n * β / 4 * K w) ∂Measure.expMeasure ν G) ≤ D * Real.exp (2 * c) := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hZ
  have hD0 : 0 < D := by linarith
  -- the two Laplace integrals are positive
  have hexpint : ∀ t : ℝ, 0 ≤ t → Integrable (fun w ↦ Real.exp (-(t * K w))) ν := fun t ht ↦
    Integrable.of_bound ((hKm.const_mul t).neg.exp).aestronglyMeasurable 1
      (Eventually.of_forall fun w ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith [hK0 w]))
  have hexppos : ∀ t : ℝ, 0 ≤ t → 0 < ∫ w, Real.exp (-(t * K w)) ∂ν := fun t ht ↦ by
    rw [integral_pos_iff_support_of_nonneg (fun w ↦ (Real.exp_pos _).le) (hexpint t ht)]
    have : Function.support (fun w ↦ Real.exp (-(t * K w))) = univ :=
      eq_univ_of_forall fun w ↦ (Real.exp_pos _).ne'
    rw [this]
    exact Measure.measure_univ_pos.mpr hν0
  have hJ1 := hexppos (n * β / 4) (by positivity)
  have hJ2 := hexppos (3 * n * β / 2) (by positivity)
  -- the numerator and denominator bounds
  have hnum : ∫ w, Real.exp (n * β / 4 * K w) * Real.exp (-G w) ∂ν
      ≤ Real.exp c * ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae hintE ((hexpint _ (by positivity)).const_mul _) ?_
    filter_upwards [hlow] with w hw
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hden : Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν
      ≤ ∫ w, Real.exp (-G w) ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae ((hexpint _ (by positivity)).const_mul _) hintG ?_
    filter_upwards [hup] with w hw
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  -- `E_Π[e^{nβK/4}] ≤ D e^{2c}`
  have hratio : (∫ w, Real.exp (n * β / 4 * K w) * Real.exp (-G w) ∂ν)
      / ∫ w, Real.exp (-G w) ∂ν ≤ D * Real.exp (2 * c) := by
    have hden' : 0 < Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν :=
      mul_pos (Real.exp_pos _) hJ2
    calc (∫ w, Real.exp (n * β / 4 * K w) * Real.exp (-G w) ∂ν) / ∫ w, Real.exp (-G w) ∂ν
        ≤ (Real.exp c * ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν) / ∫ w, Real.exp (-G w) ∂ν :=
          div_le_div_of_nonneg_right hnum hZ.le
      _ ≤ (Real.exp c * ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν)
          / (Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :=
          div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hJ1.le) hden' hden
      _ ≤ (Real.exp c * (D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν))
          / (Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLD (Real.exp_pos _).le) hden'.le
      _ = D * Real.exp (2 * c) := by
          have hEE : Real.exp c * Real.exp (-c) = 1 := by
            rw [← Real.exp_add]
            simp
          have h2c : Real.exp (2 * c) = Real.exp c * Real.exp c := by
            rw [← Real.exp_add]
            ring_nf
          rw [h2c, div_eq_iff (mul_ne_zero (Real.exp_pos _).ne' hJ2.ne')]
          linear_combination (-(D * (∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν)
            * Real.exp c)) * hEE
  rw [integral_expMeasure ν hGm _ hZ]
  exact hratio

end SingularLearningTheory.BayesGibbs
