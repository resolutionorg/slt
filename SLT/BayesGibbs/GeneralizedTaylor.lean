/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.LogPartitionTaylor
public import SLT.Probability.Moments.TiltedSecondOrder
public import SLT.Probability.Moments.ThirdAbsolute

/-!
# Taylor bounds from absolute moments

A third absolute moment bounds the Taylor remainder of the log-partition function
(`abs_log_taylor_le_of_third_absolute_moment`), a pointwise Taylor bound integrates to a bound on
the Bayes generalization error (`abs_integral_predictive_sub_mean_le`), and third and sixth
moments bound the shifted cubic remainder (`shifted_cubic_remainder_le`).
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {Q : Measure W} [IsProbabilityMeasure Q]

/-- A raw third absolute moment bounds the mixed first/second moment. -/
private theorem abs_integral_mul_integral_sq_le_cube {s : W → ℝ}
    (hs : AEStronglyMeasurable s Q) (h3 : Integrable (fun w ↦ |s w| ^ 3) Q) :
    |∫ w, s w ∂Q| * (∫ w, s w ^ 2 ∂Q) ≤ ∫ w, |s w| ^ 3 ∂Q := by
  let a := ∫ w, |s w| ∂Q
  have ha : 0 ≤ a := integral_nonneg fun w ↦ abs_nonneg _
  have hA := integral_abs_pow_three_le hs h3
  have hi1 : Integrable (fun w ↦ 3 * a * s w ^ 2) Q :=
    (integrable_sq_of_cube hs h3).const_mul _
  have hi2 : Integrable (fun w ↦ 2 * |s w| ^ 3 + a ^ 3) Q :=
    (h3.const_mul 2).add (integrable_const _)
  have h := integral_mono hi1 hi2 fun w ↦ three_mul_mul_sq_le (s := s w) ha
  rw [integral_const_mul, integral_add (h3.const_mul 2) (integrable_const _),
    integral_const_mul, integral_const_prob] at h
  have hm : |∫ w, s w ∂Q| ≤ a := by
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm s
  have hv : 0 ≤ ∫ w, s w ^ 2 ∂Q := integral_nonneg fun w ↦ sq_nonneg _
  have hmv := mul_le_mul_of_nonneg_right hm hv
  change a ^ 3 ≤ _ at hA
  nlinarith

/-- The third cumulant needs no normalization of a statistical model. -/
private theorem abs_third_cumulant_le_six_cube {s : W → ℝ}
    (hs : AEStronglyMeasurable s Q) (h3 : Integrable (fun w ↦ |s w| ^ 3) Q) :
    |(∫ w, s w ^ 3 ∂Q) - 3 * (∫ w, s w ∂Q) * (∫ w, s w ^ 2 ∂Q)
        + 2 * (∫ w, s w ∂Q) ^ 3| ≤ 6 * ∫ w, |s w| ^ 3 ∂Q := by
  have hraw : |∫ w, s w ^ 3 ∂Q| ≤ ∫ w, |s w| ^ 3 ∂Q := by
    calc
      _ ≤ ∫ w, ‖s w ^ 3‖ ∂Q := norm_integral_le_integral_norm _
      _ = _ := integral_congr_ae (.of_forall fun w ↦ by
        dsimp only
        rw [Real.norm_eq_abs, _root_.abs_pow])
  have hmean := abs_integral_pow_three_le hs h3
  have hmixed := abs_integral_mul_integral_sq_le_cube hs h3
  have hv : 0 ≤ ∫ w, s w ^ 2 ∂Q := integral_nonneg fun w ↦ sq_nonneg _
  calc
    _ ≤ |∫ w, s w ^ 3 ∂Q| +
        |3 * (∫ w, s w ∂Q) * (∫ w, s w ^ 2 ∂Q)| +
        |2 * (∫ w, s w ∂Q) ^ 3| :=
      (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ = |∫ w, s w ^ 3 ∂Q| +
        3 * |∫ w, s w ∂Q| * (∫ w, s w ^ 2 ∂Q) +
        2 * |∫ w, s w ∂Q| ^ 3 := by
      rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg hv]
      norm_num
    _ ≤ _ := by nlinarith

/-- The quadratic log-partition remainder is bounded by the largest third
absolute moment under its tilted probability measures. Derivative and moment
identifications remain explicit, so this is usable with posterior measures. -/
theorem abs_log_taylor_le_of_third_absolute_moment
    {I₀ I₁ I₂ I₃ : ℝ → ℝ} {C : ℝ}
    (ρ : ℝ → Measure W) [∀ t, IsProbabilityMeasure (ρ t)] (s : W → ℝ)
    (hpos : ∀ t ∈ Icc (0 : ℝ) 1, 0 < I₀ t)
    (h0 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt I₀ (I₁ t) t)
    (h1 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt I₁ (I₂ t) t)
    (h2 : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt I₂ (I₃ t) t)
    (hs : ∀ t ∈ Icc (0 : ℝ) 1, AEStronglyMeasurable s (ρ t))
    (h3 : ∀ t ∈ Icc (0 : ℝ) 1, Integrable (fun w ↦ |s w| ^ 3) (ρ t))
    (hm1 : ∀ t ∈ Icc (0 : ℝ) 1, I₁ t / I₀ t = ∫ w, s w ∂ρ t)
    (hm2 : ∀ t ∈ Icc (0 : ℝ) 1, I₂ t / I₀ t = ∫ w, s w ^ 2 ∂ρ t)
    (hm3 : ∀ t ∈ Icc (0 : ℝ) 1, I₃ t / I₀ t = ∫ w, s w ^ 3 ∂ρ t)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ∫ w, |s w| ^ 3 ∂ρ t ≤ C) :
    |Real.log (I₀ 1) - Real.log (I₀ 0) - I₁ 0 / I₀ 0 -
        (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2) / 2| ≤ C := by
  have h := abs_log_taylor_le hpos h0 h1 h2 (C := 6 * C) ?_
  · linarith
  · intro t ht
    rw [hm1 t ht, hm2 t ht, hm3 t ht]
    exact (abs_third_cumulant_le_six_cube (hs t ht) (h3 t ht)).trans
      (mul_le_mul_of_nonneg_left (hC t ht) (by norm_num))

/-- Integrate a pointwise Taylor bound to control Bayes generalization without
assuming that the predictive ratio integrates to one. -/
theorem abs_integral_predictive_sub_mean_le {X : Type*} [MeasurableSpace X]
    {q : Measure X} {b m B : X → ℝ}
    (hb : AEStronglyMeasurable b q) (hm : Integrable m q) (hB : Integrable B q)
    (hbound : ∀ᵐ x ∂q, |b x - m x| ≤ B x) :
    Integrable b q ∧ |(∫ x, b x ∂q) - ∫ x, m x ∂q| ≤ ∫ x, B x ∂q := by
  have hd : Integrable (fun x ↦ b x - m x) q :=
    hB.mono' (hb.sub hm.aestronglyMeasurable)
      (hbound.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx)
  have hbi : Integrable b q := by
    exact (hd.add hm).congr (.of_forall fun x ↦ by
      change (b x - m x) + m x = b x
      ring)
  refine ⟨hbi, ?_⟩
  rw [← integral_sub hbi hm, ← Real.norm_eq_abs]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono_ae hd.norm hB
      (hbound.mono fun x hx ↦ by simpa only [Real.norm_eq_abs] using hx))

/-- Splitting the shifted-field cubic bound uses precisely third and sixth
moments of the feature envelope; no density-ratio envelope appears. -/
theorem shifted_cubic_remainder_le {C h A L β : ℝ}
    (hC : 0 ≤ C) (hh : 0 ≤ h) (hA : 0 ≤ A) (hL : 0 ≤ L) (hβ : 0 < β) :
    C * h ^ 3 * A ^ 3 * (1 + L + h * A / β) ^ 3 ≤
      4 * C * h ^ 3 * A ^ 3 * (1 + L) ^ 3 +
        4 * C * h ^ 6 * A ^ 6 / β ^ 3 := by
  have hx : 0 ≤ 1 + L := by linarith
  have hy : 0 ≤ h * A / β := by positivity
  have hcube : (1 + L + h * A / β) ^ 3 ≤
      4 * ((1 + L) ^ 3 + (h * A / β) ^ 3) := by
    nlinarith [mul_nonneg (sq_nonneg (1 + L - h * A / β)) (add_nonneg hx hy)]
  calc
    _ ≤ C * h ^ 3 * A ^ 3 * (4 * ((1 + L) ^ 3 + (h * A / β) ^ 3)) :=
      mul_le_mul_of_nonneg_left hcube (by positivity)
    _ = _ := by ring

end SingularLearningTheory.BayesGibbs
