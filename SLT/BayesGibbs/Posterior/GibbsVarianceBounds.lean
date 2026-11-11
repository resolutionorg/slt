/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.KernelError
public import SLT.BayesGibbs.FiniteSampleMoments
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Bounds on the Gibbs training error and the functional variance

Under a probability measure $Q$ on parameters, such as the tempered posterior, these bounds
control the Gibbs training error and the functional variance by $nE_Q[K]$, the scaled Gibbs
generalization error.

## Main results

* `SingularLearningTheory.BayesGibbs.integrable_empirical_and_abs_gibbs_training_le`: if
  $\sqrt n|K_n - K| \le L\sqrt K$ almost everywhere, then
  $|nE_Q[K_n]| \le \frac32 nE_Q[K] + L^2/2$.
* `SingularLearningTheory.BayesGibbs.posterior_feature_variance_le`: if $f^2 \le A^2K$ almost
  everywhere, then $0 \le \mathrm{Var}_Q[f] \le A^2E_Q[K]$.
* `SingularLearningTheory.BayesGibbs.functional_variance_le_gibbs_mul_average`: if
  $f_i^2 \le A_i^2K$ for every $i < n$, then the functional variance
  $\sum_{i<n}\mathrm{Var}_Q[f_i]$ lies between $0$ and $nE_Q[K]\cdot\frac1n\sum_{i<n}A_i^2$.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {Q : Measure W} [IsProbabilityMeasure Q]

/-- The empirical relative envelope bounds Gibbs training without requiring
an extra square-root posterior moment theorem. Young's inequality is applied
before the parameter integral. -/
theorem integrable_empirical_and_abs_gibbs_training_le {K Kn : W → ℝ}
    (hKi : Integrable K Q) (hKnm : AEStronglyMeasurable Kn Q)
    (hK0 : ∀ᵐ w ∂Q, 0 ≤ K w) {n L : ℝ} (hn : 0 < n)
    (he : ∀ᵐ w ∂Q, Real.sqrt n * |Kn w - K w| ≤ L * Real.sqrt (K w)) :
    Integrable Kn Q ∧ |n * ∫ w, Kn w ∂Q| ≤
      3 / 2 * (n * ∫ w, K w ∂Q) + L ^ 2 / 2 := by
  have hs : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hpt : ∀ᵐ w ∂Q, ‖n * Kn w‖ ≤ 3 / 2 * n * K w + L ^ 2 / 2 := by
    filter_upwards [hK0, he] with w hw0 hw
    have ht2 : Real.sqrt (K w) ^ 2 = K w := Real.sq_sqrt hw0
    have he' := mul_le_mul_of_nonneg_left hw hs
    rw [← mul_assoc, ← pow_two, hs2] at he'
    have hsq := sq_nonneg (Real.sqrt n * Real.sqrt (K w) - L)
    rw [sub_sq, mul_pow, hs2, ht2] at hsq
    have hdev : n * |Kn w - K w| ≤ (n * K w + L ^ 2) / 2 := by
      nlinarith [he', hsq]
    have htri : |Kn w| ≤ |Kn w - K w| + K w := by
      simpa only [sub_add_cancel, abs_of_nonneg hw0] using abs_add_le (Kn w - K w) (K w)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hn]
    nlinarith [mul_le_mul_of_nonneg_left htri hn.le]
  have hdom : Integrable (fun w ↦ 3 / 2 * n * K w + L ^ 2 / 2) Q :=
    (hKi.const_mul _).add (integrable_const _)
  have hni : Integrable (fun w ↦ n * Kn w) Q :=
    hdom.mono' (hKnm.const_mul n) hpt
  refine ⟨(hni.const_mul n⁻¹).congr (.of_forall fun _ ↦ by field_simp), ?_⟩
  have hb := norm_integral_le_of_norm_le hdom hpt
  rw [integral_const_mul, Real.norm_eq_abs, integral_add (hKi.const_mul _) (integrable_const _),
    integral_const_mul] at hb
  have hc : (∫ _w : W, L ^ 2 / 2 ∂Q) = L ^ 2 / 2 := by simp
  rw [hc] at hb
  convert hb using 1 <;> ring

/-- Integrable squares give both integrability and nonnegative variance;
the square bound follows directly from the common feature envelope. -/
theorem posterior_feature_variance_le {f K : W → ℝ} (hfm : AEStronglyMeasurable f Q)
    (hKi : Integrable K Q) {A : ℝ}
    (hf2 : ∀ᵐ w ∂Q, f w ^ 2 ≤ A ^ 2 * K w) :
    Integrable f Q ∧ Integrable (fun w ↦ f w ^ 2) Q ∧
      0 ≤ (∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2 ∧
      (∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2 ≤ A ^ 2 * ∫ w, K w ∂Q := by
  have hf2i : Integrable (fun w ↦ f w ^ 2) Q :=
    (hKi.const_mul (A ^ 2)).mono' (hfm.pow 2) (hf2.mono fun w hw ↦ by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f w))] using hw)
  have hfi : Integrable f Q :=
    ((integrable_const 1).add hf2i).mono' hfm (.of_forall fun w ↦ by
      change |f w| ≤ 1 + f w ^ 2
      nlinarith [sq_nonneg (|f w| - 1), sq_abs (f w)])
  have hsq := sq_integral_le_integral_sq_of_integrable hfi hf2i
  have hb : ∫ w, f w ^ 2 ∂Q ≤ A ^ 2 * ∫ w, K w ∂Q := by
    rw [← integral_const_mul]
    exact integral_mono_ae hf2i (hKi.const_mul _) hf2
  exact ⟨hfi, hf2i, by linarith, by linarith [sq_nonneg (∫ w, f w ∂Q)]⟩

/-- The actual functional variance is bounded by scaled Gibbs generalization
multiplied by the empirical second envelope moment. -/
theorem functional_variance_le_gibbs_mul_average {f : ℕ → W → ℝ} {K : W → ℝ}
    (hKi : Integrable K Q) {A : ℕ → ℝ} {n : ℕ} (hn : 0 < n)
    (hfm : ∀ i < n, AEStronglyMeasurable (f i) Q)
    (hf2 : ∀ i < n, ∀ᵐ w ∂Q, f i w ^ 2 ≤ A i ^ 2 * K w) :
    0 ≤ ∑ i ∈ Finset.range n,
      ((∫ w, f i w ^ 2 ∂Q) - (∫ w, f i w ∂Q) ^ 2) ∧
    (∑ i ∈ Finset.range n, ((∫ w, f i w ^ 2 ∂Q) - (∫ w, f i w ∂Q) ^ 2)) ≤
      ((n : ℝ) * ∫ w, K w ∂Q) * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A i ^ 2) := by
  have h := fun i hi ↦ posterior_feature_variance_le (hfm i hi) hKi (hf2 i hi)
  refine ⟨Finset.sum_nonneg fun i hi ↦ (h i (Finset.mem_range.mp hi)).2.2.1, ?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range n, A i ^ 2 * ∫ w, K w ∂Q :=
      Finset.sum_le_sum fun i hi ↦ (h i (Finset.mem_range.mp hi)).2.2.2
    _ = _ := by
      rw [← Finset.sum_mul]
      have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
      field_simp

end SingularLearningTheory.BayesGibbs
