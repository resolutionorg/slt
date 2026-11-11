/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.ExpMeasure
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Perturbing the posterior variance kernel

For a probability measure $Q$, a nonnegative radial factor $r$ with $E_Q[r^2] < \infty$ and a
kernel error $e$ bounded by $\delta$ on and off the diagonal,
`SingularLearningTheory.BayesGibbs.posterior_variance_kernel_error_le` bounds
$$\Big|E_Q[r(u)^2 e(u, u)] - E_{Q \otimes Q}[r(u) r(v) e(u, v)]\Big| \le 2\delta\,E_Q[r^2].$$
Applied under the posterior with a uniform law-of-large-numbers error $\delta_n \to 0$ for the
product features, it replaces the empirical covariance in the functional variance by the
population covariance. The diagonal and off-diagonal terms are bounded separately by
`SingularLearningTheory.BayesGibbs.weighted_diagonal_kernel_error_le` and
`SingularLearningTheory.BayesGibbs.weighted_pair_kernel_error_le`, and combined using
`MeasureTheory.sq_integral_le_integral_sq_of_integrable`, which is
$E_Q[r]^2 \le E_Q[r^2]$.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {U : Type*} [MeasurableSpace U] {Q : Measure U} [IsProbabilityMeasure Q]

/-- Jensen's square bound from exactly the first two moment hypotheses. -/
theorem _root_.MeasureTheory.sq_integral_le_integral_sq_of_integrable {r : U → ℝ}
    (hr : Integrable r Q) (hr2 : Integrable (fun u ↦ r u ^ 2) Q) :
    (∫ u, r u ∂Q) ^ 2 ≤ ∫ u, r u ^ 2 ∂Q := by
  let m := ∫ u, r u ∂Q
  have h0 : 0 ≤ ∫ u, (r u - m) ^ 2 ∂Q := integral_nonneg fun _ ↦ sq_nonneg _
  have heq : (fun u ↦ (r u - m) ^ 2) = fun u ↦ (r u ^ 2 - 2 * m * r u) + m ^ 2 := by
    funext u; ring
  have hdiff : Integrable (fun u ↦ r u ^ 2 - 2 * m * r u) Q :=
    (hr2.sub (hr.const_mul (2 * m))).congr (Eventually.of_forall fun _ ↦ rfl)
  rw [heq, integral_add hdiff (integrable_const _),
    integral_sub hr2 (hr.const_mul _), integral_const_mul] at h0
  have hc : (∫ _u : U, m ^ 2 ∂Q) = m ^ 2 := by simp
  rw [hc] at h0
  dsimp [m] at h0
  nlinarith [h0]

/-- A uniform diagonal kernel error costs only the second radial moment. -/
private theorem weighted_diagonal_kernel_error_le {r e : U → ℝ} {δ : ℝ}
    (hr2 : Integrable (fun u ↦ r u ^ 2) Q)
    (he : ∀ᵐ u ∂Q, |e u| ≤ δ) :
    |∫ u, r u ^ 2 * e u ∂Q| ≤ δ * ∫ u, r u ^ 2 ∂Q := by
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hr2.const_mul δ) ?_
  filter_upwards [he] with u hu
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hu (sq_nonneg (r u))

/-- A uniform off-diagonal kernel error costs the square of the first radial
moment. The two a.e. quantifiers are retained; diagonal bounds are separate. -/
private theorem weighted_pair_kernel_error_le {r : U → ℝ} {e : U → U → ℝ} {δ : ℝ}
    (hr : Integrable r Q) (hr0 : ∀ᵐ u ∂Q, 0 ≤ r u)
    (he : ∀ᵐ u ∂Q, ∀ᵐ v ∂Q, |e u v| ≤ δ) :
    |∫ u, ∫ v, r u * r v * e u v ∂Q ∂Q| ≤ δ * (∫ u, r u ∂Q) ^ 2 := by
  have hinner : ∀ᵐ u ∂Q, |∫ v, r u * r v * e u v ∂Q| ≤
      (δ * r u) * ∫ v, r v ∂Q := by
    filter_upwards [hr0, he] with u hu he
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hr.const_mul (δ * r u)) ?_
    filter_upwards [hr0, he] with v hv hev
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg hu hv)]
    calc r u * r v * |e u v| ≤ r u * r v * δ :=
        mul_le_mul_of_nonneg_left hev (mul_nonneg hu hv)
      _ = _ := by ring
  rw [← Real.norm_eq_abs]
  have hint : Integrable (fun u ↦ (δ * r u) * ∫ v, r v ∂Q) Q :=
    (hr.const_mul δ).mul_const _
  calc
    _ ≤ ∫ u, (δ * r u) * ∫ v, r v ∂Q ∂Q :=
      norm_integral_le_of_norm_le hint (by simpa only [Real.norm_eq_abs] using hinner)
    _ = δ * (∫ u, r u ∂Q) ^ 2 := by rw [integral_mul_const, integral_const_mul]; ring

/-- Full posterior variance-kernel perturbation. A uniform product-feature
LLN error δ is multiplied by at most twice the posterior second radial moment.
Thus δ_n→0 and tight nEposterior K suffice for replacing training covariance
by population covariance. -/
private theorem posterior_variance_kernel_error_le {r : U → ℝ}
    {e : U → U → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hr : Integrable r Q) (hr2 : Integrable (fun u ↦ r u ^ 2) Q)
    (hr0 : ∀ᵐ u ∂Q, 0 ≤ r u)
    (hdiag : ∀ᵐ u ∂Q, |e u u| ≤ δ)
    (hpair : ∀ᵐ u ∂Q, ∀ᵐ v ∂Q, |e u v| ≤ δ) :
    |(∫ u, r u ^ 2 * e u u ∂Q) -
      (∫ u, ∫ v, r u * r v * e u v ∂Q ∂Q)| ≤ 2 * δ * ∫ u, r u ^ 2 ∂Q := by
  have hdiag' := weighted_diagonal_kernel_error_le hr2 hdiag
  have hpair' := weighted_pair_kernel_error_le hr hr0 hpair
  have hJ := sq_integral_le_integral_sq_of_integrable hr hr2
  calc
    _ ≤ |∫ u, r u ^ 2 * e u u ∂Q| + |∫ u, ∫ v, r u * r v * e u v ∂Q ∂Q| := abs_sub _ _
    _ ≤ δ * (∫ u, r u ^ 2 ∂Q) + δ * (∫ u, r u ∂Q) ^ 2 := add_le_add hdiag' hpair'
    _ ≤ 2 * δ * ∫ u, r u ^ 2 ∂Q := by nlinarith [mul_le_mul_of_nonneg_left hJ hδ]

end SingularLearningTheory.BayesGibbs
