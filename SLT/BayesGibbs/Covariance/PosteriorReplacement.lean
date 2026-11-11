/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Covariance.LLN
public import SLT.BayesGibbs.Posterior.PopulationMoments
public import SLT.BayesGibbs.Posterior.KernelError
public import SLT.BayesGibbs.FiniteSample.PosteriorRatios
public import SLT.BayesGibbs.TightProducts
public import SLT.BayesGibbs.FiniteSample.PosteriorFive
import SLT.BayesGibbs.Posterior.GibbsVarianceBounds

/-!
# Replacing the empirical covariance in the functional variance

At a fixed sample, the functional variance $V = \sum_{i<n} \mathrm{Var}_w[f(X_i, w)]$ differs from
its population form $n\bigl(E_w[E_q f(x, w)^2] - E_{w, v}[E_q f(x, w)f(x, v)]\bigr)$ by at most
$2\delta \cdot nE_w[K(w)]$, when the error of the empirical covariance of $f$ is at most
$\delta K(w)$ on the diagonal and $\delta\sqrt{K(w)}\sqrt{K(v)}$ for pairs. With the errors
$\delta_n \to 0$ of the uniform law of large numbers for the covariance, this replaces $V$ by its
population form in the posterior observables of [Wat09, Theorem 6.8].

## Main results

* `SingularLearningTheory.BayesGibbs.raw_kernel_integral_error_le`: a kernel error bounded by
  $\delta K(w)$ on the diagonal and $\delta\sqrt{K(w)}\sqrt{K(v)}$ for pairs changes the difference
  of its diagonal and pair posterior integrals by at most $2\delta E_w[K(w)]$.
* `SingularLearningTheory.BayesGibbs.empirical_population_variance_error_le`: the bound
  $2\delta \cdot nE_w[K(w)]$ on the gap between the functional variance and its population form.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

/-- Raw-kernel form of PosteriorKernelError, avoiding division by √K at K=0. -/
private theorem raw_kernel_integral_error_le
    {U : Type*} [MeasurableSpace U] {Q : Measure U} [IsProbabilityMeasure Q]
    {K : U → ℝ} {e : U → U → ℝ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hKm : Measurable K) (hKi : Integrable K Q)
    (hK0 : ∀ᵐ w ∂Q, 0 ≤ K w)
    (hem : Measurable (Function.uncurry e))
    (hd : ∀ᵐ w ∂Q, |e w w| ≤ δ * K w)
    (hp : ∀ᵐ w ∂Q, ∀ᵐ v ∂Q,
      |e w v| ≤ δ * (Real.sqrt (K w) * Real.sqrt (K v))) :
    |(∫ w, e w w ∂Q) - (∫ z, e z.1 z.2 ∂Q.prod Q)| ≤ 2 * δ * ∫ w, K w ∂Q := by
  have hri : Integrable (fun w ↦ Real.sqrt (K w)) Q := by
    apply ((integrable_const (1 : ℝ)).add hKi).mono' hKm.sqrt.aestronglyMeasurable
    filter_upwards [hK0] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    change Real.sqrt (K w) ≤ 1 + K w
    nlinarith [Real.sq_sqrt hw, sq_nonneg (Real.sqrt (K w) - 1 / 2)]
  have hr2i : Integrable (fun w ↦ Real.sqrt (K w) ^ 2) Q :=
    hKi.congr (hK0.mono fun w hw ↦ (Real.sq_sqrt hw).symm)
  have hJ := sq_integral_le_integral_sq_of_integrable hri hr2i
  have hsq : (∫ w, Real.sqrt (K w) ^ 2 ∂Q) = ∫ w, K w ∂Q :=
    integral_congr_ae (hK0.mono fun w hw ↦ Real.sq_sqrt hw)
  rw [hsq] at hJ
  have hdi : |∫ w, e w w ∂Q| ≤ δ * ∫ w, K w ∂Q := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (hKi.const_mul δ)
      (hd.mono fun _ h ↦ by simpa only [Real.norm_eq_abs] using h)
  have hpi : |∫ z, e z.1 z.2 ∂Q.prod Q| ≤
      δ * (∫ w, Real.sqrt (K w) ∂Q) ^ 2 := by
    have hpp : ∀ᵐ z ∂Q.prod Q,
        ‖e z.1 z.2‖ ≤ δ * (Real.sqrt (K z.1) * Real.sqrt (K z.2)) := by
      apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hem.norm
        (((hKm.sqrt.comp measurable_fst).mul (hKm.sqrt.comp measurable_snd)).const_mul δ))).mpr
      simpa only [Real.norm_eq_abs, Function.uncurry, Function.comp_def, Pi.mul_apply] using hp
    have hprod : Integrable (fun z : U × U ↦ Real.sqrt (K z.1) * Real.sqrt (K z.2))
        (Q.prod Q) := hri.smul_prod hri
    calc
      _ ≤ ∫ z, δ * (Real.sqrt (K z.1) * Real.sqrt (K z.2)) ∂Q.prod Q := by
        rw [← Real.norm_eq_abs]
        exact norm_integral_le_of_norm_le (hprod.const_mul δ) hpp
      _ = _ := by
        rw [integral_const_mul,
          integral_prod_mul (fun w ↦ Real.sqrt (K w)) (fun w ↦ Real.sqrt (K w)), pow_two]
  calc
    _ ≤ |∫ w, e w w ∂Q| + |∫ z, e z.1 z.2 ∂Q.prod Q| := abs_sub _ _
    _ ≤ δ * (∫ w, K w ∂Q) + δ * (∫ w, Real.sqrt (K w) ∂Q) ^ 2 := add_le_add hdi hpi
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hJ hδ]

/-- Exact finite-sample variance algebra, all interchanges justified by the
existing data envelope. The conclusion is exactly the two variance coordinates. -/
theorem empirical_population_variance_error_le
    {X Ω U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    {q : Measure X} [IsProbabilityMeasure q] {Q : Measure U} [IsProbabilityMeasure Q]
    {f : X → U → ℝ} {K : U → ℝ} {Xs : ℕ → Ω → X}
    {A : X → ℝ} {B δ : ℝ} {n : ℕ} (hn : 0 < n) (ω : Ω)
    (hf : Measurable (Function.uncurry f)) (hKm : Measurable K)
    (hKi : Integrable K Q) (hK0 : ∀ᵐ w ∂Q, 0 ≤ K w)
    (hAm : Measurable A) (hA2 : Integrable (fun x ↦ A x ^ 2) q)
    (hA0 : ∀ x, 0 ≤ A x) (hKB : ∀ᵐ w ∂Q, K w ≤ B)
    (hbound : ∀ᵐ x ∂q, ∀ᵐ w ∂Q, |f x w| ≤ A x * Real.sqrt (K w))
    (hsample : ∀ i < n, ∀ᵐ w ∂Q, |f (Xs i ω) w| ≤ A (Xs i ω) * Real.sqrt (K w))
    (hδ : 0 ≤ δ)
    (hdiag : ∀ᵐ w ∂Q, |rawProductError q f Xs n ω w w| ≤ δ * K w)
    (hpair : ∀ᵐ w ∂Q, ∀ᵐ v ∂Q,
      |rawProductError q f Xs n ω w v| ≤ δ * (Real.sqrt (K w) * Real.sqrt (K v))) :
    |(∑ i ∈ Finset.range n, posteriorFeatureVariance Q f (Xs i ω)) -
      (n : ℝ) * ((∫ w, ∫ x, f x w ^ 2 ∂q ∂Q) -
        ∫ z, ∫ x, f x z.1 * f x z.2 ∂q ∂Q.prod Q)| ≤
      2 * δ * ((n : ℝ) * ∫ w, K w ∂Q) := by
  obtain ⟨hD, hQ⟩ := integrable_feature_square_and_product hf hAm hA2 hA0 hKB hbound
  have hfi : ∀ i < n, Integrable (f (Xs i ω)) Q ∧ Integrable (fun w ↦ f (Xs i ω) w ^ 2) Q := by
    intro i hi
    have hs : ∀ᵐ w ∂Q, f (Xs i ω) w ^ 2 ≤ A (Xs i ω) ^ 2 * K w := by
      filter_upwards [hsample i hi, hK0] with w hw hw0
      have h := pow_le_pow_left₀ (abs_nonneg _) hw 2
      simpa only [sq_abs, mul_pow, Real.sq_sqrt hw0] using h
    have h := posterior_feature_variance_le hf.of_uncurry_left.aestronglyMeasurable hKi hs
    exact ⟨h.1, h.2.1⟩
  have hsumD : Integrable
      (fun w ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (Xs i ω) w ^ 2) Q :=
    (integrable_finsetSum _ fun i hi ↦ (hfi i (Finset.mem_range.mp hi)).2).const_mul _
  have hprod (i : ℕ) (hi : i ∈ Finset.range n) :
      Integrable (fun z : U × U ↦ f (Xs i ω) z.1 * f (Xs i ω) z.2) (Q.prod Q) :=
    (hfi i (Finset.mem_range.mp hi)).1.smul_prod (hfi i (Finset.mem_range.mp hi)).1
  have hsumQ : Integrable
      (fun z : U × U ↦ (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (Xs i ω) z.1 * f (Xs i ω) z.2)
      (Q.prod Q) :=
    (integrable_finsetSum _ fun i hi ↦
      (hfi i (Finset.mem_range.mp hi)).1.smul_prod (hfi i (Finset.mem_range.mp hi)).1).const_mul _
  have hdiagEq : (∫ w, rawProductError q f Xs n ω w w ∂Q) =
      (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, ∫ w, f (Xs i ω) w ^ 2 ∂Q) -
      ∫ w, ∫ x, f x w ^ 2 ∂q ∂Q := by
    simp only [rawProductError, ← pow_two]
    rw [integral_sub hsumD hD.integral_prod_right, integral_const_mul,
      integral_finsetSum _ fun i hi ↦ (hfi i (Finset.mem_range.mp hi)).2]
  have hpairEq : (∫ z, rawProductError q f Xs n ω z.1 z.2 ∂Q.prod Q) =
      (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (∫ w, f (Xs i ω) w ∂Q) ^ 2) -
      ∫ z, ∫ x, f x z.1 * f x z.2 ∂q ∂Q.prod Q := by
    simp only [rawProductError]
    rw [integral_sub hsumQ hQ.integral_prod_right, integral_const_mul,
      integral_finsetSum _ hprod]
    have hp (i : ℕ) : (∫ z : U × U, f (Xs i ω) z.1 * f (Xs i ω) z.2 ∂Q.prod Q) =
        (∫ w, f (Xs i ω) w ∂Q) ^ 2 := by
      rw [integral_prod_mul (fun w ↦ f (Xs i ω) w) (fun w ↦ f (Xs i ω) w), pow_two]
    simp only [hp]
  have hb := raw_kernel_integral_error_le (e := rawProductError q f Xs n ω) hδ hKm hKi hK0
    (measurable_rawProductError (q := q) (Xs := Xs) hf n ω) hdiag hpair
  rw [hdiagEq, hpairEq] at hb
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have heq : (∑ i ∈ Finset.range n, posteriorFeatureVariance Q f (Xs i ω)) -
      (n : ℝ) * ((∫ w, ∫ x, f x w ^ 2 ∂q ∂Q) -
        ∫ z, ∫ x, f x z.1 * f x z.2 ∂q ∂Q.prod Q) =
      (n : ℝ) * (((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, ∫ w, f (Xs i ω) w ^ 2 ∂Q) -
        ∫ w, ∫ x, f x w ^ 2 ∂q ∂Q) -
        ((n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, (∫ w, f (Xs i ω) w ∂Q) ^ 2) -
        ∫ z, ∫ x, f x z.1 * f x z.2 ∂q ∂Q.prod Q)) := by
    simp only [posteriorFeatureVariance, Finset.sum_sub_distrib]
    field_simp [hn0.ne']
    <;> ring
  rw [heq, abs_mul, abs_of_pos hn0]
  nlinarith [mul_le_mul_of_nonneg_left hb hn0.le]

end SingularLearningTheory.BayesGibbs
