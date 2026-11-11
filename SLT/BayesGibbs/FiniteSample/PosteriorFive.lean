/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.SecondMoment
public import SLT.BayesGibbs.Posterior.GibbsVarianceBounds
public import SLT.BayesGibbs.FiniteQuartet.PolynomialBounds
public import SLT.BayesGibbs.Posterior.Measurability
public import SLT.Probability.Moments.EmpiricalSumEven
public import SLT.FreeEnergy.FundamentalConditions
public import SLT.BayesGibbs.FiniteSampleMoments
import SLT.BayesGibbs.Posterior.FirstMoment
import SLT.BayesGibbs.ExpMeasure
import SLT.BayesGibbs.Posterior.RadialMoment
public import SLT.BayesGibbs.LaplaceDoubling.Basic
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The five posterior observables

This module defines the four scaled errors and the functional variance of the posterior
$Q = e^{-n\beta K_n}\nu/Z_n$: $nB_g = nE_q[b]$, $nB_t = \sum_{i<n} b(X_i)$, $nG_g = nE_Q[K]$,
$nG_t = nE_Q[K_n]$ and $V = \sum_{i<n} \operatorname{Var}_Q f(X_i, \cdot)$, where
$b(x) = -\log E_Q[e^{-f(x, \cdot)}]$ is the predictive value. It bounds every coordinate, for each
$n$ and each sample, by a constant times the polynomial $1 + L^2 + L^4 + a_2 + a_4$ of
`SingularLearningTheory.BayesGibbs.quartetDom`. This bound gives the asymptotic uniform integrability
of the five observables.

## Main definitions

* `SingularLearningTheory.BayesGibbs.predictiveValue`: the predictive value
  $-\log E_Q[e^{-f(x, \cdot)}]$.
* `SingularLearningTheory.BayesGibbs.posteriorFeatureMean` and
  `SingularLearningTheory.BayesGibbs.posteriorFeatureVariance`: the posterior mean and variance of
  $f(x, \cdot)$.
* `SingularLearningTheory.BayesGibbs.posteriorFive`: the five posterior observables.

## Main results

* `SingularLearningTheory.BayesGibbs.integrable_fresh_mean_and_eq`: under a bounded $K$ and an
  integrable envelope, the posterior mean of $f(x, \cdot)$ is $q$-integrable and its
  $q$-average is $E_Q[K]$.
* `SingularLearningTheory.BayesGibbs.sum_feature_mean_eq_scaled_empirical`: the posterior means at
  the samples sum to $n E_Q[K_n]$.
* `SingularLearningTheory.BayesGibbs.posteriorFive_le_quartetDom`: under relative envelopes for
  $K_n - K$ and $f$, a sixth moment of the data envelope and the Laplace doubling bound, each
  observable is at most an explicit constant times
  `SingularLearningTheory.BayesGibbs.quartetDom`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- The predictive value $b(x) = -\log E_Q[e^{-f(x, \cdot)}]$ of `Q` at `x`. When $f$ is the
log likelihood ratio and $Q$ the posterior, $e^{-b(x)}$ is the Bayes predictive density at $x$
divided by the true density. `SingularLearningTheory.BayesGibbs.posteriorFive` takes $n$ times its
$q$-average, $nB_g$, and its sum over the sample, $nB_t$. -/
@[expose] noncomputable def predictiveValue {X U : Type*} [MeasurableSpace U]
    (Q : Measure U) (f : X → U → ℝ) (x : X) : ℝ :=
  -(Real.log (∫ w, Real.exp (-f x w) ∂Q))

/-- The mean $E_Q[f(x, \cdot)]$ of $f(x, \cdot)$ under `Q`. Its $q$-average is $E_Q[K]$
(`SingularLearningTheory.BayesGibbs.integrable_fresh_mean_and_eq`) and its sum over the sample is
$n E_Q[K_n]$ (`SingularLearningTheory.BayesGibbs.sum_feature_mean_eq_scaled_empirical`). -/
@[expose] noncomputable def posteriorFeatureMean {X U : Type*} [MeasurableSpace U]
    (Q : Measure U) (f : X → U → ℝ) (x : X) : ℝ := ∫ w, f x w ∂Q

/-- The variance $E_Q[f(x, \cdot)^2] - E_Q[f(x, \cdot)]^2$ of $f(x, \cdot)$ under `Q`. Its sum
over the sample is the functional variance $V$, the last coordinate of
`SingularLearningTheory.BayesGibbs.posteriorFive`. -/
@[expose] noncomputable def posteriorFeatureVariance {X U : Type*} [MeasurableSpace U]
    (Q : Measure U) (f : X → U → ℝ) (x : X) : ℝ :=
  (∫ w, f x w ^ 2 ∂Q) - (∫ w, f x w ∂Q) ^ 2

/-- Five-observable vector, with the four errors already scaled by n.
The training Bayes sum equals n times the challenge's average also at n=0. -/
@[expose] noncomputable def posteriorFive {d : ℕ} {X Ω : Type*} [MeasurableSpace X]
    (ν : Measure (Fin d → ℝ)) (q : Measure X) (K : (Fin d → ℝ) → ℝ)
    (f : X → (Fin d → ℝ) → ℝ) (Xs : ℕ → Ω → X) (β : ℝ) (n : ℕ) (ω : Ω) : Fin 5 → ℝ :=
  let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w)
  ![(n : ℝ) * ∫ x, predictiveValue Q f x ∂q,
    ∑ i ∈ Finset.range n, predictiveValue Q f (Xs i ω),
    (n : ℝ) * ∫ w, K w ∂Q,
    (n : ℝ) * ∫ w, empiricalLoss f Xs n ω w ∂Q,
    ∑ i ∈ Finset.range n, posteriorFeatureVariance Q f (Xs i ω)]

/-- Fresh Gibbs mean identity. Compact parameter boundedness and the
L1 data envelope justify Fubini under the posterior. -/
theorem integrable_fresh_mean_and_eq {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    {q : Measure X} [IsProbabilityMeasure q] {Q : Measure U} [IsProbabilityMeasure Q]
    {f : X → U → ℝ} {K : U → ℝ} {A : X → ℝ} {B : ℝ}
    (hf : Measurable (Function.uncurry f)) (hAm : Measurable A)
    (hA : Integrable A q) (hA0 : ∀ x, 0 ≤ A x)
    (hKq : ∀ w, K w = ∫ x, f x w ∂q)
    (hKB : ∀ᵐ w ∂Q, K w ≤ B)
    (hbound : ∀ᵐ x ∂q, ∀ᵐ w ∂Q, |f x w| ≤ A x * Real.sqrt (K w)) :
    Integrable (posteriorFeatureMean Q f) q ∧
      (∫ x, posteriorFeatureMean Q f x ∂q) = ∫ w, K w ∂Q := by
  have hpt : ∀ᵐ z ∂q.prod Q, ‖f z.1 z.2‖ ≤ A z.1 * Real.sqrt (max 0 B) := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hf.norm ((hAm.comp measurable_fst).mul_const _))).mpr
    filter_upwards [hbound] with x hx
    filter_upwards [hx, hKB] with w hw hwB
    rw [Real.norm_eq_abs]
    exact hw.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hwB.trans (le_max_right _ _))) (hA0 x))
  have hi : Integrable (Function.uncurry f) (q.prod Q) :=
    ((hA.mul_const _).comp_fst Q).mono' hf.aestronglyMeasurable hpt
  refine ⟨hi.integral_prod_left, ?_⟩
  change (∫ x, ∫ w, f x w ∂Q ∂q) = _
  rw [integral_integral_swap hi]
  exact integral_congr_ae (.of_forall fun w ↦ (hKq w).symm)

/-- Summing posterior feature means gives the empirical Gibbs mean. -/
theorem sum_feature_mean_eq_scaled_empirical {d : ℕ} {X Ω : Type*}
    {Q : Measure (Fin d → ℝ)} {f : X → (Fin d → ℝ) → ℝ}
    {Xs : ℕ → Ω → X} {n : ℕ} (hn : 0 < n) (ω : Ω)
    (hfi : ∀ i < n, Integrable (f (Xs i ω)) Q) :
    (∑ i ∈ Finset.range n, posteriorFeatureMean Q f (Xs i ω)) =
      (n : ℝ) * ∫ w, empiricalLoss f Xs n ω w ∂Q := by
  simp only [posteriorFeatureMean, empiricalLoss, integral_div]
  rw [integral_finsetSum _ fun i hi ↦ hfi i (Finset.mem_range.mp hi)]
  have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  field_simp

/-- Deterministic actual-observable domination. It derives posterior
probability, all needed integrability, fresh Fubini, training mean identities,
second-order predictive bounds, and variance bounds internally. -/
theorem posteriorFive_le_quartetDom {d : ℕ} {X Ω : Type*} [MeasurableSpace X]
    {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν] {q : Measure X} [IsProbabilityMeasure q]
    {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (hν : ν ≠ 0) (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hKq : ∀ w, K w = ∫ x, f x w ∂q)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {A : X → ℝ} (hAm : Measurable A) (hA0 : ∀ x, 0 ≤ A x) (hA6 : MemLp A 6 q)
    (hAf : ∀ᵐ x ∂q, ∀ᵐ w ∂ν, |f x w| ≤ A x * Real.sqrt (K w))
    {β D L : ℝ} (hβ : 0 < β) (hD : 1 ≤ D) (hL : 0 ≤ L)
    {n : ℕ} (hn : 0 < n) (ω : Ω)
    (he : ∀ᵐ w ∂ν, Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ L * Real.sqrt (K w))
    (hAs : ∀ i < n, ∀ᵐ w ∂ν, |f (Xs i ω) w| ≤ A (Xs i ω) * Real.sqrt (K w))
    (hLD : ∫ w, Real.exp (-((n : ℝ) * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w)) ∂ν) :
    let c := 4 / β * Real.log D
    let E2 := ∫ x, A x ^ 2 ∂q
    let E4 := ∫ x, A x ^ 4 ∂q
    let d := 4 / β ^ 2
    let C := 20 + 4 * c + c * E2 + 8 * E2 + 2 * d * (1 + E4)
    ∀ j, |posteriorFive ν q K f Xs β n ω j| ≤ C * quartetDom L A Xs n ω := by
  dsimp only
  let Kn := empiricalLoss f Xs n ω
  let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * Kn w)
  let c := 4 / β * Real.log D
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hKnm : Measurable Kn := by
    unfold Kn empiricalLoss
    exact (Finset.measurable_sum _ fun i _ ↦ hf.of_uncurry_left).div_const _
  have hsand : ∀ᵐ w ∂ν,
      (n : ℝ) * β * (K w / 2) - β / 2 * L ^ 2 ≤ (n : ℝ) * β * Kn w ∧
      (n : ℝ) * β * Kn w ≤ (n : ℝ) * β * (3 / 2 * K w) + β / 2 * L ^ 2 := by
    filter_upwards [hK0, he] with w hw0 hwe
    simpa only [zero_div, add_zero, zero_mul] using
      tilted_exponent_bounds (f := 0) (A := 0) (σ := 0) hw0 hn' hβ
        ⟨le_rfl, zero_le_one⟩ hwe (by simp)
  obtain ⟨hQ, hKi, hKb⟩ := posterior_first_moment_le_ae (G := fun w ↦ (n : ℝ) * β * Kn w) hν hKm (hKnm.const_mul _)
    hK0 hKB hn' hβ (by positivity : 0 ≤ β / 2 * L ^ 2) hD
    (hsand.mono fun _ h ↦ h.1) (hsand.mono fun _ h ↦ h.2) hLD
  letI : IsProbabilityMeasure Q := hQ
  have hc : 0 ≤ c := mul_nonneg (by positivity) (Real.log_nonneg hD)
  have hgg : (n : ℝ) * ∫ w, K w ∂Q ≤ c + 4 * L ^ 2 := by
    have heq : 8 / β * (β / 2 * L ^ 2) = 4 * L ^ 2 := by field_simp; ring
    simpa only [heq] using hKb
  have hgg0 : 0 ≤ (n : ℝ) * ∫ w, K w ∂Q :=
    mul_nonneg hn'.le (integral_nonneg_of_ae (ae_expMeasure_of_ae hK0))
  have hgt := integrable_empirical_and_abs_gibbs_training_le hKi hKnm.aestronglyMeasurable
    (ae_expMeasure_of_ae hK0) hn' (ae_expMeasure_of_ae he)
  have hA1 : Integrable A q := by
    simpa only [pow_one] using integrable_pow_of_memLp
      (s := 6) (by norm_num) hA6 (a := 1) (by norm_num)
  have hA2 : Integrable (fun x ↦ A x ^ 2) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 (by norm_num)
  have hA4 : Integrable (fun x ↦ A x ^ 4) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 (by norm_num)
  have hAfQ : ∀ᵐ x ∂q, ∀ᵐ w ∂Q, |f x w| ≤ A x * Real.sqrt (K w) :=
    hAf.mono fun x hx ↦ ae_expMeasure_of_ae hx
  obtain ⟨hgi, hgi_eq⟩ := integrable_fresh_mean_and_eq hf hAm hA1 hA0 hKq
    (ae_expMeasure_of_ae hKB) hAfQ
  have hbm : Measurable (predictiveValue Q f) := by
    exact hf.neg.exp.stronglyMeasurable.integral_prod_right.measurable.log.neg
  have hsqrt : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hn)
  have hfresh := fresh_predictive_polynomial_bound hn' hsqrt hβ hbm.aestronglyMeasurable
    hgi hA2 hA4 (hAf.mono fun x hx ↦
      abs_predictive_posterior_sub_mean_scaled_le hν hKm hKnm hf.of_uncurry_left
        hK0 hKB hn' hβ (hA0 x) hD he hx hLD)
  have htrain := training_predictive_polynomial_bound hn hβ (fun i hi ↦
    abs_predictive_posterior_sub_mean_scaled_le hν hKm hKnm hf.of_uncurry_left
      hK0 hKB hn' hβ (hA0 _) hD he (hAs i hi) hLD)
  have hsquare : ∀ i < n, ∀ᵐ w ∂Q, f (Xs i ω) w ^ 2 ≤ A (Xs i ω) ^ 2 * K w := by
    intro i hi
    filter_upwards [ae_expMeasure_of_ae (hAs i hi), ae_expMeasure_of_ae hK0] with w hw hw0
    have h := pow_le_pow_left₀ (abs_nonneg _) hw 2
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hw0] using h
  have hfi : ∀ i < n, Integrable (f (Xs i ω)) Q := fun i hi ↦
    (posterior_feature_variance_le hf.of_uncurry_left.aestronglyMeasurable hKi (hsquare i hi)).1
  have hsum := sum_feature_mean_eq_scaled_empirical hn ω hfi
  have hv := functional_variance_le_gibbs_mul_average hKi hn
    (fun i _ ↦ hf.of_uncurry_left.aestronglyMeasurable) hsquare
  let a2 := (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 2
  let a4 := (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 4
  have ha2 : 0 ≤ a2 := by dsimp [a2]; positivity
  have ha4 : 0 ≤ a4 := by dsimp [a4]; positivity
  have h22 : a2 ^ 2 ≤ a4 := average_sq_le_average_pow_four hn ω
  have hbG : |(n : ℝ) * (∫ x, predictiveValue Q f x ∂q) -
      (n : ℝ) * ∫ w, K w ∂Q| ≤
      (c / 2 + 4 * L ^ 2) * (∫ x, A x ^ 2 ∂q) + 4 / β ^ 2 * (∫ x, A x ^ 4 ∂q) := by
    rw [← hgi_eq, ← mul_sub, abs_mul, abs_of_pos hn']
    exact hfresh.2
  dsimp only [posteriorFeatureMean] at hsum
  rw [hsum] at htrain
  have hall := quartet_polynomial_domination ha2 ha4 h22 hc
    (integral_nonneg fun x ↦ sq_nonneg _) (integral_nonneg fun x ↦ by positivity)
    (by positivity : 0 ≤ 4 / β ^ 2) hgg0 hgg hgt.2 hbG htrain hv.1 hv.2
  intro j
  fin_cases j
  · exact hall.1
  · exact hall.2.1
  · exact hall.2.2.1
  · exact hall.2.2.2.1
  · exact hall.2.2.2.2

end SingularLearningTheory.BayesGibbs
