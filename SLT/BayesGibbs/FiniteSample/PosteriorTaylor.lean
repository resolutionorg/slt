/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FiniteSample.PosteriorAUI
public import SLT.BayesGibbs.FiniteSample.CubicRate
import SLT.BayesGibbs.CubicResidualL1
import SLT.BayesGibbs.EnvelopeSixthMoments
public import SLT.BayesGibbs.FiniteSample.PosteriorFive
import SLT.BayesGibbs.Posterior.Measurability
import SLT.BayesGibbs.Posterior.GibbsVarianceBounds
import SLT.BayesGibbs.Posterior.FirstMoment
import SLT.BayesGibbs.ExpMeasure
import SLT.BayesGibbs.Posterior.RadialMoment
import SLT.Probability.Moments.EmpiricalSumEven
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Taylor residuals of the Bayes errors

The scaled Bayes errors are the scaled Gibbs errors minus half a posterior variance, up to
residuals: `SingularLearningTheory.BayesGibbs.generalizationTaylorResidual` is
$nB_g - nG_g + \frac n2 E_q[\mathrm{Var}_w f(x, w)]$ and
`SingularLearningTheory.BayesGibbs.trainingTaylorResidual` is $nB_t - nG_t + V/2$, with $V$ the
functional variance. Wherever the envelope bounds and the Laplace doubling bound hold, both are
bounded by `SingularLearningTheory.BayesGibbs.cubicResidualRate` times a sixth-moment dominator, with
one constant for every $n$ and every sample. With a data envelope
$|f(x, w)| \le A(x)\sqrt{K(w)}$, $A$ in $L^6(q)$, and empirical envelopes $L_n$ with uniformly
bounded sixth moments, both residuals tend to zero in $L^1$ and in probability. This replaces
$nB_g$ and $nB_t$ by Gibbs errors minus half a variance in the posterior observables of
[Wat09, Theorem 6.8].

## Main results

* `SingularLearningTheory.BayesGibbs.exists_finiteSample_taylor_bounds`: the bounds at every sample, with one
  constant.
* `SingularLearningTheory.BayesGibbs.measurable_finiteSample_taylor_residuals`: both residuals are measurable
  at every sample size.
* `SingularLearningTheory.BayesGibbs.finiteSample_taylor_residuals_tendsto`: both residuals tend to zero in
  $L^1$ and in probability.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- The residual $nB_g - nG_g + \frac n2 E_q[\mathrm{Var}_w f(x, w)]$ of the scaled
generalization Bayes error, from entries `0` and `2` of
`SingularLearningTheory.BayesGibbs.posteriorFive` and the posterior variance
`SingularLearningTheory.BayesGibbs.posteriorFeatureVariance` of $f(x, \cdot)$. Its bound is
`SingularLearningTheory.BayesGibbs.exists_finiteSample_taylor_bounds`. -/
@[expose] noncomputable def generalizationTaylorResidual {d : ℕ} {X Ω : Type*} [MeasurableSpace X]
    (ν : Measure (Fin d → ℝ)) (q : Measure X) (K : (Fin d → ℝ) → ℝ)
    (f : X → (Fin d → ℝ) → ℝ) (Xs : ℕ → Ω → X) (β : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w)
  posteriorFive ν q K f Xs β n ω 0 - posteriorFive ν q K f Xs β n ω 2 +
    (n : ℝ) * (∫ x, posteriorFeatureVariance Q f x ∂q) / 2

/-- The residual $nB_t - nG_t + V/2$ of the scaled training Bayes error, with $V$ the
functional variance, from entries `1`, `3` and `4` of
`SingularLearningTheory.BayesGibbs.posteriorFive`. Its bound is
`SingularLearningTheory.BayesGibbs.exists_finiteSample_taylor_bounds`. -/
@[expose] noncomputable def trainingTaylorResidual {d : ℕ} {X Ω : Type*} [MeasurableSpace X]
    (ν : Measure (Fin d → ℝ)) (q : Measure X) (K : (Fin d → ℝ) → ℝ)
    (f : X → (Fin d → ℝ) → ℝ) (Xs : ℕ → Ω → X) (β : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  posteriorFive ν q K f Xs β n ω 1 - posteriorFive ν q K f Xs β n ω 3 +
    posteriorFive ν q K f Xs β n ω 4 / 2

/-- Deterministic fresh/training Taylor bounds with one constant for
all n and all samples. No covariance insertion or residual bound is assumed. -/
private theorem exists_finiteSample_taylor_bounds {d : ℕ} {X Ω : Type*} [MeasurableSpace X]
    {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν] {q : Measure X} [IsProbabilityMeasure q]
    {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (hν : ν ≠ 0) (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hKq : ∀ w, K w = ∫ x, f x w ∂q)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {A : X → ℝ} (hAm : Measurable A) (hA0 : ∀ x, 0 ≤ A x) (hA6 : MemLp A 6 q)
    (hAf : ∀ᵐ x ∂q, ∀ᵐ w ∂ν, |f x w| ≤ A x * Real.sqrt (K w))
    {β D : ℝ} (hβ : 0 < β) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n → ∀ (ω : Ω) (L : ℝ), 0 ≤ L →
      (∀ᵐ w ∂ν, Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ L * Real.sqrt (K w)) →
      (∀ i < n, ∀ᵐ w ∂ν, |f (Xs i ω) w| ≤ A (Xs i ω) * Real.sqrt (K w)) →
      (∫ w, Real.exp (-((n : ℝ) * β / 4 * K w)) ∂ν ≤
        D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w)) ∂ν) →
      |generalizationTaylorResidual ν q K f Xs β n ω| ≤
        cubicResidualRate β C n * (1 + L ^ 6 + ∫ x, A x ^ 6 ∂q) ∧
      |trainingTaylorResidual ν q K f Xs β n ω| ≤ cubicResidualRate β C n *
        (1 + L ^ 6 + (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 6) := by
  obtain ⟨C, hC, hactual⟩ := exists_finiteSample_posterior_cubic_rate hν hKm hK0 hKB hβ hD
  refine ⟨C, hC, fun n hn ω L hL he hAs hLD ↦ ?_⟩
  let Kn := empiricalLoss f Xs n ω
  let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * Kn w)
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
  obtain ⟨hQ, hKi, _⟩ := posterior_first_moment_le_ae (G := fun w ↦ (n : ℝ) * β * Kn w) hν hKm (hKnm.const_mul _)
    hK0 hKB hn' hβ (by positivity : 0 ≤ β / 2 * L ^ 2) hD
    (hsand.mono fun _ h ↦ h.1) (hsand.mono fun _ h ↦ h.2) hLD
  letI : IsProbabilityMeasure Q := hQ
  have hA1 : Integrable A q := by
    simpa only [pow_one] using integrable_pow_of_memLp
      (s := 6) (by norm_num) hA6 (a := 1) (by norm_num)
  have hA2 : Integrable (fun x ↦ A x ^ 2) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 (by norm_num)
  have hA6i : Integrable (fun x ↦ A x ^ 6) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 le_rfl
  have hAfQ : ∀ᵐ x ∂q, ∀ᵐ w ∂Q, |f x w| ≤ A x * Real.sqrt (K w) :=
    hAf.mono fun x hx ↦ ae_expMeasure_of_ae hx
  obtain ⟨hgi, hgi_eq⟩ := integrable_fresh_mean_and_eq hf hAm hA1 hA0 hKq
    (ae_expMeasure_of_ae hKB) hAfQ
  have hvar : ∀ x, (∀ᵐ w ∂ν, |f x w| ≤ A x * Real.sqrt (K w)) →
      Integrable (f x) Q ∧ Integrable (fun w ↦ f x w ^ 2) Q ∧
      0 ≤ posteriorFeatureVariance Q f x ∧
      posteriorFeatureVariance Q f x ≤ A x ^ 2 * ∫ w, K w ∂Q := by
    intro x hx
    apply posterior_feature_variance_le hf.of_uncurry_left.aestronglyMeasurable hKi
    filter_upwards [ae_expMeasure_of_ae hx, ae_expMeasure_of_ae hK0] with w hw hw0
    have h := pow_le_pow_left₀ (abs_nonneg _) hw 2
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hw0] using h
  have hmeanm : Measurable (posteriorFeatureMean Q f) :=
    hf.stronglyMeasurable.integral_prod_right.measurable
  have hvarm : Measurable (posteriorFeatureVariance Q f) :=
    (hf.pow_const 2).stronglyMeasurable.integral_prod_right.measurable.sub (hmeanm.pow_const 2)
  have hvi : Integrable (posteriorFeatureVariance Q f) q :=
    (hA2.mul_const (∫ w, K w ∂Q)).mono' hvarm.aestronglyMeasurable (by
      filter_upwards [hAf] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (hvar x hx).2.2.1]
      exact (hvar x hx).2.2.2)
  have hbm : Measurable (predictiveValue Q f) :=
    hf.neg.exp.stronglyMeasurable.integral_prod_right.measurable.log.neg
  have hpoint : ∀ x, (∀ᵐ w ∂ν, |f x w| ≤ A x * Real.sqrt (K w)) →
      (n : ℝ) * |predictiveValue Q f x - posteriorFeatureMean Q f x +
        posteriorFeatureVariance Q f x / 2| ≤
      cubicResidualRate β C n * (1 + L ^ 6 + A x ^ 6) := fun x hx ↦
    hactual n hn Kn (f x) hKnm hf.of_uncurry_left L (A x) hL (hA0 x) he hx hLD
  have hfresh := fresh_quadratic_residual_le hn'
    (cubicResidualRate_nonneg hβ hC n) hL hbm.aestronglyMeasurable hgi hvi hA6i
    (hAf.mono fun x hx ↦ hpoint x hx)
  have htrain := training_quadratic_residual_le hn (fun i hi ↦ hpoint (Xs i ω) (hAs i hi))
  have hsum := sum_feature_mean_eq_scaled_empirical hn ω
    (fun i hi ↦ (hvar (Xs i ω) (hAs i hi)).1)
  refine ⟨?_, ?_⟩
  · change |(n : ℝ) * (∫ x, predictiveValue Q f x ∂q) -
      (n : ℝ) * (∫ w, K w ∂Q) + (n : ℝ) * (∫ x, posteriorFeatureVariance Q f x ∂q) / 2| ≤ _
    rw [← hgi_eq, show (n : ℝ) * (∫ x, predictiveValue Q f x ∂q) -
        (n : ℝ) * (∫ x, posteriorFeatureMean Q f x ∂q) +
        (n : ℝ) * (∫ x, posteriorFeatureVariance Q f x ∂q) / 2 =
      (n : ℝ) * ((∫ x, predictiveValue Q f x ∂q) - (∫ x, posteriorFeatureMean Q f x ∂q) +
        (∫ x, posteriorFeatureVariance Q f x ∂q) / 2) by ring,
      abs_mul, abs_of_pos hn']
    exact hfresh.2
  · rw [hsum] at htrain
    exact htrain

/-- Every actual Taylor residual is measurable, also at exceptional n. -/
private theorem measurable_finiteSample_taylor_residuals {d : ℕ} {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (ν : Measure (Fin d → ℝ)) [SFinite ν] (q : Measure X) [SFinite q]
    {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hX : ∀ i, Measurable (Xs i)) (β : ℝ) (n : ℕ) :
    Measurable (generalizationTaylorResidual ν q K f Xs β n) ∧
      Measurable (trainingTaylorResidual ν q K f Xs β n) := by
  have hY := measurable_posteriorFive ν q hKm hf hX β n
  have hj : ∀ j, Measurable fun ω ↦ posteriorFive ν q K f Xs β n ω j :=
    fun j ↦ (measurable_pi_apply j).comp hY
  let G : Ω → (Fin d → ℝ) → ℝ := fun ω w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w
  have hG : Measurable (Function.uncurry G) := (measurable_uncurry_empiricalLoss hf hX n).const_mul _
  have hm := measurable_posterior_feature_mean ν (G := G) (f := f) hG hf
  have h2 := measurable_posterior_feature_mean ν (G := G) (f := fun x w ↦ f x w ^ 2) hG (hf.pow_const 2)
  have hv : Measurable fun z : Ω × X ↦ posteriorFeatureVariance (Measure.expMeasure ν (G z.1)) f
      z.2 :=
    h2.sub (hm.pow_const 2)
  exact ⟨((hj 0).sub (hj 2)).add
      ((hv.stronglyMeasurable.integral_prod_right.measurable.const_mul (n : ℝ)).div_const 2),
    ((hj 1).sub (hj 3)).add ((hj 4).div_const 2)⟩

/-- Fresh and training quadratic Taylor residuals converge in L1
and in probability under exactly the sixth-moment setup. This is the
finite-sample Taylor endpoint; fresh variance is subsequently identified with
D−Q and training variance with the empirical covariance insertion. -/
theorem finiteSample_taylor_residuals_tendsto {d : ℕ} {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν] {q : Measure X} [IsProbabilityMeasure q]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (hν : ν ≠ 0) (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hKq : ∀ w, K w = ∫ x, f x w ∂q)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    (hXm : ∀ i, Measurable (Xs i)) (hmap : ∀ i, P.map (Xs i) = q)
    {A : X → ℝ} (hAm : Measurable A) (hA0 : ∀ x, 0 ≤ A x) (hA6 : MemLp A 6 q)
    (hAf : ∀ᵐ x ∂q, ∀ᵐ w ∂ν, |f x w| ≤ A x * Real.sqrt (K w))
    {L : ℕ → Ω → ℝ} (hL0 : ∀ n ω, 0 ≤ L n ω) {CL : ℝ}
    (hL6 : ∀ n, Integrable (fun ω ↦ L n ω ^ 6) P)
    (hL6C : ∀ n, ∫ ω, L n ω ^ 6 ∂P ≤ CL)
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ᵐ w ∂ν,
      Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ L n ω * Real.sqrt (K w))
    {β D : ℝ} (hβ : 0 < β) (hD : 1 ≤ D)
    (hLD : ∀ᶠ n : ℕ in atTop, ∫ w, Real.exp (-((n : ℝ) * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w)) ∂ν) :
    ((∀ᶠ n in atTop, Integrable (generalizationTaylorResidual ν q K f Xs β n) P) ∧
      Tendsto (fun n ↦ ∫ ω, |generalizationTaylorResidual ν q K f Xs β n ω| ∂P) atTop (𝓝 0) ∧
      TendstoInMeasure P (generalizationTaylorResidual ν q K f Xs β) atTop 0) ∧
    ((∀ᶠ n in atTop, Integrable (trainingTaylorResidual ν q K f Xs β n) P) ∧
      Tendsto (fun n ↦ ∫ ω, |trainingTaylorResidual ν q K f Xs β n ω| ∂P) atTop (𝓝 0) ∧
      TendstoInMeasure P (trainingTaylorResidual ν q K f Xs β) atTop 0) := by
  obtain ⟨C, hC, hbounds⟩ := exists_finiteSample_taylor_bounds hν hKm hf hKq hK0 hKB hAm hA0 hA6 hAf hβ hD
  have hA6i : Integrable (fun x ↦ A x ^ 6) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 le_rfl
  have hmeas := fun n ↦ measurable_finiteSample_taylor_residuals ν q hKm hf hXm β n
  have hsamples : ∀ᵐ ω ∂P, ∀ i, ∀ᵐ w ∂ν,
      |f (Xs i ω) w| ≤ A (Xs i ω) * Real.sqrt (K w) := by
    apply ae_all_iff.mpr
    intro i
    have h := hAf
    rw [← hmap i] at h
    exact ae_of_ae_map (hXm i).aemeasurable h
  have hdom : ∀ᶠ n in atTop, ∀ᵐ ω ∂P,
      |generalizationTaylorResidual ν q K f Xs β n ω| ≤
        cubicResidualRate β C n * (1 + L n ω ^ 6 + ∫ x, A x ^ 6 ∂q) ∧
      |trainingTaylorResidual ν q K f Xs β n ω| ≤ cubicResidualRate β C n *
        (1 + L n ω ^ 6 + (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 6) := by
    filter_upwards [hLD, eventually_ge_atTop 1] with n hLDn hn
    filter_upwards [he n hn, hsamples] with ω heω hsω
    exact hbounds n hn ω (L n ω) (hL0 n ω) heω (fun i _ ↦ hsω i) hLDn
  have hGi : ∀ n, Integrable (fun ω ↦ 1 + L n ω ^ 6 + ∫ x, A x ^ 6 ∂q) P :=
    fun n ↦ ((integrable_const _).add (hL6 n)).add (integrable_const _)
  have hGC : ∀ n, (∫ ω, (1 + L n ω ^ 6 + ∫ x, A x ^ 6 ∂q) ∂P) ≤
      1 + CL + ∫ x, A x ^ 6 ∂q := by
    intro n
    have hbase : Integrable (fun ω ↦ 1 + L n ω ^ 6) P :=
      (integrable_const _).add (hL6 n)
    rw [integral_add hbase (integrable_const _),
      integral_add (integrable_const _) (hL6 n)]
    simpa using add_le_add_right (add_le_add_left (hL6C n) 1) (∫ x, A x ^ 6 ∂q)
  have hlinear := fun n hn ↦ sixth_dominator_moment hL6 hL6C hAm hA6i hXm hmap (n := n) hn
  refine ⟨residual_L1_of_eventual_domination (fun n ↦ (hmeas n).1.aestronglyMeasurable)
    (.of_forall hGi) (.of_forall hGC) (.of_forall (cubicResidualRate_nonneg hβ hC))
    (cubicResidualRate_tendsto_zero β C) (hdom.mono fun n hn ↦ hn.mono fun ω hω ↦ hω.1), ?_⟩
  apply residual_L1_of_eventual_domination (fun n ↦ (hmeas n).2.aestronglyMeasurable)
    (C := 1 + CL + ∫ x, A x ^ 6 ∂q)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hlinear n hn).1
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hlinear n hn).2
  · exact .of_forall (cubicResidualRate_nonneg hβ hC)
  · exact cubicResidualRate_tendsto_zero β C
  · exact hdom.mono fun n hn ↦ hn.mono fun ω hω ↦ hω.2

end SingularLearningTheory.BayesGibbs
