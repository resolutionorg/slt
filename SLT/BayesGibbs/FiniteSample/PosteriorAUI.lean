/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FiniteSample.PosteriorFive
public import SLT.BayesGibbs.FiniteQuartet.AUI
public import SLT.BayesGibbs.EnvelopeSixthMoments
public import SLT.MeasureTheory.Function.AsympUnifIntegrable
import SLT.BayesGibbs.Posterior.Measurability
import SLT.Probability.Moments.EmpiricalSumEven

/-!
# Uniform integrability of the scaled Bayes and Gibbs errors

At sample size $n$ the five observables $nB_g$, $nB_t$, $nG_g$, $nG_t$ and the functional
variance $V$ of the tempered posterior are asymptotically uniformly integrable. The proof
dominates each observable, for all large $n$, by a multiple of the quartet dominator
`SingularLearningTheory.BayesGibbs.quartetDom`, using an envelope $|f(x, w)| \le A(x)\sqrt{K(w)}$ with
$A$ in $L^6$, a bound on the scaled empirical process with uniformly bounded sixth moments, and a
Laplace doubling bound on the prior. This lets convergence in law of the observables pass to
convergence of their expectations, as [Wat09, Theorem 6.8] requires.

## Main results

* `SingularLearningTheory.BayesGibbs.measurable_posteriorFive`: the vector of the five observables is
  measurable at every sample size.
* `SingularLearningTheory.BayesGibbs.asympUnifIntegrable_of_eventual_quartetDom`: a sequence bounded
  by a multiple of the quartet dominator for all large $n$ is asymptotically uniformly integrable.
* `SingularLearningTheory.BayesGibbs.posteriorFive_asympUnifIntegrable`: each of the five observables
  is asymptotically uniformly integrable.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- Joint measurability of the five-observable vector for every n. -/
theorem measurable_posteriorFive {d : ℕ} {X Ω : Type*}
    [MeasurableSpace X] [MeasurableSpace Ω]
    (ν : Measure (Fin d → ℝ)) [SFinite ν] (q : Measure X) [SFinite q]
    {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hX : ∀ i, Measurable (Xs i)) (β : ℝ) (n : ℕ) :
    Measurable (posteriorFive ν q K f Xs β n) := by
  let G : Ω → (Fin d → ℝ) → ℝ := fun ω w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w
  have hKn := measurable_uncurry_empiricalLoss hf hX n
  have hG : Measurable (Function.uncurry G) := hKn.const_mul _
  have hb : Measurable fun z : Ω × X ↦ predictiveValue (Measure.expMeasure ν (G z.1)) f z.2 :=
    measurable_posterior_predictive ν (G := G) (f := f) hG hf
  have hm : Measurable fun z : Ω × X ↦ posteriorFeatureMean (Measure.expMeasure ν (G z.1)) f z.2 :=
    measurable_posterior_feature_mean ν (G := G) (f := f) hG hf
  have h2 : Measurable fun z : Ω × X ↦ ∫ w, f z.2 w ^ 2 ∂Measure.expMeasure ν (G z.1) :=
    measurable_posterior_feature_mean ν (G := G) (f := fun x w ↦ f x w ^ 2) hG (hf.pow_const 2)
  have hv : Measurable fun z : Ω × X ↦ posteriorFeatureVariance (Measure.expMeasure ν (G z.1)) f
      z.2 :=
    h2.sub (hm.pow_const 2)
  have hpop : Measurable fun ω ↦ ∫ w, K w ∂Measure.expMeasure ν (G ω) :=
    measurable_posterior_integral ν hG (hKm.comp measurable_snd)
  have htrain : Measurable fun ω ↦ ∫ w, empiricalLoss f Xs n ω w ∂Measure.expMeasure ν (G ω) :=
    measurable_posterior_integral ν hG hKn
  apply measurable_pi_iff.mpr
  intro j
  fin_cases j
  · change Measurable fun ω ↦ (n : ℝ) * ∫ x, predictiveValue (Measure.expMeasure ν (G ω)) f x ∂q
    exact hb.stronglyMeasurable.integral_prod_right.measurable.const_mul _
  · change Measurable fun ω ↦ ∑ i ∈ Finset.range n, predictiveValue (Measure.expMeasure ν
      (G ω)) f (Xs i ω)
    exact Finset.measurable_sum _ fun i _ ↦ hb.comp (f := fun ω ↦ (ω, Xs i ω)) (measurable_id.prodMk (hX i))
  · exact hpop.const_mul _
  · exact htrain.const_mul _
  · change Measurable fun ω ↦ ∑ i ∈ Finset.range n, posteriorFeatureVariance (Measure.expMeasure ν
      (G ω)) f (Xs i ω)
    exact Finset.measurable_sum _ fun i _ ↦ hv.comp (f := fun ω ↦ (ω, Xs i ω)) (measurable_id.prodMk (hX i))

/-- Eventual domination suffices. No integrability of a fixed early sample
size is imposed on the original observable. -/
private theorem asympUnifIntegrable_of_eventual_quartetDom
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {q : Measure X} {P : Measure Ω} [IsProbabilityMeasure P]
    {Xs : ℕ → Ω → X} {Y : ℕ → Ω → ℝ} {L : ℕ → Ω → ℝ}
    (hLm : ∀ n, Measurable (L n)) (hL0 : ∀ n ω, 0 ≤ L n ω) {CL : ℝ}
    (hL6 : ∀ n, Integrable (fun ω ↦ L n ω ^ 6) P)
    (hL6C : ∀ n, ∫ ω, L n ω ^ 6 ∂P ≤ CL)
    {A : X → ℝ} (hAm : Measurable A) (hA0 : ∀ x, 0 ≤ A x)
    (hA6 : Integrable (fun x ↦ A x ^ 6) q)
    (hXm : ∀ i, Measurable (Xs i)) (hmap : ∀ i, P.map (Xs i) = q)
    {C : ℝ} (hC : 0 ≤ C)
    (hY : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, |Y n ω| ≤ C * quartetDom (L n ω) A Xs n ω) :
    AsympUnifIntegrable P Y := by
  let Z : ℕ → Ω → ℝ := fun n ω ↦ if n = 0 then 0 else C * quartetDom (L n ω) A Xs n ω
  have hZm : ∀ n, Measurable (Z n) := by
    intro n
    by_cases hn : n = 0
    · simp only [Z, hn, if_true]; exact measurable_const
    · simp only [Z, hn, if_false]
      unfold quartetDom
      fun_prop
  have hZ0 : ∀ ω, Z 0 ω = 0 := fun _ ↦ by simp [Z]
  have hZbd : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P,
      |Z n ω| ≤ C * quartetDom (L n ω) A Xs n ω := by
    intro n hn
    apply Eventually.of_forall
    intro ω
    simp only [Z, hn.ne', if_false, abs_of_nonneg (mul_nonneg hC (quartetDom_nonneg n ω))]
    exact le_rfl
  have hZ := asympUnifIntegrable_of_quartetDom hZm hZ0 hL0 hL6 hL6C hAm hA0 hA6 hXm hmap hC hZbd
  apply hZ.of_abs_le
  filter_upwards [hY, eventually_ge_atTop 1] with n hn hn1
  simpa only [Z, show n ≠ 0 by omega, if_false] using hn

/-- Five-observable AUI from analytic envelope inputs.
No AUI, Taylor, covariance, posterior-integrability, or remainder certificate
is a premise. All bounds are needed only eventually in sample size. -/
theorem posteriorFive_asympUnifIntegrable {d : ℕ} {X Ω : Type*}
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
    {L : ℕ → Ω → ℝ} (hLm : ∀ n, Measurable (L n)) (hL0 : ∀ n ω, 0 ≤ L n ω) {CL : ℝ}
    (hL6 : ∀ n, Integrable (fun ω ↦ L n ω ^ 6) P)
    (hL6C : ∀ n, ∫ ω, L n ω ^ 6 ∂P ≤ CL)
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ᵐ w ∂ν,
      Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ L n ω * Real.sqrt (K w))
    {β D : ℝ} (hβ : 0 < β) (hD : 1 ≤ D)
    (hLD : ∀ᶠ n : ℕ in atTop, ∫ w, Real.exp (-((n : ℝ) * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w)) ∂ν) :
    ∀ j, AsympUnifIntegrable P (fun n ω ↦ posteriorFive ν q K f Xs β n ω j) := by
  let c := 4 / β * Real.log D
  let E2 := ∫ x, A x ^ 2 ∂q
  let E4 := ∫ x, A x ^ 4 ∂q
  let d := 4 / β ^ 2
  let C := 20 + 4 * c + c * E2 + 8 * E2 + 2 * d * (1 + E4)
  have hc : 0 ≤ c := mul_nonneg (by positivity) (Real.log_nonneg hD)
  have hE2 : 0 ≤ E2 := integral_nonneg fun x ↦ sq_nonneg _
  have hE4 : 0 ≤ E4 := integral_nonneg fun x ↦ by positivity
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hA6i : Integrable (fun x ↦ A x ^ 6) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 le_rfl
  have hsamples : ∀ᵐ ω ∂P, ∀ i, ∀ᵐ w ∂ν,
      |f (Xs i ω) w| ≤ A (Xs i ω) * Real.sqrt (K w) := by
    apply ae_all_iff.mpr
    intro i
    have h := hAf
    rw [← hmap i] at h
    exact ae_of_ae_map (hXm i).aemeasurable h
  intro j
  apply asympUnifIntegrable_of_eventual_quartetDom hLm hL0 hL6 hL6C hAm hA0 hA6i hXm hmap hC
  filter_upwards [hLD, eventually_ge_atTop 1] with n hLDn hn
  filter_upwards [he n hn, hsamples] with ω heω hsω
  exact posteriorFive_le_quartetDom hν hKm hf hKq hK0 hKB hAm hA0 hA6 hAf
    hβ hD (hL0 n ω) hn ω heω (fun i _ ↦ hsω i) hLDn j

end SingularLearningTheory.BayesGibbs
