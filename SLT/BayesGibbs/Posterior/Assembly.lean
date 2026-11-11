/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.Envelopes
public import SLT.BayesGibbs.LaplaceDoubling.Atlas
public import SLT.BayesGibbs.Posterior.EventualMoments
public import SLT.BayesGibbs.Posterior.PopulationMoments
public import SLT.BayesGibbs.FiniteSample.CovarianceReplacement
public import SLT.BayesGibbs.FiniteSample.FiveAssembly
public import SLT.BayesGibbs.CompactPosterior.Assembly
import SLT.BayesGibbs.FiniteSample.PosteriorAUI
public import SLT.BayesGibbs.PopulationDiagonalLimit
public import SLT.BayesGibbs.FiniteSample.PosteriorFive
import SLT.BayesGibbs.ExpMeasure
public import SLT.BayesGibbs.SixthMoments
import SLT.FreeEnergy.Discharge
import SLT.Probability.Moments.EmpiricalSumEven
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# Asymptotics of the Bayes and Gibbs observables

The five observables $(nB_g, nB_t, nG_g, nG_t, V)$ of the tempered posterior at inverse
temperature $\beta > 0$ converge jointly in law and in expectation, under relatively finite
variance. The hypotheses are a nondegenerate resolution atlas, fundamental condition (I) at
$s = 6$, an analytic resolution of the log density ratio, an i.i.d. sample, and weak limits of
the empirical processes on the charts and on the tail $\{K \ge \delta\}$ on one limit probability
space. From these the proof derives the posterior envelopes, the Laplace doubling bound,
asymptotic uniform integrability, the Taylor residuals of the Bayes errors and the replacement of
the empirical covariance, and then applies the assembly of the compact Gaussian posterior. This
is the content of [Wat09, Theorems 6.8–6.10] and of the equations of state of
[Wat09, Main Theorem 6.3] under relatively finite variance.

## Main results

* `SingularLearningTheory.NondegenerateResolutionAtlas.posteriorFive_asymptotics`: the five
  observables converge jointly in law to `SingularLearningTheory.GaussianPosterior.compactFive` of the
  limiting process on the essential faces, and their expectations converge to the limit's. For
  some singular fluctuation $\nu \ge 0$ the expectations converge to
  `SingularLearningTheory.bayesGibbsCoefficients`, such as $E[nB_g] \to \lambda/\beta + (1 - 1/\beta)\nu$
  and $E[V] \to 2\nu/\beta$. In probability, $n(B_g - B_t - G_g + G_t) \to 0$,
  $n(G_g + G_t) \to 2\lambda/\beta$, $V - 2n(G_g - B_g) \to 0$ and $V - 2n(G_t - B_t) \to 0$.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.NondegenerateResolutionAtlas
open BayesGibbs GaussianPosterior

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : NondegenerateResolutionAtlas K φ W)
-- The metric `Metric.Sigma.metricSpace` on the disjoint union of the chart cubes
-- `SingularLearningTheory.ResolutionAtlas.FaceDomain`; its topology is the disjoint-union topology.
attribute [local instance] Metric.Sigma.metricSpace

/-- The actual five observables, on their original sample space, converge
jointly and in expectation. All posterior envelopes, Taylor remainders,
covariance replacement, and uniform integrability are derived internally
from the sixth-moment hypotheses. The chart and tail processes share
one supplied limit probability space. -/
theorem posteriorFive_asymptotics
    {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
    {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (I : FundamentalConditionI 6 q f K W)
    (L : R.toResolutionAtlas.AnalyticResolvedLikelihood 6 q f)
    (hW : IsCompact W) (hf : Measurable (Function.uncurry f))
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    (hK0 : ∀ w ∈ W, 0 ≤ K w)
    (hRFV : ∃ c : ℝ, 0 ≤ c ∧ ∀ w ∈ W, populationSecondMoment q f w ≤ c * K w)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w))
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hind : iIndepFun Xs P)
    [CompactSpace {w // w ∈ W ∧ R.δ ≤ K w}]
    (E : EmpiricalProcessLimit q
      (fun x (u : R.toResolutionAtlas.FaceDomain) ↦ L.a u.1 x u.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P P')
    {β : ℝ} (hβ : 0 < β) :
    let ν := (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))
    let hE4 := E.momentBound_four_of_six
      (L.momentBound_chart_six hX hlaw hind E)
    let Y := posteriorFive ν q K f Xs β
    let Ylim := fun ω' ↦ compactFive R.toResolutionAtlas.essentialFaceMeasure β R.rlct
      (E.covarianceKernel hE4) (-E.Ψlim ω')
    ∃ fluctuation : ℝ, 0 ≤ fluctuation ∧
      TendstoInDistribution Y atTop Ylim (fun _ ↦ P) P' ∧
      (∀ j, Integrable (fun ω' ↦ Ylim ω' j) P') ∧
      (∀ j, ∀ᶠ n in atTop, Integrable (fun ω ↦ Y n ω j) P) ∧
      (∀ j, Tendsto (fun n ↦ ∫ ω, Y n ω j ∂P) atTop
        (𝓝 (∫ ω', Ylim ω' j ∂P'))) ∧
      (∀ j, Tendsto (fun n ↦ ∫ ω, Y n ω j ∂P) atTop
        (𝓝 (bayesGibbsCoefficients β R.rlct fluctuation j))) ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 0 - Y n ω 1 - Y n ω 2 + Y n ω 3) atTop 0 ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 2 + Y n ω 3 - 2 * R.rlct / β) atTop 0 ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 4 - 2 * (Y n ω 2 - Y n ω 0)) atTop 0 ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 4 - 2 * (Y n ω 3 - Y n ω 1)) atTop 0 := by
  classical
  dsimp only
  let R₀ := R.toResolutionAtlas
  let ν := (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))
  letI : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal hφi.hasFiniteIntegral
  have hν : ν ≠ 0 := restricted_prior_ne_zero_of_sublevel_pos hvol
  have hKm : Measurable K := by
    rw [funext I.K_eq]
    exact hf.stronglyMeasurable.integral_prod_left.measurable
  have hKc : ContinuousOn K W := I.continuousOn_K
  have hK0ae : ∀ᵐ w ∂ν, 0 ≤ K w :=
    (withDensity_absolutelyContinuous _ _).ae_le
      ((ae_restrict_mem hW.measurableSet).mono fun w hw ↦ hK0 w hw)
  obtain ⟨B, hB⟩ := hW.exists_bound_of_continuousOn hKc
  have hKB : ∀ᵐ w ∂ν, K w ≤ max B 0 :=
    (withDensity_absolutelyContinuous _ _).ae_le
      ((ae_restrict_mem hW.measurableSet).mono fun w hw ↦ by
        have hb : |K w| ≤ B := by simpa only [Real.norm_eq_abs] using hB w hw
        exact (le_abs_self _).trans (hb.trans (le_max_left _ _)))
  have h2 : ∀ w ∈ W, Integrable (fun x ↦ f x w ^ 2) q := by
    intro w hw
    have hf6 : MemLp (fun x ↦ f x w) 6 q :=
      I.memLp hw
    exact integrable_pow_of_memLp (s := 6) (by norm_num) hf6 (by norm_num)
  let Λ : ℕ → Ω → ℝ := fun n ω ↦ max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖
  obtain ⟨A, hAm, hA0, hA6, hAf, hΛm, hΛ0, ⟨CL, hCL, hΛ6⟩, he⟩ :=
    exists_posterior_envelopes_six R₀ I L hW hφi hf hcont hX hlaw hind E T
  have hΛtight : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < |Λ n ω|} ≤ ENNReal.ofReal η := EmpiricalProcessLimit.max_empirical_norm_tight E T
  obtain ⟨D, hD, hLD⟩ := R.eventually_laplace_doubling hW hKm hKc hK0 hφ hφi hβ
  have hAUI := posteriorFive_asympUnifIntegrable hν hKm hf I.K_eq hK0ae hKB hX hlaw
    hAm hA0 hA6 hAf hΛm hΛ0 (fun n ↦ (hΛ6 n).1) (fun n ↦ (hΛ6 n).2) he hβ hD hLD
  have hTaylor := finiteSample_taylor_residuals_tendsto hν hKm hf I.K_eq hK0ae hKB hX hlaw
    hAm hA0 hA6 hAf hΛ0 (fun n ↦ (hΛ6 n).1) (fun n ↦ (hΛ6 n).2) he hβ hD hLD
  have hCov := finiteSample_covariance_replacement_tendstoInMeasure R₀ I L hW hφi hf hcont
    hX hlaw hind E T hν hKm hK0ae hKB hAm hA0 hA6 hAf hΛ0 hΛtight he hβ hD hLD
  have hPost := eventually_ae_posterior_probability_integrable hν hKm hf
    hK0ae hKB he hβ hD hLD
  have hA2 : Integrable (fun x ↦ A x ^ 2) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 (by norm_num)
  have hfresh : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      (n : ℝ) * (∫ x, posteriorFeatureVariance
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w)) f x ∂q) =
      populationPosteriorFive
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
        q K (empiricalLoss f Xs n ω) f n 4 := by
    filter_upwards [hPost] with n hn
    filter_upwards [hn] with ω hω
    let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w)
    letI : IsProbabilityMeasure Q := hω.1
    have h := integrable_fresh_variance_and_eq (Q := Q) hf hAm hA2 hA0
      (ae_expMeasure_of_ae hKB) (hAf.mono fun x hx ↦ ae_expMeasure_of_ae hx)
    change (n : ℝ) * (∫ x, posteriorFeatureVariance Q f x ∂q) =
      (n : ℝ) * ((∫ w, ∫ x, f x w ^ 2 ∂q ∂Q) -
        ∫ z, ∫ x, f x z.1 * f x z.2 ∂q ∂Q.prod Q)
    rw [h.2]
  let J : R₀.EmpiricalProcessInput β P P' :=
    L.toResolvedLikelihood.empiricalProcessInput β P P' hX hlaw hf I.K_eq
      (I.isCompact_tail hW R₀.δ) E
      (L.primaryLipschitzTight hX hlaw hind E.Ψ_ae_eq) T
  have hKn : J.Kn = empiricalLoss f Xs := rfl
  have hi : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      Integrable K (J.temperedPosterior n ω) ∧ Integrable (J.Kn n ω) (J.temperedPosterior n ω) := by
    filter_upwards [hPost] with n hn
    filter_upwards [hn] with ω hω
    exact hω.2
  let hE4 : E.MomentBound 4 := E.momentBound_four_of_six
    (L.momentBound_chart_six hX hlaw hind E)
  have hρ : R₀.essentialFaceMeasure ≠ 0 := R.essentialFaceMeasure_ne_zero
  obtain ⟨c, hc, hrfv⟩ := hRFV
  have hraw :=
      J.normalize_finiteSampleRawFive_sub_compactFive_tendstoInMeasure L E hE4 hβ hρ
    hW hφ hφi hf hKm hKc hK0 h2 hc hrfv hΛ0 hΛtight he
  have ha := J.posteriorFive_sub_compactFive_tendstoInMeasure ν rfl
    (E.covarianceKernel hE4) hKn hW.measurableSet hφ hφi hraw
    hTaylor.1.2.2 hTaylor.2.2.2 hCov hfresh hi
  have hfield (n : ℕ) (ω : Ω) : R₀.chartFieldCM (J.Ξ n ω) = -E.Ψ n ω := by
    ext u
    rfl
  have ha' : ∀ j, TendstoInMeasure P (fun n ω ↦ posteriorFive ν q K f Xs β n ω j -
      compactFive R₀.essentialFaceMeasure β R₀.rlct (E.covarianceKernel hE4) (-E.Ψ n ω) j)
      atTop 0 := by
    intro j
    simpa only [hfield] using ha j
  haveI : Nonempty R₀.FaceDomain := by
    obtain ⟨u, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_pos.mpr hρ).ne'
    exact ⟨u⟩
  obtain ⟨fluctuation, hfluctuation, hdist, hlimi, heventi, hcoef, hident⟩ :=
    E.compactPosterior_assembly hE4 R₀.essentialFaceMeasure hρ hβ R₀.rlct_pos
      (posteriorFive ν q K f Xs β)
      (fun n ↦ (measurable_posteriorFive ν q hKm hf hX β n).aemeasurable) ha' hAUI
  refine ⟨fluctuation, hfluctuation, hdist, hlimi, heventi, ?_, hcoef, hident⟩
  intro j
  exact (hAUI j).tendsto_integral
    (hdist.continuous_comp (g := fun z : Fin 5 → ℝ ↦ z j) (continuous_apply j))

end SingularLearningTheory.NondegenerateResolutionAtlas
