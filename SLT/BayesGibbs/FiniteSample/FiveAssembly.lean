/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FiniteSample.PosteriorRatios
public import SLT.BayesGibbs.FiniteSample.PosteriorTaylor
import SLT.BayesGibbs.FiniteSample.PosteriorAUI
public import SLT.MeasureTheory.Function.AsympUnifIntegrable
import SLT.BayesGibbs.CompactPosterior.RatioProbability
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# Convergence of the five posterior observables

The vector `SingularLearningTheory.BayesGibbs.posteriorFive` collects the four scaled errors
$nB_g, nB_t, nG_g, nG_t$ and the functional variance $V$ of the finite-sample posterior. This
module combines the estimates for the Taylor residuals, the covariance replacement and the five
raw integrals into convergence in probability of this vector to its compact limit
`SingularLearningTheory.GaussianPosterior.compactFive`, evaluated at the chart processes $\xi_n$. Under
asymptotic uniform integrability this gives joint convergence in distribution and convergence of
the expectations of all five observables.

## Main results

* `SingularLearningTheory.BayesGibbs.posteriorFive_sub_populationPosteriorFive_tendstoInMeasure`: the
  observables minus their population-covariance form tend to zero in probability when the Taylor
  residuals and the covariance replacement do.
* `EmpiricalProcessInput.posteriorFive_sub_compactFive_of_population_approx`: the ratio
  identity and the two finite-sample approximations give convergence to the compact limit.
* `EmpiricalProcessInput.posteriorFive_sub_compactFive_tendstoInMeasure`: each observable
  minus its compact limit tends to zero in probability, for the posterior on the
  restricted prior.
* `EmpiricalProcessInput.posteriorFive_asymptotics_of_compact_approx`: joint convergence
  in distribution, integrability of the limits, eventual integrability and
  convergence of the expectations.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory

/-- Coordinate projection of a finite-vector error converging to zero. -/
private theorem tendstoInMeasure_pi_apply_zero {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {X : ℕ → Ω → ι → ℝ}
    (h : TendstoInMeasure P X atTop 0) (j : ι) :
    TendstoInMeasure P (fun n ω ↦ X n ω j) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at h ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (h ε hε)
    (fun _ ↦ bot_le) fun n ↦ measure_mono ?_
  intro ω hω
  simp only [mem_ofPred_eq, Pi.zero_apply, sub_zero] at hω ⊢
  exact hω.trans (norm_le_pi_norm _ j)

namespace BayesGibbs

/-- The only error algebra needed after the Taylor and covariance
lemmas: fresh Bayes uses the population variance, training Bayes uses the
empirical variance. Their difference is exactly the covariance replacement. -/
private theorem posteriorFive_sub_populationPosteriorFive_tendstoInMeasure
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (ν : Measure (Fin d → ℝ)) (q : Measure X)
    {P : Measure Ω} {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ}
    {Xs : ℕ → Ω → X} {β : ℝ}
    (hG : TendstoInMeasure P (generalizationTaylorResidual ν q K f Xs β) atTop 0)
    (hT : TendstoInMeasure P (trainingTaylorResidual ν q K f Xs β) atTop 0)
    (hV : TendstoInMeasure P (fun (n : ℕ) ω ↦ posteriorFive ν q K f Xs β n ω 4 -
      populationPosteriorFive
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
        q K (empiricalLoss f Xs n ω) f n 4) atTop 0)
    (hfresh : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      (n : ℝ) * (∫ x, posteriorFeatureVariance
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w)) f x ∂q) =
      populationPosteriorFive
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
        q K (empiricalLoss f Xs n ω) f n 4) :
    ∀ j, TendstoInMeasure P (fun (n : ℕ) ω ↦ posteriorFive ν q K f Xs β n ω j -
      populationPosteriorFive
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
        q K (empiricalLoss f Xs n ω) f n j) atTop 0 := by
  intro j
  fin_cases j
  · refine hG.congr' ?_ EventuallyEq.rfl
    filter_upwards [hfresh] with n hn
    filter_upwards [hn] with ω hω
    dsimp only [generalizationTaylorResidual]
    rw [hω]
    simp [posteriorFive, populationPosteriorFive]
    <;> ring
  · have h := tendstoInMeasure_sub_zero hT (tendstoInMeasure_const_mul_zero (1 / 2) hV)
    refine h.congr (fun n ↦ .of_forall fun ω ↦ ?_) EventuallyEq.rfl
    simp [trainingTaylorResidual, posteriorFive, populationPosteriorFive]
    <;> ring
  · convert tendstoInMeasure_zero_const (P := P) using 1
    funext n ω
    simp [posteriorFive, populationPosteriorFive]
  · convert tendstoInMeasure_zero_const (P := P) using 1
    funext n ω
    simp [posteriorFive, populationPosteriorFive]
  · exact hV

end BayesGibbs

namespace ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
-- The metric `Metric.Sigma.metricSpace` on the disjoint union of the chart cubes
-- `SingularLearningTheory.ResolutionAtlas.FaceDomain`; its topology is the disjoint-union topology.
attribute [local instance] Metric.Sigma.metricSpace
variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {Xs : ℕ → Ω → X}
  {f : X → (Fin d → ℝ) → ℝ} {β : ℝ}
  (J : R.EmpiricalProcessInput β P P')

variable {R} in
/-- Exact ratio identities and the two independently established finite-sample
approximations combine into the five-vector approximation. -/
theorem EmpiricalProcessInput.posteriorFive_sub_compactFive_of_population_approx
    (ν : Measure (Fin d → ℝ)) (C : PSDKernel R.FaceDomain)
    (hraw : TendstoInMeasure P (fun (n : ℕ) ω ↦
      GaussianPosterior.normalizeRaw (J.finiteSampleRawFive q f n ω) -
      GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
        (R.chartFieldCM (J.Ξ n ω))) atTop 0)
    (hratio : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      GaussianPosterior.normalizeRaw (J.finiteSampleRawFive q f n ω) =
        BayesGibbs.populationPosteriorFive
          (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
          q K (empiricalLoss f Xs n ω) f n)
    (hpop : ∀ j, TendstoInMeasure P (fun (n : ℕ) ω ↦
      BayesGibbs.posteriorFive ν q K f Xs β n ω j -
        BayesGibbs.populationPosteriorFive
          (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
          q K (empiricalLoss f Xs n ω) f n j) atTop 0) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      BayesGibbs.posteriorFive ν q K f Xs β n ω -
      GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
        (R.chartFieldCM (J.Ξ n ω))) atTop 0 := by
  apply tendstoInMeasure_finite_pi_zero
  intro j
  have hr := tendstoInMeasure_pi_apply_zero hraw j
  have h := tendstoInMeasure_add_zero (hpop j) hr
  refine h.congr' ?_ EventuallyEq.rfl
  filter_upwards [hratio] with n hn
  filter_upwards [hn] with ω hω
  simp only [Pi.sub_apply]
  rw [hω]
  ring

variable {R} in
/-- Convenience endpoint for the common-process construction. Every
premise is an output of the raw-integral, Taylor, covariance or posterior
integrability modules; the original restricted prior is kept explicit. -/
theorem EmpiricalProcessInput.posteriorFive_sub_compactFive_tendstoInMeasure
    (ν : Measure (Fin d → ℝ))
    (hν : ν = (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)))
    (C : PSDKernel R.FaceDomain)
    (hKn : J.Kn = empiricalLoss f Xs)
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hraw : TendstoInMeasure P (fun (n : ℕ) ω ↦
      GaussianPosterior.normalizeRaw (J.finiteSampleRawFive q f n ω) -
      GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
        (R.chartFieldCM (J.Ξ n ω))) atTop 0)
    (hG : TendstoInMeasure P (BayesGibbs.generalizationTaylorResidual ν q K f Xs β) atTop 0)
    (hT : TendstoInMeasure P (BayesGibbs.trainingTaylorResidual ν q K f Xs β) atTop 0)
    (hV : TendstoInMeasure P (fun (n : ℕ) ω ↦ BayesGibbs.posteriorFive ν q K f Xs β n ω 4 -
      BayesGibbs.populationPosteriorFive
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
        q K (empiricalLoss f Xs n ω) f n 4) atTop 0)
    (hfresh : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      (n : ℝ) * (∫ x, BayesGibbs.posteriorFeatureVariance
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w)) f x ∂q) =
      BayesGibbs.populationPosteriorFive
        (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
        q K (empiricalLoss f Xs n ω) f n 4)
    (hi : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      Integrable K (J.temperedPosterior n ω) ∧ Integrable (J.Kn n ω) (J.temperedPosterior n ω)) :
    ∀ j, TendstoInMeasure P (fun (n : ℕ) ω ↦
      BayesGibbs.posteriorFive ν q K f Xs β n ω j -
      GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
        (R.chartFieldCM (J.Ξ n ω)) j) atTop 0 := by
  have hpop := BayesGibbs.posteriorFive_sub_populationPosteriorFive_tendstoInMeasure
    ν q hG hT hV hfresh
  have hratio : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      GaussianPosterior.normalizeRaw (J.finiteSampleRawFive q f n ω) =
        BayesGibbs.populationPosteriorFive
          (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω w))
          q K (empiricalLoss f Xs n ω) f n := by
    filter_upwards [hi, eventually_ge_atTop 2] with n hn hn2
    filter_upwards [hn] with ω hω
    have h := J.normalize_finiteSampleRawFive_eq_populationPosteriorFive q f
      hW hφ hφi hn2 ω hω.1 hω.2
    simpa only [EmpiricalProcessInput.temperedPosterior, hν, hKn] using h
  have h := J.posteriorFive_sub_compactFive_of_population_approx ν C hraw hratio hpop
  exact fun j ↦ tendstoInMeasure_pi_apply_zero h j

variable {R} in
/-- Final probabilistic consequence for actual observables: joint weak law,
all five limiting integrabilities, eventual finite-sample integrabilities,
and convergence of all five expectations. The exact expected-quartet formulas
are supplied separately by the compact Gaussian Stein theorem. -/
theorem EmpiricalProcessInput.posteriorFive_asymptotics_of_compact_approx
    (ν : Measure (Fin d → ℝ)) [SFinite ν]
    (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hXm : ∀ i, Measurable (Xs i)) (hβ : 0 < β) (hρ : R.essentialFaceMeasure ≠ 0)
    (C : PSDKernel R.FaceDomain)
    (happrox : TendstoInMeasure P (fun (n : ℕ) ω ↦
      BayesGibbs.posteriorFive ν q K f Xs β n ω -
      GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
        (R.chartFieldCM (J.Ξ n ω))) atTop 0)
    (hA : ∀ j, AsympUnifIntegrable P
      (fun (n : ℕ) ω ↦ BayesGibbs.posteriorFive ν q K f Xs β n ω j)) :
    let Ylim := fun ω' ↦ GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
      (R.chartFieldCM (J.Ξlim ω'))
    TendstoInDistribution (BayesGibbs.posteriorFive ν q K f Xs β) atTop Ylim (fun _ ↦ P) P' ∧
      (∀ j, Integrable (fun ω' ↦ Ylim ω' j) P') ∧
      (∀ᶠ n : ℕ in atTop, ∀ j, Integrable
        (fun ω ↦ BayesGibbs.posteriorFive ν q K f Xs β n ω j) P) ∧
      (∀ j, Tendsto (fun n ↦ ∫ ω, BayesGibbs.posteriorFive ν q K f Xs β n ω j ∂P) atTop
        (𝓝 (∫ ω', Ylim ω' j ∂P'))) := by
  dsimp only
  haveI : Nonempty R.FaceDomain := by
    obtain ⟨u, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_pos.mpr hρ).ne'
    exact ⟨u⟩
  have hm := fun n ↦ BayesGibbs.measurable_posteriorFive ν q hKm hf hXm β n
  have hlim := J.tendsto.continuous_comp
    ((GaussianPosterior.continuous_compactFive R.essentialFaceMeasure hβ R.rlct_pos hρ C).comp
      R.continuous_chartFieldCM)
  have hdist := tendstoInDistribution_of_tendstoInMeasure_sub
    (BayesGibbs.posteriorFive ν q K f Xs β)
    (fun ω' ↦ GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
      (R.chartFieldCM (J.Ξlim ω')))
    hlim happrox (fun n ↦ (hm n).aemeasurable)
  have hcoord (j : Fin 5) : TendstoInDistribution
      (fun n ω ↦ BayesGibbs.posteriorFive ν q K f Xs β n ω j) atTop
      (fun ω' ↦ GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct C
        (R.chartFieldCM (J.Ξlim ω')) j) (fun _ ↦ P) P' :=
    hdist.continuous_comp (g := fun z : Fin 5 → ℝ ↦ z j) (continuous_apply j)
  refine ⟨hdist, fun j ↦ (hA j).integrable_limit (hcoord j), ?_,
    fun j ↦ (hA j).tendsto_integral (hcoord j)⟩
  exact Filter.eventually_all.mpr fun j ↦ (hA j).eventually_integrable
    (fun n ↦ ((measurable_pi_apply j).comp (hm n)).aestronglyMeasurable)

end ResolutionAtlas
end SingularLearningTheory
