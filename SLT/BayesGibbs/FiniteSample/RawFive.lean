/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.GibbsLimits
public import SLT.BayesGibbs.GlobalPairNumerator
public import SLT.BayesGibbs.CompactPosterior.Ratios
import SLT.BayesGibbs.CompactPosterior.RatioProbability
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# The five raw posterior integrals

The five posterior observables are ratios of five raw integrals against
$e^{-n\beta K_n(w)}\varphi(w)\,dw$ on $W$: the evidence $Z$, the numerator $T$ of $K$, the
numerator $H$ of the centered loss $\sqrt n\,(K - K_n)$, the numerator $D$ of the population second
moment $E_q[f(x, w)^2]$ and the pair numerator $Q$ of the population product
$E_q[f(x, w) f(x, w')]$. This module defines them, scaled by powers of $n$ and $\log n$, as
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.finiteSampleRawFive` and proves them
measurable. Under relatively finite variance each one approaches the compact raw integral
`SingularLearningTheory.GaussianPosterior.compactRaw` at the chart processes in probability, and so the
normalized ratios approach `SingularLearningTheory.GaussianPosterior.compactFive`.

## Main results

* `SingularLearningTheory.ResolutionAtlas.continuous_chartFieldCM`: the chart field on the face domain
  depends continuously on the chart family.
* `EmpiricalProcessInput.finiteSampleRawFive_sub_compactRaw_tendstoInMeasure`: each scaled raw
  integral minus its compact counterpart tends to zero in probability.
* `EmpiricalProcessInput.normalize_finiteSampleRawFive_sub_compactFive_tendstoInMeasure`: the
  normalized raw integrals minus `SingularLearningTheory.GaussianPosterior.compactFive` tend to zero in
  probability.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
-- The metric `Metric.Sigma.metricSpace` on the disjoint union of the chart cubes
-- `SingularLearningTheory.ResolutionAtlas.FaceDomain`; its topology is the disjoint-union topology.
attribute [local instance] Metric.Sigma.metricSpace

/-- The finite chart-family norm controls the continuous sigma-domain norm. -/
theorem continuous_chartFieldCM : Continuous R.chartFieldCM := by
  have h : LipschitzWith 1 R.chartFieldCM := by
    apply LipschitzWith.of_dist_le_mul
    intro ζ η
    rw [NNReal.coe_one, one_mul, dist_eq_norm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
    intro u
    change ‖(ζ - η) u.1 u.2‖ ≤ ‖ζ - η‖
    exact ((ζ - η) u.1).norm_coe_le_norm u.2 |>.trans (norm_le_pi_norm _ u.1)
  exact h.continuous

/-- The ordinary radial degree-one chart sum is the compact T numerator. -/
theorem radial_one_sum_eq_compactRaw
    {β : ℝ} (hβ : 0 < β) (hρ : R.essentialFaceMeasure ≠ 0)
    (C : PSDKernel R.FaceDomain) (ζ : R.ChartFunctions) :
    (∑ α, if R.IsEssential α then
      R.chartRadialLimit β 1 α (ζ α) (R.chartWeightCM α) else 0) =
      GaussianPosterior.compactRaw R.essentialFaceMeasure β R.rlct C (R.chartFieldCM ζ) 1 := by
  haveI : Nonempty R.FaceDomain := by
    obtain ⟨u, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_pos.mpr hρ).ne'
    exact ⟨u⟩
  rw [GaussianPosterior.compactRaw_first_numerator _ hβ R.rlct_pos hρ]
  have h := R.integral_radial_essentialFaceMeasure hβ
    (by linarith [R.rlct_pos] : 0 < R.rlct + 1) (R.chartFieldCM ζ)
    (1 : C(R.FaceDomain, ℝ))
  have hw : ∀ α, R.markedChartWeight α (1 : C(R.FaceDomain, ℝ)) = R.chartWeightCM α := by
    intro α
    ext u
    simp only [markedChartWeight_apply, ContinuousMap.one_apply, mul_one, chartWeightCM_apply]
  simpa only [ContinuousMap.one_apply, one_mul, R.toChartFunctions_chartFieldCM, hw] using h.symm

/-- The self-marked degree-one-half chart sum is the compact H numerator. -/
theorem radial_self_sum_eq_compactRaw
    {β : ℝ} (hβ : 0 < β) (hρ : R.essentialFaceMeasure ≠ 0)
    (C : PSDKernel R.FaceDomain) (ζ : R.ChartFunctions) :
    (∑ α, if R.IsEssential α then R.chartRadialLimit β (1 / 2) α (ζ α)
      (R.chartWeightCM α * ζ α) else 0) =
      GaussianPosterior.compactRaw R.essentialFaceMeasure β R.rlct C (R.chartFieldCM ζ) 2 := by
  haveI : Nonempty R.FaceDomain := by
    obtain ⟨u, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_pos.mpr hρ).ne'
    exact ⟨u⟩
  rw [GaussianPosterior.compactRaw_self_numerator _ hβ R.rlct_pos hρ]
  have h := R.integral_radial_essentialFaceMeasure hβ
    (by linarith [R.rlct_pos] : 0 < R.rlct + 1 / 2) (R.chartFieldCM ζ) (R.chartFieldCM ζ)
  have hw : ∀ α, R.markedChartWeight α (R.chartFieldCM ζ) = R.chartWeightCM α * ζ α := by
    intro α
    ext u
    rfl
  simpa only [R.toChartFunctions_chartFieldCM, hw] using h.symm

namespace EmpiricalProcessInput
variable {R} {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (J : R.EmpiricalProcessInput β P P')

/-- All-n measurability for deterministic or same-sample weighted numerators. -/
theorem aemeasurable_weightedPartition
    (hφi : IntegrableOn φ W) {a : Ω → (Fin d → ℝ) → ℝ}
    (ha : Measurable (Function.uncurry a)) (n : ℕ) :
    AEMeasurable (fun ω ↦ J.weightedPartition (a ω) n ω) P := by
  have h : AEStronglyMeasurable
      (fun p : Ω × (Fin d → ℝ) ↦ a p.1 p.2 *
        Real.exp (-(n * β * J.Kn n p.1 p.2)) * φ p.2) (P.prod (volume.restrict W)) :=
    (ha.mul ((J.Kn_measurable n).const_mul _).neg.exp).aestronglyMeasurable.mul
      hφi.aestronglyMeasurable.comp_snd
  exact h.integral_prod_right'.aemeasurable

/-- The double numerator is measurable despite the prior density only being
integrable, rather than globally measurable. -/
theorem aemeasurable_pairWeightedPartition
    (hφi : IntegrableOn φ W) {B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ}
    (hB : Measurable B) (n : ℕ) : AEMeasurable (J.pairWeightedPartition B n) P := by
  let μ := (volume.restrict W).prod (volume.restrict W)
  have hφφ : AEStronglyMeasurable
      (fun z : (Fin d → ℝ) × (Fin d → ℝ) ↦ φ z.1 * φ z.2) μ :=
    hφi.aestronglyMeasurable.comp_fst.mul hφi.aestronglyMeasurable.comp_snd
  have he₁ : Measurable (fun p : Ω × ((Fin d → ℝ) × (Fin d → ℝ)) ↦
      Real.exp (-(n * β * J.Kn n p.1 p.2.1))) :=
    (((J.Kn_measurable n).comp
      (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).const_mul _).neg.exp
  have he₂ : Measurable (fun p : Ω × ((Fin d → ℝ) × (Fin d → ℝ)) ↦
      Real.exp (-(n * β * J.Kn n p.1 p.2.2))) :=
    (((J.Kn_measurable n).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).const_mul _).neg.exp
  have h : AEStronglyMeasurable
      (fun p : Ω × ((Fin d → ℝ) × (Fin d → ℝ)) ↦
        B p.2 * Real.exp (-(n * β * J.Kn n p.1 p.2.1)) *
        Real.exp (-(n * β * J.Kn n p.1 p.2.2)) * (φ p.2.1 * φ p.2.2)) (P.prod μ) :=
    (((hB.comp measurable_snd).mul he₁).mul he₂).aestronglyMeasurable.mul hφφ.comp_snd
  apply h.integral_prod_right'.aemeasurable.congr
  exact .of_forall fun ω ↦ by
    apply integral_congr_ae
    exact .of_forall fun z ↦ by dsimp [pairWeightedPartition]; ring

/-- The five genuinely finite-sample raw integrals, in the same order as
`GaussianPosterior.compactRaw`: Z,T,H,D,Q. -/
@[expose] noncomputable def finiteSampleRawFive {X : Type*} [MeasurableSpace X]
    (q : Measure X) (f : X → (Fin d → ℝ) → ℝ) (n : ℕ) (ω : Ω) : Fin 5 → ℝ :=
  ![(n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * J.normalizedEvidence n ω,
    (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) * J.weightedPartition K n ω,
    R.halfRadialScale n *
      J.weightedPartition (fun w ↦ Real.sqrt n * (K w - J.Kn n ω w)) n ω,
    (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) *
      J.weightedPartition (BayesGibbs.populationSecondMoment q f) n ω,
    R.halfRadialScale n ^ 2 * J.pairWeightedPartition (BayesGibbs.populationProduct q f) n ω]

theorem aemeasurable_finiteSampleRawFive {X : Type*} [MeasurableSpace X]
    {q : Measure X} [SFinite q] {f : X → (Fin d → ℝ) → ℝ}
    (hφi : IntegrableOn φ W) (hf : Measurable (Function.uncurry f)) (hK : Measurable K)
    (n : ℕ) : AEMeasurable (J.finiteSampleRawFive q f n) P := by
  apply aemeasurable_pi_lambda
  intro j
  fin_cases j
  · have h := J.aemeasurable_weightedPartition hφi (a := fun _ _ ↦ (1 : ℝ)) measurable_const n
    change AEMeasurable
        (fun ω ↦ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * J.normalizedEvidence n ω) P
    simpa only [weightedPartition, normalizedEvidence, one_mul] using h.const_mul
      ((n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1))
  · exact (J.aemeasurable_weightedPartition hφi (a := fun _ w ↦ K w) (hK.comp measurable_snd) n).const_mul _
  · exact (J.aemeasurable_weightedPartition hφi
      (((hK.comp measurable_snd).sub (J.Kn_measurable n)).const_mul _) n).const_mul _
  · exact (J.aemeasurable_weightedPartition hφi
      (a := fun _ w ↦ BayesGibbs.populationSecondMoment q f w)
      ((BayesGibbs.measurable_populationSecondMoment hf).comp measurable_snd) n).const_mul _
  · exact (J.aemeasurable_pairWeightedPartition hφi
      (BayesGibbs.measurable_populationProduct hf) n).const_mul _

end EmpiricalProcessInput

section Statistical
variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {Xs : ℕ → Ω → X}
  {f : X → (Fin d → ℝ) → ℝ} {s : ℝ≥0∞}
  (L : R.AnalyticResolvedLikelihood s q f)
  (E : EmpiricalProcessLimit q (fun x (u : R.FaceDomain) ↦ L.a u.1 x u.2) Xs P P')
  (hE4 : E.MomentBound 4)

variable {R} in
/-- All five actual raw coordinates approximate the same current empirical
field. Tail, diagonal, and pair terms are included in the inputs. -/
theorem EmpiricalProcessInput.finiteSampleRawFive_sub_compactRaw_tendstoInMeasure
    {β : ℝ} (hβ : 0 < β) (J : R.EmpiricalProcessInput β P P')
    (hρ : R.essentialFaceMeasure ≠ 0)
    (hW : IsCompact W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f)) (hKm : Measurable K) (hK : ContinuousOn K W)
    (hK0 : ∀ w ∈ W, 0 ≤ K w)
    (h2 : ∀ w ∈ W, Integrable (fun x ↦ f x w ^ 2) q)
    {c : ℝ} (hc : 0 ≤ c)
    (hrfv : ∀ w ∈ W, BayesGibbs.populationSecondMoment q f w ≤ c * K w)
    {Λ : ℕ → Ω → ℝ} (hΛ0 : ∀ n ω, 0 ≤ Λ n ω)
    (hΛtight : ∀ η > 0, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | C < |Λ n ω|} ≤ ENNReal.ofReal η)
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P,
      ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
        Real.sqrt n * |J.Kn n ω w - K w| ≤ Λ n ω * Real.sqrt (K w)) :
    ∀ j, TendstoInMeasure P (fun (n : ℕ) ω ↦ J.finiteSampleRawFive q f n ω j -
      GaussianPosterior.compactRaw R.essentialFaceMeasure β R.rlct
        (E.covarianceKernel hE4) (R.chartFieldCM (J.Ξ n ω)) j) atTop 0 := by
  haveI : Nonempty R.FaceDomain := by
    obtain ⟨u, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_pos.mpr hρ).ne'
    exact ⟨u⟩
  obtain ⟨B, hB⟩ := hW.exists_bound_of_continuousOn hK
  have hKB : ∀ w ∈ W, K w ≤ max B 0 := by
    intro w hw
    have hab : |K w| ≤ B := by simpa only [Real.norm_eq_abs] using hB w hw
    exact (le_abs_self _).trans (hab.trans (le_max_left _ _))
  have hKBae : ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
      K w ≤ max B 0 := (withDensity_absolutelyContinuous _ _).ae_le
        ((ae_restrict_mem hW.measurableSet).mono fun w hw ↦ hKB w hw)
  intro j
  fin_cases j
  · have h := J.tendstoInMeasure_normalizedEvidence_sub_limitFunctional hW.measurableSet hφ hφi hβ
      (fun α _ ↦ R.exists_lipschitzOnWith_weight α)
    change TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * J.normalizedEvidence n ω -
      GaussianPosterior.compactD β R.rlct R.essentialFaceMeasure (R.chartFieldCM (J.Ξ n ω))) atTop 0
    simpa only [R.compactD_essentialFaceMeasure hβ,
      R.toChartFunctions_chartFieldCM] using h
  · have h := J.population_loss_numerator_sub_limit_tendstoInMeasure hW.measurableSet hφ hφi hβ
      hKm hK0 (le_max_right B 0) hKB
    exact h.congr (fun n ↦ .of_forall fun ω ↦ by
      rw [R.radial_one_sum_eq_compactRaw hβ hρ (E.covarianceKernel hE4)]
      rfl) EventuallyEq.rfl
  · have h := J.centered_loss_numerator_sub_limit_tendstoInMeasure hW.measurableSet hφ hφi hβ
      hKm hKBae hΛ0 hΛtight he
    exact h.congr (fun n ↦ .of_forall fun ω ↦ by
      rw [R.radial_self_sum_eq_compactRaw hβ hρ (E.covarianceKernel hE4)]
      rfl) EventuallyEq.rfl
  · have h := J.normalized_populationSecondMoment_sub_compact_numerator L E hE4 hβ
      hW hφ hφi hf hK hc hrfv
    exact h.congr (fun n ↦ .of_forall fun ω ↦ by
      change (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) *
        J.weightedPartition (BayesGibbs.populationSecondMoment q f) n ω - _ =
        (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) *
        J.weightedPartition (BayesGibbs.populationSecondMoment q f) n ω -
          GaussianPosterior.compactRaw R.essentialFaceMeasure β R.rlct
            (E.covarianceKernel hE4) (R.chartFieldCM (J.Ξ n ω)) 3
      rw [GaussianPosterior.compactRaw_diag_numerator _ hβ R.rlct_pos hρ]) EventuallyEq.rfl
  · exact J.normalized_populationProduct_sub_compactQnum L E hE4 hβ
      hW hφ hφi hf hK h2 hc hrfv

variable {R} in
/-- The raw posterior ratios approximate the compact five-vector jointly. -/
theorem EmpiricalProcessInput.normalize_finiteSampleRawFive_sub_compactFive_tendstoInMeasure
    {β : ℝ} (hβ : 0 < β) (J : R.EmpiricalProcessInput β P P')
    (hρ : R.essentialFaceMeasure ≠ 0)
    (hW : IsCompact W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f)) (hKm : Measurable K) (hK : ContinuousOn K W)
    (hK0 : ∀ w ∈ W, 0 ≤ K w)
    (h2 : ∀ w ∈ W, Integrable (fun x ↦ f x w ^ 2) q)
    {c : ℝ} (hc : 0 ≤ c)
    (hrfv : ∀ w ∈ W, BayesGibbs.populationSecondMoment q f w ≤ c * K w)
    {Λ : ℕ → Ω → ℝ} (hΛ0 : ∀ n ω, 0 ≤ Λ n ω)
    (hΛtight : ∀ η > 0, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | C < |Λ n ω|} ≤ ENNReal.ofReal η)
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P,
      ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
        Real.sqrt n * |J.Kn n ω w - K w| ≤ Λ n ω * Real.sqrt (K w)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      GaussianPosterior.normalizeRaw (J.finiteSampleRawFive q f n ω) -
      GaussianPosterior.compactFive R.essentialFaceMeasure β R.rlct
        (E.covarianceKernel hE4) (R.chartFieldCM (J.Ξ n ω))) atTop 0 := by
  haveI : Nonempty R.FaceDomain := by
    obtain ⟨u, _⟩ := nonempty_of_measure_ne_zero (Measure.measure_univ_pos.mpr hρ).ne'
    exact ⟨u⟩
  apply tendstoInMeasure_finite_pi_zero
  exact GaussianPosterior.normalizedRaw_sub_compactFive_tendstoInMeasure
    R.essentialFaceMeasure hβ R.rlct_pos hρ (E.covarianceKernel hE4)
    (J.tendsto.continuous_comp R.continuous_chartFieldCM) (J.finiteSampleRawFive q f)
    (J.aemeasurable_finiteSampleRawFive hφi hf hKm)
    (J.finiteSampleRawFive_sub_compactRaw_tendstoInMeasure L E hE4 hβ hρ
      hW hφ hφi hf hKm hK hK0 h2 hc hrfv hΛ0 hΛtight he)

end Statistical
end SingularLearningTheory.ResolutionAtlas
