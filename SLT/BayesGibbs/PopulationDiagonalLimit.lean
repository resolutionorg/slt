/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.GlobalTransport
public import SLT.BayesGibbs.HalfRadial.Measure
public import SLT.BayesGibbs.CompactPosterior.Ratios
public import Mathlib.Probability.Moments.Covariance
public import SLT.FreeEnergy.SamplewiseResolution
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# The population-square numerator

The population-square numerator as a case of the weighted limits: relatively finite variance
bounds the population square pointwise, and covariance plus squared mean gives the continuous
chart mark.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.BayesGibbs
variable {X : Type*} [MeasurableSpace X] {q : Measure X}
  {d : ℕ} {f : X → (Fin d → ℝ) → ℝ}
/-- The population second moment $E_q[f(x, w)^2]$ of $f(\cdot, w)$. Under relatively finite
variance it is at most a constant times $K(w)$, so it is bounded on a compact parameter set
(`SingularLearningTheory.BayesGibbs.populationSecondMoment_bounded_of_rfv`). -/
@[expose] noncomputable def populationSecondMoment (q : Measure X) (f : X → (Fin d → ℝ) → ℝ)
    (w : Fin d → ℝ) : ℝ := ∫ x, f x w ^ 2 ∂q

private theorem populationSecondMoment_nonneg (w : Fin d → ℝ) :
    0 ≤ populationSecondMoment q f w := integral_nonneg fun x ↦ sq_nonneg _

theorem measurable_populationSecondMoment [SFinite q]
    (hf : Measurable (Function.uncurry f)) : Measurable (populationSecondMoment q f) :=
  (hf.pow_const 2).stronglyMeasurable.integral_prod_left.measurable

theorem populationSecondMoment_bounded_of_rfv
    {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hK : ContinuousOn K W) {c : ℝ} (hc : 0 ≤ c)
    (hrfv : ∀ w ∈ W, populationSecondMoment q f w ≤ c * K w) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w ∈ W, |populationSecondMoment q f w| ≤ M := by
  obtain ⟨M, hM⟩ := hW.exists_bound_of_continuousOn hK
  refine ⟨c * max M 0, mul_nonneg hc (le_max_right _ _), fun w hw ↦ ?_⟩
  rw [abs_of_nonneg (populationSecondMoment_nonneg w)]
  have hKabs : |K w| ≤ M := by simpa only [Real.norm_eq_abs] using hM w hw
  have hKw : K w ≤ max M 0 :=
    (le_abs_self _).trans (hKabs.trans (le_max_left M 0))
  exact (hrfv w hw).trans (mul_le_mul_of_nonneg_left hKw hc)
end SingularLearningTheory.BayesGibbs

namespace SingularLearningTheory.ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
/-- The metric `Metric.Sigma.metricSpace` on the disjoint union of the chart cubes
`SingularLearningTheory.ResolutionAtlas.FaceDomain`, as a local instance. Its topology is the
disjoint-union topology. -/
noncomputable local instance populationDiagonalLimitMetric1 : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace

/-- The half monomial $u^{k_\alpha} = \prod_j u_j^{k_{\alpha j}}$ on the cube of each chart
$\alpha$, as a continuous function on `SingularLearningTheory.ResolutionAtlas.FaceDomain`. It is
the $q$-mean of the chart quotient $a_\alpha(\cdot, u)$
(`SingularLearningTheory.ResolutionAtlas.ResolvedLikelihood.mean`), so adding the product of its
values at $u$ and $v$ to the covariance kernel gives the uncentered kernel
`SingularLearningTheory.ResolutionAtlas.AnalyticResolvedLikelihood.rawCovarianceCM`. -/
@[expose] noncomputable def chartMeanCM : C(R.FaceDomain, ℝ) :=
  ⟨fun u ↦ ∏ j, (u.2 : Fin d → ℝ) j ^ R.k u.1 j,
    by
      apply continuous_sigma
      intro α
      change Continuous (fun u : cube d (R.b α) ↦
        ∏ j, (u : Fin d → ℝ) j ^ R.k α j)
      exact continuous_finsetProd _ fun j _ ↦
        ((continuous_apply j).comp continuous_subtype_val).pow _⟩

theorem integral_essentialFaceMeasure_congr_faces (F G : C(R.FaceDomain, ℝ))
    (h : ∀ α v, F (R.faceEmbedding α v) = G (R.faceEmbedding α v)) :
    (∫ u, F u ∂R.essentialFaceMeasure) = ∫ u, G u ∂R.essentialFaceMeasure := by
  rw [R.integral_essentialFaceMeasure, R.integral_essentialFaceMeasure]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs
  · congr 1
    apply integral_congr_ae
    exact Eventually.of_forall fun v ↦ by
      dsimp only
      rw [h α v]
  · rfl

section Statistical
variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {Xs : ℕ → Ω → X}
  {f : X → (Fin d → ℝ) → ℝ} {s : ℝ≥0∞}
  (L : R.AnalyticResolvedLikelihood s q f)
  (E : EmpiricalProcessLimit q (fun x (u : R.FaceDomain) ↦ L.a u.1 x u.2) Xs P P')
  (hE4 : E.MomentBound 4)

variable {R} in
/-- Continuous RAW feature kernel on the whole chart domain. -/
@[expose] noncomputable def AnalyticResolvedLikelihood.rawCovarianceCM :
    C(R.FaceDomain × R.FaceDomain, ℝ) :=
  ⟨fun z ↦ (E.covarianceKernel hE4).C z.1 z.2 + R.chartMeanCM z.1 * R.chartMeanCM z.2,
    (E.covarianceKernel hE4).continuous.add
      ((R.chartMeanCM.continuous.comp continuous_fst).mul
        (R.chartMeanCM.continuous.comp continuous_snd))⟩

variable {R} in
theorem AnalyticResolvedLikelihood.rawCovarianceCM_eq (u v : R.FaceDomain) :
    L.rawCovarianceCM E hE4 (u, v) = ∫ x, L.a u.1 x u.2 * L.a v.1 x v.2 ∂q := by
  have h := E.covarianceKernel_eq hE4 u v
  rw [covariance_eq_sub (L.memLp u.1 u.2) (L.memLp v.1 v.2)] at h
  simp only [Pi.mul_apply, L.mean] at h
  change (E.covarianceKernel hE4).C u v +
    (∏ j, (u.2 : Fin d → ℝ) j ^ R.k u.1 j) *
    (∏ j, (v.2 : Fin d → ℝ) j ^ R.k v.1 j) = _
  rw [h]
  ring

variable {R} in
theorem AnalyticResolvedLikelihood.rawCovarianceCM_faces (α β : R.ι) (v w : Fin d → ℝ) :
    L.rawCovarianceCM E hE4 (R.faceEmbedding α v, R.faceEmbedding β w) =
      (E.covarianceKernel hE4).C (R.faceEmbedding α v) (R.faceEmbedding β w) := by
  change _ + (∏ j, (R.primaryZero α v : Fin d → ℝ) j ^ R.k α j) * _ = _
  rw [R.monomial_primaryZero_eq_zero]
  ring

variable {R} in
/-- Exact product factorization, used by the global Q transport. -/
theorem AnalyticResolvedLikelihood.populationProduct_chart (α β : R.ι)
    (u : cube d (R.b α)) (v : cube d (R.b β)) :
    (∫ x, f x (R.g α u) * f x (R.g β v) ∂q) =
      ((∏ j, (u : Fin d → ℝ) j ^ R.k α j) *
       (∏ j, (v : Fin d → ℝ) j ^ R.k β j)) *
        L.rawCovarianceCM E hE4 (⟨α, u⟩, ⟨β, v⟩) := by
  rw [L.rawCovarianceCM_eq E hE4, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [L.factor α, L.factor β] with x hα hβ
  rw [hα u, hβ v]
  ring

variable {R} in
/-- Raw diagonal = centered covariance diagonal + square of the mean. -/
@[expose] noncomputable def AnalyticResolvedLikelihood.rawDiagonalMark : C(R.FaceDomain, ℝ) :=
  (L.rawCovarianceCM E hE4).comp ⟨fun u ↦ (u, u), continuous_id.prodMk continuous_id⟩

variable {R} in
theorem AnalyticResolvedLikelihood.rawDiagonalMark_eq (u : R.FaceDomain) :
    L.rawDiagonalMark E hE4 u = ∫ x, L.a u.1 x u.2 ^ 2 ∂q := by
  simpa only [AnalyticResolvedLikelihood.rawDiagonalMark, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, pow_two] using L.rawCovarianceCM_eq E hE4 u u

variable {R} in
theorem AnalyticResolvedLikelihood.rawDiagonalMark_face (α : R.ι) (v : Fin d → ℝ) :
    L.rawDiagonalMark E hE4 (R.faceEmbedding α v) =
      (E.covarianceKernel hE4).C (R.faceEmbedding α v) (R.faceEmbedding α v) :=
  L.rawCovarianceCM_faces E hE4 α α v v

variable {R} in
/-- Exact actual global-square factorization at every chart point. -/
theorem AnalyticResolvedLikelihood.populationSecondMoment_chart (α : R.ι) (u : cube d (R.b α)) :
    BayesGibbs.populationSecondMoment q f (R.g α u) =
      K (R.g α u) * L.rawDiagonalMark E hE4 ⟨α, u⟩ := by
  rw [BayesGibbs.populationSecondMoment, L.rawDiagonalMark_eq E hE4,
    R.monomial α u u.2, Finset.prod_pow_two_mul]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [L.factor α] with x hx
  rw [hx u]
  ring

variable {R} in
theorem AnalyticResolvedLikelihood.diagonal_radial_sum_eq_compact_numerator {β : ℝ} (hβ : 0 < β)
    (ζ : R.ChartFunctions) :
    (∑ α, if R.IsEssential α then
      R.chartRadialLimit β 1 α (ζ α)
        (R.chartWeightCM α * R.toChartFunctions (L.rawDiagonalMark E hE4) α) else 0) =
      ∫ u, (E.covarianceKernel hE4).C u u *
        frozenInner (R.rlct + 1) β (R.chartFieldCM ζ u) ∂R.essentialFaceMeasure := by
  let g := R.chartFieldCM ζ
  let raw := L.rawDiagonalMark E hE4
  let diag : C(R.FaceDomain, ℝ) :=
    ⟨fun u ↦ (E.covarianceKernel hE4).C u u, (E.covarianceKernel hE4).continuous_diag⟩
  let S : C(R.FaceDomain, ℝ) :=
    ⟨fun u ↦ frozenInner (R.rlct + 1) β (g u),
      (continuous_frozenInner (by linarith [R.rlct_pos]) hβ).comp g.continuous⟩
  have hrad := R.integral_radial_essentialFaceMeasure hβ
    (by linarith [R.rlct_pos] : 0 < R.rlct + 1) g raw
  have hw : ∀ α, R.markedChartWeight α raw =
      R.chartWeightCM α * R.toChartFunctions raw α := by
    intro α
    ext u
    rfl
  simp only [g, R.toChartFunctions_chartFieldCM, hw] at hrad
  rw [← hrad]
  exact R.integral_essentialFaceMeasure_congr_faces (raw * S) (diag * S)
    (fun α v ↦ by
      change L.rawDiagonalMark E hE4 (R.faceEmbedding α v) * _ = _
      rw [L.rawDiagonalMark_face E hE4]
      rfl)

variable {R} in
/-- Global D-numerator approximation. Original RFV supplies hrfv with
c equal to the reciprocal of its positive constant. -/
theorem EmpiricalProcessInput.normalized_populationSecondMoment_sub_compact_numerator
    {β : ℝ} (hβ : 0 < β) (J : R.EmpiricalProcessInput β P P')
    (hW : IsCompact W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f)) (hK : ContinuousOn K W)
    {c : ℝ} (hc : 0 ≤ c)
    (hrfv : ∀ w ∈ W, BayesGibbs.populationSecondMoment q f w ≤ c * K w) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) *
        J.weightedPartition (BayesGibbs.populationSecondMoment q f) n ω -
      ∫ u, (E.covarianceKernel hE4).C u u *
        frozenInner (R.rlct + 1) β (R.chartFieldCM (J.Ξ n ω) u) ∂R.essentialFaceMeasure)
      atTop 0 := by
  obtain ⟨M, hM0, hM⟩ := BayesGibbs.populationSecondMoment_bounded_of_rfv hW hK hc hrfv
  have hfactor : ∀ α (u : cube d (R.b α)),
      BayesGibbs.populationSecondMoment q f (R.g α u) =
        (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ (1 : ℝ) *
          R.toChartFunctions (L.rawDiagonalMark E hE4) α u := by
    intro α u
    rw [Real.rpow_one, ← R.monomial α u u.2]
    exact L.populationSecondMoment_chart E hE4 α u
  have h := J.weightedPartition_sub_limit_tendstoInMeasure hW.measurableSet hφ hφi hβ
    (BayesGibbs.measurable_populationSecondMoment hf) hM0 hM (by norm_num : (0 : ℝ) ≤ 1)
    (R.toChartFunctions (L.rawDiagonalMark E hE4)) hfactor
  exact h.congr (fun n ↦ Eventually.of_forall fun ω ↦ by
    rw [L.diagonal_radial_sum_eq_compact_numerator E hE4 hβ]) EventuallyEq.rfl

end Statistical
end SingularLearningTheory.ResolutionAtlas
