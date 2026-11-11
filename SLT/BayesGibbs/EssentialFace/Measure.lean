/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MeasureTheory.Constructions.BorelSpace.Sigma
public import SLT.BayesGibbs.CompactBase.Kernel
public import SLT.BayesGibbs.Covariance.Kernel
public import SLT.BayesGibbs.Weighted.ChartLimit
public import SLT.FreeEnergy.Discharge
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import SLT.FreeEnergy.Main
import SLT.SingularIntegrals.Resolution

/-!
# EssentialFaceMeasure

The canonical finite measure on essential primary faces.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal Classical

namespace SingularLearningTheory.ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The existing sigma of cubes, named only for readability. -/
abbrev FaceDomain := (α : R.ι) × cube d (R.b α)

/-- The metric `Metric.Sigma.metricSpace` on the disjoint union of the chart cubes
`SingularLearningTheory.ResolutionAtlas.FaceDomain`, as a local instance. Its topology is the
disjoint-union topology. -/
noncomputable local instance faceMetric : MetricSpace (R.FaceDomain) := Metric.Sigma.metricSpace


/-- The chart normalization already appearing in chartLimit; NNReal keeps the
finite-measure scalar instance automatic. -/
@[expose] noncomputable def faceCoefficient (α : R.ι) : ℝ≥0 :=
  ⟨R.chartGamma α / R.b α ^ R.chartMult α,
    (div_pos (R.chartGamma_pos α) (pow_pos (R.b_pos α) _)).le⟩

/-- Lebesgue measure on the cube $[0, b_\alpha]^d$ of chart `α`, with density the trace weight
$v^\mu \tilde\varphi_\alpha(0, v)$ (`SingularLearningTheory.ResolutionAtlas.traceWeight`). Its
total mass is the essential trace mass of the chart
(`SingularLearningTheory.ResolutionAtlas.faceSourceMeasure_univ`). -/
@[expose] noncomputable def faceSourceMeasure (α : R.ι) : Measure (Fin d → ℝ) :=
  (volume.restrict (cube d (R.b α))).withDensity (fun v ↦ ENNReal.ofReal (R.traceWeight α v))

theorem faceSourceMeasure_univ (α : R.ι) :
    R.faceSourceMeasure α univ = ENNReal.ofReal (R.essentialTraceMass α) := by
  have h0 : ∀ᵐ v ∂(volume.restrict (cube d (R.b α))), 0 ≤ R.traceWeight α v :=
    (ae_restrict_mem measurableSet_Icc).mono
      fun v hv ↦ R.traceWeight_nonneg α hv
  rw [faceSourceMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (R.integrableOn_traceWeight α) h0,
    ← R.essentialTraceMass_eq]

@[expose] instance faceSourceMeasure_finite (α : R.ι) : IsFiniteMeasure (R.faceSourceMeasure α) :=
  ⟨by rw [R.faceSourceMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- The point $(0, v)$ of the face of chart `α` where the primary coordinates vanish
(`SingularLearningTheory.ResolutionAtlas.primaryZero`), as a point of
`SingularLearningTheory.ResolutionAtlas.FaceDomain`. -/
@[expose] noncomputable def faceEmbedding (α : R.ι) (v : Fin d → ℝ) : R.FaceDomain :=
  ⟨α, R.primaryZero α v⟩

theorem continuous_faceEmbedding (α : R.ι) : Continuous (R.faceEmbedding α) :=
  continuous_sigmaMk.comp (R.continuous_primaryZero α)

/-- The trace-weighted measure on the face of chart `α`: the image of
`SingularLearningTheory.ResolutionAtlas.faceSourceMeasure` under
`SingularLearningTheory.ResolutionAtlas.faceEmbedding`, a finite measure on
`SingularLearningTheory.ResolutionAtlas.FaceDomain`. -/
@[expose] noncomputable def faceChartMeasure (α : R.ι) : Measure (R.FaceDomain) :=
  (R.faceSourceMeasure α).map (R.faceEmbedding α)

@[expose] instance faceChartMeasure_finite (α : R.ι) : IsFiniteMeasure (R.faceChartMeasure α) := by
  unfold faceChartMeasure
  infer_instance

/-- The part of `SingularLearningTheory.ResolutionAtlas.essentialFaceMeasure` on chart `α`: the
face measure `SingularLearningTheory.ResolutionAtlas.faceChartMeasure` scaled by
$\gamma_\alpha / b_\alpha^{m_\alpha}$ (`SingularLearningTheory.ResolutionAtlas.faceCoefficient`)
if the chart is essential, and zero otherwise. -/
@[expose] noncomputable def essentialFaceComponent (α : R.ι) : Measure (R.FaceDomain) :=
  open scoped Classical in
  if R.IsEssential α then R.faceCoefficient α • R.faceChartMeasure α else 0

@[expose] instance essentialFaceComponent_finite (α : R.ι) : IsFiniteMeasure
    (R.essentialFaceComponent α) := by
  classical
  unfold essentialFaceComponent
  split_ifs <;> infer_instance

/-- The canonical finite base measure of the essential-face posterior. -/
@[expose] noncomputable def essentialFaceMeasure : Measure
    (R.FaceDomain) := ∑ α, R.essentialFaceComponent α

@[expose] instance essentialFaceMeasure_finite : IsFiniteMeasure R.essentialFaceMeasure := by
  unfold essentialFaceMeasure
  infer_instance

/-- Integration against one face is precisely the trace integral. -/
theorem integral_faceChartMeasure (α : R.ι) (F : C(R.FaceDomain, ℝ)) :
    ∫ u, F u ∂R.faceChartMeasure α =
      ∫ v in cube d (R.b α), R.traceWeight α v * F (R.faceEmbedding α v) := by
  rw [faceChartMeasure, integral_map (R.continuous_faceEmbedding α).measurable.aemeasurable
    F.continuous.measurable.aestronglyMeasurable]
  rw [faceSourceMeasure, integral_withDensity_eq_integral_toReal_smul₀
    (R.integrableOn_traceWeight α).aestronglyMeasurable.aemeasurable.ennreal_ofReal
    (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  rw [ENNReal.toReal_ofReal (R.traceWeight_nonneg α hv), smul_eq_mul]

/-- The generic integration formula is the main seam for all weighted insertions. -/
theorem integral_essentialFaceMeasure (F : C(R.FaceDomain, ℝ)) :
    ∫ u, F u ∂R.essentialFaceMeasure =
      ∑ α, if R.IsEssential α then
        R.chartGamma α / R.b α ^ R.chartMult α *
          ∫ v in cube d (R.b α), R.traceWeight α v * F (R.faceEmbedding α v) else 0 := by
  classical
  have hI : ∀ α ∈ (Finset.univ : Finset R.ι), Integrable F (R.essentialFaceComponent α) :=
    fun α _ ↦ Continuous.integrable_of_compactSpace _ F.continuous
  rw [essentialFaceMeasure, integral_finsetSum_measure hI]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : R.IsEssential α
  · rw [essentialFaceComponent, if_pos hα, if_pos hα, integral_smul_nnreal_measure,
      R.integral_faceChartMeasure]
    rfl
  · simp [essentialFaceComponent, hα]

/-- Exact denominator identity, with the book-sign field ζ=-Ψ. -/
theorem compactD_essentialFaceMeasure {β : ℝ} (hβ : 0 < β) (ζ : C(R.FaceDomain, ℝ)) :
    GaussianPosterior.compactD β R.rlct R.essentialFaceMeasure ζ =
      R.limitFunctional β (R.toChartFunctions ζ) := by
  let F : C(R.FaceDomain, ℝ) :=
    ⟨fun u ↦ frozenInner R.rlct β (ζ u), (continuous_frozenInner R.rlct_pos hβ).comp ζ.continuous⟩
  change (∫ u, F u ∂R.essentialFaceMeasure) = _
  rw [R.integral_essentialFaceMeasure]
  unfold limitFunctional
  apply Finset.sum_congr rfl
  intro α _
  split_ifs
  · rfl
  · rfl

/-- Continuous chart amplitude weight times a continuous mark. -/
@[expose] noncomputable def markedChartWeight (α : R.ι) (mark : C(R.FaceDomain, ℝ)) :
    C(cube d (R.b α), ℝ) :=
  ⟨fun u ↦ R.weight α u * mark ⟨α, u⟩,
    (continuousOn_iff_continuous_domRestrict.mp (R.weight_continuousOn α)).mul
      (mark.continuous.comp continuous_sigmaMk)⟩

@[simp] theorem markedChartWeight_apply (α : R.ι) (mark : C(R.FaceDomain, ℝ))
    (u : cube d (R.b α)) : R.markedChartWeight α mark u = R.weight α u * mark ⟨α, u⟩ := rfl

/-- The full marked radial limit equals a compact-base integral. p=0,1/2,1
supply the denominator, first insertion, and second insertion respectively. -/
theorem integral_radial_essentialFaceMeasure {β p : ℝ} (hβ : 0 < β)
    (hp : 0 < R.rlct + p) (ζ mark : C(R.FaceDomain, ℝ)) :
    (∫ u, mark u * frozenInner (R.rlct + p) β (ζ u) ∂R.essentialFaceMeasure) =
      ∑ α, if R.IsEssential α then
        R.chartRadialLimit β p α (R.toChartFunctions ζ α) (R.markedChartWeight α mark) else 0 := by
  let F : C(R.FaceDomain, ℝ) :=
    ⟨fun u ↦ mark u * frozenInner (R.rlct + p) β (ζ u),
      mark.continuous.mul ((continuous_frozenInner hp hβ).comp ζ.continuous)⟩
  change (∫ u, F u ∂R.essentialFaceMeasure) = _
  rw [R.integral_essentialFaceMeasure]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs
  · unfold chartRadialLimit
    congr 1
    apply integral_congr_ae
    filter_upwards with v
    change R.traceWeight α v *
      (mark (R.faceEmbedding α v) * frozenInner (R.rlct + p) β (ζ (R.faceEmbedding α v))) = _
    simp only [traceWeight, markedChartWeight_apply,
      toChartFunctions_apply, faceEmbedding, frozenInner]
    ring
  · rfl

/-- Every primary face kills the chart's half-monomial. -/
theorem monomial_primaryZero_eq_zero (α : R.ι) (v : Fin d → ℝ) :
    (∏ j, (R.primaryZero α v : Fin d → ℝ) j ^ R.k α j) = 0 := by
  obtain ⟨j, hj⟩ := R.primary_nonempty α
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  simp [primaryZero, hj, (R.k_pos_of_mem_primary hj).ne']

section Covariance
variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {q : Measure X} {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure q] [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}

theorem ResolvedLikelihood.mean_primaryZero (L : R.ResolvedLikelihood q f)
    (α : R.ι) (v : Fin d → ℝ) : ∫ x, L.a α x (R.primaryZero α v) ∂q = 0 := by
  rw [L.mean, R.monomial_primaryZero_eq_zero]

variable {R} in
/-- General covariance becomes the uncentered feature product only on the faces.
There is no constant-diagonal covariance hypothesis. -/
theorem ResolvedLikelihood.covarianceKernel_face_eq (L : R.ResolvedLikelihood q f)
    (E : EmpiricalProcessLimit q (fun x (u : R.FaceDomain) ↦ L.a u.1 x u.2) Xs P P')
    (hE4 : E.MomentBound 4) (α β : R.ι) (v w : Fin d → ℝ) :
    (E.covarianceKernel hE4).C (R.faceEmbedding α v) (R.faceEmbedding β w) =
      ∫ x, L.a α x (R.primaryZero α v) * L.a β x (R.primaryZero β w) ∂q := by
  rw [E.covarianceKernel_eq]
  change cov[fun x ↦ L.a α x (R.primaryZero α v),
    fun x ↦ L.a β x (R.primaryZero β w); q] = _
  simp only [covariance, ResolvedLikelihood.mean_primaryZero R L, sub_zero]

end Covariance
end SingularLearningTheory.ResolutionAtlas

namespace SingularLearningTheory.NondegenerateResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : NondegenerateResolutionAtlas K φ W)

/-- The metric `Metric.Sigma.metricSpace` on the disjoint union of the chart cubes
`SingularLearningTheory.ResolutionAtlas.FaceDomain`, as a local instance. Its topology is the
disjoint-union topology. -/
noncomputable local instance : MetricSpace (R.toResolutionAtlas.FaceDomain) := Metric.Sigma.metricSpace

/-- Positive trace mass makes the compact base nonzero. -/
theorem essentialFaceMeasure_ne_zero : R.toResolutionAtlas.essentialFaceMeasure ≠ 0 := by
  have hpos := R.limitFunctional_pos (β := 1) zero_lt_one
    (R.toChartFunctions (0 : C(R.toResolutionAtlas.FaceDomain, ℝ)))
  rw [← R.toResolutionAtlas.compactD_essentialFaceMeasure zero_lt_one] at hpos
  intro hzero
  simp [GaussianPosterior.compactD, hzero] at hpos

end SingularLearningTheory.NondegenerateResolutionAtlas
