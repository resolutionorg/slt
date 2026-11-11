/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.EssentialFace.Measure
public import SLT.BayesGibbs.Weighted.ContinuousChart
import SLT.FreeEnergy.Main

/-!
# The half-radial measure

The half-radial measure is finite and positive, and has the normalization
`n^(λ+1/2)/(log n)^(m-1)`.
-/

public section

namespace SingularLearningTheory.ResolutionAtlas

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The metric `Metric.Sigma.metricSpace` on the disjoint union
`SingularLearningTheory.ResolutionAtlas.FaceDomain` of the chart cubes, local to this module. Its
topology is the disjoint-union topology. -/
noncomputable local instance halfRadialMeasureMetric1 : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace

/-- Assemble the chart family using the disjoint-union topology. -/
@[expose] noncomputable def chartFieldCM (ζ : R.ChartFunctions) : C(R.FaceDomain, ℝ) :=
  ⟨fun u ↦ ζ u.1 u.2, continuous_sigma fun α ↦ (ζ α).continuous⟩

@[simp] theorem toChartFunctions_chartFieldCM (ζ : R.ChartFunctions) :
    R.toChartFunctions (R.chartFieldCM ζ) = ζ := by
  funext α
  ext u
  rfl

/-- The scale $n^{\lambda + 1/2}/(\log n)^{m-1}$ of the half-radial measure at sample size $n$,
where $\lambda$ is `SingularLearningTheory.ResolutionAtlas.rlct` and $m$ is
`SingularLearningTheory.ResolutionAtlas.mult`. Its square is the scale of the pair numerator
(`SingularLearningTheory.ResolutionAtlas.halfRadialScale_sq`). -/
@[expose] noncomputable def halfRadialScale (n : ℕ) : ℝ :=
  (n : ℝ) ^ (R.rlct + 1 / 2) / Real.log n ^ (R.mult - 1)

theorem halfRadialScale_nonneg (n : ℕ) : 0 ≤ R.halfRadialScale n :=
  div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    (pow_nonneg (Real.log_natCast_nonneg n) _)

/-- The map from $\mathbb{R}^d$ to the summand of chart $\alpha$ in
`SingularLearningTheory.ResolutionAtlas.FaceDomain` that clamps a point onto the chart cube
(`SingularLearningTheory.ResolutionAtlas.clamp`). Unlike
`SingularLearningTheory.ResolutionAtlas.faceEmbedding`, it keeps the primary coordinates. -/
@[expose] noncomputable def fullChartEmbedding (α : R.ι) (u : Fin d → ℝ) : R.FaceDomain :=
  ⟨α, R.clamp α u⟩

theorem continuous_fullChartEmbedding (α : R.ι) : Continuous (R.fullChartEmbedding α) :=
  continuous_sigmaMk.comp (R.continuous_clamp α)

/-- The density of the half-radial measure on the cube of chart $\alpha$, at sample size $n$ and
chart field $\zeta$:
$s_n\,(u^{2k})^{1/2}\,e^{-n\beta u^{2k} + \sqrt{n}\,\beta\,u^{k}\zeta(u)}\,u^{h}\,w_\alpha(u)$,
where $s_n$ is `SingularLearningTheory.ResolutionAtlas.halfRadialScale`, $k$ and $h$ are the
exponents of the chart and $w_\alpha$ is its weight. The point is clamped onto the cube before
$\zeta$ and $w_\alpha$ are evaluated (`SingularLearningTheory.ResolutionAtlas.clamp`). -/
@[expose] noncomputable def halfRadialSourceDensity (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) (u : Fin d → ℝ) : ℝ :=
  R.halfRadialScale n *
    ((∏ j, u j ^ (2 * R.k α j)) ^ (1 / 2 : ℝ) *
      Real.exp (-((n : ℝ) * β * ∏ j, u j ^ (2 * R.k α j)) +
        Real.sqrt n * β * (∏ j, u j ^ R.k α j) * ζ (R.clamp α u)) *
      (∏ j, u j ^ (R.h α j : ℝ)) * R.markedChartWeight α 1 (R.clamp α u))

theorem integrable_halfRadialSourceDensity (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) :
    IntegrableOn (R.halfRadialSourceDensity α β n ζ) (cube d (R.b α)) :=
  (R.integrable_chartRadialInsertion α β n (by norm_num : (0 : ℝ) ≤ 1 / 2)
    ζ (R.markedChartWeight α 1)).const_mul _

theorem halfRadialSourceDensity_nonneg (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) {u : Fin d → ℝ} (hu : u ∈ cube d (R.b α)) :
    0 ≤ R.halfRadialSourceDensity α β n ζ u := by
  have hk : 0 ≤ ∏ j, u j ^ (2 * R.k α j) :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu.1 j) _
  have hh : 0 ≤ ∏ j, u j ^ (R.h α j : ℝ) :=
    Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _
  have hw : 0 ≤ R.markedChartWeight α (1 : C(R.FaceDomain, ℝ)) (R.clamp α u) := by
    simpa only [markedChartWeight_apply, ContinuousMap.one_apply, mul_one] using
      R.weight_nonneg α _ (R.clamp α u).2
  exact mul_nonneg (R.halfRadialScale_nonneg n)
    (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg hk _) (Real.exp_pos _).le) hh) hw)

/-- The finite measure on $\mathbb{R}^d$ with density
`SingularLearningTheory.ResolutionAtlas.halfRadialSourceDensity` against Lebesgue measure on the
cube of chart $\alpha$. -/
@[expose] noncomputable def halfRadialSourceMeasure (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) : Measure (Fin d → ℝ) :=
  (volume.restrict (cube d (R.b α))).withDensity
    (fun u ↦ ENNReal.ofReal (R.halfRadialSourceDensity α β n ζ u))

@[expose] instance halfRadialSourceMeasure_finite (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) : IsFiniteMeasure (R.halfRadialSourceMeasure α β n ζ) := by
  have hI := R.integrable_halfRadialSourceDensity α β n ζ
  have h0 : 0 ≤ᵐ[volume.restrict (cube d (R.b α))] R.halfRadialSourceDensity α β n ζ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact R.halfRadialSourceDensity_nonneg α β n ζ hu
  exact isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hI.aestronglyMeasurable h0).mpr hI)

/-- The part of `SingularLearningTheory.ResolutionAtlas.halfRadialMeasure` from chart $\alpha$: the
image of `SingularLearningTheory.ResolutionAtlas.halfRadialSourceMeasure` under
`SingularLearningTheory.ResolutionAtlas.fullChartEmbedding`. -/
@[expose] noncomputable def halfRadialComponent (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) : Measure R.FaceDomain :=
  (R.halfRadialSourceMeasure α β n ζ).map (R.fullChartEmbedding α)

@[expose] instance halfRadialComponent_finite (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) : IsFiniteMeasure (R.halfRadialComponent α β n ζ) := by
  unfold halfRadialComponent
  infer_instance

/-- The normalized positive half-radial measure on the original sigma of cubes. -/
@[expose] noncomputable def halfRadialMeasure (β : ℝ) (n : ℕ) (ζ : R.ChartFunctions) :
    Measure R.FaceDomain := ∑ α, R.halfRadialComponent α β n (ζ α)

@[expose] instance halfRadialMeasure_finite (β : ℝ) (n : ℕ) (ζ : R.ChartFunctions) :
    IsFiniteMeasure (R.halfRadialMeasure β n ζ) := by
  unfold halfRadialMeasure
  infer_instance

theorem integral_halfRadialComponent (α : R.ι) (β : ℝ) (n : ℕ)
    (ζ : C(cube d (R.b α), ℝ)) (mark : C(R.FaceDomain, ℝ)) :
    (∫ u, mark u ∂R.halfRadialComponent α β n ζ) =
      R.halfRadialScale n *
        R.chartRadialInsertion α β (1 / 2) n ζ (R.markedChartWeight α mark) := by
  rw [halfRadialComponent,
    integral_map (R.continuous_fullChartEmbedding α).measurable.aemeasurable
      mark.continuous.measurable.aestronglyMeasurable,
    halfRadialSourceMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      (R.integrable_halfRadialSourceDensity α β n ζ).aestronglyMeasurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top),
    chartRadialInsertion, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  rw [ENNReal.toReal_ofReal (R.halfRadialSourceDensity_nonneg α β n ζ hu), smul_eq_mul]
  simp only [halfRadialSourceDensity, markedChartWeight_apply, ContinuousMap.one_apply,
    fullChartEmbedding]
  ring

/-- Exact first-insertion integral formula. -/
theorem integral_halfRadialMeasure (β : ℝ) (n : ℕ) (ζ : R.ChartFunctions)
    (mark : C(R.FaceDomain, ℝ)) :
    (∫ u, mark u ∂R.halfRadialMeasure β n ζ) =
      R.halfRadialScale n *
        ∑ α, R.chartRadialInsertion α β (1 / 2) n (ζ α) (R.markedChartWeight α mark) := by
  have hI : ∀ α ∈ (Finset.univ : Finset R.ι),
      Integrable mark (R.halfRadialComponent α β n (ζ α)) := fun α _ ↦
    Continuous.integrable_of_compactSpace _ mark.continuous
  rw [halfRadialMeasure, integral_finsetSum_measure hI, Finset.mul_sum]
  exact Finset.sum_congr rfl fun α _ ↦ R.integral_halfRadialComponent α β n (ζ α) mark

/-- The density $u \mapsto S_{\lambda+1/2}(\zeta(u))$ of
`SingularLearningTheory.ResolutionAtlas.halfRadialLimitMeasure`, where $S$ is
`SingularLearningTheory.frozenInner` at $\beta$, $\lambda$ is
`SingularLearningTheory.ResolutionAtlas.rlct` and $\zeta$ is the chart field. It is positive
(`SingularLearningTheory.ResolutionAtlas.halfRadialLimitDensity_pos`). -/
@[expose] noncomputable def halfRadialLimitDensity (β : ℝ) (hβ : 0 < β)
    (ζ : R.ChartFunctions) : C(R.FaceDomain, ℝ) :=
  ⟨fun u ↦ frozenInner (R.rlct + 1 / 2) β (ζ u.1 u.2),
    (continuous_frozenInner (by linarith [R.rlct_pos]) hβ).comp (R.chartFieldCM ζ).continuous⟩

theorem halfRadialLimitDensity_pos (β : ℝ) (hβ : 0 < β) (ζ : R.ChartFunctions)
    (u : R.FaceDomain) : 0 < R.halfRadialLimitDensity β hβ ζ u :=
  frozenInner_pos (by linarith [R.rlct_pos]) hβ _

/-- The limiting half-radial measure: `SingularLearningTheory.ResolutionAtlas.essentialFaceMeasure`
with density `SingularLearningTheory.ResolutionAtlas.halfRadialLimitDensity`. Integrals against
it are the limits of the chart radial insertions with power $1/2$
(`SingularLearningTheory.ResolutionAtlas.integral_halfRadialLimitMeasure_eq_chart`), and its pair
integral of a kernel is `SingularLearningTheory.GaussianPosterior.compactQnum`. -/
@[expose] noncomputable def halfRadialLimitMeasure (β : ℝ) (hβ : 0 < β) (ζ : R.ChartFunctions) :
    Measure R.FaceDomain :=
  R.essentialFaceMeasure.withDensity (fun u ↦ ENNReal.ofReal (R.halfRadialLimitDensity β hβ ζ u))

@[expose] instance halfRadialLimitMeasure_finite (β : ℝ) (hβ : 0 < β) (ζ : R.ChartFunctions) :
    IsFiniteMeasure (R.halfRadialLimitMeasure β hβ ζ) := by
  apply isFiniteMeasure_withDensity
  apply (lintegral_ofReal_ne_top_iff_integrable
    (R.halfRadialLimitDensity β hβ ζ).continuous.aestronglyMeasurable
    (.of_forall fun u ↦ (R.halfRadialLimitDensity_pos β hβ ζ u).le)).mpr
  exact Continuous.integrable_of_compactSpace _
    (R.halfRadialLimitDensity β hβ ζ).continuous

theorem integral_halfRadialLimitMeasure (β : ℝ) (hβ : 0 < β) (ζ : R.ChartFunctions)
    (mark : C(R.FaceDomain, ℝ)) :
    (∫ u, mark u ∂R.halfRadialLimitMeasure β hβ ζ) =
      ∫ u, mark u * frozenInner (R.rlct + 1 / 2) β (ζ u.1 u.2) ∂R.essentialFaceMeasure := by
  rw [halfRadialLimitMeasure,
    integral_withDensity_eq_integral_toReal_smul₀
      (R.halfRadialLimitDensity β hβ ζ).continuous.measurable.aemeasurable.ennreal_ofReal
      (Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with u
  rw [ENNReal.toReal_ofReal (R.halfRadialLimitDensity_pos β hβ ζ u).le, smul_eq_mul]
  exact mul_comm _ _

theorem integral_halfRadialLimitMeasure_eq_chart (β : ℝ) (hβ : 0 < β)
    (ζ : R.ChartFunctions) (mark : C(R.FaceDomain, ℝ)) :
    (∫ u, mark u ∂R.halfRadialLimitMeasure β hβ ζ) =
      ∑ α, if R.IsEssential α then
        R.chartRadialLimit β (1 / 2) α (ζ α) (R.markedChartWeight α mark) else 0 := by
  rw [R.integral_halfRadialLimitMeasure]
  have h := R.integral_radial_essentialFaceMeasure hβ
    (by linarith [R.rlct_pos] : 0 < R.rlct + 1 / 2) (R.chartFieldCM ζ) mark
  rw [R.toChartFunctions_chartFieldCM] at h
  exact h

end SingularLearningTheory.ResolutionAtlas
