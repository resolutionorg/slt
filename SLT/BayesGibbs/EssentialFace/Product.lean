/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.EssentialFace.Measure
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The two-face trace formula

The exact trace formula for a product of two essential faces.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal Classical

namespace SingularLearningTheory.GaussianPosterior

/-- Integrating one variable of a continuous compact kernel gives a continuous
function. A single constant bound handles every parameter value. -/
private theorem continuous_partial_integral_compact
    {U V : Type*} [MetricSpace U] [CompactSpace U] [MetricSpace V] [CompactSpace V]
    [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) [IsFiniteMeasure μ] (F : C(U × V, ℝ)) :
    Continuous (fun u ↦ ∫ v, F (u, v) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro u₀
  refine continuousAt_of_dominated (bound := fun _ : V ↦ ‖F‖)
    (Eventually.of_forall fun u ↦
      (F.continuous.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable)
    (Eventually.of_forall fun u ↦ Eventually.of_forall fun v ↦ F.norm_coe_le_norm (u, v))
    (integrable_const _) ?_
  exact Eventually.of_forall fun v ↦
    (F.continuous.comp (continuous_id.prodMk continuous_const)).continuousAt

end SingularLearningTheory.GaussianPosterior

namespace SingularLearningTheory.ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
/-- The metric on `SingularLearningTheory.ResolutionAtlas.FaceDomain` given by
`Metric.Sigma.metricSpace`: each chart cube keeps its own metric, and points of different cubes
are at distance at least $1$. Mathlib does not make this metric on a sigma type an instance, so
it is a local instance here. -/
noncomputable local instance : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace

/-- The sum formula before replacing individual pushforward measures by traces. -/
theorem integral_essentialFaceMeasure_chartMeasure (F : C(R.FaceDomain, ℝ)) :
    ∫ u, F u ∂R.essentialFaceMeasure =
      ∑ α, if R.IsEssential α then
        R.chartGamma α / R.b α ^ R.chartMult α * (∫ u, F u ∂R.faceChartMeasure α) else 0 := by
  rw [R.integral_essentialFaceMeasure]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs
  · rw [R.integral_faceChartMeasure]
  · rfl

/-- Two chart pushforwards produce the literal nested trace integrals. -/
theorem integral_faceChartMeasure_pair (α β : R.ι)
    (F : C(R.FaceDomain × R.FaceDomain, ℝ)) :
    (∫ u, ∫ v, F (u, v) ∂R.faceChartMeasure β ∂R.faceChartMeasure α) =
      ∫ v in cube d (R.b α), R.traceWeight α v *
        (∫ w in cube d (R.b β), R.traceWeight β w *
          F (R.faceEmbedding α v, R.faceEmbedding β w)) := by
  let G : C(R.FaceDomain, ℝ) := ⟨fun u ↦ ∫ v, F (u, v) ∂R.faceChartMeasure β,
    GaussianPosterior.continuous_partial_integral_compact _ F⟩
  change (∫ u, G u ∂R.faceChartMeasure α) = _
  rw [R.integral_faceChartMeasure]
  apply integral_congr_ae
  filter_upwards with v
  congr 1
  let H : C(R.FaceDomain, ℝ) := ⟨fun w ↦ F (R.faceEmbedding α v, w),
    F.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact R.integral_faceChartMeasure β H

/-- Exact pair bridge. This is the Q-numerator interface: specialize F(u,v) to
C(u,v) S_(λ+1/2)(ζu) S_(λ+1/2)(ζv). The centered covariance is replaced by
raw feature covariance only at the embedded faces, by covarianceKernel_face_eq. -/
theorem integral_essentialFaceMeasure_prod
    (F : C(R.FaceDomain × R.FaceDomain, ℝ)) :
    (∫ z, F z ∂(R.essentialFaceMeasure.prod R.essentialFaceMeasure)) =
      ∑ α, if R.IsEssential α then
        R.chartGamma α / R.b α ^ R.chartMult α *
          (∑ β, if R.IsEssential β then
            R.chartGamma β / R.b β ^ R.chartMult β *
              (∫ v in cube d (R.b α), R.traceWeight α v *
                (∫ w in cube d (R.b β), R.traceWeight β w *
                  F (R.faceEmbedding α v, R.faceEmbedding β w))) else 0) else 0 := by
  have hF : Integrable F (R.essentialFaceMeasure.prod R.essentialFaceMeasure) :=
    Continuous.integrable_of_compactSpace _ F.continuous
  rw [integral_prod F hF]
  let G : C(R.FaceDomain, ℝ) := ⟨fun u ↦ ∫ v, F (u, v) ∂R.essentialFaceMeasure,
    GaussianPosterior.continuous_partial_integral_compact _ F⟩
  change (∫ u, G u ∂R.essentialFaceMeasure) = _
  rw [R.integral_essentialFaceMeasure_chartMeasure]
  apply Finset.sum_congr rfl
  intro α _
  by_cases hα : R.IsEssential α
  · rw [if_pos hα, if_pos hα]
    congr 1
    let H : R.ι → C(R.FaceDomain, ℝ) := fun β ↦
      ⟨fun u ↦ ∫ v, F (u, v) ∂R.faceChartMeasure β,
        GaussianPosterior.continuous_partial_integral_compact _ F⟩
    have hG : ∀ u, G u = ∑ β, if R.IsEssential β then
        R.chartGamma β / R.b β ^ R.chartMult β * H β u else 0 := by
      intro u
      let Fu : C(R.FaceDomain, ℝ) := ⟨fun v ↦ F (u, v),
        F.continuous.comp (continuous_const.prodMk continuous_id)⟩
      exact R.integral_essentialFaceMeasure_chartMeasure Fu
    calc (∫ u, G u ∂R.faceChartMeasure α) =
        ∫ u, ∑ β, if R.IsEssential β then
          R.chartGamma β / R.b β ^ R.chartMult β * H β u else 0 ∂R.faceChartMeasure α := by
            apply integral_congr_ae
            exact Eventually.of_forall hG
      _ = ∑ β, if R.IsEssential β then
          R.chartGamma β / R.b β ^ R.chartMult β *
            (∫ u, H β u ∂R.faceChartMeasure α) else 0 := by
            rw [integral_finsetSum _ (fun β _ ↦ ?_)]
            · apply Finset.sum_congr rfl
              intro β _
              by_cases hβ : R.IsEssential β
              · simp only [hβ, if_true, integral_const_mul]
              · simp only [hβ, if_false, integral_zero]
            · by_cases hβ : R.IsEssential β
              · simp only [hβ, if_true]
                exact (Continuous.integrable_of_compactSpace _ (H β).continuous).const_mul _
              · simp only [hβ, if_false]
                exact integrable_zero _ _ _
      _ = _ := by
            apply Finset.sum_congr rfl
            intro β _
            split_ifs
            · congr 1
              exact R.integral_faceChartMeasure_pair α β F
            · rfl
  · simp only [if_neg hα]

end SingularLearningTheory.ResolutionAtlas
