/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.HalfRadial.Measure
public import SLT.BayesGibbs.CompactBase.Kernel
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The pair integral of the limiting half-radial measure

The integral of a positive semidefinite kernel $C$ against the product of the limiting
half-radial measure with itself is `SingularLearningTheory.GaussianPosterior.compactQnum`, the
numerator of the two-replica term of the limiting posterior vector on the essential faces of a
resolution atlas
(`SingularLearningTheory.ResolutionAtlas.integral_halfRadialLimitMeasure_prod_eq_compactQnum`).
The limiting half-radial density occurs once in each coordinate, which gives exactly that
normalization. The identity names the limit of the scaled pair integrals of the tempered
posterior in the convergence of the posterior observables of [Wat09, Theorem 6.8].
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
/-- The metric `Metric.Sigma.metricSpace` on the disjoint union
`SingularLearningTheory.ResolutionAtlas.FaceDomain` of the chart cubes, local to this module. Its
topology is the disjoint-union topology. -/
noncomputable local instance halfRadialCompactQMetric1 : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace

/-- Exact limiting pair insertion; the half-radial density occurs once in each
coordinate, giving precisely the compactQnum normalization. -/
theorem integral_halfRadialLimitMeasure_prod_eq_compactQnum
    (β : ℝ) (hβ : 0 < β) (ζ : R.ChartFunctions)
    (C : PSDKernel R.FaceDomain) :
    (∫ z, C.C z.1 z.2 ∂((R.halfRadialLimitMeasure β hβ ζ).prod
      (R.halfRadialLimitMeasure β hβ ζ))) =
      GaussianPosterior.compactQnum R.essentialFaceMeasure β R.rlct C (R.chartFieldCM ζ) := by
  have hd := (R.halfRadialLimitDensity β hβ ζ).continuous.measurable.ennreal_ofReal
  unfold halfRadialLimitMeasure
  rw [prod_withDensity hd hd]
  have hprod : Measurable (fun z : R.FaceDomain × R.FaceDomain ↦
      ENNReal.ofReal (R.halfRadialLimitDensity β hβ ζ z.1) *
        ENNReal.ofReal (R.halfRadialLimitDensity β hβ ζ z.2)) :=
    (hd.comp measurable_fst).mul (hd.comp measurable_snd)
  rw [integral_withDensity_eq_integral_toReal_smul₀
      hprod.aemeasurable
      (Eventually.of_forall fun _ ↦ ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  unfold GaussianPosterior.compactQnum GaussianPosterior.bilocalC
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (R.halfRadialLimitDensity_pos β hβ ζ z.1).le,
    ENNReal.toReal_ofReal (R.halfRadialLimitDensity_pos β hβ ζ z.2).le,
    smul_eq_mul]
  simp only [halfRadialLimitDensity, chartFieldCM, ContinuousMap.coe_mk]
  ring

end SingularLearningTheory.ResolutionAtlas
