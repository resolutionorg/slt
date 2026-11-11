/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.StochasticAsymptotics
public import SLT.Resolution.Atlas
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Prior-almost-everywhere properties from the charts

A resolution atlas transports the localized prior $\chi\varphi\,dw$ to the chart cubes. This
module turns a measurable property that holds at every chart point $g_\alpha(u)$ into a
statement almost everywhere for the prior, without assuming that the charts cover every point of
$W$. `SingularLearningTheory.ResolutionAtlas.ae_localized_of_chartwise` gives it for the localized
prior, and `SingularLearningTheory.ResolutionAtlas.ae_below_threshold_of_chartwise` for the prior
$\varphi\,dw$ on $W$ where $K < \delta$, where the localization is $1$.
`SingularLearningTheory.ResolutionAtlas.ae_prior_of_chart_and_tail` adds a property that holds on the
tail $K \ge \delta$ to give it for the prior on all of $W$.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- Every measurable chartwise property holds almost everywhere for the
localized prior. This is a direct consequence of the measure transport,
and requires no pointwise chart-coverage hypothesis. -/
theorem ae_localized_of_chartwise {p : (Fin d → ℝ) → Prop}
    (hp : MeasurableSet {w | p w})
    (hchart : ∀ α, ∀ u ∈ cube d (R.b α), p (R.g α u)) :
    ∀ᵐ w ∂(volume.restrict W).withDensity
      (fun w ↦ ENNReal.ofReal (R.χ w * φ w)), p w := by
  rw [R.transport, ae_finsetSum_measure_iff]
  intro α _
  apply (ae_map_iff (R.g_measurable α).aemeasurable hp).mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  exact (ae_restrict_mem measurableSet_Icc).mono fun u hu ↦ hchart α u hu

/-- Below the localization threshold the localized prior is the full prior.
This transfers any chartwise property to a prior-a.e. implication. -/
theorem ae_below_threshold_of_chartwise (hW : MeasurableSet W) (hφ : IntegrableOn φ W)
    {p : (Fin d → ℝ) → Prop} (hp : MeasurableSet {w | p w})
    (hchart : ∀ α, ∀ u ∈ cube d (R.b α), p (R.g α u)) :
    ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
      K w < R.δ → p w := by
  have hφm : AEMeasurable (fun w ↦ ENNReal.ofReal (φ w)) (volume.restrict W) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hφ.aemeasurable
  have hχφm : AEMeasurable (fun w ↦ ENNReal.ofReal (R.χ w * φ w)) (volume.restrict W) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (R.χ_measurable.aemeasurable.mul hφ.aemeasurable)
  have hloc := R.ae_localized_of_chartwise hp hchart
  rw [ae_withDensity_iff' hχφm] at hloc
  rw [ae_withDensity_iff' hφm]
  filter_upwards [hloc, ae_restrict_mem hW] with w hw hwW hφw hwK
  apply hw
  rwa [R.χ_eq_one w hwW hwK, one_mul]

/-- Chart and tail properties combine under the full prior. This is the
correct Bayes/Gibbs replacement for the MLE theorem's pointwise coverage premise.
Apply separately for each sample on its common full-measure event, or for each
fresh datum on the common q-a.e. factorization/continuity event. -/
theorem ae_prior_of_chart_and_tail (hW : MeasurableSet W) (hφ : IntegrableOn φ W)
    {p : (Fin d → ℝ) → Prop} (hp : MeasurableSet {w | p w})
    (hchart : ∀ α, ∀ u ∈ cube d (R.b α), p (R.g α u))
    (htail : ∀ w ∈ W, R.δ ≤ K w → p w) :
    ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)), p w := by
  have hlow := R.ae_below_threshold_of_chartwise hW hφ hp hchart
  have hw : ∀ᵐ w ∂(volume.restrict W).withDensity
      (fun w ↦ ENNReal.ofReal (φ w)), w ∈ W :=
    (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem hW)
  filter_upwards [hlow, hw] with w hlow hw
  by_cases hk : K w < R.δ
  · exact hlow hk
  · exact htail w hw (le_of_not_gt hk)

end SingularLearningTheory.ResolutionAtlas
