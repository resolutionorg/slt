/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Prior.AETransport
public import Mathlib.MeasureTheory.Measure.Prod
public import SLT.Resolution.Atlas
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Prior-almost-everywhere properties of parameter pairs

`SingularLearningTheory.ResolutionAtlas.ae_prior_pair_of_chart_and_tail` is the form of
`SingularLearningTheory.ResolutionAtlas.ae_prior_of_chart_and_tail` for pairs. A measurable property
$p(w, v)$ that holds whenever each of $w$ and $v$ is a chart point $g_\alpha(u)$ or a point of
$W$ with $K \ge \delta$ holds for almost every $w$ and almost every $v$ under the prior, without
assuming that the charts cover every point of $W$. It gives the bounds for pairs in the uniform
law of large numbers for the covariance.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- Tensor version of prior-a.e. chart/tail transport. No chart selector
or pointwise atlas coverage is required. The measurable outer event is obtained
from the measure of the bad inner section. -/
theorem ae_prior_pair_of_chart_and_tail
    (hW : MeasurableSet W) (hφ : IntegrableOn φ W)
    {p : (Fin d → ℝ) → (Fin d → ℝ) → Prop}
    (hp : MeasurableSet {z : (Fin d → ℝ) × (Fin d → ℝ) | p z.1 z.2})
    (hcc : ∀ α, ∀ u ∈ cube d (R.b α), ∀ γ, ∀ v ∈ cube d (R.b γ),
      p (R.g α u) (R.g γ v))
    (hct : ∀ α, ∀ u ∈ cube d (R.b α), ∀ v ∈ W, R.δ ≤ K v → p (R.g α u) v)
    (htc : ∀ w ∈ W, R.δ ≤ K w → ∀ γ, ∀ v ∈ cube d (R.b γ), p w (R.g γ v))
    (htt : ∀ w ∈ W, R.δ ≤ K w → ∀ v ∈ W, R.δ ≤ K v → p w v) :
    ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
      ∀ᵐ v ∂(volume.restrict W).withDensity (fun v ↦ ENNReal.ofReal (φ v)), p w v := by
  let ν := (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))
  haveI : IsFiniteMeasure ν :=
    isFiniteMeasure_withDensity_ofReal hφ.hasFiniteIntegral
  have hbad : Measurable fun w ↦ ν {v | ¬p w v} :=
    measurable_measure_prodMk_left hp.compl
  have hout : MeasurableSet {w | ∀ᵐ v ∂ν, p w v} := by
    simpa only [ae_iff] using measurableSet_eq_fun hbad (measurable_const (a := (0 : ℝ≥0∞)))
  apply R.ae_prior_of_chart_and_tail hW hφ hout
  · intro α u hu
    apply R.ae_prior_of_chart_and_tail hW hφ
      (hp.preimage (measurable_const.prodMk measurable_id))
    · exact fun γ v hv ↦ hcc α u hu γ v hv
    · exact fun v hv hvK ↦ hct α u hu v hv hvK
  · intro w hw hwK
    apply R.ae_prior_of_chart_and_tail hW hφ
      (hp.preimage (measurable_const.prodMk measurable_id))
    · exact fun γ v hv ↦ htc w hw hwK γ v hv
    · exact fun v hv hvK ↦ htt w hw hwK v hv hvK

end SingularLearningTheory.ResolutionAtlas
