/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.ExpMeasure
public import SLT.BayesGibbs.LaplaceDoubling.Basic

/-!
# Measurability of posterior expectations

An expectation under the tilted measure $e^{-G}\nu / Z$ is the ratio
$\int g e^{-G}\,d\nu / \int e^{-G}\,d\nu$, also when the evidence $Z$ vanishes
(`MeasureTheory.integral_expMeasure_eq_ratio`). So when the potential and the
integrand depend jointly measurably on the sample, the posterior expectation is a measurable
function of the sample on every sample, not only almost surely
(`SingularLearningTheory.BayesGibbs.measurable_posterior_integral`). The same holds jointly in the
sample and a datum $x$ for the predictive value $-\log E_w[e^{-f(x, w)}]$ and for the posterior
mean of $f(x, w)$ (`SingularLearningTheory.BayesGibbs.measurable_posterior_predictive` and
`SingularLearningTheory.BayesGibbs.measurable_posterior_feature_mean`). These make the posterior
observables of [Wat09, Theorem 6.8] random variables.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace SingularLearningTheory.BayesGibbs

/-- The posterior integral ratio identity is valid even when the evidence
vanishes. This gives measurability on every sample, independently of the
almost-sure statistical bounds used to prove probability and integrability. -/
theorem _root_.MeasureTheory.integral_expMeasure_eq_ratio {W : Type*} [MeasurableSpace W]
    (ν : Measure W) {G : W → ℝ} (hG : Measurable G) (g : W → ℝ) :
    (∫ w, g w ∂Measure.expMeasure ν G) =
      (∫ w, g w * Real.exp (-G w) ∂ν) / (∫ w, Real.exp (-G w) ∂ν) := by
  have hem : Measurable fun w ↦ Real.exp (-G w) := hG.neg.exp
  have hZ : 0 ≤ ∫ w, Real.exp (-G w) ∂ν :=
    integral_nonneg fun _ ↦ (Real.exp_pos _).le
  unfold Measure.expMeasure
  rw [integral_smul_measure g, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ]
  change ((∫ w, Real.exp (-G w) ∂ν)⁻¹) •
    ∫ w, g w ∂ν.withDensity (fun w ↦ ((Real.toNNReal (Real.exp (-G w)) : NNReal) : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hem.real_toNNReal]
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
    div_eq_inv_mul]
  simp_rw [mul_comm (Real.exp _) (g _)]

/-- Jointly measurable integrands and exponents give measurable actual
posterior expectations, including exceptional samples with zero evidence. -/
theorem measurable_posterior_integral {Ω W : Type*}
    [MeasurableSpace Ω] [MeasurableSpace W] (ν : Measure W) [SFinite ν]
    {G H : Ω → W → ℝ} (hG : Measurable (Function.uncurry G))
    (hH : Measurable (Function.uncurry H)) :
    Measurable fun ω ↦ ∫ w, H ω w ∂Measure.expMeasure ν (G ω) := by
  simp_rw [integral_expMeasure_eq_ratio ν hG.of_uncurry_left]
  exact (hH.mul hG.neg.exp).stronglyMeasurable.integral_prod_right.measurable.div
    hG.neg.exp.stronglyMeasurable.integral_prod_right.measurable

/-- Predictive logarithms are jointly measurable in sample and datum. -/
theorem measurable_posterior_predictive {Ω X W : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace W]
    (ν : Measure W) [SFinite ν] {G : Ω → W → ℝ} {f : X → W → ℝ}
    (hG : Measurable (Function.uncurry G)) (hf : Measurable (Function.uncurry f)) :
    Measurable fun z : Ω × X ↦
      -(Real.log (∫ w, Real.exp (-f z.2 w) ∂Measure.expMeasure ν (G z.1))) := by
  apply Measurable.neg
  apply Measurable.log
  apply measurable_posterior_integral ν
  · exact hG.comp ((measurable_fst.fst).prodMk measurable_snd)
  · exact hf.neg.exp.comp ((measurable_fst.snd).prodMk measurable_snd)

/-- The corresponding Gibbs means are jointly measurable as well. -/
theorem measurable_posterior_feature_mean {Ω X W : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace W]
    (ν : Measure W) [SFinite ν] {G : Ω → W → ℝ} {f : X → W → ℝ}
    (hG : Measurable (Function.uncurry G)) (hf : Measurable (Function.uncurry f)) :
    Measurable fun z : Ω × X ↦ ∫ w, f z.2 w ∂Measure.expMeasure ν (G z.1) := by
  apply measurable_posterior_integral ν
  · exact hG.comp ((measurable_fst.fst).prodMk measurable_snd)
  · exact hf.comp ((measurable_fst.snd).prodMk measurable_snd)

end SingularLearningTheory.BayesGibbs
