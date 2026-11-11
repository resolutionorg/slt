/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.LaplaceDoubling.Basic
public import SLT.SingularIntegrals.SingularityType
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Identities for exponentially tilted measures

Small identities for the normalized measure `MeasureTheory.Measure.expMeasure` with
density proportional to $e^{-G}$. `MeasureTheory.ae_expMeasure_of_ae` passes
almost-everywhere statements from the base measure to every tilt, and
`MeasureTheory.integral_tilt_expMeasure` shows that tilting such a measure again by
$e^{-tf}$ adds $tf$ to the exponent. For the prior $\varphi(w)\,dw$ restricted to $W$,
`SingularLearningTheory.BayesGibbs.integral_exp_restricted_prior` writes the normalizing integral as
$\int_W e^{-G}\varphi$, and `SingularLearningTheory.BayesGibbs.weighted_posterior_eq_expMeasure`
identifies the tilted measure with the posterior in the form of
`SingularLearningTheory.posteriorMeasure` when $G = n\beta K_n$.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

variable {U : Type*} [MeasurableSpace U] {ν : Measure U}

/-- Prior-a.e. bounds pass to every exponential tilt. -/
theorem _root_.MeasureTheory.ae_expMeasure_of_ae {G : U → ℝ} {p : U → Prop} (hp : ∀ᵐ w ∂ν, p w) :
    ∀ᵐ w ∂Measure.expMeasure ν G, p w := by
  unfold Measure.expMeasure
  exact Measure.ae_smul_measure ((withDensity_absolutelyContinuous _ _).ae_le hp) _

/-- Retilting an exponential posterior is the same normalized integral as
adding the tilt to its exponent. This identity requires no normalization of
the underlying statistical model and no integrability of the test function. -/
theorem _root_.MeasureTheory.integral_tilt_expMeasure {G f : U → ℝ} (hG : Measurable G)
    (hf : Measurable f)
    (g : U → ℝ) (t : ℝ)
    (hZ : 0 < ∫ w, Real.exp (-G w) ∂ν)
    (hZt : 0 < ∫ w, Real.exp (-(G w + t * f w)) ∂ν) :
    (∫ w, g w * Real.exp (-(t * f w)) ∂Measure.expMeasure ν G) /
        (∫ w, Real.exp (-(t * f w)) ∂Measure.expMeasure ν G) =
      ∫ w, g w ∂Measure.expMeasure ν (fun w ↦ G w + t * f w) := by
  have hGtf : Measurable (fun w ↦ G w + t * f w) := hG.add (hf.const_mul t)
  rw [integral_expMeasure ν hG _ hZ, integral_expMeasure ν hG _ hZ,
    div_div_div_cancel_right₀ hZ.ne', integral_expMeasure ν hGtf _ hZt]
  congr 1
  · apply integral_congr_ae
    filter_upwards [] with w
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  · apply integral_congr_ae
    filter_upwards [] with w
    rw [← Real.exp_add]
    congr 1
    ring

/-- The ambient restricted-prior integral is the weighted Lebesgue integral
used by the evidence definitions. -/
theorem integral_exp_restricted_prior {d : ℕ} {W : Set (Fin d → ℝ)}
    {φ : (Fin d → ℝ) → ℝ} (hW : MeasurableSet W)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) (G : (Fin d → ℝ) → ℝ) :
    (∫ w, Real.exp (-G w) ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))) =
      ∫ w in W, Real.exp (-G w) * φ w := by
  rw [integral_withDensity_eq_integral_toReal_smul₀ hφi.aemeasurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  refine setIntegral_congr_fun hW fun w hw ↦ ?_
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hφ w hw)]
  ring

/-- The weighted posterior is an exponential tilt of the prior. At `G = nβK_n` the left side is
definitionally the posterior `SingularLearningTheory.posteriorMeasure`. -/
theorem weighted_posterior_eq_expMeasure {d : ℕ} {W : Set (Fin d → ℝ)}
    {φ : (Fin d → ℝ) → ℝ} (hW : MeasurableSet W)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) (G : (Fin d → ℝ) → ℝ) :
    (ENNReal.ofReal (∫ w in W, Real.exp (-G w) * φ w))⁻¹ •
        ((volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))).withDensity
          (fun w ↦ ENNReal.ofReal (Real.exp (-G w))) =
      Measure.expMeasure ((volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))) G := by
  unfold Measure.expMeasure
  rw [integral_exp_restricted_prior hW hφ hφi]

end SingularLearningTheory.BayesGibbs
