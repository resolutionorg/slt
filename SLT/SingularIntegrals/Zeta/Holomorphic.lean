/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.Complex.IntegralCPow
public import SLT.SingularIntegrals.Transforms

/-!
# Holomorphy of the defining zeta integral

A continuous nonnegative potential on a compact parameter set is bounded. Its complex
powers are therefore integrable against a finite prior and holomorphic on `Re z > 0`,
including at parameters where the potential vanishes. Values outside the parameter set
need no regularity.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

/-- The defining zeta integral is holomorphic on the positive half-plane ([Wat09, §6.2], equation
(6.15)). Analytic resolution is needed only for its continuation. -/
theorem zetaFunction_differentiableOn_of_continuousOn
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w)
    (hφi : IntegrableOn φ W) (hφ : ∀ w ∈ W, 0 ≤ φ w) :
    DifferentiableOn ℂ (zetaFunction K φ W) {z : ℂ | 0 < z.re} := by
  classical
  let K' := W.piecewise K (fun _ ↦ 0)
  have hK'm : Measurable K' :=
    hKc.measurable_piecewise continuousOn_const hW.measurableSet
  let ν := (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))
  have hφae : 0 ≤ᵐ[volume.restrict W] φ :=
    ae_restrict_of_forall_mem hW.measurableSet hφ
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity
    ((lintegral_ofReal_ne_top_iff_integrable hφi.1 hφae).mpr hφi)
  have hac : ν ≪ volume.restrict W := withDensity_absolutelyContinuous _ _
  have hmem : ∀ᵐ w ∂ν, w ∈ W := (ae_restrict_mem hW.measurableSet).filter_mono hac.ae_le
  have hK'0 : ∀ᵐ w ∂ν, 0 ≤ K' w := by
    filter_upwards [hmem] with w hw
    simpa only [K', piecewise_eq_of_mem W K _ hw] using hK w hw
  obtain ⟨M, hM⟩ := hW.bddAbove_image hKc
  have hK'M : ∀ᵐ w ∂ν, K' w ≤ M := by
    filter_upwards [hmem] with w hw
    simpa only [K', piecewise_eq_of_mem W K _ hw] using hM ⟨w, hw, rfl⟩
  have heq (z : ℂ) : (∫ w, (K' w : ℂ) ^ z ∂ν) = zetaFunction K φ W z := by
    dsimp only [ν]
    rw [integral_withDensity_eq_integral_toReal_smul₀ hφi.aemeasurable.ennreal_ofReal
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hW.measurableSet] with w hw
    simp only [K', piecewise_eq_of_mem W K _ hw, ENNReal.toReal_ofReal (hφ w hw),
      Complex.real_smul, mul_comm]
  intro z hz
  have hd := differentiableAt_integral_cpow_of_nonneg hK'm hK'0 hK'M hz
  rw [show (fun z : ℂ ↦ ∫ w, (K' w : ℂ) ^ z ∂ν) = zetaFunction K φ W from funext heq] at hd
  exact hd.differentiableWithinAt

end SingularLearningTheory
