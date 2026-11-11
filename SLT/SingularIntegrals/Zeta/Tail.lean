/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Zeta.Holomorphic
public import SLT.SingularIntegrals.DeterministicFreeEnergy
public import SLT.Resolution.Atlas
import SLT.Analysis.Complex.IntegralCPow
public import SLT.SingularIntegrals.Transforms

/-!
# The entire tail of the zeta function

Outside the smooth resolution cutoff, the potential is bounded away from zero.
The corresponding finite prior integral is entire. No regularity of the potential
outside the compact parameter domain is assumed.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

/-- A finite prior supported away from the zero set gives an entire zeta integral. -/
private theorem zetaFunction_differentiable_of_away_from_zero
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hKc : ContinuousOn K W)
    (hφi : IntegrableOn φ W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    {ε : ℝ} (hε : 0 < ε) (haway : ∀ w ∈ W, φ w ≠ 0 → ε ≤ K w) :
    Differentiable ℂ (zetaFunction K φ W) := by
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
  have hK'ε : ∀ᵐ w ∂ν, ε ≤ K' w := by
    dsimp only [ν]
    rw [ae_withDensity_iff' hφi.aemeasurable.ennreal_ofReal]
    filter_upwards [ae_restrict_mem hW.measurableSet] with w hw hφw
    dsimp only [K']
    rw [piecewise_eq_of_mem W K _ hw]
    exact haway w hw (fun hz ↦ hφw (by rw [hz, ENNReal.ofReal_zero]))
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
  have hd := differentiable_integral_cpow_of_le_of_le hK'm hε hK'ε hK'M
  rwa [show (fun z : ℂ ↦ ∫ w, (K' w : ℂ) ^ z ∂ν) = zetaFunction K φ W from funext heq] at hd

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : ResolutionAtlas K φ W)

/-- The tail left outside the resolution charts is entire. -/
theorem zeta_tail_differentiable (hW : IsCompact W) (hKc : ContinuousOn K W)
    (hφi : IntegrableOn φ W) (hφ : ∀ w ∈ W, 0 ≤ φ w) :
    Differentiable ℂ (zetaFunction K (fun w ↦ (1 - R.χ w) * φ w) W) := by
  have hψi : IntegrableOn (fun w ↦ (1 - R.χ w) * φ w) W := by
    refine hφi.bdd_mul (c := 1)
      ((measurable_const.sub R.χ_measurable).aestronglyMeasurable) ?_
    exact .of_forall fun w ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (R.χ_le_one w))]
      linarith [R.χ_nonneg w]
  apply zetaFunction_differentiable_of_away_from_zero hW hKc hψi
    (fun w hw ↦ mul_nonneg (sub_nonneg.mpr (R.χ_le_one w)) (hφ w hw)) R.δ_pos
  intro w hw hne
  by_contra hlt
  exact hne (by rw [R.χ_eq_one w hw (lt_of_not_ge hlt), sub_self, zero_mul])

end ResolutionAtlas
end SingularLearningTheory
