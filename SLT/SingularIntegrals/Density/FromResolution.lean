/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Density.Atlas
import SLT.SingularIntegrals.Zeta.FromResolution
import SLT.SingularIntegrals.TypeOfAtlas
public import SLT.SingularIntegrals.SingularityType
public import SLT.StandardForm.FundamentalConditionI
public import SLT.Resolution.Atlas

/-!
# Exact state-density asymptotics under the analytic hypotheses

This completes [Wat09, Theorem 7.1(3)], with the density defined as the derivative
of the sublevel volume, as in [Hit26]'s
[Hit26, Section 3.1].
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

namespace NondegenerateResolutionAtlas

/-- Nondegeneracy makes the leading density coefficient strictly positive. -/
theorem exists_deriv_sublevelVolume_limit
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : NondegenerateResolutionAtlas K φ W)
    (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ t in 𝓝[>] 0, DifferentiableAt ℝ (sublevelVolume K φ W) t) ∧
      Tendsto (fun t ↦ deriv (sublevelVolume K φ W) t /
        (t ^ (R.rlct - 1) * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 C) := by
  cases d with
  | zero =>
      obtain ⟨j, _⟩ := R.active (Classical.arbitrary R.ι)
      exact Fin.elim0 j
  | succ n =>
      exact ⟨_, mul_pos R.toResolutionAtlas.rlct_pos R.sublevelCoefficient_pos,
        R.toResolutionAtlas.tendsto_deriv_sublevelVolume hW hKm hφ hφi⟩

end NondegenerateResolutionAtlas

/-- [Wat09, Theorem 7.1(3)]: the derivative exists at all sufficiently small
positive levels and has the exact power-log asymptotic. The state density is
interpreted as in [Hit26, Section 3.1].
The proof uses explicit resolution-chart slices and the fundamental theorem of
calculus, so it does not require a surface-measure version of the coarea formula. -/
theorem singularityType_stateDensity
    {d : ℕ} (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0))
    (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w))
    (lam : ℝ) (m : ℕ) (htype : IsSingularityType K φ W lam m) :
    ∃ C : ℝ, 0 < C ∧
      (∀ᶠ t in 𝓝[>] 0, DifferentiableAt ℝ (sublevelVolume K φ W) t) ∧
      Tendsto (fun t ↦ deriv (sublevelVolume K φ W) t /
        (t ^ (lam - 1) * (-Real.log t) ^ (m - 1))) (𝓝[>] 0) (𝓝 C) := by
  classical
  obtain ⟨A⟩ := exists_atlasData_of_sublevel_mass hW hKa hK II hKg hφg hvol
  have : Nonempty A.ι := A.nonempty_ι hvol
  let R := A.toNondegenerateResolutionAtlas
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  obtain ⟨U, hU, hWU, φ₁, φ₂, hφ₁, hφ₁s, hφ₂, hφ₂a, hφeq⟩ := II.factor
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun w hw ↦ by
    rw [hφeq w (hWU hw)]
    exact mul_nonneg (hφ₁ w (hWU hw)).le (hφ₂ w hw)
  have hφc : ContinuousOn φ W :=
    ((hφ₁s.continuousOn.mul hφ₂a.continuousOn).mono hWU).congr
      (fun w hw ↦ hφeq w (hWU hw))
  have hφi : IntegrableOn φ W := hφc.integrableOn_compact hW
  have hagree : ∀ w ∈ W, K w = W.piecewise K 0 w := fun w hw ↦
    (Set.piecewise_eq_of_mem W _ _ hw).symm
  have hKm : Measurable (W.piecewise K 0) :=
    ContinuousOn.measurable_piecewise hKa.continuousOn continuousOn_const hWm
  have htypeR : IsSingularityType K φ W R.rlct R.mult :=
    ((R.congr hagree).isSingularityType hWm hKm hφ hφi.aemeasurable).congr
      (fun w hw ↦ (hagree w hw).symm)
  obtain ⟨hlam, hm⟩ := htype.unique htypeR
  obtain ⟨C, hC, hd, hlim⟩ :=
    (R.congr hagree).exists_deriv_sublevelVolume_limit hWm hKm hφ hφi
  have hV : sublevelVolume K φ W = sublevelVolume (W.piecewise K 0) φ W :=
    funext (sublevelVolume_congr_on hWm hagree)
  rw [← hV] at hd hlim
  refine ⟨C, hC, hd, ?_⟩
  rw [hlam, hm]
  exact hlim

end SingularLearningTheory
