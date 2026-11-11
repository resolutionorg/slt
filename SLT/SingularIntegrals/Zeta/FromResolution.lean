/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Zeta.Continuation
public import SLT.Resolution.AtlasDataExists
public import SLT.Resolution.Assembly
import SLT.Resolution.Outer
public import SLT.StandardForm.FundamentalConditionI

/-!
# Smooth atlas construction for zeta continuation

Positive mass in every positive sublevel ensures a zero exists. The analytic locus
is an open neighbourhood of the parameter domain, so the atlas construction
applies with precisely the ambient assumptions in the zeta theorem.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

/-- Positive prior mass in every sublevel of a continuous nonnegative potential on
a compact set forces the potential to attain zero. -/
private theorem exists_zero_of_sublevel_mass
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w)
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    ∃ w ∈ W, K w = 0 := by
  by_contra hzero
  have hz : ∀ w ∈ W, K w = 0 → w ∈ (∅ : Set (Fin d → ℝ)) :=
    fun w hw hkw ↦ (hzero ⟨w, hw, hkw⟩).elim
  obtain ⟨δ, hδ, hsub⟩ := IsCompact.exists_delta hW hKc hK isOpen_empty hz
  have hempty : W ∩ {w | K w < δ} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro w ⟨hw, hkw⟩
    exact hsub w hw hkw.le
  have hm := hvol δ hδ
  simp only [hempty, Measure.restrict_empty, lintegral_zero_measure, lt_self_iff_false] at hm

/-- The smooth atlas is available under the deterministic zeta assumptions. -/
theorem exists_atlasData_of_sublevel_mass
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0))
    (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    Nonempty (AtlasData K φ W) := by
  obtain ⟨w, hw, hkw⟩ := exists_zero_of_sublevel_mass hW hKa.continuousOn hK hvol
  exact exists_atlasData hW II (isOpen_analyticAt ℝ K) hKa
    (fun _ hw ↦ hw) hK hw hkw hKg hφg

end SingularLearningTheory
