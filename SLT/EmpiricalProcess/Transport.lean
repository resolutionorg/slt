/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.LocalExpansion

/-!
# Transport of `L²(q)`-expansions along isometries

No thesis counterpart; used to move the expansions of the chart integrands `a_α` from a chart cube
to its copy in the disjoint union `⊔_α U_α` of the chart cubes ([Hit26]'s `M`), where
[Hit26, Theorem 4.2.9] is applied to the chart process.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {X : Type*} [MeasurableSpace X] {q : Measure X} {U₁ U₂ : Type*} [PseudoMetricSpace U₁]
  [PseudoMetricSpace U₂]

/-- The monomials of an expansion are constant on pairs at distance `0` (by the Lipschitz bound).
No thesis counterpart; used by `L2Expansion.image`. -/
theorem L2Expansion.m_eq_of_dist_eq_zero {g : X → U₁ → ℝ} {B : Set U₁} (E : L2Expansion q g B)
    (i : E.ι) {u v : U₁} (hu : u ∈ B) (hv : v ∈ B) (h : dist u v = 0) : E.m i u = E.m i v := by
  have hle := E.abs_m_sub_le i u hu v hv
  rw [h, mul_zero] at hle
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))

open Classical in
/-- An expansion of `g` on `B ⊆ U₁` transported along a map `ι` that is isometric on `B` to an
expansion of `g'` on `ι '' B`, where `g'(x, ι u) = g(x, u)`. -/
noncomputable def L2Expansion.image {g : X → U₁ → ℝ} {B : Set U₁} (E : L2Expansion q g B)
    (ι : U₁ → U₂) (hι : ∀ u ∈ B, ∀ v ∈ B, dist (ι u) (ι v) = dist u v) (g' : X → U₂ → ℝ)
    (hg : ∀ x, ∀ u ∈ B, g' x (ι u) = g x u) : L2Expansion q g' (ι '' B) :=
  let m' : E.ι → U₂ → ℝ := fun i p ↦ if h : ∃ u ∈ B, ι u = p then E.m i h.choose else 0
  have hm : ∀ i, ∀ u ∈ B, m' i (ι u) = E.m i u := fun i u hu ↦ by
    have h : ∃ v ∈ B, ι v = ι u := ⟨u, hu, rfl⟩
    change (if h : ∃ v ∈ B, ι v = ι u then E.m i h.choose else 0) = E.m i u
    rw [dite_eq_left h]
    exact E.m_eq_of_dist_eq_zero i h.choose_spec.1 hu
      (by rw [← hι _ h.choose_spec.1 u hu, h.choose_spec.2, dist_self])
  { E with
    m := m'
    abs_m_le := by
      rintro i _ ⟨u, hu, rfl⟩
      rw [hm i u hu]
      exact E.abs_m_le i u hu
    abs_m_sub_le := by
      rintro i _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
      rw [hm i u hu, hm i v hv, hι u hu v hv]
      exact E.abs_m_sub_le i u hu v hv
    expansion := by
      rintro _ ⟨u, hu, rfl⟩
      simp only [hm _ u hu, hg _ u hu]
      exact E.expansion u hu }

theorem L2Expansion.HigherMoment.image {g : X → U₁ → ℝ} {B : Set U₁} {E : L2Expansion q g B}
    {s : ℝ≥0∞} (h : E.HigherMoment s) (ι : U₁ → U₂)
    (hι : ∀ u ∈ B, ∀ v ∈ B, dist (ι u) (ι v) = dist u v) (g' : X → U₂ → ℝ)
    (hg : ∀ x, ∀ u ∈ B, g' x (ι u) = g x u) : (E.image ι hι g' hg).HigherMoment s := h

end SingularLearningTheory
