/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.NormalCrossing
public import SLT.Resolution.Atlas

/-!
# Elementary properties of the resolution atlas

The resolution of singularities is the hypothesis structure `ResolutionAtlas`
(`Resolution/Atlas.lean`, [Hit26, Theorem 3.3.1]
in the form of [Hit26, Section 3.3.1]). This
module proves the elementary facts about its invariants `λ_α, m_α, λ, m` that the free
energy proofs use.

| Thesis | Lean |
| --- | --- |
| [Hit26, Equation (5.2.9)] | |
| | `ResolutionAtlas.not_isEssential_iff` |

`ResolutionAtlas` supplies the chart data used by
[Hit26, Theorem 3.3.9] and [Hit26, Theorem 5.2.6].
Its construction and hypotheses are in `Resolution/FromHironaka.lean`.
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

variable {d : ℕ}

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

theorem primary_nonempty (α : R.ι) : (R.primary α).Nonempty := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (activeSet_nonempty R α) (R.ratio α)
  exact ⟨j, R.mem_primary.mpr ⟨hj, hjeq.symm⟩⟩

theorem chartMult_pos (α : R.ι) : 0 < R.chartMult α :=
  Finset.card_pos.mpr (R.primary_nonempty α)

theorem mult_pos : 0 < R.mult := by
  obtain ⟨α, hα, hαeq⟩ := Finset.exists_mem_eq_sup' (minimalCharts_nonempty R) R.chartMult
  rw [mult, hαeq]
  exact R.chartMult_pos α

theorem rlct_le_chartRlct (α : R.ι) : R.rlct ≤ R.chartRlct α :=
  Finset.inf'_le _ (Finset.mem_univ α)

theorem chartMult_le_mult {α : R.ι} (hα : R.chartRlct α = R.rlct) : R.chartMult α ≤ R.mult :=
  Finset.le_sup' R.chartMult (Finset.mem_filter.mpr ⟨Finset.mem_univ α, hα⟩)

/-- A non-essential chart has `λ_α > λ`, or `λ_α = λ` and `m_α < m` ([Hit26,
Equation (5.2.9)]). -/
theorem not_isEssential_iff (α : R.ι) :
    ¬ R.IsEssential α ↔ R.rlct < R.chartRlct α ∨
      (R.chartRlct α = R.rlct ∧ R.chartMult α < R.mult) := by
  unfold IsEssential
  constructor
  · intro hne
    rcases (R.rlct_le_chartRlct α).lt_or_eq with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq.symm, lt_of_le_of_ne (R.chartMult_le_mult heq.symm)
        fun hm ↦ hne ⟨heq.symm, hm⟩⟩
  · rintro (hlt | ⟨heq, hlt⟩) ⟨h1, h2⟩
    · exact hlt.ne' h1
    · exact hlt.ne h2

/-- An atlas for `K` is an atlas for any `K'` agreeing with `K` on `W`: the atlas uses the
potential only on `W`. No thesis counterpart. -/
@[expose] protected def congr {K' : (Fin d → ℝ) → ℝ} (h : ∀ w ∈ W, K w = K'
    w) : ResolutionAtlas K' φ W :=
  { R with
    monomial := fun α u hu ↦ by rw [← h _ (R.g_mapsTo α hu)]; exact R.monomial α u hu
    χ_eq_one := fun w hw hK ↦ R.χ_eq_one w hw (by rwa [h w hw]) }

@[simp] theorem congr_ι {K' : (Fin d → ℝ) → ℝ} (h : ∀ w ∈ W, K w = K' w) :
    (R.congr h).ι = R.ι := rfl

theorem congr_rlct {K' : (Fin d → ℝ) → ℝ} (h : ∀ w ∈ W, K w = K' w) :
    (R.congr h).rlct = R.rlct := rfl

theorem congr_mult {K' : (Fin d → ℝ) → ℝ} (h : ∀ w ∈ W, K w = K' w) :
    (R.congr h).mult = R.mult := rfl

end ResolutionAtlas

/-- `ResolutionAtlas.congr` for a nondegenerate atlas. No thesis counterpart. -/
@[expose] protected def NondegenerateResolutionAtlas.congr {K K' φ : (Fin d → ℝ) → ℝ}
    {W : Set (Fin d → ℝ)}
    (R : NondegenerateResolutionAtlas K φ W) (h : ∀ w ∈ W, K w = K' w) :
    NondegenerateResolutionAtlas K' φ W :=
  { R.toResolutionAtlas.congr h with traceMass_pos := R.traceMass_pos }

end SingularLearningTheory
