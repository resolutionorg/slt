/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.LocalQuotient

/-!
# Points with positive coordinates in the cube

`SingularLearningTheory.eq_of_eqOn_posCoords` shows that the points of the cube $[0, b]^d$ with all
coordinates positive are dense in every relatively open subset. Two functions continuous at a
point $u$ of the cube that agree at the points with positive coordinates in an open neighborhood
of $u$ agree at $u$. The proof approaches $u$ along the segment towards the center
$(b/2, \dots, b/2)$. It extends to the whole cube identities proved where all coordinates are
positive, such as those obtained by dividing by a monomial.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

section Cube

variable {d : ℕ} {b : ℝ}

/-- Points of the cube with all coordinates positive are dense in every relatively open subset:
two functions continuous at `u` that agree on such points of an open neighbourhood of `u` agree
at `u` (approach `u` along the segment towards the centre `(b/2, …, b/2)`). -/
theorem eq_of_eqOn_posCoords (hb : 0 < b) {O : Set (cube d b)} (hO : IsOpen O)
    {u : cube d b} (hu : u ∈ O) {φ ψ : cube d b → ℝ} (hφ : ContinuousAt φ u)
    (hψ : ContinuousAt ψ u) (h : ∀ v ∈ O, (∀ j, 0 < (v : Fin d → ℝ) j) → φ v = ψ v) :
    φ u = ψ u := by
  -- the segment from `u` towards the centre, parametrised by `θ` clamped to `[0, 1]`
  have hmem : ∀ θ : ℝ,
      (fun j ↦ (1 - max 0 (min θ 1)) * (u : Fin d → ℝ) j + max 0 (min θ 1) * (b / 2))
        ∈ cube d b := by
    intro θ
    refine mem_cube.2 fun j ↦ ?_
    have hθ0 : 0 ≤ max 0 (min θ 1) := le_max_left _ _
    have hθ1 : max 0 (min θ 1) ≤ 1 := max_le zero_le_one (min_le_right _ _)
    have hu0 := u.2.1 j
    have hub := u.2.2 j
    constructor
    · exact add_nonneg (mul_nonneg (by linarith) hu0) (mul_nonneg hθ0 (by linarith))
    · nlinarith [mul_nonneg (sub_nonneg.2 hθ1) (sub_nonneg.2 hub)]
  set γ : ℝ → cube d b := fun θ ↦ ⟨_, hmem θ⟩ with hγ_def
  have hγ : Continuous γ := by
    refine Continuous.subtype_mk (continuous_pi fun j ↦ ?_) _
    exact ((continuous_const.sub (continuous_const.max (continuous_id.min continuous_const))).mul
      continuous_const).add ((continuous_const.max (continuous_id.min continuous_const)).mul
      continuous_const)
  have hγ0 : γ 0 = u := by
    apply Subtype.ext
    funext j
    simp [hγ_def]
  have hpos : ∀ θ ∈ Ioo (0 : ℝ) 1, ∀ j, 0 < (γ θ : Fin d → ℝ) j := by
    intro θ hθ j
    obtain ⟨h0, h1⟩ := hθ
    have hu0 := u.2.1 j
    simp only [hγ_def, min_eq_left h1.le, max_eq_right h0.le]
    have : 0 ≤ (1 - θ) * (u : Fin d → ℝ) j := mul_nonneg (by linarith) hu0
    have : 0 < θ * (b / 2) := by positivity
    linarith
  have hO' : ∀ᶠ θ in 𝓝 (0 : ℝ), γ θ ∈ O := by
    have := hγ.continuousAt (x := 0)
    rw [ContinuousAt, hγ0] at this
    exact this (hO.mem_nhds hu)
  have hIoo : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ ∈ Ioo (0 : ℝ) 1 := by
    have h1 : ∀ᶠ θ in 𝓝[>] (0 : ℝ), θ < 1 :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds zero_lt_one)
    filter_upwards [self_mem_nhdsWithin, h1] with θ hθ hθ1
    exact ⟨hθ, hθ1⟩
  have hγt : Tendsto γ (𝓝[>] (0 : ℝ)) (𝓝 u) := by
    rw [← hγ0]
    exact tendsto_nhdsWithin_of_tendsto_nhds hγ.continuousAt
  have heq : (fun θ ↦ φ (γ θ)) =ᶠ[𝓝[>] (0 : ℝ)] fun θ ↦ ψ (γ θ) := by
    filter_upwards [hIoo, eventually_nhdsWithin_of_eventually_nhds hO'] with θ hθ hθO
    exact h _ hθO (hpos θ hθ)
  exact tendsto_nhds_unique ((hφ.tendsto.comp hγt).congr' heq) (hψ.tendsto.comp hγt)

end Cube

end SingularLearningTheory
