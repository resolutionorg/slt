/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.Discharge
public import SLT.Resolution.Atlas
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Approximating chart marks by primary-Lipschitz marks

On a compact metric space with a continuous idempotent projection $\pi$ and a continuous
$s \ge 0$ that vanishes on the image of $\pi$ and bounds the distance to it,
`SingularLearningTheory.BayesGibbs.exists_primary_amplitude_approx` approximates a continuous function
$A$ uniformly within $\varepsilon$ by a continuous $B$ with $B \circ \pi = A \circ \pi$ and
$|B(u) - B(\pi u)| \le L\,s(u)$. `SingularLearningTheory.ResolutionAtlas.exists_chart_amplitude_approx`
applies this on a chart cube of a resolution atlas, with $\pi$ setting the primary coordinates to
zero and $s$ their sum. It extends the frozen-kernel limits from marks with a Lipschitz bound in
the primary coordinates to all continuous marks, without changing their trace on the face where
the primary coordinates vanish.
-/

public section

open Set Filter Topology MeasureTheory

namespace SingularLearningTheory.BayesGibbs

/-- Approximate a continuous amplitude by one with a linear modulus toward a
projection, preserving its trace on the projection exactly. This is enough for
frozen-kernel limits; no smooth approximation theorem is required. -/
private theorem exists_primary_amplitude_approx
    {U : Type*} [MetricSpace U] [CompactSpace U]
    (π : U → U) (hπ : Continuous π) (hππ : ∀ u, π (π u) = π u)
    (s : U → ℝ) (hsc : Continuous s) (hs : ∀ u, 0 ≤ s u)
    (hsπ : ∀ u, s (π u) = 0) (hd : ∀ u, dist u (π u) ≤ s u)
    (A : C(U, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ B : C(U, ℝ), ∃ L : ℝ, ‖B - A‖ ≤ ε ∧
      (∀ u, B (π u) = A (π u)) ∧
      (∀ u, |B u - B (π u)| ≤ L * s u) := by
  obtain ⟨δ, hδ, hmod⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous A.continuous) ε hε
  let θ : U → ℝ := fun u ↦ min 1 (s u / δ)
  have hθc : Continuous θ := continuous_const.min (hsc.div_const δ)
  have hθ0 : ∀ u, 0 ≤ θ u := fun u ↦ le_min zero_le_one (div_nonneg (hs u) hδ.le)
  have hθ1 : ∀ u, θ u ≤ 1 := fun u ↦ min_le_left _ _
  have hθs : ∀ u, θ u ≤ s u / δ := fun u ↦ min_le_right _ _
  have hθπ : ∀ u, θ (π u) = 0 := by intro u; simp [θ, hsπ u]
  let B : C(U, ℝ) := ⟨fun u ↦ (1 - θ u) * A (π u) + θ u * A u,
    ((continuous_const.sub hθc).mul (A.continuous.comp hπ)).add (hθc.mul A.continuous)⟩
  have htrace : ∀ u, B (π u) = A (π u) := by
    intro u
    change (1 - θ (π u)) * A (π (π u)) + θ (π u) * A (π u) = _
    rw [hθπ, hππ]
    ring
  refine ⟨B, 2 * ‖A‖ / δ, ?_, htrace, ?_⟩
  · apply (ContinuousMap.norm_le _ hε.le).mpr
    intro u
    change ‖B u - A u‖ ≤ ε
    have heq : B u - A u = (1 - θ u) * (A (π u) - A u) := by dsimp [B]; ring
    rw [heq, Real.norm_eq_abs, abs_mul, abs_of_nonneg (sub_nonneg.mpr (hθ1 u))]
    by_cases hu : s u < δ
    · have hm : |A (π u) - A u| ≤ ε := by
        rw [abs_sub_comm]
        simpa only [Real.dist_eq] using (hmod ((hd u).trans_lt hu)).le
      calc (1 - θ u) * |A (π u) - A u| ≤ 1 * |A (π u) - A u| :=
          mul_le_mul_of_nonneg_right (by linarith [hθ0 u]) (abs_nonneg _)
        _ ≤ ε := by simpa using hm
    · have hθeq : θ u = 1 := min_eq_left ((le_div_iff₀ hδ).mpr (by linarith))
      rw [hθeq, sub_self, zero_mul]
      exact hε.le
  · intro u
    rw [htrace]
    have heq : B u - A (π u) = θ u * (A u - A (π u)) := by dsimp [B]; ring
    rw [heq, abs_mul, abs_of_nonneg (hθ0 u)]
    have hA : |A u - A (π u)| ≤ 2 * ‖A‖ := by
      calc |A u - A (π u)| ≤ |A u| + |A (π u)| := abs_sub _ _
        _ ≤ ‖A‖ + ‖A‖ := add_le_add
          (by simpa only [Real.norm_eq_abs] using A.norm_coe_le_norm u)
          (by simpa only [Real.norm_eq_abs] using A.norm_coe_le_norm (π u))
        _ = _ := by ring
    calc θ u * |A u - A (π u)| ≤ (s u / δ) * (2 * ‖A‖) :=
        mul_le_mul (hθs u) hA (abs_nonneg _) (div_nonneg (hs u) hδ.le)
      _ = _ := by ring

end SingularLearningTheory.BayesGibbs

namespace SingularLearningTheory.ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- Continuous chart marks admit primary-Lipschitz approximations with
exactly the same frozen trace. -/
theorem exists_chart_amplitude_approx (α : R.ι) (A : C(cube d (R.b α), ℝ))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ B : C(cube d (R.b α), ℝ), ∃ L : ℝ, ‖B - A‖ ≤ ε ∧
      (∀ u : cube d (R.b α), B (R.primaryZero α u) = A (R.primaryZero α u)) ∧
      (∀ u : cube d (R.b α), |B u - B (R.primaryZero α u)| ≤
        L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j) := by
  have hc : ∀ u : cube d (R.b α), ∀ j,
      (R.primaryZero α u : Fin d → ℝ) j = if j ∈ R.primary α then 0 else (u : Fin d → ℝ) j := by
    intro u j
    simp only [primaryZero]
    rw [min_eq_right (mem_cube.1 u.2 j).2, max_eq_right (mem_cube.1 u.2 j).1]
  apply BayesGibbs.exists_primary_amplitude_approx
    (π := fun u : cube d (R.b α) ↦ R.primaryZero α u)
    ((R.continuous_primaryZero α).comp continuous_subtype_val)
    (s := fun u ↦ ∑ j ∈ R.primary α, (u : Fin d → ℝ) j)
  · intro u
    apply Subtype.ext
    funext j
    simp only [hc]
    split_ifs <;> rfl
  · exact continuous_finsetSum _ fun j _ ↦ (continuous_apply j).comp continuous_subtype_val
  · intro u
    exact Finset.sum_nonneg fun j _ ↦ u.2.1 j
  · intro u
    exact Finset.sum_eq_zero fun j hj ↦ by rw [hc, if_pos hj]
  · exact R.dist_primaryZero_le α
  · exact hε

end SingularLearningTheory.ResolutionAtlas
