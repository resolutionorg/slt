/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Atlas
public import SLT.EmpiricalProcess.PatchMajorants
public import SLT.MeasureTheory.Integral.Lebesgue.Minkowski
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star

/-!
# A global Lipschitz bound on the cube from majorants on a finite open cover

No thesis counterpart as a named statement. The proof of [Hit26, Theorem 5.2.6]
uses "`∇ξ_n` converges in distribution" to control `|ξ_n(u) − ξ_n(0_P, u_{Pᶜ})|`; here the Lipschitz
majorants `R_{i,n}` of the chart
process on the patches of a finite open cover of the convex cube are chained along the segment
from `u` to `v`, giving `|Ψ_n(u) − Ψ_n(v)| ≤ (Σ_i R_{i,n}) dist(u, v)` for all `u, v` in the cube,
almost surely.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {b : ℝ}

omit [IsProbabilityMeasure P] in
/-- Chaining along segments in the convex cube: majorants of the Lipschitz constants of `Ψ_n` on
the sets of a finite open cover of the cube give a global Lipschitz majorant `Σ_i R_{i,n}`. -/
theorem EmpiricalProcess.enorm_sub_le_sum_of_patchMajorants {ι : Type*} [Fintype ι]
    {B : ι → Set (cube d b)} (hBo : ∀ i, IsOpen (B i)) (hBc : ⋃ i, B i = univ)
    {Ψ : ℕ → Ω → C(cube d b, ℝ)} (M : ∀ i, EmpiricalProcess.PatchMajorants Ψ P (B i)) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ u v : cube d b,
      ‖Ψ n ω u - Ψ n ω v‖ₑ ≤ (∑ i, (M i).R n ω) * edist u v := by
  have hae : ∀ᵐ ω ∂P, ∀ i, ∀ u ∈ B i, ∀ v ∈ B i,
      ‖Ψ n ω u - Ψ n ω v‖ₑ ≤ (M i).R n ω * edist u v :=
    ae_all_iff.mpr fun i ↦ (M i).enorm_sub_le n
  filter_upwards [hae] with ω hω u v
  obtain ⟨δ, hδ, hcov⟩ := lebesgue_number_lemma_of_metric isCompact_univ hBo (by rw [hBc])
  -- the segment from `u` to `v`, sampled at `N` equal steps of length `dist u v / N < δ`
  set N : ℕ := ⌈dist u v / δ⌉₊ + 1 with hN_def
  have hN : (0 : ℝ) < N := by positivity
  have hstep : dist u v / N < δ := by
    rw [div_lt_iff₀ hN]
    have h1 : dist u v / δ < N := by
      calc dist u v / δ ≤ ⌈dist u v / δ⌉₊ := Nat.le_ceil _
        _ < N := by rw [hN_def]; exact_mod_cast Nat.lt_succ_self _
    calc dist u v = dist u v / δ * δ := by field_simp
      _ < N * δ := by gcongr
      _ = δ * N := mul_comm _ _
  have hcube : Convex ℝ (cube d b) := convex_Icc _ _
  have hmem : ∀ m : ℕ,
      (u : Fin d → ℝ) + (((min m N : ℕ) : ℝ) / N) • ((v : Fin d → ℝ) - u) ∈ cube d b := fun m ↦
    hcube.add_smul_sub_mem u.2 v.2
      ⟨by positivity, by rw [div_le_one hN]; exact_mod_cast min_le_right m N⟩
  let w : ℕ → cube d b := fun m ↦ ⟨_, hmem m⟩
  have hw0 : w 0 = u := by
    ext1; simp [w]
  have hwN : w N = v := by
    ext1; simp [w]
  have hdist : ∀ m, m < N → dist (w m) (w (m + 1)) = dist u v / N := by
    intro m hm
    rw [Subtype.dist_eq, dist_eq_norm]
    simp only [w, Nat.min_eq_left hm.le, Nat.min_eq_left (Nat.succ_le_of_lt hm)]
    have : (u : Fin d → ℝ) + ((m : ℝ) / N) • ((v : Fin d → ℝ) - u) -
        ((u : Fin d → ℝ) + (((m + 1 : ℕ) : ℝ) / N) • ((v : Fin d → ℝ) - u)) =
        (-(1 / (N : ℝ))) • ((v : Fin d → ℝ) - u) := by
      push_cast
      rw [add_sub_add_left_eq_sub, ← sub_smul]; congr 1; ring
    rw [this, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos (by positivity),
      ← dist_eq_norm, Subtype.dist_eq, dist_comm]
    ring
  have hterm : ∀ m, m < N →
      edist (Ψ n ω (w m)) (Ψ n ω (w (m + 1))) ≤ (∑ i, (M i).R n ω) * edist (w m) (w (m + 1)) := by
    intro m hm
    obtain ⟨i, hi⟩ := hcov (w m) (mem_univ _)
    have h1 : w m ∈ B i := hi (Metric.mem_ball_self hδ)
    have h2 : w (m + 1) ∈ B i := hi (by
      rw [Metric.mem_ball, dist_comm, hdist m hm]; exact hstep)
    calc edist (Ψ n ω (w m)) (Ψ n ω (w (m + 1)))
        = ‖Ψ n ω (w m) - Ψ n ω (w (m + 1))‖ₑ := edist_eq_enorm_sub _ _
      _ ≤ (M i).R n ω * edist (w m) (w (m + 1)) := hω i _ h1 _ h2
      _ ≤ (∑ i, (M i).R n ω) * edist (w m) (w (m + 1)) := by
        gcongr
        exact Finset.single_le_sum (f := fun i ↦ (M i).R n ω) (fun _ _ ↦ zero_le)
          (Finset.mem_univ i)
  have hsum : ∑ m ∈ Finset.range N, edist (w m) (w (m + 1)) = edist u v := by
    rw [Finset.sum_congr rfl fun m hm ↦ by
      rw [edist_dist, hdist m (Finset.mem_range.mp hm)]]
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (Nat.cast_nonneg _), mul_div_cancel₀ _ hN.ne', edist_dist]
  calc ‖Ψ n ω u - Ψ n ω v‖ₑ = edist (Ψ n ω (w 0)) (Ψ n ω (w N)) := by
        rw [hw0, hwN, edist_eq_enorm_sub]
    _ ≤ ∑ m ∈ Finset.range N, edist (Ψ n ω (w m)) (Ψ n ω (w (m + 1))) :=
        edist_le_range_sum_edist (fun m ↦ Ψ n ω (w m)) N
    _ ≤ ∑ m ∈ Finset.range N, (∑ i, (M i).R n ω) * edist (w m) (w (m + 1)) :=
        Finset.sum_le_sum fun m hm ↦ hterm m (Finset.mem_range.mp hm)
    _ = (∑ i, (M i).R n ω) * edist u v := by rw [← Finset.mul_sum, hsum]

end SingularLearningTheory
