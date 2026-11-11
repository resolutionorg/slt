/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CompactPosterior.RatioProbability
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-!
# Products of tight factors with vanishing errors

If $X_n$ is tight, so that for every $\eta > 0$ there is $M$ with $P(|X_n| > M) \le \eta$ for all
large $n$, and $Y_n \to 0$ in probability, then $X_nY_n \to 0$ in probability, with no
independence or joint limit assumed
(`MeasureTheory.tendstoInMeasure_mul_zero_of_tight`). The proofs of the Bayes and
Gibbs asymptotics use it to discard error terms that are a vanishing error times a random factor
bounded in probability.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

/-- A tight random factor times an error converging to zero in probability
also converges to zero. No independence or joint weak limit is required. -/
theorem _root_.MeasureTheory.tendstoInMeasure_mul_zero_of_tight {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : ℕ → Ω → ℝ}
    (hX : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < |X n ω|} ≤ ENNReal.ofReal η)
    (hY : TendstoInMeasure P Y atTop 0) :
    TendstoInMeasure P (fun n ω ↦ X n ω * Y n ω) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hY ⊢
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact ⟨0, fun _ _ ↦ le_top⟩
  have hηr : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨M, N₁, hN₁⟩ := hX (η.toReal / 2) (half_pos hηr)
  let M' := |M| + 1
  have hM' : 0 < M' := by dsimp [M']; positivity
  have hMY := hY (ε / M') (div_pos hε hM')
  rw [ENNReal.tendsto_atTop_zero] at hMY
  obtain ⟨N₂, hN₂⟩ := hMY (ENNReal.ofReal (η.toReal / 2))
    (ENNReal.ofReal_pos.mpr (half_pos hηr))
  refine ⟨max N₁ N₂, fun n hn ↦ ?_⟩
  calc
    P {ω | ε ≤ ‖X n ω * Y n ω - (0 : Ω → ℝ) ω‖} ≤
        P ({ω | M < |X n ω|} ∪ {ω | ε / M' ≤ ‖Y n ω - (0 : Ω → ℝ) ω‖}) := by
      apply measure_mono
      intro ω hω
      simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_mul, mem_setOf_eq, mem_union] at hω ⊢
      by_contra h
      push_neg at h
      have hx : |X n ω| ≤ M' := h.1.trans (by dsimp [M']; linarith [le_abs_self M])
      have hy : M' * |Y n ω| < ε := by
        have := (lt_div_iff₀ hM').mp h.2
        nlinarith
      have := mul_le_mul_of_nonneg_right hx (abs_nonneg (Y n ω))
      linarith
    _ ≤ P {ω | M < |X n ω|} + P {ω | ε / M' ≤ ‖Y n ω - (0 : Ω → ℝ) ω‖} :=
      measure_union_le _ _
    _ ≤ ENNReal.ofReal (η.toReal / 2) + ENNReal.ofReal (η.toReal / 2) :=
      add_le_add (hN₁ n (le_of_max_le_left hn)) (hN₂ n (le_of_max_le_right hn))
    _ = η := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
        ENNReal.ofReal_toReal hηtop]

end SingularLearningTheory.BayesGibbs
