/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Log Partition Taylor
-/

public section

open Set

namespace SingularLearningTheory.BayesGibbs

/-- **Third-order Taylor bound by fencing.** If `φ, φ', φ''` are differentiable on `[0,1]` with
`φ(0) = φ'(0) = φ''(0) = 0` and `|φ'''| ≤ C` on `[0,1]`, then `|φ(1)| ≤ C/6`. -/
private theorem abs_le_of_third_deriv_le {φ φ' φ'' φ''' : ℝ → ℝ} {C : ℝ}
    (h0 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ (φ' s) s)
    (h1 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ' (φ'' s) s)
    (h2 : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt φ'' (φ''' s) s)
    (hφ0 : φ 0 = 0) (hφ'0 : φ' 0 = 0) (hφ''0 : φ'' 0 = 0)
    (hC : ∀ s ∈ Icc (0 : ℝ) 1, |φ''' s| ≤ C) : |φ 1| ≤ C / 6 := by
  -- `|φ''(s)| ≤ C s`
  have step2 : ∀ s ∈ Icc (0 : ℝ) 1, ‖φ'' s‖ ≤ C * s := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f' := φ''')
      (fun s hs ↦ (h2 s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (h2 s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (B := fun s ↦ C * s) (B' := fun _ ↦ C) (by simp [hφ''0])
      (fun s ↦ by simpa using (hasDerivAt_id s).const_mul C)
      (fun s hs ↦ by rw [Real.norm_eq_abs]; exact hC s (Ico_subset_Icc_self hs))
  -- `|φ'(s)| ≤ C s²/2`
  have step1 : ∀ s ∈ Icc (0 : ℝ) 1, ‖φ' s‖ ≤ C * s ^ 2 / 2 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f' := φ'')
      (fun s hs ↦ (h1 s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (h1 s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (B := fun s ↦ C * s ^ 2 / 2) (B' := fun s ↦ C * s) (by simp [hφ'0])
      (fun s ↦ by
        have := (((hasDerivAt_id s).pow 2).const_mul C).div_const 2
        exact this.congr_deriv (by simp; ring))
      (fun s hs ↦ step2 s (Ico_subset_Icc_self hs))
  -- `|φ(s)| ≤ C s³/6`
  have step0 : ∀ s ∈ Icc (0 : ℝ) 1, ‖φ s‖ ≤ C * s ^ 3 / 6 := by
    refine image_norm_le_of_norm_deriv_right_le_deriv_boundary (f' := φ')
      (fun s hs ↦ (h0 s hs).continuousAt.continuousWithinAt)
      (fun s hs ↦ (h0 s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
      (B := fun s ↦ C * s ^ 3 / 6) (B' := fun s ↦ C * s ^ 2 / 2) (by simp [hφ0])
      (fun s ↦ by
        have := (((hasDerivAt_id s).pow 3).const_mul C).div_const 6
        exact this.congr_deriv (by simp; ring))
      (fun s hs ↦ step1 s (Ico_subset_Icc_self hs))
  have := step0 1 (by simp)
  simpa using this

/-- **The log-partition Taylor lemma.** If `I₀ > 0` on `[0,1]`, `I₀' = I₁`, `I₁' = I₂`, `I₂' = I₃`
there, and the third cumulant `q₃ − 3q₁q₂ + 2q₁³` (`q_j = I_j/I₀`) is bounded by `C` on `[0,1]`,
then `|log I₀(1) − log I₀(0) − q₁(0) − (q₂(0) − q₁(0)²)/2| ≤ C/6`. -/
theorem abs_log_taylor_le {I₀ I₁ I₂ I₃ : ℝ → ℝ} {C : ℝ}
    (hpos : ∀ a ∈ Icc (0 : ℝ) 1, 0 < I₀ a)
    (h0 : ∀ a ∈ Icc (0 : ℝ) 1, HasDerivAt I₀ (I₁ a) a)
    (h1 : ∀ a ∈ Icc (0 : ℝ) 1, HasDerivAt I₁ (I₂ a) a)
    (h2 : ∀ a ∈ Icc (0 : ℝ) 1, HasDerivAt I₂ (I₃ a) a)
    (hC : ∀ a ∈ Icc (0 : ℝ) 1,
      |I₃ a / I₀ a - 3 * (I₁ a / I₀ a) * (I₂ a / I₀ a) + 2 * (I₁ a / I₀ a) ^ 3| ≤ C) :
    |Real.log (I₀ 1) - Real.log (I₀ 0) - I₁ 0 / I₀ 0 - (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2) / 2|
      ≤ C / 6 := by
  have hq1 : ∀ a ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun a ↦ I₁ a / I₀ a) (I₂ a / I₀ a - (I₁ a / I₀ a) ^ 2) a := by
    intro a ha
    have hne := (hpos a ha).ne'
    have := (h1 a ha).div (h0 a ha) hne
    refine this.congr_deriv (Eq.symm ?_)
    field_simp
  have hq2 : ∀ a ∈ Icc (0 : ℝ) 1,
      HasDerivAt (fun a ↦ I₂ a / I₀ a) (I₃ a / I₀ a - I₂ a / I₀ a * (I₁ a / I₀ a)) a := by
    intro a ha
    have hne := (hpos a ha).ne'
    have := (h2 a ha).div (h0 a ha) hne
    refine this.congr_deriv (Eq.symm ?_)
    field_simp
  have key := abs_le_of_third_deriv_le
    (φ := fun a ↦ Real.log (I₀ a) - Real.log (I₀ 0) - a * (I₁ 0 / I₀ 0)
      - a ^ 2 * (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2) / 2)
    (φ' := fun a ↦ I₁ a / I₀ a - I₁ 0 / I₀ 0 - a * (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2))
    (φ'' := fun a ↦ I₂ a / I₀ a - (I₁ a / I₀ a) ^ 2 - (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2))
    (φ''' := fun a ↦ I₃ a / I₀ a - 3 * (I₁ a / I₀ a) * (I₂ a / I₀ a) + 2 * (I₁ a / I₀ a) ^ 3)
    (C := C) ?_ ?_ ?_ (by simp) (by simp) (by simp) hC
  · convert key using 2
    ring
  · intro a ha
    have hne := (hpos a ha).ne'
    have hlog := (h0 a ha).log hne
    have := ((hlog.sub_const (Real.log (I₀ 0))).sub
      ((hasDerivAt_id a).mul_const (I₁ 0 / I₀ 0))).sub
      ((((hasDerivAt_id a).pow 2).mul_const (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2)).div_const 2)
    refine this.congr_deriv (Eq.symm ?_)
    simp
    ring
  · intro a ha
    have := ((hq1 a ha).sub_const (I₁ 0 / I₀ 0)).sub
      ((hasDerivAt_id a).mul_const (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2))
    refine this.congr_deriv (Eq.symm ?_)
    simp
  · intro a ha
    have := ((hq2 a ha).sub ((hq1 a ha).pow 2)).sub_const (I₂ 0 / I₀ 0 - (I₁ 0 / I₀ 0) ^ 2)
    refine this.congr_deriv (Eq.symm ?_)
    simp
    ring

end SingularLearningTheory.BayesGibbs
