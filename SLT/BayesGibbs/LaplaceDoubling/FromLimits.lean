/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Laplace.Asymptotic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Doubling bounds from normalized limits

`SingularLearningTheory.BayesGibbs.eventually_doubling_of_normalized_limits`: if $s_n > 0$ for large
$n$, $s_n J_1(n) \to c_1$ and $s_n J_2(n) \to c_2 > 0$, then there is $D \ge 1$ with
$J_1(n) \le D J_2(n)$ for all large $n$. Applied to the Laplace integrals
$\int e^{-n\beta K/4}\,d\nu$ and $\int e^{-3n\beta K/2}\,d\nu$ of the prior, whose normalized
limits are positive, it gives the Laplace doubling bound that the finite-sample posterior bounds
assume.
-/

public section

open Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- The sharp Laplace limits at temperatures β/4 and 3β/2
supply the eventual doubling premise of the finite-sample posterior bounds.
A finite prefix of sample sizes is irrelevant to both limit and AUI. -/
theorem eventually_doubling_of_normalized_limits {s J₁ J₂ : ℕ → ℝ} {c₁ c₂ : ℝ}
    (hs : ∀ᶠ n in atTop, 0 < s n)
    (h₁ : Tendsto (fun n ↦ s n * J₁ n) atTop (𝓝 c₁))
    (h₂ : Tendsto (fun n ↦ s n * J₂ n) atTop (𝓝 c₂)) (hc₂ : 0 < c₂) :
    ∃ D : ℝ, 1 ≤ D ∧ ∀ᶠ n in atTop, J₁ n ≤ D * J₂ n := by
  let D := max 1 ((|c₁| + 1) / (c₂ / 2))
  have hD : 1 ≤ D := le_max_left _ _
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hDc : |c₁| + 1 ≤ D * (c₂ / 2) :=
    (div_le_iff₀ (half_pos hc₂)).mp (le_max_right _ _)
  refine ⟨D, hD, ?_⟩
  filter_upwards [hs, h₁.eventually (eventually_lt_nhds (show c₁ < |c₁| + 1 by
      linarith [le_abs_self c₁])),
    h₂.eventually (eventually_gt_nhds (show c₂ / 2 < c₂ by linarith))] with n hsn h1n h2n
  have hb : s n * J₁ n ≤ D * (s n * J₂ n) :=
    h1n.le.trans (hDc.trans (mul_le_mul_of_nonneg_left h2n.le hD0))
  exact (mul_le_mul_iff_right₀ hsn).mp (by simpa only [mul_left_comm D] using hb)

end SingularLearningTheory.BayesGibbs
