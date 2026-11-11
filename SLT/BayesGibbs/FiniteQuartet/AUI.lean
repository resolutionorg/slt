/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MeasureTheory.Function.AsympUnifIntegrable
public import SLT.BayesGibbs.FiniteSampleMoments

/-!
# Uniform integrability from the quartet dominator

`SingularLearningTheory.BayesGibbs.asympUnifIntegrable_of_quartetDom`: a measurable sequence $Y_n$
with $Y_0 = 0$ and $|Y_n| \le C\,S_n$ almost surely for every $n > 0$ is asymptotically uniformly
integrable. Here $S_n$ is the quartet dominator `SingularLearningTheory.BayesGibbs.quartetDom`,
$1 + L_n^2 + L_n^4 + \frac1n\sum_{i<n}a(X_i)^2 + \frac1n\sum_{i<n}a(X_i)^4$, where $L_n \ge 0$
has uniformly bounded sixth moments, each $X_i$ has law $\mu$, and $a \ge 0$ has $a^6$
integrable for $\mu$. The proof bounds the $3/2$ moments of $Y_n$ uniformly in $n$.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure E} {X : ℕ → Ω → E}

/-- Quartic domination and sixth moments imply asymptotic uniform integrability. The estimates
are conditions at positive `n`; the scaled errors vanish at `n = 0`, so nothing is required
there. -/
theorem asympUnifIntegrable_of_quartetDom
    {Y : ℕ → Ω → ℝ} (hYm : ∀ n, Measurable (Y n)) (hY0 : ∀ ω, Y 0 ω = 0)
    {L : ℕ → Ω → ℝ} (hL0 : ∀ n ω, 0 ≤ L n ω) {CL : ℝ}
    (hL6 : ∀ n, Integrable (fun ω ↦ L n ω ^ 6) P)
    (hL6C : ∀ n, ∫ ω, L n ω ^ 6 ∂P ≤ CL)
    {a : E → ℝ} (ham : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    (ha6 : Integrable (fun x ↦ a x ^ 6) μ)
    (hXm : ∀ j, Measurable (X j)) (hmap : ∀ j, P.map (X j) = μ)
    {Cq : ℝ} (hCq : 0 ≤ Cq)
    (hY : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P, |Y n ω| ≤ Cq * quartetDom (L n ω) a X n ω) :
    AsympUnifIntegrable P Y := by
  let S := fun n ω ↦ quartetDom (L n ω) a X n ω
  let G := fun n ω ↦ Real.sqrt 5 *
    (3 + 2 * L n ω ^ 6 + 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6))
  let CG := Real.sqrt 5 * (3 + 2 * CL + 2 * ∫ x, a x ^ 6 ∂μ)
  have hCL : 0 ≤ CL := (integral_nonneg fun ω ↦ pow_nonneg (hL0 0 ω) 6).trans (hL6C 0)
  have hI : 0 ≤ ∫ x, a x ^ 6 ∂μ := integral_nonneg fun x ↦ pow_nonneg (ha0 x) 6
  have hCG : 0 ≤ CG := by dsimp [CG]; positivity
  have hlinear := fun n hn ↦ linear_dominator_moment hL6 hL6C ham ha6 hXm hmap (n := n) hn
  have hS0 : ∀ n ω, 0 ≤ S n ω := fun n ω ↦ quartetDom_nonneg n ω
  have hSG : ∀ n ω, 0 < n → S n ω ^ (3 / 2 : ℝ) ≤ G n ω :=
    fun n ω hn ↦ quartetDom_rpow_le (hL0 n ω) ha0 hn ω
  have hmoment := moment_of_dominated hYm hY0 hCq hS0 hY
    (fun n hn ↦ (hlinear n hn).1) hCG (fun n hn ↦ (hlinear n hn).2) hSG
  exact asympUnifIntegrable_of_integral_three_halves_le
    (Eventually.of_forall hmoment.1) (Eventually.of_forall hmoment.2)

end SingularLearningTheory.BayesGibbs
