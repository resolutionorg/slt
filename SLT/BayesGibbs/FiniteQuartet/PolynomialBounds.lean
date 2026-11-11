/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FiniteSampleMoments
public import SLT.BayesGibbs.GeneralizedTaylor
public import SLT.BayesGibbs.Posterior.KernelError
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Polynomial bounds on the scaled errors

Bounds on the four scaled errors $nB_g, nB_t, nG_g, nG_t$ and the functional variance $V$ by one
polynomial $C\,(1 + L^2 + L^4 + a_2 + a_4)$, where $L$ controls $\sqrt n\,|K_n - K|$ relative to
$\sqrt K$ and $a_2, a_4$ are the empirical second and fourth moments of the data envelope $A$.
The constant $C$ depends only on $\beta$, the Laplace doubling constant and the population moments
$E_q[A^2], E_q[A^4]$. The bounds use no exponential moment of $A$. Bounds of this form give the
asymptotic uniform integrability of the five observables.

## Main results

* `SingularLearningTheory.BayesGibbs.fresh_predictive_polynomial_bound`: integrating the single-datum
  second-order estimate over $q$ bounds $n|B_g - G_g|$ by the second and fourth population moments
  of $A$.
* `SingularLearningTheory.BayesGibbs.training_predictive_polynomial_bound`: the same bound for
  $n|B_t - G_t|$ with the empirical moments $a_2, a_4$.
* `SingularLearningTheory.BayesGibbs.quartet_polynomial_domination`: one explicit polynomial in
  $L, a_2, a_4$ dominates all five observables.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- Integrating the single-datum second-order estimate only costs the second
and fourth data-envelope moments. No exponential moment is used. -/
theorem fresh_predictive_polynomial_bound {X : Type*} [MeasurableSpace X]
    {q : Measure X} {b g A : X → ℝ} {n β c L : ℝ}
    (hn : 0 < n) (hs : 1 ≤ Real.sqrt n) (hβ : 0 < β)
    (hb : AEStronglyMeasurable b q) (hg : Integrable g q)
    (hA2 : Integrable (fun x ↦ A x ^ 2) q) (hA4 : Integrable (fun x ↦ A x ^ 4) q)
    (hbound : ∀ᵐ x ∂q, n * |b x - g x| ≤
      A x ^ 2 / 2 * (c + 4 * (L + A x / (β * Real.sqrt n)) ^ 2)) :
    Integrable b q ∧ n * |(∫ x, b x ∂q) - ∫ x, g x ∂q| ≤
      (c / 2 + 4 * L ^ 2) * (∫ x, A x ^ 2 ∂q) +
        4 / β ^ 2 * (∫ x, A x ^ 4 ∂q) := by
  let H := fun x ↦ (c / 2 + 4 * L ^ 2) * A x ^ 2 + 4 / β ^ 2 * A x ^ 4
  have hHi : Integrable H q := (hA2.const_mul _).add (hA4.const_mul _)
  have hpt : ∀ᵐ x ∂q, |n * b x - n * g x| ≤ H x := by
    filter_upwards [hbound] with x hx
    have h := tilt_pointwise_le (c := c) (L := L) (a := A x) hβ hs
    rw [← mul_sub, abs_mul, abs_of_pos hn]
    dsimp only [H]
    refine hx.trans ?_
    convert div_le_div_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  obtain ⟨hbi, hbb⟩ := abs_integral_predictive_sub_mean_le (hb.const_mul n)
    (hg.const_mul n) hHi hpt
  have hbint : Integrable b q := (hbi.const_mul n⁻¹).congr
    (.of_forall fun x ↦ by field_simp)
  refine ⟨hbint, ?_⟩
  rw [integral_const_mul, integral_const_mul, ← mul_sub, abs_mul, abs_of_pos hn,
    integral_add (hA2.const_mul _) (hA4.const_mul _), integral_const_mul,
    integral_const_mul] at hbb
  exact hbb

/-- Training integration is the same polynomial bound, with empirical
second and fourth moments in place of population moments. -/
theorem training_predictive_polynomial_bound {n : ℕ} (hn : 0 < n)
    {b g A : ℕ → ℝ} {β c L : ℝ} (hβ : 0 < β)
    (hbound : ∀ i < n, (n : ℝ) * |b i - g i| ≤
      A i ^ 2 / 2 * (c + 4 * (L + A i / (β * Real.sqrt n)) ^ 2)) :
    |(∑ i ∈ Finset.range n, b i) - ∑ i ∈ Finset.range n, g i| ≤
      (c / 2 + 4 * L ^ 2) * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A i ^ 2) +
        4 / β ^ 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A i ^ 4) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : (1 : ℝ) ≤ Real.sqrt n := Real.one_le_sqrt.mpr (Nat.one_le_cast.mpr hn)
  have hpt : ∀ i ∈ Finset.range n, |b i - g i| ≤
      ((c / 2 + 4 * L ^ 2) * A i ^ 2 + 4 / β ^ 2 * A i ^ 4) / n := by
    intro i hi
    apply (le_div_iff₀ hn').mpr
    have h := hbound i (Finset.mem_range.mp hi)
    have ht := tilt_pointwise_le (c := c) (L := L) (a := A i) hβ hs
    rw [mul_comm]
    refine h.trans ?_
    convert div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 2) using 1 <;> ring
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hpt).trans (le_of_eq ?_))
  rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

/-- All terms in this polynomial are individually dominated by the common
quartet polynomial. This small algebraic API avoids repeated norm estimates. -/
private theorem polynomial_le_coefficient_mul_quartet {L a2 a4 c0 c2 c4 d2 d4 : ℝ}
    (ha2 : 0 ≤ a2) (ha4 : 0 ≤ a4)
    (h0 : 0 ≤ c0) (h2 : 0 ≤ c2) (h4 : 0 ≤ c4) (hd2 : 0 ≤ d2) (hd4 : 0 ≤ d4) :
    c0 + c2 * L ^ 2 + c4 * L ^ 4 + d2 * a2 + d4 * a4 ≤
      (c0 + c2 + c4 + d2 + d4) * (1 + L ^ 2 + L ^ 4 + a2 + a4) := by
  have hL2 := sq_nonneg L
  have hL4 : 0 ≤ L ^ 4 := by positivity
  have hS1 : 1 ≤ 1 + L ^ 2 + L ^ 4 + a2 + a4 := by linarith
  have hS2 : L ^ 2 ≤ 1 + L ^ 2 + L ^ 4 + a2 + a4 := by linarith
  have hS4 : L ^ 4 ≤ 1 + L ^ 2 + L ^ 4 + a2 + a4 := by linarith
  have hSa2 : a2 ≤ 1 + L ^ 2 + L ^ 4 + a2 + a4 := by linarith
  have hSa4 : a4 ≤ 1 + L ^ 2 + L ^ 4 + a2 + a4 := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hS1 h0, mul_le_mul_of_nonneg_left hS2 h2,
    mul_le_mul_of_nonneg_left hS4 h4, mul_le_mul_of_nonneg_left hSa2 hd2,
    mul_le_mul_of_nonneg_left hSa4 hd4]

/-- An explicit common quartic dominator for the four scaled errors
and functional variance. The hypotheses are exactly the preceding posterior
first/second-moment estimates after fresh or training integration. -/
theorem quartet_polynomial_domination {bG bT gG gT v L a2 a4 c E2 E4 d : ℝ}
    (ha2 : 0 ≤ a2) (ha4 : 0 ≤ a4) (h22 : a2 ^ 2 ≤ a4)
    (hc : 0 ≤ c) (hE2 : 0 ≤ E2) (hE4 : 0 ≤ E4) (hd : 0 ≤ d)
    (hgG0 : 0 ≤ gG) (hgG : gG ≤ c + 4 * L ^ 2)
    (hgT : |gT| ≤ 3 / 2 * gG + L ^ 2 / 2)
    (hbG : |bG - gG| ≤ (c / 2 + 4 * L ^ 2) * E2 + d * E4)
    (hbT : |bT - gT| ≤ (c / 2 + 4 * L ^ 2) * a2 + d * a4)
    (hv0 : 0 ≤ v) (hv : v ≤ gG * a2) :
    let C := 20 + 4 * c + c * E2 + 8 * E2 + 2 * d * (1 + E4)
    let S := 1 + L ^ 2 + L ^ 4 + a2 + a4
    |bG| ≤ C * S ∧ |bT| ≤ C * S ∧ |gG| ≤ C * S ∧
      |gT| ≤ C * S ∧ |v| ≤ C * S := by
  dsimp only
  let C := 20 + 4 * c + c * E2 + 8 * E2 + 2 * d * (1 + E4)
  let S := 1 + L ^ 2 + L ^ 4 + a2 + a4
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hdom := fun c0 c2 c4 d2 d4 h0 h2 h4 hd2 hd4 ↦
    polynomial_le_coefficient_mul_quartet (L := L) ha2 ha4 h0 h2 h4 hd2 hd4
      (c0 := c0) (c2 := c2) (c4 := c4) (d2 := d2) (d4 := d4)
  have hyoung : 4 * L ^ 2 * a2 ≤ 2 * L ^ 4 + 2 * a4 := by
    nlinarith [sq_nonneg (L ^ 2 - a2)]
  have hcE : 0 ≤ c * E2 := mul_nonneg hc hE2
  have hdE : 0 ≤ d * E4 := mul_nonneg hd hE4
  have hgTb : |gT| ≤ 3 / 2 * c + 13 / 2 * L ^ 2 := by nlinarith
  have hbGb : |bG| ≤ (c + c / 2 * E2 + d * E4) + (4 + 4 * E2) * L ^ 2 := by
    have htri : |bG| ≤ |bG - gG| + |gG| := by
      simpa only [sub_add_cancel] using abs_add_le (bG - gG) gG
    rw [abs_of_nonneg hgG0] at htri
    nlinarith
  have hbTb : |bT| ≤ 3 / 2 * c + 13 / 2 * L ^ 2 + 2 * L ^ 4 +
      c / 2 * a2 + (2 + d) * a4 := by
    have htri : |bT| ≤ |bT - gT| + |gT| := by
      simpa only [sub_add_cancel] using abs_add_le (bT - gT) gT
    nlinarith
  have hvb : |v| ≤ 2 * L ^ 4 + c * a2 + 2 * a4 := by
    rw [abs_of_nonneg hv0]
    have := mul_le_mul_of_nonneg_right hgG ha2
    nlinarith
  have hfinish : ∀ z c0 c2 c4 d2 d4, 0 ≤ c0 → 0 ≤ c2 → 0 ≤ c4 →
      0 ≤ d2 → 0 ≤ d4 → |z| ≤ c0 + c2 * L ^ 2 + c4 * L ^ 4 + d2 * a2 + d4 * a4 →
      c0 + c2 + c4 + d2 + d4 ≤ C → |z| ≤ C * S := by
    intro z c0 c2 c4 d2 d4 h0 h2 h4 hd2 hd4 hz hcoeff
    exact hz.trans ((hdom c0 c2 c4 d2 d4 h0 h2 h4 hd2 hd4).trans
      (mul_le_mul_of_nonneg_right hcoeff hS))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply hfinish bG (c + c / 2 * E2 + d * E4) (4 + 4 * E2) 0 0 0
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    · simpa using hbGb
    · dsimp [C]; nlinarith
  · apply hfinish bT (3 / 2 * c) (13 / 2) 2 (c / 2) (2 + d)
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity) hbTb
    dsimp [C]; nlinarith
  · apply hfinish gG c 4 0 0 0 hc (by positivity) (by positivity) (by positivity) (by positivity)
    · simpa only [zero_mul, add_zero, abs_of_nonneg hgG0] using hgG
    · dsimp [C]; nlinarith
  · apply hfinish gT (3 / 2 * c) (13 / 2) 0 0 0
      (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    · simpa using hgTb
    · dsimp [C]; nlinarith
  · apply hfinish v 0 0 2 c 2 (by positivity) (by positivity) (by positivity) hc (by positivity)
    · simpa using hvb
    · dsimp [C]; nlinarith

end SingularLearningTheory.BayesGibbs
