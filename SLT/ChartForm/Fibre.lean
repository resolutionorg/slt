/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.Structural.Terminal
import Mathlib.Analysis.Normed.Module.Connected

/-!
# The fibre of a terminal chart over the base point

At a point `b` of a terminal chart `IsMonomialChart F φ dom e h W` with `F (φ b) = 0`, the identity
`F ∘ φ = u · y^e` with `u b ≠ 0` forces `y^e` to vanish at `b`, i.e. some coordinate `k` with
`b_k = 0` carries a positive exponent; so the exponent vector restricted to `J(b) = {k : b_k = 0}`
is nonzero, the `e_ne_zero` field of the recentred chart (`Chart.lean`). The fibre `dom ∩ φ⁻¹{w}`
over the base point is compact because `φ` is continuous on the compact box. If moreover
`F ∘ φ ≥ 0` near `b`, every exponent `e_k` with `b_k = 0` is even: the unit `u` has constant sign
on a small ball around `b` (intermediate value on a connected set), so `y^e` has constant sign at
the points of the ball with all coordinates nonzero, and the reflection `y_k ↦ -y_k`, which stays
in the ball because `b_k = 0`, flips the sign of `y^e` exactly when `e_k` is odd.

Not in the sources: the pointwise reading of the monomial form of [BM88, Theorem 4.4(4)] (compare
"if `a'_i(ỹ) = 0` … then `a'_i(0) = 0`" in the proof, p. 27) needed by the chart families of the
volume computations, where a nonnegative loss has even exponents.
-/

public section

open Set Analytic
open scoped Topology

namespace SingularLearningTheory

variable {n : ℕ}

section
open Analytic.IsMonomialChart

variable {F : (Fin n → ℝ) → ℝ} {φ : (Fin n → ℝ) → (Fin n → ℝ)} {dom W : Set (Fin n → ℝ)}
  {e h : Fin n →₀ ℕ}

/-- At a zero of `F ∘ φ` on a terminal chart some coordinate vanishing at the point carries a
positive exponent. -/
theorem _root_.Analytic.IsMonomialChart.exists_zero_coord_of_eq_zero
    (hc : IsMonomialChart F φ dom e h W) {b : Fin n → ℝ}
    (hb : b ∈ W) (h0 : F (φ b) = 0) : ∃ k, b k = 0 ∧ e k ≠ 0 := by
  obtain ⟨u, -, hu0, hue⟩ := hc.exists_unit
  have hm : monomialEval b e = 0 := by
    have h1 := hue b hb
    rw [h0] at h1
    exact (mul_eq_zero.mp h1.symm).resolve_left (hu0 b hb)
  rw [monomialEval_eq_prod, Finset.prod_eq_zero_iff] at hm
  obtain ⟨k, -, hk⟩ := hm
  exact ⟨k, (pow_eq_zero_iff'.mp hk).1, (pow_eq_zero_iff'.mp hk).2⟩

/-- The exponent vector restricted to `J(b) = {k : b_k = 0}` is nonzero at a zero of `F ∘ φ`. -/
theorem _root_.Analytic.IsMonomialChart.restricted_exponent_ne_zero
    (hc : IsMonomialChart F φ dom e h W) {b : Fin n → ℝ}
    (hb : b ∈ W) (h0 : F (φ b) = 0) :
    (fun k => if b k = 0 then e k else 0) ≠ (0 : Fin n → ℕ) := by
  obtain ⟨k, hbk, hek⟩ := hc.exists_zero_coord_of_eq_zero hb h0
  intro hzero
  have := congrFun hzero k
  simp only [hbk, ite_true, Pi.zero_apply] at this
  exact hek this

/-- The fibre of a terminal chart over `w` is compact. -/
theorem _root_.Analytic.IsMonomialChart.isCompact_fiber
    (hc : IsMonomialChart F φ dom e h W) (hdom : IsCompact dom)
    (w : Fin n → ℝ) : IsCompact (dom ∩ φ ⁻¹' {w}) :=
  hdom.of_isClosed_subset
    ((hc.analyticOnNhd.continuousOn.mono hc.subset).preimage_isClosed_of_isClosed
      hdom.isClosed isClosed_singleton)
    inter_subset_left

/-- A continuous nonvanishing function on a ball has constant sign (intermediate value on the
connected ball). -/
theorem _root_.Analytic.IsMonomialChart.unit_mul_unit_pos
    {u : (Fin n → ℝ) → ℝ} {b : Fin n → ℝ} {r : ℝ}
    (hu : ContinuousOn u (Metric.ball b r)) (hu0 : ∀ y ∈ Metric.ball b r, u y ≠ 0) :
    ∀ y ∈ Metric.ball b r, ∀ y' ∈ Metric.ball b r, 0 < u y * u y' := by
  intro y hy y' hy'
  have hconn : IsPreconnected (Metric.ball b r) := Metric.isPreconnected_ball
  rcases lt_or_gt_of_ne (hu0 y hy) with hneg | hpos
  · rcases lt_or_gt_of_ne (hu0 y' hy') with hneg' | hpos'
    · exact mul_pos_of_neg_of_neg hneg hneg'
    · exfalso
      obtain ⟨z, hz, hz0⟩ := hconn.intermediate_value hy hy' hu ⟨hneg.le, hpos'.le⟩
      exact hu0 z hz hz0
  · rcases lt_or_gt_of_ne (hu0 y' hy') with hneg' | hpos'
    · exfalso
      obtain ⟨z, hz, hz0⟩ := hconn.intermediate_value hy' hy hu ⟨hneg'.le, hpos.le⟩
      exact hu0 z hz hz0
    · exact mul_pos hpos hpos'

/-- Reflecting the coordinate `k` of `y` multiplies `y^e` by `(-1)^{e_k}`. -/
theorem _root_.Analytic.IsMonomialChart.monomialEval_update_neg
    (y : Fin n → ℝ) (k : Fin n) (e : Fin n →₀ ℕ) :
    monomialEval (Function.update y k (-y k)) e = (-1) ^ e k * monomialEval y e := by
  rw [monomialEval_eq_prod, monomialEval_eq_prod, ← Finset.mul_prod_erase Finset.univ _
    (Finset.mem_univ k), ← Finset.mul_prod_erase Finset.univ (fun j => y j ^ e j)
    (Finset.mem_univ k)]
  have hrest : ∏ j ∈ Finset.univ.erase k, Function.update y k (-y k) j ^ e j =
      ∏ j ∈ Finset.univ.erase k, y j ^ e j :=
    Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [hrest, Function.update_self, neg_pow]
  ring

/-- On a terminal chart, if `F ∘ φ ≥ 0` near `b` then every exponent of a coordinate vanishing at
`b` is even. -/
theorem _root_.Analytic.IsMonomialChart.exponents_even_of_nonneg
    (hc : IsMonomialChart F φ dom e h W) {b : Fin n → ℝ}
    (hb : b ∈ W) (hpos : ∀ᶠ y in 𝓝 b, 0 ≤ F (φ y)) : ∀ k, b k = 0 → Even (e k) := by
  intro k hbk
  by_contra hodd
  rw [Nat.not_even_iff_odd] at hodd
  obtain ⟨u, hu, hu0, hue⟩ := hc.exists_unit
  -- a ball around `b` inside `W` on which `F ∘ φ ≥ 0`
  obtain ⟨r, hr, hball⟩ :=
    Metric.eventually_nhds_iff.mp (hpos.and (hc.isOpen.mem_nhds hb))
  have hballW : ∀ y ∈ Metric.ball b r, y ∈ W := fun y hy => (hball (Metric.mem_ball.mp hy)).2
  have hsign := unit_mul_unit_pos (hu.mono hballW) fun y hy => hu0 y (hballW y hy)
  -- a small step `δ` avoiding the finitely many coordinate values `-b_j`
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ δ < r ∧ ∀ j, b j ≠ 0 → δ < |b j| := by
    refine (eventually_mem_nhdsWithin (s := Ioi (0 : ℝ))).and
      ((eventually_nhdsWithin_of_eventually_nhds (gt_mem_nhds hr)).and ?_)
    rw [Filter.eventually_all]
    intro j
    by_cases hj : b j = 0
    · exact Filter.Eventually.of_forall fun _ hj' => (hj' hj).elim
    · exact eventually_nhdsWithin_of_eventually_nhds
        ((gt_mem_nhds (abs_pos.mpr hj)).mono fun δ hδ _ => hδ)
  obtain ⟨δ, hδ0, hδr, hδb⟩ := hev.exists
  -- the point `y = b + δ` and its reflection in coordinate `k`
  set y : Fin n → ℝ := fun j => b j + δ with hy
  set y' : Fin n → ℝ := Function.update y k (-y k) with hy'
  have hyk : y k = δ := by rw [hy]; simp [hbk]
  have hymem : y ∈ Metric.ball b r := by
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro j
    rw [hy]
    simp [abs_of_pos hδ0, hδr]
  have hy'mem : y' ∈ Metric.ball b r := by
    rw [Metric.mem_ball, dist_pi_lt_iff hr]
    intro j
    by_cases hjk : j = k
    · subst hjk
      rw [hy', Function.update_self, hyk, hbk, Real.dist_eq, sub_zero, abs_neg, abs_of_pos hδ0]
      exact hδr
    · rw [hy', Function.update_of_ne hjk, hy]
      simp [abs_of_pos hδ0, hδr]
  have hyne : ∀ j, y j ≠ 0 := by
    intro j
    rw [hy]
    by_cases hj : b j = 0
    · simp [hj, hδ0.ne']
    · intro h0
      have h1 : |b j| = δ := by
        have : b j = -δ := by linarith
        rw [this, abs_neg, abs_of_pos hδ0]
      exact (hδb j hj).ne' h1
  have hm : monomialEval y e ≠ 0 := by
    rw [monomialEval_eq_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (hyne j)
  have hm' : monomialEval y' e = -monomialEval y e := by
    rw [hy', monomialEval_update_neg, hodd.neg_one_pow, neg_one_mul]
  have hA : 0 ≤ u y * monomialEval y e := by
    rw [← hue y (hballW y hymem)]
    exact (hball (Metric.mem_ball.mp hymem)).1
  have hB : 0 ≤ u y' * -monomialEval y e := by
    rw [← hm', ← hue y' (hballW y' hy'mem)]
    exact (hball (Metric.mem_ball.mp hy'mem)).1
  have hs := hsign y hymem y' hy'mem
  nlinarith [mul_nonneg hA hB, mul_pos hs (sq_pos_of_ne_zero hm)]

end

end SingularLearningTheory
