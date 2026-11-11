/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.Structural.Terminal

/-!
# Terminal charts recentred at a point of the box

A terminal chart `φ` on `W` with `F ∘ φ = u · y^e`, `det Dφ = v · y^h`, recentred at a point
`b ∈ W` (`z ↦ φ (b + z)`), is again terminal, with the exponents restricted to
`J(b) = {k : b_k = 0}`: the factors `(b_k + z_k)^{e_k}` with `b_k ≠ 0` do not vanish near `z = 0`
and are absorbed into the unit (`monomialEval_add_eq`), the new open set is
`W' = {z | b + z ∈ W, b_k + z_k ≠ 0 for b_k ≠ 0}`, and injectivity off `{z^{h|J(b)} = 0}` follows
from injectivity off `{y^h = 0}` because on `W'` the two monomials vanish together. The derivative
of `z ↦ φ (b + z)` is `Dφ (b + z)` (`fderiv_comp_add_left`). This is the observation that a
function which is a unit times a monomial in coordinates centred at one point is so at every
nearby point, used when Bierstone and Milman move to the points of a chart where some of the
factors `a'_i` vanish [BM88, proof of Theorem 4.4, p. 27]; here it lets the chart-form theorems
read off exponents at every point of a box.
-/

public section

open Set Analytic
open scoped Topology

namespace Analytic

variable {n : ℕ}

/-- A monomial at `b + z` is the monomial in the coordinates vanishing at `b`, times the factors
with `b_k ≠ 0`. -/
theorem monomialEval_add_eq (b z : Fin n → ℝ) (h : Fin n →₀ ℕ) :
    monomialEval (b + z) h =
      (∏ k ∈ Finset.univ.filter (fun k => ¬ b k = 0), (b k + z k) ^ h k) *
        monomialEval z (h.filter fun k => b k = 0) := by
  rw [monomialEval_eq_prod, monomialEval_eq_prod,
    ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun k => b k = 0)
      (fun k => (b + z) k ^ h k), mul_comm]
  congr 1
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [Finsupp.filter_apply]
  split_ifs with hk
  · rw [Pi.add_apply, hk, zero_add]
  · rw [pow_zero]

/-- An open `W ∋ b` has an open `W' ∋ 0` with `b + W' ⊆ W` on which, for every exponent `e`, the
monomial `(b + w)^e` is an analytic nonvanishing factor times the monomial `w^{e|_{b_k = 0}}`
(the monomial part of `IsMonomialChart.translate`). -/
theorem exists_translate_unit_mul_monomial {W : Set (Fin n → ℝ)} (hW : IsOpen W)
    {b : Fin n → ℝ} (hb : b ∈ W) :
    ∃ W' : Set (Fin n → ℝ), IsOpen W' ∧ (0 : Fin n → ℝ) ∈ W' ∧ (∀ w ∈ W', b + w ∈ W) ∧
      ∀ e : Fin n →₀ ℕ, ∃ P : (Fin n → ℝ) → ℝ, AnalyticOnNhd ℝ P W' ∧ (∀ w ∈ W', P w ≠ 0) ∧
        ∀ w ∈ W', monomialEval (b + w) e = P w * monomialEval w (e.filter fun k => b k = 0) := by
  classical
  set N : Finset (Fin n) := Finset.univ.filter fun k => ¬ b k = 0 with hN
  set W' : Set (Fin n → ℝ) := {w | b + w ∈ W} ∩ ⋂ k ∈ N, {w | b k + w k ≠ 0} with hW'
  have hW'open : IsOpen W' := by
    refine (hW.preimage (continuous_const.add continuous_id)).inter ?_
    exact isOpen_biInter_finset fun k _ =>
      isOpen_ne.preimage (continuous_const.add (continuous_apply k))
  have hmemW : ∀ w ∈ W', b + w ∈ W := fun _ hw => hw.1
  have hne : ∀ w ∈ W', ∀ k ∈ N, b k + w k ≠ 0 := fun _ hw k hk => mem_iInter₂.mp hw.2 k hk
  have h0 : (0 : Fin n → ℝ) ∈ W' := by
    refine ⟨by simpa using hb, mem_iInter₂.mpr fun k hk => ?_⟩
    change b k + (0 : Fin n → ℝ) k ≠ 0
    rw [Pi.zero_apply, add_zero]
    exact (Finset.mem_filter.mp hk).2
  refine ⟨W', hW'open, h0, hmemW, fun e => ⟨fun w => ∏ k ∈ N, (b k + w k) ^ e k, ?_, ?_, ?_⟩⟩
  · intro w _
    exact Finset.analyticAt_fun_prod _ fun k _ =>
      (analyticAt_const.add (analyticAt_pi_iff.mp analyticAt_id k)).fun_pow _
  · intro w hw
    exact Finset.prod_ne_zero_iff.mpr fun k hk => pow_ne_zero _ (hne w hw k hk)
  · intro w _
    exact monomialEval_add_eq b w e

/-- A terminal chart recentred at a point `b` of its open set is terminal near `0`, with the
exponents restricted to the coordinates vanishing at `b` [BM88, proof of Theorem 4.4, p. 27]. -/
protected theorem IsMonomialChart.translate {F : (Fin n → ℝ) → ℝ} {φ : (Fin n → ℝ) → (Fin n → ℝ)}
    {dom W : Set (Fin n → ℝ)} {e h : Fin n →₀ ℕ} (hc : IsMonomialChart F φ dom e h W)
    {b : Fin n → ℝ} (hb : b ∈ W) :
    ∃ W' : Set (Fin n → ℝ), IsOpen W' ∧ (0 : Fin n → ℝ) ∈ W' ∧
      ∀ dom' ⊆ W', IsMonomialChart F (fun z => φ (b + z)) dom' (e.filter fun k => b k = 0)
        (h.filter fun k => b k = 0) W' := by
  classical
  obtain ⟨u, hu, hu0, hue⟩ := hc.exists_unit
  obtain ⟨v, hv, hv0, hvh⟩ := hc.exists_jacUnit
  obtain ⟨W', hW'open, h0, hmemW, hP⟩ := exists_translate_unit_mul_monomial hc.isOpen hb
  obtain ⟨Pe, hPe, hPe0, hPee⟩ := hP e
  obtain ⟨Ph, hPh, hPh0, hPhe⟩ := hP h
  have hshift : ContinuousOn (fun z : Fin n → ℝ => b + z) W' :=
    (continuous_const.add continuous_id).continuousOn
  refine ⟨W', hW'open, h0, fun dom' hd => ?_⟩
  refine ⟨hW'open, hd, ?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (hc.analyticOnNhd (b + z) (hmemW z hz)).comp (f := fun z => b + z)
      (analyticAt_const.add analyticAt_id)
  · intro z hz z' hz' hzz'
    have h1 : b + z ∈ {y | y ∈ W ∧ monomialEval y h ≠ 0} := by
      refine ⟨hmemW z hz.1, ?_⟩
      rw [hPhe z hz.1]
      exact mul_ne_zero (hPh0 z hz.1) hz.2
    have h2 : b + z' ∈ {y | y ∈ W ∧ monomialEval y h ≠ 0} := by
      refine ⟨hmemW z' hz'.1, ?_⟩
      rw [hPhe z' hz'.1]
      exact mul_ne_zero (hPh0 z' hz'.1) hz'.2
    exact add_left_cancel (hc.injOn h1 h2 hzz')
  · refine ⟨fun z => u (b + z) * Pe z, ?_, ?_, ?_⟩
    · exact (hu.comp hshift fun z hz => hmemW z hz).mul hPe.continuousOn
    · intro z hz
      exact mul_ne_zero (hu0 _ (hmemW z hz)) (hPe0 z hz)
    · intro z hz
      rw [hue (b + z) (hmemW z hz), hPee z hz]
      ring
  · refine ⟨fun z => v (b + z) * Ph z, ?_, ?_, ?_⟩
    · exact (hv.comp hshift fun z hz => hmemW z hz).mul hPh.continuousOn
    · intro z hz
      exact mul_ne_zero (hv0 _ (hmemW z hz)) (hPh0 z hz)
    · intro z hz
      rw [fderiv_comp_add_left, hvh (b + z) (hmemW z hz), hPhe z hz]
      ring

end Analytic
