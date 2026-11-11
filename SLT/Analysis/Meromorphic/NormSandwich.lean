/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.Complex.Basic

/-!
# Pole orders from real-axis norm bounds

This specializes the real-axis sandwich argument of
`ResolutionCommon/Analysis/Meromorphic/RealAxisSandwich.lean`, using Mathlib's
pole and zero limits directly. It identifies the first zeta pole without
constructing its leading coefficient or auxiliary comparison functions.
-/

public section

open Filter Topology

namespace SingularLearningTheory.MellinAnalysis

private theorem ofReal_tendsto_nhdsGT_nhdsNE (a : ℝ) :
    Tendsto (fun x : ℝ ↦ (x : ℂ)) (𝓝[>] a) (𝓝[≠] (a : ℂ)) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · exact (Complex.continuous_ofReal.tendsto a).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    change (x : ℂ) ≠ (a : ℂ)
    exact_mod_cast (ne_of_gt hx)

/-- A meromorphic function bounded above and away from zero along a real ray
has order zero. The bounds themselves already exclude nonmeromorphic junk in
all nonzero-order cases; meromorphy is only needed by the caller's product rule. -/
private theorem meromorphicOrderAt_eq_zero_of_norm_sandwich
    {G : ℂ → ℂ} {a c C : ℝ} (hc : 0 < c)
    (hbound : ∀ᶠ x : ℝ in 𝓝[>] a, c ≤ ‖G (x : ℂ)‖ ∧ ‖G (x : ℂ)‖ ≤ C) :
    meromorphicOrderAt G (a : ℂ) = 0 := by
  rcases lt_trichotomy (meromorphicOrderAt G (a : ℂ)) 0 with hlt | heq | hgt
  · have hinf : Tendsto (fun x : ℝ ↦ ‖G (x : ℂ)‖) (𝓝[>] a) atTop :=
      tendsto_norm_cobounded_atTop.comp
        ((tendsto_cobounded_of_meromorphicOrderAt_neg hlt).comp
          (ofReal_tendsto_nhdsGT_nhdsNE a))
    obtain ⟨x, hx, hb⟩ := ((hinf.eventually_gt_atTop C).and hbound).exists
    exact False.elim (not_lt_of_ge hb.2 hx)
  · exact heq
  · have hzero : Tendsto (fun x : ℝ ↦ ‖G (x : ℂ)‖) (𝓝[>] a) (𝓝 0) := by
      simpa using ((tendsto_zero_of_meromorphicOrderAt_pos hgt).comp
        (ofReal_tendsto_nhdsGT_nhdsNE a)).norm
    obtain ⟨x, hx, hb⟩ := ((hzero.eventually (eventually_lt_nhds hc)).and hbound).exists
    exact False.elim (not_lt_of_ge hb.1 hx)

/-- Exact pole order from scaled norm bounds on the right real ray. -/
theorem _root_.meromorphicOrderAt_eq_neg_of_scaled_norm_sandwich
    {F : ℂ → ℂ} {a c C : ℝ} {m : ℕ}
    (hF : MeromorphicAt F (a : ℂ)) (hc : 0 < c)
    (hbound : ∀ᶠ x : ℝ in 𝓝[>] a,
      c ≤ ‖((x : ℂ) - (a : ℂ)) ^ m * F (x : ℂ)‖ ∧
      ‖((x : ℂ) - (a : ℂ)) ^ m * F (x : ℂ)‖ ≤ C) :
    meromorphicOrderAt F (a : ℂ) = -(m : ℤ) := by
  let P : ℂ → ℂ := (· - (a : ℂ)) ^ m
  have hP : AnalyticAt ℂ P (a : ℂ) :=
    (analyticAt_id.sub analyticAt_const).pow m
  have hzero : meromorphicOrderAt (P * F) (a : ℂ) = 0 :=
    meromorphicOrderAt_eq_zero_of_norm_sandwich hc hbound
  rw [meromorphicOrderAt_mul hP.meromorphicAt hF] at hzero
  change meromorphicOrderAt ((· - (a : ℂ)) ^ m) (a : ℂ) +
    meromorphicOrderAt F (a : ℂ) = 0 at hzero
  rw [meromorphicOrderAt_pow_id_sub_const] at hzero
  cases hord : meromorphicOrderAt F (a : ℂ) with
  | top => rw [hord] at hzero; simp at hzero
  | coe n =>
    rw [hord] at hzero
    have hsum : ((m : ℤ) : WithTop ℤ) + (n : WithTop ℤ) = ((0 : ℤ) : WithTop ℤ) :=
      hzero
    rw [← WithTop.coe_add, WithTop.coe_inj] at hsum
    congr 1
    linarith

/-- An analytic tail cannot change a genuine pole. -/
theorem _root_.meromorphicOrderAt_add_analytic_of_eq_neg
    {F T : ℂ → ℂ} {a : ℂ} {m : ℕ} (hm : 0 < m)
    (hT : AnalyticAt ℂ T a) (hF : meromorphicOrderAt F a = -(m : ℤ)) :
    meromorphicOrderAt (F + T) a = -(m : ℤ) := by
  have hlt : meromorphicOrderAt F a < meromorphicOrderAt T a := by
    have hn : meromorphicOrderAt F a < 0 := by
      rw [hF]
      exact_mod_cast (show -(m : ℤ) < 0 by omega)
    exact hn.trans_le hT.meromorphicOrderAt_nonneg
  rw [meromorphicOrderAt_add_eq_left_of_lt hT.meromorphicAt hlt, hF]

end SingularLearningTheory.MellinAnalysis
