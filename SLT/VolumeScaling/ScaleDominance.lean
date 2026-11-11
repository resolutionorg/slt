/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Dominance calculus for the model scales

The positive comparison direction — a lexicographically dominated scale is big-O of the dominant
one — and its consequence: a finite sum of scales is Θ of the dominant scale. This is the
asymptotic engine of the chart sandwich: the cover bound `V ≤ Σ_α V_α` collapses to the dominant
chart's scale (`ChartFamilyExponents`).
-/

public section

open Asymptotics _root_.Filter Set
open scoped Topology

namespace SingularLearningTheory

/-- The positive comparison: a lex-dominated scale is big-O of the
dominant one (`q < p`, or equal `λ` with `r ≤ s`). -/
theorem isBigO_llcScale_of_lex {p q r s : ℝ}
    (h : q < p ∨ (q = p ∧ r ≤ s)) :
    (llcScale p r) =O[𝓝[>] (0 : ℝ)] (llcScale q s) := by
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), llcScale q s ε = 0 → llcScale p r ε = 0 :=
    llcScale_eventually_pos.mono fun ε hε h0 => absurd h0 hε.ne'
  have hsplit : (q < p ∨ (q = p ∧ r < s)) ∨ (q = p ∧ r = s) := by
    rcases h with hlt | ⟨hqp, hrs⟩
    · exact Or.inl (Or.inl hlt)
    · rcases eq_or_lt_of_le hrs with heq | hlt'
      · exact Or.inr ⟨hqp, heq⟩
      · exact Or.inl (Or.inr ⟨hqp, hlt'⟩)
  rcases hsplit with hstrict | ⟨rfl, rfl⟩
  · refine isBigO_of_div_tendsto_nhds hne 0 ?_
    have htop := tendsto_llcScale_div_atTop
      (p := q) (q := p) (r := s) (s := r) hstrict
    refine htop.inv_tendsto_atTop.congr' ?_
    refine Eventually.of_forall fun ε => ?_
    rw [Pi.inv_apply, inv_div]
    rfl
  · exact isBigO_refl _ _

/-- **Sum dominance**: a finite sum of LLC scales is Θ of the dominant
scale, provided the dominant pair is attained. -/
theorem isTheta_sum_llcScale {ι : Type*} {s : Finset ι}
    (lam theta : ι → ℝ) {l t : ℝ}
    (hdom : ∀ α ∈ s, l < lam α ∨ (l = lam α ∧ theta α ≤ t))
    (hmem : ∃ α ∈ s, lam α = l ∧ theta α = t) :
    (fun ε => ∑ α ∈ s, llcScale (lam α) (theta α) ε) =Θ[𝓝[>] (0 : ℝ)]
      llcScale l t := by
  constructor
  · exact (IsBigO.sum fun α hα => isBigO_llcScale_of_lex (hdom α hα)).congr_left
      fun ε => Finset.sum_apply ε s _
  · obtain ⟨α₀, hα₀, hl, ht⟩ := hmem
    refine IsBigO.of_bound 1 ?_
    filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
    rw [one_mul, Real.norm_of_nonneg (llcScale_pos hε).le, Real.norm_of_nonneg
      (Finset.sum_nonneg fun α _ => (llcScale_pos hε).le)]
    calc llcScale l t ε = llcScale (lam α₀) (theta α₀) ε := by rw [hl, ht]
      _ ≤ ∑ α ∈ s, llcScale (lam α) (theta α) ε :=
          Finset.single_le_sum (fun α _ => (llcScale_pos hε).le) hα₀

/-- **The read-off engine**: a finite family of functions, each
Θ of its scale, sums to Θ of a chosen dominant scale — `i0` minimizes
`λ` and, among ties, maximizes `θ`. -/
theorem isTheta_finset_sum_of_dominant {ι : Type*} [Fintype ι]
    {F : ι → ℝ → ℝ} {lam theta : ι → ℝ} (i0 : ι)
    (hT : ∀ i, (F i) =Θ[𝓝[>] (0 : ℝ)] llcScale (lam i) (theta i))
    (hnonneg : ∀ i, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ F i ε)
    (hlam : ∀ i, lam i0 ≤ lam i)
    (htheta : ∀ i, lam i = lam i0 → theta i ≤ theta i0) :
    (fun ε => ∑ i, F i ε) =Θ[𝓝[>] (0 : ℝ)]
      llcScale (lam i0) (theta i0) := by
  have hdom : ∀ i, (llcScale (lam i) (theta i)) =O[𝓝[>] (0 : ℝ)]
      llcScale (lam i0) (theta i0) := fun i => by
    rcases eq_or_lt_of_le (hlam i) with heq | hlt
    · exact isBigO_llcScale_of_lex (Or.inr ⟨heq, htheta i heq.symm⟩)
    · exact isBigO_llcScale_of_lex (Or.inl hlt)
  constructor
  · exact (IsBigO.sum fun i _ => (hT i).1.trans (hdom i)).congr_left
      fun ε => Finset.sum_apply ε Finset.univ _
  · refine (hT i0).2.trans (IsBigO.of_bound 1 ?_)
    have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i, 0 ≤ F i ε :=
      Filter.eventually_all.mpr hnonneg
    filter_upwards [hall] with ε hε
    rw [one_mul, Real.norm_of_nonneg (hε i0), Real.norm_of_nonneg
      (Finset.sum_nonneg fun i _ => hε i)]
    exact Finset.single_le_sum (fun i _ => hε i) (Finset.mem_univ i0)

/-- **The mixed read-off engine**: the family splits into a
support `s` whose members carry scales and off-support members that
are eventually zero; the full sum is Θ of the dominant scale chosen
inside the support. -/
theorem isTheta_finset_sum_of_dominant_mixed {ι : Type*} [Fintype ι]
    {F : ι → ℝ → ℝ} {s : Finset ι} {lam theta : ι → ℝ} (i0 : ι)
    (hi0 : i0 ∈ s)
    (hT : ∀ i ∈ s, (F i) =Θ[𝓝[>] (0 : ℝ)] llcScale (lam i) (theta i))
    (hzero : ∀ i ∉ s, ∀ᶠ ε in 𝓝[>] (0 : ℝ), F i ε = 0)
    (hnonneg : ∀ i ∈ s, ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ F i ε)
    (hlam : ∀ i ∈ s, lam i0 ≤ lam i)
    (htheta : ∀ i ∈ s, lam i = lam i0 → theta i ≤ theta i0) :
    (fun ε => ∑ i, F i ε) =Θ[𝓝[>] (0 : ℝ)]
      llcScale (lam i0) (theta i0) := by
  classical
  -- the full sum eventually collapses to the support sum
  have hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ Finset.univ \ s, F i ε = 0 :=
    (Filter.eventually_all_finset _).mpr fun i hi =>
      hzero i (Finset.mem_sdiff.mp hi).2
  have hcongr : (fun ε => ∑ i, F i ε) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun ε => ∑ i ∈ s, F i ε) := by
    filter_upwards [hz] with ε hε
    exact (Finset.sum_subset (Finset.subset_univ s) fun i hu hi =>
      hε i (Finset.mem_sdiff.mpr ⟨hu, hi⟩)).symm
  refine hcongr.trans_isTheta ?_
  have hdom : ∀ i ∈ s, (llcScale (lam i) (theta i)) =O[𝓝[>] (0 : ℝ)]
      llcScale (lam i0) (theta i0) := fun i hi => by
    rcases eq_or_lt_of_le (hlam i hi) with heq | hlt
    · exact isBigO_llcScale_of_lex (Or.inr ⟨heq, htheta i hi heq.symm⟩)
    · exact isBigO_llcScale_of_lex (Or.inl hlt)
  constructor
  · exact (IsBigO.sum fun i hi => (hT i hi).1.trans (hdom i hi)).congr_left
      fun ε => Finset.sum_apply ε s _
  · refine (hT i0 hi0).2.trans (IsBigO.of_bound 1 ?_)
    have hall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ i ∈ s, 0 ≤ F i ε :=
      (Filter.eventually_all_finset _).mpr hnonneg
    filter_upwards [hall] with ε hε
    rw [one_mul, Real.norm_of_nonneg (hε i0 hi0), Real.norm_of_nonneg
      (Finset.sum_nonneg fun i hi => hε i hi)]
    exact Finset.single_le_sum (fun i hi => hε i hi) hi0

end SingularLearningTheory
