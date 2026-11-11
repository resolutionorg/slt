/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.StochasticAsymptotics
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Ratios of finite vectors with moving positive denominators

Convergence in probability of ratios of finite vectors with moving positive denominators, from
the approximation of the raw numerators and their joint weak convergence. No uniform lower bound
on the evidence is assumed.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace MeasureTheory

open SingularLearningTheory

/-- Coordinatewise convergence to zero is joint convergence for a finite vector. -/
theorem tendstoInMeasure_finite_pi_zero {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {P : Measure Ω} {X : ℕ → Ω → ι → ℝ}
    (h : ∀ i, TendstoInMeasure P (fun n ω ↦ X n ω i) atTop 0) :
    TendstoInMeasure P X atTop 0 := by
  classical
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  have hi i := (tendstoInMeasure_iff_norm.mp (h i)) ε hε
  have hsum : Tendsto (fun n ↦ ∑ i, P {ω | ε ≤ ‖X n ω i‖}) atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, sub_zero, Finset.sum_const_zero] using
      tendsto_finset_sum Finset.univ (fun i _ ↦ hi i)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ bot_le) fun n ↦ ?_
  refine (measure_mono ?_).trans (measure_iUnion_fintype_le P _)
  intro ω hω
  simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero] at hω
  apply mem_iUnion.mpr
  by_contra hn
  push_neg at hn
  have hsmall : ‖X n ω‖ < ε := (pi_norm_lt_iff hε).mpr (by simpa only [Set.mem_setOf_eq, not_le] using hn)
  exact hsmall.not_ge hω

theorem tendstoInMeasure_const_mul_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : ℕ → Ω → ℝ} (c : ℝ)
    (h : TendstoInMeasure P X atTop 0) :
    TendstoInMeasure P (fun n ω ↦ c * X n ω) atTop 0 := by
  by_cases hc : c = 0
  · subst c
    simp only [zero_mul]
    exact tendstoInMeasure_zero_const
  rw [tendstoInMeasure_iff_norm] at h ⊢
  intro ε hε
  have hc0 : 0 < |c| := abs_pos.mpr hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (h (ε / |c|) (div_pos hε hc0)) (fun _ ↦ bot_le) fun n ↦ measure_mono ?_
  intro ω hω
  simp only [Set.mem_setOf_eq, Pi.zero_apply, sub_zero, Real.norm_eq_abs, abs_mul] at hω ⊢
  exact (div_le_iff₀ hc0).mpr (by simpa only [mul_comm] using hω)

theorem tendstoInMeasure_sub_zero {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X Y : ℕ → Ω → ℝ}
    (hX : TendstoInMeasure P X atTop 0) (hY : TendstoInMeasure P Y atTop 0) :
    TendstoInMeasure P (fun n ω ↦ X n ω - Y n ω) atTop 0 := by
  simpa only [neg_one_mul, sub_eq_add_neg] using
    tendstoInMeasure_add_zero hX (tendstoInMeasure_const_mul_zero (-1) hY)

section Graph
variable {Ω Ω' E F : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [NormedAddCommGroup F] [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {g : ℕ → Ω → E} {g' : Ω' → E}

/-- A continuous residual vanishing on the limiting graph is small in probability. -/
private theorem tendstoInMeasure_graph_zero {err : ℕ → Ω → F}
    (hg : TendstoInDistribution g atTop g' (fun _ ↦ P) P')
    (he : TendstoInMeasure P err atTop 0)
    (hem : ∀ n, AEMeasurable (err n) P)
    {r : E × F → ℝ} (hr : Continuous r) (hr0 : ∀ x, r (x, 0) = 0) :
    TendstoInMeasure P (fun n ω ↦ r (g n ω, err n ω)) atTop 0 := by
  have hpair := hg.prodMk_of_tendstoInMeasure_const g err g' (c := (0 : F)) he hem
  have h := hpair.continuous_comp hr
  have hc : TendstoInDistribution (fun n ω ↦ r (g n ω, err n ω)) atTop
      (fun _ : Ω' ↦ (0 : ℝ)) (fun _ ↦ P) P' := by
    simpa only [Function.comp_def, hr0] using h
  exact tendstoInMeasure_of_tendstoInDistribution_const hc

/-- Altering an error on an event whose probability vanishes preserves convergence. -/
private theorem tendstoInMeasure_zero_of_eq_outside {a b z : ℕ → Ω → ℝ} {c : ℝ}
    (hc : 0 < c) (hb : TendstoInMeasure P b atTop 0)
    (hz : TendstoInMeasure P z atTop 0)
    (heq : ∀ n ω, ‖z n ω‖ < c → a n ω = b n ω) :
    TendstoInMeasure P a atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hb hz ⊢
  intro ε hε
  have hlim : Tendsto (fun n ↦ P {ω | c ≤ ‖z n ω‖} +
      P {ω | ε ≤ ‖b n ω‖}) atTop (𝓝 0) := by
    simpa only [Pi.zero_apply, sub_zero, add_zero] using (hz c hc).add (hb ε hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) fun n ↦ ?_
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simp only [Set.mem_union, Set.mem_setOf_eq, Pi.zero_apply, sub_zero] at hω ⊢
  by_cases hzω : c ≤ ‖z n ω‖
  · exact Or.inl hzω
  · exact Or.inr (by simpa only [heq n ω (lt_of_not_ge hzω)] using hω)

/-- Ratios inherit a current-field approximation. The denominator may be zero on
exceptional sample events; only its limiting continuous functional is positive. -/
theorem tendstoInMeasure_ratio_pow_sub {ι : Type*} [Fintype ι]
    {v : ℕ → Ω → ι → ℝ} {L : E → ι → ℝ}
    (hg : TendstoInDistribution g atTop g' (fun _ ↦ P) P')
    (hv : ∀ n, AEMeasurable (v n) P) (hL : Continuous L)
    (herr : ∀ i, TendstoInMeasure P (fun n ω ↦ v n ω i - L (g n ω) i) atTop 0)
    (i j : ι) (k : ℕ) (hpos : ∀ x, 0 < L x j) :
    TendstoInMeasure P
      (fun n ω ↦ v n ω i / (v n ω j) ^ k - L (g n ω) i / (L (g n ω) j) ^ k) atTop 0 := by
  let err : ℕ → Ω → ι → ℝ := fun n ω ↦ v n ω - L (g n ω)
  have hem : ∀ n, AEMeasurable (err n) P :=
    fun n ↦ (hv n).sub (hL.measurable.comp_aemeasurable (hg.forall_aemeasurable n))
  have he : TendstoInMeasure P err atTop 0 := tendstoInMeasure_finite_pi_zero herr
  have hLj : Continuous (fun x ↦ L x j) := (continuous_apply j).comp hL
  have hLi : Continuous (fun x ↦ L x i) := (continuous_apply i).comp hL
  let rel : E × (ι → ℝ) → ℝ := fun z ↦ z.2 j / L z.1 j
  have hr : Continuous rel := ((continuous_apply j).comp continuous_snd).div
    (hLj.comp continuous_fst) (fun z ↦ (hpos z.1).ne')
  have hr0 : ∀ x, rel (x, 0) = 0 := by intro x; simp [rel]
  have hz := tendstoInMeasure_graph_zero hg he hem hr hr0
  let safe : E × (ι → ℝ) → ℝ := fun z ↦
    (L z.1 i + z.2 i) / (max (L z.1 j + z.2 j) (L z.1 j / 2)) ^ k -
      L z.1 i / (L z.1 j) ^ k
  have hd : ∀ z : E × (ι → ℝ),
      max (L z.1 j + z.2 j) (L z.1 j / 2) ≠ 0 := fun z ↦
    (lt_of_lt_of_le (half_pos (hpos z.1)) (le_max_right _ _)).ne'
  have hje : Continuous (fun z : E × (ι → ℝ) ↦ z.2 j) :=
    (continuous_apply j).comp continuous_snd
  have hie : Continuous (fun z : E × (ι → ℝ) ↦ z.2 i) :=
    (continuous_apply i).comp continuous_snd
  have hs : Continuous safe := by
    dsimp [safe]
    have hden := (((hLj.comp continuous_fst).add hje).max
      ((hLj.comp continuous_fst).div_const 2)).pow k
    have hnum := (hLi.comp continuous_fst).add hie
    exact (hnum.div hden (fun z ↦ pow_ne_zero k (hd z))).sub
      ((hLi.comp continuous_fst).div ((hLj.comp continuous_fst).pow k)
        (fun z ↦ pow_ne_zero k (hpos z.1).ne'))
  have hs0 : ∀ x, safe (x, 0) = 0 := by
    intro x
    simp only [safe, Pi.zero_apply, add_zero]
    rw [max_eq_left (by linarith [hpos x]), sub_self]
  have hb := tendstoInMeasure_graph_zero hg he hem hs hs0
  apply tendstoInMeasure_zero_of_eq_outside (c := 1 / 2) (by norm_num) hb hz
  intro n ω hω
  have hz' : |(v n ω j - L (g n ω) j) / L (g n ω) j| < 1 / 2 := by
    simpa only [rel, err, Pi.sub_apply, Real.norm_eq_abs] using hω
  have hlow : L (g n ω) j / 2 < v n ω j := by
    have hh := (abs_lt.mp hz').1
    have hd := (lt_div_iff₀ (hpos (g n ω))).mp hh
    linarith
  dsimp only [safe, err, Pi.sub_apply]
  rw [add_sub_cancel, add_sub_cancel, max_eq_left hlow.le]

end Graph
end MeasureTheory
