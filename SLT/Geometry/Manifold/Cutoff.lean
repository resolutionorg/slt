/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


/-!
# Smooth cut-offs and finite partitions of unity on `ℝ^d`

The partitions of unity of [Hit26,
Section 3.3.1] (definition
[Hit26, Definition 3.3.6]), built by hand on `ℝ^d` from
`IsOpen.exists_contDiff_support_eq`: a smooth cut-off equal to `1` on a compact set with support
inside a given open set, and a smooth partition of unity on a compact set subordinate to a finite
open cover, each function positive on the whole of its open set within the compact set (which is
what makes the chart weights positive at the chart centres).

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 3.3.6], finite, on a compact set | |
| | `exists_smooth_partition` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped ContDiff

variable {d : ℕ}

/-- A smooth cut-off: `f = 1` on the compact `K`, `tsupport f ⊆ U`, values in `[0, 1]`.
No thesis counterpart. -/
theorem _root_.exists_smooth_cutoff {K U : Set (Fin d → ℝ)} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ f : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ f ∧ (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
      (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ U ∧ HasCompactSupport f := by
  obtain ⟨A, hAo, hKA, hAU, hAc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  obtain ⟨a, ha_supp, ha_smooth, ha_range⟩ := hAo.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨b, hb_supp, hb_smooth, hb_range⟩ :=
    hK.isClosed.isOpen_compl.exists_contDiff_support_eq (n := ⊤)
  have ha0 : ∀ x, 0 ≤ a x := fun x ↦ (ha_range ⟨x, rfl⟩).1
  have hb0 : ∀ x, 0 ≤ b x := fun x ↦ (hb_range ⟨x, rfl⟩).1
  have hpos : ∀ x, 0 < a x + b x := by
    intro x
    by_cases hx : x ∈ K
    · have hax : a x ≠ 0 := by rw [← Function.mem_support, ha_supp]; exact hKA hx
      linarith [lt_of_le_of_ne (ha0 x) hax.symm, hb0 x]
    · have hbx : b x ≠ 0 := by rw [← Function.mem_support, hb_supp]; exact hx
      linarith [lt_of_le_of_ne (hb0 x) hbx.symm, ha0 x]
  have hsupp : Function.support (fun x ↦ a x / (a x + b x)) = A := by
    ext x
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, (hpos x).ne', or_false, ← ha_supp]
  refine ⟨fun x ↦ a x / (a x + b x),
    ha_smooth.div (ha_smooth.add hb_smooth) fun x ↦ (hpos x).ne',
    fun x ↦ div_nonneg (ha0 x) (hpos x).le,
    fun x ↦ div_le_one_of_le₀ (by linarith [hb0 x]) (hpos x).le, ?_, ?_, ?_⟩
  · intro x hx
    have hbx : b x = 0 := by
      have : x ∉ Function.support b := by rw [hb_supp]; exact fun h ↦ h hx
      exact Function.notMem_support.mp this
    have := hpos x
    rw [hbx, add_zero] at this
    change a x / (a x + b x) = 1
    rw [hbx, add_zero]
    exact div_self this.ne'
  · rw [tsupport, hsupp]; exact hAU
  · change IsCompact (tsupport _)
    rw [tsupport, hsupp]; exact hAc

/-- [Hit26, Definition 3.3.6], for a finite open cover
`B i` of a compact set `T` in `ℝ^d`: smooth `ρ i ≥ 0` with `ρ i ≠ 0` only on `B i`,
`∑ i, ρ i = 1` on `T`, `∑ i, ρ i ≤ 1` everywhere, and `ρ i > 0` on `T ∩ B i`. -/
theorem _root_.exists_smooth_partition {ι : Type*} [Fintype ι] {B : ι → Set (Fin d → ℝ)}
    (hB : ∀ i, IsOpen (B i)) {T : Set (Fin d → ℝ)} (hT : IsCompact T) (hTB : T ⊆ ⋃ i, B i) :
    ∃ ρ : ι → (Fin d → ℝ) → ℝ, (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i x, 0 ≤ ρ i x) ∧
      (∀ i x, ρ i x ≠ 0 → x ∈ B i) ∧ (∀ x ∈ T, ∑ i, ρ i x = 1) ∧ (∀ x, ∑ i, ρ i x ≤ 1) ∧
      ∀ i, ∀ x ∈ T ∩ B i, 0 < ρ i x := by
  choose f hf_supp hf_smooth hf_range using fun i ↦ (hB i).exists_contDiff_support_eq (n := ⊤)
  have hf0 : ∀ i x, 0 ≤ f i x := fun i x ↦ (hf_range i ⟨x, rfl⟩).1
  have hf_pos : ∀ i x, x ∈ B i → 0 < f i x := fun i x hx ↦
    lt_of_le_of_ne (hf0 i x) (by rw [← hf_supp i] at hx; exact hx.symm)
  have hf_zero : ∀ i x, x ∉ B i → f i x = 0 := fun i x hx ↦
    Function.notMem_support.mp (by rw [hf_supp i]; exact hx)
  have hS_smooth : ContDiff ℝ ∞ fun x ↦ ∑ i, f i x := ContDiff.sum fun i _ ↦ hf_smooth i
  have hS_pos : ∀ x, 0 < ∑ i, f i x ↔ x ∈ ⋃ i, B i := by
    intro x
    constructor
    · intro hx
      by_contra h
      exact hx.ne' (Finset.sum_eq_zero fun i _ ↦ hf_zero i x fun hi ↦ h (mem_iUnion.mpr ⟨i, hi⟩))
    · intro hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (hf_pos i x hi).trans_le
        (Finset.single_le_sum (f := fun j ↦ f j x) (fun j _ ↦ hf0 j x) (Finset.mem_univ i))
  obtain ⟨χ, hχ_smooth, hχ0, hχ1, hχT, hχ_supp, -⟩ :=
    exists_smooth_cutoff hT (isOpen_iUnion hB) hTB
  refine ⟨fun i x ↦ if 0 < ∑ j, f j x then χ x * f i x / ∑ j, f j x else 0,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : 0 < ∑ j, f j x
    · have hnhds : {y | 0 < ∑ j, f j y} ∈ 𝓝 x :=
        (isOpen_lt continuous_const hS_smooth.continuous).mem_nhds hx
      refine (((hχ_smooth.contDiffAt.mul (hf_smooth i).contDiffAt).div hS_smooth.contDiffAt
        hx.ne')).congr_of_eventuallyEq ?_
      exact eventually_of_mem hnhds fun y hy ↦ ite_eq_left hy
    · have hxU : x ∉ ⋃ i, B i := fun h ↦ hx ((hS_pos x).mpr h)
      have hnhds : (tsupport χ)ᶜ ∈ 𝓝 x :=
        (isClosed_tsupport χ).isOpen_compl.mem_nhds fun h ↦ hxU (hχ_supp h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      refine eventually_of_mem hnhds fun y hy ↦ ?_
      simp [image_eq_zero_of_notMem_tsupport hy]
  · intro i x
    dsimp only
    split_ifs with h
    · exact div_nonneg (mul_nonneg (hχ0 x) (hf0 i x)) h.le
    · exact le_rfl
  · intro i x hx
    dsimp only at hx
    split_ifs at hx with h
    · by_contra hxB
      exact hx (by rw [hf_zero i x hxB]; simp)
    · exact absurd rfl hx
  · intro x hx
    have hSx := (hS_pos x).mpr (hTB hx)
    simp only [ite_eq_left hSx, hχT x hx, one_mul]
    rw [← Finset.sum_div]
    exact div_self hSx.ne'
  · intro x
    dsimp only
    by_cases hx : 0 < ∑ j, f j x
    · simp only [ite_eq_left hx]
      calc ∑ i, χ x * f i x / ∑ j, f j x = χ x * ((∑ i, f i x) / ∑ j, f j x) := by
            rw [Finset.sum_div, Finset.mul_sum]
            simp_rw [mul_div_assoc]
        _ = χ x := by rw [div_self hx.ne', mul_one]
        _ ≤ 1 := hχ1 x
    · simp only [ite_eq_right hx, Finset.sum_const_zero]
      exact zero_le_one
  · rintro i x ⟨hxT, hxB⟩
    have hSx := (hS_pos x).mpr (hTB hxT)
    dsimp only
    rw [ite_eq_left hSx, hχT x hxT, one_mul]
    exact div_pos (hf_pos i x hxB) hSx

end SingularLearningTheory
