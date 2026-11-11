/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import SLT.VolumeScaling.Comparison
public import SLT.VolumeScaling.Defs
import Mathlib.RingTheory.PiTensorProduct
import Std.Tactic.BVDecide.Normalize.Prop
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
# The local-ideal layer (K1.2 + K2)

"Local ideals" without germ rings: containment of finite function
families is *bounded-coefficient representability on `K`*
(`SingularLearningTheory.IdealLEOn`), and the λ of a family is the λ of its sum-of-squares
aggregate. The Cauchy–Schwarz bridge turns containment into aggregate
domination, K1.1 turns domination into the lexicographic exponent
comparison (Aoyagi's Lemma 1 direction: `⟨G⟩ ⊆ ⟨F⟩ ⇒ λ(G) ≤ λ(F)`,
with `θ(F) ≤ θ(G)` at ties), and mutual containment makes the
exponent predicate itself invariant (K2, an iff). For
continuous coefficients, compactness supplies the bounds.
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

open SingularLearningTheory

variable {X : Type*} {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The sum-of-squares aggregate of a finite family. -/
@[expose] def sosAggregate (F : ι → X → ℝ) (x : X) : ℝ :=
  ∑ j, (F j x) ^ 2

private theorem sosAggregate_nonneg (F : ι → X → ℝ) (x : X) :
    0 ≤ sosAggregate F x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- `⟨G⟩ ⊆ ⟨F⟩` on `K`: every member of `G` is a bounded-coefficient
combination of `F` on `K`. -/
@[expose] def IdealLEOn (K : Set X) (G : ι → X → ℝ) (F : κ → X → ℝ) : Prop :=
  ∃ a : ι → κ → X → ℝ,
    (∀ i j, ∃ C, ∀ x ∈ K, |a i j x| ≤ C) ∧
    (∀ i, ∀ x ∈ K, G i x = ∑ j, a i j x * F j x)

/-- Equal local ideals on `K`: mutual containment. -/
@[expose] def IdealEqOn (K : Set X) (G : ι → X → ℝ) (F : κ → X → ℝ) : Prop :=
  IdealLEOn K G F ∧ IdealLEOn K F G

/-- The exponent predicate of a family: that of its aggregate. -/
abbrev HasLLCExponentsFamilyOn [MeasurableSpace X] (μ : Measure X)
    (K : Set X) (F : ι → X → ℝ) (lam theta : ℝ) : Prop :=
  HasLLCExponentsOn μ K (sosAggregate F) lam theta

section Bridge

variable {K : Set X} {G : ι → X → ℝ} {F : κ → X → ℝ}

/-- The Cauchy–Schwarz core with explicit per-pair bounds. -/
private theorem sosAggregate_le_mul_of_coeffBounds
    {a : ι → κ → X → ℝ} {M : ι → κ → ℝ}
    (ha : ∀ i j, ∀ x ∈ K, |a i j x| ≤ M i j)
    (hrep : ∀ i, ∀ x ∈ K, G i x = ∑ j, a i j x * F j x) :
    ∀ x ∈ K, sosAggregate G x
      ≤ (∑ i, ∑ j, (M i j) ^ 2) * sosAggregate F x := by
  intro x hx
  have hterm : ∀ i, (G i x) ^ 2
      ≤ (∑ j, (M i j) ^ 2) * sosAggregate F x := by
    intro i
    rw [hrep i x hx]
    calc (∑ j, a i j x * F j x) ^ 2
        ≤ (∑ j, (a i j x) ^ 2) * ∑ j, (F j x) ^ 2 :=
          Finset.sum_mul_sq_le_sq_mul_sq Finset.univ _ _
      _ ≤ (∑ j, (M i j) ^ 2) * sosAggregate F x := by
          refine mul_le_mul_of_nonneg_right
            (Finset.sum_le_sum fun j _ => ?_)
            (Finset.sum_nonneg fun _ _ => sq_nonneg _)
          rw [← sq_abs (a i j x)]
          exact pow_le_pow_left₀ (abs_nonneg _) (ha i j x hx) 2
  calc sosAggregate G x = ∑ i, (G i x) ^ 2 := rfl
    _ ≤ ∑ i, (∑ j, (M i j) ^ 2) * sosAggregate F x :=
        Finset.sum_le_sum fun i _ => hterm i
    _ = (∑ i, ∑ j, (M i j) ^ 2) * sosAggregate F x := by
        rw [Finset.sum_mul]

/-- **The ideal-membership bridge (K1.2)**: containment gives aggregate
domination with a positive constant. -/
private theorem sosAggregate_le_mul_of_idealLEOn (hGF : IdealLEOn K G F) :
    ∃ C : ℝ, 0 < C ∧
      ∀ x ∈ K, sosAggregate G x ≤ C * sosAggregate F x := by
  classical
  obtain ⟨a, hbdd, hrep⟩ := hGF
  choose M hM using hbdd
  set M' : ι → κ → ℝ := fun i j => max (M i j) 0 with hM'
  have ha' : ∀ i j, ∀ x ∈ K, |a i j x| ≤ M' i j := fun i j x hx =>
    le_max_of_le_left (hM i j x hx)
  refine ⟨(∑ i, ∑ j, (M' i j) ^ 2) + 1, ?_, fun x hx => ?_⟩
  · have h1 : (0 : ℝ) ≤ ∑ i, ∑ j, (M' i j) ^ 2 :=
      Finset.sum_nonneg fun i _ =>
        Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  · calc sosAggregate G x
        ≤ (∑ i, ∑ j, (M' i j) ^ 2) * sosAggregate F x :=
          sosAggregate_le_mul_of_coeffBounds ha' hrep x hx
      _ ≤ ((∑ i, ∑ j, (M' i j) ^ 2) + 1) * sosAggregate F x :=
          mul_le_mul_of_nonneg_right (by linarith)
            (sosAggregate_nonneg F x)

omit [Fintype ι] in
/-- Compactness supplies the bounds: continuous coefficients on a
compact `K` witness containment. -/
theorem IdealLEOn.of_continuousCoeffs [TopologicalSpace X]
    (hK : IsCompact K) {a : ι → κ → X → ℝ}
    (hcont : ∀ i j, ContinuousOn (a i j) K)
    (hrep : ∀ i, ∀ x ∈ K, G i x = ∑ j, a i j x * F j x) :
    IdealLEOn K G F := by
  refine ⟨a, fun i j => ?_, hrep⟩
  rcases K.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, fun x hx => absurd hx (Set.notMem_empty x)⟩
  obtain ⟨x₀, _, hmax⟩ := hK.exists_isMaxOn hne ((hcont i j).abs)
  exact ⟨|a i j x₀|, fun x hx => hmax hx⟩

end Bridge

section Exponents

variable [MeasurableSpace X] {μ : Measure X} {K : Set X}
  {G : ι → X → ℝ} {F : κ → X → ℝ}

/-- **K1 (Aoyagi Lemma 1 direction)**: `⟨G⟩ ⊆ ⟨F⟩` on `K` forces
`λ(G) < λ(F)`, or `λ(G) = λ(F)` with `θ(F) ≤ θ(G)`. -/
private theorem lex_le_of_idealLEOn {lF tF lG tG : ℝ}
    (hGF : IdealLEOn K G F)
    (hG : HasLLCExponentsFamilyOn μ K G lG tG)
    (hF : HasLLCExponentsFamilyOn μ K F lF tF) :
    lG < lF ∨ (lG = lF ∧ tF ≤ tG) := by
  obtain ⟨C, hC, hdom⟩ := sosAggregate_le_mul_of_idealLEOn hGF
  exact hF.lex_le_of_dominated hG hC hdom

/-- **K2 (the local-ideal invariance, iff form)**: the exponent
predicate of a family depends only on its local ideal on `K`. -/
theorem IdealEqOn.hasLLCExponentsFamilyOn_iff {lam theta : ℝ}
    (hEq : IdealEqOn K G F) :
    HasLLCExponentsFamilyOn μ K G lam theta ↔
      HasLLCExponentsFamilyOn μ K F lam theta := by
  obtain ⟨C₁, hC₁, hdom₁⟩ := sosAggregate_le_mul_of_idealLEOn hEq.1
  obtain ⟨C₂, hC₂, hdom₂⟩ := sosAggregate_le_mul_of_idealLEOn hEq.2
  constructor
  · intro hG
    exact hG.of_mutually_dominated hC₁ hC₂ hdom₁ hdom₂
  · intro hF
    exact hF.of_mutually_dominated hC₂ hC₁ hdom₂ hdom₁

/-- K2, pair-equality corollary. -/
theorem IdealEqOn.exponents_eq {lF tF lG tG : ℝ}
    (hEq : IdealEqOn K G F)
    (hG : HasLLCExponentsFamilyOn μ K G lG tG)
    (hF : HasLLCExponentsFamilyOn μ K F lF tF) :
    lG = lF ∧ tG = tF := by
  have h1 := lex_le_of_idealLEOn hEq.1 hG hF
  have h2 := lex_le_of_idealLEOn hEq.2 hF hG
  rcases h1 with h1 | ⟨h1e, h1t⟩
  · rcases h2 with h2 | ⟨h2e, _⟩
    · exact absurd (lt_trans h1 h2) (lt_irrefl _)
    · exact absurd h1 (by rw [h2e]; exact lt_irrefl _)
  · rcases h2 with h2 | ⟨h2e, h2t⟩
    · exact absurd h2 (by rw [h1e]; exact lt_irrefl _)
    · exact ⟨h1e, le_antisymm h2t h1t⟩

end Exponents

section Calculus

variable {K : Set X} {G : ι → X → ℝ} {F : κ → X → ℝ}

omit [Fintype ι] in
/-- Bounded-coefficient containment composes: the coefficient matrix of
the composite is the (pointwise) matrix product, with summed bounds. -/
private theorem IdealLEOn.trans {ν : Type*} [Fintype ν] {E : ν → X → ℝ}
    (hGF : IdealLEOn K G F) (hFE : IdealLEOn K F E) : IdealLEOn K G E := by
  obtain ⟨a, ha, hrepa⟩ := hGF
  obtain ⟨b, hb, hrepb⟩ := hFE
  choose Ca hCa using ha
  choose Cb hCb using hb
  refine ⟨fun i k x => ∑ j, a i j x * b j k x, fun i k => ?_, fun i x hx => ?_⟩
  · refine ⟨∑ j, |Ca i j| * |Cb j k|, fun x hx => ?_⟩
    calc |∑ j, a i j x * b j k x| ≤ ∑ j, |a i j x * b j k x| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |a i j x| * |b j k x| := by
          simp only [abs_mul]
      _ ≤ ∑ j, |Ca i j| * |Cb j k| :=
          Finset.sum_le_sum fun j _ => mul_le_mul
            ((hCa i j x hx).trans (le_abs_self _))
            ((hCb j k x hx).trans (le_abs_self _))
            (abs_nonneg _) (abs_nonneg _)
  · calc G i x = ∑ j, a i j x * F j x := hrepa i x hx
      _ = ∑ j, a i j x * ∑ k, b j k x * E k x := by
          exact Finset.sum_congr rfl fun j _ => by rw [hrepb j x hx]
      _ = ∑ j, ∑ k, a i j x * b j k x * E k x := by
          simp only [Finset.mul_sum, mul_assoc]
      _ = ∑ k, ∑ j, a i j x * b j k x * E k x := Finset.sum_comm
      _ = ∑ k, (∑ j, a i j x * b j k x) * E k x := by
          exact Finset.sum_congr rfl fun k _ => (Finset.sum_mul ..).symm

/-- Bounded-coefficient equality is transitive. -/
protected theorem IdealEqOn.trans {ν : Type*} [Fintype ν] {E : ν → X → ℝ}
    (hGF : IdealEqOn K G F) (hFE : IdealEqOn K F E) : IdealEqOn K G E :=
  ⟨hGF.1.trans hFE.1, hFE.2.trans hGF.2⟩

omit [Fintype ι] in
/-- Containment pulls back along any map of the underlying sets: the
coefficients compose with the map, keeping their bounds. -/
private theorem IdealLEOn.precomp {Y : Type*} {K' : Set Y} (h : IdealLEOn K G F)
    (ψ : Y → X) (hψ : ∀ y ∈ K', ψ y ∈ K) :
    IdealLEOn K' (fun i y => G i (ψ y)) (fun j y => F j (ψ y)) := by
  obtain ⟨a, ha, hrep⟩ := h
  exact ⟨fun i j y => a i j (ψ y),
    fun i j => (ha i j).imp fun C hC y hy => hC _ (hψ y hy),
    fun i y hy => hrep i _ (hψ y hy)⟩

/-- Equality pulls back along any map of the underlying sets. -/
theorem IdealEqOn.precomp {Y : Type*} {K' : Set Y} (h : IdealEqOn K G F)
    (ψ : Y → X) (hψ : ∀ y ∈ K', ψ y ∈ K) :
    IdealEqOn K' (fun i y => G i (ψ y)) (fun j y => F j (ψ y)) :=
  ⟨h.1.precomp ψ hψ, h.2.precomp ψ hψ⟩

/-- Containment is reflexive (identity coefficients). -/
private theorem IdealLEOn.refl (K : Set X) (F : ι → X → ℝ) [DecidableEq ι] :
    IdealLEOn K F F :=
  ⟨fun i j _ => if i = j then 1 else 0,
    fun i j => ⟨1, fun _ _ => by by_cases h : i = j <;> simp [h]⟩,
    fun i x _ => by
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [Ne.symm hj])
        (fun hj => absurd (Finset.mem_univ _) hj)]
      simp⟩

/-- Equality of ideals is reflexive. -/
protected theorem IdealEqOn.refl (K : Set X) (F : ι → X → ℝ) [DecidableEq ι] :
    IdealEqOn K F F :=
  ⟨IdealLEOn.refl K F, IdealLEOn.refl K F⟩

/-- Families equal up to a reindexing of the index type have equal
ideals: the coefficient matrices are the 0/1 permutation pattern. -/
theorem IdealEqOn.of_reindex {K : Set X} {G : ι → X → ℝ} {F : κ → X → ℝ}
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ)
    (h : ∀ i, ∀ x ∈ K, G i x = F (e i) x) : IdealEqOn K G F := by
  constructor
  · refine ⟨fun i j x => if e i = j then 1 else 0, fun i j => ⟨1, fun x _ => ?_⟩,
      fun i x hx => ?_⟩
    · by_cases hij : e i = j <;> simp [hij]
    · rw [Finset.sum_eq_single (e i) (fun j _ hj => by simp [Ne.symm hj])
        (fun hj => absurd (Finset.mem_univ _) hj)]
      simp [h i x hx]
  · refine ⟨fun j i x => if e i = j then 1 else 0, fun j i => ⟨1, fun x _ => ?_⟩,
      fun j x hx => ?_⟩
    · by_cases hij : e i = j <;> simp [hij]
    · rw [Finset.sum_eq_single (e.symm j) (fun i _ hi => by
        simp [show ¬ e i = j from fun he => hi (by rw [← he, Equiv.symm_apply_apply])])
        (fun hj => absurd (Finset.mem_univ _) hj)]
      simp [h (e.symm j) x hx]

/-- The elementary operation along a pivot assignment: adding to each
generator a bounded multiple of its designated pivot (pivots
themselves untouched) preserves the ideal — the blow-up recursions'
row-clearing exchanges, with the pivot allowed to vary (e.g. per
output column). -/
private theorem IdealEqOn.elementaryAt {K : Set X} (F : ι → X → ℝ)
    (piv : ι → ι) (c : ι → X → ℝ)
    (hc : ∀ i, ∃ C, ∀ x ∈ K, |c i x| ≤ C)
    (hpiv : ∀ i x, c (piv i) x = 0) :
    IdealEqOn K (fun i x => F i x + c i x * F (piv i) x) F := by
  classical
  have hbound : ∀ s : ℝ, ∀ i j, ∃ C, ∀ x ∈ K,
      |(if j = i then 1 else 0) +
        s * (if j = piv i then c i x else 0)| ≤ C := by
    intro s i j
    obtain ⟨C, hC⟩ := hc i
    refine ⟨1 + |s| * C, fun x hx => ?_⟩
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · by_cases h : j = i <;> simp [h]
    · rw [abs_mul]
      by_cases h : j = piv i
      · simp only [h, ite_eq_left]
        exact mul_le_mul_of_nonneg_left (hC x hx) (abs_nonneg s)
      · simp only [h, ite_eq_right, not_false_iff, abs_zero, mul_zero]
        exact mul_nonneg (abs_nonneg s) ((abs_nonneg _).trans (hC x hx))
  have hsum : ∀ (s : ℝ) (G : ι → X → ℝ) (i : ι) (x : X),
      ∑ j, ((if j = i then 1 else 0) +
          s * (if j = piv i then c i x else 0)) * G j x =
        G i x + s * (c i x * G (piv i) x) := by
    intro s G i x
    simp only [add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      mul_assoc, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' Finset.univ i (fun j => G j x),
      Finset.sum_ite_eq' Finset.univ (piv i) fun j => s * (c i x * G j x)]
    simp
  constructor
  · refine ⟨fun i j x => (if j = i then 1 else 0) +
      (1 : ℝ) * (if j = piv i then c i x else 0),
      hbound 1, fun i x hx => ?_⟩
    rw [hsum 1 F i x]
    ring
  · refine ⟨fun i j x => (if j = i then 1 else 0) +
      (-1 : ℝ) * (if j = piv i then c i x else 0),
      hbound (-1), fun i x hx => ?_⟩
    rw [hsum (-1) (fun i x => F i x + c i x * F (piv i) x) i x]
    simp only [hpiv, zero_mul, add_zero]
    ring

/-- A family that factors through another along a sectioned map
generates the same ideal: each `G i` is a bounded multiple of
`F (e i)`, and along the section the multiple is `1` — the absorption
of redundant generators at a blow-up's exhausted block. -/
theorem IdealEqOn.of_section {K : Set X} {G : ι → X → ℝ} {F : κ → X → ℝ}
    (e : ι → κ) (sec : κ → ι) (hsec : ∀ k, e (sec k) = k)
    (c : ι → X → ℝ) (hc : ∀ i, ∃ C, ∀ x ∈ K, |c i x| ≤ C)
    (hone : ∀ k x, c (sec k) x = 1)
    (h : ∀ i, ∀ x ∈ K, G i x = c i x * F (e i) x) :
    IdealEqOn K G F := by
  classical
  constructor
  · refine ⟨fun i j x => if j = e i then c i x else 0, ?_, ?_⟩
    · intro i j
      obtain ⟨C, hC⟩ := hc i
      refine ⟨C, fun x hx => ?_⟩
      by_cases hj : j = e i
      · simpa [hj] using hC x hx
      · simpa [hj] using (abs_nonneg _).trans (hC x hx)
    · intro i x hx
      rw [Finset.sum_eq_single (e i) (fun j _ hj => by simp [hj])
        (fun hj => absurd (Finset.mem_univ _) hj)]
      simp [h i x hx]
  · refine ⟨fun k i x => if i = sec k then 1 else 0,
      fun k i => ⟨1, fun x _ => by
        by_cases hi : i = sec k <;> simp [hi]⟩, ?_⟩
    intro k x hx
    rw [Finset.sum_eq_single (sec k) (fun i _ hi => by simp [hi])
      (fun hi => absurd (Finset.mem_univ _) hi)]
    rw [h (sec k) x hx, hone k x, hsec k]
    simp

/-- The single-pivot elementary operation, as a special case. -/
theorem IdealEqOn.elementary {K : Set X} (F : ι → X → ℝ)
    (i₀ : ι) (c : ι → X → ℝ)
    (hc : ∀ i, ∃ C, ∀ x ∈ K, |c i x| ≤ C) (hi₀ : ∀ x, c i₀ x = 0) :
    IdealEqOn K (fun i x => F i x + c i x * F i₀ x) F :=
  IdealEqOn.elementaryAt F (fun _ => i₀) c hc fun _ => hi₀

end Calculus

end SingularLearningTheory
