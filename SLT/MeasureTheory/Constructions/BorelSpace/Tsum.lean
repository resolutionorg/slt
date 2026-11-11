/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
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
# Measurability of real-valued countable sums

No thesis counterpart; used by the samplewise representatives of `L²(q)`-valued analytic maps
(`FreeEnergy/SamplewiseResolution.lean`). Mathlib has `Measurable.ennreal_tsum` and
`Measurable.nnreal_tsum`; for real-valued series the sum is the difference of the sums of the
positive and negative parts on the (measurable) set of absolute summability and `0` elsewhere.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set
open scoped ENNReal

variable {X ι : Type*} [MeasurableSpace X] [Countable ι]

/-- The set of absolute summability of a countable family of real functions is measurable. -/
private theorem measurableSet_summable_abs {g : ι → X → ℝ} (hg : ∀ i, Measurable (g i)) :
    MeasurableSet {x | Summable fun i ↦ |g i x|} := by
  have h : {x | Summable fun i ↦ |g i x|} = {x | ∑' i, (‖g i x‖₊ : ℝ≥0∞) ≠ ⊤} := by
    ext x
    simp only [mem_ofPred_eq, ENNReal.tsum_coe_ne_top_iff_summable, ← NNReal.summable_coe,
      coe_nnnorm, Real.norm_eq_abs]
  rw [h]
  exact (Measurable.tsum fun i ↦ (hg i).nnnorm.coe_nnreal_ennreal)
    (measurableSet_singleton ⊤).compl

/-- A countable sum of measurable real functions is measurable (Lean's `tsum` is `0` where the
series is not summable, and for real series summability is absolute summability). -/
theorem _root_.Measurable.real_tsum {g : ι → X → ℝ} (hg : ∀ i, Measurable (g i)) :
    Measurable fun x ↦ ∑' i, g i x := by
  set S := {x | Summable fun i ↦ |g i x|} with hS
  have key : ∀ x, (∑' i, g i x) = S.indicator (fun x ↦ (∑' i, ENNReal.ofReal (g i x)).toReal
      - (∑' i, ENNReal.ofReal (-g i x)).toReal) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      have habs : Summable fun i ↦ |g i x| := hx
      have hpos : Summable fun i ↦ max (g i x) 0 :=
        habs.of_nonneg_of_le (fun i ↦ le_max_right _ _)
          (fun i ↦ max_le (le_abs_self _) (abs_nonneg _))
      have hneg : Summable fun i ↦ max (-g i x) 0 :=
        habs.of_nonneg_of_le (fun i ↦ le_max_right _ _)
          (fun i ↦ max_le (neg_le_abs _) (abs_nonneg _))
      have h1 : ∀ f : ι → ℝ, (∀ i, 0 ≤ f i) → Summable f →
          (∑' i, ENNReal.ofReal (f i)).toReal = ∑' i, f i := fun f hf hs ↦ by
        rw [← ENNReal.ofReal_tsum_of_nonneg hf hs, ENNReal.toReal_ofReal (tsum_nonneg hf)]
      have e : ∀ r : ℝ, ENNReal.ofReal r = ENNReal.ofReal (max r 0) := fun r ↦ by
        rcases le_total r 0 with h | h
        · rw [max_eq_right h, ENNReal.ofReal_eq_zero.2 h, ENNReal.ofReal_zero]
        · rw [max_eq_left h]
      have e1 : (fun i ↦ ENNReal.ofReal (g i x)) = fun i ↦ ENNReal.ofReal (max (g i x) 0) :=
        funext fun i ↦ e _
      have e2 : (fun i ↦ ENNReal.ofReal (-g i x)) = fun i ↦ ENNReal.ofReal (max (-g i x) 0) :=
        funext fun i ↦ e _
      rw [e1, e2, h1 _ (fun i ↦ le_max_right _ _) hpos, h1 _ (fun i ↦ le_max_right _ _) hneg,
        ← hpos.tsum_sub hneg]
      simp_rw [max_zero_sub_max_neg_zero_eq_self]
    · rw [indicator_of_notMem hx, tsum_eq_zero_of_not_summable]
      exact fun h ↦ hx (summable_abs_iff.2 h)
  have hmeas : Measurable (S.indicator fun x ↦ (∑' i, ENNReal.ofReal (g i x)).toReal
      - (∑' i, ENNReal.ofReal (-g i x)).toReal) := by
    refine Measurable.indicator (Measurable.sub ?_ ?_) (measurableSet_summable_abs hg)
    · exact (Measurable.tsum fun i ↦ ENNReal.measurable_ofReal.comp (hg i)).ennreal_toReal
    · exact (Measurable.tsum fun i ↦
        ENNReal.measurable_ofReal.comp (hg i).neg).ennreal_toReal
  rw [funext key]
  exact hmeas

end SingularLearningTheory
