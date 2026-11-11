/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
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
# Measure-preservation of sigma-currying

`MeasurableEquiv.piCurry` preserves the product measures: the product measure over a sigma type
curries to the iterated product measure.

The proof direction matters: `Measure.pi_eq` on the *sigma* side works
because a sigma-box pulls back under `piCurry.symm` to a nested box —
whereas on the curried side the box test ranges over arbitrary
measurable sets of the inner pi types, whose preimages are not
sigma-boxes.
-/

public section

open MeasureTheory Set

namespace MeasureTheory

variable {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
  {X : (i : ι) → κ i → Type*} [∀ i j, MeasurableSpace (X i j)]

/-- Sigma-uncurrying carries the iterated product measure to the
product over the sigma type. -/
theorem measurePreserving_piCurry_symm
    (μ : (p : Σ i, κ i) → Measure (X p.1 p.2)) [∀ p, SigmaFinite (μ p)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm
      (Measure.pi fun i => Measure.pi fun j => μ ⟨i, j⟩)
      (Measure.pi μ) := by
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable,
    (Measure.pi_eq fun t ht => ?_).symm⟩
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry X).symm ⁻¹' univ.pi t =
      univ.pi fun i => univ.pi fun j => t ⟨i, j⟩ := by
    ext g
    simp only [mem_preimage, mem_pi, mem_univ, forall_const,
      MeasurableEquiv.piCurry, Equiv.piCurry, Sigma.forall]
    exact Iff.rfl
  rw [hpre, Measure.pi_pi]
  calc ∏ i, (Measure.pi fun j => μ ⟨i, j⟩)
        (univ.pi fun j => t ⟨i, j⟩)
      = ∏ i, ∏ j, μ ⟨i, j⟩ (t ⟨i, j⟩) := by
        refine Finset.prod_congr rfl fun i _ => Measure.pi_pi _ _
    _ = ∏ p : Σ i, κ i, μ p (t p) := by
        conv_rhs => rw [← Finset.univ_sigma_univ, Finset.prod_sigma]

/-- Sigma-currying carries the product measure over the sigma type to
the iterated product measure. -/
theorem measurePreserving_piCurry
    (μ : (p : Σ i, κ i) → Measure (X p.1 p.2)) [∀ p, SigmaFinite (μ p)] :
    MeasurePreserving (MeasurableEquiv.piCurry X) (Measure.pi μ)
      (Measure.pi fun i => Measure.pi fun j => μ ⟨i, j⟩) :=
  (measurePreserving_piCurry_symm μ).symm _

end MeasureTheory
