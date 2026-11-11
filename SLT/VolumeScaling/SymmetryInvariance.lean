/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Defs
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
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
# Sublevel-volume exponents are invariant under a loss-preserving symmetry

The cleanest tool for the blow-up chart-multiplicity gate: the learning coefficient is a
*symmetry invariant*. If `e` is a measure-preserving measurable automorphism of the ambient
under which the loss is invariant (`f ∘ e = f`), then for every set `A` the sublevel volume
of `f` on the image `e '' A` equals that on `A`, so `f` has the same volume-scaling exponents
on `e '' A` as on `A`.

This is strictly weaker than `HasLLCExponentsOn.comp_diffeo` (no derivative, no Jacobian
bound): the only inputs are measure-preservation and the pointwise loss identity `f ∘ e = f`.
It is the volume-language form of "the RLCT is invariant under an automorphism of the pair
(ambient, loss)", the indirect route to certifying the non-leading affine charts of a
blow-up: the symmetry that permutes the charts carries the leading chart's exponents to each
other chart, with no explicit monomializing change of variables.

The proof is three rewrites: the image/sublevel set identity
`e '' A ∩ {f ≤ ε} = e '' (A ∩ {f ≤ ε})` (using `f ∘ e = f`), and measure-preservation of `e`
(through its inverse) to drop the image.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

/-- The measure of a set is unchanged by a measure-preserving measurable automorphism. -/
private theorem measure_image_of_measurePreserving {e : α ≃ᵐ α}
    (he : MeasurePreserving e μ μ) {B : Set α} (hB : MeasurableSet B) :
    μ (e '' B) = μ B := by
  have h1 : (⇑e) '' B = ⇑e.symm ⁻¹' B := by
    ext x
    simp only [Set.mem_image, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rwa [MeasurableEquiv.symm_apply_apply]
    · intro hx
      exact ⟨e.symm x, hx, MeasurableEquiv.apply_symm_apply e x⟩
  rw [h1]
  exact (MeasurePreserving.symm e he).measure_preimage hB.nullMeasurableSet

/-- **Symmetry invariance of the sublevel volume.** If `e` is a measure-preserving
measurable automorphism with `f ∘ e = f`, the sublevel volume of `f` on `e '' A` equals
that on `A` at every threshold. -/
private theorem sublevelVol_image_of_symmetry {e : α ≃ᵐ α} (he : MeasurePreserving e μ μ)
    (hfe : ∀ x, f (e x) = f x) {A : Set α} (hA : MeasurableSet A) (hf : Measurable f)
    (ε : ℝ) :
    sublevelVol μ (e '' A) f ε = sublevelVol μ A f ε := by
  have hset : (e '' A) ∩ {x | f x ≤ ε} = e '' (A ∩ {x | f x ≤ ε}) := by
    rw [← Set.image_inter_preimage]
    congr 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, hfe x]
  have hmeas : MeasurableSet (A ∩ {x | f x ≤ ε}) := hA.inter (hf measurableSet_Iic)
  rw [sublevelVol, sublevelVol, hset, measure_image_of_measurePreserving he hmeas]

/-- **The symmetry lemma (exponent form).** If `e` is a measure-preserving measurable
automorphism with `f ∘ e = f`, then `f` has the same volume-scaling exponents on `e '' A`
as on `A`. This carries a chart's certified exponents to the image of that chart under a
loss-preserving symmetry — the indirect route to the non-leading affine charts of a blow-up,
needing no explicit monomializing change of variables. -/
theorem HasLLCExponentsOn.image_of_symmetry {e : α ≃ᵐ α} (he : MeasurePreserving e μ μ)
    (hfe : ∀ x, f (e x) = f x) {A : Set α} (hA : MeasurableSet A) (hf : Measurable f)
    {lam theta : ℝ} (h : HasLLCExponentsOn μ A f lam theta) :
    HasLLCExponentsOn μ (e '' A) f lam theta := by
  have hsv : sublevelVol μ (e '' A) f = sublevelVol μ A f :=
    funext fun ε => sublevelVol_image_of_symmetry he hfe hA hf ε
  unfold HasLLCExponentsOn
  rw [hsv]
  exact h

end SingularLearningTheory
