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
# Sublevel volume under a measure-preserving model symmetry (orbit core)

A sublevel volume is invariant under a measure-preserving
self-equivalence of the ambient space that fixes the model: the
localization set transports along it.  This is the measure core of
the pivot-orbit transport — the non-representative cover pieces are
ambient relabelings of the representative one, and the relabeling
preserves both Lebesgue volume and the residual model, so the
sublevel volumes are *equal*, not merely comparable.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- The sublevel volume of the image of a measurable set under a
measure-preserving model-preserving self-equivalence equals that of
the set. -/
theorem sublevelVol_image_measurePreserving {τ : α ≃ᵐ α}
    (hτ : MeasurePreserving τ μ μ) {f : α → ℝ} (hf : Measurable f)
    (hcomp : ∀ x, f (τ x) = f x) {S : Set α} (hS : MeasurableSet S)
    (ε : ℝ) :
    sublevelVol μ (τ '' S) f ε = sublevelVol μ S f ε := by
  rw [sublevelVol, sublevelVol]
  congr 1
  have hB : MeasurableSet (S ∩ {x | f x ≤ ε}) :=
    hS.inter (hf measurableSet_Iic)
  have h1 : τ '' S ∩ {x | f x ≤ ε} = τ '' (S ∩ {x | f x ≤ ε}) := by
    rw [← Set.image_inter_preimage]
    congr 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, hcomp]
  have himg : τ '' (S ∩ {x | f x ≤ ε})
      = τ.symm ⁻¹' (S ∩ {x | f x ≤ ε}) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hy
      exact ⟨τ.symm y, hy, τ.apply_symm_apply y⟩
  rw [h1, himg, (hτ.symm).measure_preimage hB.nullMeasurableSet]

end SingularLearningTheory
