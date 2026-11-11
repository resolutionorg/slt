/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import SLT.PartialResolution.ExactTransport
public import SLT.PartialResolution.Defs
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
# A finite composite of transport maps is a transport (plan atom 3.2.10.1)

The change-of-variables map of a terminal chart is a finite composite of resolution
step maps, each carrying its own transport certificate (a single-coordinate monomial
Jacobian density, plan atom 3.2.9). This file records the generic fact that folds
those per-step certificates into one: a finite list of maps, each transporting a
measure to itself with its own density, composes (folding with function composition,
the identity for the empty list) to a single transport whose density is the
telescoped *pulled-back product* of the per-step densities — each step's density
evaluated at the point reached after applying the preceding steps.

Concretely, for steps `[s₁, …, s_k]` applied in order (`s₁` first), the composite
density at `x` is `s₁.J x · s₂.J (s₁ x) · … · s_k.J (s_{k-1} ⋯ s₁ x)`. This is the
``list composition'' fact of plan atom 3.2.10.1, the structural backbone of the
chart transport theorem (the chart-level node instantiates the list at a terminal
chart's step maps).

The proof is an induction on the list using the committed binary composition lemma
`VolumeScaling.TransportsToOn.comp` (the inner map sends the source set into the
outer map's domain — here trivially, every step is a transport on the whole space).
It depends only on Mathlib and the committed transport calculus.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory
open Analytic

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- **Plan atom 3.2.10.1.** A finite list of maps, each transporting `μ` to itself on
the whole space with its own density, composes (right fold of function composition,
identity at the empty list) to a single transport. The composite density is the
telescoped pulled-back product of the per-step densities: each step's density
evaluated at the image of the preceding steps. -/
theorem _root_.Analytic.transportsToOn_foldr
    (steps : List ((X → X) × (X → ℝ≥0∞)))
    (hsteps : ∀ s ∈ steps, TransportsToOn μ μ Set.univ s.1 s.2) :
    TransportsToOn μ μ Set.univ
      (steps.foldr (fun s acc => acc ∘ s.1) id)
      (steps.foldr (fun s accJ x => s.2 x * accJ (s.1 x)) fun _ => 1) := by
  induction steps with
  | nil => exact (MeasurableEquiv.refl X).transportsToOn_one (MeasurePreserving.id μ)
  | cons s rest ih =>
    exact (hsteps s List.mem_cons_self).comp
      (ih fun t ht => hsteps t (List.mem_cons_of_mem s ht)) (mapsTo_univ _ _)

end SingularLearningTheory
