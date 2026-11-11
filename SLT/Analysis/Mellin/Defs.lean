/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Defs
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
# Mellin transforms: definitions

The Mellin transform and the truncated inverse Mellin integral of [Wat09, §4.3].

The definitions are those of `SLTChallenge/Mellin.lean`, word for word, and
`SLT/Analysis/Mellin.lean` proves its theorems.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory Set

/-- [Wat09, Definition 4.8]: `(𝓜f)(z) = ∫₀^∞ f(t) t^z dt`. Restated verbatim from the library under
the library's name.

Relation to the source.
* **Translation.** `mellinTransform f z` is the book's $\int_0^\infty f(t)\,t^z\,dt$ [Wat09, eq.
  (4.10)], Mathlib's `mellin f (z + 1)`. -/
noncomputable def mellinTransform (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ z * f t

end SingularLearningTheory

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology

/-- The truncated inverse Mellin integral of [Wat09, Remark 4.3(1)],
`(2πi)⁻¹ ∫_{c−iT}^{c+iT} F(z) t^(−z−1) dz`, parametrised by the imaginary coordinate. -/
noncomputable def inverseMellinTrunc (c : ℝ) (F : ℂ → ℂ)
    (t T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ y in (-T)..T,
    F ((c : ℂ) + Complex.I * y) *
      (t : ℂ) ^ (-((c : ℂ) + Complex.I * y) - 1)

end SingularLearningTheory
