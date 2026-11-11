/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
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
# Gaussian laws from their one-dimensional marginals

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 4.2.9] (3), identification of the limit | |
| | `Measure.ext_of_map_continuousLinearMap`,
`ProbabilityTheory.covariance_eq_of_map_eq_gaussianReal` |

A probability measure on `ℝ^M` is determined by its images under the linear functionals
(Cramér–Wold, via characteristic functions), and a pair of real random variables whose sum
and summands are centred Gaussian has covariance `(c − a − b)/2` in terms of the three
variances.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

/-- Cramér–Wold: two probability measures on `ℝ^M` with the same one-dimensional linear
images are equal. -/
theorem _root_.MeasureTheory.Measure.ext_of_map_continuousLinearMap {M : ℕ}
    {μ ν : Measure (Fin M → ℝ)} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ L : (Fin M → ℝ) →L[ℝ] ℝ, μ.map L = ν.map L) : μ = ν := by
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  rw [charFunDual_eq_charFun_map_one, charFunDual_eq_charFun_map_one, h L]

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
/-- A real random variable with law `N(0, a)` is in `L²` with mean `0` and variance `a`. -/
theorem _root_.ProbabilityTheory.memLp_two_and_integral_eq_zero_of_map_eq_gaussianReal {A : Ω → ℝ}
    (hA : Measurable A)
    {a : NNReal} (h : ν.map A = gaussianReal 0 a) :
    MemLp A 2 ν ∧ ∫ ω, A ω ∂ν = 0 ∧ Var[A; ν] = a := by
  refine ⟨?_, ?_, ?_⟩
  · have := (memLp_map_measure_iff (p := 2) aestronglyMeasurable_id hA.aemeasurable).1
      (h ▸ memLp_id_gaussianReal (μ := 0) (v := a) 2)
    simpa [Function.comp_def] using this
  · have := integral_map (μ := ν) (f := id) hA.aemeasurable aestronglyMeasurable_id
    simpa [h, integral_id_gaussianReal] using this.symm
  · rw [← variance_id_map hA.aemeasurable, h, variance_id_gaussianReal]

/-- If `A`, `B` and `A + B` have laws `N(0, a)`, `N(0, b)` and `N(0, c)`, then
`cov(A, B) = (c − a − b)/2`. -/
theorem _root_.ProbabilityTheory.covariance_eq_of_map_eq_gaussianReal {A B : Ω → ℝ}
    (hA : Measurable A)
    (hB : Measurable B) {a b c : NNReal} (ha : ν.map A = gaussianReal 0 a)
    (hb : ν.map B = gaussianReal 0 b) (hc : ν.map (A + B) = gaussianReal 0 c) :
    cov[A, B; ν] = ((c : ℝ) - a - b) / 2 := by
  obtain ⟨hA2, -, hVa⟩ := memLp_two_and_integral_eq_zero_of_map_eq_gaussianReal hA ha
  obtain ⟨hB2, -, hVb⟩ := memLp_two_and_integral_eq_zero_of_map_eq_gaussianReal hB hb
  obtain ⟨-, -, hVc⟩ :=
    memLp_two_and_integral_eq_zero_of_map_eq_gaussianReal (A := A + B) (hA.add hB) hc
  have := variance_add hA2 hB2
  rw [hVc, hVa, hVb] at this
  linarith

end SingularLearningTheory
