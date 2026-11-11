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
# Mellin transforms: challenge statements

Statements for [Wat09, §4.3]. `SLT/Analysis/Mellin/Defs.lean` has the definitions word for
word, and `SLT/Analysis/Mellin.lean` proves the theorems.
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

/-- **Holomorphy on a strip of absolute convergence.** Weighted integrability
at both boundary exponents gives a holomorphic Mellin transform in the intervening strip. -/
theorem mellinTransform_differentiableOn_strip
    (f : ℝ → ℝ) (a b : ℝ) (hab : a < b)
    (ha : IntegrableOn (fun t ↦ f t * t ^ a) (Ioi 0))
    (hb : IntegrableOn (fun t ↦ f t * t ^ b) (Ioi 0)) :
    DifferentiableOn ℂ (SingularLearningTheory.mellinTransform f)
      {z : ℂ | a < z.re ∧ z.re < b} :=
  sorry

/-- The truncated inverse Mellin integral of [Wat09, Remark 4.3(1)],
`(2πi)⁻¹ ∫_{c−iT}^{c+iT} F(z) t^(−z−1) dz`, parametrised by the imaginary coordinate. -/
noncomputable def inverseMellinTrunc (c : ℝ) (F : ℂ → ℂ)
    (t T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ))⁻¹ * ∫ y in (-T)..T,
    F ((c : ℂ) + Complex.I * y) *
      (t : ℂ) ^ (-((c : ℂ) + Complex.I * y) - 1)

/-- **Mellin inversion for functions of bounded variation.** If `f` has bounded variation near `t`,
the truncated inverse Mellin integrals converge to the average of the two one-sided limits of `f` at
`t`. The inverse integral is the symmetric limit `T → ∞`, as in Remark 4.3(1).

Relation to the source.
* **Strengthening.** Integrability of $f(t)\,t^c$ on the line $\operatorname{Re} z = c$ replaces the
  book's absolute convergence on a strip $a < \operatorname{Re} z < b$.

Source statement: [Wat09, Theorem 4.5] -/
theorem inverseMellin_tendsto_of_boundedVariation
    (f : ℝ → ℝ) (c : ℝ)
    -- Assumes integrability on Re z = c rather than in a strip a < Re(z) < b
    (hconv : IntegrableOn (fun t ↦ f t * t ^ c) (Ioi 0))
    (t ε : ℝ) (ht : 0 < t) (hε : 0 < ε) (hεt : ε < t)
    (hbv : BoundedVariationOn f (Icc (t - ε) (t + ε)))
    (fp fm : ℝ) (hfp : Tendsto f (𝓝[>] t) (𝓝 fp))
    (hfm : Tendsto f (𝓝[<] t) (𝓝 fm)) :
    Tendsto (fun T ↦ inverseMellinTrunc c (SingularLearningTheory.mellinTransform f) t T)
      atTop (𝓝 (((fp + fm) / 2 : ℝ) : ℂ)) :=
  sorry

/-- **Mellin transform of a power times a power of the logarithm.** For `Re z > −λ`, the Mellin
transform of `f(t) = 𝟙_(0,a)(t) a^(−λ)/(m−1)! t^(λ−1) log(a/t)^(m−1)` is `a^z/(z+λ)^m`.

Relation to the source.
* **Strengthening.** The book's assumption $\lambda > 0$ is not needed.

Source statement: [Wat09, Example 4.7] -/
theorem mellinTransform_power_log
    (lam a : ℝ) (ha : 0 < a) (m : ℕ) (hm : 1 ≤ m)
    (z : ℂ) (hz : -lam < z.re) :
    let f := (Ioo 0 a).indicator
      (fun t ↦ a ^ (-lam) / (m - 1).factorial * t ^ (lam - 1) * Real.log (a / t) ^ (m - 1))
    SingularLearningTheory.mellinTransform f z = (a : ℂ) ^ z / (z + (lam : ℂ)) ^ m :=
  sorry

end SingularLearningTheory
