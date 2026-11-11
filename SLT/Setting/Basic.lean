/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Setting
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Probability.Independence.Basic

/-!
# Basic facts about the setting

Realisability and essential uniqueness ([Hit26, Section 2.3]), for an abstract parameter type,
and the first facts about the definitions of `SLT/Setting.lean`: `K(w₀) = 0`, measurability
of the log density ratio, `K ≥ 0` under relatively finite variance, and the nonnegativity and
continuity of a prior satisfying fundamental condition II.

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 2.3.1] | `Realizable` |
| [Hit26, Definition 2.3.2] | `EssentiallyUnique` |
-/

public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SingularLearningTheory

section Realizability

-- Ambient statistical setup, declared once and shared by everything below.
-- `X`  : the sample space (needs a `MeasurableSpace` so we can integrate / talk about `q`-a.e.)
-- `q`  : the true distribution, a measure on `X`
-- `W`  : the parameter space
-- `p w`: the model density at parameter `w` (a function `X → ℝ`)
-- `W₀` : the set of optimal parameters
variable {X : Type*} [MeasurableSpace X]
variable {W : Type*}
variable (q : Measure X) (p : W → X → ℝ) (W₀ : Set W)

/-- [Hit26, Definition 2.3.1]. The true distribution is *realisable* if
some parameter's model reproduces it exactly. -/
def Realizable (q₀ : X → ℝ) : Prop := ∃ w : W, p w = q₀

/-- The optimal distribution is *essentially unique* if there is a single density
`p₀` that every optimal parameter's model agrees with, `q`-almost-everywhere.
[Hit26, Definition 2.3.2]. -/
@[expose] def EssentiallyUnique : Prop :=
  ∃ p₀ : X → ℝ, ∀ w₀ ∈ W₀, p w₀ =ᵐ[q] p₀

end Realizability

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

/-! ## The excess loss and relatively finite variance -/

section ExcessLoss

variable {W : Set (Fin d → ℝ)}

/-- `K(w₀) = 0`: `f(x, w₀) = log (p(x|w₀)/p(x|w₀))` is `log 1 = 0`, or `log 0 = 0` where
`p(x|w₀) = 0`. -/
theorem excessLoss_self (q : Measure X) (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ) :
    excessLoss q p w₀ w₀ = 0 := by
  have : ∀ x, logDensityRatio p w₀ x w₀ = 0 := fun x ↦ by
    unfold logDensityRatio
    rcases eq_or_ne (p w₀ x) 0 with h | h
    · simp [h]
    · simp [div_self h]
  simp [excessLoss, this]

theorem measurable_uncurry_logDensityRatio {p : (Fin d → ℝ) → X → ℝ}
    (hp : Measurable (Function.uncurry p)) (w₀ : Fin d → ℝ) :
    Measurable (Function.uncurry (logDensityRatio p w₀)) := by
  have h1 : Measurable fun z : X × (Fin d → ℝ) ↦ p w₀ z.1 :=
    hp.comp (measurable_const.prodMk measurable_fst)
  have h2 : Measurable fun z : X × (Fin d → ℝ) ↦ p z.2 z.1 :=
    hp.comp (measurable_snd.prodMk measurable_fst)
  exact Real.measurable_log.comp (h1.div h2)

theorem RelativelyFiniteVariance.excessLoss_nonneg {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    {w₀ : Fin d → ℝ} (h : RelativelyFiniteVariance q p w₀ W) :
    ∀ w ∈ W, 0 ≤ excessLoss q p w₀ w := by
  obtain ⟨C, hC, h⟩ := h
  intro w hw
  exact (mul_nonneg hC.le (integral_nonneg fun x ↦ sq_nonneg (logDensityRatio p w₀ x w))).trans
    (h w hw).2

/-- RFV in the library's form `E_q[f²] ≤ C⁻¹ K`. -/
theorem RelativelyFiniteVariance.exists_integral_sq_le_inv_mul {q : Measure X}
    {p : (Fin d → ℝ) → X → ℝ} {w₀ : Fin d → ℝ}
    (h : RelativelyFiniteVariance q p w₀ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ w ∈ W, ∫ x, logDensityRatio p w₀ x w ^ 2 ∂q ≤ C⁻¹ * excessLoss q p w₀ w := by
  obtain ⟨C, hC, h⟩ := h
  exact ⟨C, hC, fun w hw ↦ (le_inv_mul_iff₀ hC).mpr (h w hw).2⟩

end ExcessLoss

/-! ## Fundamental condition II -/

namespace FundamentalConditionII

variable {φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- Under fundamental condition II the prior is nonnegative on `W`. -/
theorem nonneg (II : FundamentalConditionII φ W) {w : Fin d → ℝ} (hw : w ∈ W) : 0 ≤ φ w := by
  obtain ⟨U, -, hWU, φ₁, φ₂, h1, -, h2, -, hφ⟩ := II.factor
  rw [hφ w (hWU hw)]
  exact mul_nonneg (h1 w (hWU hw)).le (h2 w hw)

/-- Under fundamental condition II the prior is continuous on `W`. -/
theorem continuousOn (II : FundamentalConditionII φ W) : ContinuousOn φ W := by
  obtain ⟨U, -, hWU, φ₁, φ₂, -, h1, -, h2, hφ⟩ := II.factor
  exact ((h1.continuousOn.mul h2.continuousOn).congr fun w hw ↦ hφ w hw).mono hWU

end FundamentalConditionII

end SingularLearningTheory
