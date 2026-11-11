/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.BlowUpSubstitution
import Mathlib.MeasureTheory.Order.Group.Lattice
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
# The exceptional-exponent update (K4.3)

A monomial pulled back along the codimension-`(n+1)` scaling chart is
again a monomial: the block exponents are untouched and the exceptional
exponent gains the block sum,

  `(|u|^{M₀} ∏ᵢ |xᵢ|^{Mᵢ}) ∘ chartScaleVec = |u|^{M₀ + ∑ᵢ Mᵢ} ∏ᵢ |xᵢ|^{Mᵢ}`.

This is the algebra half of Aoyagi's exceptional-substitution update
`M' = M + J₁(M^{(S+1)} − J)`; the `−J` (Jacobian) half lives in K4.2's
`|u|^n` density, so composing this file's pullback identity with
`sublevelVol_chartScaleVec` hands the weighted-monomial lemmas a plain
monomial with updated exponents — no measure work at the call site.

The nonnegativity hypothesis on the block exponents is load-bearing:
at `u = 0` with exponents `(1, −1)` the product collapses to `0` while
the collected form is `0^0 = 1`.
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {n : ℕ}

/-- `∏ᵢ x^{Mᵢ} = x^{∑ᵢ Mᵢ}` for a nonnegative base and nonnegative
exponents (including `x = 0`, where both sides are `0` unless every
exponent vanishes). -/
private theorem rpow_sum_of_nonneg {x : ℝ} (hx : 0 ≤ x) {M : Fin n → ℝ}
    (hM : ∀ i, 0 ≤ M i) :
    ∏ i, x ^ M i = x ^ (∑ i, M i) := by
  rcases eq_or_lt_of_le hx with hx0 | hxpos
  · rcases eq_or_ne (∑ i, M i) 0 with hs | hs
    · have hall : ∀ i ∈ Finset.univ, M i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hM i).mp hs
      rw [← hx0, hs, Real.rpow_zero]
      exact Finset.prod_eq_one fun i hi => by
        rw [hall i hi, Real.rpow_zero]
    · obtain ⟨j, hj⟩ : ∃ j, M j ≠ 0 := by
        by_contra hno
        exact hs (Finset.sum_eq_zero fun i _ =>
          not_not.mp fun hne => hno ⟨i, hne⟩)
      rw [← hx0, Real.zero_rpow hs]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (Real.zero_rpow hj)
  · rw [← Real.rpow_sum_of_pos hxpos]

/-- The monomial family the blow-up bookkeeping moves around: an
exceptional power times a block monomial. -/
@[expose] noncomputable def expMonomial (M₀ : ℝ) (M : Fin n → ℝ)
    (p : (ℝ × α) × (Fin n → ℝ)) : ℝ :=
  |p.1.1| ^ M₀ * ∏ i, |p.2 i| ^ M i

private theorem measurable_expMonomial (M₀ : ℝ) (M : Fin n → ℝ) :
    Measurable (expMonomial (α := α) M₀ M) := by
  unfold expMonomial
  fun_prop

omit [MeasurableSpace α] in
/-- **K4.3, the exceptional-exponent update**: pulling a monomial back
along the scaling chart updates only the exceptional exponent, by the
block sum. -/
private theorem expMonomial_comp_chartScaleVec {M₀ : ℝ} (hM₀ : 0 ≤ M₀)
    {M : Fin n → ℝ} (hM : ∀ i, 0 ≤ M i) :
    expMonomial (α := α) M₀ M ∘ chartScaleVec
      = expMonomial (M₀ + ∑ i, M i) M := by
  funext p
  show |p.1.1| ^ M₀ * ∏ i, |p.1.1 * p.2 i| ^ M i
    = |p.1.1| ^ (M₀ + ∑ i, M i) * ∏ i, |p.2 i| ^ M i
  have hsplit : ∀ i, |p.1.1 * p.2 i| ^ M i
      = |p.1.1| ^ M i * |p.2 i| ^ M i := fun i => by
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  calc |p.1.1| ^ M₀ * ∏ i, |p.1.1 * p.2 i| ^ M i
      = |p.1.1| ^ M₀ * ((∏ i, |p.1.1| ^ M i) * ∏ i, |p.2 i| ^ M i) := by
        rw [← Finset.prod_mul_distrib]
        exact congrArg _ (Finset.prod_congr rfl fun i _ => hsplit i)
    _ = |p.1.1| ^ M₀ * (|p.1.1| ^ (∑ i, M i) * ∏ i, |p.2 i| ^ M i) := by
        rw [rpow_sum_of_nonneg (abs_nonneg _) hM]
    _ = |p.1.1| ^ (M₀ + ∑ i, M i) * ∏ i, |p.2 i| ^ M i := by
        rw [← mul_assoc, Real.rpow_add_of_nonneg (abs_nonneg _) hM₀
          (Finset.sum_nonneg fun i _ => hM i)]

/-- The K4.2 measure identity specialized to monomials: the sublevel
volume of a monomial on a chart image equals that of the
exponent-updated monomial on the source, against the Jacobian-weighted
measure. The weighted-monomial lemmas consume the right-hand side
directly. -/
theorem sublevelVol_chartScaleVec_expMonomial (μ : Measure (ℝ × α))
    [SFinite μ] {K : Set ((ℝ × α) × (Fin n → ℝ))} (hK : MeasurableSet K)
    (hImg : MeasurableSet (chartScaleVec '' K))
    {M₀ : ℝ} (hM₀ : 0 ≤ M₀) {M : Fin n → ℝ} (hM : ∀ i, 0 ≤ M i) (ε : ℝ) :
    sublevelVol (μ.prod volume) (chartScaleVec '' K)
      (expMonomial M₀ M) ε
      = sublevelVol
          ((μ.prod volume).withDensity
            (fun p => ENNReal.ofReal (|p.1.1| ^ n))) K
          (expMonomial (M₀ + ∑ i, M i) M) ε := by
  rw [sublevelVol_chartScaleVec μ hK hImg (measurable_expMonomial M₀ M) ε,
    expMonomial_comp_chartScaleVec hM₀ hM]

end SingularLearningTheory
