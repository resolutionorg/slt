/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
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
# The central limit theorem for the finite-dimensional distributions

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 4.2.9] (3), the CLT step |
`ProbabilityTheory.tendstoInDistribution_empiricalSum` |

For an i.i.d. sample `X_i ∼ q` and `h ∈ L²(q)`, `n^{-1/2} Σ_{i<n} (h(X_i) − E h)` converges in
distribution to `N(0, Var_q h)` (Mathlib's `tendstoInDistribution_inv_sqrt_mul_sum_sub`).
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- The scalar central limit theorem for the centred empirical sums of `h ∈ L²(q)` along an
i.i.d. sample, with the limit `N(0, Var_q h)` realised as the identity on `ℝ`. -/
theorem _root_.ProbabilityTheory.tendstoInDistribution_empiricalSum {q : Measure X}
    [IsProbabilityMeasure q]
    {P : Measure Ω} [IsProbabilityMeasure P] {Xs : ℕ → Ω → X} (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {h : X → ℝ} (hm : Measurable h)
    (hh : MemLp h 2 q) :
    TendstoInDistribution
      (fun (n : ℕ) (ω : Ω) ↦ (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (h (Xs i ω) - ∫ x, h x ∂q))
      atTop id (fun _ ↦ P) (gaussianReal 0 (Var[h; q]).toNNReal) := by
  have hq : q = P.map (Xs 0) := (hlaw 0).symm
  have hmq : AEStronglyMeasurable h (P.map (Xs 0)) := hm.aestronglyMeasurable
  have hvar : Var[h ∘ Xs 0; P] = Var[h; q] := by
    rw [hq, variance_map hm.aemeasurable (hX 0).aemeasurable]
  have hmean : ∫ ω, h (Xs 0 ω) ∂P = ∫ x, h x ∂q := by
    rw [hq, integral_map (hX 0).aemeasurable hmq]
  have hL2 : MemLp (h ∘ Xs 0) 2 P := by
    rw [hq] at hh; exact (memLp_map_measure_iff hmq (hX 0).aemeasurable).1 hh
  have hident : ∀ i, IdentDistrib (h ∘ Xs i) (h ∘ Xs 0) P P := fun i ↦
    IdentDistrib.comp ⟨(hX i).aemeasurable, (hX 0).aemeasurable, by rw [hlaw i, hlaw 0]⟩ hm
  have hY : HasLaw id (gaussianReal 0 (Var[h ∘ Xs 0; P]).toNNReal)
      (gaussianReal 0 (Var[h; q]).toNNReal) := by
    rw [hvar]; exact HasLaw.id
  have key := tendstoInDistribution_inv_sqrt_mul_sum_sub (X := fun i ↦ h ∘ Xs i) hY hL2
    (hind.comp (fun _ ↦ h) fun _ ↦ hm) hident
  have heq : (fun (n : ℕ) (ω : Ω) ↦ (√(n : ℝ))⁻¹ * ∑ i ∈ Finset.range n, (h (Xs i ω) - ∫ x, h x ∂q))
      = fun (n : ℕ) ω ↦ (√(n : ℝ))⁻¹ * (∑ k ∈ Finset.range n, (h ∘ Xs k) ω - n * P[h ∘ Xs 0]) := by
    funext n ω
    simp only [Function.comp_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, hmean]
  rw [heq]; exact key

end SingularLearningTheory
