/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import SLT.EmpiricalProcess.FourthMoment
public import SLT.EmpiricalProcess.Defs
public import SLT.Setting.Basic
public import Mathlib.Order.CompletePartialOrder
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
# The empirical process and its limit: proofs

The statements of `SLTChallenge/EmpiricalProcess.lean` ([Wat09, Chapter 5]), restated and
proved by delegation to `SLT/EmpiricalProcess/LimitOfAnalytic.lean` and
`SLT/EmpiricalProcess/FourthMoment.lean`. The Borel instances on `C(X, ℝ)` come from the
library.
-/

@[expose] public section

-- These statements mirror SLTChallenge word for word, so they keep hypotheses of the book
-- that the delegated proofs here don't need.
set_option linter.unusedVariables false

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal


universe uΩ

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
variable {d : ℕ}

/-- **Convergence in law of the empirical process.** For `W` compact, `s ≥ 2` an even integer and
`f` `L^s(q)`-valued real analytic on a neighbourhood of `W`, the empirical process of an i.i.d.
sample satisfies `EmpiricalProcessLimit` on `C(W, ℝ)`. Here `f(x, ·)` is assumed continuous on `W`
for `q`-almost every `x`, and the conclusion's random continuous function agrees with `ψ_n` almost
surely.

Relation to the source.
* **Gap.** $f(x, \cdot)$ is assumed continuous on $W$ for $q$-almost every $x$, which
  $L^s(q)$-valued analyticity does not give; the book takes $\psi_n$ to be continuous for every
  sample [Wat09, Remark 5.7].

Source statement: [Wat09, Theorem 5.9] -/
theorem convergence_of_empirical_process
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {d : ℕ}
    (q : Measure X) [IsProbabilityMeasure q] (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    (s : ℝ≥0∞) [Fact (1 ≤ s)] (hs : ∃ k : ℕ, s = ((2 * (k + 1) : ℕ) : ℝ≥0∞))
    (f : X → (Fin d → ℝ) → ℝ) (hf_meas : ∀ w, Measurable fun x ↦ f x w)
    (hf_cont : ∀ᵐ x ∂q, ContinuousOn (f x) W) (hf : LsValuedAnalytic s q f W)
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P'),
      Nonempty (EmpiricalProcessLimit q (fun x (w : W) ↦ f x w) Xs P P') := by
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  obtain ⟨k, hk⟩ := hs
  have hs2 : (2 : ℝ≥0∞) ≤ s := by
    rw [hk]
    exact_mod_cast (by omega : 2 ≤ 2 * (k + 1))
  obtain ⟨P', hP', hE⟩ := LsValuedAnalytic.exists_empiricalProcessLimit hs2 hW hf_meas hf_cont
    hf (fun i ↦ (hX i).measurable) (fun i ↦ (hX i).map_eq) hIndep
  exact ⟨C(W, ℝ), inferInstance, P', hP',
    hE⟩

/-- **Moments of the supremum of the empirical process.** For `W` compact, `s ≥ 2` an even integer
and `f` `L^s(q)`-valued real analytic on a neighbourhood of `W`, the empirical process of an i.i.d.
sample satisfies `E[sup_{w ∈ W} |ψ_n(w)|^s] ≤ C` with `C` independent of `n`. As in Theorem 5.9,
`f(x, ·)` is assumed continuous on `W` for `q`-almost every `x`.

Relation to the source.
* **Gap.** $f(x, \cdot)$ is assumed continuous on $W$ for $q$-almost every $x$, as in
  `convergence_of_empirical_process`.

Source statement: [Wat09, Theorem 5.8] -/
theorem exists_lintegral_iSup_empiricalProcess_pow_le
    {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {d : ℕ}
    (q : Measure X) [IsProbabilityMeasure q] (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    (s : ℝ≥0∞) [Fact (1 ≤ s)] (hs : ∃ k : ℕ, s = ((2 * (k + 1) : ℕ) : ℝ≥0∞))
    (f : X → (Fin d → ℝ) → ℝ) (hf_meas : ∀ w, Measurable fun x ↦ f x w)
    (hf_cont : ∀ᵐ x ∂q, ContinuousOn (f x) W) (hf : LsValuedAnalytic s q f W)
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∀ n, ∫⁻ ω, (⨆ w ∈ W, ‖empiricalProcess q f Xs n ω w‖ₑ) ^ s.toReal ∂P ≤ C := by
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  obtain ⟨k, hk⟩ := hs
  have hs2 : (2 : ℝ≥0∞) ≤ s := by
    rw [hk]
    exact_mod_cast (by omega : 2 ≤ 2 * (k + 1))
  obtain ⟨P', hP', ⟨E⟩⟩ := LsValuedAnalytic.exists_empiricalProcessLimit hs2 hW hf_meas hf_cont
    hf (fun i ↦ (hX i).measurable) (fun i ↦ (hX i).map_eq) hIndep
  have hsm : s = 2 * ((k + 1 : ℕ) : ℝ≥0∞) := by rw [hk]; push_cast; ring
  obtain ⟨C, hC, hCn⟩ := E.momentBound_of_lsValuedAnalytic_even hW (fun i ↦ (hX i).measurable)
    (fun i ↦ (hX i).map_eq) hIndep hf_cont
    (by omega : 1 ≤ k + 1) hsm hf
  refine ⟨C, hC, fun n ↦ le_of_eq_of_le (lintegral_congr_ae ?_) (hCn n)⟩
  filter_upwards [E.Ψ_ae_eq n] with ω hω
  rw [iSup_subtype']
  simp only [hω, hk, ENNReal.toReal_natCast, ENNReal.rpow_natCast]
  rfl

end SingularLearningTheory
