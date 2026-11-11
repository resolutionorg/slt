/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import SLT.VolumeScaling.CompactLocalize
import SLT.VolumeScaling.Basic
public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
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
# Stability of the volume-scaling exponents at a base point

The naive stability claim — the exponents are unchanged by shrinking the
compact neighborhood — is FALSE: for `F x = x ^ 2 * (x - 1/2) ^ 4` at `0` the
exponent on `[-1, 1]` is `1/4` (the quartic zero at `1/2` dominates) but `1/2`
on `[-1/4, 1/4]` (only the origin's zero remains). The two true replacements:

- **the monotone sandwich** — committed as `hasLLCExponentsOn_of_between`
  (`Dln/VolumeScaling/CompactLocalize.lean`); this file adds the
  compact-neighborhood phrasing
  (`SingularLearningTheory.HasLLCExponentsOn.of_between_isCompact`) and
  its closed-ball specialization, order-convexity in the radius
  (`hasLLCExponentsOn_closedBall_of_between`);
- **the basis form** (`HasLLCExponentsAt`, defined in hironaka's
  `SLT/VolumeScaling/Defs.lean`): the exponents at a base
  point are defined by agreement on all sufficiently small closed balls, so
  independence of the neighborhood choice is built into the definition. This
  file proves its API; uniqueness is inherited from `HasLLCExponentsOn.unique`.
-/

public section

open Filter MeasureTheory Set Metric
open scoped Topology ENNReal

namespace SingularLearningTheory

section Sandwich

variable {α : Type*} [MeasurableSpace α] [TopologicalSpace α] {μ : Measure α}
  [IsFiniteMeasureOnCompacts μ] {f : α → ℝ} {L K U : Set α} {lam theta : ℝ}

/-- The monotone sandwich in compact-neighborhood phrasing: if an inner set and
an outer compact set carry the same volume-scaling exponents, so does any set
between them. The finiteness hypothesis of `hasLLCExponentsOn_of_between` is
discharged by compactness. -/
theorem HasLLCExponentsOn.of_between_isCompact
    (hL : HasLLCExponentsOn μ L f lam theta) (hU : HasLLCExponentsOn μ U f lam theta)
    (hLK : L ⊆ K) (hKU : K ⊆ U) (hUc : IsCompact U) :
    HasLLCExponentsOn μ K f lam theta :=
  hasLLCExponentsOn_of_between hL hU hLK hKU hUc.measure_lt_top.ne

end Sandwich

section BasisForm

variable {α : Type*} [MeasurableSpace α] [PseudoMetricSpace α] {μ : Measure α}
  {f : α → ℝ} {w : α} {lam theta : ℝ}

/-- Radial order-convexity: if two closed balls at `w` carry the exponents
`(lam, theta)`, so does every closed ball of intermediate radius. The
closed-ball specialization of the committed monotone sandwich. -/
private theorem hasLLCExponentsOn_closedBall_of_between {r₀ r r₁ : ℝ}
    (h₀ : HasLLCExponentsOn μ (closedBall w r₀) f lam theta)
    (h₁ : HasLLCExponentsOn μ (closedBall w r₁) f lam theta)
    (hr₀ : r₀ ≤ r) (hr₁ : r ≤ r₁) (hfin : μ (closedBall w r₁) ≠ ∞) :
    HasLLCExponentsOn μ (closedBall w r) f lam theta :=
  hasLLCExponentsOn_of_between h₀ h₁
    (closedBall_subset_closedBall hr₀) (closedBall_subset_closedBall hr₁) hfin

/-- The exponent pair at a base point is unique. -/
theorem HasLLCExponentsAt.unique {l₁ t₁ l₂ t₂ : ℝ}
    (h₁ : HasLLCExponentsAt μ f w l₁ t₁) (h₂ : HasLLCExponentsAt μ f w l₂ t₂) :
    l₁ = l₂ ∧ t₁ = t₂ := by
  obtain ⟨r, hr₁, hr₂⟩ := (h₁.and h₂).exists
  exact hr₁.unique hr₂

/-- Introduction rule with an explicit threshold: exponents on `closedBall w r`
for every `0 < r ≤ r₀` give the at-point exponents. -/
theorem HasLLCExponentsAt.of_forall_Ioc {r₀ : ℝ} (hr₀ : 0 < r₀)
    (h : ∀ r ∈ Ioc (0 : ℝ) r₀, HasLLCExponentsOn μ (closedBall w r) f lam theta) :
    HasLLCExponentsAt μ f w lam theta :=
  eventually_iff_exists_mem.mpr ⟨Ioc 0 r₀, Ioc_mem_nhdsGT hr₀, h⟩

/-- Elimination rule with an explicit threshold: the at-point exponents hold on
`closedBall w r` for every positive `r` below some positive threshold. -/
private theorem HasLLCExponentsAt.exists_forall_Ioo
    (h : HasLLCExponentsAt μ f w lam theta) :
    ∃ δ > (0 : ℝ), ∀ r ∈ Ioo (0 : ℝ) δ,
      HasLLCExponentsOn μ (closedBall w r) f lam theta := by
  obtain ⟨δ, hδ, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp h
  exact ⟨δ, hδ, fun r hr => hsub hr⟩

/-- From the at-point exponents, a single small closed ball carrying them. -/
theorem HasLLCExponentsAt.exists_closedBall
    (h : HasLLCExponentsAt μ f w lam theta) :
    ∃ r > (0 : ℝ), HasLLCExponentsOn μ (closedBall w r) f lam theta := by
  obtain ⟨r, hball, hr⟩ := (h.and eventually_mem_nhdsWithin).exists
  exact ⟨r, hr, hball⟩

/-- Bridge from the basis form to a concrete neighborhood: if the exponents
hold at `w` and on one closed ball of finite measure, they hold on the closed
ball of EVERY intermediate positive radius — small radii from the at-point
germ, the rest by the sandwich. -/
theorem HasLLCExponentsAt.closedBall_of_le_outer {R : ℝ}
    (hat : HasLLCExponentsAt μ f w lam theta)
    (hR : HasLLCExponentsOn μ (closedBall w R) f lam theta)
    (hRfin : μ (closedBall w R) ≠ ∞) :
    ∀ r, 0 < r → r ≤ R → HasLLCExponentsOn μ (closedBall w r) f lam theta := by
  intro r hr hrR
  obtain ⟨δ, hδ, hδball⟩ := hat.exists_forall_Ioo
  obtain ⟨r₀, hr₀, hr₀m⟩ := exists_between (lt_min hδ hr)
  exact hasLLCExponentsOn_closedBall_of_between
    (hδball r₀ ⟨hr₀, (lt_min_iff.mp hr₀m).1⟩) hR
    (lt_min_iff.mp hr₀m).2.le hrR hRfin

end BasisForm

end SingularLearningTheory
