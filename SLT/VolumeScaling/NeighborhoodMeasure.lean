/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.ChartFamily.Defs
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
# Finite measure of the working neighborhood

The general resolution-to-volume theorem
(`VolumeScaling.MonomialChartCover.hasLLCExponentsOn_cover`)
takes the finiteness of the working neighborhood's ambient measure, `μ D.U ≠ ∞`, as a hypothesis.
This file discharges it from the interface data alone, with no extra hypothesis beyond the ambient
measure being finite on compact sets.

The neighborhood `D.U` is covered, off a null set `D.N`, by the finitely many chart images
`(D.chart α).φ '' (D.chart α).K`. Each coordinate box `(D.chart α).K` is bounded
(`K_bounded`); in the proper space `Fin (D.chart α).d → ℝ` its closure is therefore compact, and
the continuous image of that compact closure under `(D.chart α).φ` is a compact set of finite
measure containing the chart image. A finite sum of finite measures, plus the null set, bounds
`μ D.U`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

namespace MonomialChartCover

variable {Ambient : Type*} [MeasurableSpace Ambient] [TopologicalSpace Ambient]
  {μ : Measure Ambient} {f : Ambient → ℝ} {w : Ambient}
  {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Each chart image has finite ambient measure: it lies in the continuous image of the compact
closure of the chart's bounded coordinate box, which is compact, hence of finite measure when the
ambient measure is finite on compact sets. -/
private theorem measure_chartImage_ne_top [IsFiniteMeasureOnCompacts μ]
    (D : MonomialChartCover Ambient μ f w ι) (α : ι) :
    μ ((D.chart α).φ '' (D.chart α).K) ≠ ∞ := by
  have hcl : IsCompact (closure (D.chart α).K) := (D.chart α).K_bounded.isCompact_closure
  have him : IsCompact ((D.chart α).φ '' closure (D.chart α).K) :=
    hcl.image (D.chart α).φ_continuous
  exact ne_top_of_le_ne_top (him.measure_ne_top (μ := μ))
    (measure_mono (Set.image_mono subset_closure))

/-- **The capstone's finite-measure side condition.** When the ambient measure is finite on
compact sets, the working neighborhood of a resolution chart family has finite measure. -/
theorem measure_U_ne_top [IsFiniteMeasureOnCompacts μ]
    (D : MonomialChartCover Ambient μ f w ι) : μ D.U ≠ ∞ := by
  have hUsub : D.U ⊆ D.N ∪ ⋃ α, (D.chart α).φ '' (D.chart α).K := by
    intro x hx
    by_cases hxN : x ∈ D.N
    · exact Or.inl hxN
    · exact Or.inr (D.cover ⟨hx, hxN⟩)
  have hsum : μ (⋃ α, (D.chart α).φ '' (D.chart α).K) ≠ ∞ := by
    refine ne_top_of_le_ne_top ?_ (measure_iUnion_le _)
    rw [tsum_fintype]
    exact (ENNReal.sum_lt_top.mpr fun α _ => (D.measure_chartImage_ne_top α).lt_top).ne
  have hle : μ D.U ≤ μ (⋃ α, (D.chart α).φ '' (D.chart α).K) :=
    calc μ D.U ≤ μ (D.N ∪ ⋃ α, (D.chart α).φ '' (D.chart α).K) := measure_mono hUsub
      _ ≤ μ D.N + μ (⋃ α, (D.chart α).φ '' (D.chart α).K) := measure_union_le _ _
      _ = μ (⋃ α, (D.chart α).φ '' (D.chart α).K) := by rw [D.N_null, zero_add]
  exact ne_top_of_le_ne_top hsum hle

end MonomialChartCover

end SingularLearningTheory
