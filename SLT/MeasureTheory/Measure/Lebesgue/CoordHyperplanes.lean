/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Coordinate hyperplanes are null

The union `coordHyperplanes d` of the coordinate hyperplanes `{x : Fin d → ℝ | x i = 0}` is a
measurable set of Lebesgue measure zero. Every set on which some coordinate vanishes lies in it,
such as the zero set of a monomial or the walls of the charts of a blow-up, so this is the
measure-zero fact used to extend a change of variables across a chart's exceptional set.
-/

@[expose] public section

open MeasureTheory

/-- The union of the coordinate hyperplanes of `ℝ^d`: the points with a vanishing coordinate. -/
def coordHyperplanes (d : ℕ) : Set (Fin d → ℝ) := {v | ∃ j, v j = 0}

/-- The coordinate hyperplanes are Lebesgue null. -/
theorem volume_coordHyperplanes (d : ℕ) : volume (coordHyperplanes d) = 0 := by
  have h : coordHyperplanes d = ⋃ j, {x : Fin d → ℝ | x j = 0} := by
    ext v
    simp [coordHyperplanes]
  rw [h, measure_iUnion_null_iff, show (volume : Measure (Fin d → ℝ)) =
    Measure.pi fun _ => volume from volume_pi]
  exact fun j ↦ Measure.pi_hyperplane _ j 0

theorem measurableSet_coordHyperplanes (d : ℕ) : MeasurableSet (coordHyperplanes d) := by
  have : coordHyperplanes d = ⋃ j, (fun v : Fin d → ℝ ↦ v j) ⁻¹' {0} := by
    ext v
    simp [coordHyperplanes]
  rw [this]
  exact MeasurableSet.iUnion fun j ↦ (measurable_pi_apply j) (measurableSet_singleton 0)
