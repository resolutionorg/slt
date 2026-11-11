/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic

/-!
# Chart coordinates, centered boxes and exact measure transport

The two notions in which the charts of a partial resolution are measured: a chart is a map out of
a box of chart coordinates, and it carries the Jacobian-weighted Lebesgue measure exactly onto the
ambient measure.

* `CoordVec d = Fin d → ℝ` is the type of chart coordinate vectors.
* `TransportsToOn μX μY K φ J` is the measure semantics of a chart map: on *every* source subset
  `s ⊆ K`, integrating a pulled-back test function against the `J`-weighted source measure equals
  integrating the test function over the image. Quantifying over arbitrary (not necessarily
  measurable) subsets is deliberate: `Measure.restrict` is defined for arbitrary restricting sets,
  and the localization makes composition a one-line test-function substitution — while images of
  measurable sets under the blow-up maps need not be Borel, so an image-measurability hypothesis
  would poison the composition lemma.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Analytic

/-- Local chart coordinates. -/
abbrev CoordVec (d : ℕ) := Fin d → ℝ

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Local exact transport: on every source subset of `K`, the map
carries the `J`-weighted measure to the target measure on the image. -/
def TransportsToOn (μX : Measure X) (μY : Measure Y) (K : Set X)
    (φ : X → Y) (J : X → ℝ≥0∞) : Prop :=
  Measurable φ ∧ Measurable J ∧
    ∀ s ⊆ K, ∀ g : Y → ℝ≥0∞, Measurable g →
      ∫⁻ x in s, g (φ x) * J x ∂μX = ∫⁻ y in φ '' s, g y ∂μY

end Analytic
