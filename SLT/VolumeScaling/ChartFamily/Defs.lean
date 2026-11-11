/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Chart families with two-sided monomial bounds

The data from which the sublevel-volume exponents of a loss are read off: a finite family of
origin-centered charts on each of which the loss and the Jacobian factor are each bounded above
and below by constant multiples of a monomial, and whose images cover a neighborhood of the base
point up to a null set.

* `mon e u = ∏ᵢ |uᵢ|^{eᵢ}` — the monomial with a natural exponent vector `e`.
* `ResolutionChartData Ambient f w` — a single centered chart in `d` real coordinates that maps a
  box around the origin into the ambient space `Ambient`, sending the origin to a fixed point `w`,
  on which a fixed real function `f` (the loss) and a nonnegative Jacobian factor are each
  two-sidedly bounded by a monomial. The structure is abstract — parametrized by an arbitrary
  ambient space and loss, with its own box, parametrization, Jacobian factor, exponent vectors and
  two-sided constants in `Fin d → ℝ` coordinates — so that the charts produced by blow-ups
  instantiate it. Two-sided comparability, not exact equality, is the primitive: `f (φ u)` and
  `jacAbs u` are pinned between positive constant multiples of `mon e` and `mon h` respectively,
  on the box.
* `MonomialChartCover Ambient μ f w ι` — a finite nonempty family of such charts with the transport
  identity (`TransportsToOn`) of each chart's parametrization, an open neighborhood `U` of `w`, and
  a null set `N` off which the chart images cover `U`.

The chart form of a real-analytic function (`exists_monomialChartCover_of_analyticOnNhd`) is stated
as the existence of a `MonomialChartCover` for `|K|` at `w`, and the existence of the local learning
coefficient is read off it [Wat09].
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory
open Analytic

/-- The monomial `∏ᵢ |uᵢ|^{eᵢ}` in coordinates `u : Fin d → ℝ` with natural
exponent vector `e : Fin d → ℕ`. -/
noncomputable def mon {d : ℕ} (e : Fin d → ℕ) (u : Fin d → ℝ) : ℝ :=
  ∏ i, |u i| ^ (e i)

/-- **A single centered chart.** A chart in `d` real
coordinates whose box `K` has the origin in its interior, whose continuous
parametrization `φ` sends the origin to the fixed point `w`, and on which the
fixed loss `f` and the nonnegative Jacobian factor `jacAbs` are two-sidedly
bounded by the monomials `mon e` and `mon h` with positive constants. The
exponent vector `e` of the loss is nonzero (the active set is nonempty). -/
structure ResolutionChartData (Ambient : Type*) [TopologicalSpace Ambient]
    (f : Ambient → ℝ) (w : Ambient) where
  /-- Number of chart coordinates. -/
  d : ℕ
  /-- The chart box in coordinate space. -/
  K : Set (Fin d → ℝ)
  /-- The origin lies in the interior of the box. -/
  zero_mem_interior : (0 : Fin d → ℝ) ∈ interior K
  /-- The parametrization into ambient parameter space. -/
  φ : (Fin d → ℝ) → Ambient
  /-- The parametrization is continuous. -/
  φ_continuous : Continuous φ
  /-- The origin maps to the fixed point `w`. -/
  φ_zero : φ 0 = w
  /-- The absolute-Jacobian factor of the chart. -/
  jacAbs : (Fin d → ℝ) → ℝ
  /-- Loss exponent vector. -/
  e : Fin d → ℕ
  /-- Jacobian exponent vector. -/
  h : Fin d → ℕ
  /-- The loss exponent vector is nonzero (nonempty active set). -/
  e_ne_zero : e ≠ 0
  /-- Lower loss constant. -/
  cf : ℝ
  /-- Upper loss constant. -/
  Cf : ℝ
  cf_pos : 0 < cf
  cf_le_Cf : cf ≤ Cf
  /-- Lower Jacobian constant. -/
  cJ : ℝ
  /-- Upper Jacobian constant. -/
  CJ : ℝ
  cJ_pos : 0 < cJ
  cJ_le_CJ : cJ ≤ CJ
  /-- Two-sided monomial control of the loss on the box. -/
  loss_lb : ∀ u ∈ K, cf * mon e u ≤ f (φ u)
  loss_ub : ∀ u ∈ K, f (φ u) ≤ Cf * mon e u
  /-- Two-sided monomial control of the Jacobian factor on the box. -/
  jac_lb : ∀ u ∈ K, cJ * mon h u ≤ jacAbs u
  jac_ub : ∀ u ∈ K, jacAbs u ≤ CJ * mon h u
  /-- The chart box is bounded, hence contained in some centered cube. This is
  required by the chart-local sublevel-volume read-off: the monomial read-off is
  a bounded-box phenomenon (an unbounded box would give infinite-measure
  sublevel sets under the weighted Lebesgue measure), so it transfers to the
  chart region only when the box sits inside a cube. The charts of a blow-up
  are compact coordinate boxes, so they satisfy this. -/
  K_bounded : Bornology.IsBounded K
  /-- The chart box is measurable. Required by the density-reweighting step of
  the chart-local read-off (replacing the product power density by the chart's
  Jacobian factor is valid on a measurable set). The charts of a blow-up are
  compact, hence closed, hence measurable boxes. -/
  K_measurable : MeasurableSet K
  /-- The loss pulled back through the chart map is measurable. Required so the
  chart-region sublevel sets are measurable when the density is reweighted from
  the product power density to the Jacobian factor. A polynomial or analytic
  loss is continuous, hence measurable. -/
  loss_measurable : Measurable fun u => f (φ u)
  /-- The Jacobian factor is measurable. Required by the density-reweighting step:
  the chart-local read-off compares the sublevel volumes under the product power
  density and under this Jacobian density, so both densities must be measurable.
  For the charts the chart form of a real-analytic function builds, the Jacobian
  factor is `|det Dψ|`, measurable because the derivative of a function is
  (`measurable_fderiv`). -/
  jacAbs_measurable : Measurable jacAbs

/-- **The chart family.** A finite nonempty family of origin-centered charts
(indexed by `ι`), all sharing the ambient space, the loss `f`, and the base point
`w`, together with: the change-of-variables transport identity of each chart
(its parametrization carries the coordinate Lebesgue measure to the ambient
measure `μ`, with the chart's nonnegative Jacobian factor as density); an open
set `U` containing `w`; a measurable null set `N`; and a cover of `U ∖ N` by the
chart images. This is exactly the data the general theorem
(`MonomialChartCover.hasLLCExponentsOn_cover`) uses, and the form in which the chart
form of a real-analytic function is stated. -/
structure MonomialChartCover (Ambient : Type*) [MeasurableSpace Ambient]
    [TopologicalSpace Ambient] (μ : Measure Ambient) (f : Ambient → ℝ)
    (w : Ambient) (ι : Type*) [Fintype ι] [Nonempty ι] where
  /-- The chart at each index. -/
  chart : ι → ResolutionChartData Ambient f w
  /-- Each chart's parametrization transports the coordinate Lebesgue measure to
  the ambient measure, weighting by the chart's nonnegative Jacobian factor. -/
  transport : ∀ α, TransportsToOn (volume : Measure (Fin (chart α).d → ℝ)) μ
    (chart α).K (chart α).φ (fun u => ENNReal.ofReal ((chart α).jacAbs u))
  /-- A neighborhood of the base point. -/
  U : Set Ambient
  U_open : IsOpen U
  w_mem_U : w ∈ U
  /-- The exceptional null set, off which the chart cover is exact. -/
  N : Set Ambient
  N_measurable : MeasurableSet N
  N_null : μ N = 0
  /-- The chart images cover the neighborhood minus the null set. -/
  cover : U \ N ⊆ ⋃ α, (chart α).φ '' (chart α).K

end SingularLearningTheory
