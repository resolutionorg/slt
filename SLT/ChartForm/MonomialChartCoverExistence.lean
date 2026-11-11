/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import SLT.VolumeScaling.ChartFamily.Defs
import SLT.ChartForm.Assembly
import SLT.ChartForm.MonomialResolution

/-!
# Existence of a chart family for an analytic function

For an analytic `K` on an open `U ⊆ ℝ^d`, vanishing at `w ∈ U` with nonzero germ, there is a
finite nonempty chart family `MonomialChartCover` for `|K|` at `w`: finitely many charts centred
over `w`, on each of which `|K|` and the Jacobian are bounded above and below by monomials, whose
images cover a neighbourhood of `w` up to a null set (the chart form of [BM88, Theorem 4.4] at one
point). The theorem, a main theorem of the library, is `exists_monomialChartCover_of_analyticOnNhd`:
the monomial resolution of `K` near `w` that Watanabe's Theorem 2.3 provides
(`exists_monomialPartialResolution_at`, `SLT/ChartForm/MonomialResolution.lean`) is turned into the
chart family by `exists_monomialChartCover_of_isMonomial` (`SLT/ChartForm/Assembly.lean`).
-/

public section

section ChartForm

open MeasureTheory SingularLearningTheory
open scoped Topology

namespace SingularLearningTheory

/-- **Chart form of a real-analytic function**: Watanabe's resolution theorem [Wat09, Theorem 2.3]
read in charts and in measure-theoretic form, the input of the sublevel-volume computations of
[singular learning theory][Wat09].

Statement. Let `K` be real-analytic on an open set `U ⊆ ℝ^d` and `w ∈ U` a zero of `K` near which
`K` is not identically zero. Then there is a finite nonempty family of centred charts for the loss
`|K|` at `w` (`MonomialChartCover (Fin d → ℝ) volume (fun x => |K x|) w ι`): each chart consists of
a bounded set in some `ℝ^{d'}` with `0` in its interior (the chart's box, not necessarily a product
of intervals), a continuous parametrization `φ` of the box with `φ 0 = w`, a nonnegative Jacobian
factor, and exponent vectors `e ≠ 0` and `h`, such that on the box `|K| ∘ φ` lies between two
positive multiples of the monomial `u ↦ ∏ |u_i|^{e_i}` and the Jacobian factor between two positive
multiples of `u ↦ ∏ |u_i|^{h_i}`; the parametrization carries Lebesgue measure weighted by the
Jacobian factor exactly onto `volume` on the image of every subset of the box (`TransportsToOn`);
and the images of the charts cover an open neighbourhood of `w` up to a set of measure zero.

Conventions. The ambient space is `ℝ^d = Fin d → ℝ` with Lebesgue measure `volume`. "Real-analytic
on `U`" is `AnalyticOnNhd ℝ K U`; "not identically zero near `w`" is `¬ ∀ᶠ x in 𝓝 w, K x = 0`.
The conclusion is local at `w` and does not mention `U`. For `d = 0` the space is a point and the
hypotheses `h0` and `hne` contradict each other, so the statement is vacuous.

Relation to the source.
* **Gap.** Watanabe's theorem [Wat09, Theorem 2.3] produces a manifold, a proper map and charts in
  which $K \circ g$ is exactly $\pm$ a monomial; this theorem is its measure-theoretic consequence,
  the input of the volume computation: continuous parametrizations with two-sided monomial bounds,
  whose constants absorb the units. A resolution with Watanabe's charts is
  `SingularLearningTheory.exists_resolution_of_isConnected`.
* **Gap.** The bounds are two-sided monomial bounds with constants, not exact units, so the evenness
  of the exponents for a nonnegative `K` has no content at this level (reparametrizing every chart
  by `u_i ↦ u_i |u_i|` doubles the loss exponents and turns the Jacobian exponents `h_i` into
  `2h_i + 1`), and the statement leaves it out. Nor does it fix the chart dimension `d'`, part of
  the data of each chart, to be `d`.

Source statement: [Wat09, Theorem 2.3] (measure-theoretic consequence, proved from Theorem 2.3
itself, `SingularLearningTheory.exists_resolution_of_isConnected`) -/
theorem exists_monomialChartCover_of_analyticOnNhd {d : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin d → ℝ} (hw : w ∈ U) (h0 : K w = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι),
      Nonempty (MonomialChartCover (Fin d → ℝ) volume (fun x ↦ |K x|) w ι) := by
  obtain ⟨N, -, hNn, R, hR⟩ := exists_monomialPartialResolution_at hU hK hw hne
  obtain ⟨ι, hfin, hne', D, -⟩ := exists_monomialChartCover_of_isMonomial hNn R hR h0
  exact ⟨ι, hfin, hne', ⟨D⟩⟩

end SingularLearningTheory

end ChartForm

end
