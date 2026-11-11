/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Atlas

/-!
# Hypothesis: the resolved likelihood ([Wat09, Theorem 6.1], samplewise)

[Hit26, Lemma 5.2.3] ([Wat09, Theorem 6.1]) asserts, for
each chart `g_α : U_α → W` of the resolution, an `L^s(q)`-valued real analytic `a_α(x, u)` with

    f(x, g_α(u)) = u^{k_α} a_α(x, u)    and    ∫ a_α(x, u) q(dx) = u^{k_α}

for all `u ∈ U_α`. The structure `ResolvedLikelihood` records this conclusion in the form
the empirical process of the free energy chapter consumes: for `q`-almost every `x`
*simultaneously for all `u`*, with `u ↦ a_α(x, u)` continuous and `x ↦ a_α(x, ·)` measurable.

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 5.2.3], conclusion as consumed | |
| | `ResolutionAtlas.ResolvedLikelihood` |

## Where it is proved

The `L^s(q)`-valued statement is proved as a germ at the origin of a chart
(`ResolutionAtlas.resolution_of_f_germ`, `FreeEnergy/FundamentalConditions.lean`) and then at
every point of the closed cube (`FreeEnergy/LocalQuotient.lean`); the samplewise representatives
recorded here are constructed in `FreeEnergy/SamplewiseResolution.lean`
(`ResolutionAtlas.exists_resolvedLikelihood`) from the local `L^s(q)`-expansions, glued on a
common full-measure set. The construction needs the standing continuity of `u ↦ f(x, g_α(u))`
for `q`-almost every `x`, without which the factorisation cannot hold for all `u` off one null
set. In the free energy theorems `ResolvedLikelihood` appears only as a conclusion (the `a_α`
whose empirical process is the chart process).

[Hit26]'s "for all `x`" cannot hold: an `L^s(q)`-valued hypothesis says nothing on `q`-null
sets, and the samplewise factorisation needs a common null set for all `u` (the chart process
is built from one sample for every `u`), which is not implied by "for each `u`, almost every
`x`".
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)
  {X : Type*} [MeasurableSpace X]

/-- The conclusion of [Hit26, Lemma 5.2.3] ([Wat09,
Theorem 6.1]), as the empirical process consumes it: on every chart, `f(x, g_α(u)) = u^{k_α} a_α(x,
u)` for `q`-almost every `x` and all `u`, with `u ↦ a_α(x, u)` continuous, `x ↦ a_α(x, ·)`
measurable, and `E_q[a_α(·, u)] = u^{k_α}`. -/
structure ResolvedLikelihood (q : Measure X) (f : X → (Fin d → ℝ) → ℝ) where
  /-- The factor $a_\alpha(x, u)$ on the cube of chart $\alpha$, continuous in $u$ for each sample
  point $x$, with $f(x, g_\alpha(u)) = u^{k_\alpha}\,a_\alpha(x, u)$. Its empirical process is the
  chart process. -/
  a : (α : R.ι) → X → C(cube d (R.b α), ℝ)
  a_measurable : ∀ α, Measurable (a α)
  factor : ∀ α, ∀ᵐ x ∂q, ∀ u : cube d (R.b α),
    f x (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * a α x u
  mean : ∀ α (u : cube d (R.b α)), ∫ x, a α x u ∂q = ∏ j, (u : Fin d → ℝ) j ^ R.k α j

end ResolutionAtlas

end SingularLearningTheory
