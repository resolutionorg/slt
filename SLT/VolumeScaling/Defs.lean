/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

/-!
# Localized sublevel volumes and their scaling exponents

The volume-scaling pair `(λ, θ)` of a loss `f` on a region `K` for a measure `μ` is defined by
the asymptotic scaling of localized sublevel-set volumes:

  `μ (K ∩ {f ≤ ε}) ~ c · ε^λ · (−log ε)^(θ−1)`  as `ε → 0⁺`.

For Lebesgue measure this is the local learning coefficient `λ` and its multiplicity `θ` of
[singular learning theory][Wat09] (`λ` a positive rational and `θ` a natural number, as in the
free-energy expansion of [AW05]). The measure is arbitrary, so the density-weighted
volume `V_{F,ρ}(ε) = ∫_{{F ≤ ε} ∩ K} ρ` is the instance `μ = volume.withDensity ρ`.

* `sublevelVol μ K f ε` — the localized sublevel volume `μ (K ∩ {f ≤ ε})`, as a real number;
* `llcScale λ θ ε` — the model scale `ε^λ (−log ε)^(θ−1)`;
* `HasLLCExponentsOn μ K f λ θ` — the exponent-level two-sided-bound form of the scaling
  (`sublevelVol μ K f =Θ[𝓝[>] 0] llcScale λ θ`), which is what sandwich arguments produce and use.
  The relation determines `(λ, θ)` (`HasLLCExponentsOn.unique`).
* `HasLLCExponentsAt μ f w λ θ` — the same relation at a point `w` of a metric space: it holds on
  the closed ball `Metric.closedBall w r` for every small enough radius `r > 0` (eventually along
  `𝓝[>] 0`), with exponents independent of `r`.
-/

@[expose] public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f : α → ℝ}

/-- The localized sublevel-volume function `V(ε) = μ (K ∩ {f ≤ ε})`, as a real
number. (`toReal` junk when the measure is infinite is harmless: if the
localized sublevel measure is infinite eventually near `0⁺`, the junk zero
values make the scaling predicates with positive constant false, as they
should be.) -/
noncomputable def sublevelVol (μ : Measure α) (K : Set α) (f : α → ℝ) (ε : ℝ) : ℝ :=
  (μ (K ∩ {x | f x ≤ ε})).toReal

/-- The model scale `ε^λ · (−log ε)^(θ−1)` (real powers). Only its germ on
`𝓝[>] 0` matters; there both `rpow` bases are eventually positive, so no
guards are needed. -/
noncomputable def llcScale (lam theta : ℝ) (ε : ℝ) : ℝ :=
  ε ^ lam * (-Real.log ε) ^ (theta - 1)

/-- `f` has sublevel-volume exponents `lam`, `theta` on `K` with respect to `μ`:
two-sided bounds `c₁ · scale ≤ V ≤ c₂ · scale` (as an `IsTheta`), pinning
`(λ, θ)` without a leading constant (the constant-carrying form is `HasLLCOn`).
This is the form sandwich (chart read-off) arguments produce. -/
def HasLLCExponentsOn (μ : Measure α) (K : Set α) (f : α → ℝ) (lam theta : ℝ) : Prop :=
  (sublevelVol μ K f) =Θ[𝓝[>] 0] (llcScale lam theta)

/-- `f` has sublevel-volume exponents `lam`, `theta` at the point `w` with respect to `μ`:
`HasLLCExponentsOn μ (Metric.closedBall w r) f lam theta` holds for every small enough radius
`r > 0` (eventually along `𝓝[>] 0`, that is, for every `0 < r ≤ r₀` for some `r₀ > 0`). The
exponents are the same for all these radii, so the pair is an invariant of the germ of `f` at `w`.

Relation to the source.
* **Translation.** `HasLLCExponentsOn volume (Metric.closedBall w r) K λ θ` says that $\lambda$ is
  the learning coefficient and $\theta$ its multiplicity (the order $m$ of [Wat09]) for the
  sublevel volumes of $K$ in the cube of half-side $r$ about $w$, in the two-sided form
  $V(\varepsilon) \asymp \varepsilon^\lambda (-\log \varepsilon)^{\theta - 1}$;
  `HasLLCExponentsAt volume K w λ θ` is the local learning coefficient of $K$ at $w$ and its
  multiplicity. -/
def HasLLCExponentsAt [PseudoMetricSpace α] (μ : Measure α) (f : α → ℝ) (w : α)
    (lam theta : ℝ) : Prop :=
  ∀ᶠ r in 𝓝[>] (0 : ℝ), HasLLCExponentsOn μ (Metric.closedBall w r) f lam theta

end SingularLearningTheory
