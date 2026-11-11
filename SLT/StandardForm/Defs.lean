/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Tactic.NormNum
public import SLT.Resolution.Defs
public import SLT.EmpiricalProcess.Defs
public import Mathlib.Probability.Independence.Basic
public import SLT.Setting

/-!
# The standard form of the log likelihood ratio: definitions

[Wat09, §6.1]: fundamental condition I, the resolved form of the log density ratio on the
pieces of a chart family of a resolution ([Wat09, Theorem 6.1]), and the convergence of the
resulting empirical process ([Wat09, Theorem 6.2]). Together these give [Wat09, Main Theorem 6.1],
the standard form `K_n(g(u)) = u^{2k} − n^{-1/2} u^k ξ_n(u)`. The free energy formula is in
`SLT/FreeEnergy.lean`.

The definitions are those of `SLTChallenge/StandardForm.lean`, word for word, and
`SLT/StandardForm.lean` proves its theorems.

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 5.2.1] | `FundamentalConditionI` |

## Fundamental condition I: items 1–2, real instead of complex analyticity

Item 2 of [Hit26]'s condition asks for a *complex* analytic `L^s(q)`-valued extension of
`f` to an open `W^(C) ⊆ ℂ^d` ([Hit26]'s codomain `ℝ` is a typo).
Here `f` is required to be a **real** analytic map `U → L^s(q; ℝ)` on a real open
neighbourhood `U ⊇ W`, in the Banach-space sense (`AnalyticOnNhd`), represented by `f`
almost everywhere at each parameter. This is what [Hit26]'s arguments use of analyticity
and is weaker than complex analyticity on a neighbourhood (which implies it), so every
theorem below assumes less than [Hit26].

**Deviation from the source.** [Hit26]'s condition has two further items, which
`FundamentalConditionI` omits: (3) the envelope `M(x) = sup_{w ∈ W^(C)} |f(x, w)|` lies in
`L^s(q)`, and (4) `∫ M(x)² Q(x) dx < ∞` for `Q(x) = sup_{K(w) ≤ ε} p(x|w)` and some `ε > 0`
(with the model densities `p(·|w)` taken with respect to a reference measure on `X`). [Hit26]
uses item 3 for the moment bounds of [Hit26, Lemma 4.2.4] and item 4 for the tail
estimate on `{K ≥ ε}`; the formalisation derives both from item 2 (the `L^s(q)` coefficient
series of the local expansions, and the `L^s(q)`-analyticity of `f/√K` near the compact
`{K ≥ δ}`), so no theorem needs them. Every theorem
therefore assumes strictly less than [Hit26]'s fundamental condition I.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

/-- [Wat09, Definition 6.1] (fundamental condition I with index `s`), for a loss `f(x, w)` with
`K(w) = ∫ f(x, w) q(dx)`. Items (1-a) and (1-b): `f` is an `L^s(q)`-valued real analytic function on
an open neighbourhood of `W`.

Relation to the source.
* **Restatement.** Items (1-a) and (1-b) ask for an open $W^{(C)} \subseteq \mathbb{C}^d$ on which
  $f$ is $L^s(q)$-valued complex analytic. The real form here is equivalent: [Wat09, Remark 6.1 (1)]
  takes the real slice of the complex clause, and [Wat09, Remark 5.5] extends a real analytic
  $L^s(q)$-valued function to a complex one near any compact subset.
* **Strengthening.** The envelope conditions (1-c) and (2) are not assumed. -/
structure FundamentalConditionI (s : ℝ≥0∞) [Fact (1 ≤ s)] (q : Measure X)
    (f : X → (Fin d → ℝ) → ℝ) (K : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) : Prop where
  two_le : 2 ≤ s
  K_eq : ∀ w, K w = ∫ x, f x w ∂q
  /-- Items (1-a) and (1-b): `f` is `L^s(q)`-valued real analytic on an open neighbourhood
  of `W`. -/
  ls_analytic : LsValuedAnalytic s q f W

end SingularLearningTheory

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open Real (exp log)
open scoped ENNReal

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

/-- The standing assumptions of the statements of [Wat09, Ch. 6] about a model `p` with parameter
set `W`, true distribution `q` and reference parameter `w₀`: relatively finite variance at `w₀`, and
fundamental condition I with index `s` for the log density ratio `f` and the excess loss `K`. The
theorems after the structure derive what is usually assumed of `w₀`: it minimises `K` on `W`, every
other minimiser has the same model, and `K` is analytic near `W`.

Relation to the source.
* **Strengthening.** Relatively finite variance at $w_0$ [Wat18, Definition 7] replaces the
  realizability that [Wat09, Chapter 6] assumes, and $w_0 \in W$ replaces $W_0 \ne \emptyset$. When
  $q = p(\cdot \mid w_0)$ the losses are the book's, and relatively finite variance then holds under
  the book's Fundamental Condition (I) (in the coordinates of [Wat09, Theorem 6.1]
  $E_q[f(X, g(u))^2] = u^{2k} E_q[a(X, u)^2] \le C K(g(u))$ near the zeros of $K$) or under the tail
  condition of [Wat18, Lemma 4].
* **Interpretation.** The true distribution is a measure $q$, which need not have a density; `pos`
  asks $p(x \mid w) > 0$ for $q$-almost every $x$, standing in for the book's assumption that $q$
  and $p(\cdot \mid w)$ have the same support.
* **Gap.** `continuousOn`, the continuity of $f(x, \cdot)$ on $W$ for $q$-almost every $x$, is not
  in the book. Fundamental Condition (I) does not give it: changing $f(\cdot, w)$ on a $q$-null set
  depending on $w$ leaves every $L^s$ class unchanged. The book takes the empirical process to be
  continuous for every sample [Wat09, Remark 5.7]. -/
structure StandingAssumptions (s : ℝ≥0∞) [Fact (1 ≤ s)] (q : Measure X)
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ) : Prop where
  /-- `p(x|w)` is jointly measurable. -/
  measurable : Measurable (Function.uncurry p)
  /-- `W` is compact. -/
  compact : IsCompact W
  /-- `p(x|w) > 0` for every `w ∈ W`, for `q`-almost every `x`; this stands in for the book's
  assumption that `q` and `p(·|w)` have the same support. -/
  pos : ∀ᵐ x ∂q, ∀ w ∈ W, 0 < p w x
  /-- The reference parameter lies in `W`. -/
  mem : w₀ ∈ W
  /-- Relatively finite variance at `w₀`. -/
  rfv : RelativelyFiniteVariance q p w₀ W
  /-- Fundamental condition I with index `s`. -/
  conditionI : FundamentalConditionI s q (logDensityRatio p w₀) (excessLoss q p w₀) W
  /-- `f(x, ·)` is continuous on `W` for `q`-almost every `x`, which fundamental condition I
  does not give. -/
  continuousOn : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W

/-! ## The resolved log density ratio -/

section ResolvedLogDensityRatio

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- The coefficients `a(x, u)` of [Wat09, Theorem 6.1] on every piece `α` of a chart family
`F` of a resolution, in the piece's orthant coordinates `u ∈ [0, r]^d`: `L^s(q)`-valued real
analytic on a neighbourhood of the cube, with `f(x, g_α(u)) = a(x, u) u^k` (eq. (6.5)) and
`∫ a(x, u) q(dx) = u^k` (eq. (6.6)). The factorisation holds for q-a.e. `x` simultaneously for
every `u`, and `a(x, ·)` is continuous on the cube for every `x`. -/
structure ResolvedLogDensityRatio (s : ℝ≥0∞) [Fact (1 ≤ s)] {R : SLTResolution K φ W}
    (F : R.ChartFamily) (q : Measure X) (f : X → (Fin d → ℝ) → ℝ) where
  -- `L^s(q)`-valued real analytic functions `a_α` on each piece, continuous in `u`
  /-- The coefficient $a_\alpha(x, u)$ of [Wat09, Theorem 6.1] on the piece $\alpha$, with
  $f(x, g_\alpha(u)) = u^{k}\,a_\alpha(x, u)$ for $q$-almost every $x$ and every $u$ in the cube of
  the piece. -/
  a : F.Piece → X → (Fin d → ℝ) → ℝ
  a_measurable : ∀ α (u : cube d α.radius), Measurable (fun x ↦ a α x u)
  a_continuous : ∀ α x, ContinuousOn (a α x) (cube d α.radius)
  ls_analytic : ∀ α, LsValuedAnalytic s q (a α) (cube d α.radius)
  -- `f(x, g_α(u)) = a_α(x, u) u^k` for q-a.e. `x`
  factor : ∀ α, ∀ᵐ x ∂q, ∀ u : cube d α.radius,
    f x (α.map u) = (∏ j, (u : Fin d → ℝ) j ^ α.k j) * a α x u
  -- `∫ a_α(x, u) q(dx) = u^k`
  mean : ∀ α (u : cube d α.radius),
    ∫ x, a α x u ∂q = ∏ j, (u : Fin d → ℝ) j ^ α.k j

end ResolvedLogDensityRatio

/-- `1 ≤ 4` in `ℝ≥0∞`, for fundamental condition I with index `s = 4`. -/
instance fact_one_le_four_ennreal : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- `1 ≤ 6` in `ℝ≥0∞`, for fundamental condition I with index `s = 6`. -/
instance fact_one_le_six_ennreal : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

end SingularLearningTheory
