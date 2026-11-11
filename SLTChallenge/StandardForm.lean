/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Tactic.NormNum
public import SLTChallenge.Resolution
public import SLTChallenge.EmpiricalProcess
public import Mathlib.Probability.Independence.Basic
public import SLTChallenge.Setting

/-!
# The standard form of the log likelihood ratio

[Wat09, §6.1]: fundamental condition I, the resolved form of the log density ratio on the
pieces of a chart family of a resolution ([Wat09, Theorem 6.1]), and the convergence of the
resulting empirical process ([Wat09, Theorem 6.2]). Together these give [Wat09, Main Theorem 6.1],
the standard form `K_n(g(u)) = u^{2k} − n^{-1/2} u^k ξ_n(u)`. The free energy formula is in
`SLTChallenge/FreeEnergy.lean`.
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

/-! ### Consequences of the standing assumptions

The standing assumptions give what singular learning theory usually assumes of the reference
parameter and the excess loss. The reference parameter `w₀` minimises `K` on `W`, and the average
log loss `L` when `log p(·|w₀)` is integrable. Every other minimiser of `K` in `W` has the same
model up to a `q`-null set, so it gives the same `K` and satisfies the standing assumptions too:
nothing depends on which minimiser is the reference parameter, and relatively finite variance
holds at every minimiser, as the book requires. Finally `K` is real analytic on an open
neighbourhood of `W`. -/

/-- The reference parameter minimises the excess loss on `W`: `K(w₀) = 0 ≤ K(w)` for every
`w ∈ W`, by relatively finite variance. -/
theorem StandingAssumptions.isMinOn_excessLoss {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    {W : Set (Fin d → ℝ)} {w₀ : Fin d → ℝ} (h : StandingAssumptions s q p W w₀) :
    excessLoss q p w₀ w₀ = 0 ∧ IsMinOn (excessLoss q p w₀) W w₀ :=
  sorry

/-- When `log p(·|w₀)` is `q`-integrable, the reference parameter minimises the average log loss
`L(w) = −E_q[log p(X|w)]` on `W`. Relatively finite variance makes every `log p(·|w)` with
`w ∈ W` integrable, so that `K = L − L(w₀)` on `W`. -/
theorem StandingAssumptions.isMinOn_expectedNegativeLogLikelihood {d : ℕ} {X : Type*}
    [MeasurableSpace X] {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} [IsProbabilityMeasure q]
    {p : (Fin d → ℝ) → X → ℝ} {W : Set (Fin d → ℝ)} {w₀ : Fin d → ℝ}
    (h : StandingAssumptions s q p W w₀) (hL : Integrable (fun x ↦ log (p w₀ x)) q) :
    IsMinOn (expectedNegativeLogLikelihood q p) W w₀ :=
  sorry

/-- Essential uniqueness ([Wat18, Definition 6 and Lemma 3]): every minimiser `w₀'` of the excess
loss in `W` has the same model as the reference parameter, `p(·|w₀') = p(·|w₀)` for `q`-almost
every `x`. -/
theorem StandingAssumptions.ae_eq_of_excessLoss_eq_zero {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    {W : Set (Fin d → ℝ)} {w₀ w₀' : Fin d → ℝ} (h : StandingAssumptions s q p W w₀)
    (hw₀' : w₀' ∈ W) (hK : excessLoss q p w₀ w₀' = 0) :
    p w₀' =ᵐ[q] p w₀ :=
  sorry

/-- The standing assumptions do not depend on which minimiser is the reference parameter: another
minimiser `w₀'` of the excess loss in `W` gives the same excess loss and satisfies the standing
assumptions itself. The book observes after [Wat18, Lemma 3] that `f(x, w₀, w)` does not depend
on `w₀`. -/
theorem StandingAssumptions.of_excessLoss_eq_zero {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    {W : Set (Fin d → ℝ)} {w₀ w₀' : Fin d → ℝ} (h : StandingAssumptions s q p W w₀)
    (hw₀' : w₀' ∈ W) (hK : excessLoss q p w₀ w₀' = 0) :
    excessLoss q p w₀' = excessLoss q p w₀ ∧ StandingAssumptions s q p W w₀' :=
  sorry

/-- The excess loss is real analytic on an open neighbourhood of `W`, by fundamental condition I:
`K = ∫ f(x, ·) q(dx)` composes the `L^s(q)`-valued analytic map `w ↦ f(·, w)` with integration
against `q`. -/
theorem StandingAssumptions.analyticOnNhd_excessLoss {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} [IsProbabilityMeasure q]
    {p : (Fin d → ℝ) → X → ℝ} {W : Set (Fin d → ℝ)} {w₀ : Fin d → ℝ}
    (h : StandingAssumptions s q p W w₀) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ W ⊆ U ∧ AnalyticOnNhd ℝ (excessLoss q p w₀) U :=
  sorry

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

/-- **Resolved form of the log density ratio** for a given resolution `R` and chart family `F`: the
log density ratio has resolved coefficients on every piece. The continuity of `f(x, ·)` on `W` for
q-a.e. `x` lets the coefficients be chosen continuous in `u`. `W` is closed, so that the closed cube
of every piece lies over `W`, where `f` is analytic: the closed admissible orthants lie over
`closure (interior W)`, and a chart of `F` may be centred over a boundary point of a non-closed `W`
at which `f(x, ·)` is unconstrained.

Relation to the source.
* **Strengthening.** Stated for every chart family of every resolution of $K$ and every index $s$,
  and $w_0$ need not lie in $W$.
* **Strengthening.** The factorisation holds for $q$-almost every $x$ simultaneously for every $u$,
  and $a(x, \cdot)$ is continuous on the cube for every $x$; the book's eq. (6.5) is an identity in
  $L^s(q)$ at each $u$.
* **Gap.** $W$ is assumed closed, and $f(x, \cdot)$ continuous on $W$ for $q$-almost every $x$.

Source statement: [Wat09, Theorem 6.1] -/
theorem exists_resolvedLogDensityRatio {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model and parameter space
    (p : (Fin d → ℝ) → X → ℝ)
    (W : Set (Fin d → ℝ)) (hWc : IsClosed W) (φ : (Fin d → ℝ) → ℝ)
    -- the index of fundamental condition I
    (s : ℝ≥0∞) [Fact (1 ≤ s)]
    -- `w₀` need not minimise `L`: RFV already gives `K ≥ 0` on `W`, even if `w₀ ∉ W`.
    -- A piece of `F` sits over a zero `w₀'` of `K` in `W`, and RFV then gives
    -- `p(x|w₀) = p(x|w₀')` for q-a.e. `x`.
    (w₀ : Fin d → ℝ)
    (I : FundamentalConditionI s q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (hRFV : RelativelyFiniteVariance q p w₀ W)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W)
    (R : SLTResolution (excessLoss q p w₀) φ W) (F : R.ChartFamily) :
    Nonempty (ResolvedLogDensityRatio s F q (logDensityRatio p w₀)) :=
  sorry

/-- **Limit of the resolved empirical process** for the resolved coefficients: their centred
empirical process `Ψ_n(u) = n^{-1/2} Σ (a(X_i, u) − E a(X, u))` on the pieces converges in law to a
Gaussian process `Ψ`, for every index `s ≥ 2`. The free energy statements use `ξ = −Ψ`.

Relation to the source.
* **Correction.** The standard form [Wat09, eq. (6.10)] and the empirical process [Wat09, eq.
  (6.11)] as printed have opposite signs: together they give $K_n(g(u)) = 2u^{2k} - K_n(g(u))$.
  [Wat09, eq. (1.18)] has the sign of (6.10). The process $\Psi_n$ here is (6.11) as printed, and
  the statements of [Wat09, §6.2–§6.4] use $\xi = -\Psi$, the sign of (6.10).
* **Unformalised.** The relative process $\psi_n$ on $\{K > \varepsilon\}$ of part (1) and the
  moments of part (2) have no statement here.

Source statement: [Wat09, Theorem 6.2(1)] -/
theorem exists_empiricalProcessLimit {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {q : Measure X} [IsProbabilityMeasure q]
    {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {f : X → (Fin d → ℝ) → ℝ} {R : SLTResolution K φ W} {F : R.ChartFamily}
    (L : ResolvedLogDensityRatio s F q f)
    {Ω : Type*} [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
    [IsProbabilityMeasure P] (hXs : IsIIDSample q Xs P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P'),
      Nonempty (EmpiricalProcessLimit q
        (fun x (v : (α : F.Piece) × cube d α.radius) ↦ L.a v.1 x v.2)
        Xs P P') :=
  sorry

end ResolvedLogDensityRatio

/-- `1 ≤ 4` in `ℝ≥0∞`, for fundamental condition I with index `s = 4`. -/
instance fact_one_le_four_ennreal : Fact ((1 : ℝ≥0∞) ≤ 4) := ⟨by norm_num⟩

/-- `1 ≤ 6` in `ℝ≥0∞`, for fundamental condition I with index `s = 6`. -/
instance fact_one_le_six_ennreal : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

end SingularLearningTheory
