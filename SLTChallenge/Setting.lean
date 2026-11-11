/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Probability.Independence.Basic

/-!
# The setting of the challenge statements

The model is a family $p(x \mid w)$ of functions of the data, for parameters
$w \in W \subseteq \mathbb R^d$, with true distribution $q$ and a reference parameter $w_0$,
usually an optimum. Losses are measured by the log density ratio
$f(x, w) = \log(p(x \mid w_0)/p(x \mid w))$ of [Wat09, Definition 1.3], with $p(x \mid w_0)$ in
place of $q(x)$. They are the excess loss $K(w) = E_q[f(x, w)]$, its empirical counterpart $K_n$
over a sample $X_1, \dots, X_n$, and the average and empirical log losses $L$ and $L_n$
[Wat18, eq. (3.6) and (3.7)]. In place of realizability the statements assume relatively finite
variance [Wat18, Definition 7] at $w_0$: there is $C > 0$ with $C\,E_q[f(x, w)^2] \le K(w)$ on
$W$, with each $f(\cdot, w)$ in $L^2(q)$. The prior is a measure on $\mathbb R^d$ with density
$\varphi$ on $W$. Fundamental condition (II) [Wat09, Definition 6.3] asks that $W$ be
semianalytic and that $\varphi$ factor near $W$ into a positive smooth function and an analytic
function that is nonnegative on $W$. The statements assume compactness of $W$ separately.

## Main definitions

* `SingularLearningTheory.logDensityRatio`, `SingularLearningTheory.excessLoss` and
  `SingularLearningTheory.empiricalExcessLoss`: $f$, $K$ and $K_n$.
* `SingularLearningTheory.expectedNegativeLogLikelihood` and
  `SingularLearningTheory.empiricalNegativeLogLikelihood`: $L$ and $L_n$.
* `SingularLearningTheory.RelativelyFiniteVariance`: relatively finite variance at $w_0$.
* `SingularLearningTheory.IsIIDSample`: an i.i.d. sample from $q$.
* `SingularLearningTheory.priorMeasure`: the prior.
* `SingularLearningTheory.Semianalytic` and
  `SingularLearningTheory.FundamentalConditionII`: the conditions on $W$ and $\varphi$.
* `SingularLearningTheory.ZeroSetConditions`: the conditions on $K$ and $\varphi$ at
  the zeros of $K$.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory (Measure MemLp)

variable {d : ℕ} {X Ω : Type*} [MeasurableSpace X]

/-- The log density ratio `f(x, w) = log p(x|w₀)/p(x|w)` ([Wat09, Definition 1.3]). The reference
parameter `w₀` is usually an optimum.

Relation to the source.
* **Translation.** `logDensityRatio p w₀ x w` is the log density ratio $f(x, w_0, w)$ of [Wat18, eq.
  (3.3)]. When $q = p(\cdot \mid w_0)$ it is the $f(x, w)$ of [Wat09, eq. (1.1)]. -/
noncomputable def logDensityRatio (p : (Fin d → ℝ) → X → ℝ)
    (w₀ : Fin d → ℝ) (x : X) (w : Fin d → ℝ) : ℝ :=
  Real.log (p w₀ x / p w x)

/-- `K(w) = L(w) − L(w₀) = E_q[log p(X|w₀)/p(X|w)]`, the excess of `KL(q‖p(·|w))` over
`KL(q‖p(·|w₀))` ([Wat09, Definition 1.3]). Under RFV, `p(·|w₀)` is the same for every optimal `w₀`
(essential uniqueness), so `K` does not depend on that choice.

Relation to the source.
* **Translation.** `excessLoss q p w₀` is $L(w) - L(w_0)$, the excess of the Kullback–Leibler
  distance from $q$ to $p(\cdot \mid w)$ over its value at $w_0$. When $q = p(\cdot \mid w_0)$ it is
  the $K(w)$ of [Wat09, eq. (1.2)]. -/
noncomputable def excessLoss (q : Measure X)
    (p : (Fin d → ℝ) → X → ℝ) (w₀ w : Fin d → ℝ) : ℝ :=
  ∫ x, logDensityRatio p w₀ x w ∂q

/-- The empirical version `K_n(w) = (1/n) Σᵢ log p(Xᵢ|w₀)/p(Xᵢ|w)` ([Wat09, Definition 1.3]).

Relation to the source.
* **Translation.** `empiricalExcessLoss p w₀ Xs n ω` is the $K_n(w)$ of [Wat09, eq. (1.3)] for the
  first $n$ points of the sample `Xs` at `ω`, measured from $w_0$; when $q = p(\cdot \mid w_0)$ it
  is the book's. -/
noncomputable def empiricalExcessLoss (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) (w : Fin d → ℝ) : ℝ :=
  (∑ i ∈ Finset.range n, logDensityRatio p w₀ (Xs i ω) w) / n

/-- The average log loss `L(w) = −E_q[log p(X|w)]` ([Wat18, eq. (3.6)]). -/
noncomputable def expectedNegativeLogLikelihood (q : Measure X) (p : (Fin d → ℝ) → X → ℝ)
    (w : Fin d → ℝ) : ℝ :=
  -∫ x, Real.log (p w x) ∂q

/-- The empirical log loss `L_n(w) = −(1/n) Σᵢ log p(Xᵢ|w)` ([Wat18, eq. (3.7)]). -/
noncomputable def empiricalNegativeLogLikelihood (p : (Fin d → ℝ) → X → ℝ) (Xs : ℕ → Ω → X)
    (n : ℕ) (ω : Ω) (w : Fin d → ℝ) : ℝ :=
  -(∑ i ∈ Finset.range n, Real.log (p w (Xs i ω))) / n

/-- Relatively finite variance ([Wat18, Definition 7]) at the given `w₀`: there is `C > 0` with
`C E_q[f(X, w)²] ≤ K(w)` for every `w ∈ W`. Each `f(·, w)` lies in `L²(q)`.

Relation to the source.
* **Interpretation.** [Wat18, Definition 7] asks the inequality for every optimal $w_0$; here it is
  asked at the given `w₀`. Under the standing assumptions every other minimiser of $K$ in $W$ has
  the same model up to a $q$-null set and satisfies them too
  (`StandingAssumptions.of_excessLoss_eq_zero`), so the two readings agree.
* **Formalisation note.** $f(\cdot, w) \in L^2(q)$ is a separate condition because the integral of a
  non-integrable function is $0$ in Lean, which would make the inequality vacuous. -/
def RelativelyFiniteVariance (q : Measure X)
    (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) : Prop :=
  ∃ C > 0, ∀ w ∈ W,
    MemLp (fun x ↦ logDensityRatio p w₀ x w) 2 q ∧
      C * ∫ x, (logDensityRatio p w₀ x w) ^ 2 ∂q ≤ excessLoss q p w₀ w

/-- `X₀, X₁, …` is an i.i.d. sample from `q` under `P`: each `Xᵢ` has law `q` and the `Xᵢ` are
independent.

Relation to the source.
* **Translation.** `IsIIDSample q Xs P` is the book's "$X_1, X_2, \dots$ are independently subject
  to $q(x)\,dx$" [Wat09, §1.1.1], for a sequence of random variables on `(Ω, P)`. -/
structure IsIIDSample [MeasurableSpace Ω] (q : Measure X) (Xs : ℕ → Ω → X)
    (P : Measure Ω) : Prop where
  /-- Each `Xᵢ` has law `q`. -/
  measurePreserving : ∀ i, MeasureTheory.MeasurePreserving (Xs i) P q
  /-- The `Xᵢ` are independent. -/
  indep : ProbabilityTheory.iIndepFun Xs P

/-- The prior measure on the ambient parameter space, with density `φ` on `W`.
It is automatically absolutely continuous with respect to Lebesgue measure. Full support
means `(priorMeasure φ W).support = W`; it does not require `φ` to be positive at every point.

Relation to the source.
* **Translation.** `priorMeasure φ W` is the book's prior $\varphi(w)\,dw$ on $W$. -/
noncomputable def priorMeasure (φ : (Fin d → ℝ) → ℝ)
    (W : Set (Fin d → ℝ)) :
    Measure (Fin d → ℝ) :=
  (MeasureTheory.volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))

end SingularLearningTheory

/-! ## The parameter set and prior -/

namespace SingularLearningTheory

variable {d : ℕ}

/-- The condition on `W` in [Wat09, Definition 6.3]: inside an open neighbourhood `U` of
`W`, `W` is cut out by finitely many inequalities `H_i ≥ 0` with each `H_i` real analytic on
`U`. -/
def Semianalytic (W : Set (Fin d → ℝ)) : Prop :=
  ∃ (U : Set (Fin d → ℝ)) (N : ℕ) (H : Fin N → (Fin d → ℝ) → ℝ),
    IsOpen U ∧ W ⊆ U ∧ (∀ i, AnalyticOnNhd ℝ (H i) U) ∧ ∀ w ∈ U, (w ∈ W ↔ ∀ i, 0 ≤ H i w)

/-- [Wat09, Definition 6.3] (fundamental condition (II)), without the compactness of
`W`, which the theorems assume separately: `W` is semianalytic, and on an open neighbourhood
of `W` the prior factors as `φ = φ₁ φ₂` with `φ₁ > 0` smooth and `φ₂` real analytic and
nonnegative on `W`.

Relation to the source.
* **Strengthening.** $\varphi_2$ need only be nonnegative on $W$, not on the neighbourhood, so
  priors that are negative off $W$, such as the Dirichlet priors of [Wat09, §7.3], are admitted. -/
structure FundamentalConditionII (φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) : Prop where
  semianalytic : Semianalytic W
  -- prior factors into positive smooth function and non-negative analytic function
  factor : ∃ U : Set (Fin d → ℝ), IsOpen U ∧ W ⊆ U ∧ ∃ φ₁ φ₂ : (Fin d → ℝ) → ℝ,
    (∀ w ∈ U, 0 < φ₁ w) ∧ ContDiffOn ℝ (⊤ : ℕ∞) φ₁ U ∧ (∀ w ∈ W, 0 ≤ φ₂ w) ∧
      AnalyticOnNhd ℝ φ₂ U ∧
      ∀ w ∈ U, φ w = φ₁ w * φ₂ w

end SingularLearningTheory

namespace SingularLearningTheory

variable {d : ℕ}

open Filter Topology in
/-- The conditions at the zeros of `K` in `W`: neither `K` nor `φ` vanishes identically near any
zero of `K` in `W`, and every sublevel set `{K < ε}` has positive prior mass.

Relation to the source.
* **Correction.** `loss_germ` and `prior_germ` are the non-constancy hypotheses of resolution of
  singularities ([Wat09, Theorems 2.3 and 2.8] resolve functions that are not constant), which
  [Wat09, Chapter 6] applies to $K$ and to the prior without stating them: a loss vanishing on an
  open set has no normal crossing form $u^{2k}$ with $k \ne 0$ there, and its $(\lambda, m)$ are not
  defined.
* **Interpretation.** `sublevel_mass` is the book's assumption that
  $\{w \in \operatorname{supp} \varphi : K(w) = 0\}$ is not empty [Wat09, Theorem 7.1], read for the
  measure $\varphi\,dw$ on $W$. -/
structure ZeroSetConditions (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) : Prop where
  /-- `K` is not identically zero near any of its zeros in `W`. -/
  loss_germ : ∀ w ∈ W, K w = 0 → ¬ K =ᶠ[𝓝 w] 0
  /-- `φ` is not identically zero near any zero of `K` in `W`. -/
  prior_germ : ∀ w ∈ W, K w = 0 → ¬ φ =ᶠ[𝓝 w] 0
  /-- Every sublevel set `{K < ε}` of `W` has positive prior mass. -/
  sublevel_mass : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)

end SingularLearningTheory
