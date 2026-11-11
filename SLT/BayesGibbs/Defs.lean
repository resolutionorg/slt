/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.Defs

/-!
# Bayes and Gibbs estimation under relatively finite variance: definitions

[Wat09, §6.3] (Theorems 6.8–6.10 and Main Theorem 6.3) under RFV in place of
realisability, for every inverse temperature `β > 0`, with fundamental conditions (I) and (II)
at `s = 6` and without the envelope conditions (1-c) and (2) of the book's condition (I).

The four errors `B_g, B_t, G_g, G_t` and the functional variance `V` are defined with the log
density ratio relative to `p(·|w₀)` instead of `q`; they agree with the book's when
`p(·|w₀) = q`.

The definitions are those of `SLTChallenge/BayesGibbs.lean`, word for word, and
`SLT/BayesGibbs.lean` proves its theorems.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

section Definitions

variable {d : ℕ} {X Ω : Type*} [MeasurableSpace X]

/-- The tempered posterior `exp(−nβK_n(w)) φ(w) dw / Z_n⁰` on `W` ([Wat09, §6.3.1]), with
`Z_n⁰` the normalised evidence `normalizedEvidence`.

Relation to the source.
* **Translation.** `posteriorMeasure p w₀ W φ β Xs n ω` is the a posteriori distribution of [Wat09,
  §6.3.1] at inverse temperature $\beta$, written with $K_n$ measured from $w_0$; the factor it
  differs by from the book's normalisation is constant in $w$ and cancels. -/
noncomputable def posteriorMeasure (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ) (β : ℝ)
    (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : Measure (Fin d → ℝ) :=
  (ENNReal.ofReal (normalizedEvidence p w₀ W φ β Xs n ω))⁻¹ •
    (priorMeasure φ W).withDensity
      (fun w ↦ ENNReal.ofReal (Real.exp (-(n * β * empiricalExcessLoss p w₀ Xs n ω w))))

/-- The Bayes generalisation error `B_g = −E_q[log E_w[exp(−f(X, w))]]` ([Wat09, Definition 6.5]),
with `E_w` the posterior expectation and `f` relative to `p(·|w₀)`.

Relation to the source.
* **Translation.** `bayesGeneralizationError`, `bayesTrainingError`, `gibbsGeneralizationError` and
  `gibbsTrainingError` are $B_g, B_t, G_g, G_t$ of [Wat09, Definition 6.5], relative to the best
  model $p(\cdot \mid w_0)$; when $q = p(\cdot \mid w_0)$ they are the book's. -/
noncomputable def bayesGeneralizationError (q : Measure X)
    (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ) (W : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) → ℝ) (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  -∫ x, Real.log (∫ w, Real.exp (-logDensityRatio p w₀ x w)
    ∂posteriorMeasure p w₀ W φ β Xs n ω) ∂q

/-- The Bayes training error `B_t = −(1/n) Σᵢ log E_w[exp(−f(Xᵢ, w))]` ([Wat09, Definition 6.5]),
with `f` relative to `p(·|w₀)`. -/
noncomputable def bayesTrainingError (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ) (β : ℝ)
    (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  -(∑ i ∈ Finset.range n, Real.log (∫ w, Real.exp (-logDensityRatio p w₀ (Xs i ω) w)
    ∂posteriorMeasure p w₀ W φ β Xs n ω)) / n

/-- The Gibbs generalisation error `G_g = E_w[K(w)]` ([Wat09, Definition 6.5]). -/
noncomputable def gibbsGeneralizationError (q : Measure X)
    (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ) (W : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) → ℝ) (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w, excessLoss q p w₀ w ∂posteriorMeasure p w₀ W φ β Xs n ω

/-- The Gibbs training error `G_t = E_w[K_n(w)]` ([Wat09, Definition 6.5]). -/
noncomputable def gibbsTrainingError (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ) (β : ℝ)
    (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w, empiricalExcessLoss p w₀ Xs n ω w ∂posteriorMeasure p w₀ W φ β Xs n ω

/-- The functional variance `V = Σᵢ (E_w[f(Xᵢ, w)²] − E_w[f(Xᵢ, w)]²)` ([Wat09, Definition 6.6]).

Relation to the source.
* **Translation.** `functionalVariance p w₀ W φ β Xs n ω` is the $V$ of [Wat09, Definition 6.6, eq.
  (6.24)], with $f$ measured from $w_0$. -/
noncomputable def functionalVariance (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ) (β : ℝ)
    (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  let ρ := posteriorMeasure p w₀ W φ β Xs n ω
  ∑ i ∈ Finset.range n,
    ((∫ w, (logDensityRatio p w₀ (Xs i ω) w) ^ 2 ∂ρ) -
      (∫ w, logDensityRatio p w₀ (Xs i ω) w ∂ρ) ^ 2)

end Definitions

end SingularLearningTheory
