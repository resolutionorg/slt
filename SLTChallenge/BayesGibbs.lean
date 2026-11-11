/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLTChallenge.FreeEnergy

/-!
# Bayes and Gibbs estimation under relatively finite variance

[Wat09, §6.3] (Theorems 6.8–6.10 and Main Theorem 6.3) under RFV in place of
realisability, for every inverse temperature `β > 0`, with fundamental conditions (I) and (II)
at `s = 6` and without the envelope conditions (1-c) and (2) of the book's condition (I).

The four errors `B_g, B_t, G_g, G_t` and the functional variance `V` are defined with the log
density ratio relative to `p(·|w₀)` instead of `q`; they agree with the book's when
`p(·|w₀) = q`.
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

/-! ### The quartet and its limits -/

/-- **Convergence of the Bayes and Gibbs errors, under RFV.** The scaled errors `nB_g, nB_t, nG_g,
nG_t` converge jointly in law and in expectation, and `n(B_g − B_t − G_g + G_t) → 0` in probability.

Relation to the source.
* **Strengthening.** Part (1) is the joint convergence in law of the four scaled errors, where the
  book states four separate limits.
* **Gap.** The limits are not identified with the functionals $B_g^*, B_t^*, G_g^*, G_t^*$ of
  [Wat09, Definition 6.9].

Source statement: [Wat09, Theorem 6.8] -/
theorem bayes_gibbs_convergence
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 6 q p W w₀)
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W)
    (β : ℝ) (hβ : 0 < β) (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    :
    let Bg : ℕ → Ω → ℝ := bayesGeneralizationError q p w₀ W φ β Xs
    let Bt : ℕ → Ω → ℝ := bayesTrainingError p w₀ W φ β Xs
    let Gg : ℕ → Ω → ℝ := gibbsGeneralizationError q p w₀ W φ β Xs
    let Gt : ℕ → Ω → ℝ := gibbsTrainingError p w₀ W φ β Xs
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (_ : IsProbabilityMeasure P') (Bg_lim Bt_lim Gg_lim Gt_lim : Ω' → ℝ),
      -- Part (1): the scaled errors converge jointly in distribution
      TendstoInDistribution
        (fun (n : ℕ) ω ↦ ![(n : ℝ) * Bg n ω, (n : ℝ) * Bt n ω, (n : ℝ) * Gg n ω, (n : ℝ) * Gt n ω])
        atTop (fun ω' ↦ ![Bg_lim ω', Bt_lim ω', Gg_lim ω', Gt_lim ω']) (fun _ ↦ P) P' ∧
      -- Part (3): the expectations are finite and converge
      (let expectationsConverge := fun (E : ℕ → Ω → ℝ) (E_lim : Ω' → ℝ) ↦
          Integrable E_lim P' ∧ (∀ᶠ n : ℕ in atTop, Integrable (fun ω ↦ (n : ℝ) * E n ω) P) ∧
            Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * E n ω ∂P) atTop (𝓝 (∫ ω', E_lim ω' ∂P'));
        expectationsConverge Bg Bg_lim ∧ expectationsConverge Bt Bt_lim ∧
          expectationsConverge Gg Gg_lim ∧ expectationsConverge Gt Gt_lim) ∧
      -- Part (2)
      TendstoInMeasure P (fun (n : ℕ) ω ↦ (n : ℝ) * (Bg n ω - Bt n ω - Gg n ω + Gt n ω))
        atTop (fun _ ↦ 0) :=
  sorry

/-! ### Equations of state and functional variance -/

/-- **Equations of state, under RFV.** The equations of state (6.19) and (6.20), stated as
`n(E[B_g] − E[B_t] − 2β(E[G_t] − E[B_t])) → 0` and its analogue for `G_g − G_t`.

Relation to the source.
* **Restatement.** The equations are stated for the scaled expectations at finite $n$; by
  `bayes_gibbs_convergence` (3) these converge to the expectations of the limits, so the two forms
  are equivalent.

Source statement: [Wat09, Main Theorem 6.3] -/
theorem equations_of_state
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 6 q p W w₀)
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W)
    (β : ℝ) (hβ : 0 < β) (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    :
    let Bg : ℕ → Ω → ℝ := bayesGeneralizationError q p w₀ W φ β Xs
    let Bt : ℕ → Ω → ℝ := bayesTrainingError p w₀ W φ β Xs
    let Gg : ℕ → Ω → ℝ := gibbsGeneralizationError q p w₀ W φ β Xs
    let Gt : ℕ → Ω → ℝ := gibbsTrainingError p w₀ W φ β Xs
    Tendsto (fun (n : ℕ) ↦ (n : ℝ) *
      ((∫ ω, Bg n ω ∂P) - (∫ ω, Bt n ω ∂P) -
        2 * β * ((∫ ω, Gt n ω ∂P) - (∫ ω, Bt n ω ∂P))))
      atTop (𝓝 0) ∧
    Tendsto (fun (n : ℕ) ↦ (n : ℝ) *
      ((∫ ω, Gg n ω ∂P) - (∫ ω, Gt n ω ∂P) -
        2 * β * ((∫ ω, Gt n ω ∂P) - (∫ ω, Bt n ω ∂P))))
      atTop (𝓝 0) :=
  sorry

/-- **The Gibbs errors and the learning coefficient, under RFV.** `nG_g + nG_t → 2λ/β` in
probability, and `n E[G_g] + n E[G_t] → 2λ/β`.

Relation to the source.
* **Restatement.** (6.22) is stated for the limit of the scaled expectations, which by
  `bayes_gibbs_convergence` (3) is $E[G_g^*] + E[G_t^*]$.

Source statement: [Wat09, Theorem 6.9] -/
theorem gibbs_errors_learning_coefficient
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 6 q p W w₀)
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W)
    (β : ℝ) (hβ : 0 < β)
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    (lam : ℝ) (m : ℕ) (hlam : 0 < lam) (hm : 1 ≤ m)
    (htype : IsSingularityType (excessLoss q p w₀) φ W lam m) :
    let Gg : ℕ → Ω → ℝ := gibbsGeneralizationError q p w₀ W φ β Xs
    let Gt : ℕ → Ω → ℝ := gibbsTrainingError p w₀ W φ β Xs
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (n : ℝ) * (Gg n ω + Gt n ω) - 2 * lam / β)
      atTop (fun _ ↦ 0) ∧
    Tendsto (fun (n : ℕ) ↦ (∫ ω, (n : ℝ) * Gg n ω ∂P) + (∫ ω, (n : ℝ) * Gt n ω ∂P)) atTop
      (𝓝 (2 * lam / β)) :=
  sorry

/-- **The Bayes and Gibbs errors and the singular fluctuation, under RFV.** Equations (6.25)–(6.30),
with the singular fluctuation `ν` given by `E[V] → 2ν/β`. Here `ν ≥ 0`, and `ν = 0` when the log
density ratio does not fluctuate with the data near `W₀`, for example when `q` is a point mass.

Relation to the source.
* **Gap.** $\nu \ge 0$ where the book has $\nu > 0$; under relatively finite variance $\nu = 0$ is
  possible, for instance when $q$ is a point mass.
* **Gap.** $\nu$ is defined by $E[V] \to 2\nu/\beta$, not identified with the singular fluctuation
  of [Wat09, Definition 5.9], and the book's upper bound on $\nu$ is not stated.

Source statement: [Wat09, Theorem 6.10] -/
theorem bayes_gibbs_learning_coefficients
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 6 q p W w₀)
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W)
    (β : ℝ) (hβ : 0 < β) (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    (lam : ℝ) (m : ℕ) (hlam : 0 < lam) (hm : 1 ≤ m)
    (htype : IsSingularityType (excessLoss q p w₀) φ W lam m) :
    let Bg : ℕ → Ω → ℝ := bayesGeneralizationError q p w₀ W φ β Xs
    let Bt : ℕ → Ω → ℝ := bayesTrainingError p w₀ W φ β Xs
    let Gg : ℕ → Ω → ℝ := gibbsGeneralizationError q p w₀ W φ β Xs
    let Gt : ℕ → Ω → ℝ := gibbsTrainingError p w₀ W φ β Xs
    let V := functionalVariance p w₀ W φ β Xs
    ∃ ν : ℝ,
      -- (6.25)
      TendstoInMeasure P (fun (n : ℕ) ω ↦ V n ω - 2 * n * (Gt n ω - Bt n ω))
        atTop (fun _ ↦ 0) ∧
      -- (6.26)
      TendstoInMeasure P (fun (n : ℕ) ω ↦ V n ω - 2 * n * (Gg n ω - Bg n ω))
        atTop (fun _ ↦ 0) ∧
      -- the singular fluctuation, `lim E[V] = 2ν/β`
      0 ≤ ν ∧
      (∀ᶠ n : ℕ in atTop, Integrable (V n) P) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, V n ω ∂P) atTop (𝓝 (2 * ν / β)) ∧
      -- (6.27)
      Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * Bg n ω ∂P) atTop
        (𝓝 (lam / β + (1 - 1 / β) * ν)) ∧
      -- (6.28)
      Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * Bt n ω ∂P) atTop
        (𝓝 (lam / β - (1 + 1 / β) * ν)) ∧
      -- (6.29)
      Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * Gg n ω ∂P) atTop (𝓝 (lam / β + ν)) ∧
      -- (6.30)
      Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * Gt n ω ∂P) atTop (𝓝 (lam / β - ν)) :=
  sorry

end SingularLearningTheory
