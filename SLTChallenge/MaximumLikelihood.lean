/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLTChallenge.FreeEnergy

/-!
# Maximum likelihood and maximum a posteriori estimation: challenge statements

[Wat09, §6.4, Main Theorem 6.4] parts (1)–(3) and Corollary 6.4, under RFV rather than
realisability. The errors are the excess losses `excessLoss` (the book's `K`) and
`empiricalExcessLoss` (`K_n`). Estimators are measurable minimisers supplied as inputs; their
existence is not asserted. The maximum a posteriori estimator is the case `aₙ = 1`, `σ = −log φ` of
the penalised statements.

All four statements take fundamental condition I and the resolved log density ratio with index
`s = 4`. The book assumes `s ≥ 6` in Main Theorem 6.4 and Corollary 6.4, which is a stronger
assumption (`L⁶(q) ⊆ L⁴(q)`).
-/

public section

namespace SingularLearningTheory

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

/-! ### Maximum likelihood -/

/-- **Asymptotics of the maximum likelihood estimator, under RFV.** For any measurable maximum
likelihood estimator `ŵ`, the pair `(nK(ŵ), nK_n(ŵ))` converges in law to `(M, −M)`, where
`M = max_α max_{u ∈ M_α0} (max{0, ξ(u)})² / 4` at `ξ = −Ψ`, and both expectations converge.

Relation to the source.
* **Strengthening.** The index is $s = 4$ where the book has $s \ge 6$, no prior or Fundamental
  Condition (II) is assumed, and the joint limit in law is added to the book's limits in mean.
* **Gap.** $W = \overline{\operatorname{int} W}$ is assumed.

Source statement: [Wat09, Main Theorem 6.4(1)] -/
theorem maximumLikelihood_asymptotics
    {d : ℕ} {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 4 q p W w₀) (hWreg : W = closure (interior W))
    (φ : (Fin d → ℝ) → ℝ) (R : SLTResolution (excessLoss q p w₀) φ W) (F : R.ChartFamily)
    (L : ResolvedLogDensityRatio 4 F q (logDensityRatio p w₀))
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (E : EmpiricalProcessLimit q
      (fun x (v : (α : F.Piece) × cube d α.radius) ↦ L.a v.1 x v.2)
      Xs P P')
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n, Measurable (ŵ n))
    (hŵW : ∀ n, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalExcessLoss p w₀ Xs n ω (ŵ n ω) ≤ empiricalExcessLoss p w₀ Xs n ω w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * excessLoss q p w₀ (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalExcessLoss p w₀ Xs n ω (ŵ n ω)
    -- the zeros of `K` on the pieces: the book's `M_α0`, over all `α`
    let Z := {v : (α : F.Piece) × cube d α.radius |
      excessLoss q p w₀ (v.1.map v.2) = 0}
    let M := fun ω' ↦ ⨆ v : Z, (max 0 (-E.Ψlim ω' v)) ^ 2 / 4
    Integrable M P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (M ω', -M ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', M ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) :=
  sorry

/-! ### Finite and diverging penalties -/

/-- **Asymptotics of a penalized estimator with a fixed penalty, under RFV, for shifted errors.**
For penalty weights `aₙ ≥ 0` with `aₙ → a`, the pair `(nK(ŵ) − a σ(ŵ), nK_n(ŵ) + a σ(ŵ))` converges
in law to `(M, −M)`, where `M = max_α max_{u ∈ M_α0} ((max{0, ξ(u)})² / 4 − a σ(g_α(u)))` at
`ξ = −Ψ`, and both expectations converge. Here `σ` is C¹ on a neighbourhood of `W`.

Relation to the source.
* **Gap.** The limits are of the shifted errors $nK(\hat w) - a\sigma(\hat w)$ and
  $nK_n(\hat w) + a\sigma(\hat w)$. The book states limits of the unshifted errors, whose laws need
  not be determined without a condition on tied maximisers.
* **Interpretation.** The book writes the limit at a maximiser $u^*_\alpha$ in a chart; here the
  supremum is over the zeros of $K$ on all pieces.
* **Strengthening.** $\sigma$ is $C^1$ rather than $C^2$, $a_n$ need not be nondecreasing, the index
  is $s = 4$ rather than $s \ge 6$, and no prior is assumed.

Source statement: [Wat09, Main Theorem 6.4(2)] -/
theorem finitePenalty_asymptotics
    {d : ℕ} {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 4 q p W w₀) (hWreg : W = closure (interior W))
    (φ : (Fin d → ℝ) → ℝ) (R : SLTResolution (excessLoss q p w₀) φ W) (F : R.ChartFamily)
    (L : ResolvedLogDensityRatio 4 F q (logDensityRatio p w₀))
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (E : EmpiricalProcessLimit q
      (fun x (v : (α : F.Piece) × cube d α.radius) ↦ L.a v.1 x v.2)
      Xs P P')
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n, Measurable (ŵ n))
    (hŵW : ∀ n, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (σ : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (hWU : W ⊆ U) (hσ : ContDiffOn ℝ 1 σ U)
    (aSeq : ℕ → ℝ) (haSeq : ∀ n, 0 ≤ aSeq n)
    (a : ℝ) (ha : Tendsto aSeq atTop (𝓝 a))
    (hmin : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W,
      n * empiricalExcessLoss p w₀ Xs n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤
        n * empiricalExcessLoss p w₀ Xs n ω w + aSeq n * σ w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * excessLoss q p w₀ (ŵ n ω) - a * σ (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalExcessLoss p w₀ Xs n ω (ŵ n ω) + a * σ (ŵ n ω)
    -- the zeros of `K` on the pieces: the book's `M_α0`, over all `α`
    let Z := {v : (α : F.Piece) × cube d α.radius |
      excessLoss q p w₀ (v.1.map v.2) = 0}
    let M := fun ω' ↦ ⨆ v : Z,
      ((max 0 (-E.Ψlim ω' v)) ^ 2 / 4 - a * σ (v.val.1.map v.val.2))
    Integrable M P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (M ω', -M ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', M ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) :=
  sorry

-- The reward is restricted to the minimizers of `σ` over all pieces; the book's `M_α00` (p. 211)
-- minimizes `σ` within the zero set `M_α0` of each chart separately.
/-- **Asymptotics of a penalized estimator with a diverging penalty, under RFV.** For penalty
weights `aₙ ≥ 0` that diverge more slowly than every positive power of `n`, the conclusion of part
(1) holds with the reward restricted to the zeros of `K` at which `σ` is smallest over all pieces.

Relation to the source.
* **Interpretation.** The book's $\mathcal{M}_{\alpha 00}$ minimises $\sigma(g(u))$ within each
  chart's zero set; here $\mathcal{Z}_{00}$ is the set of global minimisers over all pieces, which
  is what the argument for $a_n \to \infty$ supports.
* **Strengthening.** As in part (2): $\sigma$ is $C^1$, $a_n$ need not be nondecreasing, $s = 4$,
  and no prior is assumed.

Source statement: [Wat09, Main Theorem 6.4(3)] -/
theorem divergingPenalty_asymptotics
    {d : ℕ} {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 4 q p W w₀) (hWreg : W = closure (interior W))
    (φ : (Fin d → ℝ) → ℝ) (R : SLTResolution (excessLoss q p w₀) φ W) (F : R.ChartFamily)
    (L : ResolvedLogDensityRatio 4 F q (logDensityRatio p w₀))
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    (P' : Measure Ω') [IsProbabilityMeasure P']
    (E : EmpiricalProcessLimit q
      (fun x (v : (α : F.Piece) × cube d α.radius) ↦ L.a v.1 x v.2)
      Xs P P')
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n, Measurable (ŵ n))
    (hŵW : ∀ n, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (σ : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ)) (hU : IsOpen U)
    (hWU : W ⊆ U) (hσ : ContDiffOn ℝ 1 σ U)
    (aSeq : ℕ → ℝ) (haSeq : ∀ n, 0 ≤ aSeq n)
    (ha : Tendsto aSeq atTop atTop)
    (hslow : ∀ r : ℝ, 0 < r →
      Tendsto (fun (n : ℕ) ↦ aSeq n / (n : ℝ) ^ r) atTop (𝓝 0))
    (hmin : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W,
      n * empiricalExcessLoss p w₀ Xs n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤
        n * empiricalExcessLoss p w₀ Xs n ω w + aSeq n * σ w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * excessLoss q p w₀ (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalExcessLoss p w₀ Xs n ω (ŵ n ω)
    -- the zeros of `K` on the pieces: the book's `M_α0`, over all `α`
    let Z := {v : (α : F.Piece) × cube d α.radius |
      excessLoss q p w₀ (v.1.map v.2) = 0}
    -- the zeros minimising the penalty, over all pieces (the book's `M_α00`; see below)
    let Z₀₀ := {v ∈ Z | ∀ v' ∈ Z, σ (v.1.map v.2) ≤ σ (v'.1.map v'.2)}
    let M := fun ω' ↦ ⨆ v : Z₀₀, (max 0 (-E.Ψlim ω' v)) ^ 2 / 4
    Integrable M P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (M ω', -M ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', M ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) :=
  sorry

/-! ### Free energy relative to the fitted likelihood -/

/-- **Free energy centered at the maximum likelihood estimator, under RFV.** At `β = 1`,
`F_n + Σ_{i<n} log p(X_i|ŵ) − λ log n + (m − 1) log log n` converges in law and in expectation,
where `λ` and `m` are the learning coefficient and multiplicity of `K` and `φ`.

Relation to the source.
* **Strengthening.** The index is $s = 4$ where the book has $s \ge 6$, and the convergence in
  expectation is added.
* **Gap.** The limit is not identified as $-\log Z(\xi) + \frac14 M(\xi)^2$, and the maximum a
  posteriori case is not stated.
* **Correction.** Part (2) as printed has its main term with the wrong sign, and with the sign fixed
  it differs from the expectation of part (1)'s main term by
  $n(E[K(\hat w)] - E[K_n(\hat w)]) \to \frac12 E[M(\xi)^2] \ne 0$. Both conclusions here use the
  centring $-\sum_i \log p(X_i \mid \hat w)$ of part (1).

Source statement: [Wat09, Corollary 6.4] -/
theorem freeEnergy_centered_at_maximumLikelihood
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 4 q p W w₀)
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W)
    (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n, Measurable (ŵ n))
    (hŵW : ∀ n, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalExcessLoss p w₀ Xs n ω (ŵ n ω) ≤ empiricalExcessLoss p w₀ Xs n ω w) :
    ∃ (lam : ℝ) (m : ℕ), 0 < lam ∧ 1 ≤ m ∧ IsSingularityType (excessLoss q p w₀) φ W lam m ∧
      let Rn := fun (n : ℕ) ω ↦ freeEnergy p W φ 1 Xs n ω -
        n * empiricalNegativeLogLikelihood p Xs n ω (ŵ n ω) -
        lam * Real.log n + ((m : ℝ) - 1) * Real.log (Real.log n)
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P') (Rlim : Ω' → ℝ),
        Integrable Rlim P' ∧ (∀ᶠ n : ℕ in atTop, Integrable (Rn n) P) ∧
        TendstoInDistribution Rn atTop Rlim (fun _ ↦ P) P' ∧
        Tendsto (fun (n : ℕ) ↦ ∫ ω, Rn n ω ∂P) atTop (𝓝 (∫ ω', Rlim ω' ∂P')) :=
  sorry

end SingularLearningTheory
