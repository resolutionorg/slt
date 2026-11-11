/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Probability.Independence.Basic
public import SLTChallenge.StandardForm
public import SLTChallenge.SingularIntegrals

/-!
# The free energy formula

[Wat09, §6.2]: the evidence (partition function) and stochastic complexity (free energy), the
limit functional `Y` of [Wat09, Theorem 6.7], and the free energy formula of [Wat09] Main
Theorem 6.2 in the form of [Wat09, Corollary 6.1]. The standard form of the log likelihood ratio
that these use is in `SLTChallenge/StandardForm.lean`.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open Real (exp log)
open scoped ENNReal Manifold

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

section PartitionFunctions

variable {Ω : Type*} [MeasurableSpace Ω]

/-- [Wat09, Definition 6.2]: the evidence (partition function)
`Z_n = ∫_W ∏ p(X_i|w)^β φ(w) dw = ∫_W exp(−nβ L_n(w)) φ(w) dw`. -/
noncomputable def evidence (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ)
    (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w in W, exp (-(n * β * empiricalNegativeLogLikelihood p Xs n ω w)) * φ w

/-- [Wat09, Definition 6.2]: the stochastic complexity (free energy) `F_n = −log Z_n`. -/
noncomputable def freeEnergy (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ)
    (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  -log (evidence p W φ β Xs n ω)



end PartitionFunctions

/-! ## The limit functional `Y` -/

section LimitFunctional

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- [Wat09, Theorem 6.7]: the limit functional on the right-hand side of the theorem, as a
function `Y(χ)` of a continuous function `χ` on the pieces of a chart family `F` in place of the
limit process `ξ`. The sum runs over the essential pieces; the weight of a piece is the
partition of unity `ρ` times the unit of the prior density, so that `ρ` plays the role of the
book's partition of unity in Theorem 6.5(4).

Relation to the source.
* **Translation.** `F.limitFunctional β ρ χ` is the right-hand side of [Wat09, Theorem 6.7] at the
  field $\chi$; the partition of unity `ρ` times the unit of the prior density is the book's
  $\varphi^*_0$. -/
noncomputable def SLTResolution.ChartFamily.limitFunctional (β : ℝ) {R : SLTResolution K φ W}
    (F : R.ChartFamily)
    (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (χ : C((α : F.Piece) × cube d α.radius, ℝ)) : ℝ :=
  ∑ᶠ (α : F.Piece) (_ : α.IsEssential),
    let k := α.k
    let h := α.h
    let hk := (F.chart α.chart).active
    let I := criticalCoords k h hk
    let Face := Icc (0 : {j // j ∉ I} → ℝ) (fun _ ↦ α.radius)
    gammaConst k h hk *
      ∫ t in Ioi (0 : ℝ), ∫ v : Face,
        let u := toCriticalFace k h hk (F.chart α.chart).radius_pos.le v
        t ^ (R.rlct - 1) * (∏ j, v.val j ^ ((h j : ℝ) - 2 * k j * R.rlct)) *
          exp (-(β * t) + β * √t * χ ⟨α, u⟩) *
          (ρ α.chart (α.point (u : Fin d → ℝ)) * α.densityUnit (u : Fin d → ℝ))
        ∂(volume.comap Subtype.val)

end LimitFunctional



/-- [Wat09, eq. (6.12)]: the normalised evidence `Z_n^0 = ∫_W exp(−nβ K_n(w)) φ(w) dw`.

Relation to the source.
* **Translation.** `normalizedEvidence p w₀ W φ β Xs n ω` is the $Z_n^0$ of [Wat09, eq. (6.12)] with
  $K_n$ measured from $w_0$; when $q = p(\cdot \mid w_0)$ it is the book's. -/
noncomputable def normalizedEvidence {Ω : Type*} (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (W : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) → ℝ) (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
    let Kn := empiricalExcessLoss p w₀ Xs n ω
  ∫ w in W, exp (-(n * β * Kn w)) * φ w

/-- **Convergence in law of the normalized evidence.** For a resolution `R`, a chart family `F` of
it and a partition of unity `ρ` subordinate to `F`, there are resolved coefficients `a` on the
pieces (`exists_resolvedLogDensityRatio`) such that, for every `β > 0` and every i.i.d. sample, the
centred empirical process of `a` has a limit `Ψ` and `n^λ (log n)^{−(m−1)} Z_n^0` converges in law
to `Y(ξ)`, where `λ` and `m` are read off `R`. Here `ξ = −Ψ`, with the sign of the standard form
(6.10). Since the left-hand side does not involve `F` or `ρ`, neither does the law of `Y(ξ)`.

Relation to the source.
* **Strengthening.** Stated for every resolution, chart family and subordinate partition of unity;
  the law of the limit does not depend on them.
* **Correction.** The printed limit lacks the factor $y^\mu$ of [Wat09, Definition 6.8] and §6.3.3;
  the limit here carries it, as $\prod_j v_j^{h_j - 2k_j\lambda}$.
* **Gap.** $f(x, \cdot)$ is assumed continuous on $W$ for $q$-almost every $x$.

Source statement: [Wat09, Theorem 6.7] -/
theorem tendstoInDistribution_normalizedEvidence {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model
    (p : (Fin d → ℝ) → X → ℝ)
    (hp : Measurable (Function.uncurry p)) (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    -- prior
    (φ : (Fin d → ℝ) → ℝ)
    -- `w₀` need not minimise `L`: RFV already gives `K ≥ 0` on `W`
    (w₀ : Fin d → ℝ) (hw₀ : w₀ ∈ W)
    (hRFV : RelativelyFiniteVariance q p w₀ W)
    -- fundamental condition I makes `K` real analytic on an open neighbourhood of `W`
    (I : FundamentalConditionI 2 q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (II : FundamentalConditionII φ W)
    -- needed in addition to fundamental condition I
    (hcont : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W)
    -- a resolution, a chart family of it and a subordinate partition of unity
    (R : SLTResolution (excessLoss q p w₀) φ W) (F : R.ChartFamily)
    (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube) :
    let lam := R.rlct
    let m := R.mult
    let U := (α : F.Piece) × cube d α.radius
    -- the existence of `L` is [Wat09, Theorem 6.1]
    ∃ L : ResolvedLogDensityRatio 2 F q (logDensityRatio p w₀),
      let a : X → U → ℝ := fun x ⟨α, u⟩ ↦ L.a α x u
      ∀ (β : ℝ) (hβ : 0 < β)
        -- iid dataset drawn from q
        (Ω : Type*) [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
        [IsProbabilityMeasure P]
        (hXs : IsIIDSample q Xs P),
        -- the limit of the empirical process
        ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P'),
        ∃ E : EmpiricalProcessLimit q a Xs P P',
          let Zn0 := normalizedEvidence p w₀ W φ β Xs
          -- the book's limit process `ξ = −Ψ`, the sign of the standard form (6.10)
          let ξ := fun ω' ↦ -E.Ψlim ω'
          TendstoInDistribution
            (fun (n : ℕ) (ω : Ω) ↦
              (n : ℝ) ^ lam / log n ^ (m - 1) * Zn0 n ω)
            atTop (fun ω' ↦ F.limitFunctional β ρ (ξ ω')) (fun _ ↦ P) P' :=
  sorry

/-- **Free energy formula.** There are `λ > 0` and `m ≥ 1` such that for every `β > 0` and every
i.i.d. sample, `F_n = nβ L_n(w₀) + λ log n − (m − 1) log log n + R_n` almost surely for `n ≥ 2`,
where `R_n` converges in law.

Relation to the source.
* **Translation.** $n\beta L_n(w_0)$ replaces the book's $n\beta S_n$; the two agree when
  $q = p(\cdot \mid w_0)$.
* **Restatement.** $(\lambda, m)$ is the singularity type, defined by volume scaling, where the book
  has the largest pole of the zeta function and its order; the two agree by
  `zetaFunction_meromorphic_continuation`.
* **Formalisation note.** The limit of $R_n$ is left existential here. The library identifies it as
  $-\log Y(\xi)$, the $F^R(\xi)$ of Main Formula II, in
  `NondegenerateResolutionAtlas.free_energy_formula` ([Wat09, Main Theorem 6.2]), stated for its
  internal resolution atlas.

Source statement: [Wat09, Corollary 6.1(1)] -/
theorem free_energy_formula {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model, parameter space and reference parameter
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 2 q p W w₀)
    -- prior
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W) :
    ∃ (lam : ℝ) (m : ℕ),
      0 < lam ∧ 1 ≤ m ∧ IsSingularityType (excessLoss q p w₀) φ W lam m ∧
      ∀ (β : ℝ) (hβ : 0 < β)
        -- iid dataset drawn from q
        (Ω : Type*) [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
        [IsProbabilityMeasure P]
        (hXs : IsIIDSample q Xs P),
        let Fn := freeEnergy p W φ β Xs
        let Ln := fun (n : ℕ) (ω : Ω) ↦ empiricalNegativeLogLikelihood p Xs n ω w₀
        ∃ Rn : ℕ → Ω → ℝ,
          (∀ (n : ℕ) (hn : 2 ≤ n), ∀ᵐ ω ∂P,
            Fn n ω = n * β * Ln n ω + lam * log n
              - ((m : ℝ) - 1) * log (log n) + Rn n ω) ∧
          ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
            (_ : IsProbabilityMeasure P') (Rlim : Ω' → ℝ),
            TendstoInDistribution Rn atTop Rlim (fun _ ↦ P) P' :=
  sorry

/-- **Free energy formula in expectation.** If fundamental condition I holds with index `s = 4`,
then, with `λ`, `m` and `R_n` as in `free_energy_formula`, for all large `n` `E[F_n] = nβ L + λ log
n − (m − 1) log log n + E[R_n]`, where `L = E[L_n(w₀)]` and `E[R_n]` converges. `hL` (`log p(·|w₀)`
is q-integrable) makes `L` finite.

Relation to the source.
* **Translation.** $n\beta L$ with $L = L(w_0)$ replaces the book's $n\beta S$; the two agree when
  $q = p(\cdot \mid w_0)$.

Source statement: [Wat09, Corollary 6.1(2)] -/
theorem free_energy_formula_expectation {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model, parameter space and reference parameter
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 4 q p W w₀)
    (hL : Integrable (fun x ↦ log (p w₀ x)) q)
    -- prior
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W) :
    let L := expectedNegativeLogLikelihood q p w₀
    ∃ (lam : ℝ) (m : ℕ),
      0 < lam ∧ 1 ≤ m ∧ IsSingularityType (excessLoss q p w₀) φ W lam m ∧
      ∀ (β : ℝ) (hβ : 0 < β)
        -- iid dataset drawn from q
        (Ω : Type*) [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
        [IsProbabilityMeasure P]
        (hXs : IsIIDSample q Xs P),
        let Fn := freeEnergy p W φ β Xs
        let Ln := fun (n : ℕ) (ω : Ω) ↦ empiricalNegativeLogLikelihood p Xs n ω w₀
        ∃ Rn : ℕ → Ω → ℝ,
          (∀ (n : ℕ) (hn : 2 ≤ n), ∀ᵐ ω ∂P,
            Fn n ω = n * β * Ln n ω + lam * log n
              - ((m : ℝ) - 1) * log (log n) + Rn n ω) ∧
          (∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
            (_ : IsProbabilityMeasure P') (Rlim : Ω' → ℝ),
            TendstoInDistribution Rn atTop Rlim (fun _ ↦ P) P') ∧
          (∀ᶠ n : ℕ in atTop,
            ∫ ω, Fn n ω ∂P = n * β * L + lam * log n
              - ((m : ℝ) - 1) * log (log n) + ∫ ω, Rn n ω ∂P) ∧
          ∃ ℓ : ℝ, Tendsto (fun n ↦ ∫ ω, Rn n ω ∂P) atTop (𝓝 ℓ) :=
  sorry

end SingularLearningTheory
