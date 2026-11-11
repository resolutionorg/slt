/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy
public import SLT.MaximumLikelihood.Assembly
public import SLT.MaximumLikelihood.FinitePenalty.Assembly
public import SLT.MaximumLikelihood.DivergingPenalty.Assembly
public import SLT.MaximumLikelihood.CenteredFreeEnergy
public import SLT.Resolution.PieceAtlas
public import SLT.MaximumLikelihood.Penalty.Functionals

/-!
# Maximum likelihood and maximum a posteriori estimation

The theorems of `SLTChallenge/MaximumLikelihood.lean` ([Wat09, §6.4]), proved from
`SLT/MaximumLikelihood/`. The library's theorems are stated for a resolution
atlas covering a sublevel of `K`; here they are applied to the prior-free atlas of the pieces of
the chart family (`ChartFamily.toZeroAtlas`), which covers a sublevel because `W` is regular
(`ChartFamily.exists_piece_map_eq`), and the inline limits `⨆ v : Z, …` are the library's suprema
over the images of the resolved zero sets.
-/

public section

-- These statements mirror SLTChallenge word for word, so they keep hypotheses of the book
-- that the delegated proofs here don't need.
set_option linter.unusedVariables false

namespace SingularLearningTheory

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

section PieceBridges

open SingularLearningTheory.SLTResolution SingularLearningTheory.SLTResolution.ChartFamily

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {R : SLTResolution K φ W}
  {F : R.ChartFamily}

/-- Over a regular compact `W`, the prior-free atlas of the pieces covers a sublevel of `K`. -/
private theorem zeroAtlas_cover (hW : IsCompact W) (hWreg : W = closure (interior W))
    [Nonempty F.Piece] :
    ∃ δ > 0, ∀ w ∈ W, K w < δ → ∃ α, ∃ u : cube d
      ((F.toZeroAtlas hW.isClosed).b α), (F.toZeroAtlas hW.isClosed).g α u = w := by
  refine ⟨F.δ, F.δ_pos, fun w hw hK ↦ ?_⟩
  obtain ⟨α, u, hu, rfl⟩ := F.exists_piece_map_eq hW hWreg hw hK.le
  exact ⟨α, ⟨u, hu⟩, α.extMap_eq (α.cube_subset_domain hu)⟩

/-- On the cube of a piece, the chart penalty of the prior-free atlas is the penalty at the
piece map. -/
private theorem chartPenalty_zeroAtlas (hWc : IsClosed W) [Nonempty F.Piece]
    (σ : (Fin d → ℝ) → ℝ) (u : ResolutionAtlas.Domain (F.toZeroAtlas hWc)) :
    ResolutionAtlas.chartPenalty (F.toZeroAtlas hWc) σ u
      = σ (u.1.map u.2) := by
  change σ (u.1.extMap u.2) = σ (u.1.map u.2)
  rw [u.1.extMap_eq (u.1.cube_subset_domain u.2.2)]

/-- The library's resolved zero set of the atlas of the pieces is the set of zeros of `K` on the
pieces. -/
private theorem resolvedZeroSet_zeroAtlas (hWc : IsClosed W) [Nonempty F.Piece] :
    ResolutionAtlas.resolvedZeroSet (F.toZeroAtlas hWc)
      = {v : (α : F.Piece) × cube d α.radius | K (v.1.map v.2) = 0} := by
  ext v
  constructor
  · intro hv
    change K (v.1.map v.2) = 0
    rw [v.1.loss_map v.2.2]
    exact hv
  · intro hv
    change ∏ j, (v.2 : Fin d → ℝ) j ^ (2 * v.1.k j) = 0
    rw [← v.1.loss_map v.2.2]
    exact hv

/-- The library's resolved penalty minimisers of the atlas of the pieces are the penalty minimisers
among the zeros of `K` on the pieces. -/
private theorem resolvedPenaltyMinimizers_zeroAtlas (hWc : IsClosed W) [Nonempty F.Piece]
    (σ : (Fin d → ℝ) → ℝ) :
    ResolutionAtlas.resolvedPenaltyMinimizers (F.toZeroAtlas hWc) σ
      = {v ∈ {v : (α : F.Piece) × cube d α.radius | K (v.1.map v.2) = 0} |
          ∀ v' ∈ {v : (α : F.Piece) × cube d α.radius | K (v.1.map v.2) = 0},
            σ (v.1.map v.2) ≤ σ (v'.1.map v'.2)} := by
  have hZ := resolvedZeroSet_zeroAtlas (F := F) hWc
  ext v
  constructor
  · rintro ⟨hvS, hmin⟩
    refine ⟨hZ ▸ hvS, fun v' hv' ↦ ?_⟩
    exact ((chartPenalty_zeroAtlas hWc σ v).symm.trans_le (hmin v' (hZ ▸ hv'))).trans_eq
      (chartPenalty_zeroAtlas hWc σ v')
  · rintro ⟨hvZ, hmin⟩
    refine ⟨hZ ▸ hvZ, fun v' hv'S ↦ ?_⟩
    exact ((chartPenalty_zeroAtlas hWc σ v).trans_le (hmin _ (hZ ▸ hv'S))).trans_eq
      (chartPenalty_zeroAtlas hWc σ v').symm

/-- A supremum over a set `Z` of points of the pieces' cubes, read as the supremum of an image. -/
private theorem iSup_eq_sSup_image {Z S : Set ((α : F.Piece) × cube d α.radius)} (hS : S = Z)
    (G : ((α : F.Piece) × cube d α.radius) → ℝ) :
    ⨆ v : Z, G v = sSup (G '' S) := by
  rw [hS, sSup_image']

end PieceBridges


/-- **Asymptotics of the maximum likelihood estimator, under RFV.** For any measurable maximum
likelihood estimator `ŵ`, the pair `(nK(ŵ), nK_n(ŵ))` converges in law to `(M, −M)`, where
`M = max_α max_{u ∈ M_α0} (max{0, ξ(u)})² / 4` at `ξ = −Ψ`, and both expectations converge.

Relation to the source.
* **Strengthening.** The index is $s = 4$ where the book has $s \ge 6$, no prior or Fundamental
  Condition (II) is assumed, and the joint limit in law is added to the book's limits in mean.
* **Gap.** $W = \overline{\operatorname{int} W}$ is assumed.

Source statement: [Wat09, Main Theorem 6.4(1)] -/
-- `hp_pos` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
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
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hK0 := hRFV.excessLoss_nonneg
  have : Nonempty F.Piece := by
    obtain ⟨α, -⟩ := F.exists_piece_map_eq hW hWreg hw₀ (by rw [excessLoss_self]; exact F.δ_pos.le)
    exact ⟨α⟩
  have : ∀ α : F.Piece, CompactSpace (cube d α.radius) := fun α ↦
    isCompact_iff_compactSpace.mp isCompact_Icc
  set A₀ := F.toZeroAtlas hW.isClosed
  let Lk := L.toAnalyticResolvedLikelihood A₀ id (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun α u hu ↦ α.extMap_eq (α.cube_subset_domain hu)) I.two_le
  let Ek : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (u : ResolutionAtlas.Domain A₀) ↦ Lk.a u.1 x u.2) Xs P P' :=
    E
  have h := SingularLearningTheory.MaximumLikelihood.maximumLikelihood_asymptotics A₀ I Lk
    (measurable_uncurry_logDensityRatio hp w₀) hW hK0 hcont hw₀ (excessLoss_self q p w₀)
    (zeroAtlas_cover hW hWreg) hX hIndep Ek ŵ hŵ hŵW hmin
  have hM : ∀ ω', (⨆ v : {v : (α : F.Piece) × cube d α.radius |
      excessLoss q p w₀ (v.1.map v.2) = 0}, (max 0 (-E.Ψlim ω' v)) ^ 2 / 4)
      = ResolutionAtlas.likelihoodRewardSup A₀ (ResolutionAtlas.resolvedZeroSet A₀)
        (Ek.Ψlim ω') := fun ω' ↦ by
    rw [iSup_eq_sSup_image (resolvedZeroSet_zeroAtlas hW.isClosed)
      (fun v ↦ (max 0 (-E.Ψlim ω' v)) ^ 2 / 4)]
    rfl
  dsimp only at h ⊢
  simp only [hM]
  exact h

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
-- `hp_pos` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
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
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hK0 := hRFV.excessLoss_nonneg
  have : Nonempty F.Piece := by
    obtain ⟨α, -⟩ := F.exists_piece_map_eq hW hWreg hw₀ (by rw [excessLoss_self]; exact F.δ_pos.le)
    exact ⟨α⟩
  have : ∀ α : F.Piece, CompactSpace (cube d α.radius) := fun α ↦
    isCompact_iff_compactSpace.mp isCompact_Icc
  set A₀ := F.toZeroAtlas hW.isClosed
  let Lk := L.toAnalyticResolvedLikelihood A₀ id (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun α u hu ↦ α.extMap_eq (α.cube_subset_domain hu)) I.two_le
  let Ek : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (u : ResolutionAtlas.Domain A₀) ↦ Lk.a u.1 x u.2) Xs P P' :=
    E
  have h := SingularLearningTheory.MaximumLikelihood.finitePenalty_asymptotics A₀ I Lk
    (measurable_uncurry_logDensityRatio hp w₀) hW hK0 hcont hw₀ (excessLoss_self q p w₀)
    (zeroAtlas_cover hW hWreg) hX hIndep Ek ŵ hŵ hŵW σ U hU hWU hσ aSeq haSeq a ha
    hmin
  have hM : ∀ ω', (⨆ v : {v : (α : F.Piece) × cube d α.radius |
      excessLoss q p w₀ (v.1.map v.2) = 0},
      ((max 0 (-E.Ψlim ω' v)) ^ 2 / 4 - a * σ (v.val.1.map v.val.2)))
      = ResolutionAtlas.penalizedLikelihoodRewardSup A₀ σ a (Ek.Ψlim ω') := fun ω' ↦ by
    rw [iSup_eq_sSup_image (resolvedZeroSet_zeroAtlas hW.isClosed)
      (fun v ↦ (max 0 (-E.Ψlim ω' v)) ^ 2 / 4 - a * σ (v.1.map v.2))]
    unfold ResolutionAtlas.penalizedLikelihoodRewardSup ResolutionAtlas.penalizedMax
    congr 1
    refine Set.image_congr fun u _ ↦ ?_
    have e := chartPenalty_zeroAtlas (F := F) hW.isClosed σ u
    rw [← e]
    rfl
  dsimp only at h ⊢
  simp only [hM]
  exact h

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
-- `hp_pos` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
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
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hK0 := hRFV.excessLoss_nonneg
  have : Nonempty F.Piece := by
    obtain ⟨α, -⟩ := F.exists_piece_map_eq hW hWreg hw₀ (by rw [excessLoss_self]; exact F.δ_pos.le)
    exact ⟨α⟩
  have : ∀ α : F.Piece, CompactSpace (cube d α.radius) := fun α ↦
    isCompact_iff_compactSpace.mp isCompact_Icc
  set A₀ := F.toZeroAtlas hW.isClosed
  let Lk := L.toAnalyticResolvedLikelihood A₀ id (fun _ ↦ rfl) (fun _ ↦ rfl)
    (fun α u hu ↦ α.extMap_eq (α.cube_subset_domain hu)) I.two_le
  let Ek : SingularLearningTheory.EmpiricalProcessLimit q
      (fun x (u : ResolutionAtlas.Domain A₀) ↦ Lk.a u.1 x u.2) Xs P P' :=
    E
  have h := SingularLearningTheory.MaximumLikelihood.divergingPenalty_asymptotics A₀ I Lk
    (measurable_uncurry_logDensityRatio hp w₀) hW hK0 hcont hw₀ (excessLoss_self q p w₀)
    (zeroAtlas_cover hW hWreg) hX hIndep Ek ŵ hŵ hŵW σ U hU hWU hσ aSeq haSeq ha
    hslow hmin
  have hM : ∀ ω', (⨆ v : {v ∈ {v : (α : F.Piece) × cube d α.radius |
      excessLoss q p w₀ (v.1.map v.2) = 0} | ∀ v' ∈ {v : (α : F.Piece) × cube d α.radius |
      excessLoss q p w₀ (v.1.map v.2) = 0}, σ (v.1.map v.2) ≤ σ (v'.1.map v'.2)},
      (max 0 (-E.Ψlim ω' v)) ^ 2 / 4)
      = ResolutionAtlas.likelihoodRewardSup A₀
        (ResolutionAtlas.resolvedPenaltyMinimizers A₀ σ) (Ek.Ψlim ω') := fun ω' ↦ by
    rw [iSup_eq_sSup_image
      (resolvedPenaltyMinimizers_zeroAtlas hW.isClosed σ)
      (fun v ↦ (max 0 (-E.Ψlim ω' v)) ^ 2 / 4)]
    rfl
  dsimp only at h ⊢
  simp only [hM]
  exact h

section CenteredMeasurability

variable {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {p : (Fin d → ℝ) → X → ℝ} {Xs : ℕ → Ω → X}

/-- The empirical negative log-likelihood is jointly measurable in the sample and the parameter.
Supports `freeEnergy_centered_at_maximumLikelihood`. -/
private theorem measurable_uncurry_empiricalNegativeLogLikelihood
    (hp : Measurable (Function.uncurry p)) (hX : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Measurable (Function.uncurry (empiricalNegativeLogLikelihood p Xs n)) := by
  change Measurable (fun v : Ω × (Fin d → ℝ) ↦
    -(∑ i ∈ Finset.range n, Real.log (p v.2 (Xs i v.1))) / (n : ℝ))
  refine (Finset.measurable_sum _ fun i _ ↦ ?_).neg.div_const _
  exact Real.measurable_log.comp
    (hp.comp (measurable_snd.prodMk ((hX i).comp measurable_fst)))

/-- The free energy `F_n` is almost everywhere measurable for every `n`. Supports
`freeEnergy_centered_at_maximumLikelihood`. -/
private theorem aemeasurable_freeEnergy
    (hp : Measurable (Function.uncurry p)) (hX : ∀ i, Measurable (Xs i))
    {W : Set (Fin d → ℝ)} {φ : (Fin d → ℝ) → ℝ} {P : Measure Ω}
    (hφi : IntegrableOn φ W) (β : ℝ) (n : ℕ) :
    AEMeasurable (freeEnergy p W φ β Xs n) P := by
  have hN := measurable_uncurry_empiricalNegativeLogLikelihood hp hX n
  have hZn : AEMeasurable (evidence p W φ β Xs n) P := by
    have hprod : AEStronglyMeasurable
        (fun v : Ω × (Fin d → ℝ) ↦
          Real.exp (-((n : ℝ) * β * empiricalNegativeLogLikelihood p Xs n v.1 v.2)) * φ v.2)
        (P.prod (volume.restrict W)) :=
      (Real.measurable_exp.comp (measurable_const.mul hN).neg).aestronglyMeasurable.mul
        hφi.aestronglyMeasurable.comp_snd
    exact hprod.integral_prod_right'.aemeasurable
  exact (Real.measurable_log.comp_aemeasurable hZn).neg

end CenteredMeasurability

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
by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  classical
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hK := hRFV.excessLoss_nonneg
  obtain ⟨C, hC, hRFV'⟩ := hRFV.exists_integral_sq_le_inv_mul
  obtain ⟨UK, hUK, hWUK, hKa⟩ := I.exists_analyticOnNhd_K
  obtain ⟨A⟩ := SingularLearningTheory.exists_atlasData hW II hUK hWUK
    hKa hK hw₀ (excessLoss_self q p w₀) hKg hφg
  letI := A.nonempty_ι hvol
  let R := A.toResolutionAtlas
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun _ hw ↦ II.nonneg hw
  have hφi : IntegrableOn φ W := (II.continuousOn).integrableOn_compact hW
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hlaw : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  obtain ⟨Ω', mΩ', P', hP', Rlim, hRi, hNi, hLaw, hMean, hZpos⟩ :=
    A.centered_at_maximumLikelihood I (measurable_uncurry_logDensityRatio hp w₀) hcont
      hC hRFV' hφ hφi Xs hX hIndep ŵ hŵ hŵW hmin
  letI := mΩ'
  letI := hP'
  let S : ℕ → Ω → ℝ := fun n ω ↦
    -Real.log ((n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
      normalizedEvidence p w₀ W φ 1 Xs n ω) - (n : ℝ) * empiricalExcessLoss p w₀ Xs n ω (ŵ n ω)
  let Rn : ℕ → Ω → ℝ := fun n ω ↦ freeEnergy p W φ 1 Xs n ω -
    (n : ℝ) * empiricalNegativeLogLikelihood p Xs n ω (ŵ n ω) -
    R.rlct * Real.log n + ((R.mult : ℝ) - 1) * Real.log (Real.log n)
  have hSi : ∀ᶠ n : ℕ in atTop, Integrable (S n) P := by
    simpa only
        [S, normalizedEvidence, mul_one, empiricalExcessLoss, SingularLearningTheory.empiricalLoss,
        R] using hNi
  have hSlaw : TendstoInDistribution S atTop Rlim (fun _ ↦ P) P' := by
    simpa only
        [S, normalizedEvidence, mul_one, empiricalExcessLoss, SingularLearningTheory.empiricalLoss,
        R] using hLaw
  have hSmean : Tendsto (fun n : ℕ ↦ ∫ ω, S n ω ∂P) atTop
      (𝓝 (∫ ω', Rlim ω' ∂P')) := by
    simpa only
        [S, normalizedEvidence, mul_one, empiricalExcessLoss, SingularLearningTheory.empiricalLoss,
        R] using hMean
  have hRnm : ∀ n : ℕ, AEMeasurable (Rn n) P := by
    intro n
    have hfit : Measurable (fun ω ↦ empiricalNegativeLogLikelihood p Xs n ω (ŵ n ω)) :=
      (measurable_uncurry_empiricalNegativeLogLikelihood hp hXm n).comp
        (measurable_id.prodMk (hŵ n))
    exact (((aemeasurable_freeEnergy hp hXm hφi 1 n).sub
      (aemeasurable_const.mul hfit.aemeasurable)).sub aemeasurable_const).add aemeasurable_const
  have heq : ∀ᶠ n : ℕ in atTop, S n =ᵐ[P] Rn n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    filter_upwards [ae_pos_at_samples hp_pos hXm hlaw n, hŵW n, hZpos n hn] with ω hpos hwfit hZ
    have hZ0 : 0 < normalizedEvidence p w₀ W φ 1 Xs n ω := by
      simpa only
          [normalizedEvidence, mul_one, empiricalExcessLoss, SingularLearningTheory.empiricalLoss]
          using hZ
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hcast : ((R.mult - 1 : ℕ) : ℝ) = (R.mult : ℝ) - 1 :=
      Nat.cast_pred R.mult_pos
    dsimp only [S, Rn]
    rw [freeEnergy_eq_add_neg_log_normalizedEvidence hW.measurableSet hpos hw₀ φ 1 hZ0,
      empiricalExcessLoss_eq_sub hpos hw₀ hwfit,
      Real.log_mul (div_pos (Real.rpow_pos_of_pos hn0 _) (pow_pos hlog _)).ne' hZ0.ne',
      Real.log_div (Real.rpow_pos_of_pos hn0 _).ne' (pow_pos hlog _).ne',
      Real.log_rpow hn0, Real.log_pow, hcast]
    ring
  refine ⟨R.rlct, R.mult, R.rlct_pos, R.mult_pos,
    A.toNondegenerateResolutionAtlas.isSingularityType_of_continuousOn hW I.continuousOn_K hφ
      II.continuousOn,
    Ω', mΩ', P', hP', Rlim, hRi, ?_, ?_, ?_⟩
  · filter_upwards [hSi, heq] with n hn he
    exact hn.congr he
  · exact tendstoInDistribution_of_eventually_ae_eq
      hSlaw hRnm heq
  · exact hSmean.congr' (heq.mono fun n hn ↦ integral_congr_ae hn)

end SingularLearningTheory
