/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy
public import SLT.BayesGibbs.ExpMeasure
public import SLT.BayesGibbs.FiniteSample.PosteriorFive
public import SLT.BayesGibbs.Posterior.Assembly
public import SLT.BayesGibbs.Defs
import SLT.BayesGibbs.CompactPosterior.RatioProbability
import SLT.FreeEnergy.StochasticAsymptotics

/-!
# Bayes and Gibbs estimation under relatively finite variance

The theorems of `SLTChallenge/BayesGibbs.lean`, proved from the library; the definitions are in
`SLT/BayesGibbs/Defs.lean`. The proofs identify the four errors and the functional variance
with the library's posterior five-vector `BayesGibbs.posteriorFive`, whose joint law, expectation
limits and functional-variance relations come from
`NondegenerateResolutionAtlas.posteriorFive_asymptotics`. The limit keeps the full covariance of the
limiting process; neither normalisation of the model nor positivity of the Bayes error is used. The
chart process has the book's sign `ξ = −Ψ`.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

section PosteriorBridges

variable {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {p : (Fin d → ℝ) → X → ℝ} {Xs : ℕ → Ω → X}
  {W : Set (Fin d → ℝ)} {φ : (Fin d → ℝ) → ℝ}

omit [MeasurableSpace X] [MeasurableSpace Ω] in
/-- `posteriorMeasure` is the library's `MeasureTheory.Measure.expMeasure`, also on samples with
zero
evidence. -/
private theorem posteriorMeasure_eq_expMeasure
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (w₀ : Fin d → ℝ) (β : ℝ) (n : ℕ) (ω : Ω) :
    posteriorMeasure p w₀ W φ β Xs n ω =
      Measure.expMeasure (priorMeasure φ W)
        (fun w ↦ (n : ℝ) * β * empiricalExcessLoss p w₀ Xs n ω w) := by
  exact BayesGibbs.weighted_posterior_eq_expMeasure hW hφ hφi
    (fun w ↦ (n : ℝ) * β * empiricalExcessLoss p w₀ Xs n ω w)

omit [MeasurableSpace Ω] in
/-- The library's `posteriorFive` is `(nB_g, nB_t, nG_g, nG_t, V)` for every `n`, including
`n = 0`; only the equality of posterior measures is used. -/
private theorem posteriorFive_eq_scaled_bayesGibbsFive
    (q : Measure X)
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (w₀ : Fin d → ℝ) (β : ℝ) (n : ℕ) (ω : Ω) :
    BayesGibbs.posteriorFive (priorMeasure φ W) q (excessLoss q p w₀)
      (logDensityRatio p w₀) Xs β n ω =
      ![(n : ℝ) * bayesGeneralizationError q p w₀ W φ β Xs n ω,
        (n : ℝ) * bayesTrainingError p w₀ W φ β Xs n ω,
        (n : ℝ) * gibbsGeneralizationError q p w₀ W φ β Xs n ω,
        (n : ℝ) * gibbsTrainingError p w₀ W φ β Xs n ω,
        functionalVariance p w₀ W φ β Xs n ω] := by
  have hQ : Measure.expMeasure (priorMeasure φ W)
      (fun w ↦ (n : ℝ) * β *
        SingularLearningTheory.empiricalLoss (logDensityRatio p w₀) Xs n ω w) =
      posteriorMeasure p w₀ W φ β Xs n ω := by
    simpa only [SingularLearningTheory.empiricalLoss, empiricalExcessLoss] using
      (posteriorMeasure_eq_expMeasure hW hφ hφi w₀ β n ω).symm
  dsimp only [BayesGibbs.posteriorFive]
  simp only [hQ]
  let b : X → ℝ := fun x ↦ Real.log (∫ w, Real.exp (-logDensityRatio p w₀ x w)
    ∂posteriorMeasure p w₀ W φ β Xs n ω)
  ext j
  fin_cases j
  · change (n : ℝ) * (∫ x, -b x ∂q) = (n : ℝ) * (-(∫ x, b x ∂q))
    rw [integral_neg]
  · change (∑ i ∈ Finset.range n, -b (Xs i ω)) =
      (n : ℝ) * (-(∑ i ∈ Finset.range n, b (Xs i ω)) / (n : ℝ))
    rw [Finset.sum_neg_distrib]
    by_cases hn : n = 0
    · subst n
      simp
    · field_simp [Nat.cast_ne_zero.mpr hn]
  · rfl
  · rfl
  · rfl

end PosteriorBridges

/-- One limit law, with the learning coefficient and singular fluctuation, from which the four
theorems below follow. -/
private theorem bayesGibbs_common
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (hp : Measurable (Function.uncurry p))
    (W : Set (Fin d → ℝ)) (hW : IsCompact W)
    (φ : (Fin d → ℝ) → ℝ) (w₀ : Fin d → ℝ) (hw₀ : w₀ ∈ W)
    (hRFV : RelativelyFiniteVariance q p w₀ W)
    (I : FundamentalConditionI 6 q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (II : FundamentalConditionII φ W)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W)
    (hKg : ∀ w ∈ W, excessLoss q p w₀ w = 0 → ¬ (excessLoss q p w₀ =ᶠ[𝓝 w] 0))
    (hφg : ∀ w ∈ W, excessLoss q p w₀ w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0,
      0 < ∫⁻ w in W ∩ {w | excessLoss q p w₀ w < ε}, ENNReal.ofReal (φ w))
    (β : ℝ) (hβ : 0 < β) (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P)

    :
    let e : ℕ → Ω → Fin 4 → ℝ := fun (n : ℕ) ω ↦
      ![bayesGeneralizationError q p w₀ W φ β Xs n ω,
        bayesTrainingError p w₀ W φ β Xs n ω,
        gibbsGeneralizationError q p w₀ W φ β Xs n ω,
        gibbsTrainingError p w₀ W φ β Xs n ω]
    let V := functionalVariance p w₀ W φ β Xs
    let Y₅ : ℕ → Ω → Fin 5 → ℝ := fun (n : ℕ) ω ↦
      ![(n : ℝ) * e n ω 0, (n : ℝ) * e n ω 1,
        (n : ℝ) * e n ω 2, (n : ℝ) * e n ω 3, V n ω]
    ∃ (lam : ℝ) (m : ℕ), 0 < lam ∧ 1 ≤ m ∧ IsSingularityType (excessLoss q p w₀) φ W lam m ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P') (Z : Ω' → Fin 5 → ℝ) (ν : ℝ),
        0 ≤ ν ∧
        TendstoInDistribution Y₅ atTop Z (fun _ ↦ P) P' ∧
        (∀ j, Integrable (fun ω' ↦ Z ω' j) P') ∧
        (∀ j, ∀ᶠ n in atTop, Integrable (fun ω ↦ Y₅ n ω j) P) ∧
        (∀ j, Tendsto (fun n ↦ ∫ ω, Y₅ n ω j ∂P) atTop (𝓝 (∫ ω', Z ω' j ∂P'))) ∧
        (∀ j, Tendsto (fun n ↦ ∫ ω, Y₅ n ω j ∂P) atTop
          (𝓝 (SingularLearningTheory.bayesGibbsCoefficients β lam ν j))) ∧
        TendstoInMeasure P
          (fun (n : ℕ) ω ↦ (n : ℝ) * (e n ω 0 - e n ω 1 - e n ω 2 + e n ω 3))
          atTop (fun _ ↦ 0) ∧
        TendstoInMeasure P
          (fun (n : ℕ) ω ↦ (n : ℝ) * (e n ω 2 + e n ω 3) - 2 * lam / β)
          atTop (fun _ ↦ 0) ∧
        TendstoInMeasure P (fun (n : ℕ) ω ↦ V n ω - 2 * n * (e n ω 2 - e n ω 0))
          atTop (fun _ ↦ 0) ∧
        TendstoInMeasure P (fun (n : ℕ) ω ↦ V n ω - 2 * n * (e n ω 3 - e n ω 1))
          atTop (fun _ ↦ 0) := by
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  have hK := hRFV.excessLoss_nonneg
  obtain ⟨C, hC, hRFV'⟩ := hRFV.exists_integral_sq_le_inv_mul
  obtain ⟨UK, hUK, hWUK, hKa⟩ := I.exists_analyticOnNhd_K
  obtain ⟨R⟩ := exists_nondegenerateResolutionAtlas hW II hUK hWUK
    hKa hK hw₀ (excessLoss_self q p w₀) hKg hφg hvol
  have hcontg : ∀ᵐ x ∂q, ∀ α, Continuous fun u : cube d (R.b α) ↦
      logDensityRatio p w₀ x (R.g α u) := by
    filter_upwards [hcont] with x hx α
    exact hx.comp_continuous ((R.g_analytic α).continuousOn.comp_continuous
      continuous_subtype_val fun u ↦ u.2) fun u ↦ R.g_mapsTo α u.2
  have hf : LsValuedAnalytic 6 q (logDensityRatio p w₀) W :=
    I.ls_analytic
  obtain ⟨Lk⟩ := R.toResolutionAtlas.exists_analyticResolvedLikelihood I.two_le
    (fun _ ↦ rfl) hf hC hRFV' hcontg
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hXl : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  obtain ⟨P₁, hP₁, ⟨E₀⟩⟩ :=
    Lk.exists_empiricalProcessLimit_chart hXm hXl hIndep
  obtain ⟨P₂, hP₂, ⟨T₀⟩⟩ := I.exists_tail_empiricalProcessLimit hW
    (fun w ↦ (measurable_uncurry_logDensityRatio hp w₀).comp
      (measurable_id.prodMk measurable_const)) hcont R.δ_pos hXm hXl hIndep
  letI : CompactSpace {w // w ∈ W ∧ R.δ ≤ excessLoss q p w₀ w} :=
    isCompact_iff_compactSpace.mp (I.isCompact_tail hW R.δ)
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun w hw ↦ II.nonneg hw
  have hφi : IntegrableOn φ W := (II.continuousOn).integrableOn_compact hW
  obtain ⟨ν, hν, hd, hi, hei, hM, hMc, htel, hsum, hVG, hVT⟩ :=
    R.posteriorFive_asymptotics I Lk hW (measurable_uncurry_logDensityRatio hp w₀) hcont hK
      ⟨C⁻¹, (inv_pos.mpr hC).le, hRFV'⟩ hφ hφi hvol hXm hXl hIndep
      E₀.prodFst T₀.prodSnd hβ
  have heq : BayesGibbs.posteriorFive (priorMeasure φ W) q (excessLoss q p w₀)
      (logDensityRatio p w₀) Xs β = fun (n : ℕ) ω ↦
      ![(n : ℝ) * bayesGeneralizationError q p w₀ W φ β Xs n ω,
        (n : ℝ) * bayesTrainingError p w₀ W φ β Xs n ω,
        (n : ℝ) * gibbsGeneralizationError q p w₀ W φ β Xs n ω,
        (n : ℝ) * gibbsTrainingError p w₀ W φ β Xs n ω,
        functionalVariance p w₀ W φ β Xs n ω] := by
    funext n ω
    exact posteriorFive_eq_scaled_bayesGibbsFive q hW.measurableSet hφ hφi w₀ β n ω
  change TendstoInDistribution
    (BayesGibbs.posteriorFive (priorMeasure φ W) q (excessLoss q p w₀)
      (logDensityRatio p w₀) Xs β) atTop _ (fun _ ↦ P) _ at hd
  rw [heq] at hd
  simp only [priorMeasure] at heq
  simp only [heq] at hei hM hMc htel hsum hVG hVT
  dsimp only
  refine ⟨R.rlct, R.mult, R.toResolutionAtlas.rlct_pos, R.toResolutionAtlas.mult_pos,
    R.isSingularityType_of_continuousOn hW I.continuousOn_K hφ II.continuousOn,
    _, inferInstance, P₁.prod P₂, inferInstance, _, ν, hν, hd, hi, hei, hM, hMc,
    ?_, ?_, ?_, ?_⟩
  · convert htel using 1
    funext n ω
    simp
    <;> ring
  · convert hsum using 1
    funext n ω
    simp
    <;> ring
  · convert hVG using 1
    funext n ω
    simp
    <;> ring
  · convert hVT using 1
    funext n ω
    simp
    <;> ring

/-- **Convergence of the Bayes and Gibbs errors, under RFV.** The scaled errors `nB_g, nB_t, nG_g,
nG_t` converge jointly in law and in expectation, and `n(B_g − B_t − G_g + G_t) → 0` in probability.

Relation to the source.
* **Strengthening.** Part (1) is the joint convergence in law of the four scaled errors, where the
  book states four separate limits.
* **Gap.** The limits are not identified with the functionals $B_g^*, B_t^*, G_g^*, G_t^*$ of
  [Wat09, Definition 6.9].

Source statement: [Wat09, Theorem 6.8] -/
-- `hp_pos` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
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
        atTop (fun _ ↦ 0) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  obtain ⟨lam₀, m₀, hlam₀, hm₀, htype₀, Ω', mΩ', P', hP', Z, ν, hν,
      hd, hi, hei, hM, hMc, htel, hsum, hVG, hVT⟩ :=
    bayesGibbs_common q p hp W hW φ w₀ hw₀ hRFV I II hcont hKg hφg hvol β hβ Xs P hXs
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  let π : (Fin 5 → ℝ) → Fin 4 → ℝ := fun z j ↦ z j.castSucc
  have hπ : Continuous π := continuous_pi fun j ↦ continuous_apply j.castSucc
  refine ⟨Ω', mΩ', P', hP', fun ω ↦ Z ω 0, fun ω ↦ Z ω 1, fun ω ↦ Z ω 2, fun ω ↦ Z ω 3,
    ?_, ?_, htel⟩
  · convert hd.continuous_comp hπ using 1
    · funext n ω j
      fin_cases j <;> rfl
    · funext ω j
      fin_cases j <;> rfl
  · exact ⟨⟨hi 0, hei 0, hM 0⟩, ⟨hi 1, hei 1, hM 1⟩, ⟨hi 2, hei 2, hM 2⟩, ⟨hi 3, hei 3, hM 3⟩⟩


/-- **Equations of state, under RFV.** The equations of state (6.19) and (6.20), stated as
`n(E[B_g] − E[B_t] − 2β(E[G_t] − E[B_t])) → 0` and its analogue for `G_g − G_t`.

Relation to the source.
* **Restatement.** The equations are stated for the scaled expectations at finite $n$; by
  `bayes_gibbs_convergence` (3) these converge to the expectations of the limits, so the two forms
  are equivalent.

Source statement: [Wat09, Main Theorem 6.3] -/
-- `hp_pos` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
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
      atTop (𝓝 0) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  obtain ⟨lam₀, m₀, hlam₀, hm₀, htype₀, Ω', mΩ', P', hP', Z, ν, hν,
      hd, hi, hei, hM, hMc, htel, hsum, hVG, hVT⟩ :=
    bayesGibbs_common q p hp W hW φ w₀ hw₀ hRFV I II hcont hKg hφg hvol β hβ Xs P hXs
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  let e : ℕ → Ω → Fin 4 → ℝ := fun (n : ℕ) ω ↦
    ![bayesGeneralizationError q p w₀ W φ β Xs n ω,
      bayesTrainingError p w₀ W φ β Xs n ω,
      gibbsGeneralizationError q p w₀ W φ β Xs n ω,
      gibbsTrainingError p w₀ W φ β Xs n ω]
  have hlim : ∀ j : Fin 4,
      Tendsto (fun n : ℕ ↦ ∫ ω, (n : ℝ) * e n ω j ∂P) atTop
        (𝓝 (![lam₀ / β + (1 - 1 / β) * ν,
          lam₀ / β - (1 + 1 / β) * ν, lam₀ / β + ν, lam₀ / β - ν] j)) := by
    intro j
    fin_cases j
    · exact hMc 0
    · exact hMc 1
    · exact hMc 2
    · exact hMc 3
  exact BayesGibbs.equations_of_state_of_coefficient_limits (e := e) hβ.ne' hlim


/-- **The Gibbs errors and the learning coefficient, under RFV.** `nG_g + nG_t → 2λ/β` in
probability, and `n E[G_g] + n E[G_t] → 2λ/β`.

Relation to the source.
* **Restatement.** (6.22) is stated for the limit of the scaled expectations, which by
  `bayes_gibbs_convergence` (3) is $E[G_g^*] + E[G_t^*]$.

Source statement: [Wat09, Theorem 6.9] -/
-- `hlam` and `hm` are unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
theorem gibbs_errors_learning_coefficient
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
    let Gg : ℕ → Ω → ℝ := gibbsGeneralizationError q p w₀ W φ β Xs
    let Gt : ℕ → Ω → ℝ := gibbsTrainingError p w₀ W φ β Xs
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (n : ℝ) * (Gg n ω + Gt n ω) - 2 * lam / β)
      atTop (fun _ ↦ 0) ∧
    Tendsto (fun (n : ℕ) ↦ (∫ ω, (n : ℝ) * Gg n ω ∂P) + (∫ ω, (n : ℝ) * Gt n ω ∂P)) atTop
      (𝓝 (2 * lam / β)) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  obtain ⟨lam₀, m₀, hlam₀, hm₀, htype₀, Ω', mΩ', P', hP', Z, ν, hν,
      hd, hi, hei, hM, hMc, htel, hsum, hVG, hVT⟩ :=
    bayesGibbs_common q p hp W hW φ w₀ hw₀ hRFV I II hcont hKg hφg hvol β hβ Xs P hXs
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  have hlamEq : lam₀ = lam := (SingularLearningTheory.IsSingularityType.unique
    htype₀ htype).1
  subst lam₀
  have hGg : Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * gibbsGeneralizationError q p w₀ W φ β Xs n ω ∂P)
      atTop (𝓝 (lam / β + ν)) := hMc 2
  have hGt : Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * gibbsTrainingError p w₀ W φ β Xs n ω ∂P)
      atTop (𝓝 (lam / β - ν)) := hMc 3
  refine ⟨hsum, ?_⟩
  convert hGg.add hGt using 2
  ring

/-- **The Bayes and Gibbs errors and the singular fluctuation, under RFV.** Equations (6.25)–(6.30),
with the singular fluctuation `ν` given by `E[V] → 2ν/β`. Here `ν ≥ 0`, and `ν = 0` when the log
density ratio does not fluctuate with the data near `W₀`, for example when `q` is a point mass.

Relation to the source.
* **Gap.** $\nu \ge 0$ where the book has $\nu > 0$; under relatively finite variance $\nu = 0$ is
  possible, for instance when $q$ is a point mass.
* **Gap.** $\nu$ is defined by $E[V] \to 2\nu/\beta$, not identified with the singular fluctuation
  of [Wat09, Definition 5.9], and the book's upper bound on $\nu$ is not stated.

Source statement: [Wat09, Theorem 6.10] -/
-- `hlam` and `hm` are unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
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
      -- the singular fluctuation, `lim E[V] = 2ν/β`; the book has `ν > 0`
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
      Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * Gt n ω ∂P) atTop (𝓝 (lam / β - ν)) := by
  obtain ⟨hp, hW, hp_pos, hw₀, hRFV, I, hcont⟩ := hA
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  obtain ⟨lam₀, m₀, hlam₀, hm₀, htype₀, Ω', mΩ', P', hP', Z, ν, hν,
      hd, hi, hei, hM, hMc, htel, hsum, hVG, hVT⟩ :=
    bayesGibbs_common q p hp W hW φ w₀ hw₀ hRFV I II hcont hKg hφg hvol β hβ Xs P hXs
  letI : MeasurableSpace Ω' := mΩ'
  letI : IsProbabilityMeasure P' := hP'
  have hlamEq : lam₀ = lam := (SingularLearningTheory.IsSingularityType.unique
    htype₀ htype).1
  subst lam₀
  exact ⟨ν, hVT, hVG, hν, hei 4, hMc 4, hMc 0, hMc 1, hMc 2, hMc 3⟩

/-- **The generalization errors from the training errors, under RFV.** The matrix form (6.21) of the
equations of state: `n(E[B_g] − ((1 − 2β) E[B_t] + 2β E[G_t])) → 0` and
`n(E[G_g] − (−2β E[B_t] + (1 + 2β) E[G_t])) → 0`.

Source statement: [Wat09, Corollary 6.2] -/
theorem generalization_errors_of_training_errors
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    (q : Measure X) [IsProbabilityMeasure q]
    (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (w₀ : Fin d → ℝ)
    (hA : StandingAssumptions 6 q p W w₀)
    (φ : (Fin d → ℝ) → ℝ) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions (excessLoss q p w₀) φ W)
    (β : ℝ) (hβ : 0 < β) (Xs : ℕ → Ω → X) (P : Measure Ω) [IsProbabilityMeasure P]
    (hXs : IsIIDSample q Xs P) :
    let Bg : ℕ → Ω → ℝ := bayesGeneralizationError q p w₀ W φ β Xs
    let Bt : ℕ → Ω → ℝ := bayesTrainingError p w₀ W φ β Xs
    let Gg : ℕ → Ω → ℝ := gibbsGeneralizationError q p w₀ W φ β Xs
    let Gt : ℕ → Ω → ℝ := gibbsTrainingError p w₀ W φ β Xs
    Tendsto (fun (n : ℕ) ↦ (n : ℝ) *
      ((∫ ω, Bg n ω ∂P) - ((1 - 2 * β) * (∫ ω, Bt n ω ∂P) + 2 * β * (∫ ω, Gt n ω ∂P))))
      atTop (𝓝 0) ∧
    Tendsto (fun (n : ℕ) ↦ (n : ℝ) *
      ((∫ ω, Gg n ω ∂P) - (-(2 * β) * (∫ ω, Bt n ω ∂P) + (1 + 2 * β) * (∫ ω, Gt n ω ∂P))))
      atTop (𝓝 0) := by
  obtain ⟨h1, h2⟩ := equations_of_state q p W w₀ hA φ II hZ β hβ Xs P hXs
  dsimp only at h1 h2 ⊢
  exact ⟨h1.congr fun n ↦ by ring, h2.congr fun n ↦ by ring⟩

/-- **The Bayes errors and the learning coefficient, under RFV.** `nB_g − nB_t + 2nG_t → 2λ/β` in
probability, `n E[B_g] − n E[B_t] + 2n E[G_t] → 2λ/β`, and at `β = 1`, `n E[B_g] → λ`.

Source statement: [Wat09, Corollary 6.3] -/
theorem bayes_errors_learning_coefficient
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
    let Gt : ℕ → Ω → ℝ := gibbsTrainingError p w₀ W φ β Xs
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦
        (n : ℝ) * Bg n ω - n * Bt n ω + 2 * (n * Gt n ω) - 2 * lam / β)
      atTop (fun _ ↦ 0) ∧
    Tendsto (fun (n : ℕ) ↦ (∫ ω, (n : ℝ) * Bg n ω ∂P) - (∫ ω, (n : ℝ) * Bt n ω ∂P) +
        2 * ∫ ω, (n : ℝ) * Gt n ω ∂P)
      atTop (𝓝 (2 * lam / β)) ∧
    (β = 1 → Tendsto (fun (n : ℕ) ↦ ∫ ω, (n : ℝ) * Bg n ω ∂P) atTop (𝓝 lam)) := by
  have hG := (gibbs_errors_learning_coefficient q p W w₀ hA φ II hZ β hβ Xs P hXs
    lam m hlam hm htype).1
  obtain ⟨ν, h25, h26, -, -, -, h27, h28, -, h30⟩ :=
    bayes_gibbs_learning_coefficients q p W w₀ hA φ II hZ β hβ Xs P hXs lam m hlam hm htype
  dsimp only at hG h25 h26 h27 h28 h30 ⊢
  refine ⟨?_, ?_, fun hb ↦ ?_⟩
  · refine (tendstoInMeasure_add_zero (tendstoInMeasure_add_zero hG
      (tendstoInMeasure_const_mul_zero (-1 / 2) h25))
      (tendstoInMeasure_const_mul_zero (1 / 2) h26)).congr'
      (Eventually.of_forall fun n ↦ ae_of_all _ fun ω ↦ ?_) EventuallyEq.rfl
    ring
  · convert (h27.sub h28).add (h30.const_mul 2) using 2
    ring
  · subst hb
    convert h27 using 2
    ring

/-- **The singular fluctuation from the Bayes quartet, under RFV.** With `ν` as in
`bayes_gibbs_learning_coefficients`, the scaled differences `n(E[B_g] − E[B_t])` and
`n(E[G_g] − E[G_t])` tend to `2ν`, `βn(E[G_g] − E[B_g])` and `βn(E[G_t] − E[B_t])` tend to `ν`, and
`(β/2) E[V] → ν`; hence (6.31) and (6.32), `n E[B_g] − n E[B_t] − β E[V] → 0` and
`n E[G_g] − n E[G_t] − β E[V] → 0`.

Source statement: [Wat09, Remark 6.10] -/
theorem singular_fluctuation_of_bayes_quartet
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
    ∃ ν : ℝ, 0 ≤ ν ∧
      Tendsto (fun (n : ℕ) ↦ (∫ ω, (n : ℝ) * Bg n ω ∂P) - ∫ ω, (n : ℝ) * Bt n ω ∂P)
        atTop (𝓝 (2 * ν)) ∧
      Tendsto (fun (n : ℕ) ↦ (∫ ω, (n : ℝ) * Gg n ω ∂P) - ∫ ω, (n : ℝ) * Gt n ω ∂P)
        atTop (𝓝 (2 * ν)) ∧
      Tendsto (fun (n : ℕ) ↦ β * ((∫ ω, (n : ℝ) * Gg n ω ∂P) - ∫ ω, (n : ℝ) * Bg n ω ∂P))
        atTop (𝓝 ν) ∧
      Tendsto (fun (n : ℕ) ↦ β * ((∫ ω, (n : ℝ) * Gt n ω ∂P) - ∫ ω, (n : ℝ) * Bt n ω ∂P))
        atTop (𝓝 ν) ∧
      Tendsto (fun (n : ℕ) ↦ β / 2 * ∫ ω, V n ω ∂P) atTop (𝓝 ν) ∧
      -- (6.31)
      Tendsto (fun (n : ℕ) ↦
        (∫ ω, (n : ℝ) * Bg n ω ∂P) - (∫ ω, (n : ℝ) * Bt n ω ∂P) - β * ∫ ω, V n ω ∂P)
        atTop (𝓝 0) ∧
      -- (6.32)
      Tendsto (fun (n : ℕ) ↦
        (∫ ω, (n : ℝ) * Gg n ω ∂P) - (∫ ω, (n : ℝ) * Gt n ω ∂P) - β * ∫ ω, V n ω ∂P)
        atTop (𝓝 0) := by
  obtain ⟨ν, -, -, hν, -, hV, h27, h28, h29, h30⟩ :=
    bayes_gibbs_learning_coefficients q p W w₀ hA φ II hZ β hβ Xs P hXs lam m hlam hm htype
  dsimp only at hV h27 h28 h29 h30 ⊢
  have hβ0 : β ≠ 0 := hβ.ne'
  refine ⟨ν, hν, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert h27.sub h28 using 2
    ring
  · convert h29.sub h30 using 2
    ring
  · convert (h29.sub h27).const_mul β using 2
    field_simp
    ring
  · convert (h30.sub h28).const_mul β using 2
    field_simp
    ring
  · convert hV.const_mul (β / 2) using 2
    field_simp
  · convert (h27.sub h28).sub (hV.const_mul β) using 2
    field_simp
    ring
  · convert (h29.sub h30).sub (hV.const_mul β) using 2
    field_simp
    ring

end SingularLearningTheory
