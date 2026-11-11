/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.DivergingPenalty.Approximation
import SLT.MaximumLikelihood.DivergingPenalty.Envelope
public import SLT.MaximumLikelihood.Penalty.Functionals
import SLT.MaximumLikelihood.Envelope
import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.FreeEnergy.FundamentalConditions

/-!
# DivergingPenaltyAssembly

Joint distributional and mean limits with a diverging subpolynomial penalty.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.MaximumLikelihood

variable {d : ℕ} {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [MeasurableSpace Ω'] {q : Measure X} [IsProbabilityMeasure q]
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {f : X → (Fin d → ℝ) → ℝ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The slowly diverging penalty selects exactly the penalty minimizers of the
resolved zero set. Both errors converge jointly; sharp localization transfers means. -/
theorem divergingPenalty_asymptotics
    (I : FundamentalConditionI 4 q f K W) (L : R.AnalyticResolvedLikelihood 4 q f)
    (hf : Measurable (Function.uncurry f)) (hW : IsCompact W)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hcover : ∃ δ > 0, ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {Xs : ℕ → Ω → X} (hX : ∀ i, MeasurePreserving (Xs i) P q) (hIndep : iIndepFun Xs P)
    (E : EmpiricalProcessLimit q (fun x (u : ResolutionAtlas.Domain R) ↦ L.a u.1 x u.2) Xs P P')
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n : ℕ, Measurable (ŵ n))
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (σ : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ)) (_hU : IsOpen U)
    (hWU : W ⊆ U) (hσ : ContDiffOn ℝ 1 σ U)
    (aSeq : ℕ → ℝ) (haSeq : ∀ n, 0 ≤ aSeq n) (ha : Tendsto aSeq atTop atTop)
    (hslow : ∀ r : ℝ, 0 < r → Tendsto (fun n : ℕ ↦ aSeq n / (n : ℝ) ^ r) atTop (𝓝 0))
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤
        (n : ℝ) * empiricalLoss f Xs n ω w + aSeq n * σ w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * K (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)
    let M := fun ω' ↦ ResolutionAtlas.likelihoodRewardSup R
        (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (E.Ψlim ω')
    Integrable M P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (M ω', -M ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', M ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) := by
  dsimp only
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hlaw : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  have hσW : ContinuousOn σ W := hσ.continuousOn.mono hWU
  obtain ⟨wm, hwm, hmax⟩ := hW.exists_isMaxOn ⟨w₀, hw₀⟩ hσW.abs
  let Sg := |σ wm|
  have hSg : 0 ≤ Sg := abs_nonneg _
  have hσb : ∀ w ∈ W, |σ w| ≤ Sg := fun w hw ↦ hmax hw
  obtain ⟨hσg, Λ, hΛ, hσLip⟩ := ResolutionAtlas.chartPenalty_continuous_lipschitz R hWU hσ
  obtain ⟨δ, hδ, hcoverδ⟩ := hcover
  obtain ⟨H, hHm, hH0, hNorm, ⟨D, hD, hfour⟩, henv⟩ :=
    exists_relative_envelope_fourth R I L hW (fun w ↦ hf.comp (measurable_id.prodMk measurable_const))
      hcont hδ hcoverδ hXm hlaw hIndep E
  have hchart := fun (n : ℕ) hn ↦ sampleLoss_chart_ae R L.toResolvedLikelihood hXm hlaw E (n := n) hn
  have hsharp := divergingPenalty_sharp_localization_ae R hK0 hH0 henv hw₀ hw₀K
    hŵW haSeq hSg hσb hmin hδ hcoverδ hΛ hσLip hNorm hchart hslow
  have hAUI := divergingPenalty_aui hHm hD hfour hsharp
  have htail := fun η hη ↦ uniform_tail_of_fourth_moment hHm hH0 hD hfour (η := η) hη
  have hlip := L.chartLipschitzTight hXm hlaw hIndep E.Ψ_ae_eq
  have happrox := divergingPenalty_jointError_tendstoInMeasure R
    (S := fun n ω w ↦ (n : ℝ) * empiricalLoss f Xs n ω w)
    hδ hcoverδ hσg hΛ hσLip haSeq ha hslow hH0 hNorm htail hlip hchart hŵW hmin
    (hsharp.mono fun n hn ↦ hn.mono fun ω hω ↦ hω.2.1)
  have hC : Continuous fun Ψ : C(ResolutionAtlas.Domain R, ℝ) ↦
      (ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedPenaltyMinimizers R σ) Ψ,
        -ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedPenaltyMinimizers R σ) Ψ) :=
    ResolutionAtlas.continuous_jointLikelihoodReward R _
        (ResolutionAtlas.isCompact_resolvedPenaltyMinimizers R hσg)
      (ResolutionAtlas.resolvedPenaltyMinimizers_nonempty R hσg)
  have hreward := E.tendsto.continuous_comp hC
  have hKm : Measurable K := measurable_K_of_integral hf I.K_eq
  have hGm := fun (n : ℕ) ↦ measurable_scaled_generalization hKm hŵ n
  have hTm := fun (n : ℕ) ↦ measurable_scaled_training hf hXm hŵ n
  have happrox' : TendstoInMeasure P
      ((fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω), (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω))) -
        (fun (n : ℕ) ω ↦ (ResolutionAtlas.likelihoodRewardSup R
            (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (E.Ψ n ω),
          -ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedPenaltyMinimizers R σ)
              (E.Ψ n ω)))) atTop 0 := by
    convert happrox using 1
    funext n ω
    exact Prod.ext rfl (sub_neg_eq_add _ _)
  have hjoint := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω), (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)))
    (fun ω' ↦ (ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedPenaltyMinimizers R σ)
        (E.Ψlim ω'),
      -ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedPenaltyMinimizers R σ)
          (E.Ψlim ω')))
    hreward happrox' (fun (n : ℕ) ↦ ((hGm n).prodMk (hTm n)).aemeasurable)
  have hGdist := hjoint.continuous_comp (g := Prod.fst) continuous_fst
  have hTdist := hjoint.continuous_comp (g := Prod.snd) continuous_snd
  refine ⟨hAUI.1.integrable_limit hGdist,
    mle_eventually_integrable_of_aui hf I.K_eq hXm hŵ hAUI.1 hAUI.2,
    hjoint, hAUI.1.tendsto_integral hGdist, ?_⟩
  simpa only [Function.comp_def, integral_neg] using hAUI.2.tendsto_integral hTdist

end SingularLearningTheory.MaximumLikelihood
