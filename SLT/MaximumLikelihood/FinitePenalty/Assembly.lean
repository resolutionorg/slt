/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.FinitePenalty.Approximation
import SLT.MaximumLikelihood.Penalty.Envelope
public import SLT.MaximumLikelihood.Penalty.Functionals
import SLT.MaximumLikelihood.Assembly
import SLT.MaximumLikelihood.Envelope
import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.FreeEnergy.FundamentalConditions

/-!
# Asymptotics of the estimator with a finite penalty

`SingularLearningTheory.MaximumLikelihood.finitePenalty_asymptotics` treats a measurable minimizer
$\hat w$ of $nK_n(w) + a_n\sigma(w)$ over a compact $W$, for penalty weights $a_n \ge 0$ converging
to $a$ and a penalty $\sigma$ that is $C^1$ on a neighborhood of $W$. The pair
$(nK(\hat w) - a\sigma(\hat w),\ nK_n(\hat w) + a\sigma(\hat w))$ converges in law to $(F, -F)$, and
both expectations converge. Here $F$ is
`SingularLearningTheory.ResolutionAtlas.penalizedLikelihoodRewardSup`, the supremum over the
resolved
zero set of $\max(0, -\Psi)^2/4 - a\sigma$ at the limit $\Psi$ of the empirical process, and it is
integrable. The hypotheses are fundamental condition (I) with moment index four, an analytic
resolved likelihood, and a resolution atlas whose charts cover a sublevel set of $K$. The proof
combines localization of the estimator, uniform integrability from a relative envelope with a
fourth moment, and convergence in probability of the pair to the reward at the empirical process.
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

/-- Finite penalty, joint law and both expectations, with moment index four. -/
theorem finitePenalty_asymptotics
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
    (aSeq : ℕ → ℝ) (haSeq : ∀ n, 0 ≤ aSeq n)
    (a : ℝ) (ha : Tendsto aSeq atTop (𝓝 a))
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤
        (n : ℝ) * empiricalLoss f Xs n ω w + aSeq n * σ w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) + a * σ (ŵ n ω)
    let F := fun ω' ↦ ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (E.Ψlim ω')
    Integrable F P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (F ω', -F ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', F ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', F ω' ∂P'))) := by
  dsimp only
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hlaw : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  have hσW : ContinuousOn σ W := hσ.continuousOn.mono hWU
  obtain ⟨wm, hwm, hmax⟩ := hW.exists_isMaxOn ⟨w₀, hw₀⟩ hσW.abs
  let Sg := |σ wm|
  have hSg : 0 ≤ Sg := abs_nonneg _
  have hσb : ∀ w ∈ W, |σ w| ≤ Sg := fun w hw ↦ hmax hw
  obtain ⟨hσg, Λ, hΛ, hσLip⟩ := ResolutionAtlas.chartPenalty_continuous_lipschitz R hWU hσ
  let A := |a| + 1
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have haA : a < A := by dsimp [A]; linarith [le_abs_self a]
  have hcap : ∀ᶠ n : ℕ in atTop, aSeq n ≤ A :=
    (ha.eventually (eventually_lt_nhds haA)).mono fun n hn ↦ hn.le
  obtain ⟨δ, hδ, hcoverδ⟩ := hcover
  obtain ⟨H, hHm, hH0, hNorm, ⟨D, hD, hfour⟩, henv⟩ :=
    exists_relative_envelope_fourth R I L hW (fun w ↦ hf.comp (measurable_id.prodMk measurable_const))
      hcont hδ hcoverδ hXm hlaw hIndep E
  have hloc := fun (n : ℕ) hn ↦ penalized_localization_ae hK0 hH0 henv hw₀ hw₀K
    hŵW haSeq hSg hσb hmin (n := n) hn
  have hAUI := finitePenalty_aui hK0 hH0 hHm hD hfour henv hw₀ hw₀K
    hŵW haSeq hA hSg hcap hσb hmin a
  have htail := fun η hη ↦ uniform_tail_of_fourth_moment hHm hH0 hD hfour (η := η) hη
  have hlip := L.chartLipschitzTight hXm hlaw hIndep E.Ψ_ae_eq
  have hchart := fun (n : ℕ) hn ↦ sampleLoss_chart_ae R L.toResolvedLikelihood hXm hlaw E (n := n) hn
  have happrox := finitePenalty_jointError_tendstoInMeasure R
    (S := fun n ω w ↦ (n : ℝ) * empiricalLoss f Xs n ω w)
    hδ hcoverδ hσg hΛ hSg hσLip hσb haSeq hA hcap ha hH0 hNorm htail hlip
    hchart hŵW hmin (fun n hn ↦ (hloc n hn).mono fun ω hω ↦ hω.2.1)
  have hC : Continuous fun Ψ : C(ResolutionAtlas.Domain R, ℝ) ↦
      (ResolutionAtlas.penalizedLikelihoodRewardSup R σ a Ψ,
          -ResolutionAtlas.penalizedLikelihoodRewardSup R σ a Ψ) :=
    ResolutionAtlas.continuous_jointPenalizedReward R (ResolutionAtlas.chartPenalty R σ) hσg a
  have hreward := E.tendsto.continuous_comp hC
  have hKm : Measurable K := measurable_K_of_integral hf I.K_eq
  have hσm := fun (n : ℕ) ↦ aestronglyMeasurable_penalty_comp hW hσW (hŵ n) (hŵW n)
  have hGm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω ↦ (n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω)) P := fun n ↦
    (measurable_scaled_generalization hKm hŵ n).aestronglyMeasurable.sub ((hσm n).const_mul a)
  have hTm : ∀ n : ℕ, AEStronglyMeasurable
      (fun ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) + a * σ (ŵ n ω)) P := fun n ↦
    (measurable_scaled_training hf hXm hŵ n).aestronglyMeasurable.add ((hσm n).const_mul a)
  have happrox' : TendstoInMeasure P
      ((fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω),
          (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) + a * σ (ŵ n ω))) -
        (fun (n : ℕ) ω ↦ (ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (E.Ψ n ω),
          -ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (E.Ψ n ω)))) atTop 0 := by
    convert happrox using 1
    funext n ω
    exact Prod.ext rfl (sub_neg_eq_add _ _)
  have hjoint := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω),
      (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) + a * σ (ŵ n ω)))
    (fun ω' ↦ (ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (E.Ψlim ω'),
      -ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (E.Ψlim ω')))
    hreward happrox' (fun (n : ℕ) ↦ ((hGm n).prodMk (hTm n)).aemeasurable)
  have hGdist := hjoint.continuous_comp (g := Prod.fst) continuous_fst
  have hTdist := hjoint.continuous_comp (g := Prod.snd) continuous_snd
  refine ⟨hAUI.1.integrable_limit hGdist,
    (hAUI.1.eventually_integrable hGm).and (hAUI.2.eventually_integrable hTm),
    hjoint, hAUI.1.tendsto_integral hGdist, ?_⟩
  simpa only [Function.comp_def, integral_neg] using hAUI.2.tendsto_integral hTdist

end SingularLearningTheory.MaximumLikelihood
