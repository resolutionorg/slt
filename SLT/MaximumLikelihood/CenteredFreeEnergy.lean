/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.CoveredOptimization
public import SLT.Resolution.OptimizerProcess
public import SLT.FreeEnergy.Main
public import SLT.EmpiricalProcess.ProductSpace
import SLT.MaximumLikelihood.Envelope
public import SLT.MaximumLikelihood.Geometry
public import SLT.Resolution.Assembly
import SLT.FreeEnergy.Discharge

/-!
# Free energy centered at maximum likelihood

A common empirical process couples the prior atlas to all optimizer coordinate
faces. Joint evidence/training convergence supplies the centered law; pointwise
subtraction cancels the baseline before expectations are taken.
-/

public section

namespace SingularLearningTheory.MaximumLikelihood

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

section ProbabilityHelpers

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'}

/-- Two real errors converging to zero jointly converge to zero as a pair. -/
private theorem tendstoInMeasure_pair_zero {a b : ℕ → Ω → ℝ}
    (ha : TendstoInMeasure P a atTop 0) (hb : TendstoInMeasure P b atTop 0) :
    TendstoInMeasure P (fun n ω ↦ (a n ω, b n ω)) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at ha hb ⊢
  intro ε hε
  have hlim : Tendsto (fun n ↦ P {ω | ε ≤ ‖a n ω - 0‖} + P {ω | ε ≤ ‖b n ω - 0‖})
      atTop (𝓝 0) := by simpa using (ha ε hε).add (hb ε hε)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ ↦ bot_le) fun n ↦ ?_
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω hω
  simpa only [Set.mem_union, Set.mem_ofPred_eq, Pi.zero_apply, sub_zero, Prod.norm_mk, le_max_iff] using hω

/-- A coordinate of a vanishing pair error also vanishes. -/
private theorem tendstoInMeasure_snd_zero {f : ℕ → Ω → ℝ × ℝ}
    (hf : TendstoInMeasure P f atTop 0) :
    TendstoInMeasure P (fun n ω ↦ (f n ω).2) atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hf ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hf ε hε)
    (fun _ ↦ bot_le) fun n ↦ measure_mono fun ω hω ↦ ?_
  simp only [Set.mem_ofPred_eq, Pi.zero_apply, sub_zero] at hω ⊢
  exact hω.trans (norm_snd_le _)

variable [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Distributional limits ignore an eventual almost-sure modification. -/
theorem _root_.MeasureTheory.tendstoInDistribution_of_eventually_ae_eq
    {X Y : ℕ → Ω → ℝ} {Z : Ω' → ℝ}
    (h : TendstoInDistribution X atTop Z (fun _ ↦ P) P')
    (hYm : ∀ n : ℕ, AEMeasurable (Y n) P)
    (hXY : ∀ᶠ n : ℕ in atTop, X n =ᵐ[P] Y n) :
    TendstoInDistribution Y atTop Z (fun _ ↦ P) P' where
  forall_aemeasurable := hYm
  aemeasurable_limit := h.aemeasurable_limit
  tendsto := h.tendsto.congr' (by
    filter_upwards [hXY] with n hn
    exact ProbabilityMeasure.toMeasure_injective (Measure.map_congr hn))

/-- Joint evidence/training convergence gives the centered law using the
existing scalar positive-limit logarithm theorem. -/
private theorem centered_log_of_joint_evidence_training
    {Z T : ℕ → Ω → ℝ} {Y M : Ω' → ℝ}
    (hjoint : TendstoInDistribution (fun (n : ℕ) ω ↦ (Z n ω, T n ω)) atTop
      (fun ω' ↦ (Y ω', -M ω')) (fun _ ↦ P) P')
    (hY : ∀ ω', 0 < Y ω') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ -Real.log (Z n ω * Real.exp (T n ω))) atTop
      (fun ω' ↦ -Real.log (Y ω') + M ω') (fun _ ↦ P) P' := by
  have hprod := hjoint.continuous_comp
    (g := fun v : ℝ × ℝ ↦ v.1 * Real.exp v.2) (by fun_prop)
  have hlog := tendstoInDistribution_comp_of_continuousOn_Ioi
    (g := fun x ↦ -Real.log x) hprod
    (Real.continuousOn_log.mono fun _ hx ↦ ne_of_gt hx).neg Real.measurable_log.neg
    (Filter.Eventually.of_forall fun ω' ↦ mul_pos (hY ω') (Real.exp_pos _))
  have hlim : (fun ω' ↦ -Real.log (Y ω' * Real.exp (-M ω'))) =
      fun ω' ↦ -Real.log (Y ω') + M ω' := by
    funext ω'
    rw [Real.log_mul (hY ω').ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  simpa only [Function.comp_apply, hlim] using hlog

end ProbabilityHelpers

section CoupledInputs

variable {d : ℕ} {K φ φo : (Fin d → ℝ) → ℝ} {W Wo : Set (Fin d → ℝ)}
  (R : NondegenerateResolutionAtlas K φ W) (Ro : ResolutionAtlas K φo Wo)
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  (J : R.toResolutionAtlas.IntegrableEmpiricalProcessInput 1 P P')

/-- Joint FE/MLE assembly. The supplied common chart field determines both
functionals; expectation convergence follows by subtraction after integrability. -/
private theorem centered_freeEnergy_of_coupled_inputs
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    {Ψ : ℕ → Ω → C(ResolutionAtlas.Domain Ro, ℝ)} {Ψlim : Ω' → C(ResolutionAtlas.Domain Ro, ℝ)}
    (hΨ : TendstoInDistribution Ψ atTop Ψlim (fun _ ↦ P) P')
    (Q : C(ResolutionAtlas.Domain Ro, ℝ) → R.ChartFunctions) (hQ : Continuous Q)
    (hΞ : ∀ (n : ℕ) ω, J.Ξ n ω = Q (Ψ n ω))
    (hΞlim : ∀ ω', J.Ξlim ω' = Q (Ψlim ω'))
    (M : C(ResolutionAtlas.Domain Ro, ℝ) → ℝ) (hM : Continuous M)
    (hMi : Integrable (fun ω' ↦ M (Ψlim ω')) P')
    (T : ℕ → Ω → ℝ) (hTm : ∀ n : ℕ, AEMeasurable (T n) P)
    (hTi : ∀ᶠ n : ℕ in atTop, Integrable (T n) P)
    (hTerr : TendstoInMeasure P (fun (n : ℕ) ω ↦ T n ω + M (Ψ n ω)) atTop 0)
    (hTmean : Tendsto (fun n : ℕ ↦ ∫ ω, T n ω ∂P) atTop
      (𝓝 (-(∫ ω', M (Ψlim ω') ∂P')))) :
    let Rlim := fun ω' ↦ -Real.log (R.limitFunctional 1 (J.Ξlim ω')) + M (Ψlim ω')
    Integrable Rlim P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (fun ω ↦ J.toEmpiricalProcessInput.Rn n ω - T n ω) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ J.toEmpiricalProcessInput.Rn n ω - T n ω)
        atTop Rlim (fun _ ↦ P) P' ∧
      Tendsto (fun n : ℕ ↦ ∫ ω, J.toEmpiricalProcessInput.Rn n ω - T n ω ∂P) atTop
        (𝓝 (∫ ω', Rlim ω' ∂P')) := by
  dsimp only
  have hLip := fun α (_ : R.IsEssential α) ↦ R.toResolutionAtlas.exists_lipschitzOnWith_weight α
  let Z : ℕ → Ω → ℝ := fun n ω ↦
    (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * J.toEmpiricalProcessInput.normalizedEvidence n ω
  let Y : C(ResolutionAtlas.Domain Ro, ℝ) → ℝ := fun ψ ↦ R.limitFunctional 1 (Q ψ)
  have hY : Continuous Y := (R.continuous_limitFunctional zero_lt_one).comp hQ
  have hZerr : TendstoInMeasure P (fun (n : ℕ) ω ↦ Z n ω - Y (Ψ n ω)) atTop 0 := by
    simpa only [Z, Y, hΞ] using
      J.toEmpiricalProcessInput.tendstoInMeasure_normalizedEvidence_sub_limitFunctional hW hφ hφi
          zero_lt_one hLip
  have hpairerr : TendstoInMeasure P
      ((fun (n : ℕ) ω ↦ (Z n ω, T n ω)) -
        (fun (n : ℕ) ω ↦ (Y (Ψ n ω), -M (Ψ n ω)))) atTop 0 := by
    convert tendstoInMeasure_pair_zero hZerr hTerr using 1
    funext n ω
    exact Prod.ext rfl (sub_neg_eq_add _ _)
  have hbase := hΨ.continuous_comp (hY.prodMk hM.neg)
  have hZm : ∀ n : ℕ, AEMeasurable (Z n) P := fun n ↦
    measurable_const.aemeasurable.mul
        (J.toEmpiricalProcessInput.aemeasurable_normalizedEvidence hφi n)
  have hpair := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun (n : ℕ) ω ↦ (Z n ω, T n ω)) (fun ω' ↦ (Y (Ψlim ω'), -M (Ψlim ω')))
    hbase hpairerr (fun n ↦ (hZm n).prodMk (hTm n))
  have hlog : TendstoInDistribution
      (fun (n : ℕ) ω ↦ -Real.log (Z n ω * Real.exp (T n ω))) atTop
      (fun ω' ↦ -Real.log (R.limitFunctional 1 (J.Ξlim ω')) + M (Ψlim ω'))
      (fun _ ↦ P) P' := by
    simpa only [Y, hΞlim] using centered_log_of_joint_evidence_training hpair
      (fun ω' ↦ R.limitFunctional_pos zero_lt_one (Q (Ψlim ω')))
  have heq : ∀ᶠ n : ℕ in atTop,
      (fun ω ↦ -Real.log (Z n ω * Real.exp (T n ω))) =ᵐ[P]
        fun ω ↦ J.toEmpiricalProcessInput.Rn n ω - T n ω := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    filter_upwards [R.normalizedEvidence_pos J.toEmpiricalProcessInput hW hφ hφi zero_lt_one hn]
        with ω hZω
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hlogn : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hZpos : 0 < Z n ω :=
      mul_pos (div_pos (Real.rpow_pos_of_pos hn0 _) (pow_pos hlogn _)) hZω
    change -Real.log (Z n ω * Real.exp (T n ω)) = -Real.log (Z n ω) - T n ω
    rw [Real.log_mul hZpos.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring
  have hLaw := tendstoInDistribution_of_eventually_ae_eq hlog
    (fun n ↦ (J.toEmpiricalProcessInput.aestronglyMeasurable_Rn hφi n).aemeasurable.sub (hTm n)) heq
  have hFEaui := R.asympUnifIntegrable_Rn J hW hφ hφi zero_lt_one
  have hFElaw := R.free_energy_formula J.toEmpiricalProcessInput hW hφ hφi zero_lt_one hLip
  have hFEi := hFEaui.integrable_limit hFElaw
  have hFEni := hFEaui.eventually_integrable (J.toEmpiricalProcessInput.aestronglyMeasurable_Rn hφi)
  refine ⟨hFEi.add hMi, ?_, hLaw, ?_⟩
  · filter_upwards [hFEni, hTi] with n hn ht
    exact hn.sub ht
  · have hm := (R.tendsto_integral_Rn J hW hφ hφi zero_lt_one hLip).sub hTmean
    have htarget : (∫ ω', -Real.log (R.limitFunctional 1 (J.Ξlim ω')) ∂P') -
        (-(∫ ω', M (Ψlim ω') ∂P')) =
        ∫ ω', -Real.log (R.limitFunctional 1 (J.Ξlim ω')) + M (Ψlim ω') ∂P' := by
      rw [integral_add hFEi hMi]
      ring
    rw [htarget] at hm
    apply hm.congr'
    filter_upwards [hFEni, hTi] with n hn ht
    exact (integral_sub hn ht).symm

end CoupledInputs
end SingularLearningTheory.MaximumLikelihood

namespace SingularLearningTheory.AtlasData

open MeasureTheory ProbabilityTheory Set Filter Topology MaximumLikelihood
open scoped ENNReal

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (A : AtlasData K φ W) [Nonempty A.ι]
  {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {f : X → (Fin d → ℝ) → ℝ}

/-- Assemble a centered law from already chosen common optimizer and tail
processes. Keeping these as parameters prevents product-space constructors from
being repeatedly unfolded while checking the free-energy input. -/
private theorem centered_at_maximumLikelihood_of_commonProcesses
    (I : FundamentalConditionI 4 q f K W) (hf : Measurable (Function.uncurry f))
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    {C : ℝ} (hC : 0 < C) (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (Xs : ℕ → Ω → X) (hX : ∀ i, MeasurePreserving (Xs i) P q) (hIndep : iIndepFun Xs P)
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n : ℕ, Measurable (ŵ n))
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalLoss f Xs n ω (ŵ n ω) ≤ empiricalLoss f Xs n ω w)
    (Lo : A.optimizerAtlas.AnalyticResolvedLikelihood 4 q f)
    {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    (E : EmpiricalProcessLimit q
      (fun x (v : ResolutionAtlas.Domain A.optimizerAtlas) ↦ Lo.a v.1 x v.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ A.toResolutionAtlas.δ ≤ K w}) ↦
        f x w / Real.sqrt (K w)) Xs P P') :
    let Rp := A.toResolutionAtlas
    let Rn := fun (n : ℕ) ω ↦
      -Real.log ((n : ℝ) ^ Rp.rlct / Real.log n ^ (Rp.mult - 1) *
        ∫ w in W, Real.exp (-((n : ℝ) * empiricalLoss f Xs n ω w)) * φ w) -
      (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)
    ∃ (Rlim : Ω' → ℝ), Integrable Rlim P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (Rn n) P) ∧
      TendstoInDistribution Rn atTop Rlim (fun _ ↦ P) P' ∧
      Tendsto (fun n : ℕ ↦ ∫ ω, Rn n ω ∂P) atTop (𝓝 (∫ ω', Rlim ω' ∂P')) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P,
        0 < ∫ w in W, Real.exp (-((n : ℝ) * empiricalLoss f Xs n ω w)) * φ w) := by
  classical
  let Ro : ResolutionAtlas K (fun _ ↦ 0) W := A.optimizerAtlas
  let Rp : NondegenerateResolutionAtlas K φ W := A.toNondegenerateResolutionAtlas
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hlaw : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  let Lp : A.toResolutionAtlas.AnalyticResolvedLikelihood 4 q f :=
    A.priorLikelihoodOfOptimizer Lo
  let Ep : EmpiricalProcessLimit q
      (fun x (v : ResolutionAtlas.Domain A.toResolutionAtlas) ↦ Lp.a v.1 x v.2) Xs P P' :=
    A.priorProcessOfOptimizer Lo E
  let J : A.toResolutionAtlas.IntegrableEmpiricalProcessInput 1 P P' :=
    Lp.toResolvedLikelihood.integrableEmpiricalProcessInput 1 P P'
    hXm hlaw hf I.K_eq (I.isCompact_tail A.W_compact A.toResolutionAtlas.δ) Ep
    (Lp.primaryLipschitzTight hXm hlaw hIndep Ep.Ψ_ae_eq) T
    (Lp.momentBound_chart hXm hlaw hIndep Ep)
    (I.momentBound_tail A.W_compact hcont A.toResolutionAtlas.δ_pos hXm hlaw hIndep T)
  obtain ⟨hMi, hInt, -, -, hTmean, hApprox⟩ := maximumLikelihood_asymptotics_of_positive_cover
    Ro I Lo hf A.W_compact A.K_nonneg hcont hRFV A.optimizerAtlas_cover_pos
    hX hIndep E ŵ hŵ hŵW hmin
  let Q : C(ResolutionAtlas.Domain Ro, ℝ) → A.toResolutionAtlas.ChartFunctions :=
    fun ψ ↦ -(A.toResolutionAtlas.toChartFunctions (ψ.comp A.optimizerPriorInclusion))
  have hQ : Continuous Q :=
    (A.toResolutionAtlas.continuous_toChartFunctions.comp
      (ContinuousMap.continuous_precomp A.optimizerPriorInclusion)).neg
  have hM : Continuous (ResolutionAtlas.likelihoodRewardSup Ro
      (ResolutionAtlas.resolvedZeroSet Ro)) :=
    ResolutionAtlas.continuous_likelihoodRewardSup Ro _ (ResolutionAtlas.isCompact_resolvedZeroSet
        Ro) (ResolutionAtlas.resolvedZeroSet_nonempty Ro)
  have hΞ : ∀ (n : ℕ) ω, J.Ξ n ω = Q (E.Ψ n ω) := fun _ _ ↦ rfl
  have hΞlim : ∀ ω', J.Ξlim ω' = Q (E.Ψlim ω') := fun _ ↦ rfl
  have hTm : ∀ n : ℕ, AEMeasurable
      (fun ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)) P :=
    fun n ↦ (measurable_scaled_training hf hXm hŵ n).aemeasurable
  have hTi : ∀ᶠ n : ℕ in atTop, Integrable
      (fun ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)) P :=
    hInt.mono fun _ h ↦ h.2
  have hTerr : TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) +
        ResolutionAtlas.likelihoodRewardSup Ro (ResolutionAtlas.resolvedZeroSet Ro) (E.Ψ n ω)) atTop
            0 :=
    tendstoInMeasure_snd_zero (f := fun (n : ℕ) ω ↦
      ((n : ℝ) * K (ŵ n ω) - ResolutionAtlas.likelihoodRewardSup Ro
          (ResolutionAtlas.resolvedZeroSet Ro) (E.Ψ n ω),
        (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) +
          ResolutionAtlas.likelihoodRewardSup Ro (ResolutionAtlas.resolvedZeroSet Ro) (E.Ψ n ω)))
              hApprox
  have hmain := centered_freeEnergy_of_coupled_inputs Rp Ro J
    (Ψ := E.Ψ) (Ψlim := E.Ψlim)
    A.W_compact.measurableSet hφ hφi E.tendsto Q hQ hΞ hΞlim
    (ResolutionAtlas.likelihoodRewardSup Ro (ResolutionAtlas.resolvedZeroSet Ro)) hM hMi
    (fun (n : ℕ) ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω))
    hTm hTi hTerr hTmean
  have hpos : ∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P, 0 < J.toEmpiricalProcessInput.normalizedEvidence n ω :=
    fun n hn ↦ Rp.normalizedEvidence_pos J.toEmpiricalProcessInput
      A.W_compact.measurableSet hφ hφi zero_lt_one hn
  have hKn : ∀ (n : ℕ) ω w, J.Kn n ω w = empiricalLoss f Xs n ω w :=
    fun _ _ _ ↦ rfl
  have hrlct : Rp.rlct = A.toResolutionAtlas.rlct := rfl
  have hmult : Rp.mult = A.toResolutionAtlas.mult := rfl
  refine ⟨fun ω' ↦ -Real.log (Rp.limitFunctional 1 (J.Ξlim ω')) +
    ResolutionAtlas.likelihoodRewardSup Ro (ResolutionAtlas.resolvedZeroSet Ro) (E.Ψlim ω'), ?_⟩
  simpa only [ResolutionAtlas.EmpiricalProcessInput.Rn,
    ResolutionAtlas.EmpiricalProcessInput.normalizedEvidence, hKn, hrlct, hmult, mul_one] using
    And.intro hmain.1 (And.intro hmain.2.1
      (And.intro hmain.2.2.1 (And.intro hmain.2.2.2 hpos)))

/-- The centered free energy under the semianalytic atlas data. The optimizer family and its
coverage, including thin feasible strata, are constructed in the proof; the prior atlas supplies
λ and m. -/
theorem centered_at_maximumLikelihood
    (I : FundamentalConditionI 4 q f K W) (hf : Measurable (Function.uncurry f))
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    {C : ℝ} (hC : 0 < C) (hRFV : ∀ w ∈ W, ∫ x, f x w ^ 2 ∂q ≤ C⁻¹ * K w)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (Xs : ℕ → Ω → X) (hX : ∀ i, MeasurePreserving (Xs i) P q) (hIndep : iIndepFun Xs P)
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n : ℕ, Measurable (ŵ n))
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalLoss f Xs n ω (ŵ n ω) ≤ empiricalLoss f Xs n ω w) :
    let Rp := A.toResolutionAtlas
    let Rn := fun (n : ℕ) ω ↦
      -Real.log ((n : ℝ) ^ Rp.rlct / Real.log n ^ (Rp.mult - 1) *
        ∫ w in W, Real.exp (-((n : ℝ) * empiricalLoss f Xs n ω w)) * φ w) -
      (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (Rlim : Ω' → ℝ), Integrable Rlim P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (Rn n) P) ∧
      TendstoInDistribution Rn atTop Rlim (fun _ ↦ P) P' ∧
      Tendsto (fun n : ℕ ↦ ∫ ω, Rn n ω ∂P) atTop (𝓝 (∫ ω', Rlim ω' ∂P')) ∧
      (∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P,
        0 < ∫ w in W, Real.exp (-((n : ℝ) * empiricalLoss f Xs n ω w)) * φ w) := by
  classical
  let Ro : ResolutionAtlas K (fun _ ↦ 0) W := A.optimizerAtlas
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hlaw : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  have hfa : LsValuedAnalytic 4 q f W := I.ls_analytic
  have hcontg : ∀ᵐ x ∂q, ∀ α, Continuous fun u : cube d (Ro.b α) ↦ f x (Ro.g α u) := by
    filter_upwards [hcont] with x hx α
    exact hx.comp_continuous ((Ro.g_analytic α).continuousOn.comp_continuous continuous_subtype_val
      fun u ↦ u.2) fun u ↦ Ro.g_mapsTo α u.2
  obtain ⟨Lo⟩ := Ro.exists_analyticResolvedLikelihood I.two_le I.K_eq hfa hC hRFV hcontg
  obtain ⟨P₁, hP₁, ⟨E₀⟩⟩ := Lo.exists_empiricalProcessLimit_chart hXm hlaw hIndep
  obtain ⟨P₂, hP₂, ⟨T₀⟩⟩ := I.exists_tail_empiricalProcessLimit A.W_compact
    (fun w ↦ hf.comp (measurable_id.prodMk measurable_const)) hcont
    A.toResolutionAtlas.δ_pos hXm hlaw hIndep
  let := hP₁
  let := hP₂
  obtain ⟨Rlim, hlim⟩ := centered_at_maximumLikelihood_of_commonProcesses A
    I hf hcont hC hRFV hφ hφi Xs hX hIndep ŵ hŵ hŵW hmin Lo
    (E₀.prodFst (P₂ := P₂)) (T₀.prodSnd (P₁ := P₁))
  exact ⟨_, inferInstance, P₁.prod P₂, inferInstance, Rlim, hlim⟩

end SingularLearningTheory.AtlasData
