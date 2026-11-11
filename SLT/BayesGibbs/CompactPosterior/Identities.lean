/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CompactBase.GaussianStein
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import SLT.BayesGibbs.CompactBase.Finite
import SLT.BayesGibbs.RadialMoments
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# CompactPosteriorIdentities

Radial and general-covariance Stein identities for the limiting quartet.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.GaussianPosterior

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K] (ρ : Measure K) [IsFiniteMeasure ρ]
  {β lam : ℝ}

/-- Integration is continuous on C(K); only local sup-norm domination is needed,
so no false local-compactness assumption on the function space is introduced. -/
private theorem continuous_integral_on_continuousMap : Continuous
    (fun F : C(K, ℝ) ↦ ∫ x, F x ∂ρ) := by
  rw [continuous_iff_continuousAt]
  intro F₀
  refine continuousAt_of_dominated
    (bound := fun _ : K ↦ ‖F₀‖ + 1)
    (Eventually.of_forall fun F ↦ F.continuous.measurable.aestronglyMeasurable) ?_
    (integrable_const _) (Eventually.of_forall fun x ↦ (show Continuous (fun F : C(K, ℝ) ↦ F x) from continuous_eval_const x).continuousAt)
  filter_upwards [(continuous_norm.tendsto F₀).eventually
    (eventually_lt_nhds (show ‖F₀‖ < ‖F₀‖ + 1 by linarith))] with F hF
  exact Eventually.of_forall fun x ↦ (F.norm_coe_le_norm x).trans hF.le

private theorem continuous_frozen_postcomp (hβ : 0 < β) (hlam : 0 < lam) :
    Continuous (fun g : C(K, ℝ) ↦
      (⟨fun x ↦ frozenInner lam β (g x),
        (continuous_frozenInner hlam hβ).comp g.continuous⟩ : C(K, ℝ))) :=
  ContinuousMap.continuous_postcomp
    ⟨frozenInner lam β, continuous_frozenInner hlam hβ⟩

theorem continuous_compactD (hβ : 0 < β) (hlam : 0 < lam) :
    Continuous (fun g : C(K, ℝ) ↦ compactD β lam ρ g) :=
  (continuous_integral_on_continuousMap ρ).comp (continuous_frozen_postcomp hβ hlam)

theorem continuous_compactM2 (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) :
    Continuous (fun g : C(K, ℝ) ↦ compactM2 β lam ρ g) :=
  (continuous_compactD ρ hβ (by linarith : 0 < lam + 1)).div
    (continuous_compactD ρ hβ hlam) (fun g ↦ (compactD_pos ρ hβ hlam hρ g).ne')

theorem continuous_compactH (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) :
    Continuous (fun g : C(K, ℝ) ↦ compactH β lam ρ g) := by
  have hN := (continuous_integral_on_continuousMap ρ).comp
    (continuous_id.mul (continuous_frozen_postcomp hβ (by linarith : 0 < lam + 1 / 2)))
  exact hN.div (continuous_compactD ρ hβ hlam) (fun g ↦ (compactD_pos ρ hβ hlam hρ g).ne')

theorem continuous_compactDiag (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (𝒞 : PSDKernel K) :
    Continuous (fun g : C(K, ℝ) ↦ compactDiag ρ β lam 𝒞 g) := by
  let Dg : C(K, ℝ) := ⟨fun x ↦ 𝒞.C x x, 𝒞.continuous_diag⟩
  have hc : Continuous (fun _ : C(K, ℝ) ↦ Dg) := continuous_const
  have hN := (continuous_integral_on_continuousMap ρ).comp
    (hc.mul (continuous_frozen_postcomp hβ (by linarith : 0 < lam + 1)))
  exact hN.div (continuous_compactD ρ hβ hlam) (fun g ↦ (compactD_pos ρ hβ hlam hρ g).ne')

theorem continuous_compactQnum (hβ : 0 < β) (hlam : 0 < lam) (𝒞 : PSDKernel K) :
    Continuous (fun g : C(K, ℝ) ↦ compactQnum ρ β lam 𝒞 g) := by
  let Ck : C(K × K, ℝ) := ⟨Function.uncurry 𝒞.C, 𝒞.continuous⟩
  let p₁ : C(K × K, K) := ⟨Prod.fst, continuous_fst⟩
  let p₂ : C(K × K, K) := ⟨Prod.snd, continuous_snd⟩
  have hS := continuous_frozen_postcomp (K := K) hβ (by linarith : 0 < lam + 1 / 2)
  have h₁ := (ContinuousMap.continuous_precomp p₁).comp hS
  have h₂ := (ContinuousMap.continuous_precomp p₂).comp hS
  have hc : Continuous (fun _ : C(K, ℝ) ↦ Ck) := continuous_const
  exact (continuous_integral_on_continuousMap (ρ.prod ρ)).comp ((hc.mul h₁).mul h₂)

theorem continuous_compactV (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (𝒞 : PSDKernel K) :
    Continuous (fun g : C(K, ℝ) ↦ compactV ρ β lam 𝒞 g) :=
  (continuous_compactDiag ρ hβ hlam hρ 𝒞).sub
    ((continuous_compactQnum ρ hβ hlam 𝒞).div ((continuous_compactD ρ hβ hlam).pow 2)
      (fun g ↦ pow_ne_zero _ (compactD_pos ρ hβ hlam hρ g).ne'))

/-- The radial integration-by-parts identity on an arbitrary finite compact base. -/
private theorem compactM2_eq_compactH_half_add (hβ : 0 < β) (hlam : 0 < lam)
    (hρ : ρ ≠ 0) (g : C(K, ℝ)) :
    compactM2 β lam ρ g = compactH β lam ρ g / 2 + lam / β := by
  have hD := (compactD_pos ρ hβ hlam hρ g).ne'
  have hIh : Integrable (fun x ↦ g x * frozenInner (lam + 1 / 2) β (g x)) ρ :=
    Continuous.integrable_of_compactSpace ρ
      (g.continuous.mul ((continuous_frozenInner (by linarith) hβ).comp g.continuous))
  have hI0 := integrable_fluctuation_comp ρ hβ hlam g
  have heq : (∫ x, frozenInner (lam + 1) β (g x) ∂ρ) =
      (∫ x, g x * frozenInner (lam + 1 / 2) β (g x) ∂ρ) / 2 +
        (lam / β) * compactD β lam ρ g := by
    calc (∫ x, frozenInner (lam + 1) β (g x) ∂ρ) =
        ∫ x, (g x * frozenInner (lam + 1 / 2) β (g x)) / 2 +
          (lam / β) * frozenInner lam β (g x) ∂ρ := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x ↦ by dsimp only; rw [fluctuation_recurrence β lam hβ hlam (g x)]; ring
      _ = _ := by rw [integral_add (hIh.div_const 2) (hI0.const_mul _), integral_div, integral_const_mul]; rfl
  unfold compactM2 compactH
  rw [heq]
  field_simp [hD]

theorem two_mul_compactM2_sub_compactH (hβ : 0 < β) (hlam : 0 < lam)
    (hρ : ρ ≠ 0) (g : C(K, ℝ)) :
    2 * compactM2 β lam ρ g - compactH β lam ρ g = 2 * lam / β := by
  rw [compactM2_eq_compactH_half_add ρ hβ hlam hρ g]
  ring

/-- Order: Bayes generalization, Bayes training, Gibbs generalization, Gibbs training.
The connected covariance functional replaces every constant-diagonal shortcut. -/
@[expose] noncomputable def compactQuartet (β lam : ℝ) (𝒞 : PSDKernel K)
    (g : C(K, ℝ)) : Fin 4 → ℝ :=
  ![compactM2 β lam ρ g - compactV ρ β lam 𝒞 g / 2,
    compactM2 β lam ρ g - compactH β lam ρ g - compactV ρ β lam 𝒞 g / 2,
    compactM2 β lam ρ g,
    compactM2 β lam ρ g - compactH β lam ρ g]

theorem continuous_compactQuartet (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (𝒞 : PSDKernel K) :
    Continuous (compactQuartet ρ β lam 𝒞) := by
  have hT := continuous_compactM2 ρ hβ hlam hρ
  have hH := continuous_compactH ρ hβ hlam hρ
  have hV := continuous_compactV ρ hβ hlam hρ 𝒞
  apply continuous_pi
  intro j
  fin_cases j <;> simp only [compactQuartet, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three] <;> fun_prop

section Gaussian
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒞 : PSDKernel K} (Γ : GaussianField 𝒞 P)

/-- On a compact metric base, measurable evaluations give a measurable C(K)-field. -/
theorem _root_.ProbabilityTheory.GaussianField.measurable_field : Measurable Γ.G :=
  ContinuousMap.measurable_iff_eval.mpr Γ.measurable_eval

theorem _root_.ProbabilityTheory.GaussianField.integrable_compactH (hβ : 0 < β) (hlam : 0 < lam)
    (hρ : ρ ≠ 0) :
    Integrable (fun ω ↦ compactH β lam ρ (Γ.G ω)) P := by
  have hm := (continuous_compactH ρ hβ hlam hρ).measurable.comp Γ.measurable_field
  apply (integrable_const_mul_one_add_sq P Γ.G Γ.integrable_sq_norm
    (Real.sqrt (2 * lam / β) + 1 / 2)).mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun ω ↦ ?_
  rw [Real.norm_eq_abs]
  refine (abs_compactH_le ρ hβ hlam (Γ.G ω) hρ le_rfl).trans ?_
  nlinarith [norm_nonneg (Γ.G ω), sq_nonneg (‖Γ.G ω‖ - 1), Real.sqrt_nonneg (2 * lam / β)]

theorem _root_.ProbabilityTheory.GaussianField.integrable_compactV (hβ : 0 < β) (hlam : 0 < lam)
    (hρ : ρ ≠ 0) :
    Integrable (fun ω ↦ compactV ρ β lam 𝒞 (Γ.G ω)) P := by
  obtain ⟨c, hc0, hc⟩ := 𝒞.exists_diag_bound
  have hm := (continuous_compactV ρ hβ hlam hρ 𝒞).measurable.comp Γ.measurable_field
  apply (integrable_const_mul_one_add_sq P Γ.G Γ.integrable_sq_norm
    (c * (2 * lam / β + 1 / 4))).mono' hm.aestronglyMeasurable
  refine Eventually.of_forall fun ω ↦ ?_
  dsimp only [Function.comp_def]
  rw [Real.norm_eq_abs, abs_of_nonneg (compactV_nonneg ρ hβ hlam 𝒞 (Γ.G ω) hρ)]
  refine (compactV_le ρ hβ hlam 𝒞 (Γ.G ω) hρ hc le_rfl).trans ?_
  have hb : 0 ≤ 2 * lam / β := by positivity
  nlinarith [norm_nonneg (Γ.G ω), sq_nonneg ‖Γ.G ω‖, mul_nonneg hc0 hb,
    mul_nonneg hc0 (sq_nonneg ‖Γ.G ω‖)]

theorem _root_.ProbabilityTheory.GaussianField.integrable_compactM2 (hβ : 0 < β) (hlam : 0 < lam)
    (hρ : ρ ≠ 0) :
    Integrable (fun ω ↦ compactM2 β lam ρ (Γ.G ω)) P := by
  have hi := ((Γ.integrable_compactH ρ hβ hlam hρ).div_const 2).add (integrable_const (lam / β))
  exact hi.congr (Eventually.of_forall fun ω ↦ (compactM2_eq_compactH_half_add ρ hβ hlam hρ (Γ.G ω)).symm)

/-- General-covariance expected coefficients. The singular fluctuation is β E[V]/2.
This theorem makes no assertion that the covariance diagonal is constant. -/
theorem _root_.ProbabilityTheory.GaussianField.expected_compactQuartet (hβ : 0 < β) (hlam : 0 < lam)
    (hρ : ρ ≠ 0) :
    ∃ ν : ℝ, 0 ≤ ν ∧
      (∀ j : Fin 4, Integrable (fun ω ↦ compactQuartet ρ β lam 𝒞 (Γ.G ω) j) P) ∧
      (∫ ω, compactV ρ β lam 𝒞 (Γ.G ω) ∂P) = 2 * ν / β ∧
      ∀ j : Fin 4, (∫ ω, compactQuartet ρ β lam 𝒞 (Γ.G ω) j ∂P) =
        ![lam / β + (1 - 1 / β) * ν, lam / β - (1 + 1 / β) * ν,
          lam / β + ν, lam / β - ν] j := by
  let ν := β / 2 * ∫ ω, compactV ρ β lam 𝒞 (Γ.G ω) ∂P
  have hν : 0 ≤ ν := mul_nonneg (by positivity)
    (integral_nonneg fun ω ↦ compactV_nonneg ρ hβ hlam 𝒞 (Γ.G ω) hρ)
  have hV := Γ.integrable_compactV ρ hβ hlam hρ
  have hH := Γ.integrable_compactH ρ hβ hlam hρ
  have hT := Γ.integrable_compactM2 ρ hβ hlam hρ
  have hEV : (∫ ω, compactV ρ β lam 𝒞 (Γ.G ω) ∂P) = 2 * ν / β := by
    dsimp [ν]
    field_simp [hβ.ne']
  have hEH : (∫ ω, compactH β lam ρ (Γ.G ω) ∂P) = 2 * ν := by
    rw [Γ.integral_compactH_eq ρ hβ hlam hρ]
    dsimp [ν]
    ring
  have hET : (∫ ω, compactM2 β lam ρ (Γ.G ω) ∂P) = lam / β + ν := by
    have heq : (fun ω ↦ compactM2 β lam ρ (Γ.G ω)) =
        fun ω ↦ compactH β lam ρ (Γ.G ω) / 2 + lam / β :=
      funext fun ω ↦ compactM2_eq_compactH_half_add ρ hβ hlam hρ (Γ.G ω)
    rw [heq, integral_add (hH.div_const 2) (integrable_const _), integral_div, hEH]
    simp
    ring
  have hTH : Integrable (fun ω ↦ compactM2 β lam ρ (Γ.G ω) - compactH β lam ρ (Γ.G ω)) P :=
    (hT.sub hH).congr (Eventually.of_forall fun _ ↦ rfl)
  refine ⟨ν, hν, ?_, hEV, ?_⟩
  · intro j
    fin_cases j
    · change Integrable (fun ω ↦ compactM2 β lam ρ (Γ.G ω) - compactV ρ β lam 𝒞 (Γ.G ω) / 2) P
      exact (hT.sub (hV.div_const 2)).congr (Eventually.of_forall fun _ ↦ rfl)
    · change Integrable (fun ω ↦ compactM2 β lam ρ (Γ.G ω) - compactH β lam ρ (Γ.G ω) - compactV ρ β lam 𝒞 (Γ.G ω) / 2) P
      exact (hTH.sub (hV.div_const 2)).congr (Eventually.of_forall fun _ ↦ rfl)
    · exact hT
    · exact hTH
  · intro j
    fin_cases j
    · change (∫ ω, compactM2 β lam ρ (Γ.G ω) - compactV ρ β lam 𝒞 (Γ.G ω) / 2 ∂P) = lam / β + (1 - 1 / β) * ν
      rw [integral_sub hT (hV.div_const 2), integral_div, hET, hEV]
      field_simp [hβ.ne']; ring
    · change (∫ ω, compactM2 β lam ρ (Γ.G ω) - compactH β lam ρ (Γ.G ω) - compactV ρ β lam 𝒞 (Γ.G ω) / 2 ∂P) = lam / β - (1 + 1 / β) * ν
      rw [integral_sub hTH (hV.div_const 2), integral_sub hT hH,
        integral_div, hET, hEH, hEV]
      field_simp [hβ.ne']; ring
    · exact hET
    · change (∫ ω, compactM2 β lam ρ (Γ.G ω) - compactH β lam ρ (Γ.G ω) ∂P) = lam / β - ν
      rw [integral_sub hT hH, hET, hEH]
      ring

end Gaussian
end SingularLearningTheory.GaussianPosterior
