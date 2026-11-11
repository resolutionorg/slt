/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Gaussian.OfGaussianProcess
public import SLT.EmpiricalProcess.ProductSpace
public import SLT.MeasureTheory.Function.AsympUnifIntegrable
public import SLT.BayesGibbs.CompactBase.Finite
public import SLT.FreeEnergy.FundamentalConditions

/-!
# The limit of the empirical process is a Gaussian field

The limit of the empirical process of a sixth-moment bounded model has a finite second sup-norm
moment (from the fourth-moment bound, by asymptotic uniform integrability), and a measurable
modification of `-E.Ψlim` is a `ProbabilityTheory.GaussianField` with the covariance of the
limit (`SingularLearningTheory.EmpiricalProcessLimit.exists_gaussianField`).
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory

open GaussianPosterior

variable {X Ω Ω' U : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U]
  {q : Measure X} {f : X → U → ℝ} {Xs : ℕ → Ω → X}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- The s = 6 empirical bound supplies the fourth-moment input used below. -/
theorem EmpiricalProcessLimit.momentBound_four_of_six
    (E : EmpiricalProcessLimit q f Xs P P') (hE6 : E.MomentBound 6) :
    E.MomentBound 4 := by
  obtain ⟨C, hC, hCn⟩ := hE6
  refine ⟨1 + C, ENNReal.add_ne_top.mpr ⟨by simp, hC⟩, fun n ↦ ?_⟩
  calc
    (∫⁻ ω, (⨆ u, ‖E.Ψ n ω u‖ₑ) ^ 4 ∂P) ≤
        ∫⁻ ω, 1 + (⨆ u, ‖E.Ψ n ω u‖ₑ) ^ 6 ∂P := by
      apply lintegral_mono
      intro ω
      by_cases h : (⨆ u, ‖E.Ψ n ω u‖ₑ) ≤ 1
      · exact (pow_le_one₀ bot_le h).trans (le_add_of_nonneg_right bot_le)
      · exact (pow_le_pow_right₀ (le_of_not_ge h) (by norm_num : 4 ≤ 6)).trans
          (le_add_of_nonneg_left zero_le_one)
    _ = 1 + ∫⁻ ω, (⨆ u, ‖E.Ψ n ω u‖ₑ) ^ 6 ∂P := by
      rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
    _ ≤ 1 + C := add_le_add le_rfl (hCn n)

/-- The existing fourth-moment estimate transfers a second sup-norm moment to the limit.
This uses the AUI/weak-limit theorem, without a whole-space Gaussian or Fernique claim. -/
theorem EmpiricalProcessLimit.integrable_sq_norm_limit
    (E : EmpiricalProcessLimit q f Xs P P') (hE4 : E.MomentBound 4) :
    Integrable (fun ω ↦ ‖E.Ψlim ω‖ ^ 2) P' := by
  obtain ⟨C, hC, hCn⟩ := hE4
  have hAUI : AsympUnifIntegrable P (fun n ω ↦ ‖E.Ψ n ω‖ ^ 2) := by
    apply asympUnifIntegrable_of_lintegral_sq_le hC
    filter_upwards with n
    refine (lintegral_mono fun ω ↦ ?_).trans (hCn n)
    rw [enorm_pow, enorm_norm, ← pow_mul]
    norm_num only [Nat.reduceMul]
    exact pow_le_pow_left' (ContinuousMap.enorm_le_iSup_enorm _) 4
  have hlim := E.tendsto.continuous_comp
    (g := fun g : C(U, ℝ) ↦ ‖g‖ ^ 2) (continuous_norm.pow 2)
  exact hAUI.integrable_limit hlim

/-- The finite-dimensional certificates yield a field usable by compact Stein.
The measurable modification is still a C(U)-valued random field on the original limit space,
and it equals the required negative chart-process limit almost surely. The covariance kernel
is supplied by its independent construction from the resolved coefficient map. -/
theorem EmpiricalProcessLimit.exists_gaussianField
    (E : EmpiricalProcessLimit q f Xs P P') (hE4 : E.MomentBound 4)
    (𝒞 : PSDKernel U)
    (hkernel : ∀ u v, cov[fun x ↦ f x u, fun x ↦ f x v; q] = 𝒞.C u v) :
    ∃ Γ : GaussianField 𝒞 P', Γ.G =ᵐ[P'] fun ω ↦ -E.Ψlim ω := by
  have hEm := E.tendsto.aemeasurable_limit
  let G : Ω' → C(U, ℝ) := fun ω ↦ -(hEm.mk E.Ψlim ω)
  have hGm : Measurable G := hEm.measurable_mk.neg
  have hGae : G =ᵐ[P'] fun ω ↦ -E.Ψlim ω :=
    hEm.ae_eq_mk.symm.mono fun ω hω ↦ congrArg Neg.neg hω
  have hG2 : Integrable (fun ω ↦ ‖G ω‖ ^ 2) P' := by
    refine (E.integrable_sq_norm_limit hE4).congr ?_
    filter_upwards [hGae] with ω hω
    rw [hω, norm_neg]
  have hgauss : ∀ m (u : Fin m → U),
      IsGaussian (P'.map (fun ω i ↦ G ω (u i))) := by
    intro m u
    let N : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) :=
      -(ContinuousLinearMap.id ℝ (Fin m → ℝ))
    have hNm : Measurable N := N.continuous.measurable
    have hVm := E.aemeasurable_Ψlim_pi u
    have : IsGaussian (P'.map (fun ω i ↦ E.Ψlim ω (u i))) := E.gaussian m u
    have hmap : P'.map (fun ω i ↦ G ω (u i)) =
        (P'.map (fun ω i ↦ E.Ψlim ω (u i))).map N := by
      rw [hNm.aemeasurable.map_map_of_aemeasurable hVm]
      apply Measure.map_congr
      filter_upwards [hGae] with ω hω
      funext i
      change G ω (u i) = -E.Ψlim ω (u i)
      exact congrArg (fun g : C(U, ℝ) ↦ g (u i)) hω
    rw [hmap]
    infer_instance
  have hmean : ∀ u, ∫ ω, G ω u ∂P' = 0 := by
    intro u
    calc
      (∫ ω, G ω u ∂P') = ∫ ω, -E.Ψlim ω u ∂P' := by
        refine integral_congr_ae ?_
        exact hGae.mono fun ω hω ↦ congrArg (fun g : C(U, ℝ) ↦ g u) hω
      _ = 0 := by rw [integral_neg, E.mean_zero u, neg_zero]
  have hcov : ∀ u v, cov[fun ω ↦ G ω u, fun ω ↦ G ω v; P'] = 𝒞.C u v := by
    intro u v
    have hc := (E.cov u v).trans (hkernel u v)
    simp only [covariance, E.mean_zero, hmean, sub_zero] at hc ⊢
    refine (integral_congr_ae ?_).trans hc
    filter_upwards [hGae] with ω hω
    simp only [hω, ContinuousMap.neg_apply, neg_mul_neg]
  exact ⟨GaussianField.ofGaussianProcess 𝒞 P' G hGm hG2 hgauss hmean hcov,
    hGae⟩

end SingularLearningTheory
