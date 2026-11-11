/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Gaussian.EmpiricalProcessLimit
import SLT.EmpiricalProcess.ProductSpace

/-!
# The covariance kernel of the limit process

A square-integrable continuous random field has a continuous positive semidefinite
second-moment kernel. Applied to the centered Gaussian limit, this constructs
the kernel required by compact Stein without adding a covariance hypothesis.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.GaussianPosterior

section SecondMoment

variable {U Ω : Type*} [MetricSpace U] [CompactSpace U] [MeasurableSpace Ω]
  {P : Measure Ω} (g : Ω → C(U, ℝ))
  (hg : ∀ u, AEStronglyMeasurable (fun ω ↦ g ω u) P)
  (h2 : Integrable (fun ω ↦ ‖g ω‖ ^ 2) P)

theorem _root_.ContinuousMap.norm_eval_mul_le_sq_norm (ω : Ω) (u v : U) :
    ‖g ω u * g ω v‖ ≤ ‖g ω‖ ^ 2 := by
  rw [norm_mul, pow_two]
  exact mul_le_mul ((g ω).norm_coe_le_norm u) ((g ω).norm_coe_le_norm v)
    (norm_nonneg _) (norm_nonneg _)

include hg h2 in
theorem _root_.MeasureTheory.integrable_eval_mul (u v : U) : Integrable (fun ω ↦ g ω u * g ω v) P :=
  h2.mono' ((hg u).mul (hg v)) (.of_forall fun ω ↦ ContinuousMap.norm_eval_mul_le_sq_norm g ω u v)

/-- No Gaussian assumption is needed for the second-moment kernel. -/
@[expose] noncomputable def _root_.PSDKernel.secondMoment : PSDKernel U where
  C u v := ∫ ω, g ω u * g ω v ∂P
  symm u v := by simp only [mul_comm]
  continuous := continuous_of_dominated
    (fun uv ↦ (hg uv.1).mul (hg uv.2))
    (fun uv ↦ .of_forall fun ω ↦ ContinuousMap.norm_eval_mul_le_sq_norm g ω uv.1 uv.2) h2
    (.of_forall fun ω ↦ ((g ω).continuous.comp continuous_fst).mul
      ((g ω).continuous.comp continuous_snd))
  psd m x v := by
    have hi (i j : Fin m) : Integrable
        (fun ω ↦ (g ω (x i) * g ω (x j)) * (v i * v j)) P :=
      (integrable_eval_mul g hg h2 (x i) (x j)).mul_const _
    have heq (ω : Ω) : (∑ i, g ω (x i) * v i) ^ 2 =
        ∑ i, ∑ j, (g ω (x i) * g ω (x j)) * (v i * v j) := by
      rw [pow_two, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ ↦ by ring
    have hnon : 0 ≤ ∫ ω, (∑ i, g ω (x i) * v i) ^ 2 ∂P :=
      integral_nonneg fun ω ↦ sq_nonneg _
    simp_rw [heq] at hnon
    rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ fun j _ ↦ hi i j)] at hnon
    simp_rw [integral_finsetSum _ (fun j _ ↦ hi _ j), integral_mul_const] at hnon
    simpa only [mul_assoc] using hnon

end SecondMoment
end SingularLearningTheory.GaussianPosterior

namespace SingularLearningTheory

open GaussianPosterior

variable {X Ω Ω' U : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace U] [CompactSpace U] [MeasurableSpace U] [BorelSpace U]
  {q : Measure X} {f : X → U → ℝ} {Xs : ℕ → Ω → X}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- The centered limit supplies a continuous covariance kernel. -/
@[expose] noncomputable def EmpiricalProcessLimit.covarianceKernel
    (E : EmpiricalProcessLimit q f Xs P P') (hE4 : E.MomentBound 4) : PSDKernel U :=
  PSDKernel.secondMoment E.Ψlim (fun u ↦ (E.aemeasurable_Ψlim_eval u).aestronglyMeasurable)
    (E.integrable_sq_norm_limit hE4)

theorem EmpiricalProcessLimit.covarianceKernel_eq
    (E : EmpiricalProcessLimit q f Xs P P') (hE4 : E.MomentBound 4) (u v : U) :
    (E.covarianceKernel hE4).C u v = cov[fun x ↦ f x u, fun x ↦ f x v; q] := by
  have h := E.cov u v
  simpa only [covarianceKernel, PSDKernel.secondMoment, covariance, E.mean_zero, sub_zero] using h

/-- Both the Gaussian field and its covariance kernel come from the supplied process. -/
theorem EmpiricalProcessLimit.exists_canonicalGaussianField
    (E : EmpiricalProcessLimit q f Xs P P') (hE4 : E.MomentBound 4) :
    ∃ Γ : GaussianField (E.covarianceKernel hE4) P',
      Γ.G =ᵐ[P'] fun ω ↦ -E.Ψlim ω :=
  E.exists_gaussianField hE4 (E.covarianceKernel hE4)
    (fun u v ↦ (E.covarianceKernel_eq hE4 u v).symm)

end SingularLearningTheory
