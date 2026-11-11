/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import SLT.BayesGibbs.CompactBase.GaussianStein
public import SLT.BayesGibbs.CompactBase.Finite
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Gaussian fields from their finite-dimensional laws

`ProbabilityTheory.GaussianField.ofGaussianProcess` builds a Gaussian field from a continuous
process whose finite-dimensional laws are centred Gaussians with the field's covariance.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`: the moment extensionality for finite-dimensional laws,
the Gram factor, the standard-Gaussian product instance and the first moment. The second moment is
proved by Stein's lemma instead of the tilted moment generating function.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal MatrixOrder

namespace ProbabilityTheory

open SingularLearningTheory.GaussianPosterior

section Marginal
variable {m n : ℕ}

@[expose] instance isGaussian_stdGaussianPi (k : ℕ) : IsGaussian (stdGaussianPi k) := by
  rw [← isGaussian_map_equiv_iff (EuclideanSpace.equiv (Fin k) ℝ).symm]
  have : (stdGaussianPi k).map ⇑(EuclideanSpace.equiv (Fin k) ℝ).symm =
      stdGaussian (EuclideanSpace ℝ (Fin k)) := map_pi_eq_stdGaussian
  rw [this]
  infer_instance

/-- The coordinate functional `z ↦ (A z)_j` as a continuous linear map. -/
@[expose] noncomputable def _root_.Matrix.coordFunctional (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (j : Fin m) :
    (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap ((LinearMap.proj j).comp (Matrix.mulVecLin A))

@[simp] theorem _root_.Matrix.coordFunctional_apply (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin m)
    (z : Fin (n + 1) → ℝ) : Matrix.coordFunctional A j z = A.mulVec z j := rfl

private theorem integral_coordFunctional (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (j : Fin m) :
    ∫ z, Matrix.coordFunctional A j z ∂stdGaussianPi (n + 1) = 0 := by
  have hint : ∀ k : Fin (n + 1),
      Integrable (fun z : Fin (n + 1) → ℝ ↦ A j k * z k) (stdGaussianPi (n + 1)) := fun k ↦
    (integrable_eval (μ := fun _ : Fin (n + 1) ↦ gaussianReal 0 1) (i := k)
      IsGaussian.integrable_id).const_mul (A j k)
  have hz : ∀ k : Fin (n + 1), ∫ z : Fin (n + 1) → ℝ, z k ∂stdGaussianPi (n + 1) = 0 := fun k ↦ by
    rw [stdGaussianPi, integral_eval (μ := fun _ : Fin (n + 1) ↦ gaussianReal 0 1),
      integral_id_gaussianReal]
  simp only [Matrix.coordFunctional_apply, Matrix.mulVec, dotProduct]
  rw [integral_finsetSum _ fun k _ ↦ hint k]
  refine Finset.sum_eq_zero fun k _ ↦ ?_
  rw [integral_const_mul, hz k, mul_zero]


end Marginal

section FiniteDim

variable {m : ℕ}

/-- Every continuous linear functional on `Fin m → ℝ` is a coordinate combination. -/
private theorem strongDual_pi_apply (L : StrongDual ℝ (Fin m → ℝ)) (v : Fin m → ℝ) :
    L v = ∑ i, v i * L (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [show Pi.single i (v i) = v i • (Pi.single i (1 : ℝ) : Fin m → ℝ) by
    rw [← Pi.single_smul, smul_eq_mul, mul_one], map_smul, smul_eq_mul]

theorem IsGaussian.memLp_two_proj (μ : Measure (Fin m → ℝ)) [IsGaussian μ] (i : Fin m) :
    MemLp (fun v ↦ v i) 2 μ :=
  IsGaussian.memLp_dual μ (ContinuousLinearMap.proj i) 2 (by norm_num)

private theorem integrable_proj (μ : Measure (Fin m → ℝ)) [IsGaussian μ] (i : Fin m) :
    Integrable (fun v ↦ v i) μ :=
  (IsGaussian.memLp_two_proj μ i).integrable (by norm_num)

private theorem integrable_proj_mul (μ : Measure (Fin m → ℝ)) [IsGaussian μ] (i j : Fin m) :
    Integrable (fun v ↦ v i * v j) μ :=
  (IsGaussian.memLp_two_proj μ i).integrable_mul (IsGaussian.memLp_two_proj μ j)

private theorem integral_strongDual_eq_sum (μ : Measure (Fin m → ℝ)) [IsGaussian μ]
    (L : StrongDual ℝ (Fin m → ℝ)) :
    ∫ v, L v ∂μ = ∑ i, L (Pi.single i 1) * ∫ v, v i ∂μ := by
  rw [integral_congr_ae (Filter.Eventually.of_forall fun v ↦ strongDual_pi_apply L v),
    integral_finsetSum _ fun i _ ↦ (integrable_proj μ i).mul_const _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_mul_const, mul_comm]

private theorem integral_strongDual_sq_eq_sum (μ : Measure (Fin m → ℝ)) [IsGaussian μ]
    (L : StrongDual ℝ (Fin m → ℝ)) :
    ∫ v, (L v) ^ 2 ∂μ =
      ∑ i, ∑ j, L (Pi.single i 1) * L (Pi.single j 1) * ∫ v, v i * v j ∂μ := by
  have h : ∀ v, (L v) ^ 2 =
      ∑ i, ∑ j, L (Pi.single i 1) * L (Pi.single j 1) * (v i * v j) := by
    intro v
    rw [strongDual_pi_apply L v, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall h),
    integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦
      (integrable_proj_mul μ i j).const_mul _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum _ fun j _ ↦ (integrable_proj_mul μ i j).const_mul _]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [integral_const_mul]

/-- **Gaussian laws on `Fin m → ℝ` are determined by their first and second coordinate
moments** (Cramér–Wold through the characteristic functional). -/
theorem IsGaussian.ext_of_moments (μ ν : Measure (Fin m → ℝ)) [IsGaussian μ] [IsGaussian ν]
    (h1 : ∀ i, ∫ v, v i ∂μ = ∫ v, v i ∂ν)
    (h2 : ∀ i j, ∫ v, v i * v j ∂μ = ∫ v, v i * v j ∂ν) : μ = ν := by
  refine Measure.ext_of_charFunDual (funext fun L ↦ ?_)
  rw [IsGaussian.charFunDual_eq, IsGaussian.charFunDual_eq]
  have hm : ∫ v, L v ∂μ = ∫ v, L v ∂ν := by
    rw [integral_strongDual_eq_sum, integral_strongDual_eq_sum]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [h1]
  have hv : Var[L; μ] = Var[L; ν] := by
    rw [variance_eq_sub (IsGaussian.memLp_dual μ L 2 (by norm_num)),
      variance_eq_sub (IsGaussian.memLp_dual ν L 2 (by norm_num))]
    simp only [Pi.pow_apply]
    rw [integral_strongDual_sq_eq_sum, integral_strongDual_sq_eq_sum, hm]
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by rw [h2]
  have hm' : ∫ v, (L v : ℂ) ∂μ = ∫ v, (L v : ℂ) ∂ν := by
    rw [integral_complex_ofReal, integral_complex_ofReal, hm]
  rw [hm', hv]

/-- The matrix `z ↦ A z` as a continuous linear map. -/
private noncomputable def mulVecCLM {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    (Fin (n + 1) → ℝ) →L[ℝ] (Fin m → ℝ) :=
  LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)

private theorem gaussianVector_eq_map_mulVecCLM {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    gaussianVector A = (stdGaussianPi (n + 1)).map (mulVecCLM A) := rfl

@[expose] instance isGaussian_gaussianVector {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) :
    IsGaussian (gaussianVector A) := by
  rw [gaussianVector_eq_map_mulVecCLM]
  infer_instance

/-- First coordinate moments of `gaussianVector A` vanish. -/
theorem integral_proj_gaussianVector {n : ℕ} (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (i : Fin m) :
    ∫ v, v i ∂gaussianVector A = 0 := by
  rw [integral_gaussianVector A _ (measurable_pi_apply i)]
  exact integral_coordFunctional A i


/-- The second coordinate moment follows directly from finite Stein with a linear test. -/
theorem integral_proj_mul_gaussianVector {n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (i j : Fin m) :
    ∫ v, v i * v j ∂gaussianVector A = (A * A.transpose) i j := by
  have h := gaussianVector_stein A i
    (F := fun v ↦ v j) (F' := fun _ ↦ coordProj j)
    (fun v ↦ hasFDerivAt_coord j v) (fun _ ↦ measurable_const)
    (PolyBoundedPi.coord j) (fun _ ↦ PolyBoundedPi.const _)
  simpa [coordProj_apply, Pi.single_apply, integral_const, probReal_univ,
    Finset.sum_ite_eq, Finset.sum_ite_eq'] using h

/-- The matrix square root of the continuous functional calculus. -/
@[expose] noncomputable def _root_.SingularLearningTheory.GaussianPosterior.matrixSqrt
    (C : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  CFC.sqrt C

/-- The Gram factor `[√C | 0]` of a positive semidefinite matrix, padded by a zero column. -/
@[expose] noncomputable def _root_.Matrix.gramFactor (C : Matrix (Fin m) (Fin m) ℝ) : Matrix (Fin m)
    (Fin (m + 1)) ℝ :=
  Matrix.of fun i (j : Fin (m + 1)) ↦
    Fin.snoc (α := fun _ ↦ ℝ) (fun j' ↦ matrixSqrt C i j') (0 : ℝ) j

theorem _root_.Matrix.gramFactor_mul_transpose (C : Matrix (Fin m) (Fin m) ℝ) (hC : C.PosSemidef) :
    Matrix.gramFactor C * (Matrix.gramFactor C).transpose = C := by
  have hS : matrixSqrt C * matrixSqrt C = C := CFC.sqrt_mul_sqrt_self C (ha := hC.nonneg)
  have hT : (matrixSqrt C).transpose = matrixSqrt C := by
    have := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg C)).star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this
  calc Matrix.gramFactor C * (Matrix.gramFactor C).transpose = matrixSqrt C * (matrixSqrt
      C).transpose := by
        ext i k
        simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.gramFactor, Matrix.of_apply]
        rw [Fin.sum_univ_castSucc]
        simp [Fin.snoc_castSucc, Fin.snoc_last]
    _ = C := by rw [hT, hS]

end FiniteDim

section Kernel

variable {K : Type*} [TopologicalSpace K]

/-- The kernel matrix of a `PSDKernel` is positive semidefinite. -/
theorem _root_.PSDKernel.kernelMatrix_posSemidef (𝒞 : PSDKernel K) {m : ℕ} (x : Fin m → K) :
    (𝒞.kernelMatrix x).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.2 ⟨?_, fun v ↦ ?_⟩
  · ext i j
    simp [PSDKernel.kernelMatrix, Matrix.conjTranspose_apply, 𝒞.symm]
  · have e : star v ⬝ᵥ (𝒞.kernelMatrix x).mulVec v = ∑ i, ∑ j, 𝒞.C (x i) (x j) * v i * v j := by
      simp only [star_trivial, dotProduct, Matrix.mulVec, PSDKernel.kernelMatrix, Matrix.of_apply,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    rw [e]
    exact 𝒞.psd m x v

end Kernel

/-- Construct the generic Stein field from finite-dimensional Gaussianity and coordinate
moments. No Gaussianity of the entire C(K)-valued law and no Fernique theorem is assumed. -/
@[expose] noncomputable def GaussianField.ofGaussianProcess
    {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (𝒞 : PSDKernel K) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (G : Ω → C(K, ℝ)) (hG : Measurable G)
    (hG2 : Integrable (fun ω ↦ ‖G ω‖ ^ 2) P)
    (hgauss : ∀ m (x : Fin m → K), IsGaussian (P.map (fun ω i ↦ G ω (x i))))
    (hmean : ∀ x, ∫ ω, G ω x ∂P = 0)
    (hcov : ∀ x y, cov[fun ω ↦ G ω x, fun ω ↦ G ω y; P] = 𝒞.C x y) :
    GaussianField 𝒞 P where
  G := G
  measurable_eval := fun x ↦ (continuous_eval_const x).measurable.comp hG
  integrable_sq_norm := hG2
  law := by
    intro m x
    let V : Ω → (Fin m → ℝ) := fun ω i ↦ G ω (x i)
    have hVm : Measurable V := Measurable.of_eval fun i ↦
      (continuous_eval_const (x i)).measurable.comp hG
    let μ := P.map V
    have : IsGaussian μ := hgauss m x
    let A := Matrix.gramFactor (𝒞.kernelMatrix x)
    have hA : A * A.transpose = 𝒞.kernelMatrix x :=
      Matrix.gramFactor_mul_transpose _ (𝒞.kernelMatrix_posSemidef x)
    refine ⟨m, A, hA, ?_⟩
    change μ = gaussianVector A
    apply IsGaussian.ext_of_moments
    · intro i
      rw [integral_proj_gaussianVector]
      change ∫ v, v i ∂P.map V = 0
      rw [integral_map hVm.aemeasurable (measurable_pi_apply i).aestronglyMeasurable]
      exact hmean (x i)
    · intro i j
      rw [integral_proj_mul_gaussianVector, hA]
      have hLp (k : Fin m) : MemLp (fun ω ↦ G ω (x k)) 2 P := by
        exact (memLp_map_measure_iff
          (measurable_pi_apply k).aestronglyMeasurable hVm.aemeasurable).1
              (IsGaussian.memLp_two_proj μ k)
      have hc := hcov (x i) (x j)
      rw [covariance_eq_sub (hLp i) (hLp j), hmean, hmean, mul_zero, sub_zero] at hc
      change ∫ v, v i * v j ∂P.map V = 𝒞.C (x i) (x j)
      exact (integral_map hVm.aemeasurable
        ((measurable_pi_apply i).mul (measurable_pi_apply j)).aestronglyMeasurable).trans hc

end ProbabilityTheory
