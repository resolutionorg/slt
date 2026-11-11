/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import SLT.BayesGibbs.FiniteQuartet.Det

/-!
# The finite quartet expectation identity

The expectation identity for the finite quartet with general covariance.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

section Quartet

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)] (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
include hβ hlam hρ

omit hβ hlam hρ [Nonempty (Fin m)] in
private theorem integrable_gaussianVector_of_polyBoundedPi {F : (Fin m → ℝ) → ℝ}
    (hFm : Measurable F)
    (hF : PolyBoundedPi F) : Integrable F (gaussianVector A) :=
  (integrable_map_measure hFm.aestronglyMeasurable (Matrix.measurable_mulVec A).aemeasurable).2
    (integrable_of_polyBoundedPi (hFm.comp (Matrix.measurable_mulVec A))
        (PolyBoundedPi.comp_mulVec A hF))

private theorem integrable_quartetW (i : Fin m) : Integrable (quartetW β lam ρ i)
    (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A (continuous_quartetW hβ hlam hρ i).measurable
    (polyBoundedPi_quartetW hβ hlam hρ i)

private theorem integrable_quartetR (i : Fin m) : Integrable (quartetR β lam ρ i)
    (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A (continuous_quartetR hβ hlam hρ i).measurable
    (polyBoundedPi_quartetR hβ hlam hρ i)

private theorem integrable_quartetW' (i j : Fin m) :
    Integrable (quartetW' β lam ρ i j) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A
    (continuous_quartetW' hβ hlam hρ i j).measurable (polyBoundedPi_quartetW' hβ hlam hρ i j)

private theorem integrable_quartetM2 : Integrable (quartetM2 β lam ρ) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ ↦ integrable_quartetR hβ hlam hρ A i

private theorem integrable_coord_mul_quartetW (i : Fin m) :
    Integrable (fun g ↦ g i * quartetW β lam ρ i g) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A
    ((measurable_pi_apply i).mul (continuous_quartetW hβ hlam hρ i).measurable)
    ((PolyBoundedPi.coord i).mul (polyBoundedPi_quartetW hβ hlam hρ i))

private theorem integrable_quartetH : Integrable (quartetH β lam ρ) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ ↦ integrable_coord_mul_quartetW hβ hlam hρ A i

private theorem integrable_quartetW_mul (i j : Fin m) :
    Integrable (fun g ↦ quartetW β lam ρ i g * quartetW β lam ρ j g) (gaussianVector A) :=
  integrable_gaussianVector_of_polyBoundedPi A
    ((continuous_quartetW hβ hlam hρ i).measurable.mul
      (continuous_quartetW hβ hlam hρ j).measurable)
    ((polyBoundedPi_quartetW hβ hlam hρ i).mul (polyBoundedPi_quartetW hβ hlam hρ j))

private theorem integrable_quartetQ (b : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (quartetQ β lam ρ b) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ by
    have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
    refine this.congr (Filter.Eventually.of_forall fun g ↦ ?_)
    ring


omit hβ hlam hρ [Nonempty (Fin m)] in
/-- Evaluation of the derivative of `W_i` on the `j`-th basis vector. -/
private theorem quartetW'_eval (i j : Fin m) (g : Fin m → ℝ) :
    (∑ k, quartetW' β lam ρ i k g • coordProj k : (Fin m → ℝ) →L[ℝ] ℝ) (Pi.single j 1) =
      quartetW' β lam ρ i j g := by
  simp [sum_apply, smul_apply, coordProj_apply, Pi.single_apply, Finset.sum_ite_eq']

/-- **Stein's identity for the posterior weights**: `E[G_i W_i(G)] = ∑_j b_{ij} E[∂_j W_i(G)]`. -/
private theorem integral_coord_mul_quartetW (i : Fin m) :
    ∫ g, g i * quartetW β lam ρ i g ∂gaussianVector A =
      ∑ j, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
        ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A := by
  have h := gaussianVector_stein A i (F := quartetW β lam ρ i)
    (F' := fun g ↦ ∑ k, quartetW' β lam ρ i k g • coordProj k)
    (fun g ↦ hasFDerivAt_quartetW hβ hlam hρ i g)
    (fun j ↦ by simpa only [quartetW'_eval] using (continuous_quartetW' hβ hlam hρ i j).measurable)
    (polyBoundedPi_quartetW hβ hlam hρ i)
    (fun j ↦ by simpa only [quartetW'_eval] using polyBoundedPi_quartetW' hβ hlam hρ i j)
  simpa only [quartetW'_eval] using h

end Quartet

section Det

variable {m : ℕ} (β lam : ℝ) (ρ : Fin m → ℝ)

/-- The diagonal term `∑ᵢ bᵢᵢ Rᵢ(g)`. -/
@[expose] noncomputable def quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ i, b i i * quartetR β lam ρ i g

/-- The connected two-point function with a general diagonal: `Vgen = ∑ᵢ bᵢᵢ Rᵢ − Q`. -/
@[expose] noncomputable def quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
  quartetDiag β lam ρ b g - quartetQ β lam ρ b g

variable {β lam ρ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
include hβ hlam hρ

private theorem continuous_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (quartetDiag β lam ρ b) :=
  continuous_finsetSum _ fun i _ ↦ continuous_const.mul (continuous_quartetR hβ hlam hρ i)

theorem continuous_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
    Continuous (quartetVgen β lam ρ b) :=
  (continuous_quartetDiag hβ hlam hρ b).sub (by
    unfold quartetQ
    exact continuous_finsetSum _ fun i _ ↦ continuous_finsetSum _ fun j _ ↦
      (continuous_const.mul (continuous_quartetW hβ hlam hρ i)).mul
        (continuous_quartetW hβ hlam hρ j))

end Det

section Quartet

variable {m n : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ} (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
  [Nonempty (Fin m)] (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
include hβ hlam hρ

private theorem integrable_quartetDiag (b : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (quartetDiag β lam ρ b) (gaussianVector A) :=
  integrable_finsetSum _ fun i _ ↦ (integrable_quartetR hβ hlam hρ A i).const_mul (b i i)

private theorem integrable_quartetVgen (b : Matrix (Fin m) (Fin m) ℝ) :
    Integrable (quartetVgen β lam ρ b) (gaussianVector A) :=
  (integrable_quartetDiag hβ hlam hρ A b).sub (integrable_quartetQ hβ hlam hρ A b)

/-- **Gaussian integration by parts, general diagonal**: `E[H(G)] = β E[Vgen(G)]`. -/
theorem integral_quartetH_eq_gen :
    ∫ g, quartetH β lam ρ g ∂gaussianVector A =
      β * ∫ g, quartetVgen β lam ρ (A * A.transpose) g ∂gaussianVector A := by
  set b : Matrix (Fin m) (Fin m) ℝ := A * A.transpose with hb
  have hH : ∫ g, quartetH β lam ρ g ∂gaussianVector A =
      ∑ i, ∑ j, b i j * ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A := by
    unfold quartetH
    rw [integral_finsetSum _ fun i _ ↦ integrable_coord_mul_quartetW hβ hlam hρ A i]
    exact Finset.sum_congr rfl fun i _ ↦ integral_coord_mul_quartetW hβ hlam hρ A i
  have hW' : ∀ i j, ∫ g, quartetW' β lam ρ i j g ∂gaussianVector A =
      β * (if i = j then ∫ g, quartetR β lam ρ i g ∂gaussianVector A else 0) -
        β * ∫ g, quartetW β lam ρ i g * quartetW β lam ρ j g ∂gaussianVector A := by
    intro i j
    unfold quartetW'
    have h1 : Integrable (fun g ↦ β * (if i = j then quartetR β lam ρ i g else 0))
        (gaussianVector A) := by
      by_cases h : i = j
      · simp only [h, ite_true]; exact (integrable_quartetR hβ hlam hρ A j).const_mul β
      · simp only [h, ite_false, mul_zero]; exact integrable_const 0
    have h2 : Integrable (fun g ↦ β * quartetW β lam ρ i g * quartetW β lam ρ j g)
        (gaussianVector A) := by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul β
      refine this.congr (Filter.Eventually.of_forall fun g ↦ ?_); ring
    rw [integral_sub h1 h2]
    congr 1
    · by_cases h : i = j
      · simp only [h, ite_true, integral_const_mul]
      · simp only [h, ite_false, mul_zero, integral_zero]
    · rw [← integral_const_mul]
      congr 1; funext g; ring
  rw [hH]
  simp_rw [hW']
  have hQ : ∫ g, quartetQ β lam ρ b g ∂gaussianVector A =
      ∑ i, ∑ j, b i j * ∫ g, quartetW β lam ρ i g * quartetW β lam ρ j g ∂gaussianVector A := by
    unfold quartetQ
    rw [integral_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
      refine this.congr (Filter.Eventually.of_forall fun g ↦ ?_); ring]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_finsetSum _ fun j _ ↦ by
      have := (integrable_quartetW_mul hβ hlam hρ A i j).const_mul (b i j)
      refine this.congr (Filter.Eventually.of_forall fun g ↦ ?_); ring]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← integral_const_mul]
    congr 1; funext g; ring
  have hM : ∫ g, quartetDiag β lam ρ b g ∂gaussianVector A =
      ∑ i, b i i * ∫ g, quartetR β lam ρ i g ∂gaussianVector A := by
    unfold quartetDiag
    rw [integral_finsetSum _ fun i _ ↦ (integrable_quartetR hβ hlam hρ A i).const_mul (b i i)]
    exact Finset.sum_congr rfl fun i _ ↦ integral_const_mul _ _
  unfold quartetVgen
  rw [integral_sub (integrable_quartetDiag hβ hlam hρ A b) (integrable_quartetQ hβ hlam hρ A b),
    hQ, hM, mul_sub, Finset.mul_sum, Finset.mul_sum]
  simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
    ite_true, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    ring
  · refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    ring

end Quartet
end SingularLearningTheory.GaussianPosterior
