/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Gaussian integration by parts

Gaussian integration by parts for functions of polynomial growth.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

/-- Polynomial growth: `|F x| ≤ C (1 + |x|)^k`. -/
@[expose] def _root_.PolyBounded (F : ℝ → ℝ) : Prop := ∃ (C : ℝ) (k : ℕ), ∀ x, |F x| ≤ C *
    (1 + |x|) ^ k

end SingularLearningTheory.GaussianPosterior

namespace PolyBounded

open SingularLearningTheory SingularLearningTheory.GaussianPosterior

private theorem const (c : ℝ) : PolyBounded fun _ ↦ c :=
  ⟨|c|, 0, fun x ↦ by simp⟩

private theorem id : PolyBounded fun x ↦ x :=
  ⟨1, 1, fun x ↦ by simp⟩

private theorem mul {F G : ℝ → ℝ} (hF : PolyBounded F) (hG : PolyBounded G) :
    PolyBounded fun x ↦ F x * G x := by
  obtain ⟨C, k, hC⟩ := hF
  obtain ⟨D, l, hD⟩ := hG
  refine ⟨C * D, k + l, fun x ↦ ?_⟩
  have h1 : 0 ≤ (1 + |x|) ^ k := by positivity
  have h2 : 0 ≤ (1 + |x|) ^ l := by positivity
  have hC0 : 0 ≤ C * (1 + |x|) ^ k := (abs_nonneg _).trans (hC x)
  rw [abs_mul, pow_add]
  calc |F x| * |G x| ≤ (C * (1 + |x|) ^ k) * (D * (1 + |x|) ^ l) :=
        mul_le_mul (hC x) (hD x) (abs_nonneg _) hC0
    _ = C * D * ((1 + |x|) ^ k * (1 + |x|) ^ l) := by ring

theorem add {F G : ℝ → ℝ} (hF : PolyBounded F) (hG : PolyBounded G) :
    PolyBounded fun x ↦ F x + G x := by
  obtain ⟨C, k, hC⟩ := hF
  obtain ⟨D, l, hD⟩ := hG
  refine ⟨C + D, k + l, fun x ↦ ?_⟩
  have h1 : 1 ≤ 1 + |x| := by linarith [abs_nonneg x]
  have hk : (1 + |x|) ^ k ≤ (1 + |x|) ^ (k + l) := pow_le_pow_right₀ h1 (by omega)
  have hl : (1 + |x|) ^ l ≤ (1 + |x|) ^ (k + l) := pow_le_pow_right₀ h1 (by omega)
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg (F 0)).trans (hC 0); simpa using this
  have hD0 : 0 ≤ D := by
    have := (abs_nonneg (G 0)).trans (hD 0); simpa using this
  calc |F x + G x| ≤ |F x| + |G x| := abs_add_le _ _
    _ ≤ C * (1 + |x|) ^ k + D * (1 + |x|) ^ l := add_le_add (hC x) (hD x)
    _ ≤ C * (1 + |x|) ^ (k + l) + D * (1 + |x|) ^ (k + l) :=
        add_le_add (mul_le_mul_of_nonneg_left hk hC0) (mul_le_mul_of_nonneg_left hl hD0)
    _ = (C + D) * (1 + |x|) ^ (k + l) := by ring

private theorem const_mul {F : ℝ → ℝ} (hF : PolyBounded F) (c : ℝ) : PolyBounded fun x ↦ c * F x :=
  (const c).mul hF

private theorem neg {F : ℝ → ℝ} (hF : PolyBounded F) : PolyBounded fun x ↦ -F x := by
  obtain ⟨C, k, hC⟩ := hF
  exact ⟨C, k, fun x ↦ by rw [abs_neg]; exact hC x⟩

private theorem measurable_of_continuous {F : ℝ → ℝ} (hF : Continuous
    F) : Measurable F := hF.measurable

end PolyBounded

namespace ProbabilityTheory

/-! ### Polynomial functions are Gaussian-integrable -/

section Integrable

variable (v : ℝ≥0)

theorem integrable_one_add_abs_pow (k : ℕ) :
    Integrable (fun x : ℝ ↦ (1 + |x|) ^ k) (gaussianReal 0 v) := by
  have hmom : Integrable (fun x : ℝ ↦ |x| ^ k) (gaussianReal 0 v) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := v) (k : ℝ≥0)).integrable_norm_rpow
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; simp
    · have := h (by exact_mod_cast hk.ne') ENNReal.coe_ne_top
      simpa [Real.norm_eq_abs, Real.rpow_natCast] using this
  refine ((integrable_const ((2 : ℝ) ^ k)).add (hmom.const_mul ((2 : ℝ) ^ k))).mono'
    (by fun_prop) (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Pi.add_apply]
  have h1 : 1 + |x| ≤ 2 * max 1 |x| := by
    rcases le_total 1 |x| with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have h2 : (max 1 |x|) ^ k ≤ 1 + |x| ^ k := by
    rcases le_total 1 |x| with h | h
    · rw [max_eq_right h]; linarith [pow_nonneg (abs_nonneg x) k]
    · rw [max_eq_left h, one_pow]; linarith [pow_nonneg (abs_nonneg x) k]
  calc (1 + |x|) ^ k ≤ (2 * max 1 |x|) ^ k := pow_le_pow_left₀ (by positivity) h1 k
    _ = 2 ^ k * (max 1 |x|) ^ k := mul_pow _ _ _
    _ ≤ 2 ^ k * (1 + |x| ^ k) := mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = _ := by ring

private theorem integrable_of_polyBounded {F : ℝ → ℝ} (hFm : Measurable F) (hF : PolyBounded F) :
    Integrable F (gaussianReal 0 v) := by
  obtain ⟨C, k, hC⟩ := hF
  refine ((integrable_one_add_abs_pow v k).const_mul C).mono' hFm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs]
  exact hC x

variable (hv : v ≠ 0)
include hv

private theorem integral_gaussianReal_eq (F : ℝ → ℝ) :
    ∫ x, F x ∂gaussianReal 0 v = ∫ x, gaussianPDFReal 0 v x * F x := by
  rw [integral_gaussianReal_eq_integral_smul hv]
  rfl

private theorem integrable_gaussianPDFReal_mul_of_polyBounded {F : ℝ → ℝ} (hFm : Measurable F)
    (hF : PolyBounded F) : Integrable (fun x ↦ gaussianPDFReal 0 v x * F x) := by
  have h := integrable_of_polyBounded v hFm hF
  rw [gaussianReal_of_var_ne_zero _ hv,
    integrable_withDensity_iff_integrable_smul₀' (measurable_gaussianPDF _ _).aemeasurable
      (Filter.Eventually.of_forall fun _ ↦ gaussianPDF_lt_top)] at h
  simpa [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)] using h

end Integrable

/-! ### The derivative of the Gaussian density -/

private theorem hasDerivAt_gaussianPDFReal (v : ℝ≥0) (hv : v ≠ 0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal 0 v) (-(x / v) * gaussianPDFReal 0 v x) x := by
  have hv' : (0 : ℝ) < v := by positivity
  have h1 : HasDerivAt (fun y : ℝ ↦ -(y - 0) ^ 2 / (2 * (v : ℝ))) (-(x / v)) x := by
    have := ((hasDerivAt_id x).sub_const 0).pow 2
    have h := (this.neg).div_const (2 * (v : ℝ))
    refine h.congr_deriv ?_
    simp only [id]
    field_simp
    ring
  have h2 := (h1.exp).const_mul ((Real.sqrt (2 * Real.pi * v))⁻¹)
  have hfun : gaussianPDFReal 0 v =
      fun y : ℝ ↦ (Real.sqrt (2 * Real.pi * v))⁻¹ * Real.exp (-(y - 0) ^ 2 / (2 * (v : ℝ))) :=
    funext fun y ↦ rfl
  rw [hfun]
  refine h2.congr_deriv ?_
  ring

/-! ### The Stein identity -/

/-- **Gaussian integration by parts (Stein's identity)**: for `Z ~ N(0, v)`, `v ≠ 0`, and `F ∈ C¹`
with `F, F'` of polynomial growth, `E[Z F(Z)] = v E[F'(Z)]`. -/
theorem gaussianReal_stein (v : ℝ≥0) (hv : v ≠ 0) {F F' : ℝ → ℝ} (hF : ∀ x, HasDerivAt F (F' x) x)
    (hF'm : Measurable F') (hFb : PolyBounded F) (hF'b : PolyBounded F') :
    ∫ x, x * F x ∂gaussianReal 0 v = v * ∫ x, F' x ∂gaussianReal 0 v := by
  have hFm : Measurable F :=
    (continuous_iff_continuousAt.2 fun x ↦ (hF x).continuousAt).measurable
  rw [integral_gaussianReal_eq v hv, integral_gaussianReal_eq v hv]
  set φ := gaussianPDFReal 0 v with hφ
  have hv' : (0 : ℝ) < v := by positivity
  -- integration by parts with `u = F`, `v = φ`, `v' = −(x/v) φ`
  have huv' : Integrable (F * fun x ↦ -(x / v) * φ x) := by
    have := integrable_gaussianPDFReal_mul_of_polyBounded v hv
      (F := fun x ↦ F x * -((v : ℝ)⁻¹ * x)) (hFm.mul (by fun_prop))
      (hFb.mul ((PolyBounded.id.const_mul ((v : ℝ)⁻¹)).neg))
    refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply]
    ring
  have hu'v : Integrable (F' * φ) := by
    have := integrable_gaussianPDFReal_mul_of_polyBounded v hv hF'm hF'b
    refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply]
    ring
  have huv : Integrable (F * φ) := by
    have := integrable_gaussianPDFReal_mul_of_polyBounded v hv hFm hFb
    refine this.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    simp only [Pi.mul_apply]
    ring
  have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable (u := F) (v := φ) (u' := F')
    (v' := fun x ↦ -(x / v) * φ x) (fun x _ ↦ hF x) (fun x _ ↦ hasDerivAt_gaussianPDFReal v hv x)
    huv' hu'v huv
  -- `∫ F (−x/v) φ = − ∫ F' φ`
  have hleft : ∫ x, F x * (-(x / v) * φ x) = -(1 / v) * ∫ x, φ x * (x * F x) := by
    rw [← integral_const_mul]
    congr 1; funext x; ring
  have hright : ∫ x, F' x * φ x = ∫ x, φ x * F' x := by
    congr 1; funext x; ring
  rw [hleft, hright] at hibp
  have hv0 : (v : ℝ) ≠ 0 := hv'.ne'
  have h2 : (1 / (v : ℝ)) * ∫ x, φ x * (x * F x) = ∫ x, φ x * F' x := by linarith [hibp]
  calc ∫ x, φ x * (x * F x) = v * ((1 / (v : ℝ)) * ∫ x, φ x * (x * F x)) := by
        rw [← mul_assoc, mul_one_div_cancel hv0, one_mul]
    _ = v * ∫ x, φ x * F' x := by rw [h2]

end ProbabilityTheory
