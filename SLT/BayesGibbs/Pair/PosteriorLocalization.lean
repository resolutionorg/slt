/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.GlobalTransport
public import SLT.BayesGibbs.CompactPosterior.RatioProbability
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Localizing pair integrals

Bounds for double integrals $\iint B(w, w')\,e(w)\,e(w')$ of a bounded kernel $B$ against a
nonnegative integrable weight $e$, used to localize the pair numerator of the functional variance.
`SingularLearningTheory.BayesGibbs.integrable_bounded_kernel_mul_weights` gives integrability on the
product. For a cutoff $0 \le \chi \le 1$,
`SingularLearningTheory.BayesGibbs.abs_pair_localization_error_le` bounds the change from replacing
$e$ by $\chi e$ in both factors by $2M \int (1 - \chi) e \cdot \int e$, with $M$ the bound on $|B|$.
`MeasureTheory.abs_integral_product_le_half_squares` bounds
$|E_q[fg]|$ by $(E_q[f^2] + E_q[g^2])/2$, which bounds the population product by the population
second moment.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

/-- A bounded parameter kernel, integrated against two integrable nonnegative
weights, is integrable on the product. The bound need only hold almost surely. -/
private theorem integrable_bounded_kernel_mul_weights
    {U : Type*} [MeasurableSpace U] {μ : Measure U} [SFinite μ]
    {B : U × U → ℝ} (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ z ∂μ.prod μ, |B z| ≤ M)
    {e f : U → ℝ} (he : Integrable e μ) (hf : Integrable f μ) :
    Integrable (fun z ↦ B z * e z.1 * f z.2) (μ.prod μ) := by
  refine ((he.norm.mul_prod hf.norm).const_mul M).mono'
    ((hB.aestronglyMeasurable.mul he.aestronglyMeasurable.comp_fst).mul
      hf.aestronglyMeasurable.comp_snd) ?_
  filter_upwards [hb] with z hz
  simp only [norm_mul, Real.norm_eq_abs]
  nlinarith [mul_le_mul_of_nonneg_right hz
    (mul_nonneg (abs_nonneg (e z.1)) (abs_nonneg (f z.2)))]

/-- All terms involving the complement of the localization are bounded by
`2 M` times tail evidence times total evidence. This also proves the needed
product integrability, and does not require pointwise coverage by the atlas. -/
theorem abs_pair_localization_error_le
    {U : Type*} [MeasurableSpace U] {μ : Measure U} [SFinite μ]
    {B : U × U → ℝ} (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ᵐ z ∂μ.prod μ, |B z| ≤ M)
    {e : U → ℝ} (he : Integrable e μ)
    (he0 : ∀ᵐ u ∂μ, 0 ≤ e u)
    {χ : U → ℝ} (hχm : Measurable χ)
    (hχ0 : ∀ u, 0 ≤ χ u) (hχ1 : ∀ u, χ u ≤ 1) :
    |(∫ z, B z * e z.1 * e z.2 ∂μ.prod μ) -
      ∫ z, B z * (χ z.1 * e z.1) * (χ z.2 * e z.2) ∂μ.prod μ| ≤
      2 * M * (∫ u, (1 - χ u) * e u ∂μ) * (∫ u, e u ∂μ) := by
  have hχb : ∀ u, ‖χ u‖ ≤ 1 := fun u ↦ by
    rw [Real.norm_eq_abs, abs_of_nonneg (hχ0 u)]
    exact hχ1 u
  have hl : Integrable (fun u ↦ χ u * e u) μ :=
    he.bdd_mul hχm.aestronglyMeasurable (.of_forall hχb)
  have ht : Integrable (fun u ↦ (1 - χ u) * e u) μ := by
    convert he.sub hl using 1 <;> ext u <;> simp only [Pi.sub_apply] <;> ring
  have hfull := integrable_bounded_kernel_mul_weights hB hM hb he he
  have hlocal := integrable_bounded_kernel_mul_weights hB hM hb hl hl
  have hmajor : Integrable
      (fun z : U × U ↦ M * (((1 - χ z.1) * e z.1) * e z.2 +
        e z.1 * ((1 - χ z.2) * e z.2))) (μ.prod μ) :=
    ((ht.mul_prod he).add (he.mul_prod ht)).const_mul M
  rw [← integral_sub hfull hlocal]
  have hbound : ∀ᵐ z ∂μ.prod μ,
      ‖B z * e z.1 * e z.2 - B z * (χ z.1 * e z.1) * (χ z.2 * e z.2)‖ ≤
        M * (((1 - χ z.1) * e z.1) * e z.2 +
          e z.1 * ((1 - χ z.2) * e z.2)) := by
    filter_upwards [hb, Measure.quasiMeasurePreserving_fst.ae he0, Measure.quasiMeasurePreserving_snd.ae he0] with z hz he₁ he₂
    have hc₁ := hχ0 z.1
    have hc₂ := hχ0 z.2
    have hc₁' := hχ1 z.1
    have hc₂' := hχ1 z.2
    have hcoef : 0 ≤ 1 - χ z.1 * χ z.2 := by nlinarith
    have hcoef' : 1 - χ z.1 * χ z.2 ≤ (1 - χ z.1) + (1 - χ z.2) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc₁') (sub_nonneg.mpr hc₂')]
    rw [show B z * e z.1 * e z.2 - B z * (χ z.1 * e z.1) *
        (χ z.2 * e z.2) = B z * ((1 - χ z.1 * χ z.2) * e z.1 * e z.2) by ring,
      norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (mul_nonneg hcoef he₁) he₂)]
    calc _ ≤ M * ((1 - χ z.1 * χ z.2) * e z.1 * e z.2) :=
        mul_le_mul_of_nonneg_right hz (mul_nonneg (mul_nonneg hcoef he₁) he₂)
      _ ≤ _ := by
        have h := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef' he₁) he₂) hM
        convert h using 1 <;> ring
  have h := norm_integral_le_of_norm_le hmajor hbound
  rw [Real.norm_eq_abs, integral_const_mul,
    integral_add (ht.mul_prod he) (he.mul_prod ht),
    integral_prod_mul (fun u ↦ (1 - χ u) * e u) e,
    integral_prod_mul e (fun u ↦ (1 - χ u) * e u)] at h
  convert h using 1 <;> ring

/-- The raw covariance kernel is bounded by the arithmetic mean of the two
population square moments. This avoids any global parameter-space envelope. -/
theorem _root_.MeasureTheory.abs_integral_product_le_half_squares
    {X : Type*} [MeasurableSpace X] {q : Measure X}
    {f g : X → ℝ} (hfm : AEStronglyMeasurable f q) (hgm : AEStronglyMeasurable g q)
    (hf : Integrable (fun x ↦ f x ^ 2) q) (hg : Integrable (fun x ↦ g x ^ 2) q) :
    |∫ x, f x * g x ∂q| ≤ ((∫ x, f x ^ 2 ∂q) + ∫ x, g x ^ 2 ∂q) / 2 := by
  have hmajor : Integrable (fun x ↦ (f x ^ 2 + g x ^ 2) / 2) q := (hf.add hg).div_const 2
  have hbound : ∀ᵐ x ∂q, ‖f x * g x‖ ≤ (f x ^ 2 + g x ^ 2) / 2 := by
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (|f x| - |g x|), sq_abs (f x), sq_abs (g x)]
  have h := norm_integral_le_of_norm_le hmajor hbound
  rw [Real.norm_eq_abs, integral_div, integral_add hf hg] at h
  exact h

end SingularLearningTheory.BayesGibbs
