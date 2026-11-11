/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FiniteSample.PosteriorFive
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The population form of the posterior variance of a feature

Let $Q$ be a probability measure on parameters and $q$ the data law, with
$|f(x, w)| \le A(x)\sqrt{K(w)}$, $A^2$ integrable and $K$ bounded above.
`SingularLearningTheory.BayesGibbs.integrable_feature_square_and_product` makes $f(x, w)^2$ and
$f(x, w)f(x, v)$ integrable for $q \otimes Q$ and $q \otimes Q \otimes Q$, and
`SingularLearningTheory.BayesGibbs.integrable_fresh_variance_and_eq` uses Fubini to show that
$x \mapsto \mathrm{Var}_Q[f(x, \cdot)]$ is integrable, with
$$E_q\bigl[\mathrm{Var}_Q[f(x, \cdot)]\bigr] = E_Q\bigl[E_q[f(x, w)^2]\bigr]
  - E_{Q \otimes Q}\bigl[E_q[f(x, w)f(x, v)]\bigr].$$
This is the population form of the variance in the Taylor residual of the Bayes generalization
error.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- The data envelope justifies the joint integrals of the square and pair product. -/
theorem integrable_feature_square_and_product
    {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    {q : Measure X} [IsProbabilityMeasure q] {Q : Measure U} [IsProbabilityMeasure Q]
    {f : X → U → ℝ} {K : U → ℝ} {A : X → ℝ} {B : ℝ}
    (hf : Measurable (Function.uncurry f)) (hAm : Measurable A)
    (hA2 : Integrable (fun x ↦ A x ^ 2) q) (hA0 : ∀ x, 0 ≤ A x)
    (hKB : ∀ᵐ w ∂Q, K w ≤ B)
    (hbound : ∀ᵐ x ∂q, ∀ᵐ w ∂Q, |f x w| ≤ A x * Real.sqrt (K w)) :
    Integrable (fun z : X × U ↦ f z.1 z.2 ^ 2) (q.prod Q) ∧
      Integrable (fun z : X × (U × U) ↦ f z.1 z.2.1 * f z.1 z.2.2) (q.prod (Q.prod Q)) := by
  let M := Real.sqrt (max 0 B)
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hb : ∀ᵐ x ∂q, ∀ᵐ w ∂Q, |f x w| ≤ A x * M := by
    filter_upwards [hbound] with x hx
    filter_upwards [hx, hKB] with w hw hwB
    exact hw.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hwB.trans (le_max_right _ _))) (hA0 x))
  have hDm : Measurable (fun z : X × U ↦ f z.1 z.2 ^ 2) := hf.pow_const 2
  have hDb : ∀ᵐ z ∂q.prod Q, ‖f z.1 z.2 ^ 2‖ ≤ A z.1 ^ 2 * M ^ 2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hDm.norm (((hAm.comp measurable_fst).pow_const 2).mul_const _))).mpr
    filter_upwards [hb] with x hx
    filter_upwards [hx] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change f x w ^ 2 ≤ A x ^ 2 * M ^ 2
    simpa only [sq_abs, mul_pow] using pow_le_pow_left₀ (abs_nonneg _) hw 2
  have hDi : Integrable (fun z : X × U ↦ f z.1 z.2 ^ 2) (q.prod Q) :=
    ((hA2.mul_const (M ^ 2)).comp_fst Q).mono' hDm.aestronglyMeasurable hDb
  have hQm : Measurable (fun z : X × (U × U) ↦ f z.1 z.2.1 * f z.1 z.2.2) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  have hQb : ∀ᵐ z ∂q.prod (Q.prod Q),
      ‖f z.1 z.2.1 * f z.1 z.2.2‖ ≤ A z.1 ^ 2 * M ^ 2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hQm.norm (((hAm.comp measurable_fst).pow_const 2).mul_const _))).mpr
    filter_upwards [hb] with x hx
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hx,
      Measure.quasiMeasurePreserving_snd.ae hx] with z hw hv
    change ‖f x z.1 * f x z.2‖ ≤ A x ^ 2 * M ^ 2
    rw [Real.norm_eq_abs, abs_mul]
    calc
      |f x z.1| * |f x z.2| ≤ (A x * M) * (A x * M) :=
        mul_le_mul hw hv (abs_nonneg _) (mul_nonneg (hA0 x) hM)
      _ = _ := by ring
  have hQi : Integrable (fun z : X × (U × U) ↦ f z.1 z.2.1 * f z.1 z.2.2)
      (q.prod (Q.prod Q)) :=
    ((hA2.mul_const (M ^ 2)).comp_fst (Q.prod Q)).mono' hQm.aestronglyMeasurable hQb
  exact ⟨hDi, hQi⟩

/-- The population posterior variance is exactly the diagonal population
second moment minus the posterior-pair population product. All Fubini steps
follow from the existing data envelope and compact upper bound on K. -/
theorem integrable_fresh_variance_and_eq
    {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    {q : Measure X} [IsProbabilityMeasure q] {Q : Measure U} [IsProbabilityMeasure Q]
    {f : X → U → ℝ} {K : U → ℝ} {A : X → ℝ} {B : ℝ}
    (hf : Measurable (Function.uncurry f)) (hAm : Measurable A)
    (hA2 : Integrable (fun x ↦ A x ^ 2) q) (hA0 : ∀ x, 0 ≤ A x)
    (hKB : ∀ᵐ w ∂Q, K w ≤ B)
    (hbound : ∀ᵐ x ∂q, ∀ᵐ w ∂Q, |f x w| ≤ A x * Real.sqrt (K w)) :
    Integrable (posteriorFeatureVariance Q f) q ∧
      (∫ x, posteriorFeatureVariance Q f x ∂q) =
        (∫ w, ∫ x, f x w ^ 2 ∂q ∂Q) -
        ∫ z, ∫ x, f x z.1 * f x z.2 ∂q ∂Q.prod Q := by
  obtain ⟨hDi, hQi⟩ := integrable_feature_square_and_product hf hAm hA2 hA0 hKB hbound
  have hmeanSq : (fun x ↦ (∫ w, f x w ∂Q) ^ 2) =
      fun x ↦ ∫ z, f x z.1 * f x z.2 ∂Q.prod Q := by
    funext x
    rw [integral_prod_mul, pow_two]
  have hmeanSqi : Integrable (fun x ↦ (∫ w, f x w ∂Q) ^ 2) q := by
    rw [hmeanSq]
    exact hQi.integral_prod_left
  refine ⟨hDi.integral_prod_left.sub hmeanSqi, ?_⟩
  change (∫ x, (∫ w, f x w ^ 2 ∂Q) - (∫ w, f x w ∂Q) ^ 2 ∂q) = _
  rw [integral_sub hDi.integral_prod_left hmeanSqi, hmeanSq]
  congr 1
  · exact integral_integral_swap hDi
  · exact integral_integral_swap hQi

end SingularLearningTheory.BayesGibbs
