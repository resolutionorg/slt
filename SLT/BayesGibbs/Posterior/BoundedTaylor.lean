/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.GeneralizedTaylor
public import SLT.BayesGibbs.ExpMeasure
public import SLT.BayesGibbs.LaplaceDoubling.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
# Second-order expansion of the predictive value

For a probability measure $Q$ and a function $f$ bounded $Q$-almost everywhere, the predictive
value $-\log E_Q[e^{-f}]$ differs from $E_Q[f] - \operatorname{Var}_Q(f)/2$ by at most any bound
on the third absolute moments of $f$ under the tilted measures $e^{-tf}Q/E_Q[e^{-tf}]$,
$t \in [0, 1]$. Applied at one data point under the posterior, this is the expansion that compares
the Bayes errors with the Gibbs errors. It uses neither normalization of the model nor an envelope
of the density ratio.

## Main definitions

* `ProbabilityTheory.mgfMoment`: the tilted moment $E_Q[s^k e^{ts}]$.

## Main results

* `SingularLearningTheory.BayesGibbs.hasDerivAt_mgfMoment`: for an a.e. bounded $s$, the derivative of
  the $k$-th tilted moment in $t$ is the $(k+1)$-th.
* `SingularLearningTheory.BayesGibbs.abs_predictive_quadratic_remainder_le`: the second-order
  expansion of the predictive value, with the remainder bounded by the tilted third moments.
-/

public section

open MeasureTheory Set Filter Topology

namespace ProbabilityTheory

open SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {Q : Measure W} [IsProbabilityMeasure Q]

/-- The tilted moment $E_Q[s^k e^{ts}]$: the $k$-th derivative in $t$ of the moment generating
function $E_Q[e^{ts}]$ of `s` under `Q`
(`SingularLearningTheory.BayesGibbs.hasDerivAt_mgfMoment`). It supplies the derivatives in the
second-order expansion of the predictive value
(`SingularLearningTheory.BayesGibbs.abs_predictive_quadratic_remainder_le`). -/
@[expose] noncomputable def mgfMoment (Q : Measure W) (s : W → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ w, s w ^ k * Real.exp (t * s w) ∂Q

/-- The bound used only inside the parameter integral for one fixed datum. -/
private theorem norm_pow_mul_exp_le {z B : ℝ} (hz : |z| ≤ B) (hB : 0 ≤ B) (k : ℕ) (t : ℝ) :
    ‖z ^ k * Real.exp (t * z)‖ ≤ B ^ k * Real.exp (|t| * B) := by
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hz k) ?_
    (Real.exp_pos _).le (pow_nonneg hB _)
  apply Real.exp_le_exp.mpr
  calc t * z ≤ |t * z| := le_abs_self _
    _ = |t| * |z| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left hz (abs_nonneg _)

private theorem integrable_mgfMoment {s : W → ℝ} (hs : Measurable s)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ w ∂Q, |s w| ≤ B) (k : ℕ) (t : ℝ) :
    Integrable (fun w ↦ s w ^ k * Real.exp (t * s w)) Q :=
  Integrable.of_bound ((hs.pow_const k).mul (hs.const_mul t).exp).aestronglyMeasurable
    (B ^ k * Real.exp (|t| * B)) (hb.mono fun w hw ↦ norm_pow_mul_exp_le hw hB k t)

/-- Every differentiated tilted moment exists under an a.e. bounded loss.
The local dominator may depend exponentially on B: B is fixed for this one
datum, and is never integrated over the data distribution in this lemma. -/
private theorem hasDerivAt_mgfMoment {s : W → ℝ} (hs : Measurable s)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ w ∂Q, |s w| ≤ B) (k : ℕ) (t : ℝ) :
    HasDerivAt (mgfMoment Q s k) (mgfMoment Q s (k + 1) t) t := by
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := Q)
    (F := fun t w ↦ s w ^ k * Real.exp (t * s w))
    (F' := fun t w ↦ s w ^ (k + 1) * Real.exp (t * s w))
    (s := Metric.ball t 1) (bound := fun _ ↦ B ^ (k + 1) * Real.exp ((|t| + 1) * B))
    (Metric.ball_mem_nhds t zero_lt_one)
    (Eventually.of_forall fun t' ↦
      ((hs.pow_const k).mul (hs.const_mul t').exp).aestronglyMeasurable)
    (integrable_mgfMoment hs hB hb k t)
    ((hs.pow_const (k + 1)).mul (hs.const_mul t).exp).aestronglyMeasurable
    (hb.mono fun w hw t' ht' ↦ by
      have ht'abs : |t'| ≤ |t| + 1 := by
        have ht'd : |t' - t| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using ht'
        calc |t'| = |t + (t' - t)| := by congr 1; ring
          _ ≤ |t| + |t' - t| := abs_add_le _ _
          _ ≤ |t| + 1 := by linarith
      exact (norm_pow_mul_exp_le hw hB (k + 1) t').trans
        (mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ht'abs hB)) (pow_nonneg hB _)))
    (integrable_const _)
    (Eventually.of_forall fun w t' _ ↦
      ((((hasDerivAt_id t').mul_const (s w)).exp).const_mul (s w ^ k)).congr_deriv
        (by dsimp only [id]; rw [pow_succ]; ring))
  exact hd.2

theorem mgfMoment_zero_pos {s : W → ℝ} (hs : Measurable s)
    {B : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ w ∂Q, |s w| ≤ B) (t : ℝ) :
    0 < mgfMoment Q s 0 t := by
  have hi : Integrable (fun w ↦ Real.exp (t * s w)) Q := by
    simpa only [pow_zero, one_mul] using integrable_mgfMoment hs hB hb 0 t
  change 0 < ∫ w, s w ^ 0 * Real.exp (t * s w) ∂Q
  simp only [pow_zero, one_mul]
  rw [integral_pos_iff_support_of_nonneg (fun w ↦ (Real.exp_pos _).le) hi]
  have heq : Function.support (fun w ↦ Real.exp (t * s w)) = univ :=
    eq_univ_of_forall fun w ↦ (Real.exp_pos _).ne'
  rw [heq, measure_univ]
  exact zero_lt_one

/-- Quadratic Bayes-versus-Gibbs expansion, requiring only posterior-a.e.
boundedness at this one datum and a cubic moment bound under its tilts.
No model normalization or density-ratio envelope is used. -/
theorem _root_.SingularLearningTheory.BayesGibbs.abs_predictive_quadratic_remainder_le {f : W → ℝ}
    (hf : Measurable f)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ w ∂Q, |f w| ≤ B)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ w, |f w| ^ 3 ∂Measure.expMeasure Q (fun w ↦ t * f w)) ≤ C) :
    |-(Real.log (∫ w, Real.exp (-f w) ∂Q)) - (∫ w, f w ∂Q) +
      ((∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2) / 2| ≤ C := by
  let s : W → ℝ := fun w ↦ -f w
  have hs : Measurable s := hf.neg
  have hsb : ∀ᵐ w ∂Q, |s w| ≤ B := by simpa only [s, abs_neg] using hb
  have hZ : ∀ t : ℝ, 0 < ∫ w, Real.exp (-(t * f w)) ∂Q := fun t ↦ by
    simpa only [mgfMoment, s, pow_zero, one_mul, mul_neg] using mgfMoment_zero_pos hs hB hsb t
  have hZi : ∀ t : ℝ, Integrable (fun w ↦ Real.exp (-(t * f w))) Q := fun t ↦ by
    simpa only [s, pow_zero, one_mul, mul_neg] using integrable_mgfMoment hs hB hsb 0 t
  let ρ : ℝ → Measure W := fun t ↦ Measure.expMeasure Q (fun w ↦ t * f w)
  letI : ∀ t, IsProbabilityMeasure (ρ t) := fun t ↦ isProbabilityMeasure_expMeasure Q (hZi t) (hZ t)
  have hsr : ∀ t, AEStronglyMeasurable s (ρ t) := fun _ ↦ hs.aestronglyMeasurable
  have h3 : ∀ t, Integrable (fun w ↦ |s w| ^ 3) (ρ t) := fun t ↦
    Integrable.of_bound (hs.abs.pow_const 3).aestronglyMeasurable (B ^ 3) (by
      filter_upwards [ae_expMeasure_of_ae (G := fun w ↦ t * f w) hsb] with w hw
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
      exact pow_le_pow_left₀ (abs_nonneg _) hw 3)
  have hm : ∀ k t, mgfMoment Q s k t / mgfMoment Q s 0 t = ∫ w, s w ^ k ∂ρ t := by
    intro k t
    rw [integral_expMeasure Q (hf.const_mul t) _ (hZ t)]
    simp only [mgfMoment, s, pow_zero, one_mul, mul_neg]
  have htaylor := abs_log_taylor_le_of_third_absolute_moment
    (I₀ := mgfMoment Q s 0) (I₁ := mgfMoment Q s 1)
    (I₂ := mgfMoment Q s 2) (I₃ := mgfMoment Q s 3) ρ s
    (fun t _ ↦ mgfMoment_zero_pos hs hB hsb t)
    (fun t _ ↦ hasDerivAt_mgfMoment hs hB hsb 0 t)
    (fun t _ ↦ hasDerivAt_mgfMoment hs hB hsb 1 t)
    (fun t _ ↦ hasDerivAt_mgfMoment hs hB hsb 2 t)
    (fun t _ ↦ hsr t) (fun t _ ↦ h3 t)
    (fun t _ ↦ by simpa only [pow_one] using hm 1 t)
    (fun t _ ↦ hm 2 t) (fun t _ ↦ hm 3 t)
    (fun t ht ↦ by simpa only [s, abs_neg] using hC t ht)
  have h00 : mgfMoment Q s 0 0 = 1 := by simp [mgfMoment]
  have h10 : mgfMoment Q s 1 0 = -(∫ w, f w ∂Q) := by simp [mgfMoment, s, integral_neg]
  have h20 : mgfMoment Q s 2 0 = ∫ w, f w ^ 2 ∂Q := by simp [mgfMoment, s]
  have h01 : mgfMoment Q s 0 1 = ∫ w, Real.exp (-f w) ∂Q := by simp [mgfMoment, s]
  rw [h00, h10, h20, h01, Real.log_one, sub_zero, div_one, div_one, neg_sq] at htaylor
  have heq : -(Real.log (∫ w, Real.exp (-f w) ∂Q)) - (∫ w, f w ∂Q) +
      ((∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2) / 2 =
      -(Real.log (∫ w, Real.exp (-f w) ∂Q) - (-(∫ w, f w ∂Q)) -
        ((∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2) / 2) := by ring
  rw [heq, abs_neg]
  exact htaylor

end ProbabilityTheory
