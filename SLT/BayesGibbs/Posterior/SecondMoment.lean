/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.FirstMoment
public import SLT.BayesGibbs.Posterior.BoundedSecondOrder
import SLT.BayesGibbs.Posterior.BoundedTaylor
import SLT.BayesGibbs.ExpMeasure
import SLT.BayesGibbs.Posterior.RadialMoment
public import SLT.BayesGibbs.LaplaceDoubling.Basic

/-!
# The gap between the Bayes and the Gibbs loss from second moments

Under the tempered posterior $Q \propto e^{-n\beta K_n}\nu$, with $\sqrt n|K_n - K| \le L\sqrt K$
and $|f| \le A\sqrt K$ almost everywhere for the prior and the Laplace doubling bound with
constant $D$, the predictive value $-\log E_Q[e^{-f}]$ differs from $E_Q[f]$ by at most
$$\frac{A^2}{2n}\Bigl(\frac4\beta\log D + 4\bigl(L + A/(\beta\sqrt n)\bigr)^2\Bigr).$$
The proof bounds $n$ times the second moment of $f$ under every tilt
$e^{-n\beta K_n - \sigma f}\nu$ with $\sigma \in [0, 1]$, through the posterior mean of $K$, and
applies `SingularLearningTheory.BayesGibbs.abs_predictive_sub_mean_le_of_second_moment`.

## Main results

* `SingularLearningTheory.BayesGibbs.evidence_integrable_pos_of_ae_lower_bound`: for a finite nonzero
  prior and an exponent $G$ bounded below almost everywhere, $e^{-G}$ is integrable and the
  evidence $\int e^{-G}\,d\nu$ is positive.
* `SingularLearningTheory.BayesGibbs.tilted_posterior_second_moment_le`: the bound on $n$ times the
  second moment of $f$ under a tilted posterior.
* `SingularLearningTheory.BayesGibbs.abs_predictive_posterior_sub_mean_scaled_le`: the bound above,
  scaled by $n$.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- Finite nonzero prior mass and an a.e. lower bound on G give an integrable,
strictly positive evidence. The bound is only for fixed data. -/
theorem evidence_integrable_pos_of_ae_lower_bound {G : W → ℝ}
    (hν : ν ≠ 0) (hG : Measurable G) {c : ℝ} (hGlo : ∀ᵐ w ∂ν, -c ≤ G w) :
    Integrable (fun w ↦ Real.exp (-G w)) ν ∧ 0 < ∫ w, Real.exp (-G w) ∂ν := by
  have hi : Integrable (fun w ↦ Real.exp (-G w)) ν :=
    Integrable.of_bound hG.neg.exp.aestronglyMeasurable (Real.exp c) (hGlo.mono fun w hw ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (by linarith))
  refine ⟨hi, ?_⟩
  rw [integral_pos_iff_support_of_nonneg (fun w ↦ (Real.exp_pos _).le) hi]
  have hs : Function.support (fun w ↦ Real.exp (-G w)) = univ :=
    eq_univ_of_forall fun w ↦ (Real.exp_pos _).ne'
  rw [hs]
  exact Measure.measure_univ_pos.mpr hν

/-- Polynomial second moment under the single-datum tilted posterior.
Only prior-a.e. relative and feature bounds are assumed. -/
private theorem tilted_posterior_second_moment_le {K Kn f : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hKnm : Measurable Kn) (hfm : Measurable f)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β L A D σ : ℝ} (hn : 0 < n) (hβ : 0 < β) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hσ : σ ∈ Icc 0 1)
    (he : ∀ᵐ w ∂ν, Real.sqrt n * |Kn w - K w| ≤ L * Real.sqrt (K w))
    (hf : ∀ᵐ w ∂ν, |f w| ≤ A * Real.sqrt (K w))
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    IsProbabilityMeasure (Measure.expMeasure ν (fun w ↦ n * β * Kn w + σ * f w)) ∧
      Integrable (fun w ↦ f w ^ 2) (Measure.expMeasure ν (fun w ↦ n * β * Kn w + σ * f w)) ∧
      n * (∫ w, f w ^ 2 ∂Measure.expMeasure ν (fun w ↦ n * β * Kn w + σ * f w)) ≤
        A ^ 2 * (4 / β * Real.log D + 4 * (L + A / (β * Real.sqrt n)) ^ 2) := by
  let G := fun w ↦ n * β * Kn w + σ * f w
  have hbounds : ∀ᵐ w ∂ν,
      n * β * (K w / 2) - β / 2 * (L + A / (β * Real.sqrt n)) ^ 2 ≤ G w ∧
      G w ≤ n * β * (3 / 2 * K w) + β / 2 * (L + A / (β * Real.sqrt n)) ^ 2 := by
    filter_upwards [hK0, he, hf] with w hw0 hwe hwf
    exact tilted_exponent_bounds hw0 hn hβ hσ hwe hwf
  obtain ⟨hp, hKi, hKb⟩ := posterior_first_moment_le_ae (G := G) hν hKm
    ((hKnm.const_mul _).add (hfm.const_mul _)) hK0 hKB hn hβ
    (by positivity : 0 ≤ β / 2 * (L + A / (β * Real.sqrt n)) ^ 2) hD
    (hbounds.mono fun _ h ↦ h.1) (hbounds.mono fun _ h ↦ h.2) hLD
  letI := hp
  have hf2 : ∀ᵐ w ∂Measure.expMeasure ν G, f w ^ 2 ≤ A ^ 2 * K w := by
    filter_upwards [ae_expMeasure_of_ae hK0, ae_expMeasure_of_ae hf] with w hw0 hwf
    have hsq : |f w| ^ 2 ≤ (A * Real.sqrt (K w)) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hwf 2
    simpa only [sq_abs, mul_pow, Real.sq_sqrt hw0] using hsq
  have hfi : Integrable (fun w ↦ f w ^ 2) (Measure.expMeasure ν G) :=
    (hKi.const_mul (A ^ 2)).mono' (hfm.pow_const 2).aestronglyMeasurable
      (hf2.mono fun w hw ↦ by rwa [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] )
  have hi : (∫ w, f w ^ 2 ∂Measure.expMeasure ν G) ≤ A ^ 2 * ∫ w, K w ∂Measure.expMeasure ν G := by
    rw [← integral_const_mul]
    exact integral_mono_ae hfi (hKi.const_mul _) hf2
  refine ⟨hp, hfi, ?_⟩
  have hb := mul_le_mul_of_nonneg_left hKb (sq_nonneg A)
  have hi' := mul_le_mul_of_nonneg_left hi hn.le
  have hcoeff : 8 / β * (β / 2 * (L + A / (β * Real.sqrt n)) ^ 2) =
      4 * (L + A / (β * Real.sqrt n)) ^ 2 := by field_simp; ring
  rw [hcoeff] at hb
  nlinarith

/-- ExpMeasure Bayes-minus-Gibbs bound, already scaled by n.
Its right side is polynomial in the empirical and single-datum envelopes. -/
theorem abs_predictive_posterior_sub_mean_scaled_le {K Kn f : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hKnm : Measurable Kn) (hfm : Measurable f)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β L A D : ℝ} (hn : 0 < n) (hβ : 0 < β) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (he : ∀ᵐ w ∂ν, Real.sqrt n * |Kn w - K w| ≤ L * Real.sqrt (K w))
    (hf : ∀ᵐ w ∂ν, |f w| ≤ A * Real.sqrt (K w))
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    n * |-(Real.log (∫ w, Real.exp (-f w) ∂Measure.expMeasure ν (fun w ↦ n * β * Kn w))) -
      (∫ w, f w ∂Measure.expMeasure ν (fun w ↦ n * β * Kn w))| ≤
        A ^ 2 / 2 * (4 / β * Real.log D + 4 * (L + A / (β * Real.sqrt n)) ^ 2) := by
  let G := fun w ↦ n * β * Kn w
  let Q := Measure.expMeasure ν G
  have hG : Measurable G := hKnm.const_mul _
  have htilt := fun (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) ↦ tilted_posterior_second_moment_le (σ := σ) hν hKm hKnm hfm
    hK0 hKB hn hβ hA hD hσ he hf hLD
  have hQ : IsProbabilityMeasure Q := by
    simpa only [zero_mul, add_zero] using (htilt 0 ⟨le_rfl, zero_le_one⟩).1
  letI := hQ
  have hZe : ∀ σ ∈ Icc (0 : ℝ) 1,
      0 < ∫ w, Real.exp (-(G w + σ * f w)) ∂ν := by
    intro σ hσ
    apply (evidence_integrable_pos_of_ae_lower_bound hν
      (hG.add (hfm.const_mul σ)) (c := β / 2 * (L + A / (β * Real.sqrt n)) ^ 2) ?_).2
    filter_upwards [hK0, he, hf] with w hw0 hwe hwf
    have hb := (tilted_exponent_bounds hw0 hn hβ hσ hwe hwf).1
    have hnon : 0 ≤ n * β * (K w / 2) := by positivity
    exact le_trans (by linarith) hb
  have hZ : 0 < ∫ w, Real.exp (-G w) ∂ν := by
    simpa only [zero_mul, add_zero] using hZe 0 ⟨le_rfl, zero_le_one⟩
  have hfb : ∀ᵐ w ∂Q, |f w| ≤ A * Real.sqrt (max 0 B) := by
    filter_upwards [ae_expMeasure_of_ae hf, ae_expMeasure_of_ae hKB] with w hwf hwB
    exact hwf.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hwB.trans (le_max_right _ _))) hA)
  have hZQ : ∀ σ, 0 < ∫ w, Real.exp (-(σ * f w)) ∂Q := fun σ ↦ by
    simpa only [ProbabilityTheory.mgfMoment, pow_zero, one_mul, Pi.neg_apply, mul_neg] using
      ProbabilityTheory.mgfMoment_zero_pos (Q := Q) hfm.neg (mul_nonneg hA (Real.sqrt_nonneg _))
        (by simpa only [Pi.neg_apply, abs_neg] using hfb) σ
  have hsec : ∀ σ ∈ Icc (0 : ℝ) 1,
      (∫ w, f w ^ 2 ∂Measure.expMeasure Q (fun w ↦ σ * f w)) ≤
        A ^ 2 * (4 / β * Real.log D + 4 * (L + A / (β * Real.sqrt n)) ^ 2) / n := by
    intro σ hσ
    rw [integral_expMeasure Q (hfm.const_mul _) _ (hZQ σ)]
    rw [integral_tilt_expMeasure hG hfm _ σ hZ (hZe σ hσ)]
    apply (le_div_iff₀ hn).mpr
    simpa only [G, mul_comm n] using (htilt σ hσ).2.2
  have hb := abs_predictive_sub_mean_le_of_second_moment hfm
    (mul_nonneg hA (Real.sqrt_nonneg _)) hfb hsec
  have hb' := mul_le_mul_of_nonneg_left hb hn.le
  convert hb' using 1 <;> field_simp <;> ring

end SingularLearningTheory.BayesGibbs
