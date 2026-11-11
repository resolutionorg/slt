/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.RadialMomentAE
public import SLT.BayesGibbs.Posterior.SecondMoment
public import SLT.BayesGibbs.Posterior.BoundedTaylor
public import SLT.BayesGibbs.FiniteSampleMoments
import SLT.BayesGibbs.ExpMeasure
import SLT.BayesGibbs.Posterior.RadialMoment
public import SLT.BayesGibbs.LaplaceDoubling.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The cubic remainder of the predictive expansion

Under the tempered posterior $Q \propto e^{-n\beta K_n}\nu$, with $\sqrt n|K_n - K| \le L\sqrt K$
and $|f| \le A\sqrt K$ almost everywhere for the prior and the Laplace doubling bound
$\int e^{-n\beta K/4}\,d\nu \le D\int e^{-3n\beta K/2}\,d\nu$, the predictive value
$-\log E_Q[e^{-f}]$ equals $E_Q[f] - \mathrm{Var}_Q[f]/2$ up to a remainder at most
$$A^3\Bigl(\frac{4}{n\beta}\Bigr)^{3/2}
  \Bigl(\bigl(2(\log D + \beta(L + A/(\beta\sqrt n))^2)\bigr)^{3/2} + C\Bigr),$$
where $y^{3/2} \le Ce^{y/2}$ for $y \ge 0$. The proof bounds the third absolute moment of $f$
under every tilt $e^{-n\beta K_n - \sigma f}\nu$ with $\sigma \in [0, 1]$, through the $3/2$
moment of $K$. The full posterior variance is kept, with no realizability assumption.

## Main results

* `SingularLearningTheory.BayesGibbs.tilted_posterior_third_moment_le`: the third absolute moment of
  $f$ under a tilted posterior.
* `SingularLearningTheory.BayesGibbs.abs_predictive_posterior_quadratic_remainder_le`: the bound on
  the remainder.
* `SingularLearningTheory.BayesGibbs.radial_three_halves_polynomial_bound`: the scalar bound
  $(2(\log D + \beta t^2))^{3/2} + C \le H(1 + t)^3$ for $t \ge 0$, which makes the remainder
  bound polynomial in $L$ and $A$.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- The third absolute loss moment under the one-datum posterior tilt.
This is the analytic bound needed for the quadratic Bayes expansion; its
later data integral costs only the third and sixth feature moments. -/
private theorem tilted_posterior_third_moment_le {K Kn f : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hKnm : Measurable Kn) (hfm : Measurable f)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β L A D C σ : ℝ} (hn : 0 < n) (hβ : 0 < β) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hC : 0 ≤ C)
    (hscalar : ∀ y : ℝ, 0 ≤ y → y ^ (3 / 2 : ℝ) ≤ C * Real.exp (y / 2))
    (hσ : σ ∈ Icc 0 1)
    (he : ∀ᵐ w ∂ν, Real.sqrt n * |Kn w - K w| ≤ L * Real.sqrt (K w))
    (hf : ∀ᵐ w ∂ν, |f w| ≤ A * Real.sqrt (K w))
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    IsProbabilityMeasure (Measure.expMeasure ν (fun w ↦ n * β * Kn w + σ * f w)) ∧
      Integrable (fun w ↦ |f w| ^ 3) (Measure.expMeasure ν (fun w ↦ n * β * Kn w + σ * f w)) ∧
      (∫ w, |f w| ^ 3 ∂Measure.expMeasure ν (fun w ↦ n * β * Kn w + σ * f w)) ≤
        A ^ 3 * ((4 / (n * β)) ^ (3 / 2 : ℝ) *
          ((2 * (Real.log D + β * (L + A / (β * Real.sqrt n)) ^ 2)) ^ (3 / 2 : ℝ) + C)) := by
  let G := fun w ↦ n * β * Kn w + σ * f w
  have hbounds : ∀ᵐ w ∂ν,
      n * β * (K w / 2) - β / 2 * (L + A / (β * Real.sqrt n)) ^ 2 ≤ G w ∧
      G w ≤ n * β * (3 / 2 * K w) + β / 2 * (L + A / (β * Real.sqrt n)) ^ 2 := by
    filter_upwards [hK0, he, hf] with w hw0 hwe hwf
    exact tilted_exponent_bounds hw0 hn hβ hσ hwe hwf
  obtain ⟨hp, hKi, hKb⟩ := posterior_rpow_moment_le_ae (G := G) hν hKm
    ((hKnm.const_mul _).add (hfm.const_mul _)) hK0 hKB hn hβ
    (by positivity : 0 ≤ β / 2 * (L + A / (β * Real.sqrt n)) ^ 2) hD
    (by norm_num : (0 : ℝ) ≤ 3 / 2) hC hscalar
    (hbounds.mono fun _ h ↦ h.1) (hbounds.mono fun _ h ↦ h.2) hLD
  letI := hp
  have hf3 : ∀ᵐ w ∂Measure.expMeasure ν G, |f w| ^ 3 ≤ A ^ 3 * (K w) ^ (3 / 2 : ℝ) := by
    filter_upwards [ae_expMeasure_of_ae hK0, ae_expMeasure_of_ae hf] with w hw0 hwf
    have hpow := pow_le_pow_left₀ (abs_nonneg _) hwf 3
    have hs : Real.sqrt (K w) ^ 3 = (K w) ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hw0]
      norm_num
    simpa only [mul_pow, hs] using hpow
  have hfi : Integrable (fun w ↦ |f w| ^ 3) (Measure.expMeasure ν G) :=
    (hKi.const_mul (A ^ 3)).mono' (hfm.abs.pow_const 3).aestronglyMeasurable
      (hf3.mono fun w hw ↦ by
        rwa [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) _)] )
  refine ⟨hp, hfi, ?_⟩
  have hi : (∫ w, |f w| ^ 3 ∂Measure.expMeasure ν G) ≤ A ^ 3 * ∫ w, (K w) ^ (3 / 2 : ℝ)
      ∂Measure.expMeasure ν G := by
    rw [← integral_const_mul]
    exact integral_mono_ae hfi (hKi.const_mul _) hf3
  have hcoeff : 2 * (β / 2 * (L + A / (β * Real.sqrt n)) ^ 2) =
      β * (L + A / (β * Real.sqrt n)) ^ 2 := by ring
  rw [hcoeff] at hKb
  exact hi.trans (mul_le_mul_of_nonneg_left hKb (pow_nonneg hA _))

/-- Exact quadratic expansion for the posterior. The full variance
term is retained, with no diagonal normalization or realizability premise. -/
theorem abs_predictive_posterior_quadratic_remainder_le {K Kn f : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hKnm : Measurable Kn) (hfm : Measurable f)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β L A D C : ℝ} (hn : 0 < n) (hβ : 0 < β) (hA : 0 ≤ A) (hD : 1 ≤ D)
    (hC : 0 ≤ C)
    (hscalar : ∀ y : ℝ, 0 ≤ y → y ^ (3 / 2 : ℝ) ≤ C * Real.exp (y / 2))
    (he : ∀ᵐ w ∂ν, Real.sqrt n * |Kn w - K w| ≤ L * Real.sqrt (K w))
    (hf : ∀ᵐ w ∂ν, |f w| ≤ A * Real.sqrt (K w))
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    let Q := Measure.expMeasure ν (fun w ↦ n * β * Kn w)
    |-(Real.log (∫ w, Real.exp (-f w) ∂Q)) - (∫ w, f w ∂Q) +
      ((∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2) / 2| ≤
        A ^ 3 * ((4 / (n * β)) ^ (3 / 2 : ℝ) *
          ((2 * (Real.log D + β * (L + A / (β * Real.sqrt n)) ^ 2)) ^ (3 / 2 : ℝ) + C)) := by
  let G := fun w ↦ n * β * Kn w
  let Q := Measure.expMeasure ν G
  have hG : Measurable G := hKnm.const_mul _
  have htilt := fun (σ : ℝ) (hσ : σ ∈ Icc (0 : ℝ) 1) ↦
    tilted_posterior_third_moment_le (σ := σ) hν hKm hKnm hfm
    hK0 hKB hn hβ hA hD hC hscalar hσ he hf hLD
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
  apply abs_predictive_quadratic_remainder_le hfm
    (mul_nonneg hA (Real.sqrt_nonneg _)) hfb
  intro σ hσ
  rw [integral_expMeasure Q (hfm.const_mul _) _ (hZQ σ)]
  rw [integral_tilt_expMeasure hG hfm _ σ hZ (hZe σ hσ)]
  exact (htilt σ hσ).2.2

/-- A purely scalar cubic growth estimate for the radial moment bound.
This is the step which turns posterior exponential moments into a polynomial
data envelope before the outer integral is taken. -/
theorem radial_three_halves_polynomial_bound {D β C : ℝ}
    (hD : 1 ≤ D) (hβ : 0 < β) (hC : 0 ≤ C) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ t : ℝ, 0 ≤ t →
      (2 * (Real.log D + β * t ^ 2)) ^ (3 / 2 : ℝ) + C ≤ H * (1 + t) ^ 3 := by
  have hlog : 0 ≤ Real.log D := Real.log_nonneg hD
  let c := 1 + 2 * Real.log D + 2 * β
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨c ^ (3 / 2 : ℝ) + C, by positivity, fun t ht ↦ ?_⟩
  have he : 2 * (Real.log D + β * t ^ 2) ≤ c * (1 + t) ^ 2 := by
    dsimp [c]
    nlinarith [Real.log_nonneg hD, mul_nonneg (Real.log_nonneg hD) (sq_nonneg t),
      mul_nonneg (Real.log_nonneg hD) ht, mul_nonneg hβ.le ht]
  have hpow := Real.rpow_le_rpow
    (show 0 ≤ 2 * (Real.log D + β * t ^ 2) by positivity) he (by norm_num : (0 : ℝ) ≤ 3 / 2)
  rw [Real.mul_rpow hc (sq_nonneg _), Real.sq_rpow_three_halves (by linarith : 0 ≤ 1 + t)] at hpow
  have h1 : 1 ≤ (1 + t) ^ 3 := one_le_pow₀ (by linarith : 1 ≤ 1 + t)
  nlinarith [mul_le_mul_of_nonneg_left h1 hC]

end SingularLearningTheory.BayesGibbs
