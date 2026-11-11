/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CubicResidualL1
public import SLT.BayesGibbs.EnvelopeSixthMoments
import SLT.BayesGibbs.Posterior.CubicRemainder
import SLT.BayesGibbs.FiniteSampleMoments
import SLT.Probability.Moments.OfExponential
public import SLT.BayesGibbs.LaplaceDoubling.Basic

/-!
# A uniform rate for the cubic remainder of the predictive expansion

Under the tempered posterior $Q \propto e^{-n\beta K_n}\nu$, the predictive value
$-\log E_Q[e^{-f}]$ equals $E_Q[f] - \mathrm{Var}_Q[f]/2$ up to a cubic remainder. This module
gives one constant $C$ such that, for every $n > 0$ at which the Laplace doubling bound
$\int e^{-n\beta K/4}\,d\nu \le D\int e^{-3n\beta K/2}\,d\nu$ holds, and for all measurable
$K_n$ and $f$ with $\sqrt n|K_n - K| \le L\sqrt K$ and $|f| \le A\sqrt K$ almost everywhere for
the prior, the remainder scaled by $n$ is at most
`SingularLearningTheory.BayesGibbs.cubicResidualRate` $= 128C/\sqrt n + 4C/(\beta^3 n^2)$ times
$1 + L^6 + A^6$. The rate tends to zero. The bound feeds the Taylor bounds of the Bayes errors,
`SingularLearningTheory.BayesGibbs.exists_finiteSample_taylor_bounds`.

## Main results

* `SingularLearningTheory.BayesGibbs.cubicResidualRate_tendsto_zero`: the rate tends to zero.
* `SingularLearningTheory.BayesGibbs.exists_finiteSample_posterior_cubic_rate`: the bound, with one constant
  for every sample size, loss, datum and envelope.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- Deterministic rate multiplying the sixth-moment residual dominator. -/
@[expose] noncomputable def cubicResidualRate (β C : ℝ) (n : ℕ) : ℝ :=
  128 * C * (Real.sqrt n)⁻¹ + 4 * C * ((Real.sqrt n)⁻¹) ^ 4 / β ^ 3

theorem cubicResidualRate_nonneg {β C : ℝ} (hβ : 0 < β) (hC : 0 ≤ C) (n : ℕ) :
    0 ≤ cubicResidualRate β C n := by unfold cubicResidualRate; positivity

theorem cubicResidualRate_tendsto_zero (β C : ℝ) :
    Tendsto (cubicResidualRate β C) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ ↦ (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  change Tendsto (fun n : ℕ ↦
    128 * C * (Real.sqrt n)⁻¹ + 4 * C * ((Real.sqrt n)⁻¹) ^ 4 / β ^ 3) atTop (𝓝 0)
  simpa using
    (h.const_mul (128 * C)).add (((h.pow 4).const_mul (4 * C)).div_const (β ^ 3))

/-- A constant independent of sample size, sample, and datum controls the
actual posterior quadratic remainder by a vanishing rate times sixth powers.
All evidence and tilted-integrability premises are derived internally.
The only asymptotic premise is the deterministic Laplace doubling bound. -/
theorem exists_finiteSample_posterior_cubic_rate {W : Type*} [MeasurableSpace W]
    {ν : Measure W} [IsFiniteMeasure ν] {K : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w)
    {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {β D : ℝ} (hβ : 0 < β) (hD : 1 ≤ D) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ), 0 < n → ∀ (Kn f : W → ℝ),
      Measurable Kn → Measurable f → ∀ L A : ℝ, 0 ≤ L → 0 ≤ A →
      (∀ᵐ w ∂ν, Real.sqrt n * |Kn w - K w| ≤ L * Real.sqrt (K w)) →
      (∀ᵐ w ∂ν, |f w| ≤ A * Real.sqrt (K w)) →
      (∫ w, Real.exp (-((n : ℝ) * β / 4 * K w)) ∂ν ≤
        D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w)) ∂ν) →
      let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * Kn w)
      (n : ℝ) * |-(Real.log (∫ w, Real.exp (-f w) ∂Q)) - (∫ w, f w ∂Q) +
        ((∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2) / 2| ≤
          cubicResidualRate β C n * (1 + L ^ 6 + A ^ 6) := by
  obtain ⟨C₀, hC₀, hscalar⟩ := Real.exists_rpow_le_exp_half (by norm_num : (0 : ℝ) ≤ 3 / 2)
  obtain ⟨H, hH, hpoly⟩ := radial_three_halves_polynomial_bound hD hβ hC₀
  let C := (4 / β) ^ (3 / 2 : ℝ) * H
  have hC : 0 ≤ C := mul_nonneg (Real.rpow_nonneg (by positivity) _) hH
  refine ⟨C, hC, fun n hn Kn f hKnm hfm L A hL hA he hf hLD ↦ ?_⟩
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  let h := (Real.sqrt n)⁻¹
  have hh : 0 ≤ h := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn'.le
  have hnh : (n : ℝ) * h ^ 2 = 1 := by dsimp [h]; rw [inv_pow, hsq]; exact mul_inv_cancel₀ hn'.ne'
  have hshift : L + A / (β * Real.sqrt n) = L + h * A / β := by dsimp [h]; ring
  have hrad : (4 / ((n : ℝ) * β)) ^ (3 / 2 : ℝ) = (4 / β) ^ (3 / 2 : ℝ) * h ^ 3 := by
    have heq : 4 / ((n : ℝ) * β) = (4 / β) * h ^ 2 := by
      dsimp [h]
      rw [inv_pow, hsq]
      ring
    rw [heq, Real.mul_rpow (by positivity : 0 ≤ 4 / β) (sq_nonneg h), Real.sq_rpow_three_halves hh]
  have hpost := abs_predictive_posterior_quadratic_remainder_le hν hKm hKnm hfm hK0 hKB
    hn' hβ hA hD hC₀ hscalar he hf hLD
  have hb : (let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * Kn w)
      |-(Real.log (∫ w, Real.exp (-f w) ∂Q)) - (∫ w, f w ∂Q) +
        ((∫ w, f w ^ 2 ∂Q) - (∫ w, f w ∂Q) ^ 2) / 2|) ≤
      C * h ^ 3 * A ^ 3 * (1 + L + h * A / β) ^ 3 := by
    refine hpost.trans ?_
    have hp := mul_le_mul_of_nonneg_left
      (hpoly (L + A / (β * Real.sqrt n)) (by positivity))
      (show 0 ≤ A ^ 3 * (4 / ((n : ℝ) * β)) ^ (3 / 2 : ℝ) by positivity)
    rw [hrad, hshift] at hp
    rw [hrad, hshift]
    dsimp only [C]
    convert hp using 1 <;> ring
  have hfin := scaled_cubic_remainder_le_sixth hn'.le hh hnh hA hL hβ hC hb
  simpa only [cubicResidualRate, h] using hfin

end SingularLearningTheory.BayesGibbs
