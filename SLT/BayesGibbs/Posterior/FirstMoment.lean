/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.RadialMoment
public import SLT.BayesGibbs.ExpMeasure
public import SLT.BayesGibbs.LaplaceDoubling.Basic

/-!
# First moment of the posterior

Let $\nu$ be a nonzero finite measure and $G$ a potential with
$n\beta K/2 - c \le G \le 3n\beta K/2 + c$, as the scaled empirical loss $n\beta K_n$ is, and let
$\nu$ satisfy the Laplace doubling bound
$\int e^{-n\beta K/4}\,d\nu \le D\int e^{-3n\beta K/2}\,d\nu$. Then the tilted measure
$e^{-G}\nu / Z$ is a probability measure, $K$ is integrable under it, and
$nE[K] \le (4/\beta)\log D + (8/\beta)c$. This is the bound on $nG_g$ at a fixed sample from which
the bounds on the posterior observables of [Wat09, Theorem 6.8] start.

## Main results

* `SingularLearningTheory.BayesGibbs.posterior_first_moment_le`: the bound, for $K \ge 0$ everywhere.
* `SingularLearningTheory.BayesGibbs.posterior_first_moment_le_ae`: the bound, for $K \ge 0$ almost
  everywhere under $\nu$, as for the prior restricted to the parameter set.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- First posterior moment, discharging all evidence and integrability
premises of the Laplace-doubling estimate. -/
private theorem posterior_first_moment_le {K G : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hGm : Measurable G)
    (hK0 : ∀ w, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β c D : ℝ} (hn : 0 < n) (hβ : 0 < β) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hlow : ∀ᵐ w ∂ν, n * β * (K w / 2) - c ≤ G w)
    (hup : ∀ᵐ w ∂ν, G w ≤ n * β * (3 / 2 * K w) + c)
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    IsProbabilityMeasure (Measure.expMeasure ν G) ∧
      Integrable K (Measure.expMeasure ν G) ∧
      n * (∫ w, K w ∂Measure.expMeasure ν G) ≤ 4 / β * Real.log D + 8 / β * c := by
  have hGint : Integrable (fun w ↦ Real.exp (-G w)) ν :=
    Integrable.of_bound hGm.neg.exp.aestronglyMeasurable (Real.exp c) (by
      filter_upwards [hlow] with w hw
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      apply Real.exp_le_exp.mpr
      have hw0 := hK0 w
      have : 0 ≤ n * β * (K w / 2) := by positivity
      linarith)
  have hZ : 0 < ∫ w, Real.exp (-G w) ∂ν := by
    rw [integral_pos_iff_support_of_nonneg (fun w ↦ (Real.exp_pos _).le) hGint]
    have hs : Function.support (fun w ↦ Real.exp (-G w)) = univ :=
      eq_univ_of_forall fun w ↦ (Real.exp_pos _).ne'
    rw [hs]
    exact Measure.measure_univ_pos.mpr hν
  have hKint : Integrable (fun w ↦ K w * Real.exp (-G w)) ν :=
    Integrable.of_bound (hKm.mul hGm.neg.exp).aestronglyMeasurable
      (max 0 B * Real.exp c) (by
        filter_upwards [hlow, hKB] with w hw hB
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK0 w), abs_of_pos (Real.exp_pos _)]
        have he : Real.exp (-G w) ≤ Real.exp c := by
          apply Real.exp_le_exp.mpr
          have hw0 := hK0 w
          have : 0 ≤ n * β * (K w / 2) := by positivity
          linarith
        exact mul_le_mul (hB.trans (le_max_right _ _)) he (Real.exp_pos _).le (le_max_left _ _))
  have hEint : Integrable (fun w ↦ Real.exp (n * β / 4 * K w) * Real.exp (-G w)) ν :=
    Integrable.of_bound ((hKm.const_mul _).exp.mul hGm.neg.exp).aestronglyMeasurable
      (Real.exp c) (by
        filter_upwards [hlow] with w hw
        rw [Real.norm_eq_abs, abs_of_pos (mul_pos (Real.exp_pos _) (Real.exp_pos _)),
          ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        have hw0 := hK0 w
        have : 0 ≤ n * β / 4 * K w := by positivity
        linarith)
  letI := isProbabilityMeasure_expMeasure ν hGint hZ
  refine ⟨inferInstance, integrable_expMeasure ν hGm hZ hKint, ?_⟩
  rw [integral_expMeasure ν hGm _ hZ]
  exact posterior_ratio_K_le hKm hGm hK0 hn hβ hD hlow hup hLD hZ hKint hGint hEint

/-- Prior-a.e. positivity suffices. This is the ambient-prior version used by
the challenge's posterior; values outside W have no effect. -/
theorem posterior_first_moment_le_ae {K G : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hGm : Measurable G)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β c D : ℝ} (hn : 0 < n) (hβ : 0 < β) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hlow : ∀ᵐ w ∂ν, n * β * (K w / 2) - c ≤ G w)
    (hup : ∀ᵐ w ∂ν, G w ≤ n * β * (3 / 2 * K w) + c)
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    IsProbabilityMeasure (Measure.expMeasure ν G) ∧
      Integrable K (Measure.expMeasure ν G) ∧
      n * (∫ w, K w ∂Measure.expMeasure ν G) ≤ 4 / β * Real.log D + 8 / β * c := by
  let K' := fun w ↦ max 0 (K w)
  have heq : K' =ᵐ[ν] K := hK0.mono fun w hw ↦ max_eq_right hw
  have hi (a : ℝ) : (∫ w, Real.exp (-(a * K' w)) ∂ν) =
      ∫ w, Real.exp (-(a * K w)) ∂ν := integral_congr_ae (heq.mono fun w hw ↦ by dsimp only; rw [hw])
  have hLD' : ∫ w, Real.exp (-(n * β / 4 * K' w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K' w)) ∂ν := by
    rw [hi, hi]
    exact hLD
  have hK'm : Measurable K' := measurable_const.max hKm
  have hK'B : ∀ᵐ w ∂ν, K' w ≤ B := by
    filter_upwards [heq, hKB] with w hw h
    rwa [hw]
  have hlo' : ∀ᵐ w ∂ν, n * β * (K' w / 2) - c ≤ G w := by
    filter_upwards [heq, hlow] with w hw h
    rwa [hw]
  have hup' : ∀ᵐ w ∂ν, G w ≤ n * β * (3 / 2 * K' w) + c := by
    filter_upwards [heq, hup] with w hw h
    rwa [hw]
  obtain ⟨hp, hi, hb⟩ := posterior_first_moment_le (K := K') hν hK'm hGm
    (fun _ ↦ le_max_left _ _) hK'B hn hβ hc hD hlo' hup' hLD'
  have hep : K' =ᵐ[Measure.expMeasure ν G] K := ae_expMeasure_of_ae heq
  exact ⟨hp, hi.congr hep, (integral_congr_ae hep) ▸ hb⟩

end SingularLearningTheory.BayesGibbs
