/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.ExponentialMoment
public import SLT.Probability.Moments.OfExponential
public import SLT.BayesGibbs.LaplaceDoubling.Basic

/-!
# Polynomial moments of the posterior

Bounds on $E[K^r]$ under a tilted posterior $e^{-G}\nu/Z$ whose exponent is sandwiched between
$n\beta K/2 - c$ and $3n\beta K/2 + c$. The posterior moments of $K$ then decay like $n^{-r}$, which
controls the radial factor $\sqrt K$ in the bounds on the posterior observables.

## Main results

* `SingularLearningTheory.BayesGibbs.tilted_exponent_bounds`: if
  $\sqrt n\,|K_n - K| \le L\sqrt K$ and $|f| \le A\sqrt K$, then $n\beta K_n + \sigma f$ lies
  between $n\beta K/2$ and $3n\beta K/2$ up to $\frac\beta2 (L + A/(\beta\sqrt n))^2$, for every
  $\sigma \in [0, 1]$.
* `SingularLearningTheory.BayesGibbs.posterior_rpow_moment_le`: under such a sandwich and the Laplace
  doubling bound, the posterior is a probability measure, $K^r$ is integrable under it and
  $E[K^r] \le (4/(n\beta))^r\,\big((2(\log D + 2c))^r + C\big)$.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

/-- The relative envelope remains valid after a single-datum tilt, with
L replaced by L+A/(β√n). Only the interval 0≤σ≤1 is used; no exponential
moment of the data envelope A is needed. -/
theorem tilted_exponent_bounds {K Kn f n β L A σ : ℝ}
    (hK : 0 ≤ K) (hn : 0 < n) (hβ : 0 < β) (hσ : σ ∈ Icc 0 1)
    (he : Real.sqrt n * |Kn - K| ≤ L * Real.sqrt K)
    (hf : |f| ≤ A * Real.sqrt K) :
    n * β * (K / 2) - β / 2 * (L + A / (β * Real.sqrt n)) ^ 2 ≤ n * β * Kn + σ * f ∧
      n * β * Kn + σ * f ≤ n * β * (3 / 2 * K) +
        β / 2 * (L + A / (β * Real.sqrt n)) ^ 2 := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hs2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have ht2 : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK
  have hde : n * β * |Kn - K| ≤ β * Real.sqrt n * L * Real.sqrt K := by
    calc
      n * β * |Kn - K| = (β * Real.sqrt n) * (Real.sqrt n * |Kn - K|) := by
        calc
          _ = β * (Real.sqrt n) ^ 2 * |Kn - K| := by rw [hs2]; ring
          _ = _ := by ring
      _ ≤ (β * Real.sqrt n) * (L * Real.sqrt K) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hβ.le hs.le)
      _ = _ := by ring
  have hsf : |σ * f| ≤ A * Real.sqrt K := by
    rw [abs_mul, abs_of_nonneg hσ.1]
    exact (mul_le_mul_of_nonneg_right hσ.2 (abs_nonneg f)).trans (by simpa using hf)
  have hdev : |n * β * Kn + σ * f - n * β * K| ≤
      β * Real.sqrt n * L * Real.sqrt K + A * Real.sqrt K := by
    calc
      _ = |n * β * (Kn - K) + σ * f| := by congr 1; ring
      _ ≤ |n * β * (Kn - K)| + |σ * f| := abs_add_le _ _
      _ ≤ β * Real.sqrt n * L * Real.sqrt K + A * Real.sqrt K := by
        rw [abs_mul, abs_of_nonneg (mul_nonneg hn.le hβ.le)]
        exact add_le_add hde hsf
  have hcancel : β * Real.sqrt n * (L + A / (β * Real.sqrt n)) =
      β * Real.sqrt n * L + A := by
    field_simp
  have hyoung : β * Real.sqrt n * L * Real.sqrt K + A * Real.sqrt K ≤
      n * β * K / 2 + β / 2 * (L + A / (β * Real.sqrt n)) ^ 2 := by
    have hsq := mul_nonneg hβ.le
      (sq_nonneg (Real.sqrt n * Real.sqrt K - (L + A / (β * Real.sqrt n))))
    rw [sub_sq, mul_pow, hs2, ht2] at hsq
    have hcancel' := congrArg (fun z : ℝ ↦ z * Real.sqrt K) hcancel
    nlinarith [hsq, hcancel']
  have h := abs_le.mp (hdev.trans hyoung)
  constructor <;> linarith

section Moment

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- Polynomial posterior radial moments from Laplace doubling and an
exponent sandwich. All posterior integrability and evidence positivity are
proved here from finite nonzero prior mass and the bounded population loss.
On a compact parameter set apply this on its subtype, or replace K off that
set by max(0,K). -/
theorem posterior_rpow_moment_le {K G : W → ℝ}
    (hν : ν ≠ 0) (hKm : Measurable K) (hGm : Measurable G)
    (hK0 : ∀ w, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    {n β c D r C : ℝ} (hn : 0 < n) (hβ : 0 < β) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hscalar : ∀ y : ℝ, 0 ≤ y → y ^ r ≤ C * Real.exp (y / 2))
    (hlow : ∀ᵐ w ∂ν, n * β * (K w / 2) - c ≤ G w)
    (hup : ∀ᵐ w ∂ν, G w ≤ n * β * (3 / 2 * K w) + c)
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :
    IsProbabilityMeasure (Measure.expMeasure ν G) ∧
      Integrable (fun w ↦ (K w) ^ r) (Measure.expMeasure ν G) ∧
      (∫ w, (K w) ^ r ∂Measure.expMeasure ν G) ≤
        (4 / (n * β)) ^ r * ((2 * (Real.log D + 2 * c)) ^ r + C) := by
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
  have hpost := posterior_exponential_moment_le hKm hGm hK0 hn hβ hD
    hlow hup hLD hZ hKint hGint hEint
  have hYint : Integrable (fun w ↦ Real.exp (n * β / 4 * K w)) (Measure.expMeasure ν G) :=
    integrable_expMeasure ν hGm hZ hEint
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hBd : 0 ≤ Real.log D + 2 * c := add_nonneg (Real.log_nonneg hD) (by positivity)
  have hpost' : (∫ w, Real.exp (n * β / 4 * K w) ∂Measure.expMeasure ν G) ≤
      Real.exp (Real.log D + 2 * c) := by
    rw [Real.exp_add, Real.exp_log hDpos]
    exact hpost
  obtain ⟨hri, hbound⟩ := integral_rpow_le_of_exponential_moment
    (ρ := Measure.expMeasure ν G) (hKm.const_mul (n * β / 4)).aestronglyMeasurable
    (Eventually.of_forall fun w ↦ mul_nonneg (by positivity) (hK0 w))
    hr hBd hC hscalar hYint hpost'
  have heq : ∀ w, (K w) ^ r = (4 / (n * β)) ^ r * (n * β / 4 * K w) ^ r := by
    intro w
    rw [← Real.mul_rpow (by positivity : 0 ≤ 4 / (n * β))
      (mul_nonneg (by positivity) (hK0 w))]
    congr 1
    field_simp
  refine ⟨inferInstance, (hri.const_mul ((4 / (n * β)) ^ r)).congr
    (Eventually.of_forall fun w ↦ (heq w).symm), ?_⟩
  calc
    (∫ w, (K w) ^ r ∂Measure.expMeasure ν G) =
        (4 / (n * β)) ^ r * ∫ w, (n * β / 4 * K w) ^ r ∂Measure.expMeasure ν G := by
      simp_rw [heq]
      rw [integral_const_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg (by positivity) r)

end Moment

end SingularLearningTheory.BayesGibbs
