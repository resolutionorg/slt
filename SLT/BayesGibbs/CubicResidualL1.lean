/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.CubicRemainder
public import SLT.BayesGibbs.FiniteQuartet.PolynomialBounds
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import SLT.BayesGibbs.GeneralizedTaylor
import SLT.Analysis.SpecialFunctions.Pow.LogBounds
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# The cubic residual of the predictive expansion in $L^1$

The Bayes loss at a point, $-\log E_w[e^{-f(x, w)}]$, is the posterior mean of $f(x, w)$ minus
half its posterior variance, up to a cubic remainder. This module scales that remainder by $n$
and bounds it by a coefficient of order $1/\sqrt{n}$ times the sixth-moment dominator
$1 + L^6 + A^6$, both after integrating over fresh data and after summing over the training
sample. A residual dominated in this way tends to zero in $L^1$ and in probability. This is how
$nB_g$ and $nB_t$ are replaced by $nG_g - V/2$ and $nG_t - V/2$ in the posterior observables of
[Wat09, Theorem 6.8].

## Main results

* `SingularLearningTheory.BayesGibbs.scaled_cubic_remainder_le_sixth`: a cubic Taylor bound at step
  $h$ with $nh^2 = 1$, scaled by $n$, is at most a coefficient of order $h$ times
  $1 + L^6 + A^6$.
* `SingularLearningTheory.BayesGibbs.fresh_quadratic_residual_le`: integrating the residual bound over
  fresh data bounds the scaled residual of the integrals.
* `SingularLearningTheory.BayesGibbs.training_quadratic_residual_le`: summing the residual bound over
  the sample bounds the residual of the sums, with the empirical sixth moment of $A$.
* `SingularLearningTheory.BayesGibbs.residual_L1_of_eventual_domination`: a residual eventually
  dominated by a vanishing coefficient times a dominator of bounded expectation tends to zero in
  $L^1$ and in probability.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

/-- The mixed cubic term costs sixth moments, even when its two envelopes
are dependent. -/
private theorem mixed_cubic_le_sixth {A L : ℝ} (hA : 0 ≤ A) (hL : 0 ≤ L) :
    A ^ 3 * (1 + L) ^ 3 ≤ 32 * (1 + L ^ 6 + A ^ 6) := by
  have h6 := add_pow_le_two_pow_mul_add_pow zero_le_one hL 6
  norm_num only [one_pow, Nat.reducePow] at h6
  have hY := two_mul_le_add_sq (A ^ 3) ((1 + L) ^ 3)
  rw [← pow_mul, ← pow_mul] at hY
  norm_num only [Nat.reduceMul] at hY
  nlinarith [pow_nonneg hA 6]

/-- Scale the cubic Taylor bound by n, then absorb both mixed terms
into a sixth-moment dominator. For h=1/sqrt(n), the displayed coefficient
converges to zero. -/
theorem scaled_cubic_remainder_le_sixth {r n h A L β C : ℝ}
    (hn : 0 ≤ n) (hh : 0 ≤ h) (hnh : n * h ^ 2 = 1)
    (hA : 0 ≤ A) (hL : 0 ≤ L) (hβ : 0 < β) (hC : 0 ≤ C)
    (hr : |r| ≤ C * h ^ 3 * A ^ 3 * (1 + L + h * A / β) ^ 3) :
    n * |r| ≤ (128 * C * h + 4 * C * h ^ 4 / β ^ 3) * (1 + L ^ 6 + A ^ 6) := by
  have hsplit := shifted_cubic_remainder_le hC hh hA hL hβ
  have hscaled := mul_le_mul_of_nonneg_left (hr.trans hsplit) hn
  have h3 : n * h ^ 3 = h := by nlinarith [congrArg (fun z ↦ z * h) hnh]
  have h6 : n * h ^ 6 = h ^ 4 := by
    have h := congrArg (fun z ↦ z * h ^ 4) hnh
    nlinarith
  have hsc : n * |r| ≤ 4 * C * h * (A ^ 3 * (1 + L) ^ 3) +
      4 * C * h ^ 4 / β ^ 3 * A ^ 6 := by
    calc _ ≤ n * (4 * C * h ^ 3 * A ^ 3 * (1 + L) ^ 3 + 4 * C * h ^ 6 * A ^ 6 / β ^ 3) := hscaled
      _ = _ := by
        calc _ = 4 * C * (n * h ^ 3) * (A ^ 3 * (1 + L) ^ 3) +
            4 * C * (n * h ^ 6) / β ^ 3 * A ^ 6 := by ring
          _ = _ := by rw [h3, h6]
  have hmix := mul_le_mul_of_nonneg_left (mixed_cubic_le_sixth hA hL)
    (show 0 ≤ 4 * C * h by positivity)
  have hlast : 4 * C * h ^ 4 / β ^ 3 * A ^ 6 ≤
      4 * C * h ^ 4 / β ^ 3 * (1 + L ^ 6 + A ^ 6) :=
    mul_le_mul_of_nonneg_left (by nlinarith [show 0 ≤ L ^ 6 by positivity]) (by positivity)
  nlinarith

/-- Integrate a quadratic residual over fresh data, keeping its complete
variance term. The hypotheses come directly from the fixed-sample posterior
Taylor estimate and its polynomial integrability bounds. -/
theorem fresh_quadratic_residual_le {X : Type*} [MeasurableSpace X] {q : Measure X}
    [IsProbabilityMeasure q] {b g v A : X → ℝ} {n c L : ℝ}
    (hn : 0 < n) (hc : 0 ≤ c) (hL : 0 ≤ L)
    (hb : AEStronglyMeasurable b q) (hg : Integrable g q) (hv : Integrable v q)
    (hA6 : Integrable (fun x ↦ A x ^ 6) q)
    (hr : ∀ᵐ x ∂q, n * |b x - g x + v x / 2| ≤ c * (1 + L ^ 6 + A x ^ 6)) :
    Integrable b q ∧ n * |(∫ x, b x ∂q) - (∫ x, g x ∂q) + (∫ x, v x ∂q) / 2| ≤
      c * (1 + L ^ 6 + ∫ x, A x ^ 6 ∂q) := by
  have hdom : Integrable (fun x ↦ c * (1 + L ^ 6 + A x ^ 6)) q :=
    ((integrable_const _).add hA6).const_mul c
  have hm : Integrable (fun x ↦ n * (g x - v x / 2)) q :=
    (hg.sub (hv.div_const 2)).const_mul n
  obtain ⟨hbi, hbnd⟩ := abs_integral_predictive_sub_mean_le (hb.const_mul n) hm hdom (by
    filter_upwards [hr] with x hx
    rw [show n * b x - n * (g x - v x / 2) = n * (b x - g x + v x / 2) by ring,
      abs_mul, abs_of_pos hn]
    exact hx)
  refine ⟨(hbi.const_mul n⁻¹).congr (.of_forall fun x ↦ by field_simp), ?_⟩
  rw [integral_const_mul, integral_const_mul,
    integral_sub hg (hv.div_const 2), integral_div,
    show n * (∫ x, b x ∂q) - n * ((∫ x, g x ∂q) - (∫ x, v x ∂q) / 2) =
      n * ((∫ x, b x ∂q) - (∫ x, g x ∂q) + (∫ x, v x ∂q) / 2) by ring,
    abs_mul, abs_of_pos hn, integral_const_mul,
    integral_add (integrable_const _) hA6] at hbnd
  simpa using hbnd

/-- A training quadratic residual has the same sixth-moment dominator,
with the empirical sixth moment. -/
theorem training_quadratic_residual_le {n : ℕ} (hn : 0 < n)
    {b g v A : ℕ → ℝ} {c L : ℝ}
    (hr : ∀ i < n, (n : ℝ) * |b i - g i + v i / 2| ≤ c * (1 + L ^ 6 + A i ^ 6)) :
    |(∑ i ∈ Finset.range n, b i) - (∑ i ∈ Finset.range n, g i) +
      (∑ i ∈ Finset.range n, v i) / 2| ≤
        c * (1 + L ^ 6 + (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A i ^ 6) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hsum : |∑ i ∈ Finset.range n, (b i - g i + v i / 2)| ≤
      ∑ i ∈ Finset.range n, c * (1 + L ^ 6 + A i ^ 6) / n :=
    (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i hi ↦
      (le_div_iff₀ hn').mpr (by simpa only [mul_comm (n : ℝ)] using hr i (Finset.mem_range.mp hi)))
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_div] using
    hsum.trans (le_of_eq (by
      rw [← Finset.sum_div, ← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp))

/-- L1 convergence with eventual integrability implies convergence in measure,
without any integrability requirement on a finite prefix. -/
private theorem tendstoInMeasure_zero_of_integral_abs_tendsto {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y : ℕ → Ω → ℝ}
    (hi : ∀ᶠ n in atTop, Integrable (Y n) P)
    (ht : Tendsto (fun n ↦ ∫ ω, |Y n ω| ∂P) atTop (𝓝 0)) :
    TendstoInMeasure P Y atTop 0 := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
  have heq : (fun n ↦ eLpNorm (Y n - 0) 1 P) =ᶠ[atTop]
      (fun n ↦ ENNReal.ofReal (∫ ω, |Y n ω| ∂P)) := by
    filter_upwards [hi] with n hn
    simp only [sub_zero]
    rw [eLpNorm_one_eq_lintegral_enorm hn.aestronglyMeasurable]
    simp_rw [Real.enorm_eq_ofReal_abs]
    exact (ofReal_integral_eq_lintegral_ofReal hn.abs (.of_forall fun ω ↦ abs_nonneg _)).symm
  have hlim : Tendsto (fun n ↦ ENNReal.ofReal (∫ ω, |Y n ω| ∂P)) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal ht
  exact hlim.congr' heq.symm

/-- A vanishing deterministic coefficient times any uniformly L1 bounded
nonnegative dominator gives the residual's L1 and probability limits. -/
theorem residual_L1_of_eventual_domination {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Y G : ℕ → Ω → ℝ} {c : ℕ → ℝ} {C : ℝ}
    (hYm : ∀ n, AEStronglyMeasurable (Y n) P)
    (hGi : ∀ᶠ n in atTop, Integrable (G n) P)
    (hGC : ∀ᶠ n in atTop, ∫ ω, G n ω ∂P ≤ C)
    (hc : ∀ᶠ n in atTop, 0 ≤ c n) (hct : Tendsto c atTop (𝓝 0))
    (hdom : ∀ᶠ n in atTop, ∀ᵐ ω ∂P, |Y n ω| ≤ c n * G n ω) :
    (∀ᶠ n in atTop, Integrable (Y n) P) ∧
      Tendsto (fun n ↦ ∫ ω, |Y n ω| ∂P) atTop (𝓝 0) ∧ TendstoInMeasure P Y atTop 0 := by
  have hi : ∀ᶠ n in atTop, Integrable (Y n) P := by
    filter_upwards [hGi, hdom] with n hgin hdn
    exact (hgin.const_mul _).mono' (hYm n)
      (hdn.mono fun ω hω ↦ by simpa only [Real.norm_eq_abs] using hω)
  have hb : ∀ᶠ n in atTop, ∫ ω, |Y n ω| ∂P ≤ c n * C := by
    filter_upwards [hi, hGi, hGC, hc, hdom] with n hin hgin hgn hcn hdn
    calc _ ≤ ∫ ω, c n * G n ω ∂P := integral_mono_ae hin.abs (hgin.const_mul _) hdn
      _ = c n * ∫ ω, G n ω ∂P := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hgn hcn
  have ht : Tendsto (fun n ↦ ∫ ω, |Y n ω| ∂P) atTop (𝓝 0) :=
    squeeze_zero' (.of_forall fun n ↦ integral_nonneg fun ω ↦ abs_nonneg _) hb
      (by simpa only [zero_mul] using hct.mul_const C)
  exact ⟨hi, ht, tendstoInMeasure_zero_of_integral_abs_tendsto hi ht⟩

end SingularLearningTheory.BayesGibbs
