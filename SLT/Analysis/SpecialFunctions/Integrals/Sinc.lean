/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# The Dirichlet integral `∫₀^∞ sin x / x dx = π/2`

The improper Dirichlet integral is the analytic input for the principal-value reading of the
inverse Mellin transform ([Wat09, Theorem 4.5, §4.3] remark (1) on (4.11): the line integral as
the symmetric limit `∫_{−M}^{M}`) and for the book's truncated-power example, whose inverse line
integral is not absolutely convergent.

The route is the classical Fubini argument with the auxiliary exponential: for `x > 0`,
`sin x / x = ∫₀^∞ e^{−xt} sin x dt`, and
`∫₀^R e^{−xt} sin x dx = (1 − e^{−Rt}(t sin R + cos R))/(1 + t²)` has the explicit primitive
`−e^{−xt}(t sin x + cos x)/(1 + t²)`. Hence
`∫₀^R sinc = π/2 − ∫₀^∞ e^{−Rt}(t sin R + cos R)/(1 + t²) dt`, and the remainder is at most
`2/R`.
The main statements are `Real.tendsto_integral_sinc` (the limit `π/2`), `abs_integral_sinc_sub_le`
(the explicit rate `2/R`) and `Real.abs_integral_sinc_le` (the uniform bound `π/2 + 2` on every
partial
integral, the input for dominated-convergence arguments with the Dirichlet kernel).
-/

public section

open MeasureTheory Set Filter Topology Real

namespace Real

/-- The primitive in `x` of `e^{−xt} sin x`. -/
private noncomputable def dirichletPrim (t x : ℝ) : ℝ :=
  -(Real.exp (-x * t) * (t * Real.sin x + Real.cos x)) / (1 + t ^ 2)

private theorem hasDerivAt_dirichletPrim (t x : ℝ) :
    HasDerivAt (dirichletPrim t) (Real.exp (-x * t) * Real.sin x) x := by
  have h1 : HasDerivAt (fun x : ℝ ↦ Real.exp (-x * t)) (Real.exp (-x * t) * (-1 * t)) x := by
    have := ((hasDerivAt_id x).neg.mul_const t).exp
    simpa using this
  have h2 : HasDerivAt (fun x : ℝ ↦ t * Real.sin x + Real.cos x)
      (t * Real.cos x + -Real.sin x) x :=
    ((Real.hasDerivAt_sin x).const_mul t).add (Real.hasDerivAt_cos x)
  have h : HasDerivAt
      (fun x : ℝ ↦ -(Real.exp (-x * t) * (t * Real.sin x + Real.cos x)) / (1 + t ^ 2))
      (-(Real.exp (-x * t) * (-1 * t) * (t * Real.sin x + Real.cos x)
        + Real.exp (-x * t) * (t * Real.cos x + -Real.sin x)) / (1 + t ^ 2)) x :=
    ((h1.mul h2).neg).div_const (1 + t ^ 2)
  have hpos : (1 + t ^ 2) ≠ 0 := by positivity
  unfold dirichletPrim
  refine h.congr_deriv ?_
  rw [div_eq_iff hpos]
  ring

private theorem integral_exp_neg_mul_sin (t R : ℝ) :
    ∫ x in (0 : ℝ)..R, Real.exp (-x * t) * Real.sin x
      = (1 - Real.exp (-R * t) * (t * Real.sin R + Real.cos R)) / (1 + t ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ ↦ hasDerivAt_dirichletPrim t x)
    ((by fun_prop : Continuous fun x : ℝ ↦ Real.exp (-x * t) * Real.sin x).intervalIntegrable
      _ _)]
  simp only [dirichletPrim]
  have hpos : (1 + t ^ 2) ≠ 0 := by positivity
  simp only [neg_zero, zero_mul, Real.exp_zero, Real.sin_zero, Real.cos_zero, mul_zero, zero_add,
    one_mul]
  field_simp
  ring

/-- `∫₀^∞ e^{−xt} dt = 1/x` for `x > 0`. -/
private theorem integral_exp_neg_mul_Ioi_zero {x : ℝ} (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) = 1 / x := by
  rw [integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

private theorem integrableOn_exp_neg_mul_Ioi_zero {x : ℝ} (hx : 0 < x) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-x * t)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (by linarith) 0

/-- `sin x / x = ∫₀^∞ e^{−xt} sin x dt` for `x > 0`. -/
private theorem sinc_eq_integral_exp {x : ℝ} (hx : 0 < x) :
    sinc x = ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * Real.sin x := by
  rw [integral_mul_const, integral_exp_neg_mul_Ioi_zero hx, sinc_of_ne_zero hx.ne']
  ring

/-- Joint integrability of `e^{−xt} sin x` on `(0, R] × (0, ∞)`. -/
private theorem integrable_exp_neg_mul_sin_prod {R : ℝ} :
    Integrable (fun p : ℝ × ℝ ↦ Real.exp (-p.1 * p.2) * Real.sin p.1)
      ((volume.restrict (Ioc (0 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ ↦ Real.exp (-p.1 * p.2) * Real.sin p.1)
      ((volume.restrict (Ioc (0 : ℝ) R)).prod (volume.restrict (Ioi (0 : ℝ)))) :=
    (by fun_prop : Continuous fun p : ℝ × ℝ ↦ Real.exp (-p.1 * p.2) * Real.sin p.1)
      |>.aestronglyMeasurable
  refine (integrable_prod_iff hmeas).mpr ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact (integrableOn_exp_neg_mul_Ioi_zero hx.1).mul_const _
  · refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas.norm.integral_prod_right' ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have hcalc : ∫ t in Ioi (0 : ℝ), ‖Real.exp (-x * t) * Real.sin x‖ = |sinc x| := by
      simp_rw [norm_mul, Real.norm_eq_abs, Real.abs_exp]
      rw [integral_mul_const, integral_exp_neg_mul_Ioi_zero hx.1, sinc_of_ne_zero hx.1.ne',
        abs_div, abs_of_pos hx.1]
      ring
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), hcalc]
    exact abs_sinc_le_one x

/-- The Fubini identity: `∫₀^R sinc = ∫₀^∞ (1 − e^{−Rt}(t sin R + cos R))/(1 + t²) dt`. -/
private theorem integral_sinc_eq_integral_Ioi {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in (0 : ℝ)..R, sinc x
      = ∫ t in Ioi (0 : ℝ),
          (1 - Real.exp (-R * t) * (t * Real.sin R + Real.cos R)) / (1 + t ^ 2) := by
  rw [intervalIntegral.integral_of_le hR]
  have h1 : ∫ x in Ioc (0 : ℝ) R, sinc x
      = ∫ x in Ioc (0 : ℝ) R, ∫ t in Ioi (0 : ℝ), Real.exp (-x * t) * Real.sin x :=
    setIntegral_congr_fun measurableSet_Ioc fun x hx ↦ sinc_eq_integral_exp hx.1
  rw [h1, integral_integral_swap (f := fun x t ↦ Real.exp (-x * t) * Real.sin x)
    integrable_exp_neg_mul_sin_prod]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  rw [← intervalIntegral.integral_of_le hR, integral_exp_neg_mul_sin]

/-- The remainder integrand is dominated by `2 e^{−Rt}`. -/
private theorem abs_dirichlet_remainder_le (R t : ℝ) (ht : 0 ≤ t) :
    |Real.exp (-R * t) * (t * Real.sin R + Real.cos R) / (1 + t ^ 2)| ≤ 2 * Real.exp (-R * t) := by
  rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 1 + t ^ 2), abs_mul, Real.abs_exp,
    div_le_iff₀ (by positivity)]
  have h1 : |t * Real.sin R + Real.cos R| ≤ t + 1 := by
    calc |t * Real.sin R + Real.cos R| ≤ |t * Real.sin R| + |Real.cos R| := abs_add_le _ _
      _ ≤ t * 1 + 1 := by
        rw [abs_mul, abs_of_nonneg ht]
        exact add_le_add (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one R) ht)
          (Real.abs_cos_le_one R)
      _ = t + 1 := by ring
  have h2 : t + 1 ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_nonneg (t - 1/4)]
  calc Real.exp (-R * t) * |t * Real.sin R + Real.cos R|
      ≤ Real.exp (-R * t) * (2 * (1 + t ^ 2)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (Real.exp_pos _).le
    _ = 2 * Real.exp (-R * t) * (1 + t ^ 2) := by ring

private theorem integrableOn_dirichlet_remainder {R : ℝ} (hR : 0 < R) :
    IntegrableOn (fun t : ℝ ↦ Real.exp (-R * t) * (t * Real.sin R + Real.cos R) / (1 + t ^ 2))
      (Ioi 0) := by
  refine Integrable.mono' ((integrableOn_exp_neg_mul_Ioi_zero hR).const_mul 2)
    (((by fun_prop : Continuous fun t : ℝ ↦
      Real.exp (-R * t) * (t * Real.sin R + Real.cos R)).div (by fun_prop)
      fun t ↦ by positivity).aestronglyMeasurable) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [Real.norm_eq_abs]
  exact abs_dirichlet_remainder_le R t (le_of_lt ht)

/-- `∫₀^R sinc = π/2 − ∫₀^∞ e^{−Rt}(t sin R + cos R)/(1 + t²) dt` for `R > 0`. -/
private theorem integral_sinc_eq_sub {R : ℝ} (hR : 0 < R) :
    ∫ x in (0 : ℝ)..R, sinc x
      = π / 2 - ∫ t in Ioi (0 : ℝ),
          Real.exp (-R * t) * (t * Real.sin R + Real.cos R) / (1 + t ^ 2) := by
  rw [integral_sinc_eq_integral_Ioi hR.le]
  have hsplit : ∀ t : ℝ, (1 - Real.exp (-R * t) * (t * Real.sin R + Real.cos R)) / (1 + t ^ 2)
      = (1 + t ^ 2)⁻¹ - Real.exp (-R * t) * (t * Real.sin R + Real.cos R) / (1 + t ^ 2) := by
    intro t
    have : (1 + t ^ 2) ≠ 0 := by positivity
    field_simp
  simp_rw [hsplit]
  rw [integral_sub integrable_inv_one_add_sq.integrableOn (integrableOn_dirichlet_remainder hR),
    integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]

/-- The explicit rate: `|∫₀^R sinc − π/2| ≤ 2/R` for `R > 0`. -/
private theorem abs_integral_sinc_sub_le {R : ℝ} (hR : 0 < R) :
    |(∫ x in (0 : ℝ)..R, sinc x) - π / 2| ≤ 2 / R := by
  rw [integral_sinc_eq_sub hR, sub_sub_cancel_left, abs_neg]
  have hb := norm_integral_le_of_norm_le ((integrableOn_exp_neg_mul_Ioi_zero hR).const_mul 2)
    (f := fun t : ℝ ↦ Real.exp (-R * t) * (t * Real.sin R + Real.cos R) / (1 + t ^ 2))
    (μ := volume.restrict (Ioi (0 : ℝ))) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [Real.norm_eq_abs]
      exact abs_dirichlet_remainder_le R t (le_of_lt ht))
  rw [Real.norm_eq_abs] at hb
  refine hb.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_exp_neg_mul_Ioi_zero hR]
  ring

/-- **The Dirichlet integral**: `∫₀^R sin x / x dx → π/2` as `R → ∞`. -/
theorem tendsto_integral_sinc :
    Tendsto (fun R : ℝ ↦ ∫ x in (0 : ℝ)..R, sinc x) atTop (𝓝 (π / 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨max 1 (4 / ε), fun R hR ↦ ?_⟩
  have hR1 : (1 : ℝ) ≤ R := (le_max_left _ _).trans hR
  have hR4 : 4 / ε ≤ R := (le_max_right _ _).trans hR
  have hRpos : 0 < R := by linarith
  rw [Real.dist_eq]
  refine (abs_integral_sinc_sub_le hRpos).trans_lt ?_
  rw [div_lt_iff₀ hRpos]
  have : 4 ≤ ε * R := by
    rwa [div_le_iff₀ hε, mul_comm] at hR4
  linarith

/-- The partial integrals are odd in `R`. -/
private theorem integral_sinc_neg (R : ℝ) :
    ∫ x in (0 : ℝ)..(-R), sinc x = -∫ x in (0 : ℝ)..R, sinc x := by
  have : ∫ x in (0 : ℝ)..R, sinc x = ∫ x in (0 : ℝ)..R, sinc (-x) := by
    simp_rw [sinc_neg]
  rw [this, intervalIntegral.integral_comp_neg, neg_zero, intervalIntegral.integral_symm]

/-- The uniform bound on the partial Dirichlet integrals: `|∫₀^R sinc| ≤ π/2 + 2` for every `R`. -/
theorem abs_integral_sinc_le (R : ℝ) : |∫ x in (0 : ℝ)..R, sinc x| ≤ π / 2 + 2 := by
  have key : ∀ R : ℝ, 0 ≤ R → |∫ x in (0 : ℝ)..R, sinc x| ≤ π / 2 + 2 := by
    intro R hR
    rcases le_or_gt 1 R with h1 | h1
    · have hRpos : 0 < R := by linarith
      have := abs_integral_sinc_sub_le hRpos
      have h2 : 2 / R ≤ 2 := by
        rw [div_le_iff₀ hRpos]; linarith
      have hpi := Real.pi_pos
      rw [abs_le] at this ⊢
      constructor <;> linarith [this.1, this.2]
    · have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := R)
        (f := sinc) (C := 1) fun x _ ↦ by
          rw [Real.norm_eq_abs]; exact abs_sinc_le_one x
      rw [Real.norm_eq_abs, sub_zero, abs_of_nonneg hR, one_mul] at hb
      have hpi := Real.pi_pos
      linarith
  rcases le_or_gt 0 R with hR | hR
  · exact key R hR
  · have := key (-R) (by linarith)
    rwa [integral_sinc_neg, abs_neg] at this

end Real
