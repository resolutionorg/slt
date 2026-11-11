/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# [Wat09, Theorem 6.6] — holomorphy of `z ↦ ∫ K^z dν`

Equation (6.15) introduces `ζ(z) = ∫ K(w)^z φ(w) dw` as a holomorphic function on `Re z > 0`, and
the proof of Theorem 6.6 splits `ζ = ζ₁ + ζ₂` with `ζ₂(z) = ∫_{K ≥ ε} K^z φ` holomorphic on the
entire complex plane, because on the compact set `{K ≥ ε}` the derivative `K^z log K` is bounded.
This file proves both holomorphy statements for a finite measure `ν` and a measurable `K`:

* `hasDerivAt_integral_cpow`: the differentiation-under-the-integral core, with the integrand
  `K^z` and derivative `log K · K^z` (`hasDerivAt_ofReal_cpow_const`, including `K = 0`) under an
  abstract uniform bound on a disc;
* `differentiable_integral_cpow_of_le_of_le`: **`ζ₂` is entire** — if `ε ≤ K ≤ M` a.e. (`ε > 0`),
  then `z ↦ ∫ K^z dν` is complex-differentiable everywhere;
* `differentiableAt_integral_cpow_of_nonneg`: **`ζ` is holomorphic on `Re z > 0`** — if
  `0 ≤ K ≤ M` a.e., then `z ↦ ∫ K^z dν` is complex-differentiable at every `z₀` with `Re z₀ > 0`
  (the small-`K` part of the derivative is controlled by `t^a |log t| ≤ 2/a` on `(0, 1]`).
-/

public section

open MeasureTheory Complex Filter Set Topology

namespace SingularLearningTheory.MellinAnalysis

/-- The `z`-derivative of `z ↦ t^z` for real `t ≥ 0`, at any `z` with `t ≠ 0` or `z ≠ 0`:
`log t · t^z` (with `log 0 = 0`, `0^z = 0` for `z ≠ 0`). -/
private theorem hasDerivAt_ofReal_cpow_const {t : ℝ} (ht : 0 ≤ t) {z : ℂ} (h : t ≠ 0 ∨ z ≠ 0) :
    HasDerivAt (fun z : ℂ ↦ (t : ℂ) ^ z) (Complex.log (t : ℂ) * (t : ℂ) ^ z) z := by
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    have hz : z ≠ 0 := h.resolve_left (fun h' ↦ h' rfl)
    simp only [Complex.ofReal_zero, Complex.log_zero, zero_mul]
    have : (fun z : ℂ ↦ (0 : ℂ) ^ z) =ᶠ[𝓝 z] fun _ ↦ (0 : ℂ) := by
      filter_upwards [isOpen_ne.mem_nhds hz] with y hy
      exact Complex.zero_cpow hy
    exact (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq this
  · have hc : (t : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    have := (hasStrictDerivAt_const_cpow (x := (t : ℂ)) (y := z) (Or.inl hc)).hasDerivAt
    simpa only [mul_comm] using this

variable {W : Type*} [MeasurableSpace W] {ν : Measure W}

/-- **Differentiation under the integral for `∫ K^z dν`**: with a uniform bound `B` on
`‖log K · K^z‖` over a disc around `z₀` (on which a.e. `K ≠ 0` or `z ≠ 0`), `z ↦ ∫ K^z dν` has
derivative `∫ log K · K^{z₀} dν` at `z₀`. -/
private theorem hasDerivAt_integral_cpow [IsFiniteMeasure ν] {K : W → ℝ} (hK : Measurable K)
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {z₀ : ℂ} {δ B B₀ : ℝ} (hδ : 0 < δ)
    (hne : ∀ᵐ w ∂ν, ∀ z ∈ Metric.ball z₀ δ, K w ≠ 0 ∨ z ≠ 0)
    (hB₀ : ∀ᵐ w ∂ν, ‖(K w : ℂ) ^ z₀‖ ≤ B₀)
    (hB : ∀ᵐ w ∂ν, ∀ z ∈ Metric.ball z₀ δ, ‖Complex.log (K w : ℂ) * (K w : ℂ) ^ z‖ ≤ B) :
    HasDerivAt (fun z : ℂ ↦ ∫ w, (K w : ℂ) ^ z ∂ν)
      (∫ w, Complex.log (K w : ℂ) * (K w : ℂ) ^ z₀ ∂ν) z₀ := by
  have hKc : Measurable fun w ↦ (K w : ℂ) := Complex.measurable_ofReal.comp hK
  have hmeas : ∀ z : ℂ, AEStronglyMeasurable (fun w ↦ (K w : ℂ) ^ z) ν := fun z ↦
    (hKc.pow_const z).aestronglyMeasurable
  have hmeas' : AEStronglyMeasurable (fun w ↦ Complex.log (K w : ℂ) * (K w : ℂ) ^ z₀) ν :=
    ((Complex.measurable_log.comp hKc).mul (hKc.pow_const z₀)).aestronglyMeasurable
  have hint : Integrable (fun w ↦ (K w : ℂ) ^ z₀) ν := (integrable_const B₀).mono' (hmeas z₀) hB₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun (z : ℂ) w ↦ (K w : ℂ) ^ z)
    (F' := fun (z : ℂ) w ↦ Complex.log (K w : ℂ) * (K w : ℂ) ^ z)
    (x₀ := z₀) (bound := fun _ ↦ B) (Metric.ball_mem_nhds z₀ hδ)
    (Filter.Eventually.of_forall hmeas) hint hmeas' hB (integrable_const B) ?_
  · exact key.2
  · filter_upwards [hK0, hne] with w hw hw' z hzb
    exact hasDerivAt_ofReal_cpow_const hw (hw' z hzb)

/-- `t^r ≤ exp(|log t| · |r|)` for `t > 0`. -/
private theorem rpow_le_exp_abs {t r : ℝ} (ht : 0 < t) : t ^ r ≤ Real.exp (|Real.log t| * |r|) := by
  rw [Real.rpow_def_of_pos ht]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans (abs_mul _ _).le)

/-- Real parts on the disc `ball z₀ δ` lie in `(Re z₀ − δ, Re z₀ + δ)`. -/
private theorem re_mem_of_mem_ball {z z₀ : ℂ} {δ : ℝ} (hz : z ∈ Metric.ball z₀ δ) :
    z₀.re - δ ≤ z.re ∧ z.re ≤ z₀.re + δ := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have := Complex.abs_re_le_norm (z - z₀)
  rw [sub_re] at this
  constructor <;> linarith [abs_le.mp this]

/-- **`ζ₂` is entire.** If `ε ≤ K ≤ M` a.e. with `ε > 0` (a finite measure `ν`), then
`z ↦ ∫ K^z dν` is complex-differentiable on all of `ℂ`. -/
theorem _root_.differentiable_integral_cpow_of_le_of_le [IsFiniteMeasure ν] {K : W → ℝ}
    (hK : Measurable K) {ε M : ℝ} (hε : 0 < ε) (hKε : ∀ᵐ w ∂ν, ε ≤ K w)
    (hKM : ∀ᵐ w ∂ν, K w ≤ M) : Differentiable ℂ fun z : ℂ ↦ ∫ w, (K w : ℂ) ^ z ∂ν := by
  intro z₀
  set L : ℝ := max |Real.log ε| |Real.log M| with hL
  set R : ℝ := |z₀.re| + 1 with hR
  have hlog : ∀ {t : ℝ}, ε ≤ t → t ≤ M → |Real.log t| ≤ L := fun {t} h1 h2 ↦
    abs_le_max_abs_abs (Real.log_le_log hε h1) (Real.log_le_log (hε.trans_le h1) h2)
  have hL0 : 0 ≤ L := le_max_of_le_left (abs_nonneg _)
  have hpow : ∀ {t : ℝ}, ε ≤ t → t ≤ M → ∀ {r : ℝ}, |r| ≤ R → t ^ r ≤ Real.exp (L * R) := by
    intro t h1 h2 r hr
    have ht : 0 < t := hε.trans_le h1
    exact (rpow_le_exp_abs ht).trans (Real.exp_le_exp.mpr
      (mul_le_mul (hlog h1 h2) hr (abs_nonneg _) hL0))
  have hB₀ : ∀ᵐ w ∂ν, ‖(K w : ℂ) ^ z₀‖ ≤ Real.exp (L * R) := by
    filter_upwards [hKε, hKM] with w h1 h2
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hε.trans_le h1)]
    exact hpow h1 h2 (by rw [hR]; linarith)
  have hB : ∀ᵐ w ∂ν, ∀ z ∈ Metric.ball z₀ 1,
      ‖Complex.log (K w : ℂ) * (K w : ℂ) ^ z‖ ≤ L * Real.exp (L * R) := by
    filter_upwards [hKε, hKM] with w h1 h2 z hz
    have ht : 0 < K w := hε.trans_le h1
    have hre : |z.re| ≤ R := by
      obtain ⟨hlo, hhi⟩ := re_mem_of_mem_ball hz
      rw [hR, abs_le]; constructor <;> linarith [abs_le.mp (le_refl |z₀.re|), le_abs_self z₀.re,
        neg_abs_le z₀.re]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, ← Complex.ofReal_log ht.le,
      Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul (hlog h1 h2) (hpow h1 h2 hre) (by positivity) hL0
  have hne : ∀ᵐ w ∂ν, ∀ z ∈ Metric.ball z₀ 1, K w ≠ 0 ∨ z ≠ 0 :=
    hKε.mono fun w h z _ ↦ Or.inl (hε.trans_le h).ne'
  exact (hasDerivAt_integral_cpow hK (hKε.mono fun w h ↦ hε.le.trans h) one_pos hne hB₀
    hB).differentiableAt

/-- The small-`t` and large-`t` bound on the derivative integrand: for `0 ≤ t ≤ M` and
`a ≤ r ≤ b` with `a > 0`, `|log t| t^r ≤ 2/a + M'^b log M'` where `M' = max M 1`. -/
private theorem abs_log_mul_rpow_le {t M a b r : ℝ} (ht : 0 ≤ t) (htM : t ≤ M) (ha : 0 < a)
    (hr₁ : a ≤ r) (hr₂ : r ≤ b) :
    |Real.log t| * t ^ r ≤ 2 / a + (max M 1) ^ b * Real.log (max M 1) := by
  set M' := max M 1 with hM'
  have hM'1 : (1 : ℝ) ≤ M' := le_max_right _ _
  have hb : 0 ≤ b := by linarith
  have hlogM' : 0 ≤ Real.log M' := Real.log_nonneg hM'1
  have hterm2 : 0 ≤ M' ^ b * Real.log M' := mul_nonneg (by positivity) hlogM'
  have hterm1 : 0 ≤ 2 / a := by positivity
  rcases eq_or_lt_of_le ht with h0 | hpos
  · rw [← h0, Real.log_zero, abs_zero, zero_mul]; linarith
  rcases le_or_gt t 1 with ht1 | ht1
  · -- `0 < t ≤ 1`: `|log t| ≤ t^{−a/2}/(a/2)`, `t^r ≤ t^a`
    have h1 : |Real.log t| ≤ t ^ (-(a / 2)) / (a / 2) := by
      rw [abs_of_nonpos (Real.log_nonpos hpos.le ht1)]
      have hlog := Real.neg_rpow_div_le_log hpos.le (half_pos ha)
      rw [neg_div] at hlog
      linarith
    have h2 : t ^ r ≤ t ^ a := Real.rpow_le_rpow_of_exponent_ge hpos ht1 hr₁
    have h3 : t ^ (-(a / 2)) * t ^ a = t ^ (a / 2) := by
      rw [← Real.rpow_add hpos]; ring_nf
    have h4 : t ^ (a / 2) ≤ 1 := Real.rpow_le_one hpos.le ht1 (by positivity)
    calc |Real.log t| * t ^ r ≤ (t ^ (-(a / 2)) / (a / 2)) * t ^ a :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = 2 / a * t ^ (a / 2) := by rw [div_mul_eq_mul_div, h3]; field_simp
      _ ≤ 2 / a := by nlinarith
      _ ≤ 2 / a + M' ^ b * Real.log M' := by linarith
  · -- `1 < t ≤ M'`: `|log t| ≤ log M'`, `t^r ≤ M'^b`
    have htM' : t ≤ M' := htM.trans (le_max_left _ _)
    have h1 : |Real.log t| ≤ Real.log M' := by
      rw [abs_of_nonneg (Real.log_nonneg ht1.le)]
      exact Real.log_le_log hpos htM'
    have h2 : t ^ r ≤ M' ^ b :=
      (Real.rpow_le_rpow hpos.le htM' (by linarith)).trans
        (Real.rpow_le_rpow_of_exponent_le hM'1 hr₂)
    calc |Real.log t| * t ^ r ≤ Real.log M' * M' ^ b :=
          mul_le_mul h1 h2 (by positivity) hlogM'
      _ ≤ 2 / a + M' ^ b * Real.log M' := by linarith [mul_comm (Real.log M') (M' ^ b)]

/-- **`ζ` is holomorphic on `Re z > 0`.** If `0 ≤ K ≤ M` a.e. (a finite measure `ν`), then
`z ↦ ∫ K^z dν` is complex-differentiable at every `z₀` with `Re z₀ > 0` (eq. (6.15)). -/
theorem _root_.differentiableAt_integral_cpow_of_nonneg [IsFiniteMeasure ν] {K : W → ℝ}
    (hK : Measurable K) {M : ℝ} (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) (hKM : ∀ᵐ w ∂ν, K w ≤ M) {z₀ : ℂ}
    (hz₀ : 0 < z₀.re) : DifferentiableAt ℂ (fun z : ℂ ↦ ∫ w, (K w : ℂ) ^ z ∂ν) z₀ := by
  set a : ℝ := z₀.re / 2 with ha
  have ha0 : 0 < a := by positivity
  set M' : ℝ := max M 1 with hM'
  have hM'1 : (1 : ℝ) ≤ M' := le_max_right _ _
  have hre : ∀ z ∈ Metric.ball z₀ a, a ≤ z.re ∧ z.re ≤ 3 * z₀.re / 2 := fun z hz ↦ by
    obtain ⟨h1, h2⟩ := re_mem_of_mem_ball hz
    constructor <;> linarith
  have hne : ∀ᵐ w ∂ν, ∀ z ∈ Metric.ball z₀ a, K w ≠ 0 ∨ z ≠ 0 :=
    Filter.Eventually.of_forall fun w z hz ↦ Or.inr fun h0 ↦ by
      have := (hre z hz).1
      rw [h0, zero_re] at this
      linarith
  have hB₀ : ∀ᵐ w ∂ν, ‖(K w : ℂ) ^ z₀‖ ≤ 1 + M' ^ z₀.re := by
    filter_upwards [hK0, hKM] with w h0 hM
    rw [Complex.norm_cpow_eq_rpow_re_of_nonneg h0 hz₀.ne']
    rcases le_or_gt (K w) 1 with h1 | h1
    · have := Real.rpow_le_one h0 h1 hz₀.le
      have : 0 ≤ M' ^ z₀.re := by positivity
      linarith
    · have := Real.rpow_le_rpow h0 (hM.trans (le_max_left M 1)) hz₀.le
      linarith
  have hB : ∀ᵐ w ∂ν, ∀ z ∈ Metric.ball z₀ a, ‖Complex.log (K w : ℂ) * (K w : ℂ) ^ z‖
      ≤ 2 / a + M' ^ (3 * z₀.re / 2) * Real.log M' := by
    filter_upwards [hK0, hKM] with w h0 hM z hz
    rcases eq_or_lt_of_le h0 with hK0' | hpos
    · rw [← hK0', Complex.ofReal_zero, Complex.log_zero, zero_mul, norm_zero]
      have : 0 ≤ M' ^ (3 * z₀.re / 2) * Real.log M' :=
        mul_nonneg (by positivity) (Real.log_nonneg hM'1)
      positivity
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hpos, ← Complex.ofReal_log hpos.le,
        Complex.norm_real, Real.norm_eq_abs]
      exact abs_log_mul_rpow_le h0 hM ha0 (hre z hz).1 (hre z hz).2
  exact (hasDerivAt_integral_cpow hK hK0 ha0 hne hB₀ hB).differentiableAt

end SingularLearningTheory.MellinAnalysis
