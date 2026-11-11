/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.Analysis.SpecialFunctions.Integrals.Sinc
public import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# The Dirichlet kernel at a jump: `(1/π) ∫ g(v) sin(M(v−r))/(v−r) dv → ½(g(r+) + g(r−))`

The localization lemma behind the principal-value reading of the inverse Mellin transform
([Wat09, Theorem 4.5, §4.3] remark (1) on (4.11)). For an integrable `g : ℝ → ℝ` with one-sided
limits `g(r±)` approached at a Lipschitz rate on a right and a left neighbourhood of `r`, the
Dirichlet kernel `D_M(t) = M sinc(M t) = sin(M t)/t` satisfies
`∫ g(v) D_M(v − r) dv → (π/2) (g(r+) + g(r−))`. Away from `r` and for the divided differences
`(g(v) − g(r±))/(v − r)` near `r` the integrals vanish by the Riemann–Lebesgue lemma
(Mathlib's `Real.tendsto_integral_exp_smul_cocompact`, in the sine form with a phase
`tendsto_integral_mul_sin_add_atTop`); the constant terms give the Dirichlet integral
`∫₀^{Mδ} sinc → π/2` (`Real.tendsto_integral_sinc`).
-/

public section

open MeasureTheory Set Filter Topology Real
open scoped FourierTransform

namespace Real

section RiemannLebesgue

/-- **Riemann–Lebesgue in complex form**: `∫ k(v) e^{iMv} dv → 0` as `M → ∞` (for a non-integrable
`k` the integral is `0` by convention, so no hypothesis is needed). -/
private theorem tendsto_integral_mul_exp_atTop (k : ℝ → ℝ) :
    Tendsto (fun M : ℝ ↦ ∫ v, (k v : ℂ) * Complex.exp (((M * v : ℝ) : ℂ) * Complex.I)) atTop
      (𝓝 0) := by
  have hRL := Real.tendsto_integral_exp_smul_cocompact (fun v ↦ (k v : ℂ))
  have h1 : Tendsto (fun M : ℝ ↦ M / (2 * π)) atTop atTop :=
    tendsto_id.atTop_div_const (by positivity)
  have hg : Tendsto (fun M : ℝ ↦ -(M / (2 * π))) atTop (cocompact ℝ) :=
    (tendsto_neg_atTop_atBot.comp h1).mono_right atBot_le_cocompact
  refine (hRL.comp hg).congr fun M ↦ ?_
  simp only [Function.comp]
  refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
  beta_reduce
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, mul_comm]
  congr 2
  have hπ : (π : ℝ) ≠ 0 := Real.pi_ne_zero
  have : (2 * π * -(v * -(M / (2 * π))) : ℝ) = M * v := by
    field_simp
  rw [this]

/-- **Riemann–Lebesgue, sine form with a phase**: for integrable `k : ℝ → ℝ` and any phase
`θ(M)`, `∫ k(v) sin(M v + θ(M)) dv → 0` as `M → ∞`. -/
private theorem tendsto_integral_mul_sin_add_atTop {k : ℝ → ℝ} (hk : Integrable k) (θ : ℝ → ℝ) :
    Tendsto (fun M : ℝ ↦ ∫ v, k v * Real.sin (M * v + θ M)) atTop (𝓝 0) := by
  have h := tendsto_integral_mul_exp_atTop k
  have hint : ∀ M : ℝ,
      Integrable (fun v ↦ (k v : ℂ) * Complex.exp (((M * v : ℝ) : ℂ) * Complex.I)) := by
    intro M
    refine hk.norm.mono' ?_ (Eventually.of_forall fun v ↦ ?_)
    · exact (Complex.continuous_ofReal.comp_aestronglyMeasurable hk.1).mul
        (Continuous.aestronglyMeasurable (by fun_prop))
    · rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
  have key : ∀ M, ∫ v, k v * Real.sin (M * v + θ M)
      = (Complex.exp (((θ M : ℝ) : ℂ) * Complex.I)
          * ∫ v, (k v : ℂ) * Complex.exp (((M * v : ℝ) : ℂ) * Complex.I)).im := by
    intro M
    rw [← integral_const_mul, ← RCLike.im_to_complex, ← integral_im ((hint M).const_mul _)]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    have e : Complex.exp (((θ M : ℝ) : ℂ) * Complex.I)
        * ((k v : ℂ) * Complex.exp (((M * v : ℝ) : ℂ) * Complex.I))
        = (k v : ℂ) * Complex.exp (((M * v + θ M : ℝ) : ℂ) * Complex.I) := by
      rw [Complex.ofReal_add, add_mul, Complex.exp_add]
      ring
    simp only [RCLike.im_to_complex]
    rw [e, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have hprod : Tendsto (fun M : ℝ ↦ Complex.exp (((θ M : ℝ) : ℂ) * Complex.I)
      * ∫ v, (k v : ℂ) * Complex.exp (((M * v : ℝ) : ℂ) * Complex.I)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero] at h ⊢
    refine h.congr fun M ↦ ?_
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have := (Complex.continuous_im.tendsto 0).comp hprod
  simp only [Complex.zero_im] at this
  exact this.congr fun M ↦ (key M).symm

end RiemannLebesgue

section Kernel

/-- The Dirichlet kernel `D_M(t) = M sinc(M t)` (`= sin(M t)/t` for `t ≠ 0`). -/
@[expose] noncomputable def dirichletKer (M t : ℝ) : ℝ := M * sinc (M * t)

theorem dirichletKer_eq {M t : ℝ} (ht : t ≠ 0) : dirichletKer M t = Real.sin (M * t) / t := by
  unfold dirichletKer
  rcases eq_or_ne M 0 with hM | hM
  · simp [hM]
  · rw [sinc_of_ne_zero (mul_ne_zero hM ht)]
    field_simp

private theorem dirichletKer_neg (M t : ℝ) : dirichletKer M (-t) = dirichletKer M t := by
  unfold dirichletKer
  rw [mul_neg, sinc_neg]

theorem abs_dirichletKer_le (M t : ℝ) : |dirichletKer M t| ≤ |M| := by
  unfold dirichletKer
  rw [abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (abs_sinc_le_one _)

theorem continuous_dirichletKer (M : ℝ) : Continuous (dirichletKer M) := by
  unfold dirichletKer
  fun_prop

private theorem integrable_mul_dirichletKer {g : ℝ → ℝ} (hg : Integrable g) (M r : ℝ) :
    Integrable (fun v ↦ g v * dirichletKer M (v - r)) := by
  refine (hg.norm.const_mul |M|).mono' (hg.1.mul ((continuous_dirichletKer M).comp
    (continuous_id.sub continuous_const)).aestronglyMeasurable)
    (Eventually.of_forall fun v ↦ ?_)
  calc ‖g v * dirichletKer M (v - r)‖ = ‖g v‖ * ‖dirichletKer M (v - r)‖ := norm_mul _ _
    _ ≤ ‖g v‖ * |M| := mul_le_mul_of_nonneg_left
        (by rw [Real.norm_eq_abs]; exact abs_dirichletKer_le M _) (norm_nonneg _)
    _ = |M| * ‖g v‖ := mul_comm _ _

/-- `∫₀^δ D_M(t) dt = ∫₀^{Mδ} sinc`. -/
private theorem integral_dirichletKer_Ioc (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∫ t in Ioc (0 : ℝ) δ, dirichletKer M t = ∫ x in (0 : ℝ)..M * δ, sinc x := by
  rw [← intervalIntegral.integral_of_le hδ.le]
  unfold dirichletKer
  rw [intervalIntegral.integral_const_mul, ← smul_eq_mul,
    intervalIntegral.smul_integral_comp_mul_left, mul_zero]

/-- **Riemann–Lebesgue for a Lipschitz-dominated integrand**: if `|q(t)| ≤ L t` on `(0, δ]`, then
`∫₀^δ q(t) D_M(t) dt → 0` (the divided difference `q(t)/t` is bounded, so its integral against
`sin(M t)` vanishes). -/
theorem tendsto_integral_mul_dirichletKer_Ioc_of_le_mul {q : ℝ → ℝ} {δ L : ℝ}
    (hqm : AEStronglyMeasurable q (volume.restrict (Ioc 0 δ)))
    (hlip : ∀ t ∈ Ioc 0 δ, |q t| ≤ L * t) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, q t * dirichletKer M t) atTop (𝓝 0) := by
  set k : ℝ → ℝ := (Ioc (0 : ℝ) δ).indicator fun t ↦ q t * t⁻¹ with hk
  have hkm : AEStronglyMeasurable k volume :=
    (aestronglyMeasurable_indicator_iff measurableSet_Ioc).mpr
      (hqm.mul measurable_inv.aestronglyMeasurable.restrict)
  have hkb : ∀ t, ‖k t‖ ≤ (Ioc (0 : ℝ) δ).indicator (fun _ ↦ max L 0) t := by
    intro t
    by_cases ht : t ∈ Ioc (0 : ℝ) δ
    · simp only [hk, indicator_of_mem ht, Real.norm_eq_abs]
      rw [abs_mul, abs_inv, abs_of_pos ht.1, ← div_eq_mul_inv, div_le_iff₀ ht.1]
      exact (hlip t ht).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) ht.1.le)
    · simp [hk, indicator_of_notMem ht]
  have hki : Integrable k :=
    (((integrableOn_const (C := max L 0) measure_Ioc_lt_top.ne).integrable_indicator
      measurableSet_Ioc).mono' hkm (Eventually.of_forall hkb))
  have hid : ∀ M, ∫ t in Ioc (0 : ℝ) δ, q t * dirichletKer M t
      = ∫ t, k t * Real.sin (M * t + 0) := by
    intro M
    rw [← integral_indicator measurableSet_Ioc]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    by_cases ht : t ∈ Ioc (0 : ℝ) δ
    · simp only [hk, indicator_of_mem ht, add_zero]
      rw [dirichletKer_eq ht.1.ne', div_eq_mul_inv]
      ring
    · simp [hk, indicator_of_notMem ht]
  simp_rw [hid]
  exact tendsto_integral_mul_sin_add_atTop hki (fun _ ↦ 0)

/-- The near part of the right half-line: the divided difference `(g(t) − gp)/t` is bounded on
`(0, δ]`, so its integral against `sin(M t)` vanishes (Riemann–Lebesgue). -/
private theorem tendsto_integral_sub_mul_dirichletKer_Ioc {g : ℝ → ℝ} (hg : Integrable g)
    {gp δ L : ℝ} (hlip : ∀ t ∈ Ioc 0 δ, |g t - gp| ≤ L * t) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g t - gp) * dirichletKer M t) atTop (𝓝 0) :=
  tendsto_integral_mul_dirichletKer_Ioc_of_le_mul
    ((hg.1.sub aestronglyMeasurable_const).restrict) hlip

/-- A bounded measurable function times the Dirichlet kernel is integrable on `(0, δ]`. -/
theorem integrableOn_mul_dirichletKer_of_bounded {q : ℝ → ℝ} {δ B : ℝ}
    (hqm : AEStronglyMeasurable q (volume.restrict (Ioc 0 δ)))
    (hb : ∀ t ∈ Ioc 0 δ, |q t| ≤ B) (M : ℝ) :
    IntegrableOn (fun t ↦ q t * dirichletKer M t) (Ioc 0 δ) := by
  have hD : IntegrableOn (dirichletKer M) (Ioc 0 δ) :=
    ((continuous_dirichletKer M).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  refine (hD.norm.const_mul B).mono' (hqm.mul (continuous_dirichletKer M).aestronglyMeasurable)
    ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact hb t ht) (norm_nonneg _)

/-- The far part: away from the singularity `g(t)/t` is integrable, so the integral against
`sin(M t)` vanishes (Riemann–Lebesgue). -/
private theorem tendsto_integral_mul_dirichletKer_Ioi {g : ℝ → ℝ} (hg : Integrable g) {δ : ℝ}
    (hδ : 0 < δ) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioi δ, g t * dirichletKer M t) atTop (𝓝 0) := by
  set k : ℝ → ℝ := (Ioi δ).indicator fun t ↦ g t * t⁻¹ with hk
  have hki : Integrable k := by
    refine (hg.norm.const_mul δ⁻¹).mono'
      ((hg.1.mul measurable_inv.aestronglyMeasurable).indicator measurableSet_Ioi)
      (Eventually.of_forall fun t ↦ ?_)
    by_cases ht : t ∈ Ioi δ
    · have ht0 : 0 < t := hδ.trans ht
      simp only [hk, indicator_of_mem ht, Real.norm_eq_abs]
      rw [abs_mul, abs_inv, abs_of_pos ht0, ← div_eq_mul_inv, div_le_iff₀ ht0]
      have : 1 ≤ δ⁻¹ * t := by
        rw [← div_eq_inv_mul, le_div_iff₀ hδ, one_mul]
        exact le_of_lt ht
      calc |g t| = |g t| * 1 := (mul_one _).symm
        _ ≤ |g t| * (δ⁻¹ * t) := mul_le_mul_of_nonneg_left this (abs_nonneg _)
        _ = δ⁻¹ * |g t| * t := by ring
    · simp only [hk, indicator_of_notMem ht, norm_zero, Real.norm_eq_abs]
      positivity
  have hid : ∀ M, ∫ t in Ioi δ, g t * dirichletKer M t = ∫ t, k t * Real.sin (M * t + 0) := by
    intro M
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    by_cases ht : t ∈ Ioi δ
    · simp only [hk, indicator_of_mem ht, add_zero]
      rw [dirichletKer_eq (hδ.trans ht).ne', div_eq_mul_inv]
      ring
    · simp [hk, indicator_of_notMem ht]
  simp_rw [hid]
  exact tendsto_integral_mul_sin_add_atTop hki (fun _ ↦ 0)

/-- **The right half-line from a near-part certificate**: if the near part
`∫₀^δ (g(t) − gp) D_M(t) dt` vanishes, then `∫₀^∞ g(t) D_M(t) dt → (π/2) gp`. -/
private theorem tendsto_integral_mul_dirichletKer_Ioi_zero_of_near {g : ℝ → ℝ} (hg : Integrable g)
    {gp δ : ℝ} (hδ : 0 < δ)
    (hnear : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g t - gp) * dirichletKer M t) atTop
      (𝓝 0)) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioi (0 : ℝ), g t * dirichletKer M t) atTop (𝓝 (π / 2 * gp)) := by
  have hI : ∀ M, Integrable (fun t ↦ g t * dirichletKer M t) := fun M ↦ by
    simpa using integrable_mul_dirichletKer hg M 0
  have hD : ∀ M, IntegrableOn (dirichletKer M) (Ioc 0 δ) := fun M ↦
    ((continuous_dirichletKer M).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  have hsplit : ∀ M, ∫ t in Ioi (0 : ℝ), g t * dirichletKer M t
      = ((∫ t in Ioc (0 : ℝ) δ, (g t - gp) * dirichletKer M t)
          + gp * ∫ t in Ioc (0 : ℝ) δ, dirichletKer M t)
        + ∫ t in Ioi δ, g t * dirichletKer M t := by
    intro M
    rw [← Ioc_union_Ioi_eq_Ioi hδ.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hI M).integrableOn (hI M).integrableOn]
    congr 1
    have h1 : IntegrableOn (fun t ↦ (g t - gp) * dirichletKer M t) (Ioc 0 δ) := by
      have : (fun t ↦ (g t - gp) * dirichletKer M t)
          = fun t ↦ g t * dirichletKer M t - gp * dirichletKer M t := by
        funext t; ring
      rw [this]
      exact (hI M).integrableOn.sub ((hD M).const_mul gp)
    rw [← integral_const_mul, ← integral_add h1 ((hD M).const_mul gp)]
    refine setIntegral_congr_fun measurableSet_Ioc fun t _ ↦ ?_
    ring
  simp_rw [hsplit]
  have h3 := tendsto_integral_mul_dirichletKer_Ioi hg hδ
  have h2 : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, dirichletKer M t) atTop (𝓝 (π / 2)) := by
    have hMδ : Tendsto (fun M : ℝ ↦ M * δ) atTop atTop := tendsto_id.atTop_mul_const hδ
    refine (tendsto_integral_sinc.comp hMδ).congr' ?_
    filter_upwards [eventually_gt_atTop 0] with M _
    simp only [Function.comp]
    exact (integral_dirichletKer_Ioc M hδ).symm
  convert (hnear.add (h2.const_mul gp)).add h3 using 2
  ring

/-- **The right half-line**: `∫₀^∞ g(t) D_M(t) dt → (π/2) g(0+)` when `g` is integrable and
`|g(t) − g(0+)| ≤ L t` on `(0, δ]`. -/
theorem tendsto_integral_mul_dirichletKer_Ioi_zero {g : ℝ → ℝ} (hg : Integrable g)
    {gp δ L : ℝ} (hδ : 0 < δ) (hlip : ∀ t ∈ Ioc 0 δ, |g t - gp| ≤ L * t) :
    Tendsto (fun M : ℝ ↦ ∫ t in Ioi (0 : ℝ), g t * dirichletKer M t) atTop (𝓝 (π / 2 * gp)) :=
  tendsto_integral_mul_dirichletKer_Ioi_zero_of_near hg hδ
    (tendsto_integral_sub_mul_dirichletKer_Ioc hg hlip)

/-- **The left half-line from a near-part certificate**, by reflection: the near part is that
of `t ↦ g(−t)`. -/
private theorem tendsto_integral_mul_dirichletKer_Iio_zero_of_near {g : ℝ → ℝ} (hg : Integrable g)
    {gm δ : ℝ} (hδ : 0 < δ)
    (hnear : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (-t) - gm) * dirichletKer M t) atTop
      (𝓝 0)) :
    Tendsto (fun M : ℝ ↦ ∫ t in Iio (0 : ℝ), g t * dirichletKer M t) atTop (𝓝 (π / 2 * gm)) := by
  have hg' : Integrable (fun t ↦ g (-t)) := hg.comp_neg
  have h := tendsto_integral_mul_dirichletKer_Ioi_zero_of_near hg' hδ hnear
  refine h.congr fun M ↦ ?_
  have e := integral_comp_neg_Ioi (0 : ℝ) (fun t ↦ g t * dirichletKer M t)
  simp only [neg_zero] at e
  rw [setIntegral_congr_set Iio_ae_eq_Iic, ← e]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  simp only [dirichletKer_neg]

/-- **The left half-line**, by reflection. -/
theorem tendsto_integral_mul_dirichletKer_Iio_zero {g : ℝ → ℝ} (hg : Integrable g)
    {gm δ L : ℝ} (hδ : 0 < δ) (hlip : ∀ t ∈ Ioc 0 δ, |g (-t) - gm| ≤ L * t) :
    Tendsto (fun M : ℝ ↦ ∫ t in Iio (0 : ℝ), g t * dirichletKer M t) atTop (𝓝 (π / 2 * gm)) :=
  tendsto_integral_mul_dirichletKer_Iio_zero_of_near hg hδ
    (tendsto_integral_sub_mul_dirichletKer_Ioc hg.comp_neg hlip)

/-- **The Dirichlet kernel at a jump, centred at `0`, from near-part certificates.** -/
private theorem tendsto_integral_mul_dirichletKer_zero_of_near {g : ℝ → ℝ} (hg : Integrable g)
    {gp gm δ : ℝ} (hδ : 0 < δ)
    (hR : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g t - gp) * dirichletKer M t) atTop (𝓝 0))
    (hL : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (-t) - gm) * dirichletKer M t) atTop
      (𝓝 0)) :
    Tendsto (fun M : ℝ ↦ ∫ t, g t * dirichletKer M t) atTop (𝓝 (π / 2 * (gp + gm))) := by
  have hsplit : ∀ M, ∫ t, g t * dirichletKer M t
      = (∫ t in Iio (0 : ℝ), g t * dirichletKer M t)
        + ∫ t in Ioi (0 : ℝ), g t * dirichletKer M t := by
    intro M
    rw [← integral_add_compl measurableSet_Iio
      (by simpa using integrable_mul_dirichletKer hg M 0), compl_Iio, integral_Ici_eq_integral_Ioi]
  simp_rw [hsplit]
  convert (tendsto_integral_mul_dirichletKer_Iio_zero_of_near hg hδ hL).add
    (tendsto_integral_mul_dirichletKer_Ioi_zero_of_near hg hδ hR) using 2
  ring

/-- **The Dirichlet kernel at a jump, centred at `0`.** -/
private theorem tendsto_integral_mul_dirichletKer_zero {g : ℝ → ℝ} (hg : Integrable g)
    {gp gm δ L : ℝ} (hδ : 0 < δ) (hR : ∀ t ∈ Ioc 0 δ, |g t - gp| ≤ L * t)
    (hL : ∀ t ∈ Ioc 0 δ, |g (-t) - gm| ≤ L * t) :
    Tendsto (fun M : ℝ ↦ ∫ t, g t * dirichletKer M t) atTop (𝓝 (π / 2 * (gp + gm))) :=
  tendsto_integral_mul_dirichletKer_zero_of_near hg hδ
    (tendsto_integral_sub_mul_dirichletKer_Ioc hg hR)
    (tendsto_integral_sub_mul_dirichletKer_Ioc hg.comp_neg hL)

/-- **The Dirichlet kernel at a jump from near-part certificates**: for integrable `g` and
`gp, gm` with `∫₀^δ (g(r ± t) − g(r±)) D_M(t) dt → 0`,
`∫ g(v) sin(M(v−r))/(v−r) dv → (π/2)(g(r+) + g(r−))` as `M → ∞`. -/
theorem tendsto_integral_mul_dirichletKer_of_near {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ)
    {gp gm δ : ℝ} (hδ : 0 < δ)
    (hR : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (r + t) - gp) * dirichletKer M t) atTop
      (𝓝 0))
    (hL : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (r - t) - gm) * dirichletKer M t) atTop
      (𝓝 0)) :
    Tendsto (fun M : ℝ ↦ ∫ v, g v * dirichletKer M (v - r)) atTop (𝓝 (π / 2 * (gp + gm))) := by
  have hg' : Integrable (fun t ↦ g (t + r)) := hg.comp_add_right r
  have hR' : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (t + r) - gp) * dirichletKer M t)
      atTop (𝓝 0) := by
    refine hR.congr fun M ↦ integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp only
    rw [add_comm r t]
  have hL' : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ, (g (-t + r) - gm) * dirichletKer M t)
      atTop (𝓝 0) := by
    refine hL.congr fun M ↦ integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
    simp only
    rw [show r - t = -t + r by ring]
  have h := tendsto_integral_mul_dirichletKer_zero_of_near hg' hδ (gp := gp) (gm := gm) hR' hL'
  refine h.congr fun M ↦ ?_
  rw [← integral_add_right_eq_self (fun v ↦ g v * dirichletKer M (v - r)) r]
  simp only [add_sub_cancel_right]

/-- **The Dirichlet kernel at a jump** (the localization lemma of the principal-value inversion):
for integrable `g` with one-sided limits `g(r±)` approached at a Lipschitz rate on `(0, δ]`,
`∫ g(v) sin(M(v−r))/(v−r) dv → (π/2)(g(r+) + g(r−))` as `M → ∞`. -/
theorem tendsto_integral_mul_dirichletKer {g : ℝ → ℝ} (hg : Integrable g) (r : ℝ)
    {gp gm δ L : ℝ} (hδ : 0 < δ) (hR : ∀ t ∈ Ioc 0 δ, |g (r + t) - gp| ≤ L * t)
    (hL : ∀ t ∈ Ioc 0 δ, |g (r - t) - gm| ≤ L * t) :
    Tendsto (fun M : ℝ ↦ ∫ v, g v * dirichletKer M (v - r)) atTop (𝓝 (π / 2 * (gp + gm))) := by
  have hg' : Integrable (fun t ↦ g (t + r)) := hg.comp_add_right r
  have h := tendsto_integral_mul_dirichletKer_zero hg' hδ (gp := gp) (gm := gm) (L := L)
    (fun t ht ↦ by have := hR t ht; rwa [add_comm] at this)
    (fun t ht ↦ by have := hL t ht; rwa [show r - t = -t + r by ring] at this)
  refine h.congr fun M ↦ ?_
  rw [← integral_add_right_eq_self (fun v ↦ g v * dirichletKer M (v - r)) r]
  simp only [add_sub_cancel_right]

end Kernel

end Real
