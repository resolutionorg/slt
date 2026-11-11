/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Transforms
public import SLT.Analysis.Fourier.DirichletKernel
public import SLT.Analysis.Mellin.Defs

/-!
# [Wat09, Theorem 4.5] in principal-value form: the jump average `½{f(s+0) + f(s−0)}`

The book reads the line integral of (4.11) as the symmetric limit `lim_{M→∞} ∫_{c−iM}^{c+iM}`
and recovers the average of the one-sided limits of `f` at `s` (§4.3 remark (1)). Here:

The transform in the logarithmic variable `x = log t` is a Fourier integral of
`h(x) = f(eˣ) e^{(c+1)x}` (`mellinTransform_eq_integral_logVar`). Fubini identifies its
truncated inverse with the Dirichlet-kernel integral at `u = log s`
(`inverseMellinTrunc_eq`). The localization result `inverseMellin_tendsto_of_near` reduces
inversion to vanishing of the two local remainder integrals; `InverseMellinBV` verifies
these using bounded variation.

No absolute integrability of `F` along the line is assumed (the book's example `f = t^{λ−1}` on
`(0, a)` has `|F(c+iy)| ~ 1/|y|`), and `f` may jump at `s`.
-/

public section

open MeasureTheory Set Filter Topology Complex

namespace SingularLearningTheory.MellinAnalysis

section Elementary

/-- `|eˣ − 1| ≤ |x| e^{|x|}`. -/
theorem _root_.Real.abs_exp_sub_one_le_abs_mul_exp
    (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 : (0 : ℝ) ≤ Real.exp x - 1 := by linarith [Real.add_one_le_exp x]
    rw [abs_of_nonneg hx, abs_of_nonneg h1]
    have h := Real.add_one_le_exp (-x)
    have hpos := Real.exp_pos x
    have : (-x + 1) * Real.exp x ≤ 1 := by
      calc (-x + 1) * Real.exp x ≤ Real.exp (-x) * Real.exp x :=
            mul_le_mul_of_nonneg_right h hpos.le
        _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    nlinarith
  · have h1 : Real.exp x - 1 ≤ 0 := by linarith [Real.exp_le_one_iff.mpr hx.le]
    rw [abs_of_neg hx, abs_of_nonpos h1]
    have h2 := Real.add_one_le_exp x
    have h3 : (1 : ℝ) ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith

/-- The logarithmic-variable representative `h(x) = f(eˣ) e^{(c+1)x}` of the Mellin integrand. -/
@[expose] noncomputable def logVar (f : ℝ → ℝ) (c x : ℝ) : ℝ := f (Real.exp x) * Real.exp
    ((c + 1) * x)

private theorem exp_image_univ : Real.exp '' univ = Ioi 0 := by rw [image_univ, Real.range_exp]

private theorem hasDerivWithinAt_exp_univ (x : ℝ) (_ : x ∈ (univ : Set ℝ)) :
    HasDerivWithinAt Real.exp (Real.exp x) univ x :=
  (Real.hasDerivAt_exp x).hasDerivWithinAt

/-- `∫₀^∞ |f(t)| t^c dt < ∞` is the integrability of `h`. -/
private theorem integrable_logVar_iff (f : ℝ → ℝ) (c : ℝ) :
    Integrable (logVar f c) ↔ IntegrableOn (fun t ↦ f t * t ^ c) (Ioi 0) := by
  rw [← exp_image_univ, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    hasDerivWithinAt_exp_univ Real.exp_injective.injOn, integrableOn_univ]
  refine integrable_congr (Eventually.of_forall fun x ↦ ?_)
  simp only [logVar, smul_eq_mul, abs_of_pos (Real.exp_pos x)]
  rw [Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp, mul_comm x c, add_mul, one_mul,
    Real.exp_add]
  ring

/-- The book's transform (4.10) in the logarithmic variable: `F(c + iy) = ∫ h(x) e^{iyx} dx`. -/
private theorem mellinTransform_eq_integral_logVar (f : ℝ → ℝ) (c y : ℝ) :
    mellinTransform f (c + y * I)
      = ∫ x, (logVar f c x : ℂ) * Complex.exp (((y * x : ℝ) : ℂ) * I) := by
  unfold mellinTransform
  rw [← exp_image_univ, integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    hasDerivWithinAt_exp_univ Real.exp_injective.injOn, setIntegral_univ]
  refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
  simp only [abs_of_pos (Real.exp_pos x), logVar, real_smul]
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Real.exp_pos x).ne'),
    ← Complex.ofReal_log (Real.exp_pos x).le, Real.log_exp]
  push_cast
  rw [show (x : ℂ) * (c + y * I) = c * x + y * x * I by ring, Complex.exp_add,
    show (c + 1) * (x : ℂ) = c * x + x by ring, Complex.exp_add]
  ring

/-- `s^{−(c+iy)−1} = s^{−(c+1)} e^{−iy log s}` for `s > 0`. -/
private theorem cpow_neg_sub_one_eq {s : ℝ} (hs : 0 < s) (c y : ℝ) :
    (s : ℂ) ^ (-(c + y * I) - 1)
      = ((s ^ (-(c + 1)) : ℝ) : ℂ) * Complex.exp (-(((y * Real.log s : ℝ) : ℂ) * I)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hs.ne'), ← Complex.ofReal_log hs.le,
    Real.rpow_def_of_pos hs, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `∫_{−M}^{M} e^{iyt} dy = 2 D_M(t)` (`= 2 sin(Mt)/t`, `= 2M` at `t = 0`). -/
private theorem integral_exp_mul_I_symm (M t : ℝ) :
    ∫ y in -M..M, Complex.exp (((y * t : ℝ) : ℂ) * I) = 2 * (Real.dirichletKer M t : ℂ) := by
  rcases eq_or_ne t 0 with ht | ht
  · subst ht
    simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
      intervalIntegral.integral_const, sub_neg_eq_add, real_smul, mul_one, Real.dirichletKer,
      Real.sinc_zero]
    push_cast
    ring
  · have hc : (t : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast ht) I_ne_zero
    have e : ∀ y : ℝ, Complex.exp (((y * t : ℝ) : ℂ) * I) = Complex.exp (((t : ℂ) * I) * y) :=
      fun y ↦ by push_cast; ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc, Real.dirichletKer_eq ht, div_eq_iff hc]
    have h1 : (t : ℂ) * I * (M : ℂ) = ((M * t : ℝ) : ℂ) * I := by push_cast; ring
    have h2 : (t : ℂ) * I * ((-M : ℝ) : ℂ) = (-(M * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [h1, h2, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
      ← Complex.ofReal_sin]
    have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht
    push_cast
    field_simp
    ring

end Elementary

section Inversion

/-- The truncated inverse as a Dirichlet-kernel integral in the logarithmic variable:
`(1/2πi) ∫_{c−iM}^{c+iM} F(z) s^{−z−1} dz = (s^{−(c+1)}/π) ∫ h(x) D_M(x − log s) dx`. -/
private theorem inverseMellinTrunc_eq {f : ℝ → ℝ} {c : ℝ}
    (hconv : IntegrableOn (fun t ↦ f t * t ^ c) (Ioi 0)) {s : ℝ} (hs : 0 < s) {M : ℝ}
    (hM : 0 ≤ M) :
    inverseMellinTrunc c (mellinTransform f) s M
      = (((s ^ (-(c + 1)) / Real.pi) : ℝ) : ℂ)
          * ((∫ x, logVar f c x * Real.dirichletKer M (x - Real.log s) : ℝ) : ℂ) := by
  have hh : Integrable (logVar f c) := (integrable_logVar_iff f c).mpr hconv
  set u := Real.log s with hu
  -- the integrand on the line
  have hpt : ∀ y : ℝ, mellinTransform f (c + y * I) * (s : ℂ) ^ (-(c + y * I) - 1)
      = ((s ^ (-(c + 1)) : ℝ) : ℂ)
        * ∫ x, (logVar f c x : ℂ) * Complex.exp (((y * (x - u) : ℝ) : ℂ) * I) := by
    intro y
    rw [mellinTransform_eq_integral_logVar, cpow_neg_sub_one_eq hs, ← hu]
    rw [show ∀ (A B C : ℂ), A * (B * C) = B * (A * C) from fun A B C ↦ by ring,
      ← integral_mul_const]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x ↦ ?_)
    simp only
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  -- Fubini on `[−M, M] × ℝ`
  have hprod : Integrable (fun z : ℝ × ℝ ↦
      (logVar f c z.2 : ℂ) * Complex.exp (((z.1 * (z.2 - u) : ℝ) : ℂ) * I))
      ((volume.restrict (Ioc (-M) M)).prod volume) := by
    have hcont : Continuous (fun z : ℝ × ℝ ↦ Complex.exp (((z.1 * (z.2 - u) : ℝ) : ℂ) * I)) := by
      fun_prop
    have hmeas : AEStronglyMeasurable
        (fun z : ℝ × ℝ ↦ (logVar f c z.2 : ℂ) * Complex.exp (((z.1 * (z.2 - u) : ℝ) : ℂ) * I))
        ((volume.restrict (Ioc (-M) M)).prod volume) :=
      by exact (Complex.continuous_ofReal.comp_aestronglyMeasurable
        (hh.1.comp_quasiMeasurePreserving (Measure.quasiMeasurePreserving_snd
          (μ := volume.restrict (Ioc (-M) M)) (ν := volume)))).mul hcont.aestronglyMeasurable
    refine ((integrable_const (1 : ℝ)).mul_prod hh.norm).mono' hmeas
      (Eventually.of_forall fun z ↦ ?_)
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, one_mul]
  have hswap := integral_integral_swap
    (f := fun (y x : ℝ) ↦ (logVar f c x : ℂ) * Complex.exp (((y * (x - u) : ℝ) : ℂ) * I)) hprod
  -- the inner `y`-integral is `2 D_M(x − u)`
  have hinner : ∀ x : ℝ,
      ∫ y in Ioc (-M) M, (logVar f c x : ℂ) * Complex.exp (((y * (x - u) : ℝ) : ℂ) * I)
      = (logVar f c x : ℂ) * (2 * (Real.dirichletKer M (x - u) : ℂ)) := by
    intro x
    rw [integral_const_mul, ← intervalIntegral.integral_of_le (by linarith : -M ≤ M),
      integral_exp_mul_I_symm]
  -- assemble
  unfold inverseMellinTrunc
  simp_rw [mul_comm I, hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by linarith : -M ≤ M),
    hswap]
  simp_rw [hinner]
  rw [show (fun x : ℝ ↦ (logVar f c x : ℂ) * (2 * (Real.dirichletKer M (x - u) : ℂ)))
      = fun x : ℝ ↦ (2 : ℂ) * ((logVar f c x * Real.dirichletKer M (x - u) : ℝ) : ℂ) from by
        funext x; push_cast; ring,
    integral_const_mul, integral_complex_ofReal]
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp

/-- **Theorem 4.5 in principal-value form from near-part certificates**: if the near parts of
the logarithmic representative `h = logVar f c` at `u = log s` vanish,
`∫₀^δ (h(u ± t) − f(s±0) s^{c+1}) D_M(t) dt → 0`, then the symmetric truncations converge to
`½{f(s+0) + f(s−0)}`. -/
theorem inverseMellin_tendsto_of_near (f : ℝ → ℝ) {c : ℝ}
    (hconv : IntegrableOn (fun t ↦ f t * t ^ c) (Ioi 0)) {s : ℝ} (hs : 0 < s)
    {fp fm δ : ℝ} (hδ : 0 < δ)
    (hR : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ,
      (logVar f c (Real.log s + t) - fp * s ^ (c + 1)) * Real.dirichletKer M t) atTop (𝓝 0))
    (hL : Tendsto (fun M : ℝ ↦ ∫ t in Ioc (0 : ℝ) δ,
      (logVar f c (Real.log s - t) - fm * s ^ (c + 1)) * Real.dirichletKer M t) atTop (𝓝 0)) :
    Tendsto (fun M : ℝ ↦ inverseMellinTrunc c (mellinTransform f) s M) atTop
      (𝓝 (((fp + fm) / 2 : ℝ) : ℂ)) := by
  have hh : Integrable (logVar f c) := (integrable_logVar_iff f c).mpr hconv
  set u := Real.log s with hu
  set a := c + 1 with ha
  -- the kernel limit
  have hker := Real.tendsto_integral_mul_dirichletKer_of_near hh u hδ hR hL
  -- the truncated inverse is the kernel integral (for `M ≥ 0`)
  have hconst : (fp + fm) / 2
      = s ^ (-(c + 1)) / Real.pi * (Real.pi / 2 * (fp * s ^ a + fm * s ^ a)) := by
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [← ha, Real.rpow_neg hs.le]
    field_simp
  have hlimR : Tendsto (fun M : ℝ ↦ s ^ (-(c + 1)) / Real.pi
      * ∫ x, logVar f c x * Real.dirichletKer M (x - u)) atTop (𝓝 ((fp + fm) / 2)) := by
    rw [hconst]
    exact hker.const_mul _
  have hlim := (Complex.continuous_ofReal.tendsto _).comp hlimR
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with M hM
  simp only [Function.comp]
  rw [inverseMellinTrunc_eq hconv hs hM, Complex.ofReal_mul]


end Inversion

end SingularLearningTheory.MellinAnalysis
