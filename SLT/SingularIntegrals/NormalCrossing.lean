/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.SpecialFunctions.Pow.LogBounds
public import SLT.FreeEnergy.AnalyticDivision
public import SLT.SingularIntegrals.StateDensity
public import SLT.Resolution.Atlas
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Algebra.Order.Ring.Star
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Normal crossing calculations

The explicit one-dimensional integrals behind the normal-crossing section of the
singular-integrals chapter of [Hit26] (Chapter 3).

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 3.2.2] ([Wat09, Example 4.7]) | `integral_rpow_mul_log_pow` |
| [Hit26, Lemma 3.2.4] ([Wat09, Corollary 4.3]), `m = 1` | `sublevelVolume_monomial` |
| [Hit26, Lemma 3.2.3] ([Wat09, Theorem 4.6]) | `stateDensityMeasure_monomial_cube`, |
| | `isStateDensity_monomial_cube` |
| the constant `γ_b` of [Wat09, Theorem 4.6] | `gammaConst` |
| [Hit26, Equation (3.2.1)], `Z^p(n)` | `normalCrossingIntegral₀` |
| [Hit26, Theorem 3.2.6] ([Wat09, Theorem 4.7]) | `blockIntegral₀_lower_bound`, `blockIntegral₀_upper_bound` |
| block form of a cube integral (no thesis counterpart) | `MeasurableEquiv.blockEquiv`,
`integral_cube_eq_blockIntegral₀` |

## The state density of a monomial in several variables

[Wat09, Theorem 4.6] computes the state density of `F(u) = a u^{2k}` on the cube `[0, b]^m`
against the weight `u^h`, when every coordinate has the same ratio
`(h_j + 1) / (2 k_j) = λ`. [Hit26] proves it by reading the answer off the
Mellin transform of the zeta function `∫ (a u^{2k})^z u^h du`, which needs
uniqueness of Mellin inversion. Here the proof is by induction on the number of
coordinates instead:

* one coordinate is the substitution `t = a u^{2k}` (`map_monomial_one_dim`);
* adding a coordinate multiplies the energy by an independent factor, so the
  state density measure is the *multiplicative convolution* of the two state
  density measures (`stateDensityMeasure` of a product is `Measure.mconv`), and
  the convolution of `t^{λ-1} (log (c₁/t))^n` with `s^{λ-1}` on `(0, c₂)` is
  `p^{λ-1} (log (c₁ c₂ / p))^{n+1} / (n + 1)` (`mconv_logPowerDensity`).

The densities involved are all of the shape `logPowerDensity`.
-/

public section

open MeasureTheory Nat Set
open scoped MeasureTheory

namespace SingularLearningTheory

/-- `t ↦ t^(λ-1) c^(-λ) (log (c/t))^n / n!` on `(0, c)`, and `0` elsewhere. Up to the
constant `∏ b^(h_j+1) / (2 k_j)`, this is the state density of `u ↦ a u^{2k}` on
`[0, b]^(n+1)` against `u^h`, with `c = a b^{2|k|}` ([Wat09, Theorem 4.6]). -/
@[expose] noncomputable def logPowerDensity (lam : ℝ) (n : ℕ) (c : ℝ) : ℝ → ℝ :=
  (Ioo 0 c).indicator fun t ↦ t ^ (lam - 1) * c ^ (-lam) * Real.log (c / t) ^ n / n !

private theorem logPowerDensity_nonneg {lam c : ℝ} (n : ℕ) (hc : 0 < c) (t : ℝ) :
    0 ≤ logPowerDensity lam n c t := by
  unfold logPowerDensity
  refine indicator_nonneg (fun t ht ↦ ?_) t
  obtain ⟨ht0, htc⟩ := ht
  have hlog : 0 ≤ Real.log (c / t) := Real.log_nonneg ((one_le_div ht0).mpr htc.le)
  positivity

private theorem measurable_logPowerDensity (lam : ℝ) (n : ℕ) (c : ℝ) :
    Measurable (logPowerDensity lam n c) := by
  unfold logPowerDensity
  refine Measurable.indicator ?_ measurableSet_Ioo
  fun_prop

/-- No thesis counterpart; the Gamma-type integral used by
`integral_rpow_mul_log_pow`, and hence by
[Hit26, Lemma 3.2.2]. -/
private theorem integral_pow_mul_exp_neg {s : ℝ} (hs : 0 < s) (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), x ^ m * Real.exp (-(s * x)) = (m ! : ℝ) / s ^ (m + 1) := by
  have key := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (m : ℝ) + 1) (r := s)
    (by positivity) hs
  rw [Real.Gamma_nat_eq_factorial] at key
  have hcongr : ∫ x in Ioi (0 : ℝ), x ^ m * Real.exp (-(s * x))
      = ∫ x in Ioi (0 : ℝ), x ^ ((m : ℝ) + 1 - 1) * Real.exp (-(s * x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx ↦ ?_
    rw [add_sub_cancel_right, Real.rpow_natCast]
  rw [hcongr, key, show ((m : ℝ) + 1) = ((m + 1 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_natCast, div_pow, one_pow]
  ring

/-- [Hit26, Lemma 3.2.2] ([Wat09, Example 4.7]), the integral at
its heart: for `a, s > 0` and `m : ℕ`,

    ∫₀^a t^(s-1) (log (a/t))^m dt = m! · a^s / s^(m+1).

[Hit26] obtains this by `m` integrations by parts; the proof here is the
substitution `t = a e^{-x}`, which turns it into `integral_pow_mul_exp_neg`.

Taking `s = z + λ` and multiplying by `a^{-λ}/(m-1)!` gives [Hit26]'s Mellin
transform `(𝓜ν)(z) = a^z / (z + λ)^m` of the state density in the lemma. -/
theorem _root_.integral_rpow_mul_log_pow {a s : ℝ} (ha : 0 < a) (hs : 0 < s) (m : ℕ) :
    ∫ t in Ioo (0 : ℝ) a, t ^ (s - 1) * Real.log (a / t) ^ m
      = (m ! : ℝ) * a ^ s / s ^ (m + 1) := by
  have himg : (fun x ↦ a * Real.exp (-x)) '' Ioi 0 = Ioo 0 a := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      have hlt : Real.exp (-x) < 1 := Real.exp_lt_one_iff.mpr (by simpa using hx)
      exact ⟨by positivity, by nlinarith [Real.exp_pos (-x)]⟩
    · rintro ⟨ht0, hta⟩
      refine ⟨Real.log (a / t), Real.log_pos ((one_lt_div ht0).mpr hta), ?_⟩
      change a * Real.exp (-Real.log (a / t)) = t
      rw [Real.exp_neg, Real.exp_log (by positivity)]
      field_simp
  have hderiv : ∀ x ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun x ↦ a * Real.exp (-x)) (-(a * Real.exp (-x))) (Ioi 0) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ ↦ Real.exp (-x)) (-Real.exp (-x)) x := by
      exact ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun x : ℝ ↦ a * Real.exp (-x)) (-(a * Real.exp (-x))) x := by
      simpa [mul_neg] using h1.const_mul a
    exact h2.hasDerivWithinAt
  have hinj : InjOn (fun x ↦ a * Real.exp (-x)) (Ioi (0 : ℝ)) := by
    intro x _ y _ hxy
    exact neg_injective (Real.exp_eq_exp.mp (mul_left_cancel₀ ha.ne' hxy))
  rw [← himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hderiv hinj]
  have hsub : ∀ x ∈ Ioi (0 : ℝ),
      |(-(a * Real.exp (-x)))| •
          ((a * Real.exp (-x)) ^ (s - 1) * Real.log (a / (a * Real.exp (-x))) ^ m)
        = a ^ s * (x ^ m * Real.exp (-(s * x))) := by
    intro x _
    have hax : (0 : ℝ) < a * Real.exp (-x) := by positivity
    have hlog : Real.log (a / (a * Real.exp (-x))) = x := by
      rw [show a / (a * Real.exp (-x)) = Real.exp x by rw [Real.exp_neg]; field_simp,
        Real.log_exp]
    have hrpow : (a * Real.exp (-x)) ^ (s - 1)
        = a ^ (s - 1) * Real.exp (-(x * (s - 1))) := by
      rw [Real.mul_rpow ha.le (Real.exp_pos _).le, ← Real.exp_mul, neg_mul]
    rw [hlog, hrpow, abs_neg, abs_of_pos hax, smul_eq_mul,
      show a * Real.exp (-x) * (a ^ (s - 1) * Real.exp (-(x * (s - 1))) * x ^ m)
          = a ^ (1 : ℝ) * a ^ (s - 1) * (Real.exp (-x) * Real.exp (-(x * (s - 1)))) * x ^ m by
        rw [Real.rpow_one]; ring,
      ← Real.rpow_add ha, ← Real.exp_add, show (1 : ℝ) + (s - 1) = s by ring,
      show -x + -(x * (s - 1)) = -(s * x) by ring]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hsub, integral_const_mul,
    integral_pow_mul_exp_neg hs m]
  ring

/-- [Hit26, Lemma 3.2.4] ([Wat09, Corollary 4.3]) in the case
`m = 1`: the sublevel volume of the one-variable monomial `F(u) = a u^(2k)` on
`(0, b)` against the weight `u^h`.

[Hit26] writes the answer as `γ_b t^λ / (λ a^λ)` with
`γ_b = b^(|h| + m - 2|k|λ) / (2^m (m-1)! k₁⋯k_m)`; at `m = 1` that constant is
`b^(h + 1 - 2kλ) / (2k) = 1 / (2k)`, since `2kλ = h + 1`, and so
`γ_b / λ = 1 / (2kλ) = 1 / (h + 1)`, which is the form proved here. -/
theorem sublevelVolume_monomial {a b h t : ℝ} {k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hk : 0 < k) (hh : -1 < h) (ht0 : 0 < t) (htb : t < a * b ^ (2 * k)) :
    sublevelVolume (fun u ↦ a * u ^ (2 * k)) (fun u ↦ u ^ h) (Ioo 0 b) t
      = t ^ ((h + 1) / (2 * k)) / (a ^ ((h + 1) / (2 * k)) * (h + 1)) := by
  have hk0 : 2 * k ≠ 0 := by omega
  have hkR : ((2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hta : 0 < t / a := div_pos ht0 ha
  set c : ℝ := (t / a) ^ (((2 * k : ℕ) : ℝ))⁻¹ with hcdef
  have hc0 : 0 < c := Real.rpow_pos_of_pos hta _
  have hcpow : c ^ (2 * k) = t / a := by
    rw [hcdef, ← Real.rpow_natCast _ (2 * k), ← Real.rpow_mul hta.le,
      inv_mul_cancel₀ hkR, Real.rpow_one]
  have hcb : c < b := by
    rw [← pow_lt_pow_iff_left₀ hc0.le hb.le hk0, hcpow, div_lt_iff₀ ha]
    linarith [htb]
  have hset : Ioo (0 : ℝ) b ∩ {u | a * u ^ (2 * k) ≤ t} = Ioc 0 c := by
    ext u
    simp only [mem_inter_iff, mem_Ioo, mem_Ioc, mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hu0, _⟩, hut⟩
      refine ⟨hu0, ?_⟩
      rw [← pow_le_pow_iff_left₀ hu0.le hc0.le hk0, hcpow, le_div_iff₀ ha, mul_comm]
      exact hut
    · rintro ⟨hu0, huc⟩
      refine ⟨⟨hu0, lt_of_le_of_lt huc hcb⟩, ?_⟩
      have := (pow_le_pow_iff_left₀ hu0.le hc0.le hk0).mpr huc
      rw [hcpow, le_div_iff₀ ha, mul_comm] at this
      exact this
  have hmeas : MeasurableSet {u : ℝ | a * u ^ (2 * k) ≤ t} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [sublevelVolume, setIntegral_indicator hmeas, hset,
    ← intervalIntegral.integral_of_le hc0.le, integral_rpow (Or.inl hh),
    Real.zero_rpow (by linarith), sub_zero, hcdef, ← Real.rpow_mul hta.le,
    Real.div_rpow ht0.le ha.le,
    show (((2 * k : ℕ) : ℝ))⁻¹ * (h + 1) = (h + 1) / (2 * k) by push_cast; ring]
  have hX : (0 : ℝ) < a ^ ((h + 1) / (2 * k)) := Real.rpow_pos_of_pos ha _
  field_simp

/-! ## The state density of a monomial in several variables ([Wat09, Theorem 4.6]) -/

/-- One coordinate of [Wat09, Theorem 4.6]: the pushforward of `u^h du` on `[0, b]` along
`u ↦ a u^{2k}` has density `(1 / 2k) a^{-λ} t^{λ-1}` on `(0, a b^{2k})`, where
`λ = (h + 1) / (2k)`. Written with the constant `b^(h+1) / (2k)` so that it is the
`n = 0` case of `stateDensityMeasure_monomial_cube`.

[Hit26] assumes `h > -1`; that is only needed for the measures to be finite, and
the identity of (possibly infinite) measures holds for every real `h`. The proof is
the substitution `u = (t/a)^{1/(2k)}` on the open interval. -/
private theorem map_monomial_one_dim {a b h lam : ℝ} {k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hk : 0 < k) (hlam : (h + 1) / (2 * k) = lam) :
    Measure.map (fun u : ℝ ↦ a * u ^ (2 * k))
        ((volume.restrict (Icc 0 b)).withDensity fun u ↦ ENNReal.ofReal (u ^ h))
      = volume.withDensity fun t ↦
          ENNReal.ofReal (b ^ (h + 1) / (2 * k) * logPowerDensity lam 0 (a * b ^ (2 * k)) t) := by
  have hk0 : 2 * k ≠ 0 := by omega
  have hkR : ((2 * k : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  set c : ℝ := a * b ^ (2 * k) with hcdef
  have hc : 0 < c := by positivity
  set e : ℝ := ((2 * k : ℕ) : ℝ)⁻¹ with hedef
  have he : 0 < e := by positivity
  have hlam' : e * (h + 1) = lam := by rw [hedef, ← hlam]; push_cast; ring
  have h2k : ((2 * k : ℕ) : ℝ) * lam = h + 1 := by
    rw [← hlam', ← mul_assoc, mul_inv_cancel₀ hkR, one_mul]
  set g : ℝ → ℝ := fun t ↦ (t / a) ^ e with hgdef
  have hgpow : ∀ t, 0 < t → g t ^ (2 * k) = t / a := fun t ht ↦
    Real.rpow_inv_natCast_pow (div_pos ht ha).le hk0
  have hgpos : ∀ t, 0 < t → 0 < g t := fun t ht ↦ Real.rpow_pos_of_pos (div_pos ht ha) _
  have hgb : ∀ t ∈ Ioo (0 : ℝ) c, g t < b := by
    intro t ht
    rw [← pow_lt_pow_iff_left₀ (hgpos t ht.1).le hb.le hk0, hgpow t ht.1, div_lt_iff₀ ha,
      mul_comm]
    exact ht.2
  have himg : g '' Ioo 0 c = Ioo 0 b := by
    ext u
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨hgpos t ht.1, hgb t ht⟩
    · rintro ⟨hu0, hub⟩
      refine ⟨a * u ^ (2 * k), ⟨by positivity, ?_⟩, ?_⟩
      · exact mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hub hu0.le hk0) ha
      · change (a * u ^ (2 * k) / a) ^ e = u
        rw [mul_div_cancel_left₀ _ ha.ne', hedef, Real.pow_rpow_inv_natCast hu0.le hk0]
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) c,
      HasDerivWithinAt g (e * (t / a) ^ (e - 1) / a) (Ioo 0 c) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ ↦ t / a) (1 / a) t := (hasDerivAt_id t).div_const a
    have h2 := h1.rpow_const (p := e) (Or.inl (div_pos ht.1 ha).ne')
    exact (h2.congr_deriv (by ring)).hasDerivWithinAt
  have hinj : InjOn g (Ioo (0 : ℝ) c) := by
    intro s hs t ht hst
    have := congrArg (· ^ (2 * k)) hst
    simp only [hgpow s hs.1, hgpow t ht.1] at this
    exact (div_left_inj' ha.ne').mp this
  have hF : Measurable fun u : ℝ ↦ a * u ^ (2 * k) := by fun_prop
  have hw : Measurable fun u : ℝ ↦ ENNReal.ofReal (u ^ h) := by fun_prop
  refine Measure.ext_of_lintegral _ fun f hf ↦ ?_
  rw [lintegral_map hf hF,
    lintegral_withDensity_eq_lintegral_mul _ hw (g := fun u ↦ f (a * u ^ (2 * k))) (hf.comp hF),
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun t ↦ ENNReal.ofReal (b ^ (h + 1) / (2 * k) * logPowerDensity lam 0 c t))
      ((measurable_const.mul (measurable_logPowerDensity lam 0 c)).ennreal_ofReal) hf,
    ← Measure.restrict_congr_set Ioo_ae_eq_Icc, ← himg,
    lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioo hderiv hinj]
  have hrhs : (fun t ↦ ENNReal.ofReal (b ^ (h + 1) / (2 * k) * logPowerDensity lam 0 c t)) * f
      = (Ioo 0 c).indicator fun t ↦
          ENNReal.ofReal (b ^ (h + 1) / (2 * k) * (t ^ (lam - 1) * c ^ (-lam))) * f t := by
    funext t
    by_cases ht : t ∈ Ioo 0 c
    · simp [logPowerDensity, indicator_of_mem ht]
    · simp [logPowerDensity, indicator_of_notMem ht]
  rw [hrhs, lintegral_indicator measurableSet_Ioo]
  refine setLIntegral_congr_fun measurableSet_Ioo fun t ht ↦ ?_
  have hta : 0 < t / a := div_pos ht.1 ha
  simp only [Pi.mul_apply]
  rw [show a * g t ^ (2 * k) = t by rw [hgpow t ht.1]; field_simp, ← mul_assoc,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 2
  have hL : e * (t / a) ^ (e - 1) / a * g t ^ h = e / a * (t ^ (lam - 1) / (a ^ lam / a)) := by
    rw [hgdef]
    simp only
    rw [← Real.rpow_mul hta.le,
      show e * (t / a) ^ (e - 1) / a * (t / a) ^ (e * h)
        = e / a * ((t / a) ^ (e - 1) * (t / a) ^ (e * h)) by ring,
      ← Real.rpow_add hta, show e - 1 + e * h = lam - 1 by linear_combination hlam',
      Real.div_rpow ht.1.le ha.le, Real.rpow_sub_one ha.ne']
  have hc' : c ^ (-lam) = (a ^ lam)⁻¹ * (b ^ (h + 1))⁻¹ := by
    rw [hcdef, Real.mul_rpow ha.le (by positivity), ← Real.rpow_natCast b (2 * k),
      ← Real.rpow_mul hb.le, Real.rpow_neg ha.le, mul_neg, h2k, Real.rpow_neg hb.le]
  have hX : 0 < a ^ lam := Real.rpow_pos_of_pos ha _
  have hY : 0 < b ^ (h + 1) := Real.rpow_pos_of_pos hb _
  rw [abs_of_pos (by positivity), hL, hc', hedef]
  push_cast
  field_simp


/-- No thesis counterpart; the calculus behind `mconv_logPowerDensity`:
`∫_a^c (log (c/t))^n / t dt = (log (c/a))^(n+1) / (n+1)` for `0 < a < c`. -/
private theorem integral_log_pow_div_Ioo {a c : ℝ} (n : ℕ) (ha : 0 < a) (hac : a < c) :
    ∫ t in Ioo a c, Real.log (c / t) ^ n / t = Real.log (c / a) ^ (n + 1) / (n + 1) := by
  have hc : 0 < c := ha.trans hac
  have hderiv : ∀ t, 0 < t →
      HasDerivAt (fun t ↦ -Real.log (c / t) ^ (n + 1) / (n + 1))
        (Real.log (c / t) ^ n / t) t := by
    intro t ht0
    have h1 : HasDerivAt (fun t ↦ c / t) (c * -(t ^ 2)⁻¹) t := by
      simpa [div_eq_mul_inv] using (hasDerivAt_inv ht0.ne').const_mul c
    have h2 := (((h1.log (div_pos hc ht0).ne').fun_pow (n + 1)).neg).div_const ((n : ℝ) + 1)
    refine h2.congr_deriv ?_
    simp only [Nat.add_sub_cancel]
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have ht : t ≠ 0 := ht0.ne'
    have hc' : c ≠ 0 := hc.ne'
    push_cast
    field_simp
  have hcont : ContinuousOn (fun t ↦ -Real.log (c / t) ^ (n + 1) / (n + 1)) (Icc a c) :=
    continuousOn_of_forall_continuousAt fun t ht ↦ (hderiv t (ha.trans_le ht.1)).continuousAt
  have hint : IntervalIntegrable (fun t ↦ Real.log (c / t) ^ n / t) volume a c := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hac.le]
    refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
    have ht0 : 0 < t := ha.trans_le ht.1
    exact (((continuousAt_const.div₀ continuousAt_id ht0.ne').log
      (div_pos hc ht0).ne').pow n).div₀ continuousAt_id ht0.ne'
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hac.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac.le hcont
      (fun t ht ↦ hderiv t (ha.trans ht.1)) hint,
    div_self hc.ne', Real.log_one, zero_pow (Nat.succ_ne_zero n)]
  ring

/-- No thesis counterpart; the integrand of the fibre integral in
`mconv_logPowerDensity`, identified as an indicator. -/
private theorem logPowerDensity_mul_div_eq_indicator {lam c₁ c₂ C₁ C₂ p : ℝ} (n : ℕ) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hp : 0 < p) (t : ℝ) :
    C₁ * logPowerDensity lam n c₁ t * |t⁻¹| * (C₂ * logPowerDensity lam 0 c₂ (p / t))
      = (Ioo (p / c₂) c₁).indicator
          (fun t ↦ C₁ * C₂ * p ^ (lam - 1) * (c₁ * c₂) ^ (-lam) / n ! *
            (Real.log (c₁ / t) ^ n / t)) t := by
  unfold logPowerDensity
  by_cases ht : t ∈ Ioo (p / c₂) c₁
  · have ht0 : 0 < t := (div_pos hp hc₂).trans ht.1
    have ht1 : t ∈ Ioo 0 c₁ := ⟨ht0, ht.2⟩
    have ht2 : p / t ∈ Ioo 0 c₂ :=
      ⟨div_pos hp ht0, (div_lt_iff₀ ht0).mpr (by rw [mul_comm]; exact (div_lt_iff₀ hc₂).mp ht.1)⟩
    rw [indicator_of_mem ht, indicator_of_mem ht1, indicator_of_mem ht2,
      abs_of_pos (inv_pos.mpr ht0), Real.div_rpow hp.le ht0.le, Real.mul_rpow hc₁.le hc₂.le]
    have hne : t ^ (lam - 1) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
    have ht' : t ≠ 0 := ht0.ne'
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    field_simp
  · rw [indicator_of_notMem ht]
    by_cases ht1 : t ∈ Ioo 0 c₁
    · have ht0 : 0 < t := ht1.1
      have hle : t ≤ p / c₂ := by
        by_contra h
        exact ht ⟨not_le.mp h, ht1.2⟩
      have ht2 : p / t ∉ Ioo 0 c₂ := fun h ↦
        absurd h.2 (not_lt.mpr ((le_div_iff₀ ht0).mpr
          (by rw [mul_comm]; exact (le_div_iff₀ hc₂).mp hle)))
      rw [indicator_of_notMem ht2]
      ring
    · rw [indicator_of_notMem ht1]
      ring

/-- No thesis counterpart; the fibre integral in `mconv_logPowerDensity`. -/
private theorem lintegral_logPowerDensity_fiber {lam c₁ c₂ C₁ C₂ : ℝ} (n : ℕ) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (p : ℝ) :
    ∫⁻ t, ENNReal.ofReal (C₁ * logPowerDensity lam n c₁ t) * ENNReal.ofReal |t⁻¹| *
        ENNReal.ofReal (C₂ * logPowerDensity lam 0 c₂ (p / t))
      = ENNReal.ofReal (C₁ * C₂ * logPowerDensity lam (n + 1) (c₁ * c₂) p) := by
  have hρ₁ : ∀ t, 0 ≤ C₁ * logPowerDensity lam n c₁ t :=
    fun t ↦ mul_nonneg hC₁ (logPowerDensity_nonneg n hc₁ t)
  have hreal : ∀ t, ENNReal.ofReal (C₁ * logPowerDensity lam n c₁ t) * ENNReal.ofReal |t⁻¹| *
      ENNReal.ofReal (C₂ * logPowerDensity lam 0 c₂ (p / t))
        = ENNReal.ofReal (C₁ * logPowerDensity lam n c₁ t * |t⁻¹| *
            (C₂ * logPowerDensity lam 0 c₂ (p / t))) := by
    intro t
    rw [ENNReal.ofReal_mul (mul_nonneg (hρ₁ t) (abs_nonneg _)), ENNReal.ofReal_mul (hρ₁ t)]
  simp_rw [hreal]
  by_cases hp : p ∈ Ioo 0 (c₁ * c₂)
  · obtain ⟨hp0, hpc⟩ := hp
    set K : ℝ := C₁ * C₂ * p ^ (lam - 1) * (c₁ * c₂) ^ (-lam) / n ! with hK
    have hK0 : 0 ≤ K := by positivity
    have ha : 0 < p / c₂ := div_pos hp0 hc₂
    have hac : p / c₂ < c₁ := (div_lt_iff₀ hc₂).mpr hpc
    have hind : ∀ t, ENNReal.ofReal (C₁ * logPowerDensity lam n c₁ t * |t⁻¹| *
        (C₂ * logPowerDensity lam 0 c₂ (p / t)))
          = (Ioo (p / c₂) c₁).indicator
              (fun t ↦ ENNReal.ofReal (K * (Real.log (c₁ / t) ^ n / t))) t := by
      intro t
      rw [logPowerDensity_mul_div_eq_indicator n hc₁ hc₂ hp0 t]
      by_cases ht : t ∈ Ioo (p / c₂) c₁
      · rw [indicator_of_mem ht, indicator_of_mem ht]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht, ENNReal.ofReal_zero]
    simp_rw [hind]
    rw [lintegral_indicator measurableSet_Ioo]
    have hint : IntegrableOn (fun t ↦ K * (Real.log (c₁ / t) ^ n / t)) (Ioo (p / c₂) c₁) := by
      refine IntegrableOn.mono_set ?_ Ioo_subset_Ioc_self
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hac.le]
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le hac.le]
      refine continuousOn_of_forall_continuousAt fun t ht ↦ ?_
      have ht0 : 0 < t := ha.trans_le ht.1
      exact ((((continuousAt_const.div₀ continuousAt_id ht0.ne').log
        (div_pos hc₁ ht0).ne').pow n).div₀ continuousAt_id ht0.ne').const_mul K
    have hnn : 0 ≤ᵐ[volume.restrict (Ioo (p / c₂) c₁)]
        fun t ↦ K * (Real.log (c₁ / t) ^ n / t) := by
      refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ ?_
      have ht0 : 0 < t := ha.trans ht.1
      have hlog : 0 ≤ Real.log (c₁ / t) := Real.log_nonneg ((one_le_div ht0).mpr ht.2.le)
      simp only [Pi.zero_apply]
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_const_mul,
      integral_log_pow_div_Ioo n ha hac]
    congr 1
    have hlog : c₁ / (p / c₂) = c₁ * c₂ / p := by field_simp
    rw [hlog, hK]
    unfold logPowerDensity
    rw [indicator_of_mem (mem_Ioo.mpr ⟨hp0, hpc⟩), Nat.factorial_succ]
    push_cast
    field_simp
  · have hzero : ∀ t, C₁ * logPowerDensity lam n c₁ t * |t⁻¹| *
        (C₂ * logPowerDensity lam 0 c₂ (p / t)) = 0 := by
      intro t
      unfold logPowerDensity
      by_cases ht1 : t ∈ Ioo 0 c₁
      · have ht0 : 0 < t := ht1.1
        have ht2 : p / t ∉ Ioo 0 c₂ := by
          rintro ⟨h1, h2⟩
          refine hp ⟨?_, ?_⟩
          · have := mul_pos h1 ht0
            rwa [div_mul_cancel₀ _ ht0.ne'] at this
          · rw [div_lt_iff₀ ht0] at h2
            nlinarith [mul_pos hc₂ (sub_pos.mpr ht1.2)]
        rw [indicator_of_notMem ht2]
        ring
      · rw [indicator_of_notMem ht1]
        ring
    simp_rw [hzero, ENNReal.ofReal_zero, lintegral_zero]
    unfold logPowerDensity
    rw [indicator_of_notMem hp, mul_zero, ENNReal.ofReal_zero]

/-- The inductive step of [Wat09, Theorem 4.6]: the multiplicative convolution of
`C₁ t^{λ-1} c₁^{-λ} (log (c₁/t))^n / n!` on `(0, c₁)` with `C₂ s^{λ-1} c₂^{-λ}` on
`(0, c₂)` is `C₁ C₂ p^{λ-1} (c₁ c₂)^{-λ} (log (c₁ c₂ / p))^{n+1} / (n+1)!` on
`(0, c₁ c₂)`.

No thesis counterpart: this replaces [Hit26]'s Mellin-inversion argument. -/
private theorem mconv_logPowerDensity {lam c₁ c₂ C₁ C₂ : ℝ} (n : ℕ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) :
    (volume.withDensity fun t ↦ ENNReal.ofReal (C₁ * logPowerDensity lam n c₁ t)) ∗ₘ
        (volume.withDensity fun s ↦ ENNReal.ofReal (C₂ * logPowerDensity lam 0 c₂ s))
      = volume.withDensity fun p ↦
          ENNReal.ofReal (C₁ * C₂ * logPowerDensity lam (n + 1) (c₁ * c₂) p) := by
  set ρ₁ : ℝ → ENNReal := fun t ↦ ENNReal.ofReal (C₁ * logPowerDensity lam n c₁ t) with hρ₁
  set ρ₂ : ℝ → ENNReal := fun s ↦ ENNReal.ofReal (C₂ * logPowerDensity lam 0 c₂ s) with hρ₂
  set ρ₃ : ℝ → ENNReal := fun p ↦ ENNReal.ofReal (C₁ * C₂ * logPowerDensity lam (n + 1) (c₁ * c₂) p)
    with hρ₃
  have hm₁ : Measurable ρ₁ := ((measurable_logPowerDensity lam n c₁).const_mul C₁).ennreal_ofReal
  have hm₂ : Measurable ρ₂ := ((measurable_logPowerDensity lam 0 c₂).const_mul C₂).ennreal_ofReal
  have hm₃ : Measurable ρ₃ :=
    ((measurable_logPowerDensity lam (n + 1) (c₁ * c₂)).const_mul (C₁ * C₂)).ennreal_ofReal
  refine Measure.ext_of_lintegral _ fun g hg ↦ ?_
  rw [Measure.lintegral_mconv_eq_lintegral_prod hg, prod_withDensity hm₁ hm₂,
    lintegral_withDensity_eq_lintegral_mul _ (by fun_prop)
      (show Measurable fun z : ℝ × ℝ ↦ g (z.1 * z.2) from hg.comp measurable_mul),
    lintegral_withDensity_eq_lintegral_mul _ hm₃ hg, lintegral_prod _ (by fun_prop)]
  simp only [Pi.mul_apply]
  have hfiber : ∀ t, ∫⁻ s, ρ₁ t * ρ₂ s * g (t * s)
      = ∫⁻ p, ρ₁ t * ENNReal.ofReal |t⁻¹| * ρ₂ (p / t) * g p := by
    intro t
    by_cases ht : 0 < t
    · have hH : Measurable fun p ↦ ρ₂ (p / t) * g p :=
        (hm₂.comp (measurable_id.div_const t)).mul hg
      have hsub : ∫⁻ s, ρ₂ s * g (t * s) = ENNReal.ofReal |t⁻¹| * ∫⁻ p, ρ₂ (p / t) * g p := by
        have := lintegral_map (μ := volume) hH (measurable_const_mul t)
        rw [Real.map_volume_mul_left ht.ne', lintegral_smul_measure, smul_eq_mul] at this
        rw [this]
        refine lintegral_congr fun s ↦ ?_
        simp only [mul_div_cancel_left₀ s ht.ne']
      calc ∫⁻ s, ρ₁ t * ρ₂ s * g (t * s)
          = ρ₁ t * ∫⁻ s, ρ₂ s * g (t * s) := by
            simp_rw [mul_assoc]
            exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = ρ₁ t * (ENNReal.ofReal |t⁻¹| * ∫⁻ p, ρ₂ (p / t) * g p) := by rw [hsub]
        _ = ∫⁻ p, ρ₁ t * ENNReal.ofReal |t⁻¹| * ρ₂ (p / t) * g p := by
            symm
            simp_rw [mul_assoc]
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    · have h0 : ρ₁ t = 0 := by
        rw [hρ₁]
        simp only
        unfold logPowerDensity
        rw [indicator_of_notMem (fun h ↦ ht h.1), mul_zero, ENNReal.ofReal_zero]
      simp [h0]
  simp_rw [hfiber]
  have hmeas : Measurable (Function.uncurry fun t p ↦
      ρ₁ t * ENNReal.ofReal |t⁻¹| * ρ₂ (p / t) * g p) :=
    (((hm₁.comp measurable_fst).mul (measurable_fst.inv.abs.ennreal_ofReal)).mul
      (hm₂.comp (measurable_snd.div measurable_fst))).mul (hg.comp measurable_snd)
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  refine lintegral_congr fun p ↦ ?_
  rw [lintegral_mul_const _ (show Measurable fun x : ℝ ↦ ρ₁ x * ENNReal.ofReal |x⁻¹| * ρ₂ (p / x)
    from (hm₁.mul (measurable_inv.abs.ennreal_ofReal)).mul
      (hm₂.comp (measurable_const.div measurable_id)))]
  exact congrArg (· * g p) (lintegral_logPowerDensity_fiber n hc₁ hc₂ hC₁ hC₂ p)



/-- Pushing a measure with density along a measurable equivalence transports the
density along the inverse. No thesis counterpart; used to move between
`Fin (n+1) → ℝ` and `ℝ × (Fin n → ℝ)`. -/
private theorem map_withDensity_equiv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (e : α ≃ᵐ β) (μ : Measure α) (f : α → ENNReal) :
    Measure.map e (μ.withDensity f) = (Measure.map e μ).withDensity (f ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs, withDensity_apply _ (e.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.measurable hs, lintegral_map_equiv]
  refine lintegral_congr fun x ↦ ?_
  simp

/-- The pushforward of a product measure along a product of two functions is the
multiplicative convolution of the two pushforwards. No thesis counterpart; this is
how a new coordinate enters the state density measure of a monomial. -/
private theorem map_mul_prod_eq_mconv {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν] {K₁ : α → ℝ} {K₂ : β → ℝ}
    (h₁ : Measurable K₁) (h₂ : Measurable K₂) :
    Measure.map (fun z : α × β ↦ K₁ z.1 * K₂ z.2) (μ.prod ν)
      = (Measure.map K₁ μ) ∗ₘ (Measure.map K₂ ν) := by
  rw [Measure.mconv, Measure.map_prod_map _ _ h₁ h₂,
    Measure.map_map measurable_mul (h₁.prodMap h₂)]
  rfl

/-- On the cube every coordinate is nonnegative, so the weight `u^h` may be read as
a product of `ENNReal` factors. No thesis counterpart. -/
theorem withDensity_cube_prod {n : ℕ} {b : ℝ} (h : Fin n → ℝ) :
    (volume.restrict (cube n b)).withDensity
        (fun u ↦ ENNReal.ofReal (∏ j, u j ^ h j))
      = (volume.restrict (cube n b)).withDensity
        (fun u ↦ ∏ j, ENNReal.ofReal (u j ^ h j)) := by
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact ENNReal.ofReal_prod_of_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _

/-- Splitting off the first coordinate of the weighted cube `u^h du` on `[0, b]^(n+1)`
gives the product of the weighted interval `x^{h₀} dx` on `[0, b]` with the weighted
cube on `[0, b]^n`. No thesis counterpart. -/
private theorem map_piFinSuccAbove_cube {n : ℕ} {b : ℝ} (h : Fin (n + 1) → ℝ) :
    Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0)
        ((volume.restrict (cube (n + 1) b)).withDensity
          fun u ↦ ∏ j, ENNReal.ofReal (u j ^ h j))
      = ((volume.restrict (Icc 0 b)).withDensity fun x ↦ ENNReal.ofReal (x ^ h 0)).prod
          ((volume.restrict (cube n b)).withDensity
            fun y ↦ ∏ j, ENNReal.ofReal (y j ^ h (Fin.succ j))) := by
  have hμ : Measure.map (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) 0)
      (volume.restrict (cube (n + 1) b))
      = (volume.restrict (Icc 0 b)).prod
          (volume.restrict (cube n b)) := by
    simp only [cube_eq_pi]
    rw [volume_pi, Measure.restrict_pi_pi,
      (measurePreserving_piFinSuccAbove (fun _ ↦ volume.restrict (Icc 0 b)) 0).map_eq,
      volume_pi, Measure.restrict_pi_pi]
  rw [map_withDensity_equiv, hμ, prod_withDensity (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ,
    Fin.insertNth_zero']

/-- Push a measure through a measurable equivalence and back. No thesis counterpart. -/
private theorem map_eq_map_comp_symm {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (e : α ≃ᵐ β) {K : α → γ} (hK : Measurable K) (μ : Measure α) :
    Measure.map K μ = Measure.map (K ∘ e.symm) (Measure.map e μ) := by
  rw [← Measure.map_map hK e.symm.measurable, MeasurableEquiv.map_symm_map]

theorem NormalCrossing.measurable_monomial {n : ℕ} (k : Fin n → ℕ) (a : ℝ) :
    Measurable fun u : Fin n → ℝ ↦ a * ∏ j, u j ^ (2 * k j) :=
  (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _).const_mul a

open SingularLearningTheory.NormalCrossing

/-- [Hit26, Lemma 3.2.3] ([Wat09, Theorem 4.6]), as an identity of
measures: the state density measure of `F(u) = a u^{2k}` on `[0, b]^(n+1)` against
`u^h` is `(∏ b^(h_j+1) / (2 k_j)) · logPowerDensity λ n (a b^{2|k|})`. See
`isStateDensity_monomial_cube` for [Hit26]'s form of the density.

[Hit26]'s hypothesis `h_j > -1` is not needed for the identity of measures (only
for their finiteness) and is omitted. Induction on the number of coordinates: the
first coordinate is `map_monomial_one_dim`, the rest is the induction hypothesis with
`a = 1`, and `mconv_logPowerDensity` combines the two. -/
theorem stateDensityMeasure_monomial_cube {n : ℕ} {k : Fin (n + 1) → ℕ} {h : Fin (n + 1) → ℝ}
    {lam a b : ℝ} (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (ha : 0 < a) (hb : 0 < b) :
    stateDensityMeasure (fun u ↦ a * ∏ j, u j ^ (2 * k j)) (fun u ↦ ∏ j, u j ^ h j)
        (cube (n + 1) b)
      = volume.withDensity fun t ↦ ENNReal.ofReal ((∏ j, b ^ (h j + 1) / (2 * k j)) *
          logPowerDensity lam n (a * b ^ (2 * ∑ j, k j)) t) := by
  induction n generalizing a with
  | zero =>
    have hμ : Measure.map (MeasurableEquiv.funUnique (Fin 1) ℝ)
          (volume.restrict (cube 1 b))
        = volume.restrict (Icc 0 b) := by
      rw [cube_eq_pi, volume_pi, Measure.restrict_pi_pi]
      exact (measurePreserving_funUnique (volume.restrict (Icc 0 b)) (Fin 1)).map_eq
    rw [stateDensityMeasure, withDensity_cube_prod,
      map_eq_map_comp_symm (MeasurableEquiv.funUnique (Fin 1) ℝ)
          (NormalCrossing.measurable_monomial k a),
      map_withDensity_equiv, hμ]
    have hK : ((fun u : Fin 1 → ℝ ↦ a * ∏ j, u j ^ (2 * k j)) ∘
          (MeasurableEquiv.funUnique (Fin 1) ℝ).symm) = fun x ↦ a * x ^ (2 * k 0) := by
      funext x; simp
    have hφ : ((fun u : Fin 1 → ℝ ↦ ∏ j, ENNReal.ofReal (u j ^ h j)) ∘
          (MeasurableEquiv.funUnique (Fin 1) ℝ).symm) = fun x ↦ ENNReal.ofReal (x ^ h 0) := by
      funext x; simp
    rw [hK, hφ, map_monomial_one_dim ha hb (hk 0) (hlam 0)]
    simp
  | succ n ih =>
    rw [stateDensityMeasure, withDensity_cube_prod,
      map_eq_map_comp_symm (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) ↦ ℝ) 0)
        (NormalCrossing.measurable_monomial k a), map_piFinSuccAbove_cube]
    have hK : ((fun u : Fin (n + 2) → ℝ ↦ a * ∏ j, u j ^ (2 * k j)) ∘
          (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) ↦ ℝ) 0).symm)
        = fun z : ℝ × (Fin (n + 1) → ℝ) ↦
            (a * z.1 ^ (2 * k 0)) * ∏ j, z.2 j ^ (2 * k (Fin.succ j)) := by
      funext z
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv, Fin.prod_univ_succ,
        Fin.insertNth_zero', mul_assoc]
    have ih' := ih (k := fun j ↦ k (Fin.succ j)) (h := fun j ↦ h (Fin.succ j))
      (fun j ↦ hk _) (fun j ↦ hlam _) one_pos
    rw [stateDensityMeasure, withDensity_cube_prod] at ih'
    simp only [one_mul] at ih'
    have hK₁ : Measurable fun x : ℝ ↦ a * x ^ (2 * k 0) := by fun_prop
    have hK₂ : Measurable fun y : Fin (n + 1) → ℝ ↦ ∏ j, y j ^ (2 * k (Fin.succ j)) :=
      Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
    rw [hK, map_mul_prod_eq_mconv (K₁ := fun x : ℝ ↦ a * x ^ (2 * k 0))
      (K₂ := fun y : Fin (n + 1) → ℝ ↦ ∏ j, y j ^ (2 * k (Fin.succ j))) _ _ hK₁ hK₂,
      map_monomial_one_dim ha hb (hk 0) (hlam 0), ih', Measure.mconv_comm,
      mconv_logPowerDensity n (by positivity) (by positivity) (by positivity) (by positivity)]
    congr 1
    funext t
    rw [Fin.prod_univ_succ (f := fun j ↦ b ^ (h j + 1) / (2 * k j)), Fin.sum_univ_succ (f := k)]
    rw [show b ^ (2 * ∑ x : Fin (n + 1), k x.succ) * (a * b ^ (2 * k 0))
        = a * b ^ (2 * (k 0 + ∑ i : Fin (n + 1), k i.succ)) by ring]
    congr 2
    ring


/-- The constant `γ_b` of [Hit26, Lemma 3.2.3]:
`γ_b = b^(|h| + m - 2|k|λ) / (2^m (m-1)! k₁ ⋯ k_m)`, with `m` the number of coordinates, for
real
exponents `h`. On the critical coordinates of `SingularLearningTheory.normalCrossing`
the power of `b` is `1`, and the constant is `SingularLearningTheory.gammaConst`. -/
@[expose] noncomputable def NormalCrossing.gammaConst {m : ℕ} (k : Fin m → ℕ) (h : Fin m → ℝ)
    (lam b : ℝ) : ℝ :=
  b ^ ((∑ j, h j) + m - 2 * (∑ j, k j) * lam) / (2 ^ m * (m - 1)! * ∏ j, (k j : ℝ))

/-- The two ways of writing the constant in [Wat09, Theorem 4.6] agree:
`(∏ b^(h_j+1) / (2 k_j)) · c^{-λ} / n! = γ_b / a^λ` for `c = a b^{2|k|}` and `m = n + 1`. -/
private theorem NormalCrossing.prod_div_mul_rpow_neg_eq_gammaConst {n : ℕ} {k : Fin
    (n + 1) → ℕ}
    {h : Fin (n + 1) → ℝ}
    {lam a b : ℝ} (hk : ∀ j, 0 < k j) (ha : 0 < a) (hb : 0 < b) :
    (∏ j, b ^ (h j + 1) / (2 * k j)) * (a * b ^ (2 * ∑ j, k j)) ^ (-lam) / n !
      = NormalCrossing.gammaConst k h lam b / a ^ lam := by
  have hprod : (∏ j, b ^ (h j + 1) / (2 * (k j : ℝ)))
      = b ^ ((∑ j, h j) + (n + 1 : ℕ)) / (2 ^ (n + 1) * ∏ j, (k j : ℝ)) := by
    rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_fin,
      ← Real.rpow_sum_of_pos hb, Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin]
    simp
  rw [hprod, NormalCrossing.gammaConst, Real.mul_rpow ha.le (by positivity), ← Real.rpow_natCast b,
    ← Real.rpow_mul hb.le, Real.rpow_neg ha.le, mul_neg, Real.rpow_neg hb.le,
    show ((∑ j, h j) + (n + 1 : ℕ) - 2 * (∑ j, k j) * lam)
      = ((∑ j, h j) + (n + 1 : ℕ)) + -(((2 * ∑ j, k j : ℕ) : ℝ) * lam) by push_cast; ring,
    Real.rpow_add hb ((∑ j, h j) + (n + 1 : ℕ)) (-(((2 * ∑ j, k j : ℕ) : ℝ) * lam)),
    Real.rpow_neg hb.le, Nat.succ_sub_one]
  have hk' : (0 : ℝ) < ∏ j, (k j : ℝ) := Finset.prod_pos fun j _ ↦ by exact_mod_cast hk j
  have hb1 : (0 : ℝ) < b ^ ((∑ j, h j) + (n + 1 : ℕ)) := Real.rpow_pos_of_pos hb _
  have hb2 : (0 : ℝ) < b ^ (((2 * ∑ j, k j : ℕ) : ℝ) * lam) := Real.rpow_pos_of_pos hb _
  have ha1 : (0 : ℝ) < a ^ lam := Real.rpow_pos_of_pos ha _
  field_simp

/-- [Hit26, Lemma 3.2.3] ([Wat09, Theorem 4.6]), in [Hit26]'s form:
the state density function of `F(u) = a u^{2k}` on `[0, b]^m` against `u^h` is

    ν(t) = γ_b · t^{λ-1} / a^λ · (log (a b^{2|k|} / t))^{m-1}    for 0 < t < a b^{2|k|},

and `0` otherwise, where `γ_b = b^(|h| + m - 2|k|λ) / (2^m (m-1)! k₁ ⋯ k_m)` and
`m = n + 1` is the number of coordinates. [Hit26]'s `h_j > -1` is only needed for
finiteness and is omitted; `IsStateDensity` is an identity of measures. -/
private theorem isStateDensity_monomial_cube {n : ℕ} {k : Fin (n + 1) → ℕ} {h : Fin (n + 1) → ℝ}
    {lam a b : ℝ} (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (ha : 0 < a) (hb : 0 < b) :
    IsStateDensity (fun u ↦ a * ∏ j, u j ^ (2 * k j)) (fun u ↦ ∏ j, u j ^ h j)
      (cube (n + 1) b)
      ((Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator fun t ↦
        NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
          Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ n) := by
  have hc : 0 < a * b ^ (2 * ∑ j, k j) := by positivity
  have hγ : 0 ≤ NormalCrossing.gammaConst k h lam b := by
    unfold NormalCrossing.gammaConst
    have : (0 : ℝ) < ∏ j, (k j : ℝ) := Finset.prod_pos fun j _ ↦ by exact_mod_cast hk j
    positivity
  have hpt : ∀ t, (∏ j, b ^ (h j + 1) / (2 * k j)) *
        logPowerDensity lam n (a * b ^ (2 * ∑ j, k j)) t
      = (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator (fun t ↦
          NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
            Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ n) t := by
    intro t
    unfold logPowerDensity
    by_cases ht : t ∈ Ioo 0 (a * b ^ (2 * ∑ j, k j))
    · rw [indicator_of_mem ht, indicator_of_mem ht,
        show NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
            Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ n
          = NormalCrossing.gammaConst k h lam b / a ^ lam *
            (t ^ (lam - 1) * Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ n) by ring,
        ← prod_div_mul_rpow_neg_eq_gammaConst hk ha hb]
      ring
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, mul_zero]
  refine ⟨?_, ?_, ?_⟩
  · exact Measurable.indicator (by fun_prop) measurableSet_Ioo
  · intro t
    refine indicator_nonneg (fun t ht ↦ ?_) t
    obtain ⟨ht0, htc⟩ := ht
    have hlog : 0 ≤ Real.log (a * b ^ (2 * ∑ j, k j) / t) :=
      Real.log_nonneg ((one_le_div ht0).mpr htc.le)
    have ha' : 0 < a ^ lam := Real.rpow_pos_of_pos ha _
    positivity
  · rw [stateDensityMeasure_monomial_cube hk hlam ha hb]
    exact withDensity_congr_ae (.of_forall fun t ↦ congrArg ENNReal.ofReal (hpt t))

/-! ## [Wat09, Theorem 4.7]: the asymptotics of `Z^p(n)` for a normal crossing potential

[Hit26, Section 3.2]. The coordinates are
split into `m = r + 1 ≥ 1` *primary* coordinates `u`, on which `(h_j + 1)/(2 k_j) = λ`,
and `m' ≥ 0` *secondary* coordinates `v`, on which `2 k'_j λ < h'_j + 1`. [Hit26]
takes `k', h' ∈ ℕ^{m'}` and writes the secondary condition as
`λ < (h'_j + 1)/(2 k'_j)`; the form used here is equivalent when `k'_j ≥ 1` and also
covers `k'_j = 0` (where it reads `h'_j > -1`).

[Hit26] states [Wat09, Theorem 4.7] "for any `n > 1`". The upper bound is false for
`1 < n < 2` when `m ≥ 2` (`Z^p(n) → Z^p(1) > 0` while `(log n)^{m-1} → 0`), so it is
stated for `n ≥ 2` here; the lower bound holds for all `n > 1`. -/

/-- The normal crossing potential `K(u, v) = u^{2k} v^{2k'}`:
`SingularLearningTheory.normalCrossing` in block coordinates, the critical
coordinates `u` and the others `v`. -/
@[expose] def NormalCrossing.potential {m m' : ℕ} (k : Fin m → ℕ) (k' : Fin m' → ℕ)
    (z : (Fin m → ℝ) × (Fin m' → ℝ)) : ℝ :=
  (∏ j, z.1 j ^ (2 * k j)) * ∏ j, z.2 j ^ (2 * k' j)

/-- The weight `u^h v^{h'}` with real exponents: `SingularLearningTheory.monomialWeight`
in block coordinates. -/
@[expose] noncomputable def NormalCrossing.monomialWeight {m m' : ℕ} (h : Fin m → ℝ)
    (h' : Fin m' → ℝ)
    (z : (Fin m → ℝ) × (Fin m' → ℝ)) : ℝ :=
  (∏ j, z.1 j ^ h j) * ∏ j, z.2 j ^ h' j

/-- [Hit26, Equation (3.2.1)]:

    Z^p(n) = ∫_{[0,b]^{m+m'}} K(u, v)^p e^{-nβK(u, v)} u^h v^{h'} du dv.

`SingularLearningTheory.normalCrossingIntegral₀` in block coordinates, with real exponents.
-/
@[expose] noncomputable def NormalCrossing.blockIntegral₀ {m m' : ℕ} (k : Fin m → ℕ) (h : Fin m → ℝ)
    (k' : Fin m' → ℕ) (h' : Fin m' → ℝ) (b β p n : ℝ) : ℝ :=
  ∫ z in cube m b ×ˢ cube m' b,
    potential k k' z ^ p * Real.exp (-(n * β * potential k k' z)) *
      NormalCrossing.monomialWeight h h' z

section GBTheorem47

variable {r m' : ℕ} {k : Fin (r + 1) → ℕ} {h : Fin (r + 1) → ℝ} {k' : Fin m' → ℕ}
  {h' : Fin m' → ℝ} {lam b β p : ℝ}

/-- [Wat09, Theorem 4.4] combined with [Wat09, Theorem 4.6]: an integral of a function of `a u^{2k}`
over the cube against `u^h` is an integral over `(0, ∞)` against the explicit state density.
No thesis counterpart as a single statement; this is how every integral in the proofs
of [Wat09, Theorems 4.7–4.9] is evaluated. -/
theorem integral_cube_monomial {a : ℝ} (hk : ∀ j, 0 < k j)
    (hlam : ∀ j, (h j + 1) / (2 * k j) = lam) (ha : 0 < a) (hb : 0 < b) {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f volume)
    (hint : Integrable fun t ↦ f t * (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
      (fun t ↦ NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
        Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r) t) :
    ∫ u in cube (r + 1) b, f (a * ∏ j, u j ^ (2 * k j)) * ∏ j, u j ^ h j
      = ∫ t in Ioi 0, f t * (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
          (fun t ↦ NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
            Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r) t := by
  have hsd := isStateDensity_monomial_cube hk hlam ha hb
  have hK : Measurable fun u : Fin (r + 1) → ℝ ↦ a * ∏ j, u j ^ (2 * k j) :=
    NormalCrossing.measurable_monomial k a
  have hφ : AEMeasurable (fun u : Fin (r + 1) → ℝ ↦ ∏ j, u j ^ h j)
      (volume.restrict (cube (r + 1) b)) :=
    (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _).aemeasurable
  have hφ0 : 0 ≤ᵐ[volume.restrict (cube (r + 1) b)] fun u : Fin (r + 1) → ℝ ↦ ∏ j, u j ^ h j := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _
  have hK0 : ∀ u ∈ cube (r + 1) b, 0 ≤ a * ∏ j, u j ^ (2 * k j) := fun u hu ↦
    mul_nonneg ha.le (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu.1 j) _)
  exact (IsStateDensity.setIntegral_mul hsd hK hφ hφ0 hK0 hf hint).symm

/-- No thesis counterpart. Pulling `exp (-t)` inside the indicator turns the integral over
`(0, ∞)` of `exp (-t) * 𝟙_{(0, c)} g` into the integral of `exp (-t) * g` over `(0, c)`. -/
private theorem integral_exp_neg_mul_indicator_Ioo (c : ℝ) (g : ℝ → ℝ) :
    ∫ t in Ioi 0, Real.exp (-t) * (Ioo 0 c).indicator g t
      = ∫ t in Ioo 0 c, Real.exp (-t) * g t := by
  have h : ∀ t, Real.exp (-t) * (Ioo 0 c).indicator g t
      = (Ioo 0 c).indicator (fun t ↦ Real.exp (-t) * g t) t :=
    fun t ↦ (Set.indicator_mul_right (Ioo 0 c) (fun t ↦ Real.exp (-t)) g).symm
  simp_rw [h]
  rw [setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.mpr Ioo_subset_Ioi_self]

/-- No thesis counterpart. On `(0, c)`, `log (c / t) ≥ 0`. -/
theorem _root_.Real.log_div_nonneg_of_mem_Ioo {c t : ℝ} (ht : t ∈ Ioo 0 c) : 0 ≤ Real.log (c / t) :=
  Real.log_nonneg ((one_le_div ht.1).mpr ht.2.le)

/-- `t^(s-1) (log (c/t))^r` is integrable on `(0, c)` for `s > 0`. No thesis counterpart. -/
theorem _root_.integrableOn_rpow_mul_log_pow_Ioo {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (r : ℕ) :
    IntegrableOn (fun t ↦ t ^ (s - 1) * Real.log (c / t) ^ r) (Ioo 0 c) := by
  have hg : IntegrableOn (fun t : ℝ ↦ Real.exp c *
      (t ^ (s - 1) * Real.exp (-t) * |Real.log (c / t)| ^ r)) (Ioo 0 c) :=
    ((integrableOn_rpow_mul_exp_neg_mul_abs_log_div_pow hs hc r).mono_set
      Ioo_subset_Ioi_self).const_mul _
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      t ^ (s - 1) * Real.log (c / t) ^ r).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    have hlog := Real.log_div_nonneg_of_mem_Ioo ht
    obtain ⟨ht0, htc⟩ := ht
    have hX : 0 ≤ t ^ (s - 1) * Real.log (c / t) ^ r :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (pow_nonneg hlog r)
    rw [Real.norm_eq_abs, abs_of_nonneg hX, abs_of_nonneg hlog]
    have h1 : 1 ≤ Real.exp c * Real.exp (-t) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    calc t ^ (s - 1) * Real.log (c / t) ^ r
        = 1 * (t ^ (s - 1) * Real.log (c / t) ^ r) := (one_mul _).symm
      _ ≤ (Real.exp c * Real.exp (-t)) * (t ^ (s - 1) * Real.log (c / t) ^ r) :=
          mul_le_mul_of_nonneg_right h1 hX
      _ = _ := by ring

/-- On the open cube, `(u^{2k})^p u^h = u^{h + 2kp}`. No thesis counterpart. Positivity of
`u` is needed: at `u_j = 0` with `h_j + 2 k_j p = 0 ≠ h_j` the two sides differ. -/
theorem _root_.Real.prod_pow_rpow_mul_prod_rpow {m : ℕ} (k : Fin m → ℕ) (h : Fin m → ℝ) (p : ℝ)
    {u : Fin m → ℝ} (hu : ∀ j, 0 < u j) :
    (∏ j, u j ^ (2 * k j)) ^ p * ∏ j, u j ^ h j = ∏ j, u j ^ (h j + 2 * k j * p) := by
  rw [← Real.finsetProd_rpow _ _ (fun j _ ↦ pow_nonneg (hu j).le _), ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [Real.rpow_add (hu j), ← Real.rpow_natCast, ← Real.rpow_mul (hu j).le, mul_comm]
  push_cast
  ring_nf

/-- The weight `v^μ` integrates to a positive finite constant over the cube when every
`μ_j > -1`. No thesis counterpart. -/
theorem integral_cube_rpow {m : ℕ} {μ : Fin m → ℝ} (hμ : ∀ j, -1 < μ j) (hb : 0 < b) :
    ∫ v in cube m b, ∏ j, v j ^ μ j = ∏ j, b ^ (μ j + 1) / (μ j + 1) := by
  rw [cube_eq_pi, volume_pi, Measure.restrict_pi_pi,
    integral_fintype_prod_eq_prod (fun j (x : ℝ) ↦ x ^ μ j)]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb.le,
    integral_rpow (Or.inl (hμ j)), Real.zero_rpow (by linarith [hμ j]), sub_zero]

theorem integrableOn_cube_rpow {m : ℕ} {μ : Fin m → ℝ} (hμ : ∀ j, -1 < μ j) (hb : 0 < b) :
    IntegrableOn (fun v : Fin m → ℝ ↦ ∏ j, v j ^ μ j) (cube m b) := by
  rw [IntegrableOn, cube_eq_pi, volume_pi, Measure.restrict_pi_pi]
  refine Integrable.fintype_prod (f := fun j (x : ℝ) ↦ x ^ μ j) fun j ↦ ?_
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hb.le).mp
    (intervalIntegral.intervalIntegrable_rpow' (hμ j))

/-- No thesis counterpart. The integrand of `lower_bound_core` with `exp (-t)` inside the
indicator is nonnegative and integrable on `(0, c)`. -/
private theorem integrableOn_exp_neg_mul_rpow_mul_log_pow_Ioo {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (r : ℕ) :
    IntegrableOn (fun t ↦ Real.exp (-t) * (t ^ (s - 1) * Real.log (c / t) ^ r)) (Ioo 0 c) := by
  refine (integrableOn_rpow_mul_log_pow_Ioo hs hc r).mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      Real.exp (-t) * (t ^ (s - 1) * Real.log (c / t) ^ r)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioo]
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    have hlog := Real.log_div_nonneg_of_mem_Ioo ht
    obtain ⟨ht0, _⟩ := ht
    have hX : 0 ≤ t ^ (s - 1) * Real.log (c / t) ^ r :=
      mul_nonneg (Real.rpow_nonneg ht0.le _) (pow_nonneg hlog r)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le hX)]
    exact mul_le_of_le_one_left hX (Real.exp_le_one_iff.mpr (by linarith))

/-- The `t`-integral behind the lower bound of [Wat09, Theorem 4.7]: restricting to `t < c₀`, where
`log (n c₀ / t) ≥ log n`, gives a factor `(log n)^r`. No thesis counterpart. -/
private theorem lower_bound_core {s c₀ n : ℝ} (hs : 0 < s) (hc₀ : 0 < c₀) (hn : 1 < n) (r : ℕ) :
    Real.log n ^ r * ∫ t in Ioo 0 c₀, Real.exp (-t) * t ^ (s - 1)
      ≤ ∫ t in Ioi 0, Real.exp (-t) *
          (Ioo 0 (n * c₀)).indicator (fun t ↦ t ^ (s - 1) * Real.log (n * c₀ / t) ^ r) t := by
  have hn0 : 0 < n := by linarith
  have hnc : 0 < n * c₀ := by positivity
  have hsub : Ioo 0 c₀ ⊆ Ioo 0 (n * c₀) :=
    Ioo_subset_Ioo_right (le_mul_of_one_le_left hc₀.le hn.le)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg hn.le
  have hint := integrableOn_exp_neg_mul_rpow_mul_log_pow_Ioo hs hnc r
  have hnonneg : ∀ t ∈ Ioo 0 (n * c₀),
      0 ≤ Real.exp (-t) * (t ^ (s - 1) * Real.log (n * c₀ / t) ^ r) := fun t ht ↦
    mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (pow_nonneg (Real.log_div_nonneg_of_mem_Ioo ht) r))
  rw [integral_exp_neg_mul_indicator_Ioo, ← integral_const_mul]
  calc ∫ t in Ioo 0 c₀, Real.log n ^ r * (Real.exp (-t) * t ^ (s - 1))
      ≤ ∫ t in Ioo 0 c₀, Real.exp (-t) * (t ^ (s - 1) * Real.log (n * c₀ / t) ^ r) := by
        refine setIntegral_mono_on
          (((Real.GammaIntegral_convergent hs).mono_set Ioo_subset_Ioi_self).const_mul _)
          (hint.mono_set hsub) measurableSet_Ioo fun t ht ↦ ?_
        obtain ⟨ht0, htc⟩ := ht
        have hlog : Real.log n ≤ Real.log (n * c₀ / t) := by
          rw [mul_div_assoc, Real.log_mul hn0.ne' (div_pos hc₀ ht0).ne']
          linarith [Real.log_nonneg ((one_le_div ht0).mpr htc.le)]
        have hX : 0 ≤ Real.exp (-t) * t ^ (s - 1) :=
          mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg ht0.le _)
        calc Real.log n ^ r * (Real.exp (-t) * t ^ (s - 1))
            ≤ Real.log (n * c₀ / t) ^ r * (Real.exp (-t) * t ^ (s - 1)) :=
              mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hlogn hlog r) hX
          _ = _ := by ring
    _ ≤ _ :=
        setIntegral_mono_set hint
          ((ae_restrict_iff' measurableSet_Ioo).mpr (Filter.Eventually.of_forall hnonneg))
          hsub.eventuallyLE

/-- The `t`-integral behind the upper bound of [Wat09, Theorem 4.7]: for `0 < c ≤ n c₀` and `n ≥ 2`,
`log (c/t) ≤ log n + |log (c₀/t)|` on `(0, c)`, and the resulting integral is
`O((log n)^r)` with a constant independent of `c` and `n`. No thesis counterpart. -/
private theorem upper_bound_core {s c₀ : ℝ} (hs : 0 < s) (hc₀ : 0 < c₀) (r : ℕ) :
    ∃ A > 0, ∀ n c : ℝ, 2 ≤ n → 0 < c → c ≤ n * c₀ →
      ∫ t in Ioi 0, Real.exp (-t) *
          (Ioo 0 c).indicator (fun t ↦ t ^ (s - 1) * Real.log (c / t) ^ r) t
        ≤ A * Real.log n ^ r := by
  set G : ℝ := ∫ t in Ioi 0, Real.exp (-t) * t ^ (s - 1) with hG
  set L : ℝ := ∫ t in Ioi 0, t ^ (s - 1) * Real.exp (-t) * |Real.log (c₀ / t)| ^ r with hL
  have hGpos : 0 < G := by
    rw [hG, ← Real.Gamma_eq_integral hs]
    exact Real.Gamma_pos_of_pos hs
  have hL0 : 0 ≤ L := setIntegral_nonneg measurableSet_Ioi fun t ht ↦ by
    have ht : 0 < t := ht
    positivity
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hGint := Real.GammaIntegral_convergent hs
  have hLint := integrableOn_rpow_mul_exp_neg_mul_abs_log_div_pow hs hc₀ r
  refine ⟨2 ^ r * G + 2 ^ r * L / Real.log 2 ^ r, by positivity, ?_⟩
  intro n c hn hc hcn
  have hn0 : 0 < n := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hratio : L ≤ L / Real.log 2 ^ r * Real.log n ^ r := by
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog2.le hlog2n r) hL0
  have hdom : ∀ t ∈ Ioi (0 : ℝ),
      Real.exp (-t) * (Ioo 0 c).indicator (fun t ↦ t ^ (s - 1) * Real.log (c / t) ^ r) t
        ≤ 2 ^ r * Real.log n ^ r * (Real.exp (-t) * t ^ (s - 1))
          + 2 ^ r * (t ^ (s - 1) * Real.exp (-t) * |Real.log (c₀ / t)| ^ r) := by
    intro t ht
    have ht : 0 < t := ht
    by_cases htc : t ∈ Ioo 0 c
    · rw [indicator_of_mem htc]
      have hlog0 := Real.log_div_nonneg_of_mem_Ioo htc
      have hlog : Real.log (c / t) ≤ Real.log n + |Real.log (c₀ / t)| := by
        calc Real.log (c / t) ≤ Real.log (n * c₀ / t) :=
              Real.log_le_log (div_pos hc ht) (div_le_div_of_nonneg_right hcn ht.le)
          _ = Real.log n + Real.log (c₀ / t) := by
              rw [mul_div_assoc, Real.log_mul hn0.ne' (div_pos hc₀ ht).ne']
          _ ≤ Real.log n + |Real.log (c₀ / t)| := by
              linarith [le_abs_self (Real.log (c₀ / t))]
      have hpow : Real.log (c / t) ^ r ≤ 2 ^ r * (Real.log n ^ r + |Real.log (c₀ / t)| ^ r) :=
        (pow_le_pow_left₀ hlog0 hlog r).trans
          (add_pow_le_two_pow_mul_add_pow hlogn (abs_nonneg _) r)
      have hX : 0 ≤ Real.exp (-t) * t ^ (s - 1) := by positivity
      calc Real.exp (-t) * (t ^ (s - 1) * Real.log (c / t) ^ r)
          = (Real.exp (-t) * t ^ (s - 1)) * Real.log (c / t) ^ r := by ring
        _ ≤ (Real.exp (-t) * t ^ (s - 1)) *
              (2 ^ r * (Real.log n ^ r + |Real.log (c₀ / t)| ^ r)) :=
            mul_le_mul_of_nonneg_left hpow hX
        _ = _ := by ring
    · rw [indicator_of_notMem htc, mul_zero]
      positivity
  have hnonneg : ∀ t ∈ Ioi (0 : ℝ),
      0 ≤ Real.exp (-t) * (Ioo 0 c).indicator (fun t ↦ t ^ (s - 1) * Real.log (c / t) ^ r) t := by
    intro t ht
    have ht : 0 < t := ht
    refine mul_nonneg (Real.exp_pos _).le (indicator_nonneg (fun t htc ↦ ?_) t)
    exact mul_nonneg (Real.rpow_nonneg htc.1.le _)
      (pow_nonneg (Real.log_div_nonneg_of_mem_Ioo htc) r)
  calc ∫ t in Ioi 0,
        Real.exp (-t) * (Ioo 0 c).indicator (fun t ↦ t ^ (s - 1) * Real.log (c / t) ^ r) t
      ≤ ∫ t in Ioi 0, 2 ^ r * Real.log n ^ r * (Real.exp (-t) * t ^ (s - 1))
          + 2 ^ r * (t ^ (s - 1) * Real.exp (-t) * |Real.log (c₀ / t)| ^ r) :=
        integral_mono_of_nonneg
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hnonneg))
          ((hGint.const_mul _).add (hLint.const_mul _))
          ((ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hdom))
    _ = 2 ^ r * Real.log n ^ r * G + 2 ^ r * L := by
        rw [integral_add (hGint.const_mul _) (hLint.const_mul _), integral_const_mul,
          integral_const_mul]
    _ ≤ 2 ^ r * Real.log n ^ r * G + 2 ^ r * (L / Real.log 2 ^ r * Real.log n ^ r) := by
        gcongr
    _ = _ := by ring

theorem restrict_ocube_eq {m : ℕ} (b : ℝ) :
    (volume : Measure (Fin m → ℝ)).restrict (ocube m b) = volume.restrict (cube m b) :=
  Measure.restrict_congr_set (by
    rw [volume_pi, ocube, cube]
    exact Measure.univ_pi_Ioo_ae_eq_Icc (μ := fun _ ↦ volume))

/-- `Z^p(n)` as an integral against the product of the (open) cube measures. -/
theorem NormalCrossing.blockIntegral₀_eq_integral_prod {m m' : ℕ} (k : Fin m → ℕ) (h : Fin m → ℝ)
    (k' : Fin m' → ℕ)
    (h' : Fin m' → ℝ) (b β p n : ℝ) :
    NormalCrossing.blockIntegral₀ k h k' h' b β p n
      = ∫ z, potential k k' z ^ p * Real.exp (-(n * β * potential k k' z)) *
          NormalCrossing.monomialWeight h h' z
        ∂((volume.restrict (ocube m b)).prod (volume.restrict (ocube m' b))) := by
  rw [NormalCrossing.blockIntegral₀, restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict]
  rfl

/-- On the open cube the integrand of `Z^p(n)` factorises as
`e^{-(nβ v^{2k'}) u^{2k}} · u^{h + 2kp} · v^{h' + 2k'p}`. No thesis counterpart. -/
private theorem NormalCrossing.blockIntegral₀_integrand_eq {m m' : ℕ} (k : Fin m → ℕ)
    (h : Fin m → ℝ)
    (k' : Fin m' → ℕ)
    (h' : Fin m' → ℝ) (β p n : ℝ) {z : (Fin m → ℝ) × (Fin m' → ℝ)}
    (hu : ∀ j, 0 < z.1 j) (hv : ∀ j, 0 < z.2 j) :
    potential k k' z ^ p * Real.exp (-(n * β * potential k k' z)) *
        NormalCrossing.monomialWeight h h' z
      = Real.exp (-((n * β * ∏ j, z.2 j ^ (2 * k' j)) * ∏ j, z.1 j ^ (2 * k j))) *
          (∏ j, z.1 j ^ (h j + 2 * k j * p)) * ∏ j, z.2 j ^ (h' j + 2 * k' j * p) := by
  have hu0 : ∀ j, 0 ≤ z.1 j := fun j ↦ (hu j).le
  have hv0 : ∀ j, 0 ≤ z.2 j := fun j ↦ (hv j).le
  have hU : 0 ≤ ∏ j, z.1 j ^ (2 * k j) := Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu0 j) _
  have hV : 0 ≤ ∏ j, z.2 j ^ (2 * k' j) := Finset.prod_nonneg fun j _ ↦ pow_nonneg (hv0 j) _
  rw [potential, NormalCrossing.monomialWeight, Real.mul_rpow hU hV,
    show (∏ j, z.1 j ^ (2 * k j)) ^ p * (∏ j, z.2 j ^ (2 * k' j)) ^ p *
        Real.exp (-(n * β * ((∏ j, z.1 j ^ (2 * k j)) * ∏ j, z.2 j ^ (2 * k' j)))) *
        ((∏ j, z.1 j ^ h j) * ∏ j, z.2 j ^ h' j)
      = Real.exp (-(n * β * ((∏ j, z.1 j ^ (2 * k j)) * ∏ j, z.2 j ^ (2 * k' j)))) *
        ((∏ j, z.1 j ^ (2 * k j)) ^ p * ∏ j, z.1 j ^ h j) *
        ((∏ j, z.2 j ^ (2 * k' j)) ^ p * ∏ j, z.2 j ^ h' j) by ring,
    Real.prod_pow_rpow_mul_prod_rpow k h p hu, Real.prod_pow_rpow_mul_prod_rpow k' h' p hv,
    show n * β * ((∏ j, z.1 j ^ (2 * k j)) * ∏ j, z.2 j ^ (2 * k' j))
      = n * β * (∏ j, z.2 j ^ (2 * k' j)) * ∏ j, z.1 j ^ (2 * k j) by ring]

/-- No thesis counterpart. -/
theorem NormalCrossing.measurable_potential {m m' : ℕ} (k : Fin m → ℕ) (k' : Fin m' → ℕ) :
    Measurable (potential k k') := by
  unfold potential
  exact (Finset.measurable_prod _ fun j _ ↦
      ((measurable_pi_apply j).comp measurable_fst).pow_const _).mul
    (Finset.measurable_prod _ fun j _ ↦ ((measurable_pi_apply j).comp measurable_snd).pow_const _)

/-- No thesis counterpart. -/
theorem NormalCrossing.measurable_monomialWeight {m m' : ℕ} (h : Fin m → ℝ)
    (h' : Fin m' → ℝ) :
    Measurable (NormalCrossing.monomialWeight h h') := by
  unfold NormalCrossing.monomialWeight
  exact (Finset.measurable_prod _ fun j _ ↦
      ((measurable_pi_apply j).comp measurable_fst).pow_const _).mul
    (Finset.measurable_prod _ fun j _ ↦ ((measurable_pi_apply j).comp measurable_snd).pow_const _)

/-- Almost every point of the product of the open cubes has all coordinates in `(0, b)`. -/
theorem ae_prod_ocube {m m' : ℕ} (b : ℝ) :
    ∀ᵐ z : (Fin m → ℝ) × (Fin m' → ℝ)
      ∂((volume.restrict (ocube m b)).prod (volume.restrict (ocube m' b))),
      (∀ j, z.1 j ∈ Ioo 0 b) ∧ ∀ j, z.2 j ∈ Ioo 0 b := by
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem ((MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo).prod
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo))] with z hz
  exact ⟨fun j ↦ hz.1 j (mem_univ j), fun j ↦ hz.2 j (mem_univ j)⟩

/-- `K(u, v) ≤ b^{2|k| + 2|k'|}` on the cube. -/
theorem NormalCrossing.potential_le {m m' : ℕ} (k : Fin m → ℕ) (k' : Fin m' → ℕ) {b : ℝ}
    (hb : 0 < b)
    {z : (Fin m → ℝ) × (Fin m' → ℝ)} (hu : ∀ j, z.1 j ∈ Icc 0 b) (hv : ∀ j, z.2 j ∈ Icc 0 b) :
    potential k k' z ≤ b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j) := by
  unfold potential
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum]
  exact mul_le_mul
    (Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hu j).1 _) fun j _ ↦
      pow_le_pow_left₀ (hu j).1 (hu j).2 _)
    (Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hv j).1 _) fun j _ ↦
      pow_le_pow_left₀ (hv j).1 (hv j).2 _)
    (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hv j).1 _)
    (Finset.prod_nonneg fun j _ ↦ pow_nonneg hb.le _)

/-- `K ≥ 0` on the cube. -/
theorem NormalCrossing.potential_nonneg {m m' : ℕ} (k : Fin m → ℕ) (k' : Fin m' → ℕ)
    {z : (Fin m → ℝ) × (Fin m' → ℝ)} (hu : ∀ j, 0 ≤ z.1 j) (hv : ∀ j, 0 ≤ z.2 j) :
    0 ≤ potential k k' z :=
  mul_nonneg (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu j) _)
    (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hv j) _)

/-- The integrand of `Z^p(n)` is integrable on the (open) cube: the weight is integrable
and the remaining factor is bounded. -/
theorem NormalCrossing.integrable_blockIntegral₀_integrand {m m' : ℕ} (k : Fin m → ℕ)
    {h : Fin m → ℝ}
    (k' : Fin m' → ℕ)
    {h' : Fin m' → ℝ} {b β p n : ℝ} (hh : ∀ j, -1 < h j) (hh' : ∀ j, -1 < h' j) (hb : 0 < b)
    (hβ : 0 ≤ β) (hp : 0 ≤ p) (hn : 0 ≤ n) :
    Integrable (fun z ↦ potential k k' z ^ p * Real.exp (-(n * β * potential k k' z)) *
        NormalCrossing.monomialWeight h h' z)
      ((volume.restrict (ocube m b)).prod (volume.restrict (ocube m' b))) := by
  have hw : Integrable (NormalCrossing.monomialWeight h h')
      ((volume.restrict (ocube m b)).prod (volume.restrict (ocube m' b))) := by
    rw [restrict_ocube_eq, restrict_ocube_eq]
    exact (integrableOn_cube_rpow hh hb).mul_prod (integrableOn_cube_rpow hh' hb)
  refine hw.bdd_mul (c := (b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j)) ^ p)
    ((measurable_potential k k').pow_const p |>.mul
      (Real.measurable_exp.comp ((measurable_potential k k').const_mul _).neg)
      |>.aestronglyMeasurable) ?_
  filter_upwards [ae_prod_ocube (m := m) (m' := m') b] with z hz
  have hu : ∀ j, z.1 j ∈ Icc 0 b := fun j ↦ Ioo_subset_Icc_self (hz.1 j)
  have hv : ∀ j, z.2 j ∈ Icc 0 b := fun j ↦ Ioo_subset_Icc_self (hz.2 j)
  have hK0 : 0 ≤ potential k k' z :=
    potential_nonneg k k' (fun j ↦ (hu j).1) fun j ↦ (hv j).1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hK0 _) (Real.exp_pos _).le)]
  calc potential k k' z ^ p * Real.exp (-(n * β * potential k k' z))
      ≤ potential k k' z ^ p * 1 := by
        gcongr
        exact Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hn hβ])
    _ ≤ (b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j)) ^ p := by
        rw [mul_one]
        exact Real.rpow_le_rpow hK0 (potential_le k k' hb hu hv) hp

/-- `γ_b > 0`. -/
theorem NormalCrossing.gammaConst_pos {m : ℕ} {k : Fin m → ℕ} (h : Fin m → ℝ) (lam : ℝ)
    {b : ℝ}
    (hk : ∀ j, 0 < k j) (hb : 0 < b) : 0 < NormalCrossing.gammaConst k h lam b := by
  unfold NormalCrossing.gammaConst
  have : (0 : ℝ) < ∏ j, (k j : ℝ) := Finset.prod_pos fun j _ ↦ by exact_mod_cast hk j
  positivity

/-- `u^{2k} ≤ b^{2|k|}` on the cube. No thesis counterpart. -/
theorem _root_.Finset.prod_pow_le_of_mem_Icc {m : ℕ} (k : Fin m → ℕ) {b : ℝ} {u : Fin m → ℝ}
    (hu : ∀ j, u j ∈ Icc 0 b) : ∏ j, u j ^ (2 * k j) ≤ b ^ (2 * ∑ j, k j) := by
  rw [Finset.mul_sum, ← Finset.prod_pow_eq_pow_sum]
  exact Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hu j).1 _) fun j _ ↦
    pow_le_pow_left₀ (hu j).1 (hu j).2 _

/-- The exponent bookkeeping behind [Wat09, Theorem 4.7]: with `s = λ + p`, the shifted primary
weights `h_j + 2 k_j p` have ratio `s`, the secondary weights `h'_j + 2 k'_j p` exceed `-1`,
and `h_j > -1`, `h'_j > -1`. -/
theorem NormalCrossing.exponents_aux (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hp : 0 ≤ p) :
    (∀ j, -1 < h j) ∧ (∀ j, -1 < h' j) ∧
      (∀ j, (h j + 2 * k j * p + 1) / (2 * k j) = lam + p) ∧
      (∀ j, -1 < h' j + 2 * k' j * p) := by
  have hkR : ∀ j, (0 : ℝ) < k j := fun j ↦ by exact_mod_cast hk j
  have key : ∀ j, h j + 1 = lam * (2 * k j) := fun j ↦ by
    have := hlam j
    rwa [div_eq_iff (by have := hkR j; positivity)] at this
  refine ⟨fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_, fun j ↦ ?_⟩
  · have := key j; have := hkR j; nlinarith
  · have := hsec j
    have : (0 : ℝ) ≤ 2 * k' j * lam := by positivity
    linarith
  · rw [div_eq_iff (by have := hkR j; positivity)]; linarith [key j]
  · have := hsec j
    have : (0 : ℝ) ≤ 2 * k' j * lam := by positivity
    have : (0 : ℝ) ≤ 2 * k' j * p := by positivity
    linarith

/-- [Hit26, Theorem 3.2.6] ([Wat09, Theorem 4.7]), lower bound: there is
`a₁ > 0` with `a₁ (log n)^{m-1} / n^{λ+p} ≤ Z^p(n)` for all `n > 1`. -/
theorem NormalCrossing.blockIntegral₀_lower_bound (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) /
    (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    (hp : 0 ≤ p) :
    ∃ a₁ > 0, ∀ n : ℝ, 1 < n →
      a₁ * Real.log n ^ r / n ^ (lam + p) ≤ NormalCrossing.blockIntegral₀ k h k' h' b β p n := by
  obtain ⟨hh, hh', hkp, hμ'⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec hp
  have hs : 0 < lam + p := by positivity
  have hB : 0 < b ^ (2 * ∑ j, k' j) := by positivity
  set c₀ : ℝ := β * b ^ (2 * ∑ j, k' j) * b ^ (2 * ∑ j, k j) with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  have hγ : 0 < NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b :=
      gammaConst_pos _ _ hk hb
  have hcv : 0 < ∏ j, b ^ (h' j + 2 * k' j * p + 1) / (h' j + 2 * k' j * p + 1) :=
    Finset.prod_pos fun j _ ↦ div_pos (Real.rpow_pos_of_pos hb _) (by linarith [hμ' j])
  have hI₀ : 0 < ∫ t in Ioo 0 c₀, Real.exp (-t) * t ^ (lam + p - 1) := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsupp : Function.support (fun t : ℝ ↦ Real.exp (-t) * t ^ (lam + p - 1)) ∩ Ioo 0 c₀
          = Ioo 0 c₀ := by
        refine inter_eq_right.mpr fun t ht ↦ ?_
        exact (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht.1 _)).ne'
      rw [hsupp, Real.volume_Ioo, sub_zero]
      exact ENNReal.ofReal_pos.mpr hc₀
    · refine ae_restrict_of_forall_mem measurableSet_Ioo fun t ht ↦ ?_
      exact (mul_pos (Real.exp_pos _) (Real.rpow_pos_of_pos ht.1 _)).le
    · exact (Real.GammaIntegral_convergent hs).mono_set Ioo_subset_Ioi_self
  refine ⟨(∏ j, b ^ (h' j + 2 * k' j * p + 1) / (h' j + 2 * k' j * p + 1)) *
    NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b *
    (β * b ^ (2 * ∑ j, k' j)) ^ (-(lam + p)) *
    ∫ t in Ioo 0 c₀, Real.exp (-t) * t ^ (lam + p - 1), by positivity, fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by linarith
  set a : ℝ := n * β * b ^ (2 * ∑ j, k' j) with ha_def
  have ha : 0 < a := by positivity
  have hac : a * b ^ (2 * ∑ j, k j) = n * c₀ := by rw [ha_def, hc₀_def]; ring
  -- Step 1: bound the integrand below on the open cube.
  rw [blockIntegral₀_eq_integral_prod, restrict_ocube_eq, restrict_ocube_eq]
  have step1 : ∫ z : (Fin (r + 1) → ℝ) × (Fin m' → ℝ),
        (Real.exp (-(a * ∏ j, z.1 j ^ (2 * k j))) * ∏ j, z.1 j ^ (h j + 2 * k j * p)) *
          ∏ j, z.2 j ^ (h' j + 2 * k' j * p)
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b)))
      ≤ ∫ z, potential k k' z ^ p * Real.exp (-(n * β * potential k k' z)) *
          NormalCrossing.monomialWeight h h' z
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) := by
    refine integral_mono_of_nonneg ?_
        (integrable_blockIntegral₀_integrand k k' hh hh' hb hβ.le hp hn0.le) ?_
    · filter_upwards [ae_prod_ocube (m := r + 1) (m' := m') b] with z hz
      exact mul_nonneg (mul_nonneg (Real.exp_pos _).le
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hz.1 j).1.le _))
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hz.2 j).1.le _)
    · filter_upwards [ae_prod_ocube (m := r + 1) (m' := m') b] with z hz
      rw [blockIntegral₀_integrand_eq k h k' h' β p n (fun j ↦ (hz.1 j).1) (fun j ↦ (hz.2 j).1)]
      refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hz.1 j).1.le _))
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hz.2 j).1.le _)
      rw [Real.exp_le_exp, neg_le_neg_iff, ha_def]
      have hU : 0 ≤ ∏ j, z.1 j ^ (2 * k j) :=
        Finset.prod_nonneg fun j _ ↦ pow_nonneg (hz.1 j).1.le _
      have hV := Finset.prod_pow_le_of_mem_Icc k' fun j ↦ Ioo_subset_Icc_self (hz.2 j)
      have hnβ : 0 ≤ n * β := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hV hnβ]
  -- Step 2: the lower integrand factorises.
  rw [integral_prod_mul (fun u : Fin (r + 1) → ℝ ↦
      Real.exp (-(a * ∏ j, u j ^ (2 * k j))) * ∏ j, u j ^ (h j + 2 * k j * p))
    (fun v : Fin m' → ℝ ↦ ∏ j, v j ^ (h' j + 2 * k' j * p)), restrict_ocube_eq,
    restrict_ocube_eq, integral_cube_rpow hμ' hb] at step1
  -- Step 3: the `u`-integral via [Wat09, Theorem 4.6].
  set ν : ℝ → ℝ := (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
    (fun t ↦ NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b * t ^
        (lam + p - 1) /
      a ^ (lam + p) * Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r) with hν_def
  have hνint : Integrable ν := by
    rw [hν_def, integrable_indicator_iff measurableSet_Ioo]
    have := ((integrableOn_rpow_mul_log_pow_Ioo hs (by positivity : 0 < a * b ^ (2 * ∑ j, k j))
      r).const_mul
          (NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b / a ^ (lam + p)))
    exact IntegrableOn.congr_fun this (fun t _ ↦ by ring) measurableSet_Ioo
  have hν0 : ∀ t, 0 ≤ ν t := by
    intro t
    rw [hν_def]
    refine indicator_nonneg (fun t ht ↦ ?_) t
    obtain ⟨ht0, htc⟩ := ht
    have hlog : 0 ≤ Real.log (a * b ^ (2 * ∑ j, k j) / t) :=
      Real.log_nonneg ((one_le_div ht0).mpr htc.le)
    positivity
  have hint : Integrable fun t ↦ Real.exp (-t) * ν t := by
    refine hνint.mono' (Real.measurable_exp.comp measurable_neg |>.aestronglyMeasurable.mul
      hνint.aestronglyMeasurable) (Filter.Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hν0 t))]
    by_cases ht : t ∈ Ioo 0 (a * b ^ (2 * ∑ j, k j))
    · exact mul_le_of_le_one_left (hν0 t) (Real.exp_le_one_iff.mpr (by linarith [ht.1]))
    · simp [hν_def, indicator_of_notMem ht]
  have step3 := integral_cube_monomial (r := r) (a := a) hk hkp ha hb
    (f := fun t ↦ Real.exp (-t)) (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
    hint
  rw [step3] at step1
  -- Step 4: pull the constant out of the state density and apply the core estimate.
  have hpull : ∫ t in Ioi 0, Real.exp (-t) * ν t
      = NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b / a ^ (lam + p) *
        ∫ t in Ioi 0, Real.exp (-t) *
          (Ioo 0 (n * c₀)).indicator (fun t ↦ t ^ (lam + p - 1) * Real.log (n * c₀ / t) ^ r) t := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    rw [hν_def, ← hac]
    by_cases ht : t ∈ Ioo 0 (a * b ^ (2 * ∑ j, k j))
    · simp only [indicator_of_mem ht]; ring
    · simp [indicator_of_notMem ht]
  have hcore := lower_bound_core hs hc₀ hn r
  -- Step 5: assemble.
  have hpow : a ^ (lam + p) = n ^ (lam + p) * (β * b ^ (2 * ∑ j, k' j)) ^ (lam + p) := by
    rw [ha_def, mul_assoc, Real.mul_rpow hn0.le (by positivity)]
  rw [hpull, hpow] at step1
  have hnpos : 0 < n ^ (lam + p) := Real.rpow_pos_of_pos hn0 _
  have hβB : 0 < (β * b ^ (2 * ∑ j, k' j)) ^ (lam + p) := by positivity
  rw [Real.rpow_neg (by positivity)]
  calc _ = (∏ j, b ^ (h' j + 2 * k' j * p + 1) / (h' j + 2 * k' j * p + 1)) *
        (NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b /
          (n ^ (lam + p) * (β * b ^ (2 * ∑ j, k' j)) ^ (lam + p))) *
        (Real.log n ^ r * ∫ t in Ioo 0 c₀, Real.exp (-t) * t ^ (lam + p - 1)) := by
        ring
    _ ≤ (∏ j, b ^ (h' j + 2 * k' j * p + 1) / (h' j + 2 * k' j * p + 1)) *
        (NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b /
          (n ^ (lam + p) * (β * b ^ (2 * ∑ j, k' j)) ^ (lam + p)) *
        ∫ t in Ioi 0, Real.exp (-t) *
          (Ioo 0 (n * c₀)).indicator
            (fun t ↦ t ^ (lam + p - 1) * Real.log (n * c₀ / t) ^ r) t) := by
        rw [mul_assoc]
        gcongr
    _ ≤ _ := by
        convert step1 using 1
        ring

/-- [Hit26, Theorem 3.2.6] ([Wat09, Theorem 4.7]), upper bound: there is
`a₂ > 0` with `Z^p(n) ≤ a₂ (log n)^{m-1} / n^{λ+p}` for all `n ≥ 2`. [Hit26] says
`n > 1`, which is false for `m ≥ 2`. -/
theorem NormalCrossing.blockIntegral₀_upper_bound (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) /
    (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    (hp : 0 ≤ p) :
    ∃ a₂ > 0, ∀ n : ℝ, 2 ≤ n →
      NormalCrossing.blockIntegral₀ k h k' h' b β p n ≤ a₂ * Real.log n ^ r / n ^ (lam + p) := by
  obtain ⟨hh, hh', hkp, hμ'⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec hp
  have hs : 0 < lam + p := by positivity
  have hB : 0 < b ^ (2 * ∑ j, k' j) := by positivity
  set c₀ : ℝ := β * b ^ (2 * ∑ j, k' j) * b ^ (2 * ∑ j, k j) with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  have hγ : 0 < NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b :=
      gammaConst_pos _ _ hk hb
  obtain ⟨A, hA, hcore⟩ := upper_bound_core hs hc₀ r
  -- the secondary weight after dividing out `(v^{2k'})^{λ+p}`
  set μ : Fin m' → ℝ := fun j ↦ h' j - 2 * k' j * lam with hμ_def
  have hμ : ∀ j, -1 < μ j := fun j ↦ by
    have := hsec j
    simp only [hμ_def]
    linarith
  have hcμ : 0 ≤ ∏ j, b ^ (μ j + 1) / (μ j + 1) :=
    Finset.prod_nonneg fun j _ ↦ (div_pos (Real.rpow_pos_of_pos hb _) (by linarith [hμ j])).le
  refine ⟨NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b * A * β ^
      (-(lam + p)) *
    (∏ j, b ^ (μ j + 1) / (μ j + 1)) + 1, by positivity, fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hnpos : 0 < n ^ (lam + p) := Real.rpow_pos_of_pos hn0 _
  -- Step 1: Fubini, integrating out the primary coordinates first.
  rw [blockIntegral₀_eq_integral_prod,
    integral_prod_symm _ (integrable_blockIntegral₀_integrand k k' hh hh' hb hβ.le hp hn0.le)]
  -- Step 2: for a.e. `v`, the inner integral is bounded by `C (log n)^r v^μ / n^{λ+p}`.
  set C : ℝ := NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b * A * β ^
      (-(lam + p)) *
    Real.log n ^ r / n ^ (lam + p) with hC_def
  have hC : 0 ≤ C := by positivity
  have inner : ∀ v : Fin m' → ℝ, (∀ j, v j ∈ Ioo 0 b) →
      ∫ u in ocube (r + 1) b, potential k k' (u, v) ^ p *
          Real.exp (-(n * β * potential k k' (u, v))) * NormalCrossing.monomialWeight h h' (u, v)
        ≤ C * ∏ j, v j ^ μ j := by
    intro v hv
    have hv0 : ∀ j, 0 < v j := fun j ↦ (hv j).1
    set V : ℝ := ∏ j, v j ^ (2 * k' j) with hV_def
    have hV : 0 < V := Finset.prod_pos fun j _ ↦ pow_pos (hv0 j) _
    have hVle : V ≤ b ^ (2 * ∑ j, k' j) :=
      Finset.prod_pow_le_of_mem_Icc k' fun j ↦ Ioo_subset_Icc_self (hv j)
    set a : ℝ := n * β * V with ha_def
    have ha : 0 < a := by positivity
    -- rewrite the inner integrand on the open cube
    have hre : ∫ u in ocube (r + 1) b, potential k k' (u, v) ^ p *
          Real.exp (-(n * β * potential k k' (u, v))) * NormalCrossing.monomialWeight h h' (u, v)
        = (∫ u in cube (r + 1) b, Real.exp (-(a * ∏ j, u j ^ (2 * k j))) *
            ∏ j, u j ^ (h j + 2 * k j * p)) * ∏ j, v j ^ (h' j + 2 * k' j * p) := by
      rw [← integral_mul_const, ← restrict_ocube_eq]
      refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)
        fun u hu ↦ ?_
      have hu0 : ∀ j, 0 < u j := fun j ↦ (hu j (mem_univ j)).1
      exact blockIntegral₀_integrand_eq k h k' h' β p n (z := (u, v)) hu0 hv0
    rw [hre]
    -- the `u`-integral via [Wat09, Theorem 4.6]
    set ν : ℝ → ℝ := (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
      (fun t ↦ NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b * t ^
          (lam + p - 1) /
        a ^ (lam + p) * Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r) with hν_def
    have hνint : Integrable ν := by
      rw [hν_def, integrable_indicator_iff measurableSet_Ioo]
      have := ((integrableOn_rpow_mul_log_pow_Ioo hs
        (by positivity : 0 < a * b ^ (2 * ∑ j, k j)) r).const_mul
        (NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b / a ^ (lam + p)))
      exact IntegrableOn.congr_fun this (fun t _ ↦ by ring) measurableSet_Ioo
    have hν0 : ∀ t, 0 ≤ ν t := by
      intro t
      rw [hν_def]
      refine indicator_nonneg (fun t ht ↦ ?_) t
      obtain ⟨ht0, htc⟩ := ht
      have hlog : 0 ≤ Real.log (a * b ^ (2 * ∑ j, k j) / t) :=
        Real.log_nonneg ((one_le_div ht0).mpr htc.le)
      positivity
    have hint : Integrable fun t ↦ Real.exp (-t) * ν t := by
      refine hνint.mono' (Real.measurable_exp.comp measurable_neg |>.aestronglyMeasurable.mul
        hνint.aestronglyMeasurable) (Filter.Eventually.of_forall fun t ↦ ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hν0 t))]
      by_cases ht : t ∈ Ioo 0 (a * b ^ (2 * ∑ j, k j))
      · exact mul_le_of_le_one_left (hν0 t) (Real.exp_le_one_iff.mpr (by linarith [ht.1]))
      · simp [hν_def, indicator_of_notMem ht]
    have step3 := integral_cube_monomial (r := r) (a := a) hk hkp ha hb
      (f := fun t ↦ Real.exp (-t)) (Real.measurable_exp.comp measurable_neg).aestronglyMeasurable
      hint
    rw [step3]
    have hpull : ∫ t in Ioi 0, Real.exp (-t) * ν t
        = NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b / a ^ (lam + p) *
          ∫ t in Ioi 0, Real.exp (-t) * (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
              (fun t ↦ t ^ (lam + p - 1) * Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r) t := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
      rw [hν_def]
      by_cases ht : t ∈ Ioo 0 (a * b ^ (2 * ∑ j, k j))
      · simp only [indicator_of_mem ht]; ring
      · simp [indicator_of_notMem ht]
    have hcle : a * b ^ (2 * ∑ j, k j) ≤ n * c₀ := by
      rw [ha_def, hc₀_def]
      have := mul_le_mul_of_nonneg_left hVle (by positivity : (0 : ℝ) ≤ n * β)
      nlinarith [pow_pos hb (2 * ∑ j, k j)]
    have hbound := hcore n (a * b ^ (2 * ∑ j, k j)) hn (by positivity) hcle
    -- a^{λ+p} = (nβ)^{λ+p} V^{λ+p}, and v^{h'+2k'p} / V^{λ+p} = v^μ
    have hVpow : V ^ (lam + p) = ∏ j, v j ^ (2 * k' j * (lam + p)) := by
      rw [hV_def, ← Real.finsetProd_rpow _ _ fun j _ ↦ pow_nonneg (hv0 j).le _]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [← Real.rpow_natCast, ← Real.rpow_mul (hv0 j).le]
      push_cast
      ring_nf
    have hvμ : (∏ j, v j ^ (h' j + 2 * k' j * p)) / V ^ (lam + p) = ∏ j, v j ^ μ j := by
      rw [hVpow, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl fun j _ ↦ ?_
      rw [← Real.rpow_sub (hv0 j), hμ_def]
      ring_nf
    have hapow : a ^ (lam + p) = (n * β) ^ (lam + p) * V ^ (lam + p) := by
      rw [ha_def, Real.mul_rpow (by positivity) hV.le]
    have hnβ : (n * β) ^ (lam + p) = n ^ (lam + p) * β ^ (lam + p) :=
      Real.mul_rpow hn0.le hβ.le
    have hVp : 0 < V ^ (lam + p) := Real.rpow_pos_of_pos hV _
    have hβp : 0 < β ^ (lam + p) := Real.rpow_pos_of_pos hβ _
    calc (∫ t in Ioi 0, Real.exp (-t) * ν t) * ∏ j, v j ^ (h' j + 2 * k' j * p)
        ≤ NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b / a ^ (lam + p) *
            (A * Real.log n ^ r) * ∏ j, v j ^ (h' j + 2 * k' j * p) := by
          rw [hpull]
          gcongr
          exact Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv0 j).le _
      _ = C * ((∏ j, v j ^ (h' j + 2 * k' j * p)) / V ^ (lam + p)) := by
          rw [hC_def, hapow, hnβ, Real.rpow_neg hβ.le]
          ring
      _ = C * ∏ j, v j ^ μ j := by rw [hvμ]
  -- Step 3: integrate the bound over the secondary cube.
  have hint_v : Integrable (fun v : Fin m' → ℝ ↦ C * ∏ j, v j ^ μ j)
      (volume.restrict (ocube m' b)) := by
    rw [restrict_ocube_eq]; exact (integrableOn_cube_rpow hμ hb).const_mul C
  have hnonneg_u : ∀ v : Fin m' → ℝ, (∀ j, v j ∈ Ioo 0 b) →
      0 ≤ ∫ u in ocube (r + 1) b, potential k k' (u, v) ^ p *
          Real.exp (-(n * β * potential k k' (u, v))) * NormalCrossing.monomialWeight h h'
              (u, v) := by
    intro v hv
    refine setIntegral_nonneg (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo) fun u hu ↦ ?_
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ (hu j (mem_univ j)).1.le
    have hK0 := potential_nonneg k k' (z := (u, v)) hu0 fun j ↦ (hv j).1.le
    refine mul_nonneg (mul_nonneg (Real.rpow_nonneg hK0 _) (Real.exp_pos _).le) ?_
    exact mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu0 j) _)
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv j).1.le _)
  have hae : ∀ᵐ v ∂(volume.restrict (ocube m' b)), ∀ j, v j ∈ Ioo 0 b := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)] with v hv
    exact fun j ↦ hv j (mem_univ j)
  calc ∫ v in ocube m' b, ∫ u in ocube (r + 1) b, potential k k' (u, v) ^ p *
          Real.exp (-(n * β * potential k k' (u, v))) * NormalCrossing.monomialWeight h h' (u, v)
      ≤ ∫ v in ocube m' b, C * ∏ j, v j ^ μ j := by
        refine integral_mono_of_nonneg ?_ hint_v ?_
        · filter_upwards [hae] with v hv using hnonneg_u v hv
        · filter_upwards [hae] with v hv using inner v hv
    _ = C * ∏ j, b ^ (μ j + 1) / (μ j + 1) := by
        rw [integral_const_mul, restrict_ocube_eq, integral_cube_rpow hμ hb]
    _ ≤ _ := by
        rw [hC_def]
        have : 0 ≤ Real.log n ^ r / n ^ (lam + p) := by positivity
        calc NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b * A * β ^
            (-(lam + p)) *
              Real.log n ^ r / n ^ (lam + p) * ∏ j, b ^ (μ j + 1) / (μ j + 1)
            = (NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b * A * β ^
                (-(lam + p)) *
                ∏ j, b ^ (μ j + 1) / (μ j + 1)) * (Real.log n ^ r / n ^ (lam + p)) := by ring
          _ ≤ (NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b * A * β ^
              (-(lam + p)) *
                (∏ j, b ^ (μ j + 1) / (μ j + 1)) + 1) *
              (Real.log n ^ r / n ^ (lam + p)) := by gcongr; linarith
          _ = _ := by ring

end GBTheorem47

/-! ## Splitting the coordinates of `ℝ^d` into two blocks

No thesis counterpart. A finset `P ⊆ Fin d` with bijections `Fin r ≃ P` and `Fin s ≃ Pᶜ`
gives a measure preserving equivalence `(Fin r → ℝ) × (Fin s → ℝ) ≃ᵐ (Fin d → ℝ)` that
carries `cube r b ×ˢ cube s b` onto `cube d b` and monomials onto block monomials. -/

section Block

variable {d r s : ℕ} {P : Finset (Fin d)} (eP : Fin r ≃ {j // j ∈ P}) (eS : Fin s ≃ {j // j ∉ P})

/-- The index bijection `Fin r ⊕ Fin s ≃ Fin d` assembled from `eP` and `eS`. -/
@[expose] def _root_.Equiv.blockIndex : Fin r ⊕ Fin s ≃ Fin d := (eP.sumCongr eS).trans
    (Equiv.sumCompl (· ∈ P))

@[simp] theorem _root_.Equiv.blockIndex_inl (i : Fin r) : Equiv.blockIndex eP eS
    (Sum.inl i) = eP i := rfl

@[simp] theorem _root_.Equiv.blockIndex_inr (i : Fin s) : Equiv.blockIndex eP eS
    (Sum.inr i) = eS i := rfl

/-- The block coordinates `z = (u|_P, u|_{Pᶜ}) ↦ u`, as a measurable equivalence. -/
@[expose] noncomputable def _root_.MeasurableEquiv.blockEquiv : (Fin r → ℝ) × (Fin s → ℝ) ≃ᵐ
    (Fin d → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin r ⊕ Fin s ↦ ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (Equiv.blockIndex eP eS))

@[simp] theorem _root_.MeasurableEquiv.blockEquiv_apply_inl (z : (Fin r → ℝ) × (Fin s → ℝ))
    (i : Fin r) :
    MeasurableEquiv.blockEquiv eP eS z (eP i) = z.1 i :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) (Equiv.blockIndex eP eS)
    ((MeasurableEquiv.sumPiEquivProdPi fun _ : Fin r ⊕ Fin s ↦ ℝ).symm z) (Sum.inl i)

@[simp] theorem _root_.MeasurableEquiv.blockEquiv_apply_inr (z : (Fin r → ℝ) × (Fin s → ℝ))
    (i : Fin s) :
    MeasurableEquiv.blockEquiv eP eS z (eS i) = z.2 i :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) (Equiv.blockIndex eP eS)
    ((MeasurableEquiv.sumPiEquivProdPi fun _ : Fin r ⊕ Fin s ↦ ℝ).symm z) (Sum.inr i)

theorem _root_.MeasurableEquiv.blockEquiv_measurePreserving : MeasurePreserving
    (MeasurableEquiv.blockEquiv eP eS) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm _).trans
    (volume_measurePreserving_piCongrLeft _ _)

theorem _root_.MeasurableEquiv.blockEquiv_preimage_cube (b : ℝ) :
    MeasurableEquiv.blockEquiv eP eS ⁻¹' cube d b = cube r b ×ˢ cube s b := by
  ext z
  simp only [mem_preimage, mem_cube, mem_prod]
  constructor
  · intro H
    exact ⟨fun i ↦ by simpa using H (eP i), fun i ↦ by simpa using H (eS i)⟩
  · rintro ⟨H₁, H₂⟩ j
    obtain ⟨t, rfl⟩ := (Equiv.blockIndex eP eS).surjective j
    rcases t with i | i
    · simpa using H₁ i
    · simpa using H₂ i

theorem _root_.MeasurableEquiv.prod_blockEquiv (f : Fin d → ℝ → ℝ) (z : (Fin r → ℝ) × (Fin s → ℝ)) :
    ∏ j, f j (MeasurableEquiv.blockEquiv eP eS z j) = (∏ i, f (eP i) (z.1 i)) * ∏ i, f (eS i)
        (z.2 i) := by
  rw [← (Equiv.blockIndex eP eS).prod_comp fun j ↦ f j (MeasurableEquiv.blockEquiv eP eS z j),
      Fintype.prod_sum_type]
  simp

/-- The integral of `e^{-nβ u^{2k}} u^h` over `[0, b]^d` is `Z^0(n)` for the block data
`(k|_P, h|_P, k|_{Pᶜ}, h|_{Pᶜ})`. -/
theorem NormalCrossing.integral_cube_eq_blockIntegral₀ (k h : Fin d → ℕ) (b β n : ℝ) :
    ∫ u in cube d b, Real.exp (-(n * β * ∏ j, u j ^ (2 * k j))) * ∏ j, u j ^ (h j : ℝ)
      = NormalCrossing.blockIntegral₀ (fun i ↦ k (eP i)) (fun i ↦ (h (eP i) : ℝ)) (fun i ↦ k (eS i))
          (fun i ↦ (h (eS i) : ℝ)) b β 0 n := by
  rw [← (MeasurableEquiv.blockEquiv_measurePreserving eP eS).setIntegral_preimage_emb
    (MeasurableEquiv.blockEquiv eP eS).measurableEmbedding,
        MeasurableEquiv.blockEquiv_preimage_cube, NormalCrossing.blockIntegral₀]
  congr 1
  funext z
  simp only [Real.rpow_zero, one_mul, potential, NormalCrossing.monomialWeight]
  rw [MeasurableEquiv.prod_blockEquiv eP eS fun j x ↦ x ^ (2 * k j), MeasurableEquiv.prod_blockEquiv
      eP eS fun j x ↦ x ^ (h j : ℝ)]

end Block

end SingularLearningTheory
