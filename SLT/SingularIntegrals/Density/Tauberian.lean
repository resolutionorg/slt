/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Invariance
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Monotone reduced densities

A power-logarithmic volume asymptotic determines an antitone reduced density.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.SliceDensity

/-- The normalized volume limit under dilation of its level. -/
private theorem tendsto_volume_dilate {V : ℝ → ℝ} {lam C : ℝ} {m : ℕ}
    (hV : Tendsto (fun t ↦ V t / (t ^ lam * (-Real.log t) ^ (m - 1)))
      (𝓝[>] 0) (𝓝 C)) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t ↦ V (c * t) / (t ^ lam * (-Real.log t) ^ (m - 1)))
      (𝓝[>] 0) (𝓝 (C * c ^ lam)) := by
  have hd : Tendsto (fun t : ℝ ↦ c * t) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have ht : Tendsto (fun t : ℝ ↦ c * t) (𝓝 (0 : ℝ)) (𝓝 (c * 0)) :=
        (tendsto_const_nhds.mul tendsto_id)
      simpa only [mul_zero] using ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht using mul_pos hc ht
  have hr := SingularLearningTheory.tendsto_llcScale_div_const_ratio
    (lam := lam) (theta := ((m - 1 : ℕ) : ℝ) + 1) (inv_pos.mpr hc)
  have hr' : Tendsto (fun t : ℝ ↦
      ((c * t) ^ lam * (-Real.log (c * t)) ^ (m - 1)) /
        (t ^ lam * (-Real.log t) ^ (m - 1))) (𝓝[>] 0) (𝓝 (c ^ lam)) := by
    simpa [SingularLearningTheory.llcScale, Real.rpow_natCast, div_inv_eq_mul, mul_comm,
      Real.inv_rpow hc.le, ← Real.rpow_neg hc.le] using hr
  refine ((hV.comp hd).mul hr').congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (div_pos one_pos hc)] with t ht
  have hct : 0 < c * t := mul_pos hc ht.1
  have hct1 : c * t < 1 := by nlinarith [(lt_div_iff₀ hc).mp ht.2]
  have hn : (c * t) ^ lam * (-Real.log (c * t)) ^ (m - 1) ≠ 0 :=
    (mul_pos (Real.rpow_pos_of_pos hct _) (pow_pos (neg_pos.mpr (Real.log_neg hct hct1)) _)).ne'
  dsimp
  exact div_mul_div_cancel₀ hn

section Tauberian

variable {v G : ℝ → ℝ≥0∞} {lam : ℝ} (hlam : 0 < lam)
  (hv : ∀ s, 0 < s → v s = ENNReal.ofReal (s ^ (lam - 1)) * G s)
  (hG : ∀ s t, 0 < s → s ≤ t → G t ≤ G s)
include hlam hv hG

omit hv hG in
/-- `∫_{(a,b]} s^{λ−1} ds = (b^λ − a^λ)/λ` in `ℝ≥0∞`. -/
private theorem lintegral_Ioc_ofReal_rpow {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ s in Ioc a b, ENNReal.ofReal (s ^ (lam - 1)) =
      ENNReal.ofReal ((b ^ lam - a ^ lam) / lam) := by
  have hint : IntegrableOn (fun s : ℝ ↦ s ^ (lam - 1)) (Ioc a b) :=
    (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦
      Real.rpow_nonneg (by linarith [hs.1]) _)]
  congr 1
  rw [← intervalIntegral.integral_of_le hab, integral_rpow (Or.inl (by linarith)), sub_add_cancel]

/-- **Monotone-density lower bound**: `G(b) (b^λ − a^λ)/λ ≤ ∫_{(a,b]} v`. -/
private theorem lintegral_Ioc_ge_of_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    G b * ENNReal.ofReal ((b ^ lam - a ^ lam) / lam) ≤ ∫⁻ s in Ioc a b, v s := by
  calc G b * ENNReal.ofReal ((b ^ lam - a ^ lam) / lam)
      = ∫⁻ s in Ioc a b, ENNReal.ofReal (s ^ (lam - 1)) * G b := by
        rw [lintegral_mul_const _ (f := fun s ↦ ENNReal.ofReal (s ^ (lam - 1))) (by fun_prop),
          lintegral_Ioc_ofReal_rpow hlam ha hab, mul_comm]
    _ ≤ ∫⁻ s in Ioc a b, v s := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs ↦ ?_
        have hs0 : 0 < s := ha.trans hs.1
        rw [hv s hs0]
        exact mul_le_mul' le_rfl (hG s b hs0 hs.2)

/-- **Monotone-density upper bound**: `∫_{(a,b]} v ≤ G(a) (b^λ − a^λ)/λ`. -/
private theorem lintegral_Ioc_le_of_antitone {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫⁻ s in Ioc a b, v s ≤ G a * ENNReal.ofReal ((b ^ lam - a ^ lam) / lam) := by
  calc ∫⁻ s in Ioc a b, v s
      ≤ ∫⁻ s in Ioc a b, ENNReal.ofReal (s ^ (lam - 1)) * G a := by
        refine setLIntegral_mono' measurableSet_Ioc fun s hs ↦ ?_
        have hs0 : 0 < s := ha.trans hs.1
        rw [hv s hs0]
        exact mul_le_mul' le_rfl (hG a s ha hs.1.le)
    _ = G a * ENNReal.ofReal ((b ^ lam - a ^ lam) / lam) := by
        rw [lintegral_mul_const _ (f := fun s ↦ ENNReal.ofReal (s ^ (lam - 1))) (by fun_prop),
          lintegral_Ioc_ofReal_rpow hlam ha hab, mul_comm]

omit hlam hv hG in
/-- The integral over `(−∞, b)` splits at `a`. -/
private theorem lintegral_Iio_eq_add_Ioc (a b : ℝ) (hab : a ≤ b) :
    ∫⁻ s in Iio b, v s = (∫⁻ s in Iio a, v s) + ∫⁻ s in Ioc a b, v s := by
  calc ∫⁻ s in Iio b, v s = ∫⁻ s in Iic b, v s := setLIntegral_congr Iio_ae_eq_Iic
    _ = ∫⁻ s in Iic a ∪ Ioc a b, v s := by rw [Iic_union_Ioc_eq_Iic hab]
    _ = (∫⁻ s in Iic a, v s) + ∫⁻ s in Ioc a b, v s :=
        lintegral_union measurableSet_Ioc ((Iic_disjoint_Ioi le_rfl).mono_right Ioc_subset_Ioi_self)
    _ = (∫⁻ s in Iio a, v s) + ∫⁻ s in Ioc a b, v s := by
        rw [setLIntegral_congr (Iio_ae_eq_Iic (a := a))]

/-- Finiteness of an antitone reduced density from finiteness of the volume. -/
private theorem redDens_ne_top_of_antitone (hVfin : ∀ t, 0 < t → ∫⁻ s in Iio t, v s ≠ ⊤) {t : ℝ}
    (ht : 0 < t) : G t ≠ ⊤ := by
  intro h
  have hle := lintegral_Ioc_ge_of_antitone hlam hv hG (a := t / 2) (b := t) (by positivity)
    (by linarith)
  rw [h, ENNReal.top_mul] at hle
  · exact hVfin (t + 1) (by linarith) (top_le_iff.mp (hle.trans (lintegral_mono_set
      (Ioc_subset_Iic_self.trans (Iic_subset_Iio.mpr (by linarith))))))
  · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    have : (t / 2) ^ lam < t ^ lam := Real.rpow_lt_rpow (by positivity) (by linarith) hlam
    exact div_pos (by linarith) hlam

/-- **Monotone-density Tauberian theorem**: if `G` is antitone on `(0, ∞)`, `v(s) = s^{λ−1} G(s)`
and `V(t) = ∫_{(−∞,t)} v` has the normalised limit `C` at `(λ, m)`, then
`G(t)/(−log t)^{m−1} → λ C` as `t → 0⁺`. -/
theorem _root_.tendsto_toReal_div_of_antitone {m : ℕ} {C : ℝ}
    (hVfin : ∀ t, 0 < t → ∫⁻ s in Iio t, v s ≠ ⊤)
    (hlim : Tendsto (fun t ↦ (∫⁻ s in Iio t, v s).toReal /
      (t ^ lam * (-Real.log t) ^ (m - 1))) (𝓝[>] 0) (𝓝 C)) :
    Tendsto (fun t ↦ (G t).toReal / (-Real.log t) ^ (m - 1)) (𝓝[>] 0) (𝓝 (lam * C)) := by
  set V : ℝ → ℝ := fun t ↦ (∫⁻ s in Iio t, v s).toReal with hV_def
  have hκ : 0 < 1 - (1 / 2 : ℝ) ^ lam := by
    have := Real.rpow_lt_one (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hlam
    linarith
  have hκ' : 0 < (2 : ℝ) ^ lam - 1 := by
    have := Real.one_lt_rpow (x := (2 : ℝ)) (by norm_num) hlam
    linarith
  -- finiteness of `G` on `(0, ∞)`
  have hGfin : ∀ t, 0 < t → G t ≠ ⊤ := by
    intro t ht h
    have hle := lintegral_Ioc_ge_of_antitone hlam hv hG (a := t / 2) (b := t) (by positivity)
      (by linarith)
    rw [h, ENNReal.top_mul] at hle
    · exact hVfin (t + 1) (by linarith) (top_le_iff.mp (hle.trans (lintegral_mono_set
        (Ioc_subset_Iic_self.trans (Iic_subset_Iio.mpr (by linarith))))))
    · rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have : (t / 2) ^ lam < t ^ lam :=
        Real.rpow_lt_rpow (by positivity) (by linarith) hlam
      exact div_pos (by linarith) hlam
  -- the sandwich for `t ∈ (0, 1)`
  have hsand : ∀ t, 0 < t → t < 1 →
      lam * (V (2 * t) - V t) / (((2 : ℝ) ^ lam - 1) * (t ^ lam * (-Real.log t) ^ (m - 1))) ≤
          (G t).toReal / (-Real.log t) ^ (m - 1) ∧
        (G t).toReal / (-Real.log t) ^ (m - 1) ≤
          lam * (V t - V (1 / 2 * t)) /
            ((1 - (1 / 2 : ℝ) ^ lam) * (t ^ lam * (-Real.log t) ^ (m - 1))) := by
    intro t ht ht1
    have hlog : 0 < -Real.log t := by
      have := Real.log_neg ht ht1
      linarith
    have hL : 0 < (-Real.log t) ^ (m - 1) := pow_pos hlog _
    have hT : 0 < t ^ lam := Real.rpow_pos_of_pos ht _
    have hP : (t ^ lam * (-Real.log t) ^ (m - 1)) = t ^ lam * (-Real.log t) ^ (m - 1) := rfl
    have hB1 : ∫⁻ s in Ioc (1 / 2 * t) t, v s ≠ ⊤ :=
      ne_top_of_le_ne_top (hVfin (t + 1) (by linarith)) (lintegral_mono_set
        (Ioc_subset_Iic_self.trans (Iic_subset_Iio.mpr (by linarith))))
    have hB2 : ∫⁻ s in Ioc t (2 * t), v s ≠ ⊤ :=
      ne_top_of_le_ne_top (hVfin (2 * t + 1) (by linarith)) (lintegral_mono_set
        (Ioc_subset_Iic_self.trans (Iic_subset_Iio.mpr (by linarith))))
    -- `V t − V (t/2) = ∫_{(t/2, t]} v` and `V (2t) − V t = ∫_{(t, 2t]} v`
    have hD1 : V t - V (1 / 2 * t) = (∫⁻ s in Ioc (1 / 2 * t) t, v s).toReal := by
      simp only [hV_def]
      rw [lintegral_Iio_eq_add_Ioc (v := v) (1 / 2 * t) t (by linarith),
        ENNReal.toReal_add (hVfin (1 / 2 * t) (by positivity)) hB1]
      ring
    have hD2 : V (2 * t) - V t = (∫⁻ s in Ioc t (2 * t), v s).toReal := by
      simp only [hV_def]
      rw [lintegral_Iio_eq_add_Ioc (v := v) t (2 * t) (by linarith),
        ENNReal.toReal_add (hVfin t ht) hB2]
      ring
    -- the two monotone bounds in real form
    have hup : (G t).toReal * ((t ^ lam - (1 / 2 * t) ^ lam) / lam) ≤ V t - V (1 / 2 * t) := by
      rw [hD1]
      have := lintegral_Ioc_ge_of_antitone hlam hv hG (a := 1 / 2 * t) (b := t) (by positivity)
        (by linarith)
      have h' := ENNReal.toReal_mono hB1 this
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr
        (Real.rpow_le_rpow (by positivity) (by linarith) hlam.le)) hlam.le)] at h'
    have hlo : V (2 * t) - V t ≤ (G t).toReal * (((2 * t) ^ lam - t ^ lam) / lam) := by
      rw [hD2]
      have := lintegral_Ioc_le_of_antitone hlam hv hG (a := t) (b := 2 * t) ht (by linarith)
      have h' := ENNReal.toReal_mono (ENNReal.mul_ne_top (hGfin t ht) ENNReal.ofReal_ne_top) this
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (div_nonneg (sub_nonneg.mpr
        (Real.rpow_le_rpow ht.le (by linarith) hlam.le)) hlam.le)] at h'
    have e1 : t ^ lam - (1 / 2 * t) ^ lam = (1 - (1 / 2 : ℝ) ^ lam) * t ^ lam := by
      rw [Real.mul_rpow (by norm_num) ht.le]; ring
    have e2 : (2 * t) ^ lam - t ^ lam = ((2 : ℝ) ^ lam - 1) * t ^ lam := by
      rw [Real.mul_rpow (by norm_num) ht.le]; ring
    rw [e1] at hup
    rw [e2] at hlo
    constructor
    · rw [hP, div_le_div_iff₀ (by positivity) hL]
      have := mul_le_mul_of_nonneg_right hlo (le_of_lt (mul_pos hlam hL))
      calc lam * (V (2 * t) - V t) * (-Real.log t) ^ (m - 1)
          ≤ (G t).toReal * ((((2 : ℝ) ^ lam - 1) * t ^ lam) / lam) *
              (lam * (-Real.log t) ^ (m - 1)) := by
            linarith
        _ = (G t).toReal * (((2 : ℝ) ^ lam - 1) * (t ^ lam * (-Real.log t) ^ (m - 1))) := by
            field_simp
    · rw [hP, div_le_div_iff₀ hL (by positivity)]
      have := mul_le_mul_of_nonneg_right hup (le_of_lt (mul_pos hlam hL))
      calc (G t).toReal * ((1 - (1 / 2 : ℝ) ^ lam) * (t ^ lam * (-Real.log t) ^ (m - 1)))
          = (G t).toReal * (((1 - (1 / 2 : ℝ) ^ lam) * t ^ lam) / lam) *
              (lam * (-Real.log t) ^ (m - 1)) := by field_simp
        _ ≤ lam * (V t - V (1 / 2 * t)) * (-Real.log t) ^ (m - 1) := by linarith
  -- the limits of the two bounds
  have h2 := tendsto_volume_dilate hlim (c := 2) (by norm_num)
  have hhalf := tendsto_volume_dilate hlim (c := 1 / 2) (by norm_num)
  have hlim' : Tendsto (fun t ↦ V t / (t ^ lam * (-Real.log t) ^ (m - 1))) (𝓝[>] 0) (𝓝 C) := hlim
  have hlo_lim : Tendsto (fun t ↦ lam * (V (2 * t) - V t) /
      (((2 : ℝ) ^ lam - 1) * (t ^ lam * (-Real.log t) ^ (m - 1)))) (𝓝[>] 0) (𝓝 (lam * C)) := by
    have := ((h2.sub hlim').const_mul lam).div_const ((2 : ℝ) ^ lam - 1)
    have heq : lam * (C * 2 ^ lam - C) / (2 ^ lam - 1) = lam * C := by
      rw [div_eq_iff hκ'.ne']; ring
    rw [heq] at this
    refine this.congr fun t ↦ ?_
    rw [← sub_div, ← mul_div_assoc, div_div, mul_comm ((t ^ lam * (-Real.log t) ^ (m - 1)))]
  have hup_lim : Tendsto (fun t ↦ lam * (V t - V (1 / 2 * t)) /
      ((1 - (1 / 2 : ℝ) ^ lam) * (t ^ lam * (-Real.log t) ^ (m - 1)))) (𝓝[>] 0) (𝓝 (lam * C)) := by
    have := ((hlim'.sub hhalf).const_mul lam).div_const (1 - (1 / 2 : ℝ) ^ lam)
    have heq : lam * (C - C * (1 / 2) ^ lam) / (1 - (1 / 2) ^ lam) = lam * C := by
      rw [div_eq_iff hκ.ne']; ring
    rw [heq] at this
    refine this.congr fun t ↦ ?_
    rw [← sub_div, ← mul_div_assoc, div_div, mul_comm ((t ^ lam * (-Real.log t) ^ (m - 1)))]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo_lim hup_lim ?_ ?_
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (hsand t ht.1 ht.2).1
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact (hsand t ht.1 ht.2).2

/-- An antitone reduced density is bounded by its cumulative mass on a dyadic interval. -/
private theorem t_mul_density_le_cumulative
    (hVfin : ∀ t, 0 < t → ∫⁻ s in Iio t, v s ≠ ⊤) {t : ℝ} (ht : 0 < t) :
    t * (v t).toReal ≤ lam / (1 - (1 / 2 : ℝ) ^ lam) * (∫⁻ s in Iio t, v s).toReal := by
  have hκ : 0 < 1 - (1 / 2 : ℝ) ^ lam := by
    have := Real.rpow_lt_one (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num) hlam
    linarith
  have hbound := lintegral_Ioc_ge_of_antitone hlam hv hG (a := t / 2) (b := t)
    (by positivity) (by linarith)
  have hsub : ∫⁻ s in Ioc (t / 2) t, v s ≤ ∫⁻ s in Iio t, v s := by
    rw [setLIntegral_congr (Iio_ae_eq_Iic (a := t))]
    exact lintegral_mono_set Ioc_subset_Iic_self
  have hreal := ENNReal.toReal_mono (hVfin t ht) (hbound.trans hsub)
  have hd : 0 ≤ (t ^ lam - (t / 2) ^ lam) / lam := div_nonneg
    (sub_nonneg.mpr (Real.rpow_le_rpow (by positivity) (by linarith) hlam.le)) hlam.le
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hd] at hreal
  have hdil : (t / 2) ^ lam = (1 / 2 : ℝ) ^ lam * t ^ lam := by
    rw [show t / 2 = (1 / 2 : ℝ) * t by ring, Real.mul_rpow (by norm_num) ht.le]
  rw [hdil] at hreal
  have hprod : t * (v t).toReal = t ^ lam * (G t).toReal := by
    rw [hv t ht, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.rpow_nonneg ht.le _), Real.rpow_sub_one ht.ne']
    field_simp
  rw [hprod]
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hκ).2
  rw [← mul_div_assoc] at hreal
  have := (div_le_iff₀ hlam).mp hreal
  nlinarith

/-- A zero normalized volume coefficient gives a zero normalized density coefficient. -/
theorem _root_.tendsto_t_mul_density_zero {lam₀ : ℝ} {m : ℕ}
    (hVfin : ∀ t, 0 < t → ∫⁻ s in Iio t, v s ≠ ⊤)
    (hlim : Tendsto (fun t ↦ (∫⁻ s in Iio t, v s).toReal /
      (t ^ lam₀ * (-Real.log t) ^ (m - 1))) (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun t ↦ t * (v t).toReal / (t ^ lam₀ * (-Real.log t) ^ (m - 1)))
      (𝓝[>] 0) (𝓝 0) := by
  have hupper := hlim.const_mul (lam / (1 - (1 / 2 : ℝ) ^ lam))
  simp only [mul_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact div_nonneg (mul_nonneg ht.1.le ENNReal.toReal_nonneg)
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (pow_nonneg (neg_nonneg.mpr
        (Real.log_nonpos ht.1.le ht.2.le)) _))
  · filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right (t_mul_density_le_cumulative hlam hv hG hVfin ht.1)
    exact mul_nonneg (Real.rpow_nonneg ht.1.le _) (pow_nonneg (neg_nonneg.mpr
      (Real.log_nonpos ht.1.le ht.2.le)) _)

end Tauberian

end SingularLearningTheory.SliceDensity
