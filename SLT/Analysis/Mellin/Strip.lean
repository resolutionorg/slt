/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Transforms
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Holomorphy on a strip of absolute Mellin convergence

Weighted integrability at two real exponents dominates the Mellin integrand and its
complex derivative on every smaller strip. Unlike pointwise power-growth conditions,
these hypotheses allow arbitrary integrable singularities in the original function.
-/

public section

open MeasureTheory Set Filter Topology Complex

namespace SingularLearningTheory.MellinAnalysis

private theorem rpow_le_endpoints {t a b c : ℝ} (ht : 0 < t)
    (hac : a ≤ c) (hcb : c ≤ b) : t ^ c ≤ t ^ a + t ^ b := by
  rcases le_or_gt 1 t with h | h
  · exact le_add_of_nonneg_of_le (Real.rpow_nonneg ht.le _)
      (Real.rpow_le_rpow_of_exponent_le h hcb)
  · exact le_add_of_le_of_nonneg (Real.rpow_le_rpow_of_exponent_ge ht h.le hac)
      (Real.rpow_nonneg ht.le _)

private theorem log_mul_rpow_le {t a b c v : ℝ} (ht : 0 < t) (hv : 0 < v)
    (hac : a + v ≤ c) (hcb : c + v ≤ b) :
    |Real.log t| * t ^ c ≤ (t ^ a + t ^ b) / v := by
  rcases le_or_gt 1 t with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    calc Real.log t * t ^ c ≤ t ^ v / v * t ^ c :=
          mul_le_mul_of_nonneg_right (Real.log_le_rpow_div ht.le hv)
            (Real.rpow_nonneg ht.le _)
      _ = t ^ (c + v) / v := by rw [Real.rpow_add ht]; ring
      _ ≤ (t ^ a + t ^ b) / v := by
        gcongr
        exact le_add_of_nonneg_of_le (Real.rpow_nonneg ht.le _)
          (Real.rpow_le_rpow_of_exponent_le h hcb)
  · rw [abs_of_nonpos (Real.log_nonpos ht.le h.le)]
    have hlog : -Real.log t ≤ t ^ (-v) / v := by
      have := Real.neg_rpow_div_le_log ht.le hv
      rw [neg_div] at this
      linarith
    calc -Real.log t * t ^ c ≤ t ^ (-v) / v * t ^ c :=
          mul_le_mul_of_nonneg_right hlog (Real.rpow_nonneg ht.le _)
      _ = t ^ (c - v) / v := by rw [sub_eq_add_neg, Real.rpow_add ht]; ring
      _ ≤ (t ^ a + t ^ b) / v := by
        gcongr
        exact le_add_of_le_of_nonneg
          (Real.rpow_le_rpow_of_exponent_ge ht h.le (by linarith))
          (Real.rpow_nonneg ht.le _)

/-- The Mellin transform is complex differentiable between two exponents of absolute
convergence ([Wat09, §4.3]). -/
theorem mellinTransform_differentiableOn_strip
    (f : ℝ → ℝ) (a b : ℝ)
    (ha : IntegrableOn (fun t ↦ f t * t ^ a) (Ioi 0))
    (hb : IntegrableOn (fun t ↦ f t * t ^ b) (Ioi 0)) :
    DifferentiableOn ℂ (mellinTransform f) {z : ℂ | a < z.re ∧ z.re < b} := by
  have hf : AEStronglyMeasurable f (volume.restrict (Ioi 0)) := by
    have hw : AEStronglyMeasurable (fun t : ℝ ↦ t ^ a) (volume.restrict (Ioi 0)) :=
      (measurable_id.pow_const a).aestronglyMeasurable
    refine (ha.1.div₀ hw).congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_div_cancel_right₀ (f t) (Real.rpow_pos_of_pos ht a).ne'
  have hfc := Complex.continuous_ofReal.comp_aestronglyMeasurable hf
  have hmeas (z : ℂ) : AEStronglyMeasurable
      (fun t : ℝ ↦ (t : ℂ) ^ z * f t) (volume.restrict (Ioi 0)) :=
    (measurable_ofReal_cpow z).aestronglyMeasurable.mul hfc
  have hint {z : ℂ} (haz : a ≤ z.re) (hzb : z.re ≤ b) :
      IntegrableOn (fun t : ℝ ↦ (t : ℂ) ^ z * f t) (Ioi 0) := by
    refine (ha.norm.add hb.norm).mono' (hmeas z) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Pi.add_apply, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos ht a),
      abs_of_pos (Real.rpow_pos_of_pos ht b)]
    nlinarith [mul_le_mul_of_nonneg_right (rpow_le_endpoints ht haz hzb) (abs_nonneg (f t))]
  intro z hz
  obtain ⟨v, hv, hza, hzb⟩ : ∃ v : ℝ, 0 < v ∧ a + 2 * v < z.re ∧ z.re + 2 * v < b := by
    have hleft : 0 < z.re - a := sub_pos.mpr hz.1
    have hright : 0 < b - z.re := sub_pos.mpr hz.2
    refine ⟨min (z.re - a) (b - z.re) / 4, by positivity, ?_, ?_⟩
    · have := min_le_left (z.re - a) (b - z.re)
      have : a < z.re := hz.1
      linarith
    · have := min_le_right (z.re - a) (b - z.re)
      have : z.re < b := hz.2
      linarith
  let F : ℂ → ℝ → ℂ := fun z t ↦ (t : ℂ) ^ z * f t
  let F' : ℂ → ℝ → ℂ := fun z t ↦ (t : ℂ) ^ z * Real.log t * f t
  let bound : ℝ → ℝ := fun t ↦ (‖f t * t ^ a‖ + ‖f t * t ^ b‖) / v
  have hm' : AEStronglyMeasurable (F' z) (volume.restrict (Ioi 0)) :=
    ((measurable_ofReal_cpow z).aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp Real.measurable_log).aestronglyMeasurable).mul hfc
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi 0),
      ∀ w ∈ Metric.ball z v, ‖F' w t‖ ≤ bound t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w hw
    have hdist : |w.re - z.re| < v :=
      (Complex.abs_re_le_norm (w - z)).trans_lt (by simpa [dist_eq_norm] using hw)
    have hlo : a + v ≤ w.re := by have := (abs_lt.mp hdist).1; linarith
    have hhi : w.re + v ≤ b := by have := (abs_lt.mp hdist).2; linarith
    have key := mul_le_mul_of_nonneg_right (log_mul_rpow_le ht hv hlo hhi)
      (abs_nonneg (f t))
    simp only [F', bound, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos ht a), abs_of_pos (Real.rpow_pos_of_pos ht b)]
    calc t ^ w.re * |Real.log t| * |f t|
        = (|Real.log t| * t ^ w.re) * |f t| := by ring
      _ ≤ ((t ^ a + t ^ b) / v) * |f t| := key
      _ = (|f t| * t ^ a + |f t| * t ^ b) / v := by ring
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi 0), ∀ w ∈ Metric.ball z v,
      HasDerivAt (fun z ↦ F z t) (F' w t) w := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht w _
    have ht' : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
    convert ((hasDerivAt_id' w).const_cpow (Or.inl ht')).mul_const (f t : ℂ) using 1
    simp [F', Complex.ofReal_log ht.le]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Metric.ball_mem_nhds z hv) (Eventually.of_forall hmeas) (hint hz.1.le hz.2.le)
    hm' hbound ((ha.norm.add hb.norm).div_const v) hdiff).2.differentiableAt.differentiableWithinAt

end SingularLearningTheory.MellinAnalysis
