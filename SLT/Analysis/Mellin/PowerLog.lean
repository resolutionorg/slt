/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.Mellin.Strip
public import SLT.SingularIntegrals.NormalCrossing
public import SLT.SingularIntegrals.Transforms
import Mathlib.Analysis.Complex.Convex

/-!
# The power-log Mellin integral

The real integral and its integrability are already proved in `NormalCrossing`.
Holomorphy on the half-plane of convergence and the identity principle extend that
formula to complex exponents, giving the pole of order `m` in [Wat09, §4.3].
-/

public section

open MeasureTheory Set Filter Topology Complex

namespace SingularLearningTheory.MellinAnalysis

private theorem powerLog_weighted_integrable
    (lam b r : ℝ) (hb : 0 < b) (hr : -lam < r) (n : ℕ) :
    IntegrableOn
      (fun t ↦ (Ioo 0 b).indicator
        (fun t ↦ t ^ (lam - 1) * Real.log (b / t) ^ n) t * t ^ r)
      (Ioi 0) := by
  have hg := integrableOn_rpow_mul_log_pow_Ioo
    (s := lam + r) (by linarith) hb n
  have heq :
      (fun t ↦ (Ioo 0 b).indicator
        (fun t ↦ t ^ (lam - 1) * Real.log (b / t) ^ n) t * t ^ r)
      = (Ioo 0 b).indicator
          (fun t ↦ t ^ (lam + r - 1) * Real.log (b / t) ^ n) := by
    funext t
    by_cases ht : t ∈ Ioo 0 b
    · simp only [indicator_of_mem ht]
      rw [show lam + r - 1 = (lam - 1) + r by ring, Real.rpow_add ht.1]
      ring
    · simp [indicator_of_notMem ht]
  rw [heq]
  exact (hg.integrable_indicator measurableSet_Ioo).integrableOn

private theorem eqOn_re_gt_of_eq_on_reals
    {F G : ℂ → ℂ} (a : ℝ)
    (hF : DifferentiableOn ℂ F {w : ℂ | a < w.re})
    (hG : DifferentiableOn ℂ G {w : ℂ | a < w.re})
    (hreal : ∀ r : ℝ, a < r → F (r : ℂ) = G (r : ℂ)) :
    EqOn F G {w : ℂ | a < w.re} := by
  have hopen : IsOpen {w : ℂ | a < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hpoint : ((a + 1 : ℝ) : ℂ) ∈ {w : ℂ | a < w.re} := by
    simp only [mem_ofPred_eq, Complex.ofReal_re]
    linarith
  apply (hF.analyticOnNhd hopen).eqOn_of_preconnected_of_mem_closure
    (hG.analyticOnNhd hopen) (convex_halfSpace_re_gt a).isPreconnected hpoint
  rw [Metric.mem_closure_iff]
  intro ε hε
  refine ⟨((a + 1 + ε / 2 : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
  · exact hreal _ (by linarith)
  · simp only [mem_singleton_iff]
    intro h
    have h' := congrArg Complex.re h
    simp only [Complex.ofReal_re] at h'
    linarith
  · rw [dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      show (a + 1) - (a + 1 + ε / 2) = -(ε / 2) by ring,
      abs_neg, abs_of_pos (half_pos hε)]
    linarith

/-- The Mellin transform of a truncated power times a logarithmic power ([Wat09, §4.3]).
The base `b` is positive, and `Re z > −λ` is exactly the convergence half-plane. -/
theorem mellinTransform_power_log
    (lam b : ℝ) (hb : 0 < b) (m : ℕ) (hm : 1 ≤ m)
    (z : ℂ) (hz : -lam < z.re) :
    mellinTransform
      ((Ioo 0 b).indicator (fun t ↦ t ^ (lam - 1) * Real.log (b / t) ^ (m - 1))) z
      = ((m - 1).factorial : ℂ) * (b : ℂ) ^ (z + (lam : ℂ)) /
        (z + (lam : ℂ)) ^ m := by
  let f : ℝ → ℝ := (Ioo 0 b).indicator
    (fun t ↦ t ^ (lam - 1) * Real.log (b / t) ^ (m - 1))
  let G : ℂ → ℂ := fun w ↦ ((m - 1).factorial : ℂ) * (b : ℂ) ^ (w + (lam : ℂ)) /
    (w + (lam : ℂ)) ^ m
  have hF : DifferentiableOn ℂ (mellinTransform f) {w : ℂ | -lam < w.re} := by
    intro w hw
    change -lam < w.re at hw
    let a := (-lam + w.re) / 2
    let c := w.re + 1
    have ha : -lam < a := by dsimp [a]; linarith [hw]
    have hc : -lam < c := by dsimp [c]; linarith [hw]
    have hstrip := mellinTransform_differentiableOn_strip f a c
      (powerLog_weighted_integrable lam b a hb ha (m - 1))
      (powerLog_weighted_integrable lam b c hb hc (m - 1))
    have hopen : IsOpen {v : ℂ | a < v.re ∧ v.re < c} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter
        (isOpen_lt Complex.continuous_re continuous_const)
    have hw' : w ∈ {v : ℂ | a < v.re ∧ v.re < c} := by
      dsimp [a, c]
      constructor <;> linarith [hw]
    exact (hstrip.differentiableAt (hopen.mem_nhds hw')).differentiableWithinAt
  have hG : DifferentiableOn ℂ G {w : ℂ | -lam < w.re} := by
    intro w hw
    change -lam < w.re at hw
    have hw0 : w + (lam : ℂ) ≠ 0 := by
      intro h
      have h' := congrArg Complex.re h
      simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at h'
      linarith [hw]
    exact ((((differentiableAt_id.add_const (lam : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne'))).const_mul ((m - 1).factorial : ℂ)).div
      ((differentiableAt_id.add_const (lam : ℂ)).pow m)
      (pow_ne_zero m hw0)).differentiableWithinAt
  have hreal : ∀ r : ℝ, -lam < r → mellinTransform f (r : ℂ) = G (r : ℂ) := by
    intro r hr
    have heq : (fun t : ℝ ↦ (t : ℂ) ^ (r : ℂ) * (f t : ℂ))
        = (Ioo 0 b).indicator
          (fun t ↦ ((t ^ (lam + r - 1) * Real.log (b / t) ^ (m - 1) : ℝ) : ℂ)) := by
      funext t
      by_cases ht : t ∈ Ioo 0 b
      · simp only [f, indicator_of_mem ht]
        rw [← Complex.ofReal_cpow ht.1.le, ← Complex.ofReal_mul,
          show lam + r - 1 = r + (lam - 1) by ring, Real.rpow_add ht.1]
        congr 1
        ring
      · simp [f, indicator_of_notMem ht]
    rw [mellinTransform, heq, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, integral_complex_ofReal,
      integral_rpow_mul_log_pow hb (by linarith : 0 < lam + r) (m - 1)]
    dsimp [G]
    rw [show m - 1 + 1 = m by omega]
    push_cast
    rw [Complex.ofReal_cpow hb.le]
    simp [add_comm]
  exact eqOn_re_gt_of_eq_on_reals (-lam) hF hG hreal hz

end SingularLearningTheory.MellinAnalysis
