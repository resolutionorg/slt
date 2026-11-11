/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Laplace Doubling
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace MeasureTheory

section Doubling

variable {W : Type*} [MeasurableSpace W] {ν : Measure W} [IsFiniteMeasure ν]

/-- The relative-fluctuation bound `√n |Kₙ − K| ≤ L √K` gives the two-sided exponent bounds
`½K − L²/(2n) ≤ Kₙ ≤ (3/2)K + L²/(2n)` (Young's inequality). -/
private theorem Kn_bounds_of_relative_fluctuation {K Kn : ℝ} (hK0 : 0 ≤ K) {n : ℝ} (hn : 0 < n)
    {L : ℝ} (h : Real.sqrt n * |Kn - K| ≤ L * Real.sqrt K) :
    K / 2 - L ^ 2 / (2 * n) ≤ Kn ∧ Kn ≤ 3 / 2 * K + L ^ 2 / (2 * n) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hsK : Real.sqrt K ^ 2 = K := Real.sq_sqrt hK0
  have hsn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  -- `|Kₙ − K| ≤ (L/√n) √K ≤ ½ K + L²/(2n)`
  have hAM : L * Real.sqrt K ≤ Real.sqrt n * (K / 2 + L ^ 2 / (2 * n)) := by
    have h0 : 0 ≤ (Real.sqrt n * Real.sqrt K - L) ^ 2 := sq_nonneg _
    have e : Real.sqrt n * (K / 2 + L ^ 2 / (2 * n))
        = (Real.sqrt n ^ 2 * Real.sqrt K ^ 2 + L ^ 2) / (2 * Real.sqrt n) := by
      rw [hsK, hsn2]
      field_simp
      rw [hsn2]
    rw [e, le_div_iff₀ (by positivity)]
    nlinarith [h0]
  have hb : |Kn - K| ≤ K / 2 + L ^ 2 / (2 * n) := by
    have := h.trans hAM
    exact le_of_mul_le_mul_left this hsn
  constructor
  · linarith [(abs_le.mp hb).1]
  · linarith [(abs_le.mp hb).2]

/-- **The Gibbs measure of an exponent** `G`: `e^{−G} ν / Z`, `Z = ∫ e^{−G} dν`. The tempered
posterior is the case `G = nβKₙ`, the tilted posteriors are `G = nβKₙ + σ f(Xᵢ,·)`. -/
@[expose] noncomputable def Measure.expMeasure (ν : Measure W) (G : W → ℝ) : Measure W :=
  (ENNReal.ofReal (∫ w, Real.exp (-G w) ∂ν))⁻¹
    • ν.withDensity fun w ↦ ENNReal.ofReal (Real.exp (-G w))

omit [IsFiniteMeasure ν] in
theorem integral_expMeasure (ν : Measure W) {G : W → ℝ} (hGm : Measurable G) (g : W → ℝ)
    (hZ : 0 < ∫ w, Real.exp (-G w) ∂ν) :
    ∫ w, g w ∂Measure.expMeasure ν G = (∫ w, g w * Real.exp (-G w) ∂ν) / ∫ w, Real.exp (-G w) ∂ν :=
        by
  have hem : Measurable fun w ↦ Real.exp (-G w) := hGm.neg.exp
  unfold Measure.expMeasure
  rw [integral_smul_measure g, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ.le]
  change ((∫ w, Real.exp (-G w) ∂ν)⁻¹)
    • ∫ w, g w ∂ν.withDensity (fun w ↦ ((Real.toNNReal (Real.exp (-G w)) : NNReal) : ℝ≥0∞)) = _
  rw [integral_withDensity_eq_integral_smul hem.real_toNNReal]
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le,
    div_eq_inv_mul]
  simp_rw [mul_comm (Real.exp _) (g _)]

omit [IsFiniteMeasure ν] in
theorem isProbabilityMeasure_expMeasure (ν : Measure W) [SFinite ν] {G : W → ℝ}
    (hint : Integrable (fun w ↦ Real.exp (-G w)) ν) (hZ : 0 < ∫ w, Real.exp (-G w) ∂ν) :
    IsProbabilityMeasure (Measure.expMeasure ν G) := by
  constructor
  unfold Measure.expMeasure
  rw [Measure.smul_apply, withDensity_apply' _ univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun w ↦ (Real.exp_pos _).le),
    smul_eq_mul, ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr hZ).ne' ENNReal.ofReal_ne_top]

omit [IsFiniteMeasure ν] in
theorem integrable_expMeasure (ν : Measure W) {G : W → ℝ} (hGm : Measurable G)
    (hZ : 0 < ∫ w, Real.exp (-G w) ∂ν) {g : W → ℝ}
    (hg : Integrable (fun w ↦ g w * Real.exp (-G w)) ν) : Integrable g (Measure.expMeasure ν G) :=
        by
  have hem : Measurable fun w ↦ Real.exp (-G w) := hGm.neg.exp
  unfold Measure.expMeasure
  rw [integrable_smul_measure (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_pos.mpr hZ).ne')]
  change Integrable g (ν.withDensity fun w ↦ ((Real.toNNReal (Real.exp (-G w)) : NNReal) : ℝ≥0∞))
  rw [integrable_withDensity_iff_integrable_smul hem.real_toNNReal]
  refine hg.congr (Eventually.of_forall fun w ↦ ?_)
  simp only [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (Real.exp_pos _).le]
  ring


/-- **The Laplace doubling estimate for a Gibbs ratio.** For a finite measure `ν`, `K ≥ 0` and
an exponent `G` (the tempered empirical loss `nβKₙ`, possibly tilted) with
`nβ(½K) − c ≤ G ≤ nβ(3/2 K) + c` `ν`-a.e., if the Laplace ratio is bounded,
`∫ e^{−nβK/4} dν ≤ D ∫ e^{−3nβK/2} dν`, then

`n ∫ K e^{−G} dν / ∫ e^{−G} dν ≤ (4/β) log D + (8/β) c`

(Jensen for `exp` under the Gibbs measure `e^{−G} ν / Z`: `e^{(nβ/4) E[K]} ≤ E[e^{nβK/4}]
≤ e^{2c} J(nβ/4)/J(3nβ/2) ≤ D e^{2c}`). -/
theorem _root_.SingularLearningTheory.BayesGibbs.posterior_ratio_K_le {K G : W → ℝ}
    (hKm : Measurable K) (hGm : Measurable G)
    (hK0 : ∀ w, 0 ≤ K w) {n β c D : ℝ} (hn : 0 < n) (hβ : 0 < β) (hD : 1 ≤ D)
    (hlow : ∀ᵐ w ∂ν, n * β * (K w / 2) - c ≤ G w)
    (hup : ∀ᵐ w ∂ν, G w ≤ n * β * (3 / 2 * K w) + c)
    (hLD : ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν
      ≤ D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν)
    (hZ : 0 < ∫ w, Real.exp (-G w) ∂ν) (hint : Integrable (fun w ↦ K w * Real.exp (-G w)) ν)
    (hintG : Integrable (fun w ↦ Real.exp (-G w)) ν)
    (hintE : Integrable (fun w ↦ Real.exp (n * β / 4 * K w) * Real.exp (-G w)) ν) :
    n * ((∫ w, K w * Real.exp (-G w) ∂ν) / ∫ w, Real.exp (-G w) ∂ν)
      ≤ 4 / β * Real.log D + 8 / β * c := by
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hZ
  have hD0 : 0 < D := by linarith
  -- the two Laplace integrals are positive
  have hexpint : ∀ t : ℝ, 0 ≤ t → Integrable (fun w ↦ Real.exp (-(t * K w))) ν := fun t ht ↦
    Integrable.of_bound ((hKm.const_mul t).neg.exp).aestronglyMeasurable 1
      (Eventually.of_forall fun w ↦ by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (by nlinarith [hK0 w]))
  have hexppos : ∀ t : ℝ, 0 ≤ t → 0 < ∫ w, Real.exp (-(t * K w)) ∂ν := fun t ht ↦ by
    rw [integral_pos_iff_support_of_nonneg (fun w ↦ (Real.exp_pos _).le) (hexpint t ht)]
    have : Function.support (fun w ↦ Real.exp (-(t * K w))) = univ :=
      eq_univ_of_forall fun w ↦ (Real.exp_pos _).ne'
    rw [this]
    exact Measure.measure_univ_pos.mpr hν0
  have hJ1 := hexppos (n * β / 4) (by positivity)
  have hJ2 := hexppos (3 * n * β / 2) (by positivity)
  -- the Gibbs measure
  have hPi : IsProbabilityMeasure (Measure.expMeasure ν G) := isProbabilityMeasure_expMeasure ν
      hintG hZ
  have hφi : Integrable (fun w ↦ n * β / 4 * K w) (Measure.expMeasure ν G) := by
    refine integrable_expMeasure ν hGm hZ ((hint.const_mul (n * β / 4)).congr
      (Eventually.of_forall fun w ↦ ?_))
    ring
  have hei : Integrable (Real.exp ∘ fun w ↦ n * β / 4 * K w) (Measure.expMeasure ν G) :=
    integrable_expMeasure ν hGm hZ hintE
  have hJ := convexOn_exp.map_integral_le (μ := Measure.expMeasure ν G)
      Real.continuous_exp.continuousOn
    isClosed_univ (Eventually.of_forall fun _ ↦ mem_univ _) hφi hei
  rw [integral_expMeasure ν hGm _ hZ, integral_expMeasure ν hGm _ hZ] at hJ
  have e1 : ∫ w, n * β / 4 * K w * Real.exp (-G w) ∂ν
      = n * β / 4 * ∫ w, K w * Real.exp (-G w) ∂ν := by
    rw [← integral_const_mul]
    congr 1
    funext w
    ring
  rw [e1, mul_div_assoc] at hJ
  -- the numerator and denominator bounds
  have hnum : ∫ w, Real.exp (n * β / 4 * K w) * Real.exp (-G w) ∂ν
      ≤ Real.exp c * ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae hintE ((hexpint _ (by positivity)).const_mul _) ?_
    filter_upwards [hlow] with w hw
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  have hden : Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν
      ≤ ∫ w, Real.exp (-G w) ∂ν := by
    rw [← integral_const_mul]
    refine integral_mono_ae ((hexpint _ (by positivity)).const_mul _) hintG ?_
    filter_upwards [hup] with w hw
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  -- `E_Π[e^{nβK/4}] ≤ D e^{2c}`
  have hratio : (∫ w, Real.exp (n * β / 4 * K w) * Real.exp (-G w) ∂ν)
      / ∫ w, Real.exp (-G w) ∂ν ≤ D * Real.exp (2 * c) := by
    have hden' : 0 < Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν :=
      mul_pos (Real.exp_pos _) hJ2
    calc (∫ w, Real.exp (n * β / 4 * K w) * Real.exp (-G w) ∂ν) / ∫ w, Real.exp (-G w) ∂ν
        ≤ (Real.exp c * ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν) / ∫ w, Real.exp (-G w) ∂ν :=
          div_le_div_of_nonneg_right hnum hZ.le
      _ ≤ (Real.exp c * ∫ w, Real.exp (-(n * β / 4 * K w)) ∂ν)
          / (Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :=
          div_le_div_of_nonneg_left (mul_nonneg (Real.exp_pos _).le hJ1.le) hden' hden
      _ ≤ (Real.exp c * (D * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν))
          / (Real.exp (-c) * ∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν) :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLD (Real.exp_pos _).le) hden'.le
      _ = D * Real.exp (2 * c) := by
          have hEE : Real.exp c * Real.exp (-c) = 1 := by
            rw [← Real.exp_add]
            simp
          have h2c : Real.exp (2 * c) = Real.exp c * Real.exp c := by
            rw [← Real.exp_add]
            ring_nf
          rw [h2c, div_eq_iff (mul_ne_zero (Real.exp_pos _).ne' hJ2.ne')]
          linear_combination (-(D * (∫ w, Real.exp (-(3 * n * β / 2 * K w)) ∂ν)
            * Real.exp c)) * hEE
  -- take logarithms
  have hlog : n * β / 4 * ((∫ w, K w * Real.exp (-G w) ∂ν) / ∫ w, Real.exp (-G w) ∂ν)
      ≤ Real.log D + 2 * c := by
    have h := hJ.trans hratio
    have h2 := Real.log_le_log (Real.exp_pos _) h
    rwa [Real.log_exp, Real.log_mul hD0.ne' (Real.exp_pos _).ne', Real.log_exp] at h2
  calc n * ((∫ w, K w * Real.exp (-G w) ∂ν) / ∫ w, Real.exp (-G w) ∂ν)
      = 4 / β * (n * β / 4 * ((∫ w, K w * Real.exp (-G w) ∂ν) / ∫ w, Real.exp (-G w) ∂ν)) := by
        field_simp
    _ ≤ 4 / β * (Real.log D + 2 * c) := mul_le_mul_of_nonneg_left hlog (by positivity)
    _ = 4 / β * Real.log D + 8 / β * c := by ring

end Doubling

end MeasureTheory
