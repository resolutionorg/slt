/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Laplace.Representation
public import SLT.VolumeScaling.Laplace.Scale
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The model-head integral after `u = s·ε` and its integrability

The head of the Laplace representation against the model scale is

  `H(s) = s ∫_{(0, ε₀]} e^{−s·ε} · llcScale λ θ ε dε`.

This file performs the substitution `u = s·ε`:

  `H(s) = s^{−λ} ∫_{(0, s·ε₀]} e^{−u} u^λ (log s − log u)^{θ−1} du`,

and provides the integrability layer the head bounds and the
precise Γ-limit consume: the log-power domination
`(1+|log u|)^β ≤ C·(u^{−δ} + u^δ)` and Gamma-type integrability of
`e^{−u} u^λ (1+|log u|)^β` on `(0, ∞)` for `λ > −1`.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal

namespace Real

open SingularLearningTheory

/-! ## The substitution identity -/

/-- The head integral after `u = s·ε`: for `s > 0`, `ε₀ > 0`,

  `s ∫_{(0,ε₀]} e^{−s·ε} llcScale λ θ ε dε
     = s^{−λ} ∫_{(0, s·ε₀]} e^{−u} u^λ (log s − log u)^{θ−1} du`
(any `ε₀ : ℝ`; for `ε₀ ≤ 0` both sides are zero). -/
theorem _root_.SingularLearningTheory.mul_setIntegral_head_eq_subst {lam theta s ε₀ : ℝ}
    (hs : 0 < s) :
    s * ∫ ε in Ioc (0 : ℝ) ε₀, Real.exp (-(s * ε)) * llcScale lam theta ε
      = s ^ (-lam) * ∫ u in Ioc (0 : ℝ) (s * ε₀),
          Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
  set G : ℝ → ℝ := (Ioc (0 : ℝ) (s * ε₀)).indicator
    (fun u => Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
    with hGdef
  -- The substitution on the indicator-extended integrand.
  have hsub : ∫ ε in Ioi (0 : ℝ), G (s * ε) = s⁻¹ * ∫ u in Ioi (0 : ℝ), G u := by
    have h := integral_comp_mul_left_Ioi G 0 hs
    rw [mul_zero] at h
    rw [h, smul_eq_mul]
  -- Pointwise on `Ioi 0`: `G (s·ε) = s^lam · (head indicator integrand) ε`.
  have hpt : ∀ ε ∈ Ioi (0 : ℝ), G (s * ε)
      = s ^ lam * (Ioc (0 : ℝ) ε₀).indicator
          (fun ε => Real.exp (-(s * ε)) * llcScale lam theta ε) ε := by
    intro ε hε
    rw [mem_Ioi] at hε
    have hmem : s * ε ∈ Ioc (0 : ℝ) (s * ε₀) ↔ ε ∈ Ioc (0 : ℝ) ε₀ := by
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨hε, le_of_mul_le_mul_left h2 hs⟩
      · rintro ⟨h1, h2⟩
        exact ⟨mul_pos hs h1, mul_le_mul_of_nonneg_left h2 hs.le⟩
    by_cases hc : ε ∈ Ioc (0 : ℝ) ε₀
    · rw [hGdef, indicator_of_mem (hmem.mpr hc), indicator_of_mem hc]
      have hlog : Real.log s - Real.log (s * ε) = -Real.log ε := by
        rw [Real.log_mul hs.ne' hε.ne']
        ring
      have hpow : (s * ε) ^ lam = s ^ lam * ε ^ lam :=
        Real.mul_rpow hs.le hε.le
      rw [hlog, hpow, llcScale]
      ring
    · rw [hGdef, indicator_of_notMem (fun hmem' => hc (hmem.mp hmem')),
        indicator_of_notMem hc, mul_zero]
  -- Collapse the indicators on both sides.
  have hL : ∫ ε in Ioi (0 : ℝ), G (s * ε)
      = s ^ lam * ∫ ε in Ioc (0 : ℝ) ε₀,
          Real.exp (-(s * ε)) * llcScale lam theta ε := by
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
      setIntegral_indicator measurableSet_Ioc,
      inter_eq_self_of_subset_right Ioc_subset_Ioi_self]
  have hR : ∫ u in Ioi (0 : ℝ), G u
      = ∫ u in Ioc (0 : ℝ) (s * ε₀),
          Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
    rw [hGdef, setIntegral_indicator measurableSet_Ioc,
      inter_eq_self_of_subset_right Ioc_subset_Ioi_self]
  have hkey := hsub
  rw [hL, hR] at hkey
  -- `s^lam · head = s⁻¹ · subst` ⇒ `s · head = s^{−lam} · subst`.
  have hslam : (0 : ℝ) < s ^ lam := Real.rpow_pos_of_pos hs _
  rw [Real.rpow_neg hs.le]
  field_simp at hkey ⊢
  linear_combination hkey

/-! ## The integrability layer -/

/-- The log-power domination: `(1+|log u|)^β` is dominated
by a symmetric pair of power kernels, `(1+β/δ)^β · (u^{−δ} + u^δ)`, for any
`δ > 0`. This converts log-weighted integrands into Gamma-type ones. -/
private theorem one_add_abs_log_rpow_le {β δ u : ℝ} (hβ : 0 ≤ β) (hδ : 0 < δ)
    (hu : 0 < u) :
    (1 + |Real.log u|) ^ β ≤ (1 + β / δ) ^ β * (u ^ (-δ) + u ^ δ) := by
  have hprod : u ^ (-δ) * u ^ δ = 1 := by
    rw [← Real.rpow_add hu, neg_add_cancel, Real.rpow_zero]
  have hpos₁ : (0 : ℝ) < u ^ (-δ) := Real.rpow_pos_of_pos hu _
  have hpos₂ : (0 : ℝ) < u ^ δ := Real.rpow_pos_of_pos hu _
  have hsum : (1 : ℝ) ≤ u ^ (-δ) + u ^ δ := by
    nlinarith [sq_nonneg (u ^ (-δ) - 1), hprod, hpos₁, hpos₂]
  rcases eq_or_lt_of_le hβ with hβ0 | hβpos
  · rw [← hβ0, Real.rpow_zero, Real.rpow_zero, one_mul]
    exact hsum
  · -- For `v ≥ 1`: `(1 + log v)^β ≤ (1+β/δ)^β v^δ`.
    have hpow : ∀ v : ℝ, 1 ≤ v →
        (1 + Real.log v) ^ β ≤ (1 + β / δ) ^ β * v ^ δ := by
      intro v hv
      have hbase : 1 + Real.log v ≤ (1 + β / δ) * v ^ (δ / β) := by
        have hlog : Real.log v ≤ v ^ (δ / β) / (δ / β) :=
          Real.log_le_rpow_div (by linarith) (by positivity)
        have hone : (1 : ℝ) ≤ v ^ (δ / β) := Real.one_le_rpow hv (by positivity)
        have hdiv : v ^ (δ / β) / (δ / β) = (β / δ) * v ^ (δ / β) := by
          rw [div_eq_mul_inv, mul_comm]
          congr 1
          rw [← one_div, one_div_div]
        nlinarith [hlog, hone]
      have h1 : (0 : ℝ) ≤ 1 + Real.log v := by
        have := Real.log_nonneg hv
        linarith
      calc (1 + Real.log v) ^ β
          ≤ ((1 + β / δ) * v ^ (δ / β)) ^ β :=
            Real.rpow_le_rpow h1 hbase hβ
        _ = (1 + β / δ) ^ β * (v ^ (δ / β)) ^ β :=
            Real.mul_rpow (by positivity) (by positivity)
        _ = (1 + β / δ) ^ β * v ^ δ := by
            rw [← Real.rpow_mul (by linarith : (0:ℝ) ≤ v),
              div_mul_cancel₀ _ hβpos.ne']
    have hC : (0 : ℝ) ≤ (1 + β / δ) ^ β := by positivity
    rcases le_total 1 u with hu1 | hu1
    · rw [abs_of_nonneg (Real.log_nonneg hu1)]
      calc (1 + Real.log u) ^ β
          ≤ (1 + β / δ) ^ β * u ^ δ := hpow u hu1
        _ ≤ (1 + β / δ) ^ β * (u ^ (-δ) + u ^ δ) := by nlinarith [hpos₁, hC]
    · have hinv1 : (1 : ℝ) ≤ u⁻¹ := (one_le_inv₀ hu).mpr hu1
      have habs : 1 + |Real.log u| = 1 + Real.log u⁻¹ := by
        rw [Real.log_inv, abs_of_nonpos (Real.log_nonpos hu.le hu1)]
      have hinvpow : (u⁻¹) ^ δ = u ^ (-δ) := by
        rw [Real.inv_rpow hu.le, ← Real.rpow_neg hu.le]
      calc (1 + |Real.log u|) ^ β
          = (1 + Real.log u⁻¹) ^ β := by rw [habs]
        _ ≤ (1 + β / δ) ^ β * (u⁻¹) ^ δ := hpow u⁻¹ hinv1
        _ = (1 + β / δ) ^ β * u ^ (-δ) := by rw [hinvpow]
        _ ≤ (1 + β / δ) ^ β * (u ^ (-δ) + u ^ δ) := by nlinarith [hpos₂, hC]

/-- Gamma-type integrability: `e^{−u} u^p` is integrable on `(0,∞)` for
`p > −1`. -/
theorem _root_.integrableOn_exp_neg_rpow {p : ℝ} (hp : -1 < p) :
    IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ p) (Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := p + 1) (by linarith)
  simpa using h

/-- The dominating kernel of the head bounds: `e^{−u} u^λ (1+|log u|)^β` is
integrable on `(0,∞)` for `λ > −1`, `β ≥ 0`. -/
theorem _root_.integrableOn_exp_rpow_log_pow {lam β : ℝ} (hlam : -1 < lam)
    (hβ : 0 ≤ β) :
    IntegrableOn
      (fun u : ℝ => Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ β)
      (Ioi 0) := by
  set δ : ℝ := (lam + 1) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hint : IntegrableOn
      (fun u : ℝ => (1 + β / δ) ^ β
        * (Real.exp (-u) * u ^ (lam - δ) + Real.exp (-u) * u ^ (lam + δ)))
      (Ioi 0) :=
    ((integrableOn_exp_neg_rpow (by rw [hδdef]; linarith)).add
      (integrableOn_exp_neg_rpow (by linarith))).const_mul _
  refine Integrable.mono' hint ?_ ?_
  · exact ((measurable_id.neg.exp.mul (measurable_id.pow_const lam)).mul
      ((measurable_const.add Real.measurable_log.abs).pow_const β)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun u hu => ?_)
    rw [mem_Ioi] at hu
    have hnn : (0 : ℝ) ≤ Real.exp (-u) * u ^ lam :=
      mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hu.le _)
    have hlogp : (0 : ℝ) ≤ (1 + |Real.log u|) ^ β := by positivity
    rw [Real.norm_of_nonneg (mul_nonneg hnn hlogp)]
    calc Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ β
        ≤ Real.exp (-u) * u ^ lam
            * ((1 + β / δ) ^ β * (u ^ (-δ) + u ^ δ)) :=
          mul_le_mul_of_nonneg_left (one_add_abs_log_rpow_le hβ hδ hu) hnn
      _ = (1 + β / δ) ^ β
            * (Real.exp (-u) * u ^ (lam - δ) + Real.exp (-u) * u ^ (lam + δ)) := by
          rw [Real.rpow_sub hu, Real.rpow_add hu, Real.rpow_neg hu.le,
            div_eq_mul_inv]
          ring

/-- The substituted head integrand is integrable on its window: for
`λ > −1`, `s > 1`, `ε₀ ∈ (0,1)`, the function
`e^{−u} u^λ (log s − log u)^{θ−1}` is integrable on `(0, s·ε₀]`. The
`ε₀ < 1` cutoff keeps `log s − log u ≥ −log ε₀ > 0` on the window, which
controls the negative-exponent regime `θ < 1`. -/
private theorem integrableOn_head_integrand {lam theta s ε₀ : ℝ} (hlam : -1 < lam)
    (hs : 1 < s) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    IntegrableOn
      (fun u => Real.exp (-u)
        * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
      (Ioc (0 : ℝ) (s * ε₀)) := by
  have hs0 : (0 : ℝ) < s := one_pos.trans hs
  have h1s : (0 : ℝ) < 1 + Real.log s := by
    have := Real.log_pos hs
    linarith
  have hε₀log : (0 : ℝ) < -Real.log ε₀ := neg_pos.mpr (Real.log_neg hε₀ hε₀1)
  set C : ℝ := max ((1 + Real.log s) ^ (theta - 1))
    ((-Real.log ε₀) ^ (theta - 1)) with hCdef
  have hC : 0 ≤ C :=
    le_trans (Real.rpow_nonneg h1s.le _) (le_max_left _ _)
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp (-u)
        * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
      (volume.restrict (Ioc 0 (s * ε₀))) :=
    (measurable_id.neg.exp.mul ((measurable_id.pow_const lam).mul
      ((measurable_const.sub Real.measurable_log).pow_const _))).aestronglyMeasurable
  have hgint : IntegrableOn
      (fun u : ℝ => C * (Real.exp (-u) * u ^ lam
        * (1 + |Real.log u|) ^ |theta - 1|)) (Ioc (0 : ℝ) (s * ε₀)) :=
    IntegrableOn.mono_set
      ((integrableOn_exp_rpow_log_pow hlam (abs_nonneg (theta - 1))).const_mul C)
      Ioc_subset_Ioi_self
  refine Integrable.mono' hgint hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr
    (Eventually.of_forall fun u hu => ?_)
  rcases hu with ⟨hu0, hus⟩
  have hbase_lo : -Real.log ε₀ ≤ Real.log s - Real.log u := by
    have h := Real.log_le_log hu0 hus
    rw [Real.log_mul hs0.ne' hε₀.ne'] at h
    linarith
  have hbase_pos : (0 : ℝ) < Real.log s - Real.log u :=
    lt_of_lt_of_le hε₀log hbase_lo
  have hfac : (Real.log s - Real.log u) ^ (theta - 1)
      ≤ C * (1 + |Real.log u|) ^ |theta - 1| := by
    rcases le_total 0 (theta - 1) with hθ | hθ
    · have hbase_hi : Real.log s - Real.log u
          ≤ (1 + Real.log s) * (1 + |Real.log u|) := by
        have h2 : -Real.log u ≤ |Real.log u| := neg_le_abs _
        nlinarith [abs_nonneg (Real.log u), Real.log_pos hs]
      calc (Real.log s - Real.log u) ^ (theta - 1)
          ≤ ((1 + Real.log s) * (1 + |Real.log u|)) ^ (theta - 1) :=
            Real.rpow_le_rpow hbase_pos.le hbase_hi hθ
        _ = (1 + Real.log s) ^ (theta - 1)
              * (1 + |Real.log u|) ^ (theta - 1) :=
            Real.mul_rpow h1s.le (by positivity)
        _ ≤ C * (1 + |Real.log u|) ^ |theta - 1| := by
            rw [abs_of_nonneg hθ]
            exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    · calc (Real.log s - Real.log u) ^ (theta - 1)
          ≤ (-Real.log ε₀) ^ (theta - 1) :=
            Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hθ
              (mem_Ioi.mpr hε₀log) (mem_Ioi.mpr hbase_pos) hbase_lo
        _ ≤ C * 1 := by rw [mul_one]; exact le_max_right _ _
        _ ≤ C * (1 + |Real.log u|) ^ |theta - 1| := by
            refine mul_le_mul_of_nonneg_left ?_ hC
            exact Real.one_le_rpow
              (by nlinarith [abs_nonneg (Real.log u)]) (abs_nonneg _)
  have hnn1 : (0 : ℝ) ≤ Real.exp (-u) * u ^ lam :=
    mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hu0.le _)
  have hfacnn : (0 : ℝ) ≤ (Real.log s - Real.log u) ^ (theta - 1) :=
    Real.rpow_nonneg hbase_pos.le _
  rw [Real.norm_of_nonneg (by
    exact mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hu0.le _) hfacnn))]
  calc Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
      ≤ Real.exp (-u) * (u ^ lam * (C * (1 + |Real.log u|) ^ |theta - 1|)) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.exp_nonneg _)
        exact mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hu0.le _)
    _ = C * (Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1|) := by
        ring


/-! ## Asymptotic helpers for the head bounds -/

/-- Log powers lose to the identity: `(log s)^c / s → 0` at `atTop`. -/
theorem tendsto_log_rpow_div_atTop (c : ℝ) :
    Tendsto (fun s : ℝ => Real.log s ^ c / s) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero c 1 one_pos).comp
    Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
  show Real.log s ^ c * Real.exp (-1 * Real.log s) = Real.log s ^ c / s
  rw [show (-1 : ℝ) * Real.log s = -Real.log s by ring, Real.exp_neg,
    Real.exp_log hs, div_eq_mul_inv]

/-- A quadratic lower bound on `exp` inverted: `e^{−√s/2} ≤ 16/s` for
`s > 0`. (Keeps `√`-composition out of the far-piece estimates.) -/
private theorem exp_neg_sqrt_half_le {s : ℝ} (hs : 0 < s) :
    Real.exp (-(Real.sqrt s / 2)) ≤ 16 / s := by
  have hsq : 0 ≤ Real.sqrt s := Real.sqrt_nonneg s
  have hsq2 : Real.sqrt s ^ 2 = s := Real.sq_sqrt hs.le
  have hexp : Real.sqrt s / 4 + 1 ≤ Real.exp (Real.sqrt s / 4) :=
    Real.add_one_le_exp _
  have he : Real.exp (Real.sqrt s / 4) ^ 2 = Real.exp (Real.sqrt s / 2) := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have h2 : s / 16 ≤ Real.exp (Real.sqrt s / 2) := by
    nlinarith [hexp, Real.exp_pos (Real.sqrt s / 4), hsq, hsq2, he]
  have h16 : (0 : ℝ) < s / 16 := by positivity
  rw [Real.exp_neg]
  calc (Real.exp (Real.sqrt s / 2))⁻¹
      ≤ (s / 16)⁻¹ := by
        exact inv_anti₀ h16 h2
    _ = 16 / s := by field_simp

/-- The Gamma kernel is dominated by a half-rate exponential away from
the origin: there is `B > 0` with `e^{−u} u^λ ≤ B e^{−u/2}` for `u ≥ 1`. -/
theorem exists_exp_rpow_le_exp_half (lam : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ u : ℝ, 1 ≤ u →
      Real.exp (-u) * u ^ lam ≤ B * Real.exp (-(1 / 2 * u)) := by
  rcases le_or_gt lam 0 with hlam | hlam
  · refine ⟨1, one_pos, fun u hu => ?_⟩
    have hpow : u ^ lam ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hu hlam
    calc Real.exp (-u) * u ^ lam
        ≤ Real.exp (-u) * 1 :=
          mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
      _ = Real.exp (-u) := mul_one _
      _ ≤ 1 * Real.exp (-(1 / 2 * u)) := by
          rw [one_mul]
          exact Real.exp_le_exp.mpr (by linarith)
  · refine ⟨Real.exp (lam * (Real.log (2 * lam) - 1)), Real.exp_pos _,
      fun u hu => ?_⟩
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
    have h2l : (0 : ℝ) < 2 * lam := by linarith
    have hkey : Real.log u ≤ Real.log (2 * lam) + (u / (2 * lam) - 1) := by
      have hdiv : (0 : ℝ) < u / (2 * lam) := by positivity
      have h := Real.log_le_sub_one_of_pos hdiv
      rw [Real.log_div hu0.ne' h2l.ne'] at h
      linarith
    have hcalc : lam * (u / (2 * lam)) = 1 / 2 * u := by
      field_simp
    have hmul : lam * Real.log u
        ≤ lam * (Real.log (2 * lam) - 1) + 1 / 2 * u := by
      have h := mul_le_mul_of_nonneg_left hkey hlam.le
      nlinarith [h, hcalc]
    calc Real.exp (-u) * u ^ lam
        = Real.exp (-u + Real.log u * lam) := by
          rw [Real.rpow_def_of_pos hu0, ← Real.exp_add]
      _ ≤ Real.exp (lam * (Real.log (2 * lam) - 1) + -(1 / 2 * u)) := by
          apply Real.exp_le_exp.mpr
          nlinarith [hmul]
      _ = Real.exp (lam * (Real.log (2 * lam) - 1))
            * Real.exp (-(1 / 2 * u)) := Real.exp_add _ _

/-! ## The head Θ-bound -/

/-- **Lower half.** The substituted head integral eventually
dominates a positive multiple of `(log s)^{θ−1}`: the fixed window
`u ∈ (1, e]` already carries it. -/
private theorem head_subst_eventually_ge {lam theta ε₀ : ℝ} (hlam : -1 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ s : ℝ in atTop,
      c * Real.log s ^ (theta - 1)
        ≤ ∫ u in Ioc (0 : ℝ) (s * ε₀),
            Real.exp (-u)
              * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
  have he1 : (1 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  set m : ℝ := Real.exp (-Real.exp 1) * min 1 (Real.exp 1 ^ lam) with hmdef
  have hm : 0 < m :=
    mul_pos (Real.exp_pos _)
      (lt_min one_pos (Real.rpow_pos_of_pos (Real.exp_pos 1) _))
  have h2p : (0 : ℝ) < (2 : ℝ) ^ (-|theta - 1|) := Real.rpow_pos_of_pos two_pos _
  refine ⟨(Real.exp 1 - 1) * (m * (2 : ℝ) ^ (-|theta - 1|)),
    mul_pos (by linarith) (mul_pos hm h2p), ?_⟩
  filter_upwards [eventually_ge_atTop (Real.exp 1 / ε₀),
    Real.tendsto_log_atTop.eventually_ge_atTop 2,
    eventually_gt_atTop (1 : ℝ)] with s hse hlog2 hs1
  have hs0 : (0 : ℝ) < s := one_pos.trans hs1
  have hwin_top : Real.exp 1 ≤ s * ε₀ := by
    rw [div_le_iff₀ hε₀] at hse
    linarith
  have hwin : Ioc (1 : ℝ) (Real.exp 1) ⊆ Ioc (0 : ℝ) (s * ε₀) :=
    fun u hu => ⟨one_pos.trans hu.1, hu.2.trans hwin_top⟩
  have hbig_int := integrableOn_head_integrand
    (lam := lam) (theta := theta) hlam hs1 hε₀ hε₀1
  have hbase_pos : ∀ u ∈ Ioc (0 : ℝ) (s * ε₀),
      0 < Real.log s - Real.log u := by
    intro u hu
    have h := Real.log_le_log hu.1 hu.2
    rw [Real.log_mul hs0.ne' hε₀.ne'] at h
    have : Real.log ε₀ < 0 := Real.log_neg hε₀ hε₀1
    linarith
  have hnn : ∀ u ∈ Ioc (0 : ℝ) (s * ε₀),
      0 ≤ Real.exp (-u)
        * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
    intro u hu
    exact mul_nonneg (Real.exp_nonneg _)
      (mul_nonneg (Real.rpow_nonneg hu.1.le _)
        (Real.rpow_nonneg (hbase_pos u hu).le _))
  -- Pointwise lower bound on the window.
  have hpt : ∀ u ∈ Ioc (1 : ℝ) (Real.exp 1),
      m * ((2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1))
        ≤ Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
    intro u hu
    have hu1 : (1 : ℝ) < u := hu.1
    have hu0 : (0 : ℝ) < u := one_pos.trans hu1
    have hlogupos : 0 < Real.log u := Real.log_pos hu1
    have hlogu1 : Real.log u ≤ 1 := by
      calc Real.log u ≤ Real.log (Real.exp 1) :=
            Real.log_le_log hu0 hu.2
        _ = 1 := Real.log_exp 1
    have hker : m ≤ Real.exp (-u) * u ^ lam := by
      have h1 : Real.exp (-Real.exp 1) ≤ Real.exp (-u) :=
        Real.exp_le_exp.mpr (by linarith [hu.2])
      have h2 : min 1 (Real.exp 1 ^ lam) ≤ u ^ lam := by
        rcases le_or_gt 0 lam with hl | hl
        · exact le_trans (min_le_left _ _) (Real.one_le_rpow hu1.le hl)
        · refine le_trans (min_le_right _ _) ?_
          exact Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hl.le
            (mem_Ioi.mpr hu0) (mem_Ioi.mpr (Real.exp_pos 1)) hu.2
      exact mul_le_mul h1 h2
        (le_min one_pos.le (Real.rpow_pos_of_pos (Real.exp_pos 1) _).le)
        (Real.exp_nonneg _)
    have hfac : (2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1)
        ≤ (Real.log s - Real.log u) ^ (theta - 1) := by
      have hlogs0 : (0 : ℝ) < Real.log s := by linarith
      have hbpos : (0 : ℝ) < Real.log s - Real.log u := by linarith
      rcases le_or_gt 0 (theta - 1) with hθ | hθ
      · have hhalf : Real.log s / 2 ≤ Real.log s - Real.log u := by
          linarith
        calc (2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1)
            = (Real.log s / 2) ^ (theta - 1) := by
              rw [Real.div_rpow hlogs0.le two_pos.le, abs_of_nonneg hθ,
                Real.rpow_neg two_pos.le, div_eq_mul_inv, mul_comm]
          _ ≤ (Real.log s - Real.log u) ^ (theta - 1) :=
              Real.rpow_le_rpow (by positivity) hhalf hθ
      · have h2le1 : (2 : ℝ) ^ (-|theta - 1|) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos one_le_two
            (neg_nonpos.mpr (abs_nonneg _))
        calc (2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1)
            ≤ 1 * Real.log s ^ (theta - 1) :=
              mul_le_mul_of_nonneg_right h2le1 (Real.rpow_nonneg hlogs0.le _)
          _ = Real.log s ^ (theta - 1) := one_mul _
          _ ≤ (Real.log s - Real.log u) ^ (theta - 1) :=
              Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hθ.le
                (mem_Ioi.mpr hbpos) (mem_Ioi.mpr hlogs0) (by linarith)
    calc m * ((2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1))
        ≤ (Real.exp (-u) * u ^ lam)
            * ((Real.log s - Real.log u) ^ (theta - 1)) :=
          mul_le_mul hker hfac (by positivity) (by positivity)
      _ = Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
          ring
  -- Window integral of the constant.
  have hconst : ∫ _u in Ioc (1 : ℝ) (Real.exp 1),
      (m * ((2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1))) ∂volume
        = (Real.exp 1 - 1)
            * (m * ((2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1))) := by
    rw [setIntegral_const, measureReal_def, Real.volume_Ioc,
      ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ Real.exp 1 - 1),
      smul_eq_mul]
  have hmono1 : ∫ _u in Ioc (1 : ℝ) (Real.exp 1),
      (m * ((2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1))) ∂volume
        ≤ ∫ u in Ioc (1 : ℝ) (Real.exp 1),
            Real.exp (-u)
              * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc hpt
    · exact integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    · exact IntegrableOn.mono_set hbig_int hwin
  have hmono2 : ∫ u in Ioc (1 : ℝ) (Real.exp 1),
      Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
        ≤ ∫ u in Ioc (0 : ℝ) (s * ε₀),
            Real.exp (-u)
              * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
    refine setIntegral_mono_set hbig_int ?_ (LE.le.eventuallySubset hwin)
    exact (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun u hu => hnn u hu)
  calc (Real.exp 1 - 1) * (m * (2 : ℝ) ^ (-|theta - 1|))
        * Real.log s ^ (theta - 1)
      = (Real.exp 1 - 1)
          * (m * ((2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1))) := by
        ring
    _ = ∫ _u in Ioc (1 : ℝ) (Real.exp 1),
          (m * ((2 : ℝ) ^ (-|theta - 1|) * Real.log s ^ (theta - 1))) ∂volume :=
        hconst.symm
    _ ≤ ∫ u in Ioc (1 : ℝ) (Real.exp 1),
          Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := hmono1
    _ ≤ ∫ u in Ioc (0 : ℝ) (s * ε₀),
          Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := hmono2

/-- **Upper half.** The substituted head integral is eventually
bounded by a constant multiple of `(log s)^{θ−1}`: split at `√s`; the
near piece is dominated through the log-power kernel, the far piece is
exponentially small. -/
private theorem head_subst_eventually_le {lam theta ε₀ : ℝ} (hlam : -1 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ s : ℝ in atTop,
      ∫ u in Ioc (0 : ℝ) (s * ε₀),
          Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
        ≤ C * Real.log s ^ (theta - 1) := by
  obtain ⟨B, hB, hBbd⟩ := exists_exp_rpow_le_exp_half lam
  set K : ℝ := ∫ u in Ioi (0 : ℝ),
    Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1| with hKdef
  have hK : 0 ≤ K :=
    setIntegral_nonneg measurableSet_Ioi fun u hu =>
      mul_nonneg (mul_nonneg (Real.exp_nonneg _)
        (Real.rpow_nonneg (le_of_lt hu) _)) (Real.rpow_nonneg (by positivity) _)
  have hε₀log : (0 : ℝ) < -Real.log ε₀ := neg_pos.mpr (Real.log_neg hε₀ hε₀1)
  set c' : ℝ := (-Real.log ε₀) ^ (theta - 1) with hc'def
  have hc' : 0 < c' := Real.rpow_pos_of_pos hε₀log _
  have h2pow : (1 : ℝ) ≤ (2 : ℝ) ^ |theta - 1| :=
    Real.one_le_rpow one_le_two (abs_nonneg _)
  refine ⟨(2 : ℝ) ^ |theta - 1| * K + 1, by nlinarith [hK, h2pow], ?_⟩
  have htend : Tendsto
      (fun s : ℝ => 32 * B * c' * (Real.log s ^ (1 - theta) / s))
      atTop (𝓝 0) := by
    have h := (tendsto_log_rpow_div_atTop (1 - theta)).const_mul (32 * B * c')
    simpa using h
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop ((ε₀⁻¹) ^ (2 : ℕ)),
    eventually_ge_atTop (64 * B),
    htend.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2)]
    with s hs1 hlog1 hsq hs64 hsmall
  have hs0 : (0 : ℝ) < s := one_pos.trans hs1
  have hlogs0 : (0 : ℝ) < Real.log s := by linarith
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt s := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hs1.le
  have hsqrt0 : (0 : ℝ) < Real.sqrt s := lt_of_lt_of_le one_pos hsqrt1
  have hsplitpt : Real.sqrt s ≤ s * ε₀ := by
    have h1 : ε₀⁻¹ ≤ Real.sqrt s := by
      have h := Real.sqrt_le_sqrt hsq
      rwa [Real.sqrt_sq (by positivity : (0:ℝ) ≤ ε₀⁻¹)] at h
    have h2 : (1 : ℝ) ≤ Real.sqrt s * ε₀ := by
      rw [← inv_mul_cancel₀ hε₀.ne']
      exact mul_le_mul_of_nonneg_right h1 hε₀.le
    calc Real.sqrt s = Real.sqrt s * 1 := (mul_one _).symm
      _ ≤ Real.sqrt s * (Real.sqrt s * ε₀) :=
          mul_le_mul_of_nonneg_left h2 hsqrt0.le
      _ = Real.sqrt s * Real.sqrt s * ε₀ := by ring
      _ = s * ε₀ := by rw [Real.mul_self_sqrt hs0.le]
  have hbig_int := integrableOn_head_integrand
    (lam := lam) (theta := theta) hlam hs1 hε₀ hε₀1
  have hnear_sub : Ioc (0 : ℝ) (Real.sqrt s) ⊆ Ioc (0 : ℝ) (s * ε₀) :=
    Ioc_subset_Ioc_right hsplitpt
  have hfar_sub : Ioc (Real.sqrt s) (s * ε₀) ⊆ Ioc (0 : ℝ) (s * ε₀) :=
    Ioc_subset_Ioc_left hsqrt0.le
  -- The exponential moment bound shared by both far-piece terms.
  have hd0 : 2 * B * Real.exp (-(1 / 2 * Real.sqrt s)) ≤ 32 * B / s := by
    have h := exp_neg_sqrt_half_le hs0
    rw [show -(1 / 2 * Real.sqrt s) = -(Real.sqrt s / 2) by ring]
    calc 2 * B * Real.exp (-(Real.sqrt s / 2))
        ≤ 2 * B * (16 / s) :=
          mul_le_mul_of_nonneg_left h (by positivity)
      _ = 32 * B / s := by ring
  have hd1 : 2 * B * Real.exp (-(1 / 2 * Real.sqrt s)) ≤ 1 / 2 := by
    refine hd0.trans ?_
    rw [div_le_iff₀ hs0]
    linarith
  have hd2 : c' * (2 * B * Real.exp (-(1 / 2 * Real.sqrt s)))
      ≤ 1 / 2 * Real.log s ^ (theta - 1) := by
    have hone : Real.log s ^ (1 - theta) * Real.log s ^ (theta - 1) = 1 := by
      rw [← Real.rpow_add hlogs0]
      norm_num
    have hprod : Real.log s ^ (1 - theta) / s * Real.log s ^ (theta - 1)
        = 1 / s := by
      rw [div_mul_eq_mul_div, hone]
    have hstep : c' * (32 * B / s)
        = 32 * B * c' * (Real.log s ^ (1 - theta) / s)
          * Real.log s ^ (theta - 1) := by
      calc c' * (32 * B / s) = 32 * B * c' * (1 / s) := by ring
        _ = 32 * B * c'
              * (Real.log s ^ (1 - theta) / s * Real.log s ^ (theta - 1)) := by
            rw [hprod]
        _ = 32 * B * c' * (Real.log s ^ (1 - theta) / s)
              * Real.log s ^ (theta - 1) := by ring
    calc c' * (2 * B * Real.exp (-(1 / 2 * Real.sqrt s)))
        ≤ c' * (32 * B / s) := mul_le_mul_of_nonneg_left hd0 hc'.le
      _ = 32 * B * c' * (Real.log s ^ (1 - theta) / s)
            * Real.log s ^ (theta - 1) := hstep
      _ ≤ 1 / 2 * Real.log s ^ (theta - 1) :=
          mul_le_mul_of_nonneg_right hsmall.le (Real.rpow_nonneg hlogs0.le _)
  -- Split the integral at √s.
  have hdisj : Disjoint (Ioc (0 : ℝ) (Real.sqrt s)) (Ioc (Real.sqrt s) (s * ε₀)) :=
    Set.disjoint_left.mpr fun x hx1 hx2 => absurd hx1.2 (not_le.mpr hx2.1)
  have hsplit : ∫ u in Ioc (0 : ℝ) (s * ε₀),
      Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
        = (∫ u in Ioc (0 : ℝ) (Real.sqrt s),
            Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
          + ∫ u in Ioc (Real.sqrt s) (s * ε₀),
              Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
    rw [← Ioc_union_Ioc_eq_Ioc hsqrt0.le hsplitpt]
    exact setIntegral_union hdisj measurableSet_Ioc
      (IntegrableOn.mono_set hbig_int hnear_sub)
      (IntegrableOn.mono_set hbig_int hfar_sub)
  -- Near piece.
  have hnear : ∫ u in Ioc (0 : ℝ) (Real.sqrt s),
      Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
        ≤ (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1) * K := by
    have hpt : ∀ u ∈ Ioc (0 : ℝ) (Real.sqrt s),
        Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
          ≤ (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
              * (Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1|) := by
      intro u hu
      have hu0 : (0 : ℝ) < u := hu.1
      have hloghalf : Real.log u ≤ Real.log s / 2 := by
        calc Real.log u ≤ Real.log (Real.sqrt s) := Real.log_le_log hu0 hu.2
          _ = Real.log s / 2 := Real.log_sqrt hs0.le
      have hbase_pos : (0 : ℝ) < Real.log s - Real.log u := by linarith
      have hone_le : (1 : ℝ) ≤ (1 + |Real.log u|) ^ |theta - 1| :=
        Real.one_le_rpow (by nlinarith [abs_nonneg (Real.log u)]) (abs_nonneg _)
      have hfac : (Real.log s - Real.log u) ^ (theta - 1)
          ≤ (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
              * (1 + |Real.log u|) ^ |theta - 1| := by
        rcases le_or_gt 0 (theta - 1) with hθ | hθ
        · have hhi : Real.log s - Real.log u
              ≤ Real.log s * (1 + |Real.log u|) := by
            have h2 : -Real.log u ≤ |Real.log u| := neg_le_abs _
            nlinarith [abs_nonneg (Real.log u)]
          calc (Real.log s - Real.log u) ^ (theta - 1)
              ≤ (Real.log s * (1 + |Real.log u|)) ^ (theta - 1) :=
                Real.rpow_le_rpow hbase_pos.le hhi hθ
            _ = Real.log s ^ (theta - 1) * (1 + |Real.log u|) ^ (theta - 1) :=
                Real.mul_rpow hlogs0.le (by positivity)
            _ = 1 * Real.log s ^ (theta - 1)
                  * (1 + |Real.log u|) ^ |theta - 1| := by
                rw [abs_of_nonneg hθ, one_mul]
            _ ≤ (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
                  * (1 + |Real.log u|) ^ |theta - 1| := by
                have hr : (0:ℝ) ≤ Real.log s ^ (theta - 1) :=
                  Real.rpow_nonneg hlogs0.le _
                have hr2 : (0:ℝ) ≤ (1 + |Real.log u|) ^ |theta - 1| := by
                  positivity
                nlinarith [mul_nonneg hr hr2, h2pow]
        · have hhalf : Real.log s / 2 ≤ Real.log s - Real.log u := by linarith
          calc (Real.log s - Real.log u) ^ (theta - 1)
              ≤ (Real.log s / 2) ^ (theta - 1) :=
                Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hθ.le
                  (mem_Ioi.mpr (by linarith : (0:ℝ) < Real.log s / 2))
                  (mem_Ioi.mpr hbase_pos) hhalf
            _ = (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1) := by
                rw [Real.div_rpow hlogs0.le two_pos.le,
                  abs_of_neg (by linarith : theta - 1 < 0),
                  Real.rpow_neg two_pos.le, div_eq_mul_inv, mul_comm]
            _ ≤ (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
                  * (1 + |Real.log u|) ^ |theta - 1| := by
                have hr : (0:ℝ) ≤ (2:ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1) := by
                  positivity
                nlinarith [hone_le, hr]
      have hker : (0 : ℝ) ≤ Real.exp (-u) * u ^ lam :=
        mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hu0.le _)
      calc Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
          = (Real.exp (-u) * u ^ lam)
              * (Real.log s - Real.log u) ^ (theta - 1) := by ring
        _ ≤ (Real.exp (-u) * u ^ lam)
              * ((2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
                * (1 + |Real.log u|) ^ |theta - 1|) :=
            mul_le_mul_of_nonneg_left hfac hker
        _ = (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
              * (Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1|) := by
            ring
    have hkint : IntegrableOn
        (fun u : ℝ => Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1|)
        (Ioi (0 : ℝ)) := integrableOn_exp_rpow_log_pow hlam (abs_nonneg _)
    calc ∫ u in Ioc (0 : ℝ) (Real.sqrt s),
        Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
        ≤ ∫ u in Ioc (0 : ℝ) (Real.sqrt s),
            (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
              * (Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1|) := by
          refine setIntegral_mono_on (IntegrableOn.mono_set hbig_int hnear_sub)
            ?_ measurableSet_Ioc hpt
          exact (IntegrableOn.mono_set (hkint.const_mul _) Ioc_subset_Ioi_self)
      _ = (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1)
            * ∫ u in Ioc (0 : ℝ) (Real.sqrt s),
                Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1| :=
          integral_const_mul _ _
      _ ≤ (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1) * K := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine setIntegral_mono_set hkint ?_
            (LE.le.eventuallySubset Ioc_subset_Ioi_self)
          exact (ae_restrict_iff' measurableSet_Ioi).mpr
            (Eventually.of_forall fun u hu =>
              mul_nonneg (mul_nonneg (Real.exp_nonneg _)
                (Real.rpow_nonneg (le_of_lt hu) _))
                (Real.rpow_nonneg (by positivity) _))
  -- Far piece.
  have hfar : ∫ u in Ioc (Real.sqrt s) (s * ε₀),
      Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
        ≤ Real.log s ^ (theta - 1) := by
    have hexpint : IntegrableOn (fun u : ℝ => Real.exp (-(1 / 2 * u)))
        (Ioi (Real.sqrt s)) := by
      simpa [neg_mul] using
        exp_neg_integrableOn_Ioi (Real.sqrt s) (by norm_num : (0:ℝ) < 1/2)
    have hpt : ∀ u ∈ Ioc (Real.sqrt s) (s * ε₀),
        Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
          ≤ (Real.log s ^ (theta - 1) + c')
              * (B * Real.exp (-(1 / 2 * u))) := by
      intro u hu
      have hu1 : (1 : ℝ) ≤ u := hsqrt1.trans hu.1.le
      have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu1
      have hbase_lo : -Real.log ε₀ ≤ Real.log s - Real.log u := by
        have h := Real.log_le_log hu0 hu.2
        rw [Real.log_mul hs0.ne' hε₀.ne'] at h
        linarith
      have hbase_pos : (0 : ℝ) < Real.log s - Real.log u :=
        lt_of_lt_of_le hε₀log hbase_lo
      have hfac : (Real.log s - Real.log u) ^ (theta - 1)
          ≤ Real.log s ^ (theta - 1) + c' := by
        rcases le_or_gt 0 (theta - 1) with hθ | hθ
        · have hhi : Real.log s - Real.log u ≤ Real.log s := by
            have : (0:ℝ) ≤ Real.log u := Real.log_nonneg hu1
            linarith
          calc (Real.log s - Real.log u) ^ (theta - 1)
              ≤ Real.log s ^ (theta - 1) :=
                Real.rpow_le_rpow hbase_pos.le hhi hθ
            _ ≤ Real.log s ^ (theta - 1) + c' := by linarith
        · calc (Real.log s - Real.log u) ^ (theta - 1)
              ≤ c' :=
                Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hθ.le
                  (mem_Ioi.mpr hε₀log) (mem_Ioi.mpr hbase_pos) hbase_lo
            _ ≤ Real.log s ^ (theta - 1) + c' := by
                have : (0:ℝ) ≤ Real.log s ^ (theta - 1) :=
                  Real.rpow_nonneg hlogs0.le _
                linarith
      have hkerb : Real.exp (-u) * u ^ lam ≤ B * Real.exp (-(1 / 2 * u)) :=
        hBbd u hu1
      have hfacnn : (0 : ℝ) ≤ (Real.log s - Real.log u) ^ (theta - 1) :=
        Real.rpow_nonneg hbase_pos.le _
      calc Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
          = (Real.exp (-u) * u ^ lam)
              * (Real.log s - Real.log u) ^ (theta - 1) := by ring
        _ ≤ (B * Real.exp (-(1 / 2 * u)))
              * (Real.log s ^ (theta - 1) + c') :=
            mul_le_mul hkerb hfac hfacnn (by positivity)
        _ = (Real.log s ^ (theta - 1) + c')
              * (B * Real.exp (-(1 / 2 * u))) := by ring
    calc ∫ u in Ioc (Real.sqrt s) (s * ε₀),
        Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
        ≤ ∫ u in Ioc (Real.sqrt s) (s * ε₀),
            (Real.log s ^ (theta - 1) + c') * (B * Real.exp (-(1 / 2 * u))) := by
          refine setIntegral_mono_on (IntegrableOn.mono_set hbig_int hfar_sub)
            ?_ measurableSet_Ioc hpt
          exact IntegrableOn.mono_set ((hexpint.const_mul B).const_mul _)
            Ioc_subset_Ioi_self
      _ = (Real.log s ^ (theta - 1) + c') * B
            * ∫ u in Ioc (Real.sqrt s) (s * ε₀), Real.exp (-(1 / 2 * u)) := by
          rw [← integral_const_mul]
          refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
          ring
      _ ≤ (Real.log s ^ (theta - 1) + c') * B
            * ∫ u in Ioi (Real.sqrt s), Real.exp (-(1 / 2 * u)) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine setIntegral_mono_set hexpint ?_
            (LE.le.eventuallySubset Ioc_subset_Ioi_self)
          exact Eventually.of_forall fun u => Real.exp_nonneg _
      _ = (Real.log s ^ (theta - 1) + c')
            * (2 * B * Real.exp (-(1 / 2 * Real.sqrt s))) := by
          rw [integral_exp_neg_mul_Ioi (by norm_num : (0:ℝ) < 1/2)]
          ring_nf
      _ = Real.log s ^ (theta - 1) * (2 * B * Real.exp (-(1 / 2 * Real.sqrt s)))
            + c' * (2 * B * Real.exp (-(1 / 2 * Real.sqrt s))) := by ring
      _ ≤ Real.log s ^ (theta - 1) * (1 / 2)
            + 1 / 2 * Real.log s ^ (theta - 1) := by
          refine add_le_add ?_ hd2
          exact mul_le_mul_of_nonneg_left hd1 (Real.rpow_nonneg hlogs0.le _)
      _ = Real.log s ^ (theta - 1) := by ring
  rw [hsplit]
  calc (∫ u in Ioc (0 : ℝ) (Real.sqrt s),
        Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
        + ∫ u in Ioc (Real.sqrt s) (s * ε₀),
            Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1))
      ≤ (2 : ℝ) ^ |theta - 1| * Real.log s ^ (theta - 1) * K
          + Real.log s ^ (theta - 1) := add_le_add hnear hfar
    _ = ((2 : ℝ) ^ |theta - 1| * K + 1) * Real.log s ^ (theta - 1) := by ring

/-- The substituted head integral is `Θ((log s)^{θ−1})` at
`atTop`. -/
private theorem head_subst_isTheta {lam theta ε₀ : ℝ} (hlam : -1 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    (fun s => ∫ u in Ioc (0 : ℝ) (s * ε₀),
        Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
      =Θ[atTop] fun s => Real.log s ^ (theta - 1) := by
  obtain ⟨c, hc, hge⟩ := head_subst_eventually_ge
    (lam := lam) (theta := theta) hlam hε₀ hε₀1
  obtain ⟨C, hC, hle⟩ := head_subst_eventually_le
    (lam := lam) (theta := theta) hlam hε₀ hε₀1
  have hlogpos : ∀ᶠ s : ℝ in atTop, (0 : ℝ) < Real.log s ^ (theta - 1) := by
    filter_upwards [Real.tendsto_log_atTop.eventually_gt_atTop 0] with s h
    exact Real.rpow_pos_of_pos h _
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨C, ?_⟩
    filter_upwards [hle, hge, hlogpos] with s h1 h2 h3
    rw [Real.norm_of_nonneg (le_trans (by positivity) h2),
      Real.norm_of_nonneg h3.le]
    exact h1
  · rw [Asymptotics.isBigO_iff]
    refine ⟨c⁻¹, ?_⟩
    filter_upwards [hge, hlogpos] with s h2 h3
    rw [Real.norm_of_nonneg h3.le,
      Real.norm_of_nonneg (le_trans (by positivity) h2)]
    calc Real.log s ^ (theta - 1)
        = c⁻¹ * (c * Real.log s ^ (theta - 1)) := by
          rw [← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
      _ ≤ c⁻¹ * ∫ u in Ioc (0 : ℝ) (s * ε₀),
            Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) :=
          mul_le_mul_of_nonneg_left h2 (inv_pos.mpr hc).le

/-- The head of the Laplace representation is `Θ(laplaceScale λ θ)` at `atTop`, for `λ > −1`
and any cutoff `ε₀ ∈ (0, 1)`. -/
theorem _root_.SingularLearningTheory.mul_setIntegral_head_isTheta {lam theta ε₀ : ℝ}
    (hlam : -1 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    (fun s => s * ∫ ε in Ioc (0 : ℝ) ε₀,
        Real.exp (-(s * ε)) * llcScale lam theta ε)
      =Θ[atTop] SingularLearningTheory.laplaceScale lam theta := by
  have heq : (fun s : ℝ => s * ∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * llcScale lam theta ε)
        =ᶠ[atTop] fun s => s ^ (-lam) * ∫ u in Ioc (0 : ℝ) (s * ε₀),
          Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    exact mul_setIntegral_head_eq_subst hs
  have hpow : (fun s : ℝ => s ^ (-lam)) =Θ[atTop] fun s : ℝ => s ^ (-lam) :=
    Asymptotics.isTheta_rfl
  have hmul := hpow.mul (head_subst_isTheta
    (lam := lam) (theta := theta) hlam hε₀ hε₀1)
  refine heq.trans_isTheta (hmul.trans_eventuallyEq ?_)
  filter_upwards with s
  rfl


/-! ## The precise head limit -/

/-- The normalized head integral converges to `Γ(λ+1)`:
for `λ > −1`, any `θ`, `ε₀ ∈ (0,1)`,

  `I(s) / (log s)^{θ−1} → Γ(λ+1)`  as `s → ∞`,

by dominated convergence along `atTop`, with the log-power kernel
as the dominating function and the regime split at `log u = ½ log s`. -/
theorem head_subst_div_tendsto_gamma {lam theta ε₀ : ℝ} (hlam : -1 < lam)
    (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    Tendsto (fun s => (∫ u in Ioc (0 : ℝ) (s * ε₀),
        Real.exp (-u) * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
      / Real.log s ^ (theta - 1)) atTop (𝓝 (Real.Gamma (lam + 1))) := by
  have hε₀log : (0 : ℝ) < -Real.log ε₀ := neg_pos.mpr (Real.log_neg hε₀ hε₀1)
  set c' : ℝ := (-Real.log ε₀) ^ (theta - 1) with hc'def
  have hc' : 0 < c' := Real.rpow_pos_of_pos hε₀log _
  set Cd : ℝ := (2 : ℝ) ^ |theta - 1| * (1 + c') with hCddef
  have h2pow : (1 : ℝ) ≤ (2 : ℝ) ^ |theta - 1| :=
    Real.one_le_rpow one_le_two (abs_nonneg _)
  have hCd1 : (1 : ℝ) ≤ Cd := by
    rw [hCddef]
    nlinarith [h2pow, hc']
  have hCd2 : (2 : ℝ) ^ |theta - 1| ≤ Cd := by
    rw [hCddef]
    nlinarith [h2pow, hc']
  have hCdc : c' * (2 : ℝ) ^ |theta - 1| ≤ Cd := by
    rw [hCddef]
    nlinarith [h2pow, hc']
  have hgamma : ∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ lam
      = Real.Gamma (lam + 1) := by
    rw [Real.Gamma_eq_integral (by linarith : (0 : ℝ) < lam + 1)]
    refine setIntegral_congr_fun measurableSet_Ioi fun u _ => ?_
    rw [show lam + 1 - 1 = lam by ring]
  have hmain : Tendsto (fun s => ∫ u in Ioi (0 : ℝ),
      (Ioc (0 : ℝ) (s * ε₀)).indicator
        (fun u => Real.exp (-u) * u ^ lam
          * ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)) u)
      atTop (𝓝 (∫ u in Ioi (0 : ℝ), Real.exp (-u) * u ^ lam)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun u => Cd
        * (Real.exp (-u) * u ^ lam * (1 + |Real.log u|) ^ |theta - 1|))
      ?_ ?_ ?_ ?_
    · filter_upwards with s
      refine (Measurable.indicator ?_ measurableSet_Ioc).aestronglyMeasurable
      exact (measurable_id.neg.exp.mul (measurable_id.pow_const lam)).mul
        (((measurable_const.sub Real.measurable_log).div_const _).pow_const _)
    · filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
        eventually_gt_atTop (1 : ℝ)] with s hlog1 hs1
      refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun u hu => ?_)
      rw [mem_Ioi] at hu
      have hlogs0 : (0 : ℝ) < Real.log s := by linarith
      by_cases hmem : u ∈ Ioc (0 : ℝ) (s * ε₀)
      · rw [indicator_of_mem hmem]
        have hbase_lo : -Real.log ε₀ ≤ Real.log s - Real.log u := by
          have h := Real.log_le_log hu hmem.2
          rw [Real.log_mul (by linarith : s ≠ 0) hε₀.ne'] at h
          linarith
        have hbase_pos : (0 : ℝ) < Real.log s - Real.log u :=
          lt_of_lt_of_le hε₀log hbase_lo
        have hratio_pos : (0 : ℝ) < (Real.log s - Real.log u) / Real.log s :=
          div_pos hbase_pos hlogs0
        have hone_le : (1 : ℝ) ≤ (1 + |Real.log u|) ^ |theta - 1| :=
          Real.one_le_rpow (by nlinarith [abs_nonneg (Real.log u)])
            (abs_nonneg _)
        have hkernn : (0 : ℝ) ≤ (1 + |Real.log u|) ^ |theta - 1| := by
          positivity
        have hpow_le : ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)
            ≤ Cd * (1 + |Real.log u|) ^ |theta - 1| := by
          rcases le_or_gt (Real.log u) (Real.log s / 2) with hreg | hreg
          · rcases le_or_gt 0 (theta - 1) with hθ | hθ
            · have hub : (Real.log s - Real.log u) / Real.log s
                  ≤ 1 + |Real.log u| := by
                rw [div_le_iff₀ hlogs0]
                have h1 : -Real.log u ≤ |Real.log u| := neg_le_abs _
                nlinarith [abs_nonneg (Real.log u)]
              calc ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)
                  ≤ (1 + |Real.log u|) ^ (theta - 1) :=
                    Real.rpow_le_rpow hratio_pos.le hub hθ
                _ = (1 + |Real.log u|) ^ |theta - 1| := by
                    rw [abs_of_nonneg hθ]
                _ ≤ Cd * (1 + |Real.log u|) ^ |theta - 1| := by
                    nlinarith [hone_le, hCd1, hkernn]
            · have hlb : (1 : ℝ) / 2
                  ≤ (Real.log s - Real.log u) / Real.log s := by
                rw [div_le_div_iff₀ two_pos hlogs0]
                linarith
              calc ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)
                  ≤ ((1 : ℝ) / 2) ^ (theta - 1) :=
                    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hθ.le
                      (mem_Ioi.mpr (by norm_num)) (mem_Ioi.mpr hratio_pos) hlb
                _ = (2 : ℝ) ^ |theta - 1| := by
                    rw [abs_of_neg (by linarith : theta - 1 < 0), one_div,
                      Real.inv_rpow two_pos.le, ← Real.rpow_neg two_pos.le]
                _ ≤ Cd * (1 + |Real.log u|) ^ |theta - 1| := by
                    nlinarith [hone_le, hCd2,
                      Real.rpow_pos_of_pos two_pos |theta - 1|]
          · have hu1 : (0 : ℝ) < Real.log u := by linarith
            rcases le_or_gt 0 (theta - 1) with hθ | hθ
            · have hub : (Real.log s - Real.log u) / Real.log s ≤ 1 := by
                rw [div_le_one hlogs0]
                linarith
              calc ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)
                  ≤ (1 : ℝ) ^ (theta - 1) :=
                    Real.rpow_le_rpow hratio_pos.le hub hθ
                _ = 1 := Real.one_rpow _
                _ ≤ Cd * (1 + |Real.log u|) ^ |theta - 1| := by
                    nlinarith [hone_le, hCd1]
            · have habs : |theta - 1| = 1 - theta := by
                rw [abs_of_neg (by linarith : theta - 1 < 0)]
                ring
              have hlb : -Real.log ε₀ / Real.log s
                  ≤ (Real.log s - Real.log u) / Real.log s := by
                gcongr
              calc ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)
                  ≤ (-Real.log ε₀ / Real.log s) ^ (theta - 1) :=
                    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hθ.le
                      (mem_Ioi.mpr (div_pos hε₀log hlogs0))
                      (mem_Ioi.mpr hratio_pos) hlb
                _ = c' * Real.log s ^ (1 - theta) := by
                    rw [Real.div_rpow hε₀log.le hlogs0.le, hc'def,
                      div_eq_mul_inv, ← Real.rpow_neg hlogs0.le,
                      show -(theta - 1) = 1 - theta by ring]
                _ ≤ c' * (2 * Real.log u) ^ (1 - theta) := by
                    refine mul_le_mul_of_nonneg_left ?_ hc'.le
                    exact Real.rpow_le_rpow hlogs0.le (by linarith)
                      (by linarith)
                _ ≤ c' * (2 * (1 + |Real.log u|)) ^ (1 - theta) := by
                    refine mul_le_mul_of_nonneg_left ?_ hc'.le
                    refine Real.rpow_le_rpow (by linarith) ?_ (by linarith)
                    have := le_abs_self (Real.log u)
                    linarith [abs_nonneg (Real.log u)]
                _ = c' * ((2 : ℝ) ^ (1 - theta)
                      * (1 + |Real.log u|) ^ (1 - theta)) := by
                    rw [Real.mul_rpow two_pos.le
                      (by positivity : (0:ℝ) ≤ 1 + |Real.log u|)]
                _ ≤ Cd * (1 + |Real.log u|) ^ |theta - 1| := by
                    rw [← habs]
                    calc c' * ((2 : ℝ) ^ |theta - 1|
                          * (1 + |Real.log u|) ^ |theta - 1|)
                        = c' * (2 : ℝ) ^ |theta - 1|
                            * (1 + |Real.log u|) ^ |theta - 1| := by ring
                      _ ≤ Cd * (1 + |Real.log u|) ^ |theta - 1| :=
                          mul_le_mul_of_nonneg_right hCdc hkernn
        have hker_nn : (0 : ℝ) ≤ Real.exp (-u) * u ^ lam :=
          mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hu.le _)
        rw [Real.norm_of_nonneg (mul_nonneg hker_nn
          (Real.rpow_nonneg hratio_pos.le _))]
        calc Real.exp (-u) * u ^ lam
            * ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)
            ≤ Real.exp (-u) * u ^ lam
              * (Cd * (1 + |Real.log u|) ^ |theta - 1|) :=
              mul_le_mul_of_nonneg_left hpow_le hker_nn
          _ = Cd * (Real.exp (-u) * u ^ lam
              * (1 + |Real.log u|) ^ |theta - 1|) := by ring
      · rw [indicator_of_notMem hmem, norm_zero]
        positivity
    · exact (integrableOn_exp_rpow_log_pow hlam (abs_nonneg _)).const_mul Cd
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun u hu => ?_)
      rw [mem_Ioi] at hu
      have hratio : Tendsto
          (fun s : ℝ => (Real.log s - Real.log u) / Real.log s)
          atTop (𝓝 1) := by
        have h0 : Tendsto (fun s : ℝ => 1 - Real.log u / Real.log s)
            atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub
            (Tendsto.div_atTop tendsto_const_nhds Real.tendsto_log_atTop)
        rw [sub_zero] at h0
        refine h0.congr' ?_
        filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1]
          with s hl
        have : Real.log s ≠ 0 := by linarith
        field_simp
      have hpow : Tendsto (fun s : ℝ =>
          ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1))
          atTop (𝓝 1) := by
        have hc := (Real.continuousAt_rpow_const 1 (theta - 1)
          (Or.inl one_ne_zero)).tendsto
        have hcomp := hc.comp hratio
        rwa [Real.one_rpow] at hcomp
      have hval : Tendsto (fun s : ℝ => Real.exp (-u) * u ^ lam
          * ((Real.log s - Real.log u) / Real.log s) ^ (theta - 1)) atTop
          (𝓝 (Real.exp (-u) * u ^ lam)) := by
        have h1 := hpow.const_mul (Real.exp (-u) * u ^ lam)
        rwa [mul_one] at h1
      refine Tendsto.congr' ?_ hval
      filter_upwards [eventually_ge_atTop (u / ε₀)] with s hs
      have hu_le : u ≤ s * ε₀ := by
        rw [div_le_iff₀ hε₀] at hs
        linarith
      have hmem2 : u ∈ Ioc (0 : ℝ) (s * ε₀) := ⟨hu, hu_le⟩
      rw [indicator_of_mem hmem2]
  rw [hgamma] at hmain
  refine Tendsto.congr' ?_ hmain
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1 : ℝ)] with s hlog1 hs1
  have hlogs0 : (0 : ℝ) < Real.log s := by linarith
  rw [setIntegral_indicator measurableSet_Ioc,
    inter_eq_self_of_subset_right Ioc_subset_Ioi_self, eq_comm,
    ← integral_div]
  refine setIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have hbase_lo : -Real.log ε₀ ≤ Real.log s - Real.log u := by
    have h := Real.log_le_log hu.1 hu.2
    rw [Real.log_mul (by linarith : s ≠ 0) hε₀.ne'] at h
    linarith
  have hbase_pos : (0 : ℝ) < Real.log s - Real.log u :=
    lt_of_lt_of_le hε₀log hbase_lo
  rw [Real.div_rpow hbase_pos.le hlogs0.le]
  ring

end Real
