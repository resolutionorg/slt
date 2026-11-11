/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Laplace.Model
public import SLT.VolumeScaling.Invariance
import SLT.VolumeScaling.Laplace.Representation
public import SLT.VolumeScaling.Laplace.Scale
public import SLT.VolumeScaling.Basic

/-!
# The exponent-level Laplace asymptotic

The first assembly theorem of the downstream arc: if `f` has the
volume-scaling exponents `(λ, θ)` on `K` (`HasLLCExponentsOn`, the
two-sided-bound form), is a.e. nonnegative and a.e. measurable on `K`,
and `μ K ≠ ∞`, then the Laplace integral has exactly the matching growth
order:

  `(fun s => ∫_K e^{−s·f} dμ) =Θ[atTop] laplaceScale λ θ`.

The proof chains the pieces: the layer-cake representation turns `Z(s)` into
`s ∫_0^∞ e^{−sε} V(ε) dε`; the head/tail
split isolates a window `(0, ε₀]` on which the scaling bounds
`c₁·llcScale ≤ V ≤ c₂·llcScale` hold; the head Θ-bound
identifies the window contribution with `SingularLearningTheory.laplaceScale` up to constants;
and the tail estimate kills the rest. The nonnegativity threshold
`λ ≥ 0` is not a hypothesis — it is forced by `μ K ≠ ∞`
(`HasLLCExponentsOn.nonneg_lam`).
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal NNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f : α → ℝ}

/-- The model scale is measurable. -/
private theorem measurable_llcScale (lam theta : ℝ) :
    Measurable (llcScale lam theta) := by
  unfold llcScale
  exact (measurable_id.pow_const lam).mul
    (Real.measurable_log.neg.pow_const (theta - 1))

/-- **λ ≥ 0 is forced by finite `K`-mass**:
a negative exponent would make the scale blow up at `0⁺` while the
sublevel volume stays bounded, contradicting the `scale =O V` half of
`HasLLCExponentsOn`. -/
theorem HasLLCExponentsOn.nonneg_lam {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta) (hfin : μ K ≠ ⊤) : 0 ≤ lam := by
  by_contra hneg
  rw [not_le] at hneg
  obtain ⟨C, hC⟩ := Asymptotics.isBigO_iff.mp h.2
  have htop := (tendsto_llcScale_atTop (ha := hneg) (b := theta)).eventually_gt_atTop
    (max (C * (μ K).toReal) 0)
  obtain ⟨ε, hb, hgt⟩ := (hC.and htop).exists
  have hV0 : (0 : ℝ) ≤ sublevelVol μ K f ε := sublevelVol_nonneg μ K f ε
  have hVle : sublevelVol μ K f ε ≤ (μ K).toReal := sublevelVol_le hfin ε
  have hscale_pos : (0 : ℝ) < llcScale lam theta ε :=
    lt_of_le_of_lt (le_max_right _ _) hgt
  rw [Real.norm_of_nonneg hscale_pos.le, Real.norm_of_nonneg hV0] at hb
  have hCV : C * sublevelVol μ K f ε ≤ max (C * (μ K).toReal) 0 := by
    rcases le_or_gt 0 C with hC0 | hC0
    · exact le_trans (mul_le_mul_of_nonneg_left hVle hC0) (le_max_left _ _)
    · exact le_trans (mul_nonpos_of_nonpos_of_nonneg hC0.le hV0) (le_max_right _ _)
  linarith [hb, hCV, hgt]

/-- The ε-side head integrand `e^{−sε}·llcScale λ θ ε` is integrable on
`(0, ε₀]` for `λ > −1`, `s > 0`, `ε₀ ∈ (0,1)`. -/
theorem integrableOn_exp_mul_llcScale {lam theta s ε₀ : ℝ} (hlam : -1 < lam)
    (hs : 0 < s) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    IntegrableOn (fun ε => Real.exp (-(s * ε)) * llcScale lam theta ε)
      (Ioc (0 : ℝ) ε₀) := by
  have hε₀log : (0 : ℝ) < -Real.log ε₀ := neg_pos.mpr (Real.log_neg hε₀ hε₀1)
  set C : ℝ := Real.exp ε₀ * max 1 ((-Real.log ε₀) ^ (theta - 1)) with hCdef
  have hC : 0 ≤ C :=
    mul_nonneg (Real.exp_nonneg _) (le_trans one_pos.le (le_max_left _ _))
  have hgint : IntegrableOn
      (fun ε : ℝ => C * (Real.exp (-ε) * ε ^ lam
        * (1 + |Real.log ε|) ^ |theta - 1|)) (Ioc (0 : ℝ) ε₀) :=
    IntegrableOn.mono_set
      ((integrableOn_exp_rpow_log_pow hlam (abs_nonneg _)).const_mul C)
      Ioc_subset_Ioi_self
  refine Integrable.mono' hgint ?_ ?_
  · exact ((measurable_id.const_mul s).neg.exp.mul
      (measurable_llcScale lam theta)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioc).mpr
      (Eventually.of_forall fun ε hε => ?_)
    have hε0 : (0 : ℝ) < ε := hε.1
    have hε1 : ε < 1 := lt_of_le_of_lt hε.2 hε₀1
    have hlogneg : (0 : ℝ) < -Real.log ε := neg_pos.mpr (Real.log_neg hε0 hε1)
    have hscale_nn : (0 : ℝ) ≤ llcScale lam theta ε := (llcScale_pos ⟨hε0, hε1⟩).le
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) hscale_nn)]
    have hexp1 : Real.exp (-(s * ε)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [hε0, hs]
    have hexp2 : (1 : ℝ) ≤ Real.exp ε₀ * Real.exp (-ε) := by
      rw [← Real.exp_add]
      have : (0 : ℝ) ≤ ε₀ - ε := by linarith [hε.2]
      calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (ε₀ + -ε) := Real.exp_le_exp.mpr (by linarith)
    have hfac : (-Real.log ε) ^ (theta - 1)
        ≤ max 1 ((-Real.log ε₀) ^ (theta - 1))
            * (1 + |Real.log ε|) ^ |theta - 1| := by
      have habs : -Real.log ε ≤ 1 + |Real.log ε| := by
        have := neg_le_abs (Real.log ε)
        linarith [abs_nonneg (Real.log ε)]
      have hbase_lo : -Real.log ε₀ ≤ -Real.log ε := by
        have := Real.log_le_log hε0 hε.2
        linarith
      have hone_le : (1 : ℝ) ≤ (1 + |Real.log ε|) ^ |theta - 1| :=
        Real.one_le_rpow (by linarith [abs_nonneg (Real.log ε)]) (abs_nonneg _)
      rcases le_or_gt 0 (theta - 1) with hθ | hθ
      · calc (-Real.log ε) ^ (theta - 1)
            ≤ (1 + |Real.log ε|) ^ (theta - 1) :=
              Real.rpow_le_rpow hlogneg.le habs hθ
          _ = 1 * (1 + |Real.log ε|) ^ |theta - 1| := by
              rw [abs_of_nonneg hθ, one_mul]
          _ ≤ max 1 ((-Real.log ε₀) ^ (theta - 1))
                * (1 + |Real.log ε|) ^ |theta - 1| :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      · calc (-Real.log ε) ^ (theta - 1)
            ≤ (-Real.log ε₀) ^ (theta - 1) :=
              Real.antitoneOn_rpow_Ioi_of_exponent_nonpos hθ.le
                (mem_Ioi.mpr hε₀log) (mem_Ioi.mpr hlogneg) hbase_lo
          _ = (-Real.log ε₀) ^ (theta - 1) * 1 := (mul_one _).symm
          _ ≤ max 1 ((-Real.log ε₀) ^ (theta - 1))
                * (1 + |Real.log ε|) ^ |theta - 1| :=
              mul_le_mul (le_max_right _ _) hone_le one_pos.le
                (le_trans one_pos.le (le_max_left _ _))
    calc Real.exp (-(s * ε)) * llcScale lam theta ε
        ≤ 1 * llcScale lam theta ε :=
          mul_le_mul_of_nonneg_right hexp1 hscale_nn
      _ = ε ^ lam * (-Real.log ε) ^ (theta - 1) := by rw [one_mul]; rfl
      _ ≤ ε ^ lam * (max 1 ((-Real.log ε₀) ^ (theta - 1))
            * (1 + |Real.log ε|) ^ |theta - 1|) :=
          mul_le_mul_of_nonneg_left hfac (Real.rpow_nonneg hε0.le _)
      _ ≤ (Real.exp ε₀ * Real.exp (-ε))
            * (ε ^ lam * (max 1 ((-Real.log ε₀) ^ (theta - 1))
              * (1 + |Real.log ε|) ^ |theta - 1|)) := by
          refine le_mul_of_one_le_left ?_ hexp2
          positivity
      _ = C * (Real.exp (-ε) * ε ^ lam
            * (1 + |Real.log ε|) ^ |theta - 1|) := by
          rw [hCdef]
          ring

/-- **The exponent-level Laplace asymptotic.** If `f` has the
volume-scaling exponents `(λ, θ)` on `K` and `μ K ≠ ∞`, the Laplace
integral has the matching growth order:

  `(fun s => ∫_K e^{−s·f} dμ) =Θ[atTop] s^{−λ} (log s)^{θ−1}`.

`λ ≥ 0` is derived, not assumed. -/
theorem HasLLCExponentsOn.laplace_isTheta {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta)
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) :
    (fun s => ∫ x in K, Real.exp (-(s * f x)) ∂μ)
      =Θ[atTop] SingularLearningTheory.laplaceScale lam theta := by
  have hlam0 : 0 ≤ lam := h.nonneg_lam hfin
  have hlam : (-1 : ℝ) < lam := by linarith
  obtain ⟨c₁, hc₁, c₂, hc₂, hev⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp h
  obtain ⟨δ, hδmem, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  rw [mem_Ioi] at hδmem
  set ε₀ : ℝ := min (δ / 2) (1 / 2) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by norm_num)
  have hε₀1 : ε₀ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hwin : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      c₁ * llcScale lam theta ε ≤ sublevelVol μ K f ε
        ∧ sublevelVol μ K f ε ≤ c₂ * llcScale lam theta ε := by
    intro ε hε
    refine hsub ⟨hε.1, ?_⟩
    calc ε ≤ ε₀ := hε.2
      _ ≤ δ / 2 := min_le_left _ _
      _ < δ := by linarith
  set Λ : ℝ → ℝ := SingularLearningTheory.laplaceScale lam theta with hΛdef
  set H : ℝ → ℝ := fun s => s * ∫ ε in Ioc (0 : ℝ) ε₀,
    Real.exp (-(s * ε)) * llcScale lam theta ε with hHdef
  have hHTheta : H =Θ[atTop] Λ := mul_setIntegral_head_isTheta hlam hε₀ hε₀1
  have hΛpos : ∀ᶠ s in atTop, 0 < Λ s := SingularLearningTheory.laplaceScale_eventually_pos
  have hHnn : ∀ᶠ s in atTop, 0 ≤ H s := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
    refine mul_nonneg hs.le (setIntegral_nonneg measurableSet_Ioc fun ε hε => ?_)
    exact mul_nonneg (Real.exp_nonneg _)
      (llcScale_pos ⟨hε.1, lt_of_le_of_lt hε.2 hε₀1⟩).le
  obtain ⟨C₂, hC₂ev⟩ := Asymptotics.isBigO_iff.mp hHTheta.1
  obtain ⟨C₃, hC₃ev⟩ := Asymptotics.isBigO_iff.mp hHTheta.2
  have htail_small : ∀ᶠ s in atTop,
      (μ K).toReal * Real.exp (-(s * ε₀)) ≤ Λ s := by
    have hb := (SingularLearningTheory.isLittleO_exp_neg_laplaceScale (lam := lam) (theta := theta)
      hε₀).def (c := ((μ K).toReal + 1)⁻¹) (by positivity)
    filter_upwards [hb, hΛpos] with s hbs hpos
    rw [Real.norm_of_nonneg (Real.exp_nonneg _),
      Real.norm_of_nonneg hpos.le] at hbs
    have hμ : (0 : ℝ) ≤ (μ K).toReal := ENNReal.toReal_nonneg
    have h1 : (μ K).toReal * Real.exp (-(s * ε₀))
        ≤ (μ K).toReal * (((μ K).toReal + 1)⁻¹ * Λ s) :=
      mul_le_mul_of_nonneg_left hbs hμ
    have hco : (μ K).toReal * ((μ K).toReal + 1)⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by positivity)]
      linarith
    have h2 : (μ K).toReal * (((μ K).toReal + 1)⁻¹ * Λ s) ≤ Λ s := by
      calc (μ K).toReal * (((μ K).toReal + 1)⁻¹ * Λ s)
          = (μ K).toReal * ((μ K).toReal + 1)⁻¹ * Λ s := by ring
        _ ≤ 1 * Λ s := mul_le_mul_of_nonneg_right hco hpos.le
        _ = Λ s := one_mul _
    linarith
  have hmain : ∀ᶠ s in atTop,
      c₁ * H s ≤ (∫ x in K, Real.exp (-(s * f x)) ∂μ) ∧
      (∫ x in K, Real.exp (-(s * f x)) ∂μ) ≤ c₂ * H s + Λ s := by
    filter_upwards [eventually_gt_atTop (1 : ℝ), htail_small] with s hs1 htl
    have hs0 : (0 : ℝ) < s := one_pos.trans hs1
    have hrep := setIntegral_exp_neg_mul_eq (μ := μ) (K := K) hf hf0 hfin hs0
    have hsplit := setIntegral_exp_sublevelVol_split
      (μ := μ) (K := K) (f := f) hfin hs0 hε₀
    have hVint : IntegrableOn
        (fun ε => Real.exp (-(s * ε)) * sublevelVol μ K f ε)
        (Ioc (0 : ℝ) ε₀) :=
      IntegrableOn.mono_set (integrableOn_exp_mul_sublevelVol hfin hs0 0)
        Ioc_subset_Ioi_self
    have hSint : IntegrableOn
        (fun ε => Real.exp (-(s * ε)) * llcScale lam theta ε)
        (Ioc (0 : ℝ) ε₀) :=
      integrableOn_exp_mul_llcScale hlam hs0 hε₀ hε₀1
    have hVle : ∫ ε in Ioc (0 : ℝ) ε₀,
        Real.exp (-(s * ε)) * sublevelVol μ K f ε
          ≤ c₂ * ∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * llcScale lam theta ε := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on hVint (hSint.const_mul c₂)
        measurableSet_Ioc fun ε hε => ?_
      calc Real.exp (-(s * ε)) * sublevelVol μ K f ε
          ≤ Real.exp (-(s * ε)) * (c₂ * llcScale lam theta ε) :=
            mul_le_mul_of_nonneg_left (hwin ε hε).2 (Real.exp_nonneg _)
        _ = c₂ * (Real.exp (-(s * ε)) * llcScale lam theta ε) := by ring
    have hVge : c₁ * (∫ ε in Ioc (0 : ℝ) ε₀,
        Real.exp (-(s * ε)) * llcScale lam theta ε)
          ≤ ∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * sublevelVol μ K f ε := by
      rw [← integral_const_mul]
      refine setIntegral_mono_on (hSint.const_mul c₁) hVint
        measurableSet_Ioc fun ε hε => ?_
      calc c₁ * (Real.exp (-(s * ε)) * llcScale lam theta ε)
          = Real.exp (-(s * ε)) * (c₁ * llcScale lam theta ε) := by ring
        _ ≤ Real.exp (-(s * ε)) * sublevelVol μ K f ε :=
            mul_le_mul_of_nonneg_left (hwin ε hε).1 (Real.exp_nonneg _)
    have htail_nn : 0 ≤ ∫ ε in Ioi ε₀,
        Real.exp (-(s * ε)) * sublevelVol μ K f ε :=
      setIntegral_exp_mul_sublevelVol_nonneg _
    have htail_le := mul_setIntegral_exp_sublevelVol_tail_le
      (μ := μ) (K := K) (f := f) hfin hs0 ε₀
    constructor
    · calc c₁ * H s
          = s * (c₁ * ∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * llcScale lam theta ε) := by
            rw [hHdef]; ring
        _ ≤ s * ∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * sublevelVol μ K f ε :=
            mul_le_mul_of_nonneg_left hVge hs0.le
        _ ≤ s * (∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * sublevelVol μ K f ε)
            + s * ∫ ε in Ioi ε₀,
                Real.exp (-(s * ε)) * sublevelVol μ K f ε := by
            nlinarith [htail_nn, hs0.le]
        _ = ∫ x in K, Real.exp (-(s * f x)) ∂μ := by
            rw [hrep, hsplit]; ring
    · calc ∫ x in K, Real.exp (-(s * f x)) ∂μ
          = s * (∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * sublevelVol μ K f ε)
            + s * ∫ ε in Ioi ε₀,
                Real.exp (-(s * ε)) * sublevelVol μ K f ε := by
            rw [hrep, hsplit]; ring
        _ ≤ c₂ * H s + (μ K).toReal * Real.exp (-(s * ε₀)) := by
            have h1 : s * (∫ ε in Ioc (0 : ℝ) ε₀,
                Real.exp (-(s * ε)) * sublevelVol μ K f ε) ≤ c₂ * H s := by
              calc s * (∫ ε in Ioc (0 : ℝ) ε₀,
                  Real.exp (-(s * ε)) * sublevelVol μ K f ε)
                  ≤ s * (c₂ * ∫ ε in Ioc (0 : ℝ) ε₀,
                      Real.exp (-(s * ε)) * llcScale lam theta ε) :=
                    mul_le_mul_of_nonneg_left hVle hs0.le
                _ = c₂ * H s := by rw [hHdef]; ring
            exact add_le_add h1 htail_le
        _ ≤ c₂ * H s + Λ s := by linarith
  have hZnn : ∀ s : ℝ, 0 ≤ ∫ x in K, Real.exp (-(s * f x)) ∂μ :=
    fun s => integral_nonneg fun x => Real.exp_nonneg _
  constructor
  · rw [Asymptotics.isBigO_iff]
    refine ⟨c₂ * max C₂ 0 + 1, ?_⟩
    filter_upwards [hmain, hC₂ev, hΛpos, hHnn] with s hm hb2 hpos hHn
    rw [Real.norm_of_nonneg hHn, Real.norm_of_nonneg hpos.le] at hb2
    have hH_le : H s ≤ max C₂ 0 * Λ s :=
      le_trans hb2 (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
    rw [Real.norm_of_nonneg (hZnn s), Real.norm_of_nonneg hpos.le]
    calc ∫ x in K, Real.exp (-(s * f x)) ∂μ
        ≤ c₂ * H s + Λ s := hm.2
      _ ≤ c₂ * (max C₂ 0 * Λ s) + Λ s := by
          have := mul_le_mul_of_nonneg_left hH_le hc₂.le
          linarith
      _ = (c₂ * max C₂ 0 + 1) * Λ s := by ring
  · rw [Asymptotics.isBigO_iff]
    refine ⟨max C₃ 0 / c₁, ?_⟩
    filter_upwards [hmain, hC₃ev, hΛpos, hHnn] with s hm hb3 hpos hHn
    rw [Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg hHn] at hb3
    have hΛ_le : Λ s ≤ max C₃ 0 * H s :=
      le_trans hb3 (mul_le_mul_of_nonneg_right (le_max_left _ _) hHn)
    rw [Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (hZnn s)]
    have hHZ : H s ≤ (∫ x in K, Real.exp (-(s * f x)) ∂μ) / c₁ := by
      rw [le_div_iff₀ hc₁]
      calc H s * c₁ = c₁ * H s := by ring
        _ ≤ ∫ x in K, Real.exp (-(s * f x)) ∂μ := hm.1
    calc Λ s ≤ max C₃ 0 * H s := hΛ_le
      _ ≤ max C₃ 0 * ((∫ x in K, Real.exp (-(s * f x)) ∂μ) / c₁) :=
          mul_le_mul_of_nonneg_left hHZ (le_max_right _ _)
      _ = max C₃ 0 / c₁ * ∫ x in K, Real.exp (-(s * f x)) ∂μ := by ring


/-! ## The O(1) free-energy form -/

/-- The log of the Laplace scale, for `s > 1`:
`log (laplaceScale λ θ s) = −λ·log s + (θ−1)·log (log s)`. -/
private theorem log_laplaceScale {lam theta s : ℝ} (hs1 : 1 < s) :
    Real.log (SingularLearningTheory.laplaceScale lam theta s)
      = -lam * Real.log s + (theta - 1) * Real.log (Real.log s) := by
  have hs0 : (0 : ℝ) < s := one_pos.trans hs1
  have hlog0 : (0 : ℝ) < Real.log s := Real.log_pos hs1
  unfold SingularLearningTheory.laplaceScale
  rw [Real.log_mul (Real.rpow_pos_of_pos hs0 _).ne'
      (Real.rpow_pos_of_pos hlog0 _).ne',
    Real.log_rpow hs0, Real.log_rpow hlog0]

/-- **The O(1) free-energy form** (the Sampling-4 benchmark
statement): under the volume-scaling exponents, the deterministic free
energy satisfies

  `−log Z(s) = λ·log s − (θ−1)·log log s + O(1)`  as `s → ∞`,

stated as `=O[atTop]` of the constant function. -/
theorem HasLLCExponentsOn.log_laplace_sub_isBigO {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta)
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) :
    (fun s => Real.log (∫ x in K, Real.exp (-(s * f x)) ∂μ)
        + lam * Real.log s - (theta - 1) * Real.log (Real.log s))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have hZTheta := h.laplace_isTheta hf hf0 hfin
  have hΛpos : ∀ᶠ s : ℝ in atTop, 0 < SingularLearningTheory.laplaceScale lam theta s :=
    SingularLearningTheory.laplaceScale_eventually_pos
  have hZnn : ∀ s : ℝ, 0 ≤ ∫ x in K, Real.exp (-(s * f x)) ∂μ :=
    fun s => integral_nonneg fun x => Real.exp_nonneg _
  obtain ⟨C, hCev⟩ := Asymptotics.isBigO_iff.mp hZTheta.1
  obtain ⟨C', hC'ev⟩ := Asymptotics.isBigO_iff.mp hZTheta.2
  have hC'pos : 0 < C' := by
    obtain ⟨s, hb, hpos⟩ := (hC'ev.and hΛpos).exists
    rw [Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (hZnn s)] at hb
    by_contra hle
    rw [not_lt] at hle
    linarith [hb, hpos, mul_nonpos_of_nonpos_of_nonneg hle (hZnn s)]
  set D : ℝ := |Real.log (max C 1)| + |Real.log C'| with hDdef
  rw [Asymptotics.isBigO_iff]
  refine ⟨D, ?_⟩
  filter_upwards [hCev, hC'ev, hΛpos, eventually_gt_atTop (1 : ℝ)]
    with s hb1 hb2 hpos hs1
  rw [Real.norm_of_nonneg hpos.le, Real.norm_of_nonneg (hZnn s)] at hb1 hb2
  have hZub : (∫ x in K, Real.exp (-(s * f x)) ∂μ)
      ≤ max C 1 * SingularLearningTheory.laplaceScale lam theta s :=
    le_trans hb1 (mul_le_mul_of_nonneg_right (le_max_left _ _) hpos.le)
  have hZlb : C'⁻¹ * SingularLearningTheory.laplaceScale lam theta s
      ≤ ∫ x in K, Real.exp (-(s * f x)) ∂μ := by
    rw [inv_mul_le_iff₀ hC'pos]
    linarith [hb2]
  have hZpos : 0 < ∫ x in K, Real.exp (-(s * f x)) ∂μ :=
    lt_of_lt_of_le (mul_pos (inv_pos.mpr hC'pos) hpos) hZlb
  have hlog_ub : Real.log (∫ x in K, Real.exp (-(s * f x)) ∂μ)
      ≤ Real.log (max C 1) + Real.log (SingularLearningTheory.laplaceScale lam theta s) := by
    calc Real.log (∫ x in K, Real.exp (-(s * f x)) ∂μ)
        ≤ Real.log (max C 1 * SingularLearningTheory.laplaceScale lam theta s) :=
          Real.log_le_log hZpos hZub
      _ = Real.log (max C 1) + Real.log (SingularLearningTheory.laplaceScale lam theta s) :=
          Real.log_mul (by positivity) hpos.ne'
  have hlog_lb : Real.log (SingularLearningTheory.laplaceScale lam theta s) - Real.log C'
      ≤ Real.log (∫ x in K, Real.exp (-(s * f x)) ∂μ) := by
    have h1 : Real.log (C'⁻¹ * SingularLearningTheory.laplaceScale lam theta s)
        ≤ Real.log (∫ x in K, Real.exp (-(s * f x)) ∂μ) :=
      Real.log_le_log (mul_pos (inv_pos.mpr hC'pos) hpos) hZlb
    rw [Real.log_mul (inv_pos.mpr hC'pos).ne' hpos.ne', Real.log_inv] at h1
    linarith
  have hΛlog : Real.log (SingularLearningTheory.laplaceScale lam theta s)
      = -lam * Real.log s + (theta - 1) * Real.log (Real.log s) :=
    log_laplaceScale hs1
  rw [Real.norm_eq_abs, norm_one, mul_one, abs_le]
  constructor
  · have h2 := le_abs_self (Real.log C')
    have h3 := abs_nonneg (Real.log (max C 1))
    rw [hDdef]
    linarith [hlog_lb, hΛlog]
  · have h2 := le_abs_self (Real.log (max C 1))
    have h3 := abs_nonneg (Real.log C')
    rw [hDdef]
    linarith [hlog_ub, hΛlog]

/-- **Along the naturals**: the benchmark form
`F_n = λ·log n − (θ−1)·log log n + O(1)`. -/
theorem HasLLCExponentsOn.log_laplace_sub_isBigO_nat {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta)
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) :
    (fun n : ℕ => Real.log (∫ x in K, Real.exp (-((n : ℝ) * f x)) ∂μ)
        + lam * Real.log (n : ℝ) - (theta - 1) * Real.log (Real.log (n : ℝ)))
      =O[atTop] (fun _ : ℕ => (1 : ℝ)) :=
  (h.log_laplace_sub_isBigO hf hf0 hfin).comp_tendsto
    tendsto_natCast_atTop_atTop


/-! ## The prior/withDensity layer -/

section WithDensity

variable {w : α → ℝ≥0∞} {c₁ c₂ : ℝ≥0}

/-- Finite `K`-mass survives a density bounded above on `K`. -/
private theorem withDensity_apply_ne_top (hKm : MeasurableSet K) (hfin : μ K ≠ ⊤)
    (hw : ∀ x ∈ K, w x ≤ (c₂ : ℝ≥0∞)) : (μ.withDensity w) K ≠ ⊤ := by
  rw [withDensity_apply w hKm]
  have hb : ∫⁻ x in K, w x ∂μ ≤ ∫⁻ _x in K, (c₂ : ℝ≥0∞) ∂μ := by
    refine lintegral_mono_ae ?_
    exact (ae_restrict_iff' hKm).mpr (Filter.Eventually.of_forall hw)
  refine ne_top_of_le_ne_top ?_ hb
  rw [setLIntegral_const]
  exact ENNReal.mul_ne_top ENNReal.coe_ne_top hfin

/-- The restricted weighted measure is absolutely continuous with respect
to the restricted base measure. -/
private theorem restrict_withDensity_absolutelyContinuous (hKm : MeasurableSet K) :
    (μ.withDensity w).restrict K ≪ μ.restrict K := by
  rw [restrict_withDensity hKm]
  exact withDensity_absolutelyContinuous _ _

/-- **Θ-form.** The Laplace integral against a re-weighted measure
(a prior with two-sided density bounds on `K`) keeps the growth order. -/
theorem HasLLCExponentsOn.laplace_isTheta_withDensity {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta) (hKm : MeasurableSet K)
    (hc₁ : 0 < c₁) (hw : ∀ x ∈ K, (c₁ : ℝ≥0∞) ≤ w x ∧ w x ≤ c₂)
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) :
    (fun s => ∫ x in K, Real.exp (-(s * f x)) ∂(μ.withDensity w))
      =Θ[atTop] SingularLearningTheory.laplaceScale lam theta := by
  have hac := restrict_withDensity_absolutelyContinuous (μ := μ) (w := w) hKm
  exact (HasLLCExponentsOn.withDensity hKm hfin hc₁ hw h).laplace_isTheta
    (hf.mono_ac hac) (hac.ae_le hf0)
    (withDensity_apply_ne_top hKm hfin fun x hx => (hw x hx).2)

/-- **O(1) free-energy form** for the weighted measure. -/
theorem HasLLCExponentsOn.log_laplace_sub_isBigO_withDensity {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta) (hKm : MeasurableSet K)
    (hc₁ : 0 < c₁) (hw : ∀ x ∈ K, (c₁ : ℝ≥0∞) ≤ w x ∧ w x ≤ c₂)
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) :
    (fun s => Real.log (∫ x in K, Real.exp (-(s * f x)) ∂(μ.withDensity w))
        + lam * Real.log s - (theta - 1) * Real.log (Real.log s))
      =O[atTop] (fun _ : ℝ => (1 : ℝ)) := by
  have hac := restrict_withDensity_absolutelyContinuous (μ := μ) (w := w) hKm
  exact (HasLLCExponentsOn.withDensity hKm hfin hc₁ hw h).log_laplace_sub_isBigO
    (hf.mono_ac hac) (hac.ae_le hf0)
    (withDensity_apply_ne_top hKm hfin fun x hx => (hw x hx).2)

end WithDensity


/-! ## The constant-carrying assembly -/

/-- The per-window sandwich feeding the constant-carrying assembly: if
the sublevel volume is pinched between `(c−δ)·llcScale` and
`(c+δ)·llcScale` on `(0, ε₀]`, then eventually
`(c−δ)·R(s) ≤ Z(s)/Λ(s) ≤ (c+δ)·R(s) + tail(s)`, where `R` is the
2c-normalized head and the tail term is exponentially small. -/
private theorem laplace_ratio_window {lam theta c δ ε₀ : ℝ}
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) (hlam : -1 < lam) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1)
    (hwin : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (c - δ) * llcScale lam theta ε ≤ sublevelVol μ K f ε ∧
      sublevelVol μ K f ε ≤ (c + δ) * llcScale lam theta ε) :
    ∀ᶠ s in atTop,
      (c - δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
          * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
        / Real.log s ^ (theta - 1))
        ≤ (∫ x in K, Real.exp (-(s * f x)) ∂μ) / SingularLearningTheory.laplaceScale lam theta s ∧
      (∫ x in K, Real.exp (-(s * f x)) ∂μ) / SingularLearningTheory.laplaceScale lam theta s
        ≤ (c + δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1))
          + (μ K).toReal * (Real.exp (-(s * ε₀)) / SingularLearningTheory.laplaceScale lam theta
              s) := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with s hs1 hlog1
  have hs0 : (0 : ℝ) < s := one_pos.trans hs1
  have hΛpos : (0 : ℝ) < SingularLearningTheory.laplaceScale lam theta s :=
      SingularLearningTheory.laplaceScale_pos hs1
  have hrep := setIntegral_exp_neg_mul_eq (μ := μ) (K := K) hf hf0 hfin hs0
  have hsplit := setIntegral_exp_sublevelVol_split
    (μ := μ) (K := K) (f := f) hfin hs0 hε₀
  have hVint : IntegrableOn
      (fun ε => Real.exp (-(s * ε)) * sublevelVol μ K f ε)
      (Ioc (0 : ℝ) ε₀) :=
    IntegrableOn.mono_set (integrableOn_exp_mul_sublevelVol hfin hs0 0)
      Ioc_subset_Ioi_self
  have hSint : IntegrableOn
      (fun ε => Real.exp (-(s * ε)) * llcScale lam theta ε)
      (Ioc (0 : ℝ) ε₀) :=
    integrableOn_exp_mul_llcScale hlam hs0 hε₀ hε₀1
  have hVub : ∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * sublevelVol μ K f ε
        ≤ (c + δ) * ∫ ε in Ioc (0 : ℝ) ε₀,
            Real.exp (-(s * ε)) * llcScale lam theta ε := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hVint (hSint.const_mul _)
      measurableSet_Ioc fun ε hε => ?_
    calc Real.exp (-(s * ε)) * sublevelVol μ K f ε
        ≤ Real.exp (-(s * ε)) * ((c + δ) * llcScale lam theta ε) :=
          mul_le_mul_of_nonneg_left (hwin ε hε).2 (Real.exp_nonneg _)
      _ = (c + δ) * (Real.exp (-(s * ε)) * llcScale lam theta ε) := by ring
  have hVlb : (c - δ) * (∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * llcScale lam theta ε)
        ≤ ∫ ε in Ioc (0 : ℝ) ε₀,
            Real.exp (-(s * ε)) * sublevelVol μ K f ε := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hSint.const_mul _) hVint
      measurableSet_Ioc fun ε hε => ?_
    calc (c - δ) * (Real.exp (-(s * ε)) * llcScale lam theta ε)
        = Real.exp (-(s * ε)) * ((c - δ) * llcScale lam theta ε) := by ring
      _ ≤ Real.exp (-(s * ε)) * sublevelVol μ K f ε :=
          mul_le_mul_of_nonneg_left (hwin ε hε).1 (Real.exp_nonneg _)
  have h2a := mul_setIntegral_head_eq_subst
    (lam := lam) (theta := theta) (ε₀ := ε₀) hs0
  have hslam : (0 : ℝ) < s ^ (-lam) := Real.rpow_pos_of_pos hs0 _
  -- the normalized-head identity `X/Λ = I/(log s)^{θ−1}` for
  -- `X := s · (head scale integral)`
  have hHR : s * (∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * llcScale lam theta ε) / SingularLearningTheory.laplaceScale lam theta s
        = (∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1) := by
    rw [h2a, show SingularLearningTheory.laplaceScale lam theta s
        = s ^ (-lam) * Real.log s ^ (theta - 1) from rfl,
      mul_div_mul_left _ _ hslam.ne']
  have htail_nn : 0 ≤ ∫ ε in Ioi ε₀,
      Real.exp (-(s * ε)) * sublevelVol μ K f ε :=
    setIntegral_exp_mul_sublevelVol_nonneg _
  have htail_le := mul_setIntegral_exp_sublevelVol_tail_le
    (μ := μ) (K := K) (f := f) hfin hs0 ε₀
  have hZsplit : (∫ x in K, Real.exp (-(s * f x)) ∂μ)
      = s * (∫ ε in Ioc (0 : ℝ) ε₀,
          Real.exp (-(s * ε)) * sublevelVol μ K f ε)
        + s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * sublevelVol μ K f ε := by
    rw [hrep, hsplit]
    ring
  have habs_lo : (c - δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * llcScale lam theta ε)
        ≤ ∫ x in K, Real.exp (-(s * f x)) ∂μ := by
    rw [hZsplit]
    have h1 : (c - δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
        Real.exp (-(s * ε)) * llcScale lam theta ε)
          = s * ((c - δ) * ∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * llcScale lam theta ε) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hVlb hs0.le
    nlinarith [mul_nonneg hs0.le htail_nn]
  have habs_hi : (∫ x in K, Real.exp (-(s * f x)) ∂μ)
      ≤ (c + δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
          Real.exp (-(s * ε)) * llcScale lam theta ε)
        + (μ K).toReal * Real.exp (-(s * ε₀)) := by
    rw [hZsplit]
    have h2 := mul_le_mul_of_nonneg_left hVub hs0.le
    nlinarith [htail_le]
  constructor
  · rw [← hHR, ← mul_div_assoc]
    gcongr
  · rw [← hHR]
    calc (∫ x in K, Real.exp (-(s * f x)) ∂μ) / SingularLearningTheory.laplaceScale lam theta s
        ≤ ((c + δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
            Real.exp (-(s * ε)) * llcScale lam theta ε)
          + (μ K).toReal * Real.exp (-(s * ε₀))) / SingularLearningTheory.laplaceScale lam theta
              s := by
          gcongr
      _ = (c + δ) * (s * (∫ ε in Ioc (0 : ℝ) ε₀,
            Real.exp (-(s * ε)) * llcScale lam theta ε) / SingularLearningTheory.laplaceScale lam
                theta s)
          + (μ K).toReal * (Real.exp (-(s * ε₀)) / SingularLearningTheory.laplaceScale lam theta
              s) := by
          rw [add_div, mul_div_assoc, mul_div_assoc, mul_div_assoc]

/-- **The constant-carrying Laplace asymptotic.** Under the
ratio-limit form of the volume scaling (`HasLLCOn`, constant `c > 0`),
the Laplace integral has the sharp Watanabe constant:

  `Z(s) / (s^{−λ}(log s)^{θ−1}) → c · Γ(λ+1)`  as `s → ∞`. -/
theorem HasLLCOn.laplace_div_tendsto {lam theta c : ℝ}
    (h : HasLLCOn μ K f lam theta c) (hc : 0 < c)
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) :
    Tendsto (fun s => (∫ x in K, Real.exp (-(s * f x)) ∂μ)
        / SingularLearningTheory.laplaceScale lam theta s) atTop
      (𝓝 (c * Real.Gamma (lam + 1))) := by
  have hexp := h.hasLLCExponentsOn hc
  have hlam0 : 0 ≤ lam := hexp.nonneg_lam hfin
  have hlam : (-1 : ℝ) < lam := by linarith
  have hΓ : 0 < Real.Gamma (lam + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hwinex : ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        (c - δ) * llcScale lam theta ε ≤ sublevelVol μ K f ε ∧
        sublevelVol μ K f ε ≤ (c + δ) * llcScale lam theta ε := by
    intro δ hδ
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        sublevelVol μ K f ε / llcScale lam theta ε ∈ Ioo (c - δ) (c + δ) :=
      h (Ioo_mem_nhds (by linarith) (by linarith))
    have hev2 := hev.and
      (llcScale_eventually_pos (lam := lam) (theta := theta))
    obtain ⟨b, hbmem, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev2
    rw [mem_Ioi] at hbmem
    refine ⟨min (b / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), fun ε hε => ?_⟩
    have hmem : ε ∈ Ioo (0 : ℝ) b := by
      refine ⟨hε.1, ?_⟩
      calc ε ≤ min (b / 2) (1 / 2) := hε.2
        _ ≤ b / 2 := min_le_left _ _
        _ < b := by linarith
    obtain ⟨hratio, hpos⟩ := hsub hmem
    rw [mem_Ioo] at hratio
    constructor
    · have h1 := hratio.1
      rw [lt_div_iff₀ hpos] at h1
      linarith
    · have h1 := hratio.2
      rw [div_lt_iff₀ hpos] at h1
      linarith
  rw [tendsto_order]
  constructor
  · intro a ha
    set δ : ℝ := min (c / 2)
      ((c * Real.Gamma (lam + 1) - a) / (2 * (c + Real.Gamma (lam + 1) + 1)))
      with hδdef
    have hnum : 0 < c * Real.Gamma (lam + 1) - a := by linarith
    have hden : (0 : ℝ) < 2 * (c + Real.Gamma (lam + 1) + 1) := by positivity
    have hδpos : 0 < δ := lt_min (by linarith) (div_pos hnum hden)
    have hδc : δ ≤ c / 2 := min_le_left _ _
    have hδ2 : δ * (2 * (c + Real.Gamma (lam + 1) + 1))
        ≤ c * Real.Gamma (lam + 1) - a := by
      have := min_le_right (c / 2)
        ((c * Real.Gamma (lam + 1) - a) / (2 * (c + Real.Gamma (lam + 1) + 1)))
      calc δ * (2 * (c + Real.Gamma (lam + 1) + 1))
          ≤ (c * Real.Gamma (lam + 1) - a)
              / (2 * (c + Real.Gamma (lam + 1) + 1))
              * (2 * (c + Real.Gamma (lam + 1) + 1)) := by
            exact mul_le_mul_of_nonneg_right this hden.le
        _ = c * Real.Gamma (lam + 1) - a := div_mul_cancel₀ _ hden.ne'
    obtain ⟨ε₀, hε₀, hε₀1, hwin⟩ := hwinex δ hδpos
    have hsand := laplace_ratio_window (μ := μ) (K := K) (f := f)
      hf hf0 hfin hlam hε₀ hε₀1 hwin
    have hR := Real.head_subst_div_tendsto_gamma
      (lam := lam) (theta := theta) (ε₀ := ε₀) hlam hε₀ hε₀1
    have hRev := hR.eventually (Ioo_mem_nhds
      (show Real.Gamma (lam + 1) - δ < Real.Gamma (lam + 1) by linarith)
      (show Real.Gamma (lam + 1) < Real.Gamma (lam + 1) + δ by linarith))
    filter_upwards [hsand, hRev] with s hs hRs
    have hcδ : 0 < c - δ := by linarith
    have hkey : a < (c - δ) * (Real.Gamma (lam + 1) - δ) := by
      nlinarith [hδ2, hnum, hδpos, sq_nonneg δ]
    calc a < (c - δ) * (Real.Gamma (lam + 1) - δ) := hkey
      _ ≤ (c - δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1)) :=
          mul_le_mul_of_nonneg_left hRs.1.le hcδ.le
      _ ≤ _ := hs.1
  · intro b hb
    set δ : ℝ := min (min (c / 2) 1)
      ((b - c * Real.Gamma (lam + 1)) / (2 * (c + Real.Gamma (lam + 1) + 2)))
      with hδdef
    have hnum : 0 < b - c * Real.Gamma (lam + 1) := by linarith
    have hden : (0 : ℝ) < 2 * (c + Real.Gamma (lam + 1) + 2) := by positivity
    have hδpos : 0 < δ :=
      lt_min (lt_min (by linarith) one_pos) (div_pos hnum hden)
    have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ2 : δ * (2 * (c + Real.Gamma (lam + 1) + 2))
        ≤ b - c * Real.Gamma (lam + 1) := by
      have hm := min_le_right (min (c / 2) 1)
        ((b - c * Real.Gamma (lam + 1)) / (2 * (c + Real.Gamma (lam + 1) + 2)))
      calc δ * (2 * (c + Real.Gamma (lam + 1) + 2))
          ≤ (b - c * Real.Gamma (lam + 1))
              / (2 * (c + Real.Gamma (lam + 1) + 2))
              * (2 * (c + Real.Gamma (lam + 1) + 2)) :=
            mul_le_mul_of_nonneg_right hm hden.le
        _ = b - c * Real.Gamma (lam + 1) := div_mul_cancel₀ _ hden.ne'
    obtain ⟨ε₀, hε₀, hε₀1, hwin⟩ := hwinex δ hδpos
    have hsand := laplace_ratio_window (μ := μ) (K := K) (f := f)
      hf hf0 hfin hlam hε₀ hε₀1 hwin
    have hR := Real.head_subst_div_tendsto_gamma
      (lam := lam) (theta := theta) (ε₀ := ε₀) hlam hε₀ hε₀1
    have hRev := hR.eventually (Ioo_mem_nhds
      (show Real.Gamma (lam + 1) - δ < Real.Gamma (lam + 1) by linarith)
      (show Real.Gamma (lam + 1) < Real.Gamma (lam + 1) + δ by linarith))
    have htail0 : Tendsto (fun s => (μ K).toReal
        * (Real.exp (-(s * ε₀)) / SingularLearningTheory.laplaceScale lam theta s)) atTop (𝓝 0) :=
            by
      have h0 := (SingularLearningTheory.tendsto_exp_neg_mul_div_laplaceScale
        (lam := lam) (theta := theta) hε₀).const_mul (μ K).toReal
      simpa using h0
    have htailev := htail0.eventually_lt_const hδpos
    filter_upwards [hsand, hRev, htailev] with s hs hRs htl
    have hδsq : δ * δ ≤ δ := by nlinarith [hδ1, hδpos]
    have hkey : (c + δ) * (Real.Gamma (lam + 1) + δ) + δ < b := by
      nlinarith [hδ2, hnum, hδsq]
    calc (∫ x in K, Real.exp (-(s * f x)) ∂μ) / SingularLearningTheory.laplaceScale lam theta s
        ≤ (c + δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1))
          + (μ K).toReal * (Real.exp (-(s * ε₀)) / SingularLearningTheory.laplaceScale lam theta
              s) :=
          hs.2
      _ ≤ (c + δ) * (Real.Gamma (lam + 1) + δ) + δ := by
          have h1 : (c + δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
              * (u ^ lam * (Real.log s - Real.log u) ^ (theta - 1)))
            / Real.log s ^ (theta - 1))
              ≤ (c + δ) * (Real.Gamma (lam + 1) + δ) :=
            mul_le_mul_of_nonneg_left hRs.2.le (by linarith)
          linarith [htl]
      _ < b := hkey

/-- **The sharp free-energy limit.** Under `HasLLCOn` with
constant `c > 0`:

  `log Z(s) + λ·log s − (θ−1)·log log s → log (c·Γ(λ+1))`. -/
theorem HasLLCOn.log_laplace_tendsto {lam theta c : ℝ}
    (h : HasLLCOn μ K f lam theta c) (hc : 0 < c)
    (hf : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    (hfin : μ K ≠ ⊤) :
    Tendsto (fun s => Real.log (∫ x in K, Real.exp (-(s * f x)) ∂μ)
        + lam * Real.log s - (theta - 1) * Real.log (Real.log s)) atTop
      (𝓝 (Real.log (c * Real.Gamma (lam + 1)))) := by
  have hexp := h.hasLLCExponentsOn hc
  have hlam0 : 0 ≤ lam := hexp.nonneg_lam hfin
  have hΓ : 0 < Real.Gamma (lam + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hT : 0 < c * Real.Gamma (lam + 1) := mul_pos hc hΓ
  have h4 := h.laplace_div_tendsto hc hf hf0 hfin
  have hlog := h4.log hT.ne'
  refine Tendsto.congr' ?_ hlog
  have hZev := h4.eventually (Ioo_mem_nhds
    (show c * Real.Gamma (lam + 1) / 2 < c * Real.Gamma (lam + 1) by linarith)
    (lt_add_one _))
  filter_upwards [hZev, SingularLearningTheory.laplaceScale_eventually_pos,
    eventually_gt_atTop (1 : ℝ)] with s hZΛ hΛ hs1
  have hZpos : 0 < ∫ x in K, Real.exp (-(s * f x)) ∂μ := by
    have h1 : 0 < (∫ x in K, Real.exp (-(s * f x)) ∂μ)
        / SingularLearningTheory.laplaceScale lam theta s := lt_trans (by positivity) hZΛ.1
    by_contra hle
    rw [not_lt] at hle
    have := div_nonpos_of_nonpos_of_nonneg hle hΛ.le
    linarith
  rw [Real.log_div hZpos.ne' hΛ.ne', log_laplaceScale hs1]
  ring

end SingularLearningTheory
