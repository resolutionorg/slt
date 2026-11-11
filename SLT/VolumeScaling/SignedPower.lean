/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.Basic.Real.Sign
public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import SLT.VolumeScaling.BlockKernel
import SLT.VolumeScaling.Transport
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The signed power chart

The map `x ↦ sgn(x)·|x|^{h+1}` pushes the `|x|^h`-weighted Lebesgue measure on `[-1,1]` to
`(h+1)⁻¹` times unweighted Lebesgue measure on `[-1,1]`: the weight is killed exactly. This is
the per-coordinate substitution that flattens an equal-exponent block onto the unweighted
product of `LFoldProduct`; the second half of the file derives the exponents of an
equal-exponent weighted monomial block on the unit cube (`hasLLCExponentsOn_equal_block`), the
input of the split theorem (`StrictFamily`).
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Real

/-- The signed power map `x ↦ sgn(x)·|x|^a`. -/
noncomputable def signedPow (a x : ℝ) : ℝ := Real.sign x * |x| ^ a

@[simp] theorem signedPow_zero_right (a : ℝ) : signedPow a 0 = 0 := by
  simp [signedPow, Real.sign_zero]

theorem signedPow_of_pos {a x : ℝ} (hx : 0 < x) :
    signedPow a x = x ^ a := by
  rw [signedPow, Real.sign_of_pos hx, abs_of_pos hx, one_mul]

theorem signedPow_of_neg {a x : ℝ} (hx : x < 0) :
    signedPow a x = -(-x) ^ a := by
  rw [signedPow, Real.sign_of_neg hx, abs_of_neg hx, neg_one_mul]

theorem signedPow_neg (a x : ℝ) : signedPow a (-x) = -signedPow a x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [signedPow_of_neg hx, signedPow_of_pos (neg_pos.mpr hx), neg_neg]
  · simp
  · rw [signedPow_of_pos hx, signedPow_of_neg (neg_lt_zero.mpr hx),
      neg_neg]

theorem abs_signedPow {a : ℝ} (ha : 0 < a) (x : ℝ) :
    |signedPow a x| = |x| ^ a := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [signedPow_of_neg hx, abs_neg,
      abs_of_nonneg (Real.rpow_nonneg (neg_nonneg.mpr hx.le) _),
      abs_of_neg hx]
  · simp [Real.zero_rpow ha.ne']
  · rw [signedPow_of_pos hx,
      abs_of_nonneg (Real.rpow_nonneg hx.le _), abs_of_pos hx]

theorem strictMono_signedPow {a : ℝ} (ha : 0 < a) :
    StrictMono (signedPow a) := by
  intro x y hxy
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rcases lt_trichotomy y 0 with hy | rfl | hy
    · rw [signedPow_of_neg hx, signedPow_of_neg hy, neg_lt_neg_iff]
      exact Real.rpow_lt_rpow (neg_nonneg.mpr hy.le)
        (neg_lt_neg hxy) ha
    · rw [signedPow_of_neg hx, signedPow_zero_right, neg_lt_zero]
      exact Real.rpow_pos_of_pos (neg_pos.mpr hx) a
    · rw [signedPow_of_neg hx, signedPow_of_pos hy]
      exact lt_trans (neg_lt_zero.mpr
        (Real.rpow_pos_of_pos (neg_pos.mpr hx) a))
        (Real.rpow_pos_of_pos hy a)
  · rw [signedPow_zero_right, signedPow_of_pos hxy]
    exact Real.rpow_pos_of_pos hxy a
  · rw [signedPow_of_pos hx, signedPow_of_pos (hx.trans hxy)]
    exact Real.rpow_lt_rpow hx.le hxy ha

/-- The signed power maps are mutually inverse. -/
theorem signedPow_signedPow {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    signedPow a⁻¹ (signedPow a x) = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [signedPow_of_neg hx, signedPow_neg,
      signedPow_of_pos (Real.rpow_pos_of_pos (neg_pos.mpr hx) a),
      ← Real.rpow_mul (neg_pos.mpr hx).le, mul_inv_cancel₀ ha,
      Real.rpow_one, neg_neg]
  · simp
  · rw [signedPow_of_pos hx,
      signedPow_of_pos (Real.rpow_pos_of_pos hx a),
      ← Real.rpow_mul hx.le, mul_inv_cancel₀ ha, Real.rpow_one]

theorem signedPow_signedPow_inv {a : ℝ} (ha : a ≠ 0) (t : ℝ) :
    signedPow a (signedPow a⁻¹ t) = t := by
  have h := signedPow_signedPow (a := a⁻¹) (inv_ne_zero ha) t
  rwa [inv_inv] at h

theorem signedPow_preimage_Iic {a : ℝ} (ha : 0 < a) (t : ℝ) :
    signedPow a ⁻¹' (Iic t) = Iic (signedPow a⁻¹ t) := by
  ext x
  rw [mem_preimage, mem_Iic, mem_Iic,
    ← (strictMono_signedPow (inv_pos.mpr ha)).le_iff_le,
    signedPow_signedPow ha.ne']

@[simp] theorem signedPow_one_right {a : ℝ} : signedPow a 1 = 1 := by
  rw [signedPow_of_pos one_pos, Real.one_rpow]

@[simp] theorem signedPow_neg_one_right {a : ℝ} :
    signedPow a (-1) = -1 := by
  rw [signedPow_neg, signedPow_one_right]

theorem measurable_sign : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const)
    measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id)
      measurable_const measurable_const)

theorem measurable_signedPow (a : ℝ) : Measurable (signedPow a) := by
  unfold signedPow
  have h : Measurable fun p : ℝ × ℝ => p.1 ^ p.2 := measurable_pow
  exact Real.measurable_sign.mul
    (h.comp (measurable_abs.prodMk measurable_const))

end Real

namespace SingularLearningTheory

open Real

/-- The endpoint integral of the weight: an exact signed-power
formula, uniform across the sign of the endpoint. -/
theorem integral_abs_rpow_endpoint {h t : ℝ} (hh : 0 ≤ h)
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    ∫ x in (-1 : ℝ)..t, |x| ^ h
      = (1 + signedPow (h + 1) t) / (h + 1) := by
  have hcont : Continuous fun x : ℝ => |x| ^ h :=
    continuous_abs.rpow_const fun x => Or.inr hh
  have hpos : (0 : ℝ) < h + 1 := by linarith
  have hneg1 : ∫ x in (-1 : ℝ)..(0 : ℝ), |x| ^ h = 1 / (h + 1) := by
    have h2 := intervalIntegral.integral_comp_neg (a := (0 : ℝ))
      (b := 1) (fun x => |x| ^ h)
    simp only [abs_neg, neg_zero] at h2
    rw [← h2]
    rw [intervalIntegral.integral_congr (g := fun x => x ^ h) ?_]
    · rw [integral_rpow (Or.inl (by linarith)),
        Real.zero_rpow hpos.ne', sub_zero, Real.one_rpow]
    · intro x hx
      rw [uIcc_of_le one_pos.le, mem_Icc] at hx
      dsimp only
      rw [abs_of_nonneg hx.1]
  rcases le_or_gt 0 t with htpos | htneg
  · have hhalf : ∫ x in (0 : ℝ)..t, |x| ^ h
        = t ^ (h + 1) / (h + 1) := by
      rw [intervalIntegral.integral_congr (g := fun x => x ^ h) ?_]
      · rw [integral_rpow (Or.inl (by linarith)),
          Real.zero_rpow hpos.ne', sub_zero]
      · intro x hx
        rw [uIcc_of_le htpos, mem_Icc] at hx
        dsimp only
        rw [abs_of_nonneg hx.1]
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (a := (-1 : ℝ)) (b := 0) (c := t)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
      hneg1, hhalf]
    rcases eq_or_lt_of_le htpos with rfl | htpos'
    · rw [signedPow_zero_right, Real.zero_rpow hpos.ne']
      ring
    · rw [signedPow_of_pos htpos']
      ring
  · have hsplit : ∫ x in (-1 : ℝ)..(0 : ℝ), |x| ^ h
        = (∫ x in (-1 : ℝ)..t, |x| ^ h)
          + ∫ x in t..(0 : ℝ), |x| ^ h :=
      (intervalIntegral.integral_add_adjacent_intervals
        (hcont.intervalIntegrable _ _)
        (hcont.intervalIntegrable _ _)).symm
    have htail : ∫ x in t..(0 : ℝ), |x| ^ h
        = (-t) ^ (h + 1) / (h + 1) := by
      have h2 := intervalIntegral.integral_comp_neg (a := (0 : ℝ))
        (b := -t) (fun x => |x| ^ h)
      simp only [abs_neg, neg_zero, neg_neg] at h2
      rw [← h2]
      rw [intervalIntegral.integral_congr (g := fun x => x ^ h) ?_]
      · rw [integral_rpow (Or.inl (by linarith)),
          Real.zero_rpow hpos.ne', sub_zero]
      · intro x hx
        rw [uIcc_of_le (neg_nonneg.mpr htneg.le), mem_Icc] at hx
        dsimp only
        rw [abs_of_nonneg hx.1]
    have hs := hsplit
    rw [hneg1, htail] at hs
    rw [signedPow_of_neg htneg]
    linear_combination -hs


/-- The weighted interval measure is finite. -/
theorem weighted_interval_finite {h : ℝ} (hh : 0 ≤ h) :
    IsFiniteMeasure ((volume.restrict (Icc (-1 : ℝ) 1)).withDensity
      fun x => ENNReal.ofReal (|x| ^ h)) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  calc ∫⁻ x, ENNReal.ofReal (|x| ^ h)
        ∂(volume.restrict (Icc (-1 : ℝ) 1))
      ≤ ∫⁻ _, (1 : ℝ≥0∞) ∂(volume.restrict (Icc (-1 : ℝ) 1)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Icc).mpr
          (Filter.Eventually.of_forall fun x hx => ?_))
        exact ENNReal.ofReal_le_one.mpr
          (Real.rpow_le_one (abs_nonneg x)
            (abs_le.mpr ⟨hx.1, hx.2⟩) hh)
    _ < ⊤ := by
        rw [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top

/-- **The signed-power pushforward**: `x ↦ sgn(x)·|x|^{h+1}`
pushes the `|x|^h`-weighted Lebesgue measure on `[-1,1]` to `(h+1)⁻¹`
times unweighted Lebesgue on `[-1,1]`. The weight is killed exactly. -/
theorem map_signedPow_weighted {h : ℝ} (hh : 0 ≤ h) :
    Measure.map (signedPow (h + 1))
      ((volume.restrict (Icc (-1 : ℝ) 1)).withDensity
        fun x => ENNReal.ofReal (|x| ^ h))
    = (ENNReal.ofReal (h + 1))⁻¹ • volume.restrict (Icc (-1 : ℝ) 1) := by
  have hpos : (0 : ℝ) < h + 1 := by linarith
  have := weighted_interval_finite hh
  have hcont : Continuous fun x : ℝ => |x| ^ h :=
    continuous_abs.rpow_const fun x => Or.inr hh
  refine Measure.ext_of_Iic _ _ fun t => ?_
  rw [Measure.map_apply (measurable_signedPow _) measurableSet_Iic,
    signedPow_preimage_Iic hpos,
    withDensity_apply _ measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic,
    Measure.smul_apply, Measure.restrict_apply measurableSet_Iic,
    smul_eq_mul]
  set ss := signedPow (h + 1)⁻¹ t with hssdef
  have hmono := strictMono_signedPow (inv_pos.mpr hpos)
  rcases lt_or_ge t (-1) with ht1 | ht1
  · have hs1 : ss < -1 := by
      rw [hssdef, show (-1 : ℝ) = signedPow (h + 1)⁻¹ (-1) from
        signedPow_neg_one_right.symm]
      exact hmono ht1
    have he1 : Iic ss ∩ Icc (-1 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false,
        iff_false, not_and]
      intro hx h1 _
      linarith
    have he2 : Iic t ∩ Icc (-1 : ℝ) 1 = ∅ := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, mem_empty_iff_false,
        iff_false, not_and]
      intro hx h1 _
      linarith
    rw [he1, he2]
    simp
  rcases le_or_gt t 1 with ht2 | ht2
  · have hs : ss ∈ Icc (-1 : ℝ) 1 := by
      constructor
      · have h1 := hmono.le_iff_le.mpr ht1
        rwa [signedPow_neg_one_right] at h1
      · have h1 := hmono.le_iff_le.mpr ht2
        rwa [signedPow_one_right] at h1
    have hIic1 : Iic ss ∩ Icc (-1 : ℝ) 1 = Icc (-1) ss := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxs, hx1, _⟩
        exact ⟨hx1, hxs⟩
      · rintro ⟨hx1, hxs⟩
        exact ⟨hxs, hx1, hxs.trans hs.2⟩
    have hIic2 : Iic t ∩ Icc (-1 : ℝ) 1 = Icc (-1) t := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxs, hx1, _⟩
        exact ⟨hx1, hxs⟩
      · rintro ⟨hx1, hxs⟩
        exact ⟨hxs, hx1, hxs.trans ht2⟩
    have hint : ∫⁻ x in Icc (-1 : ℝ) ss, ENNReal.ofReal (|x| ^ h)
        = ENNReal.ofReal ((1 + signedPow (h + 1) ss) / (h + 1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (hcont.integrableOn_Icc)
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (abs_nonneg x) h),
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le hs.1,
        integral_abs_rpow_endpoint hh hs]
    rw [hIic1, hIic2, hint, hssdef, signedPow_signedPow_inv hpos.ne',
      Real.volume_Icc, ← ENNReal.ofReal_inv_of_pos hpos,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    congr 1
    field_simp
    ring
  · have hs2 : (1 : ℝ) < ss := by
      have h1 := hmono ht2
      rwa [signedPow_one_right] at h1
    have hfull1 : Iic ss ∩ Icc (-1 : ℝ) 1 = Icc (-1) 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨_, hx⟩
        exact hx
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx2.trans hs2.le, hx1, hx2⟩
    have hfull2 : Iic t ∩ Icc (-1 : ℝ) 1 = Icc (-1) 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨_, hx⟩
        exact hx
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx2.trans ht2.le, hx1, hx2⟩
    have hone : (1 : ℝ) ∈ Icc (-1 : ℝ) 1 := by
      constructor <;> norm_num
    have hint : ∫⁻ x in Icc (-1 : ℝ) 1, ENNReal.ofReal (|x| ^ h)
        = ENNReal.ofReal (2 / (h + 1)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal
        (hcont.integrableOn_Icc)
        (Filter.Eventually.of_forall fun x =>
          Real.rpow_nonneg (abs_nonneg x) h),
        MeasureTheory.integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by norm_num : (-1:ℝ) ≤ 1),
        integral_abs_rpow_endpoint hh hone, signedPow_one_right]
      norm_num
    rw [hfull1, hfull2, hint, Real.volume_Icc,
      ← ENNReal.ofReal_inv_of_pos hpos,
      ← ENNReal.ofReal_mul (inv_nonneg.mpr hpos.le)]
    congr 1
    field_simp
    norm_num

/-! ## The equal-exponent block on the unit cube -/

/-- The signed power map as a measurable equivalence. -/
noncomputable def signedPowEquiv {a : ℝ} (ha : 0 < a) : ℝ ≃ᵐ ℝ where
  toFun := signedPow a
  invFun := signedPow a⁻¹
  left_inv := signedPow_signedPow ha.ne'
  right_inv := signedPow_signedPow_inv ha.ne'
  measurable_toFun := measurable_signedPow a
  measurable_invFun := measurable_signedPow a⁻¹

/-- Restriction moves into the localizing set at the `sublevelVol`
level. -/
theorem sublevelVol_restrict {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S K : Set α} (hS : MeasurableSet S) (f : α → ℝ)
    (ε : ℝ) :
    sublevelVol (μ.restrict S) K f ε = sublevelVol μ (K ∩ S) f ε := by
  unfold sublevelVol
  rw [Measure.restrict_apply' hS, Set.inter_right_comm]

theorem hasLLCExponentsOn_restrict_iff {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {S K : Set α} (hS : MeasurableSet S) {f : α → ℝ}
    {lam theta : ℝ} :
    HasLLCExponentsOn (μ.restrict S) K f lam theta ↔
      HasLLCExponentsOn μ (K ∩ S) f lam theta := by
  unfold HasLLCExponentsOn
  have hVeq : sublevelVol (μ.restrict S) K f
      = sublevelVol μ (K ∩ S) f :=
    funext fun ε => sublevelVol_restrict hS f ε
  rw [hVeq]

/-- **The equal-exponent block**: an equal-`λ` weighted monomial block
on the unit cube has exponents `(λ, m+1)` — the block size is the
multiplicity. -/
theorem hasLLCExponentsOn_equal_block {m : ℕ} {k : Fin (m + 1) → ℕ}
    {h : Fin (m + 1) → ℝ} (hk : ∀ i, 0 < k i) (hh : ∀ i, 0 ≤ h i)
    {lam : ℝ} (heq : ∀ i, (h i + 1) / (2 * k i : ℝ) = lam) :
    HasLLCExponentsOn
      (Measure.pi fun i => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i))
      (Set.univ.pi fun _ : Fin (m + 1) => Icc (-1 : ℝ) 1)
      (fun x => ∏ i, |x i| ^ (2 * k i : ℝ))
      lam (m + 1) := by
  classical
  have hpos : ∀ i, (0 : ℝ) < h i + 1 := fun i => by linarith [hh i]
  have hlam : 0 < lam := by
    rw [← heq 0]
    exact div_pos (hpos 0) (by have := hk 0; positivity)
  set src : Fin (m + 1) → Measure ℝ := fun i =>
    (volume.restrict (Icc (-1 : ℝ) 1)).withDensity
      fun x => ENNReal.ofReal (|x| ^ h i) with hsrc
  set cs : Fin (m + 1) → ℝ≥0∞ := fun i =>
    (ENNReal.ofReal (h i + 1))⁻¹ with hcs
  have hfin : ∀ i, IsFiniteMeasure (src i) := fun i =>
    weighted_interval_finite (hh i)
  have hfin2 : ∀ i, IsFiniteMeasure
      (cs i • volume.restrict (Icc (-1 : ℝ) 1)) := fun i => by
    constructor
    rw [Measure.smul_apply, smul_eq_mul]
    refine ENNReal.mul_lt_top ?_ ?_
    · exact lt_of_le_of_lt (ENNReal.inv_le_one.mpr
        (ENNReal.one_le_ofReal.mpr (by linarith [hh i])))
        ENNReal.one_lt_top
    · rw [Measure.restrict_apply_univ, Real.volume_Icc]
      exact ENNReal.ofReal_lt_top
  have hmp : MeasurePreserving
      (fun (a : Fin (m + 1) → ℝ) i => signedPow (h i + 1) (a i))
      (Measure.pi src)
      (Measure.pi fun i => cs i • volume.restrict (Icc (-1 : ℝ) 1)) :=
    measurePreserving_pi _ _ fun i =>
      ⟨measurable_signedPow _, map_signedPow_weighted (hh i)⟩
  have hpismul : Measure.pi
      (fun i => cs i • volume.restrict (Icc (-1 : ℝ) 1))
      = (∏ i, cs i) • Measure.pi
          (fun _ : Fin (m + 1) => volume.restrict (Icc (-1 : ℝ) 1)) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => rfl
  have hmap : Measure.map
      (MeasurableEquiv.piCongrRight fun i => signedPowEquiv (hpos i))
      (Measure.pi src)
      = (∏ i, cs i) • Measure.pi
          (fun _ : Fin (m + 1) => volume.restrict (Icc (-1 : ℝ) 1)) := by
    rw [show ⇑(MeasurableEquiv.piCongrRight
        fun i => signedPowEquiv (hpos i))
        = fun (a : Fin (m + 1) → ℝ) i => signedPow (h i + 1) (a i)
      from rfl, hmp.map_eq, hpismul]
  have hc0 : (∏ i, cs i) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    rw [hcs]
    exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top
  have hctop : (∏ i, cs i) ≠ ⊤ := by
    refine (ENNReal.prod_lt_top fun i _ => ?_).ne
    rw [hcs]
    exact lt_of_le_of_ne le_top (ENNReal.inv_ne_top.mpr
      (ENNReal.ofReal_pos.mpr (hpos i)).ne')
  have htrans := hasLLCExponentsOn_comp_smul_measurableEquiv
    (μ := Measure.pi src)
    (ν := Measure.pi fun _ : Fin (m + 1) =>
      volume.restrict (Icc (-1 : ℝ) 1))
    (K' := Set.univ)
    (g := fun z => (∏ i, |z i|) ^ (1 / lam))
    (lam := lam) (theta := (m + 1 : ℝ))
    (MeasurableEquiv.piCongrRight fun i => signedPowEquiv (hpos i))
    hc0 hctop hmap
  have hsrcpi : Measure.pi src
      = (Measure.pi fun i => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ h i)).restrict
        (Set.univ.pi fun _ : Fin (m + 1) => Icc (-1 : ℝ) 1) := by
    rw [Measure.restrict_pi_pi]
    refine congrArg Measure.pi (funext fun i => ?_)
    rw [hsrc]
    exact (restrict_withDensity measurableSet_Icc _).symm
  have hrestr : Measure.pi
      (fun _ : Fin (m + 1) => volume.restrict (Icc (-1 : ℝ) 1))
      = (volume : Measure (Fin (m + 1) → ℝ)).restrict
        (Set.univ.pi fun _ => Icc (-1 : ℝ) 1) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hfun : (fun a : Fin (m + 1) → ℝ =>
      (∏ i, |(MeasurableEquiv.piCongrRight
        fun i => signedPowEquiv (hpos i)) a i|) ^ (1 / lam))
      = fun x => ∏ i, |x i| ^ (2 * k i : ℝ) := by
    funext x
    change (∏ i, |signedPow (h i + 1) (x i)|) ^ (1 / lam)
      = ∏ i, |x i| ^ (2 * k i : ℝ)
    rw [Finset.prod_congr rfl
      (fun i _ => abs_signedPow (hpos i) (x i)),
      ← Real.finsetProd_rpow _ _
        (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    have hi : h i + 1 = lam * (2 * (k i : ℝ)) := by
      have h0 := heq i
      have h2k : (2 * (k i : ℝ)) ≠ 0 := by
        have := hk i
        positivity
      rw [div_eq_iff h2k] at h0
      linarith [h0]
    rw [hi]
    field_simp
  have hcube : MeasurableSet
      (Set.univ.pi fun _ : Fin (m + 1) => Icc (-1 : ℝ) 1) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hgoal : HasLLCExponentsOn (Measure.pi src) Set.univ
      (fun x => ∏ i, |x i| ^ (2 * k i : ℝ)) lam (m + 1)
      ↔ HasLLCExponentsOn
        (Measure.pi fun i => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ h i))
        (Set.univ.pi fun _ : Fin (m + 1) => Icc (-1 : ℝ) 1)
        (fun x => ∏ i, |x i| ^ (2 * k i : ℝ)) lam (m + 1) := by
    rw [hsrcpi, hasLLCExponentsOn_restrict_iff hcube, Set.univ_inter]
  rw [← hgoal]
  rw [Set.preimage_univ, hfun] at htrans
  rw [htrans, hrestr, hasLLCExponentsOn_restrict_iff hcube,
    Set.univ_inter]
  exact hasLLCExponentsOn_prod_abs_rpow m hlam

end SingularLearningTheory
