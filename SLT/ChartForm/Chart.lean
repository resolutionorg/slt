/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.Structural.Terminal
public import SLT.VolumeScaling.ChartFamily.Defs
import SLT.MeasureTheory.Measure.Lebesgue.CoordHyperplanes
import SLT.PartialResolution.ExactTransport
import SLT.PartialResolution.Structural.Translate
import SLT.ChartForm.Fibre
import SLT.VolumeScaling.ChartFamily.Basic
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The recentred terminal chart as a chart of a chart family

A terminal chart `IsMonomialChart K φ dom e h W` recentred at a point `b ∈ W` with `φ b = w`, on a
closed cube `closedBall 0 ϱ` small enough that `b + closedBall 0 ϱ ⊆ W` and that the translated
chart of `IsMonomialChart.translate` is terminal on it, is a
`ResolutionChartData (Fin n → ℝ) (fun x => |K x|) w`: the box is the cube, the parametrization is
`z ↦ φ (b + z)` carried by the coordinatewise retraction `clampTo ϱ` onto the cube (the fields
`φ_continuous` and `Measurable` of the structure are global, while `φ` is only known on `W`), the
Jacobian factor is `|det D(φ (b + ·))|`, the exponent vectors are `e` and `h` restricted to
`J(b) = {k : b_k = 0}` (nonzero by `Fibre.lean`), and the two-sided bounds are the minimum and
maximum of the continuous nonvanishing units on the compact cube. The transport of Lebesgue measure
is built directly on the cube: Mathlib's Jacobian change of variables
`lintegral_image_eq_lintegral_abs_det_fderiv_mul` on the measurable set where the Jacobian monomial
does not vanish (there the translated chart is injective), upgraded to arbitrary subsets through
measurable hulls exactly as `PartialResolution.transportsToOn` does, and extended across the null
set `{z^h = 0}` (a finite union of coordinate hyperplanes, with null image because the chart is
differentiable there) by `TransportsToOn.mono_ae`. The general lemma
`transportsToOn_of_injOn_of_hasFDerivWithinAt` is `PartialResolution.transportsToOn` freed from the
`PartialResolution` structure and from the global measurability of the differentiable carrier.

Not in the sources: the analytic bookkeeping behind [BM88, Theorem 4.4(3), p. 23] in chart form.
-/

@[expose] public section

open Set MeasureTheory Analytic
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {n : ℕ}

/-! ### The change of variables on a set -/

/-- Measurable case of the Jacobian change of variables for a map injective on a measurable set,
with the derivative of a carrier `ψ` within the set (Mathlib's
`lintegral_image_eq_lintegral_abs_det_fderiv_mul`). -/
theorem _root_.MeasurableSet.lintegral_image_of_injOn_of_hasFDerivWithinAt {s : Set (Fin n → ℝ)}
    (hs : MeasurableSet s)
    {φ ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hder : ∀ x ∈ s, HasFDerivWithinAt φ (fderiv ℝ ψ x) s x)
    (hinj : InjOn φ s) (g : (Fin n → ℝ) → ℝ≥0∞) :
    ∫⁻ x in s, g (φ x) * ENNReal.ofReal |(fderiv ℝ ψ x).det| = ∫⁻ y in φ '' s, g y := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hder hinj g]
  exact lintegral_congr fun _ => mul_comm _ _

/-- A map that is injective on a measurable set `s` of finite measure and finite image measure,
with `HasFDerivWithinAt φ (fderiv ℝ ψ x) s x` at every point of `s`, transports Lebesgue measure
exactly on `s` with density `|det D ψ|`, over arbitrary subsets of `s`, through measurable hulls
(the argument of `PartialResolution.transportsToOn`). -/
theorem transportsToOn_of_injOn_of_hasFDerivWithinAt {s : Set (Fin n → ℝ)} (hs : MeasurableSet s)
    (hsfin : volume s ≠ ⊤) {φ ψ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : Measurable φ)
    (himg : volume (φ '' s) ≠ ⊤) (hder : ∀ x ∈ s, HasFDerivWithinAt φ (fderiv ℝ ψ x) s x)
    (hinj : InjOn φ s) :
    TransportsToOn volume volume s φ (fun x => ENNReal.ofReal |(fderiv ℝ ψ x).det|) := by
  have hJ : Measurable fun x => ENNReal.ofReal |(fderiv ℝ ψ x).det| :=
    ((ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ ψ)).abs).ennreal_ofReal
  refine ⟨hφ, hJ, fun t hsub g _ => ?_⟩
  have htfin : volume t ≠ ⊤ := ((measure_mono hsub).trans_lt hsfin.lt_top).ne
  have htimg : volume (φ '' t) ≠ ⊤ :=
    ((measure_mono (image_mono hsub)).trans_lt himg.lt_top).ne
  have hmeas : ∀ m : Set (Fin n → ℝ), MeasurableSet m → m ⊆ s →
      ∫⁻ x in m, g (φ x) * ENNReal.ofReal |(fderiv ℝ ψ x).det| = ∫⁻ y in φ '' m, g y :=
    fun m hm hms => MeasurableSet.lintegral_image_of_injOn_of_hasFDerivWithinAt hm
      (fun x hx => (hder x (hms hx)).mono hms) (hinj.mono hms) g
  -- the outer measurable hull, clipped to `s`
  set m₁ := toMeasurable volume t ∩ s with hm₁def
  have hm₁ : MeasurableSet m₁ := (measurableSet_toMeasurable _ _).inter hs
  have hsm₁ : t ⊆ m₁ := subset_inter (subset_toMeasurable _ _) hsub
  have hrestr₁ : volume.restrict m₁ = volume.restrict t :=
    le_antisymm
      ((Measure.restrict_mono inter_subset_left le_rfl).trans
        (Measure.restrict_toMeasurable htfin).le)
      (Measure.restrict_mono hsm₁ le_rfl)
  -- the hull further clipped to the preimage of the image hull
  set m₂ := m₁ ∩ φ ⁻¹' (toMeasurable volume (φ '' t)) with hm₂def
  have hm₂ : MeasurableSet m₂ := hm₁.inter (hφ (measurableSet_toMeasurable _ _))
  have hsm₂ : t ⊆ m₂ :=
    subset_inter hsm₁ fun x hx => subset_toMeasurable _ _ (mem_image_of_mem _ hx)
  have hrestr₂ : volume.restrict m₂ = volume.restrict t :=
    le_antisymm ((Measure.restrict_mono inter_subset_left le_rfl).trans hrestr₁.le)
      (Measure.restrict_mono hsm₂ le_rfl)
  apply le_antisymm
  · calc ∫⁻ x in t, g (φ x) * ENNReal.ofReal |(fderiv ℝ ψ x).det|
        = ∫⁻ x in m₂, g (φ x) * ENNReal.ofReal |(fderiv ℝ ψ x).det| := by rw [hrestr₂]
      _ = ∫⁻ y in φ '' m₂, g y := hmeas m₂ hm₂ (inter_subset_left.trans inter_subset_right)
      _ ≤ ∫⁻ y in toMeasurable volume (φ '' t), g y :=
          lintegral_mono' (Measure.restrict_mono (fun y hy => by
            obtain ⟨x, hxm, rfl⟩ := hy
            exact hxm.2) le_rfl) le_rfl
      _ = ∫⁻ y in φ '' t, g y := by rw [Measure.restrict_toMeasurable htimg]
  · calc ∫⁻ y in φ '' t, g y
        ≤ ∫⁻ y in φ '' m₁, g y :=
          lintegral_mono' (Measure.restrict_mono (image_mono hsm₁) le_rfl) le_rfl
      _ = ∫⁻ x in m₁, g (φ x) * ENNReal.ofReal |(fderiv ℝ ψ x).det| :=
          (hmeas m₁ hm₁ inter_subset_right).symm
      _ = ∫⁻ x in t, g (φ x) * ENNReal.ofReal |(fderiv ℝ ψ x).det| := by rw [hrestr₁]

/-! ### The retraction onto a cube -/

/-- The coordinatewise retraction of `ℝ^n` onto the closed cube `closedBall 0 ϱ` (sup norm): each
coordinate is clamped to `[-ϱ, ϱ]`. It carries the recentred chart to a globally continuous map
agreeing with `z ↦ φ (b + z)` on the cube. -/
def clampTo (ϱ : ℝ) (z : Fin n → ℝ) : Fin n → ℝ := fun k => max (-ϱ) (min ϱ (z k))

/-- The retraction onto the cube is continuous. -/
theorem continuous_clampTo (ϱ : ℝ) : Continuous (clampTo (n := n) ϱ) :=
  continuous_pi fun k => continuous_const.max (continuous_const.min (continuous_apply k))

/-- The retraction lands in the closed cube. -/
theorem clampTo_mem_closedBall {ϱ : ℝ} (hϱ : 0 ≤ ϱ) (z : Fin n → ℝ) :
    clampTo ϱ z ∈ Metric.closedBall (0 : Fin n → ℝ) ϱ := by
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hϱ]
  intro k
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

/-- The retraction is the identity on the closed cube. -/
theorem clampTo_of_mem {ϱ : ℝ} {z : Fin n → ℝ} (hz : z ∈ Metric.closedBall (0 : Fin n → ℝ) ϱ) :
    clampTo ϱ z = z := by
  have hϱ : 0 ≤ ϱ := (norm_nonneg z).trans (mem_closedBall_zero_iff.mp hz)
  have hk : ∀ k, |z k| ≤ ϱ := fun k => by
    have := (pi_norm_le_iff_of_nonneg hϱ).mp (mem_closedBall_zero_iff.mp hz) k
    rwa [Real.norm_eq_abs] at this
  funext k
  simp only [clampTo]
  rw [min_eq_right (abs_le.mp (hk k)).2, max_eq_right (abs_le.mp (hk k)).1]

/-! ### The recentred chart -/

/-- The absolute value of the monomial `z^e` restricted to the coordinates vanishing at `b` is the
monomial `mon` of the restricted exponent vector. -/
theorem abs_monomialEval_filter (z b : Fin n → ℝ) (e : Fin n →₀ ℕ) :
    |monomialEval z (e.filter fun k => b k = 0)| =
      mon (fun k => if b k = 0 then e k else 0) z := by
  classical
  rw [monomialEval_eq_prod, Finset.abs_prod, mon]
  exact Finset.prod_congr rfl fun k _ => by rw [abs_pow, Finsupp.filter_apply]

/-- The terminal chart `φ` recentred at `b ∈ W` with `φ b = w`, on a closed cube `closedBall 0 ϱ`
with `b + closedBall 0 ϱ ⊆ W`, is a chart of a chart family for the loss `|K|` at `w`: image
`φ '' closedBall b ϱ`, dimension `n`, loss and Jacobian exponents `e|_{J(b)}` and `h|_{J(b)}`, and
the exact transport of Lebesgue measure on its box. -/
theorem _root_.Analytic.IsMonomialChart.exists_resolutionChartData {K : (Fin n → ℝ) → ℝ}
    {φ : (Fin n → ℝ) → (Fin n → ℝ)} {dom W : Set (Fin n → ℝ)} {e h : Fin n →₀ ℕ}
    (hc : IsMonomialChart K φ dom e h W) {b w : Fin n → ℝ} (hb : b ∈ W) (hφb : φ b = w)
    (h0 : K w = 0) :
    ∃ ϱ : ℝ, 0 < ϱ ∧ Metric.closedBall b ϱ ⊆ W ∧
      ∃ χ : ResolutionChartData (Fin n → ℝ) (fun x => |K x|) w,
        χ.φ '' χ.K = φ '' Metric.closedBall b ϱ ∧
        TransportsToOn volume volume χ.K χ.φ (fun u => ENNReal.ofReal (χ.jacAbs u)) ∧
        ∃ hd : χ.d = n,
          (∀ k : Fin n, χ.e (Fin.cast hd.symm k) = if b k = 0 then e k else 0) ∧
          ∀ k : Fin n, χ.h (Fin.cast hd.symm k) = if b k = 0 then h k else 0 := by
  classical
  obtain ⟨W', hW'o, h0W', hchart⟩ := hc.translate hb
  obtain ⟨r, hr, hrW'⟩ := Metric.isOpen_iff.mp hW'o 0 h0W'
  obtain ⟨r', hr', hr'W⟩ := Metric.isOpen_iff.mp hc.isOpen b hb
  set ϱ : ℝ := min (r / 2) (r' / 2) with hϱdef
  have hϱ : 0 < ϱ := lt_min (half_pos hr) (half_pos hr')
  have hcubeW' : Metric.closedBall (0 : Fin n → ℝ) ϱ ⊆ W' :=
    (Metric.closedBall_subset_ball ((min_le_left _ _).trans_lt (half_lt_self hr))).trans hrW'
  have hcubeW : Metric.closedBall b ϱ ⊆ W :=
    (Metric.closedBall_subset_ball ((min_le_right _ _).trans_lt (half_lt_self hr'))).trans hr'W
  set ψ : (Fin n → ℝ) → (Fin n → ℝ) := fun z => φ (b + z) with hψ
  have hc' : IsMonomialChart K ψ (Metric.closedBall 0 ϱ) (e.filter fun k => b k = 0)
      (h.filter fun k => b k = 0) W' := hchart _ hcubeW'
  obtain ⟨u, hu, hu0, hue⟩ := hc'.exists_unit
  obtain ⟨v, hv, hv0, hvh⟩ := hc'.exists_jacUnit
  set Φ : (Fin n → ℝ) → (Fin n → ℝ) := fun z => ψ (clampTo ϱ z) with hΦ
  have hΦeq : EqOn Φ ψ (Metric.closedBall 0 ϱ) := fun z hz => by
    simp only [hΦ, clampTo_of_mem hz]
  have hcl : ∀ z, clampTo ϱ z ∈ Metric.closedBall (0 : Fin n → ℝ) ϱ :=
    clampTo_mem_closedBall hϱ.le
  have hclW' : ∀ z, clampTo ϱ z ∈ W' := fun z => hcubeW' (hcl z)
  have hψc : ContinuousOn ψ W' := hc'.analyticOnNhd.continuousOn
  have hΦc : Continuous Φ := hψc.comp_continuous (continuous_clampTo ϱ) hclW'
  have hψdiff : ∀ z ∈ W', DifferentiableAt ℝ ψ z := fun z hz =>
    (hc'.analyticOnNhd z hz).differentiableAt
  -- the compact cube and the extrema of the units on it
  have hcube : IsCompact (Metric.closedBall (0 : Fin n → ℝ) ϱ) := isCompact_closedBall _ _
  have hne : (Metric.closedBall (0 : Fin n → ℝ) ϱ).Nonempty := ⟨0, Metric.mem_closedBall_self hϱ.le⟩
  have huc : ContinuousOn (fun z => |u z|) (Metric.closedBall 0 ϱ) := (hu.mono hcubeW').abs
  have hvc : ContinuousOn (fun z => |v z|) (Metric.closedBall 0 ϱ) := (hv.mono hcubeW').abs
  obtain ⟨zu, hzu, hzumin⟩ := hcube.exists_isMinOn hne huc
  obtain ⟨zU, hzU, hzUmax⟩ := hcube.exists_isMaxOn hne huc
  obtain ⟨zv, hzv, hzvmin⟩ := hcube.exists_isMinOn hne hvc
  obtain ⟨zV, hzV, hzVmax⟩ := hcube.exists_isMaxOn hne hvc
  rw [isMinOn_iff] at hzumin hzvmin
  rw [isMaxOn_iff] at hzUmax hzVmax
  -- the values of the loss and of the Jacobian on the cube
  have hloss : ∀ z ∈ Metric.closedBall (0 : Fin n → ℝ) ϱ,
      |K (Φ z)| = |u z| * mon (fun k => if b k = 0 then e k else 0) z := fun z hz => by
    rw [hΦeq hz, hue z (hcubeW' hz), abs_mul, abs_monomialEval_filter]
  have hjac : ∀ z ∈ Metric.closedBall (0 : Fin n → ℝ) ϱ,
      |(fderiv ℝ ψ z).det| = |v z| * mon (fun k => if b k = 0 then h k else 0) z := fun z hz => by
    rw [hvh z (hcubeW' hz), abs_mul, abs_monomialEval_filter]
  have hlossc : Continuous fun z => |K (Φ z)| := by
    have : (fun z => |K (Φ z)|) =
        fun z => |u (clampTo ϱ z)| * mon (fun k => if b k = 0 then e k else 0) (clampTo ϱ z) :=
      funext fun z => by
        simp only [hΦ]
        rw [hue _ (hclW' z), abs_mul, abs_monomialEval_filter]
    rw [this]
    exact ((hu.comp_continuous (continuous_clampTo ϱ) hclW').abs).mul
      ((continuous_mon _).comp (continuous_clampTo ϱ))
  -- the chart
  let χ : ResolutionChartData (Fin n → ℝ) (fun x => |K x|) w :=
    { d := n
      K := Metric.closedBall 0 ϱ
      zero_mem_interior := mem_interior_iff_mem_nhds.mpr (Metric.closedBall_mem_nhds 0 hϱ)
      φ := Φ
      φ_continuous := hΦc
      φ_zero := by
        simp only [hΦ, clampTo_of_mem (Metric.mem_closedBall_self hϱ.le), hψ, add_zero, hφb]
      jacAbs := fun z => |(fderiv ℝ ψ z).det|
      e := fun k => if b k = 0 then e k else 0
      h := fun k => if b k = 0 then h k else 0
      e_ne_zero := hc.restricted_exponent_ne_zero hb (by rw [hφb]; exact h0)
      cf := |u zu|
      Cf := |u zU|
      cf_pos := abs_pos.mpr (hu0 zu (hcubeW' hzu))
      cf_le_Cf := hzumin zU hzU
      cJ := |v zv|
      CJ := |v zV|
      cJ_pos := abs_pos.mpr (hv0 zv (hcubeW' hzv))
      cJ_le_CJ := hzvmin zV hzV
      loss_lb := fun z hz => by
        show |u zu| * mon _ z ≤ |K (Φ z)|
        rw [hloss z hz]
        exact mul_le_mul_of_nonneg_right (hzumin z hz) (mon_nonneg _ _)
      loss_ub := fun z hz => by
        show |K (Φ z)| ≤ |u zU| * mon _ z
        rw [hloss z hz]
        exact mul_le_mul_of_nonneg_right (hzUmax z hz) (mon_nonneg _ _)
      jac_lb := fun z hz => by
        show |v zv| * mon _ z ≤ |(fderiv ℝ ψ z).det|
        rw [hjac z hz]
        exact mul_le_mul_of_nonneg_right (hzvmin z hz) (mon_nonneg _ _)
      jac_ub := fun z hz => by
        show |(fderiv ℝ ψ z).det| ≤ |v zV| * mon _ z
        rw [hjac z hz]
        exact mul_le_mul_of_nonneg_right (hzVmax z hz) (mon_nonneg _ _)
      K_bounded := Metric.isBounded_closedBall
      K_measurable := measurableSet_closedBall
      loss_measurable := hlossc.measurable
      jacAbs_measurable :=
        (ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ ψ)).abs }
  -- the transport on the cube: off the Jacobian monomial's zero set, then across it
  set s₀ := Metric.closedBall (0 : Fin n → ℝ) ϱ ∩
    {z | monomialEval z (h.filter fun k => b k = 0) ≠ 0} with hs₀
  have hmonc : Continuous fun z : Fin n → ℝ => monomialEval z (h.filter fun k => b k = 0) := by
    simp only [monomialEval_eq_prod]
    exact continuous_finsetProd _ fun k _ => (continuous_apply k).pow _
  have hs₀m : MeasurableSet s₀ :=
    measurableSet_closedBall.inter (isOpen_ne_fun hmonc continuous_const).measurableSet
  have hT₀ : TransportsToOn volume volume s₀ Φ fun z => ENNReal.ofReal |(fderiv ℝ ψ z).det| :=
    transportsToOn_of_injOn_of_hasFDerivWithinAt hs₀m
      ((measure_mono inter_subset_left).trans_lt hcube.measure_lt_top).ne hΦc.measurable
      ((measure_mono (image_mono inter_subset_left)).trans_lt
        (hcube.image hΦc).measure_lt_top).ne
      (fun z hz => ((hψdiff z (hcubeW' hz.1)).hasFDerivAt.hasFDerivWithinAt).congr
        (hΦeq.mono inter_subset_left) (hΦeq hz.1))
      ((hc'.injOn.mono fun z hz =>
        (⟨hcubeW' hz.1, hz.2⟩ : z ∈ W' ∧ monomialEval z (h.filter fun k => b k = 0) ≠ 0)).congr
        (hΦeq.mono inter_subset_left).symm)
  set Nz := Metric.closedBall (0 : Fin n → ℝ) ϱ ∩
    {z | monomialEval z (h.filter fun k => b k = 0) = 0} with hNzdef
  have hNz : volume Nz = 0 := by
    refine measure_mono_null (fun z hz => ?_)
      (volume_coordHyperplanes n)
    have hz2 := hz.2
    rw [mem_ofPred_eq, monomialEval_eq_prod, Finset.prod_eq_zero_iff] at hz2
    obtain ⟨i, -, hi⟩ := hz2
    exact ⟨i, (pow_eq_zero_iff'.mp hi).1⟩
  have hNzimg : volume (Φ '' Nz) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      (fun z hz => ((hψdiff z (hcubeW' hz.1)).differentiableWithinAt).congr
        (hΦeq.mono inter_subset_left) (hΦeq hz.1)) hNz
  have hT : TransportsToOn volume volume (Metric.closedBall 0 ϱ) Φ
      fun z => ENNReal.ofReal |(fderiv ℝ ψ z).det| :=
    (hT₀.mono_ae hNz hNzimg).mono_dom fun z hz => by
      by_cases hm : monomialEval z (h.filter fun k => b k = 0) = 0
      · exact Or.inr ⟨hz, hm⟩
      · exact Or.inl ⟨hz, hm⟩
  -- the image of the chart
  have himage : Φ '' Metric.closedBall 0 ϱ = φ '' Metric.closedBall b ϱ := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨b + z, ?_, by rw [hΦeq hz]⟩
      rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
      exact mem_closedBall_zero_iff.mp hz
    · rintro ⟨x, hx, rfl⟩
      have hxz : x - b ∈ Metric.closedBall (0 : Fin n → ℝ) ϱ := by
        rw [mem_closedBall_zero_iff, ← dist_eq_norm]
        exact hx
      refine ⟨x - b, hxz, ?_⟩
      rw [hΦeq hxz]
      simp only [hψ, add_sub_cancel]
  exact ⟨ϱ, hϱ, hcubeW, χ, himage, hT, rfl, fun k => by rw [Fin.cast_eq_self],
    fun k => by rw [Fin.cast_eq_self]⟩

end SingularLearningTheory
