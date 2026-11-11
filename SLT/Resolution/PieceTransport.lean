/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Chart.Family
public import SLT.Resolution.Atlas
public import SLT.MeasureTheory.Measure.Lebesgue.CoordHyperplanes
import all Mathlib.Geometry.Manifold.LocalDiffeomorph  -- exposes `IsLocalDiffeomorphAt` for `obtain`
public import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# The transport identity for the pieces of a chart family

[Hit26, Equation (3.3.5)] for a chart family `F` of an
`SLTResolution` and a smooth partition of unity `ρ` subordinate to it: near the zeros of `K`, the
prior measure `φ dw` on `W` is the sum over the pieces `α` of the pushforwards of
`u^{h_α} ρ(α.point u) c_α(u) du` on `[0, r_α]^d` along the piece maps
(`ChartFamily.lintegral_transport`). The proof changes variables piece by piece through
`π ∘ e.symm`, which is injective off the preimage of the exceptional set and has nonvanishing
Jacobian on an admissible open orthant (`SLTChart.density_eq`); the coordinate hyperplanes of the
charts have null images, the open orthants of one chart have disjoint images, the non-admissible
orthants miss `W`, and the partition of unity sums to one at almost every point of
`W ∩ {K ≤ δ}`: such a point has its preimage in the open cube of a chart over a zero of `K`, off
the hyperplanes, hence in an admissible orthant, hence in the resolved parameter set.

From the identity, `ChartFamily.toResolutionAtlas` packages the pieces as a `ResolutionAtlas`, the
input of the library's free energy, maximum likelihood and singularity type theorems.

| Thesis | Lean |
| --- | --- |
| [Hit26, Equation (3.3.5)], for the pieces of a chart family | |
| | `SLTResolution.ChartFamily.lintegral_transport` |
-/

public section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff ENNReal

namespace SingularLearningTheory

variable {d : ℕ}

/-! ## Coordinate hyperplanes -/

/-- The closed orthant `reflect s '' [0, r]^d` is the open orthant up to the hyperplanes. -/
private theorem reflectOrthant_image_cube_subset {r : ℝ} (s : Fin d → Bool) :
    reflectOrthant s '' cube d r ⊆ openOrthant r s ∪ coordHyperplanes d := by
  rintro _ ⟨u, hu, rfl⟩
  by_cases h0 : ∀ j, u j ≠ 0
  · refine Or.inl (reflectOrthant_mem_openOrthant s fun j ↦ ?_)
    obtain ⟨h1, h2⟩ := mem_cube.1 hu j
    exact ⟨lt_of_le_of_ne h1 (h0 j).symm, h2⟩
  · push Not at h0
    obtain ⟨j, hj⟩ := h0
    exact Or.inr ⟨j, by simp [hj]⟩

private theorem openOrthant_subset_reflectOrthant_image {r : ℝ} (s : Fin d → Bool) :
    openOrthant r s ⊆ reflectOrthant s '' cube d r := fun v hv ↦
  ⟨reflectOrthant s v, reflectOrthant_mem_cube_of_mem_openOrthant s hv,
    reflectOrthant_reflectOrthant s v⟩

private theorem disjoint_openOrthant {r : ℝ} {s s' : Fin d → Bool} (h : s ≠ s') :
    Disjoint (openOrthant r s) (openOrthant r s') := by
  rw [Set.disjoint_left]
  intro v hv hv'
  apply h
  funext j
  have h1 := (hv j).2
  have h2 := (hv' j).2
  cases hs : s j <;> cases hs' : s' j <;> simp_all <;> linarith

private theorem measurableSet_openOrthant {r : ℝ} (s : Fin d → Bool) :
    MeasurableSet (openOrthant r s) := by
  have : openOrthant r s = ⋂ j, ({v : Fin d → ℝ | |v j| ≤ r} ∩
      {v | 0 < (if s j then v j else -v j)}) := by
    ext v
    simp [openOrthant]
  rw [this]
  refine MeasurableSet.iInter fun j ↦ (measurableSet_le ?_ measurable_const).inter
    (measurableSet_lt measurable_const ?_)
  · exact (measurable_pi_apply j).abs
  · by_cases h : s j <;> simp only [h, ite_true, Bool.false_eq_true, ite_false]
    · exact measurable_pi_apply j
    · exact (measurable_pi_apply j).neg

namespace SLTResolution

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : SLTResolution K φ W)

/-! ## The inverse of `π` off the exceptional set -/

/-- A measurable null set containing the exceptional set. -/
@[expose] def nullExceptional : Set (Fin d → ℝ) := toMeasurable volume R.exceptional

theorem subset_nullExceptional : R.exceptional ⊆ R.nullExceptional :=
  subset_toMeasurable _ _

theorem measurableSet_nullExceptional : MeasurableSet R.nullExceptional :=
  measurableSet_toMeasurable _ _

theorem volume_nullExceptional : volume R.nullExceptional = 0 := by
  rw [nullExceptional, measure_toMeasurable, R.volume_exceptional]

/-- Off the exceptional set, a point of `U` has exactly one preimage. -/
theorem eq_of_π_eq {z z' : R.M} (h : R.π z = R.π z') (hz : R.π z ∉ R.exceptional) : z = z' :=
  R.bijOn_off_exceptional.injOn hz (by rwa [mem_preimage, ← h]) h

/-! ## Images of hyperplanes -/

/-- The image under `π ∘ e.symm` of the coordinate hyperplanes in the box `[-r, r]^d` of a chart
is null. -/
theorem volume_image_hyperplanes {z : R.M} (C : R.Chart z) :
    volume ((R.π ∘ C.extension.symm) ''
      (Icc (fun _ ↦ -C.radius) (fun _ ↦ C.radius) ∩ coordHyperplanes d)) = 0 :=
  addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (fun v hv ↦ ((R.analyticOnNhd_comp_symm C v (C.box_subset hv.1)).differentiableAt
      ).differentiableWithinAt)
    (measure_mono_null inter_subset_right (volume_coordHyperplanes d))

variable [Nonempty R.M]

/-- A preimage of `w` under `π`, the unique one off the exceptional set. -/
@[expose] noncomputable def pre (w : Fin d → ℝ) : R.M := Function.invFun R.π w

theorem π_pre {w : Fin d → ℝ} (hw : w ∈ R.U) : R.π (R.pre w) = w :=
  Function.invFun_eq (by rw [← R.range_π] at hw; exact hw)

theorem pre_π {z : R.M} (hz : R.π z ∉ R.exceptional) : R.pre (R.π z) = z :=
  R.eq_of_π_eq (R.π_pre (R.range_π ▸ mem_range_self z)) (by rwa [R.π_pre (R.range_π ▸
    mem_range_self z)])

/-- The preimage is continuous on `U` off the exceptional set: near a point off it, `π` is a
local diffeomorphism, and the preimage is the inverse of that local diffeomorphism. -/
theorem continuousOn_pre : ContinuousOn R.pre (R.U \ R.exceptional) := by
  intro w hw
  set z := R.pre w
  have hzw : R.π z = w := R.π_pre hw.1
  have hz : z ∈ R.π ⁻¹' R.exceptionalᶜ := by simp [hzw, hw.2]
  obtain ⟨Φ, hzΦ, hEq⟩ := R.isLocalDiffeomorphOn_off_exceptional ⟨z, hz⟩
  have hΦw : w ∈ Φ.target := by
    rw [← hzw, hEq hzΦ]
    exact Φ.map_source' hzΦ
  have hcont : ContinuousAt Φ.toOpenPartialHomeomorph.symm w :=
    Φ.toOpenPartialHomeomorph.continuousAt_symm hΦw
  have heq : ∀ w' ∈ Φ.target ∩ (R.U \ R.exceptional), R.pre w' = Φ.invFun w' := by
    intro w' hw'
    have h1 : R.π (Φ.invFun w') = w' := by
      rw [hEq (Φ.map_target' hw'.1)]
      exact Φ.right_inv' hw'.1
    have h2 := R.π_pre hw'.2.1
    exact R.eq_of_π_eq (h2.trans h1.symm) (by rw [h2]; exact hw'.2.2)
  have hev : R.pre =ᶠ[𝓝[R.U \ R.exceptional] w] Φ.invFun := by
    filter_upwards [inter_mem_nhdsWithin _ (Φ.open_target.mem_nhds hΦw)] with w' hw'
    exact heq w' ⟨hw'.2, hw'.1⟩
  refine (ContinuousWithinAt.congr_of_eventuallyEq hcont.continuousWithinAt hev ?_)
  exact heq w ⟨hΦw, hw⟩


/-! ## One chart: the preimage of the exceptional set in an admissible orthant is null -/

omit [Nonempty R.M] in
/-- On an admissible open orthant of a chart, the Jacobian of `π ∘ e.symm` does not vanish: the
pulled-back prior density `c |u^h|` is positive there. -/
theorem det_ne_zero_of_admissible {z : R.M} (C : R.Chart z) {s : Fin d → Bool}
    (hs : C.IsAdmissible s) {v : Fin d → ℝ} (hv : v ∈ openOrthant C.radius s) :
    (fderiv ℝ (R.π ∘ C.extension.symm) v).det ≠ 0 := by
  have hvt := C.openOrthant_subset_target s hv
  have hpos : 0 < C.densityUnit v * |∏ j, v j ^ C.h j| :=
    mul_pos (C.densityUnit_pos v hvt) (abs_pos.mpr (Finset.prod_ne_zero_iff.mpr fun j _ ↦
      pow_ne_zero _ (ne_zero_of_mem_openOrthant hv j)))
  intro h0
  have := C.density_eq v hvt (interior_subset (hs v hv))
  rw [h0, abs_zero, mul_zero] at this
  exact hpos.ne' this.symm

omit [Nonempty R.M] in
/-- On an admissible open orthant, the prior is positive along `π ∘ e.symm` and the density
identity splits as `|det| · φ`. -/
theorem density_eq_of_admissible {z : R.M} (C : R.Chart z) {s : Fin d → Bool}
    (hs : C.IsAdmissible s) {v : Fin d → ℝ} (hv : v ∈ openOrthant C.radius s) :
    0 < φ (R.π (C.extension.symm v)) ∧
      C.densityUnit v * |∏ j, v j ^ C.h j| =
        |(fderiv ℝ (R.π ∘ C.extension.symm) v).det| * φ (R.π (C.extension.symm v)) := by
  have hvt := C.openOrthant_subset_target s hv
  have hpos : 0 < C.densityUnit v * |∏ j, v j ^ C.h j| :=
    mul_pos (C.densityUnit_pos v hvt) (abs_pos.mpr (Finset.prod_ne_zero_iff.mpr fun j _ ↦
      pow_ne_zero _ (ne_zero_of_mem_openOrthant hv j)))
  have heq := C.density_eq v hvt (interior_subset (hs v hv))
  have hdet : 0 < |(fderiv ℝ (R.π ∘ C.extension.symm) v).det| :=
    abs_pos.mpr (R.det_ne_zero_of_admissible C hs hv)
  refine ⟨?_, by rw [← heq, mul_comm]⟩
  by_contra hneg
  push Not at hneg
  have : φ (R.π (C.extension.symm v)) * |(fderiv ℝ (R.π ∘ C.extension.symm) v).det| ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg hdet.le
  rw [heq] at this
  exact this.not_gt hpos

/-- A measurable extension of a function continuous on a measurable set does not change the
preimages inside that set. -/
theorem _root_.measurableSet_inter_preimage_of_continuousOn {f : (Fin d → ℝ) → (Fin d → ℝ)}
    {S T : Set (Fin d → ℝ)} (hS : MeasurableSet S) (hf : ContinuousOn f S)
    (hT : MeasurableSet T) : MeasurableSet (S ∩ f ⁻¹' T) := by
  classical
  have hm : Measurable (S.piecewise f fun _ ↦ 0) :=
    hf.measurable_piecewise continuousOn_const hS
  have : S ∩ f ⁻¹' T = S ∩ (S.piecewise f fun _ ↦ 0) ⁻¹' T := by
    ext v
    simp only [mem_inter_iff, mem_preimage, and_congr_right_iff]
    intro hv
    rw [Set.piecewise_eq_of_mem _ _ _ hv]
  rw [this]
  exact hS.inter (hm hT)

omit [Nonempty R.M] in
/-- On an admissible open orthant, the points that `π ∘ e.symm` sends into the exceptional set
are null. Near each such point `π ∘ e.symm` is injective (inverse function theorem, the Jacobian
is nonzero), so on each of countably many such neighbourhoods `∫ |det|` is at most the measure of
the null image. -/
theorem volume_openOrthant_inter_preimage {z : R.M} (C : R.Chart z) {s : Fin d → Bool}
    (hs : C.IsAdmissible s) :
    volume (openOrthant C.radius s ∩ (R.π ∘ C.extension.symm) ⁻¹' R.nullExceptional) = 0 := by
  set Γ := R.π ∘ C.extension.symm
  set O := openOrthant C.radius s
  set S := O ∩ Γ ⁻¹' R.nullExceptional
  have hOt : O ⊆ C.extension.target := C.openOrthant_subset_target s
  have hΓa : ∀ v ∈ O, AnalyticAt ℝ Γ v := fun v hv ↦ R.analyticOnNhd_comp_symm C v (hOt hv)
  have hSm : MeasurableSet S := measurableSet_inter_preimage_of_continuousOn
    (measurableSet_openOrthant s) (fun v hv ↦ (hΓa v hv).continuousAt.continuousWithinAt)
    R.measurableSet_nullExceptional
  -- a neighbourhood of each point of `O` on which `Γ` is injective
  have hloc : ∀ v : O, ∃ B : Set (Fin d → ℝ), IsOpen B ∧ (v : Fin d → ℝ) ∈ B ∧ InjOn Γ B := by
    rintro ⟨v, hv⟩
    have hdet := R.det_ne_zero_of_admissible C hs hv
    set f' := fderiv ℝ Γ v
    let e : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
      (LinearMap.equivOfDetNeZero (f' : (Fin d → ℝ) →ₗ[ℝ] (Fin d → ℝ)) hdet).toContinuousLinearEquiv
    have he : (e : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) = f' := by ext; rfl
    have hstrict : HasStrictFDerivAt Γ (e : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)) v :=
      he ▸ (hΓa v hv).hasStrictFDerivAt
    exact ⟨(hstrict.toOpenPartialHomeomorph Γ).source,
      (hstrict.toOpenPartialHomeomorph Γ).open_source, hstrict.mem_toOpenPartialHomeomorph_source,
      (hstrict.toOpenPartialHomeomorph Γ).injOn⟩
  choose B hBo hvB hBinj using hloc
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable B hBo
  have hcov : S ⊆ ⋃ v ∈ T, B v := by
    rw [hTU]
    exact fun v hv ↦ mem_iUnion.mpr ⟨⟨v, hv.1⟩, hvB _⟩
  -- `∫_S |det Γ'| = 0`
  have hzero : ∀ v ∈ T, ∫⁻ x in S ∩ B v, ENNReal.ofReal |(fderiv ℝ Γ x).det| = 0 := by
    intro v _
    refine nonpos_iff_eq_zero.mp ?_
    refine (lintegral_abs_det_fderiv_le_addHaar_image volume (hSm.inter (hBo v).measurableSet)
      (fun x hx ↦ (hΓa x hx.1.1).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
      ((hBinj v).mono inter_subset_right)).trans ?_
    refine (measure_mono ?_).trans R.volume_nullExceptional.le
    rintro _ ⟨x, hx, rfl⟩
    exact hx.1.2
  have hT' : Countable T := hTc.to_subtype
  have hint : ∫⁻ x in S, ENNReal.ofReal |(fderiv ℝ Γ x).det| = 0 := by
    have h1 : S = ⋃ v : T, S ∩ B v := by
      ext x
      simp only [mem_iUnion, mem_inter_iff, exists_and_left, iff_self_and]
      intro hx
      obtain ⟨v, hv⟩ := mem_iUnion₂.mp (hcov hx)
      exact ⟨⟨v, hv.1⟩, hv.2⟩
    refine nonpos_iff_eq_zero.mp ?_
    rw [h1]
    refine (lintegral_iUnion_le _ _).trans ?_
    simp [hzero _ (Subtype.prop _)]
  have hmeas : Measurable fun x ↦ ENNReal.ofReal |(fderiv ℝ Γ x).det| :=
    ENNReal.measurable_ofReal.comp ((ContinuousLinearMap.continuous_det.measurable.comp
      (measurable_fderiv ℝ Γ)).abs)
  rw [setLIntegral_eq_zero_iff hSm hmeas] at hint
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hint] with x hx hxS
  have h0 := hx hxS
  rw [ENNReal.ofReal_eq_zero, abs_nonpos_iff] at h0
  exact R.det_ne_zero_of_admissible C hs hxS.1 h0

/-! ## One piece: change of variables -/

namespace ChartFamily

variable {R} (F : R.ChartFamily)

/-- The part of the open orthant of a piece off the preimage of the exceptional set, where
`π ∘ e.symm` is injective. -/
@[expose] def Piece.good {F : R.ChartFamily} (α : F.Piece) : Set (Fin d → ℝ) :=
  openOrthant α.radius α.orthant \
    (R.π ∘ (F.chart α.chart).extension.symm) ⁻¹' R.nullExceptional

omit [Nonempty R.M] in
theorem Piece.measurableSet_good {F : R.ChartFamily} (α : F.Piece) : MeasurableSet α.good := by
  have h := measurableSet_inter_preimage_of_continuousOn (measurableSet_openOrthant α.orthant)
    (fun v hv ↦ (R.analyticOnNhd_comp_symm (F.chart α.chart) v
      ((F.chart α.chart).openOrthant_subset_target _ hv)).continuousAt.continuousWithinAt)
    R.measurableSet_nullExceptional
  have : α.good = openOrthant α.radius α.orthant \
      (openOrthant α.radius α.orthant ∩
        (R.π ∘ (F.chart α.chart).extension.symm) ⁻¹' R.nullExceptional) := by
    ext v
    simp [Piece.good]
  rw [this]
  exact (measurableSet_openOrthant _).diff h

omit [Nonempty R.M] in
theorem Piece.injOn_good {F : R.ChartFamily} (α : F.Piece) :
    InjOn (R.π ∘ (F.chart α.chart).extension.symm) α.good := by
  intro v hv v' hv' h
  have hex : R.π ((F.chart α.chart).extension.symm v) ∉ R.exceptional := fun hm ↦
    hv.2 (R.subset_nullExceptional hm)
  have h1 := R.eq_of_π_eq h hex
  have hvt := (F.chart α.chart).openOrthant_subset_target _ hv.1
  have hv't := (F.chart α.chart).openOrthant_subset_target _ hv'.1
  exact (F.chart α.chart).extension.symm.injOn
    (by rwa [OpenPartialHomeomorph.symm_source]) (by rwa [OpenPartialHomeomorph.symm_source]) h1

omit [Nonempty R.M] in
/-- The closed orthant of a piece agrees with its good part up to a null set. -/
theorem Piece.image_cube_ae_eq_good {F : R.ChartFamily} (α : F.Piece) :
    (reflectOrthant α.orthant '' cube d α.radius : Set (Fin d → ℝ)) =ᵐ[volume] α.good := by
  rw [ae_eq_set]
  constructor
  · refine measure_mono_null (fun v hv ↦ ?_) (measure_union_null (volume_coordHyperplanes d)
      (R.volume_openOrthant_inter_preimage (F.chart α.chart) α.admissible))
    rcases reflectOrthant_image_cube_subset α.orthant hv.1 with h | h
    · refine Or.inr ⟨h, ?_⟩
      by_contra hn
      exact hv.2 ⟨h, hn⟩
    · exact Or.inl h
  · exact measure_mono_null (fun v hv ↦ hv.2 (openOrthant_subset_reflectOrthant_image _ hv.1.1))
      measure_empty

/-- **Change of variables on one piece**: the integral over the cube `[0, r]^d` against
`u^h ρ(point u) c(u) du` of a function of the piece map is the integral against `ρ φ dw` over
the image of the good part of the orthant. -/
theorem lintegral_piece (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (α : F.Piece) (G : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ u in cube d α.radius, G (α.map u) *
        ENNReal.ofReal ((∏ j, u j ^ (α.h j : ℝ)) * (ρ α.chart (α.point u) * α.densityUnit u))
      = ∫⁻ w in (R.π ∘ (F.chart α.chart).extension.symm) '' α.good,
          G w * ENNReal.ofReal (ρ α.chart (R.pre w) * φ w) := by
  set C := F.chart α.chart
  set s := α.orthant
  set Γ := R.π ∘ C.extension.symm
  set F₀ : (Fin d → ℝ) → ℝ≥0∞ := fun v ↦ G (Γ v) *
    ENNReal.ofReal (|∏ j, v j ^ C.h j| * (ρ α.chart (C.extension.symm v) * C.densityUnit v))
  have hcube : MeasurableSet (cube d α.radius) := measurableSet_Icc
  -- reflect the cube onto the closed orthant
  have h1 : ∫⁻ u in cube d α.radius, G (α.map u) *
        ENNReal.ofReal ((∏ j, u j ^ (α.h j : ℝ)) * (ρ α.chart (α.point u) * α.densityUnit u))
      = ∫⁻ u in cube d α.radius, F₀ (reflectOrthant s u) := by
    refine setLIntegral_congr_fun hcube fun u hu ↦ ?_
    simp only [F₀, Piece.map, Piece.point, Piece.densityUnit, Γ, Function.comp_apply]
    congr 3
    rw [abs_prod_reflectOrthant_pow, Finset.abs_prod]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Real.rpow_natCast, abs_pow, abs_of_nonneg (hu.1 j)]
  have hemb : MeasurableEmbedding (reflectOrthant s : (Fin d → ℝ) → _) :=
    (reflectOrthantCLE s).toHomeomorph.measurableEmbedding
  have hpre : reflectOrthant s ⁻¹' (reflectOrthant s '' cube d α.radius) = cube d α.radius :=
    (reflectOrthant_involutive s).injective.preimage_image _
  have h2 : ∫⁻ u in cube d α.radius, F₀ (reflectOrthant s u)
      = ∫⁻ v in reflectOrthant s '' cube d α.radius, F₀ v := by
    have := (measurePreserving_reflectOrthant s).setLIntegral_comp_preimage_emb hemb F₀
      (reflectOrthant s '' cube d α.radius)
    rwa [hpre] at this
  have h3 : ∫⁻ v in reflectOrthant s '' cube d α.radius, F₀ v = ∫⁻ v in α.good, F₀ v :=
    setLIntegral_congr α.image_cube_ae_eq_good
  -- on the good part, the integrand is `|det Γ'| · (g ∘ Γ)`
  set g : (Fin d → ℝ) → ℝ≥0∞ := fun w ↦ G w * ENNReal.ofReal (ρ α.chart (R.pre w) * φ w)
  have h4 : ∫⁻ v in α.good, F₀ v
      = ∫⁻ v in α.good, ENNReal.ofReal |(fderiv ℝ Γ v).det| * g (Γ v) := by
    refine setLIntegral_congr_fun α.measurableSet_good fun v hv ↦ ?_
    have hex : R.π (C.extension.symm v) ∉ R.exceptional := fun hm ↦
      hv.2 (R.subset_nullExceptional hm)
    obtain ⟨hφ, hden⟩ := R.density_eq_of_admissible C α.admissible hv.1
    have hpre' : R.pre (Γ v) = C.extension.symm v := R.pre_π hex
    simp only [F₀, g, hpre']
    have : |∏ j, v j ^ C.h j| * (ρ α.chart (C.extension.symm v) * C.densityUnit v)
        = |(fderiv ℝ Γ v).det| * (ρ α.chart (C.extension.symm v) * φ (Γ v)) := by
      calc _ = ρ α.chart (C.extension.symm v) * (C.densityUnit v * |∏ j, v j ^ C.h j|) := by ring
        _ = _ := by rw [hden]; simp only [Γ, Function.comp_apply]; ring
    rw [this, ENNReal.ofReal_mul (abs_nonneg _)]
    ring
  rw [h1, h2, h3, h4, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume α.measurableSet_good
    (fun v hv ↦ (R.analyticOnNhd_comp_symm C v
      (C.openOrthant_subset_target _ hv.1)).differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    α.injOn_good g]

end ChartFamily

omit [Nonempty R.M] in
/-- A point of `W` in the open cube of a chart whose image is off the images of the coordinate
hyperplanes lies in an admissible open orthant of the chart. -/
theorem exists_admissible_of_mem_openCube {z : R.M} (C : R.Chart z) {y : R.M}
    (hy : y ∈ C.openCube) (hyW : R.π y ∈ W)
    (hH : R.π y ∉ (R.π ∘ C.extension.symm) ''
      (Icc (fun _ ↦ -C.radius) (fun _ ↦ C.radius) ∩ coordHyperplanes d)) :
    ∃ s, C.IsAdmissible s ∧ C.extension y ∈ openOrthant C.radius s := by
  set v := C.extension y
  have hΓ : (R.π ∘ C.extension.symm) v = R.π y := by
    simp [v, C.extension.left_inv hy.1]
  have hbox : ∀ j, |v j| ≤ C.radius := fun j ↦
    abs_le.mpr ⟨(hy.2 j (mem_univ j)).1.le, (hy.2 j (mem_univ j)).2.le⟩
  have h0 : ∀ j, v j ≠ 0 := by
    intro j hj
    exact hH ⟨v, ⟨⟨fun k ↦ (abs_le.mp (hbox k)).1, fun k ↦ (abs_le.mp (hbox k)).2⟩, j, hj⟩, hΓ⟩
  have horth := mem_openOrthant_sign hbox h0
  refine ⟨_, ?_, horth⟩
  rcases C.orthant_dichotomy (fun j ↦ decide (0 < v j)) with h | h
  · exact h
  · exact absurd (by simpa [v, C.extension.left_inv hy.1] using hyW) (h v horth)

namespace ChartFamily

variable {R} {F : R.ChartFamily}

noncomputable instance instFintypePiece : Fintype F.Piece := by
  classical
  exact Fintype.ofInjective (fun α : F.Piece ↦ (α.chart, α.orthant)) fun α β h ↦ by
    cases α; cases β; simp_all

omit [Nonempty R.M] in
theorem Piece.measurableSet_image_good (α : F.Piece) :
    MeasurableSet ((R.π ∘ (F.chart α.chart).extension.symm) '' α.good) :=
  α.measurableSet_good.image_of_continuousOn_injOn
    (fun v hv ↦ (R.analyticOnNhd_comp_symm (F.chart α.chart) v
      ((F.chart α.chart).openOrthant_subset_target _ hv.1)).continuousAt.continuousWithinAt)
    α.injOn_good

omit [Nonempty R.M] in
theorem Piece.image_good_subset (α : F.Piece) :
    (R.π ∘ (F.chart α.chart).extension.symm) '' α.good ⊆ W := by
  rintro _ ⟨v, hv, rfl⟩
  exact interior_subset (α.admissible v hv.1)

omit [Nonempty R.M] in
/-- Two pieces of the same chart have disjoint images. -/
theorem Piece.disjoint_image_good {α β : F.Piece} (hc : α.chart = β.chart) (hne : α ≠ β) :
    Disjoint ((R.π ∘ (F.chart α.chart).extension.symm) '' α.good)
      ((R.π ∘ (F.chart β.chart).extension.symm) '' β.good) := by
  rw [Set.disjoint_left]
  rintro _ ⟨v, hv, rfl⟩ ⟨v', hv', hvv'⟩
  obtain ⟨i, s, hs⟩ := α
  obtain ⟨i', s', hs'⟩ := β
  simp only at hc
  subst hc
  have hss : s ≠ s' := fun h ↦ hne (by subst h; rfl)
  have hex : R.π ((F.chart i).extension.symm v) ∉ R.exceptional := fun hm ↦
    hv.2 (R.subset_nullExceptional hm)
  have h1 := R.eq_of_π_eq hvv'.symm hex
  have hvt := (F.chart i).openOrthant_subset_target _ hv.1
  have hv't := (F.chart i).openOrthant_subset_target _ hv'.1
  have h2 : v = v' := (F.chart i).extension.symm.injOn
    (by rwa [OpenPartialHomeomorph.symm_source]) (by rwa [OpenPartialHomeomorph.symm_source]) h1
  subst h2
  exact Set.disjoint_left.mp (disjoint_openOrthant hss) hv.1 hv'.1

open scoped Classical in
/-- **The pieces of one chart** carry all of the mass of `ρ_i φ` on `W`: off the null images of
the exceptional set and of the coordinate hyperplanes, a point of `W` where `ρ_i ≠ 0` has its
preimage in the open cube of the chart, hence in an admissible open orthant. -/
theorem sum_lintegral_chart (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube) (hWm : MeasurableSet W) (i : F.ι)
    (G : (Fin d → ℝ) → ℝ≥0∞) :
    ∑ α ∈ Finset.univ.filter (fun α : F.Piece ↦ α.chart = i),
        ∫⁻ w in (R.π ∘ (F.chart α.chart).extension.symm) '' α.good,
          G w * ENNReal.ofReal (ρ α.chart (R.pre w) * φ w)
      = ∫⁻ w in W, G w * ENNReal.ofReal (ρ i (R.pre w) * φ w) := by
  classical
  set g : (Fin d → ℝ) → ℝ≥0∞ := fun w ↦ G w * ENNReal.ofReal (ρ i (R.pre w) * φ w)
  set D : F.Piece → Set (Fin d → ℝ) := fun α ↦
    (R.π ∘ (F.chart α.chart).extension.symm) '' α.good
  set T := Finset.univ.filter (fun α : F.Piece ↦ α.chart = i)
  have hsum : ∑ α ∈ T, ∫⁻ w in D α, G w * ENNReal.ofReal (ρ α.chart (R.pre w) * φ w)
      = ∑ α ∈ T, ∫⁻ w in D α, g w :=
    Finset.sum_congr rfl fun α hα ↦ by rw [(Finset.mem_filter.mp hα).2]
  rw [hsum, ← lintegral_biUnion_finset (fun α _ β _ hne ↦ ?disj)
    (fun α _ ↦ α.measurableSet_image_good) g]
  case disj =>
    exact Piece.disjoint_image_good ((Finset.mem_filter.mp ‹α ∈ T›).2.trans
      (Finset.mem_filter.mp ‹β ∈ T›).2.symm) hne
  set D' := ⋃ α ∈ T, D α
  have hD'm : MeasurableSet D' := Finset.measurableSet_biUnion _ fun α _ ↦
    α.measurableSet_image_good
  have hD'W : D' ⊆ W := iUnion₂_subset fun α _ ↦ α.image_good_subset
  rw [← union_sdiff_cancel hD'W, lintegral_union (hWm.diff hD'm) disjoint_sdiff_right]
  -- `g` vanishes almost everywhere on `W \ D'`
  set H := (R.π ∘ (F.chart i).extension.symm) ''
    (Icc (fun _ ↦ -(F.chart i).radius) (fun _ ↦ (F.chart i).radius) ∩ coordHyperplanes d)
  have hnull : volume (R.nullExceptional ∪ H) = 0 :=
    measure_union_null R.volume_nullExceptional (R.volume_image_hyperplanes (F.chart i))
  have hzero : ∫⁻ w in W \ D', g w = 0 := by
    rw [setLIntegral_congr_fun_ae (hWm.diff hD'm) (g := fun _ ↦ 0) ?_, lintegral_zero]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with w hwN hw
    by_contra hg
    have hρ0 : ρ i (R.pre w) ≠ 0 := fun h0 ↦ hg (by simp [g, h0])
    have hz : R.pre w ∈ (F.chart i).openCube := hρ i (subset_tsupport _ hρ0)
    have hπ : R.π (R.pre w) = w := R.π_pre (R.W_subset_U hw.1)
    obtain ⟨s, hs, hv⟩ := R.exists_admissible_of_mem_openCube (F.chart i) hz
      (by rw [hπ]; exact hw.1) (fun h ↦ hwN (Or.inr (by rwa [hπ] at h)))
    apply hw.2
    refine mem_iUnion₂.mpr ⟨⟨i, s, hs⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩, ?_⟩
    refine ⟨(F.chart i).extension (R.pre w), ⟨hv, fun hN ↦ hwN (Or.inl ?_)⟩, ?_⟩
    · simpa [(F.chart i).extension.left_inv hz.1, hπ] using hN
    · simp [(F.chart i).extension.left_inv hz.1, hπ]
  rw [hzero, add_zero]

end ChartFamily

/-- A continuous function of the preimage is almost everywhere measurable on `W`: off the null
exceptional set the preimage is continuous. -/
theorem aemeasurable_comp_pre {f : R.M → ℝ} (hf : Continuous f) (hWm : MeasurableSet W) :
    AEMeasurable (fun w ↦ f (R.pre w)) (volume.restrict W) := by
  classical
  set S := R.U \ R.nullExceptional
  have hSm : MeasurableSet S := R.isOpen_U.measurableSet.diff R.measurableSet_nullExceptional
  have hc : ContinuousOn (fun w ↦ f (R.pre w)) S :=
    hf.comp_continuousOn
      (R.continuousOn_pre.mono (sdiff_subset_sdiff_right R.subset_nullExceptional))
  refine ⟨S.piecewise (fun w ↦ f (R.pre w)) 0, hc.measurable_piecewise continuousOn_const hSm, ?_⟩
  rw [Filter.EventuallyEq, ae_restrict_iff' hWm]
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp R.volume_nullExceptional] with w hwN hwW
  have hwS : w ∈ S := ⟨R.W_subset_U hwW, hwN⟩
  rw [Set.piecewise_eq_of_mem _ _ _ hwS]

namespace ChartFamily

variable {R} {F : R.ChartFamily}

/-- **The transport identity for the pieces**, in integral form: the sum over the pieces of the
integrals over `[0, r]^d` against `u^h ρ(point u) c(u) du` of a function of the piece map is the
integral over `W` against `(Σ_i ρ_i ∘ π⁻¹) φ dw`. -/
theorem sum_lintegral_pieces (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube) (hWm : MeasurableSet W)
    (hφm : AEMeasurable φ (volume.restrict W)) (G : (Fin d → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∑ α : F.Piece, ∫⁻ u in cube d α.radius, G (α.map u) *
        ENNReal.ofReal ((∏ j, u j ^ (α.h j : ℝ)) * (ρ α.chart (α.point u) * α.densityUnit u))
      = ∫⁻ w in W, G w * ENNReal.ofReal ((∑ i, ρ i (R.pre w)) * φ w) := by
  classical
  simp_rw [lintegral_piece F ρ]
  rw [← Finset.sum_fiberwise Finset.univ (fun α : F.Piece ↦ α.chart)]
  have h1 : ∀ i : F.ι, ∑ α ∈ Finset.univ.filter (fun α : F.Piece ↦ α.chart = i),
      ∫⁻ w in (R.π ∘ (F.chart α.chart).extension.symm) '' α.good,
        G w * ENNReal.ofReal (ρ α.chart (R.pre w) * φ w)
      = ∫⁻ w in W, G w * ENNReal.ofReal (ρ i (R.pre w) * φ w) := fun i ↦ by
    convert sum_lintegral_chart ρ hρ hWm i G
  simp_rw [h1]
  have hm : ∀ i ∈ Finset.univ, AEMeasurable
      (fun w ↦ G w * ENNReal.ofReal (ρ i (R.pre w) * φ w)) (volume.restrict W) := fun i _ ↦
    hG.aemeasurable.mul (ENNReal.measurable_ofReal.comp_aemeasurable
      ((R.aemeasurable_comp_pre (ρ i).2.continuous hWm).mul hφm))
  rw [← lintegral_finsetSum' _ hm]
  refine lintegral_congr fun w ↦ ?_
  rw [← Finset.mul_sum]
  congr 1
  rcases le_or_gt 0 (φ w) with hφ | hφ
  · rw [← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ mul_nonneg (ρ.nonneg i _) hφ, Finset.sum_mul]
  · rw [ENNReal.ofReal_of_nonpos (mul_nonpos_of_nonneg_of_nonpos
      (Finset.sum_nonneg fun i _ ↦ ρ.nonneg i _) hφ.le)]
    exact Finset.sum_eq_zero fun i _ ↦ ENNReal.ofReal_of_nonpos
      (mul_nonpos_of_nonneg_of_nonpos (ρ.nonneg i _) hφ.le)

/-- **Almost every point of `W` near the zeros lies under the sublevel of `F`**: for a small `δ`,
almost every point of `W ∩ {K ≤ δ}` has its preimage in the open cube of a chart over a zero of
`K`, off its coordinate hyperplanes, hence in an admissible open orthant, hence in the resolved
parameter set and the sublevel of `F`. -/
theorem exists_ae_mem_sublevel (hW : IsCompact W) (hKc : ContinuousOn K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) :
    ∃ δ > 0, δ ≤ F.δ ∧ ∀ᵐ w, w ∈ W → K w ≤ δ → R.pre w ∈ F.sublevel := by
  obtain ⟨ι, _, centre, chart, δ₀, hδ₀, hcov⟩ := R.exists_finite_cover_sublevel hW hKc hK
  refine ⟨min δ₀ F.δ, lt_min hδ₀ F.δ_pos, min_le_right _ _, ?_⟩
  set H : Set (Fin d → ℝ) := ⋃ j, (R.π ∘ (chart j).extension.symm) ''
    (Icc (fun _ ↦ -(chart j).radius) (fun _ ↦ (chart j).radius) ∩ coordHyperplanes d)
  have hnull : volume (R.nullExceptional ∪ H) = 0 :=
    measure_union_null R.volume_nullExceptional
      (measure_iUnion_null fun j ↦ R.volume_image_hyperplanes (chart j))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with w hwN hwW hwK
  have hπ : R.π (R.pre w) = w := R.π_pre (R.W_subset_U hwW)
  obtain ⟨j, hj⟩ := hcov (R.pre w) (by rw [hπ]; exact hwW)
    (by rw [hπ]; exact hwK.trans (min_le_left _ _))
  obtain ⟨s, hs, hv⟩ := R.exists_admissible_of_mem_openCube (chart j) hj
    (by rw [hπ]; exact hwW) (fun h ↦ hwN (Or.inr (mem_iUnion.mpr ⟨j, by rwa [hπ] at h⟩)))
  have hint : R.π (R.pre w) ∈ interior W := by
    have := hs _ hv
    rwa [(chart j).extension.left_inv hj.1] at this
  exact ⟨subset_closure hint, by
    show K (R.π (R.pre w)) ≤ F.δ
    rw [hπ]
    exact hwK.trans (min_le_right _ _)⟩

/-- **The partition of unity sums to one almost everywhere near the zeros** of `K` in `W`. -/
theorem exists_ae_sum_eq_one (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) :
    ∃ δ > 0, δ ≤ F.δ ∧ ∀ᵐ w, w ∈ W → K w ≤ δ → ∑ i, ρ i (R.pre w) = 1 := by
  obtain ⟨δ, hδ, hδF, hae⟩ := exists_ae_mem_sublevel (F := F) hW hKc hK
  refine ⟨δ, hδ, hδF, ?_⟩
  filter_upwards [hae] with w hw hwW hwK
  have := ρ.sum_eq_one (hw hwW hwK)
  rwa [finsum_eq_sum_of_fintype] at this

end ChartFamily


namespace ChartFamily

variable {R} {F : R.ChartFamily}

open scoped Classical in
/-- The localization of an atlas built from a partition of unity: `1` on `W ∩ {K ≤ δ}`, and the
sum of the partition of unity at the preimage off the exceptional set elsewhere. -/
@[expose] noncomputable def localization (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M
    F.sublevel)
    (δ : ℝ) (w : Fin d → ℝ) : ℝ :=
  if w ∈ W ∧ K w ≤ δ then 1
  else (R.U \ R.nullExceptional).piecewise (fun w ↦ ∑ i, ρ i (R.pre w)) 0 w

theorem localization_nonneg (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (δ : ℝ) (w : Fin d → ℝ) : 0 ≤ localization ρ δ w := by
  classical
  unfold localization
  split_ifs
  · exact zero_le_one
  · by_cases hw : w ∈ R.U \ R.nullExceptional
    · rw [Set.piecewise_eq_of_mem _ _ _ hw]
      exact Finset.sum_nonneg fun i _ ↦ ρ.nonneg i _
    · rw [Set.piecewise_eq_of_notMem _ _ _ hw]
      rfl

theorem localization_le_one (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (δ : ℝ) (w : Fin d → ℝ) : localization ρ δ w ≤ 1 := by
  classical
  unfold localization
  split_ifs
  · exact le_rfl
  · by_cases hw : w ∈ R.U \ R.nullExceptional
    · rw [Set.piecewise_eq_of_mem _ _ _ hw]
      have := ρ.sum_le_one (R.pre w)
      rwa [finsum_eq_sum_of_fintype] at this
    · rw [Set.piecewise_eq_of_notMem _ _ _ hw]
      exact zero_le_one

theorem localization_eq_one (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    {δ : ℝ} {w : Fin d → ℝ} (hw : w ∈ W) (hK : K w ≤ δ) : localization ρ δ w = 1 := by
  classical
  simp [localization, hw, hK]

theorem measurable_localization (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hW : IsClosed W) (hKc : ContinuousOn K W) (δ : ℝ) :
    Measurable (localization ρ δ) := by
  classical
  have hS : MeasurableSet {w | w ∈ W ∧ K w ≤ δ} :=
    (hKc.preimage_isClosed_of_isClosed hW isClosed_Iic).measurableSet
  have hc : ContinuousOn (fun w ↦ ∑ i, ρ i (R.pre w)) (R.U \ R.nullExceptional) :=
    continuousOn_finsetSum _ fun i _ ↦ (ρ i).2.continuous.comp_continuousOn
      (R.continuousOn_pre.mono (sdiff_subset_sdiff_right R.subset_nullExceptional))
  have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℝ)))
    (R.isOpen_U.measurableSet.diff R.measurableSet_nullExceptional)
  exact Measurable.ite hS measurable_const hm

/-- The threshold below which the partition of unity sums to one almost everywhere on `W`. -/
noncomputable def atlasδ (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) : ℝ :=
  (exists_ae_sum_eq_one ρ hW hKc hK).choose

/-- The specification of `atlasδ`: it is positive and at most `F.δ`, and below it the partition of
unity sums to one almost everywhere on `W`. -/
theorem atlasδ_spec (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) :
    0 < atlasδ ρ hW hKc hK ∧ atlasδ ρ hW hKc hK ≤ F.δ ∧
      ∀ᵐ w, w ∈ W → K w ≤ atlasδ ρ hW hKc hK → ∑ i, ρ i (R.pre w) = 1 :=
  (exists_ae_sum_eq_one ρ hW hKc hK).choose_spec

/-- **The atlas of the pieces** of a chart family with a subordinate partition of unity: chart
maps the piece maps, exponents `k`, `h` of the charts, weights `ρ(point u) c(u)`, and the
transport identity `sum_lintegral_pieces`. -/
@[expose] noncomputable def toResolutionAtlas
    (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube) (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) (hφc : ContinuousOn φ W)
    [Nonempty F.Piece] : ResolutionAtlas K φ W where
  ι := F.Piece
  b α := α.radius
  b_pos α := (F.chart α.chart).radius_pos
  k α := α.k
  h α := α.h
  active α := (F.chart α.chart).active
  g α := α.extMap
  g_analytic α := α.analyticOnNhd_extMap
  g_measurable α := α.measurable_extMap
  g_mapsTo α u hu := by
    rw [α.extMap_eq (α.cube_subset_domain hu)]
    exact α.map_mem hW.isClosed hu
  monomial α u hu := by
    rw [α.extMap_eq (α.cube_subset_domain hu)]
    exact α.loss_map hu
  weight α u := ρ α.chart (α.point u) * α.densityUnit u
  weight_nonneg α u hu := mul_nonneg (ρ.nonneg _ _)
    ((F.chart α.chart).densityUnit_pos _ (α.cube_subset_domain hu)).le
  weight_contDiffOn α := α.contDiffOn_weight ρ
  χ := localization ρ (atlasδ ρ hW hKc hK)
  χ_measurable := measurable_localization ρ hW.isClosed hKc _
  χ_nonneg := localization_nonneg ρ _
  χ_le_one := localization_le_one ρ _
  δ := atlasδ ρ hW hKc hK
  δ_pos := (atlasδ_spec ρ hW hKc hK).1
  χ_eq_one w hw hK' := localization_eq_one ρ hw hK'.le
  transport := by
    classical
    have hWm : MeasurableSet W := hW.isClosed.measurableSet
    have hφm : AEMeasurable φ (volume.restrict W) := hφc.aemeasurable hWm
    obtain ⟨-, -, hae⟩ := atlasδ_spec ρ hW hKc hK
    ext A hA
    set G : (Fin d → ℝ) → ℝ≥0∞ := A.indicator 1
    have hG : Measurable G := measurable_const.indicator hA
    rw [withDensity_apply _ hA, Measure.finsetSum_apply]
    have hind : ∀ (μ : Measure (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ≥0∞),
        ∫⁻ x in A, f x ∂μ = ∫⁻ x, G x * f x ∂μ := fun μ f ↦ by
      rw [← lintegral_indicator hA]
      refine lintegral_congr fun x ↦ ?_
      by_cases hx : x ∈ A <;> simp [G, hx]
    rw [hind]
    have hpiece : ∀ α : F.Piece, (Measure.map α.extMap
        ((volume.restrict (cube d α.radius)).withDensity fun u ↦ ENNReal.ofReal
          ((∏ j, u j ^ (α.h j : ℝ)) * (ρ α.chart (α.point u) * α.densityUnit u)))) A
        = ∫⁻ u in cube d α.radius, G (α.map u) * ENNReal.ofReal
          ((∏ j, u j ^ (α.h j : ℝ)) * (ρ α.chart (α.point u) * α.densityUnit u)) := by
      intro α
      rw [Measure.map_apply α.measurable_extMap hA, withDensity_apply _ (α.measurable_extMap hA),
        ← lintegral_indicator (α.measurable_extMap hA)]
      refine setLIntegral_congr_fun measurableSet_Icc
        fun u hu ↦ ?_
      have hgu := α.extMap_eq (α.cube_subset_domain hu)
      by_cases hA' : α.map u ∈ A
      · rw [Set.indicator_of_mem (show u ∈ α.extMap ⁻¹' A by rw [mem_preimage, hgu]; exact hA')]
        simp [G, hA']
      · rw [Set.indicator_of_notMem (show u ∉ α.extMap ⁻¹' A by rw [mem_preimage, hgu]; exact hA')]
        simp [G, hA']
    simp_rw [hpiece]
    rw [sum_lintegral_pieces ρ hρ hWm hφm G hG]
    refine (setLIntegral_congr_fun_ae hWm ?_).symm
    filter_upwards [hae, measure_eq_zero_iff_ae_notMem.mp R.volume_nullExceptional]
      with w hw1 hwN hwW
    congr 2
    by_cases hKw : K w ≤ atlasδ ρ hW hKc hK
    · rw [localization_eq_one ρ hwW hKw, hw1 hwW hKw]
    · simp only [localization, hwW, hKw, and_false, ite_false]
      rw [Set.piecewise_eq_of_mem _ _ _ (show w ∈ R.U \ R.nullExceptional from
        ⟨R.W_subset_U hwW, hwN⟩)]

end ChartFamily

end SLTResolution

end SingularLearningTheory
