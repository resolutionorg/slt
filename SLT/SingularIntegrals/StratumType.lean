/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.LocalType
public import SLT.SingularIntegrals.TypeOfAtlas
import SLT.SingularIntegrals.PositiveCube
import SLT.VolumeScaling.Transport
import SLT.VolumeScaling.Invariance
import SLT.VolumeScaling.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Stratum types of a resolution atlas, and the local type from an atlas

The chart cube `[0, b_α]^d` of a resolution atlas is stratified by which coordinates vanish. At a
point `P` of the cube the monomial `u^{2k_α}` against `u^{h_α}` has, on a small box around `P`,
the sublevel-volume exponents of the *stratum type* `σ_α(P) = (λ_P, m_P)`, computed over the
active coordinates vanishing at `P` (`stratumRlct`, `stratumMult`; the chart type is the stratum
type of the origin). This module proves the two box estimates — every box is `O` of its stratum
scale (`chartMeasure_box_isBigO`), a box around a point with positive weight is `Ω` of it
(`llcScale_stratum_isBigO_box`) — the compact covering bound `chartMeasure_isBigO_of_forall`, and
from them the **local type from an atlas** (`hasLocalSingularityType_of_atlas`): if the chart
maps are continuous, `(λ, m)` is at least as singular as the stratum type of every point of the
fibre of the atlas over `x`, and some fibre point realises `(λ, m)` with positive weight, then
`(λ, m)` is the local singularity type at `x`.

No thesis counterpart for the stratum types; the local type is [Hit26,
Definition 6.2.1] by volume scaling (`LocalType.lean`).
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology Asymptotics SingularLearningTheory Metric
open scoped ENNReal

variable {d : ℕ}

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-! ## Face types -/

/-- The type `(λ_J, m_J)` of a set `J` of coordinates: the least ratio `(h_j + 1)/(2k_j)` over
`J` (`0` for `J = ∅`). -/
@[expose] noncomputable def faceRlct (α : R.ι) (J : Finset (Fin d)) : ℝ :=
  if h : J.Nonempty then J.inf' h (R.ratio α) else 0

/-- The multiplicity of a set `J` of coordinates: the number of `j ∈ J` attaining `λ_J`. -/
@[expose] noncomputable def faceMult (α : R.ι) (J : Finset (Fin d)) : ℕ :=
  (J.filter fun j ↦ R.ratio α j = R.faceRlct α J).card

/-- The stratum of a point `P` of the cube: the active coordinates vanishing at `P`. -/
@[expose] noncomputable def stratum (α : R.ι) (P : Fin d → ℝ) : Finset (Fin d) :=
  (R.activeSet α).filter fun j ↦ P j = 0

/-- The stratum type `λ_P` of a point of the cube. -/
@[expose] noncomputable def stratumRlct (α : R.ι) (P : Fin d → ℝ) : ℝ := R.faceRlct α
    (R.stratum α P)

/-- The stratum type `m_P` of a point of the cube. -/
@[expose] noncomputable def stratumMult (α : R.ι) (P : Fin d → ℝ) : ℕ := R.faceMult α
    (R.stratum α P)

theorem faceRlct_of_nonempty (α : R.ι) {J : Finset (Fin d)} (hJ : J.Nonempty) :
    R.faceRlct α J = J.inf' hJ (R.ratio α) := by
  rw [faceRlct, dite_eq_left hJ]

theorem faceRlct_activeSet (α : R.ι) : R.faceRlct α (R.activeSet α) = R.chartRlct α :=
  R.faceRlct_of_nonempty α (activeSet_nonempty R α)

theorem faceMult_activeSet (α : R.ι) : R.faceMult α (R.activeSet α) = R.chartMult α := by
  rw [faceMult, faceRlct_activeSet, chartMult_eq_card, primary_eq_filter]

/-- The chart type is the stratum type of the origin. -/
theorem stratum_zero (α : R.ι) : R.stratum α 0 = R.activeSet α := by
  ext j
  simp [stratum]

theorem faceRlct_le (α : R.ι) {J : Finset (Fin d)} {j : Fin d} (hj : j ∈ J) :
    R.faceRlct α J ≤ R.ratio α j := by
  rw [R.faceRlct_of_nonempty α ⟨j, hj⟩]
  exact Finset.inf'_le _ hj

theorem exists_ratio_eq_faceRlct (α : R.ι) {J : Finset (Fin d)} (hJ : J.Nonempty) :
    ∃ j ∈ J, R.ratio α j = R.faceRlct α J := by
  rw [R.faceRlct_of_nonempty α hJ]
  obtain ⟨j, hj, h⟩ := Finset.exists_mem_eq_inf' hJ (R.ratio α)
  exact ⟨j, hj, h.symm⟩

theorem faceRlct_pos (α : R.ι) {J : Finset (Fin d)} (hJ : J.Nonempty) (hJa : J ⊆ R.activeSet α) :
    0 < R.faceRlct α J := by
  obtain ⟨j, hj, h⟩ := R.exists_ratio_eq_faceRlct α hJ
  rw [← h, ratio]
  have hk : 0 < R.k α j := by simpa [activeSet] using hJa hj
  positivity

/-- A larger face is at least as singular: `J ⊆ J'` gives `(λ_{J'}, m_{J'})` at least as
singular as `(λ_J, m_J)`. -/
theorem moreSingular_faceType_of_subset (α : R.ι) {J J' : Finset (Fin d)} (hJ : J.Nonempty)
    (hJJ : J ⊆ J') :
    MoreSingular (R.faceRlct α J') (R.faceMult α J') (R.faceRlct α J) (R.faceMult α J) := by
  have hJ' : J'.Nonempty := hJ.mono hJJ
  have hle : R.faceRlct α J' ≤ R.faceRlct α J := by
    obtain ⟨j, hj, h⟩ := R.exists_ratio_eq_faceRlct α hJ
    rw [← h]
    exact R.faceRlct_le α (hJJ hj)
  rcases eq_or_lt_of_le hle with heq | hlt
  · refine Or.inr ⟨heq, ?_⟩
    rw [faceMult, faceMult, heq]
    exact Finset.card_le_card (Finset.filter_subset_filter _ hJJ)
  · exact Or.inl hlt

/-! ## The restricted exponents and the box -/

/-- The exponents `k_α` restricted to the coordinates in `Z` (`0` elsewhere). -/
@[expose] noncomputable def faceK (α : R.ι) (Z : Finset (Fin d)) (j : Fin d) : ℕ :=
  if j ∈ Z then R.k α j else 0

/-- The exponents `h_α` restricted to the coordinates in `Z` (`0` elsewhere). -/
@[expose] noncomputable def faceH (α : R.ι) (Z : Finset (Fin d)) (j : Fin d) : ℕ :=
  if j ∈ Z then R.h α j else 0

/-- The part `∏_{j ∈ Z} u_j^{2k_j}` of the chart monomial. -/
@[expose] noncomputable def faceMonomial (α : R.ι) (Z : Finset (Fin d)) (u : Fin d → ℝ) : ℝ :=
  ∏ j, u j ^ (2 * R.faceK α Z j)

/-- The part `∏_{j ∈ Z} u_j^{h_j}` of the monomial weight. -/
@[expose] noncomputable def faceDensity (α : R.ι) (Z : Finset (Fin d)) (u : Fin d → ℝ) : ℝ :=
  ∏ j, u j ^ (R.faceH α Z j : ℝ)

/-- The measure `∏_{j ∈ Z} u_j^{h_j} du`. -/
@[expose] noncomputable def faceMeasure (α : R.ι) (Z : Finset (Fin d)) : Measure (Fin d → ℝ) :=
  volume.withDensity fun u ↦ ENNReal.ofReal (R.faceDensity α Z u)

theorem faceMonomial_eq (α : R.ι) (Z : Finset (Fin d)) (u : Fin d → ℝ) :
    R.faceMonomial α Z u = ∏ j ∈ Z, u j ^ (2 * R.k α j) := by
  rw [faceMonomial, ← Finset.prod_mul_prod_compl Z]
  have h1 : ∏ j ∈ Z, u j ^ (2 * R.faceK α Z j) = ∏ j ∈ Z, u j ^ (2 * R.k α j) :=
    Finset.prod_congr rfl fun j hj ↦ by simp [faceK, hj]
  have h2 : ∏ j ∈ Zᶜ, u j ^ (2 * R.faceK α Z j) = 1 :=
    Finset.prod_eq_one fun j hj ↦ by simp [faceK, Finset.mem_compl.mp hj]
  rw [h1, h2, mul_one]

theorem faceDensity_eq (α : R.ι) (Z : Finset (Fin d)) (u : Fin d → ℝ) :
    R.faceDensity α Z u = ∏ j ∈ Z, u j ^ (R.h α j : ℝ) := by
  rw [faceDensity, ← Finset.prod_mul_prod_compl Z]
  have h1 : ∏ j ∈ Z, u j ^ (R.faceH α Z j : ℝ) = ∏ j ∈ Z, u j ^ (R.h α j : ℝ) :=
    Finset.prod_congr rfl fun j hj ↦ by simp [faceH, hj]
  have h2 : ∏ j ∈ Zᶜ, u j ^ (R.faceH α Z j : ℝ) = 1 :=
    Finset.prod_eq_one fun j hj ↦ by simp [faceH, Finset.mem_compl.mp hj]
  rw [h1, h2, mul_one]

theorem measurable_faceMonomial (α : R.ι) (Z : Finset (Fin d)) : Measurable (R.faceMonomial α Z) :=
  Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _

theorem continuous_cubeMonomial (α : R.ι) : Continuous (R.cubeMonomial α) :=
  continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _

/-- The restricted monomial against the restricted density on `[0, η]^d` has the type of
`Z ∩ active` (the coordinates of `Z` on which the monomial depends). -/
theorem hasLLCExponentsOn_faceMonomial (α : R.ι) (Z : Finset (Fin d))
    (hJ : (Z ∩ R.activeSet α).Nonempty) {η : ℝ} (hη : 0 < η) :
    HasLLCExponentsOn (R.faceMeasure α Z) (cube d η) (R.faceMonomial α Z)
      (R.faceRlct α (Z ∩ R.activeSet α)) (R.faceMult α (Z ∩ R.activeSet α)) := by
  have hpos : ∀ j, 0 < R.faceK α Z j ↔ j ∈ Z ∩ R.activeSet α := fun j ↦ by
    by_cases hj : j ∈ Z
    · simp [faceK, hj, activeSet]
    · simp [faceK, hj]
  have hratio : ∀ j ∈ Z, ((R.faceH α Z j : ℝ) + 1) / (2 * R.faceK α Z j) = R.ratio α j :=
    fun j hj ↦ by simp [faceK, faceH, hj, ratio]
  have hfilter : (Finset.univ.filter fun j ↦ 0 < R.faceK α Z j ∧
      ((R.faceH α Z j : ℝ) + 1) / (2 * R.faceK α Z j) = R.faceRlct α (Z ∩ R.activeSet α))
      = (Z ∩ R.activeSet α).filter fun j ↦ R.ratio α j = R.faceRlct α (Z ∩ R.activeSet α) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hpos]
    constructor
    · rintro ⟨hj, h⟩
      exact ⟨hj, by rw [← hratio j (Finset.mem_inter.mp hj).1]; exact h⟩
    · rintro ⟨hj, h⟩
      exact ⟨hj, by rw [hratio j (Finset.mem_inter.mp hj).1]; exact h⟩
  have hmin : ∀ j, 0 < R.faceK α Z j →
      R.faceRlct α (Z ∩ R.activeSet α) ≤ ((R.faceH α Z j : ℝ) + 1) / (2 * R.faceK α Z j) := by
    intro j hj
    rw [hpos] at hj
    rw [hratio j (Finset.mem_inter.mp hj).1]
    exact R.faceRlct_le α hj
  have hatt : ∃ j, 0 < R.faceK α Z j ∧
      ((R.faceH α Z j : ℝ) + 1) / (2 * R.faceK α Z j) = R.faceRlct α (Z ∩ R.activeSet α) := by
    obtain ⟨j, hj, h⟩ := R.exists_ratio_eq_faceRlct α hJ
    exact ⟨j, (hpos j).mpr hj, by rw [hratio j (Finset.mem_inter.mp hj).1]; exact h⟩
  have h := hasLLCExponentsOn_monomial_cube (R.faceK α Z) (R.faceH α Z)
    (R.faceRlct_pos α hJ Finset.inter_subset_right) hmin hatt hη
  rw [hfilter] at h
  exact h

/-- The shift placing the box around `P`: `0` on the coordinates vanishing at `P`, `P_j − η`
on the others. -/
@[expose] noncomputable def _root_.faceShift (P : Fin d → ℝ) (η : ℝ) (j : Fin d) : ℝ :=
  if P j = 0 then 0 else P j - η

/-- The box `∏_j [t_j, t_j + η]` around `P` with the shift `t = faceShift P η`. -/
@[expose] def _root_.faceBox (P : Fin d → ℝ) (η : ℝ) : Set (Fin d → ℝ) :=
  pi univ fun j ↦ Icc (faceShift P η j) (faceShift P η j + η)

/-- The set of coordinates vanishing at `P`. -/
@[expose] noncomputable def _root_.zeroCoords (P : Fin d → ℝ) : Finset
    (Fin d) := Finset.univ.filter fun j ↦ P j = 0

theorem _root_.measurableSet_faceBox (P : Fin d → ℝ) (η : ℝ) : MeasurableSet (faceBox P η) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc

theorem _root_.faceShift_of_zero {P : Fin d → ℝ} {η : ℝ} {j : Fin d} (h : P j = 0) :
    faceShift P η j = 0 := by simp [faceShift, h]

theorem _root_.faceShift_of_ne_zero {P : Fin d → ℝ} {η : ℝ} {j : Fin d} (h : P j ≠ 0) :
    faceShift P η j = P j - η := by simp [faceShift, h]

/-- Translating the box `∏_j [t_j, t_j + η]` back to `[0, η]^d`: the restricted monomial and
density do not see a translation of the coordinates outside `Z`. -/
theorem sublevelVol_faceMeasure_box (α : R.ι) (Z : Finset (Fin d)) {t : Fin d → ℝ}
    (htZ : ∀ j ∈ Z, t j = 0) (η ε : ℝ) :
    sublevelVol (R.faceMeasure α Z) (pi univ fun j ↦ Icc (t j) (t j + η)) (R.faceMonomial α Z) ε
      = sublevelVol (R.faceMeasure α Z) (cube d η) (R.faceMonomial α Z) ε := by
  have hBox : MeasurableSet (pi univ fun j ↦ Icc (t j) (t j + η)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hT := sublevelVol_withDensity_comp_measurePreserving (MeasurableEquiv.addRight t)
    (measurePreserving_add_right volume t)
    (w := fun u ↦ ENNReal.ofReal (R.faceDensity α Z u)) hBox (R.measurable_faceMonomial α Z) ε
  have h1 : ∀ x : Fin d → ℝ, R.faceDensity α Z (x + t) = R.faceDensity α Z x := fun x ↦
    Finset.prod_congr rfl fun j _ ↦ by
      by_cases hj : j ∈ Z
      · simp [htZ j hj]
      · simp [faceH, hj]
  have h2 : ∀ x : Fin d → ℝ, R.faceMonomial α Z (x + t) = R.faceMonomial α Z x := fun x ↦
    Finset.prod_congr rfl fun j _ ↦ by
      by_cases hj : j ∈ Z
      · simp [htZ j hj]
      · simp [faceK, hj]
  have h3 : (MeasurableEquiv.addRight t) ⁻¹' (pi univ fun j ↦ Icc (t j) (t j + η)) = cube d η := by
    ext u
    rw [mem_cube]
    simp only [mem_preimage, MeasurableEquiv.coe_addRight, mem_univ_pi, Pi.add_apply, mem_Icc]
    constructor <;> intro H j <;> have := H j <;> constructor <;> linarith
  rw [faceMeasure, ← hT, h3]
  simp only [MeasurableEquiv.coe_addRight, h1, h2]

/-! ## The box estimates -/

section Box

variable (α : R.ι) {P : Fin d → ℝ} (hP : P ∈ cube d (R.b α)) {η : ℝ} (hη : 0 < η)
  (hηP : ∀ j, P j ≠ 0 → η < P j) (hηb : η ≤ R.b α)

include hP hηP hηb in
theorem faceBox_subset_cube : faceBox P η ⊆ cube d (R.b α) := by
  intro u hu
  refine mem_cube.2 fun j ↦ ?_
  have h := hu j (mem_univ j)
  rw [mem_Icc] at h
  by_cases hj : P j = 0
  · rw [faceShift_of_zero hj] at h
    exact ⟨h.1, h.2.trans (by linarith)⟩
  · rw [faceShift_of_ne_zero hj] at h
    have := (mem_cube.1 hP j).2
    have := hηP j hj
    constructor <;> linarith

theorem _root_.faceShift_zeroCoords (P : Fin d → ℝ)
    (η : ℝ) : ∀ j ∈ zeroCoords P, faceShift P η j = 0 :=
  fun j hj ↦ faceShift_of_zero (by simpa [zeroCoords] using hj)

theorem zeroSet_inter_activeSet (P : Fin d → ℝ) : zeroCoords P ∩ R.activeSet α = R.stratum α P := by
  ext j
  simp [zeroCoords, stratum, activeSet, and_comm]

include hP hη hηP hηb in
/-- **The lower box estimate.** If the weight is at least `c₀ > 0` on the box around `P`, the
chart measure of `{u^{2k_α} ≤ ε}` in the box is `Ω` of the stratum scale of `P`. -/
theorem llcScale_stratum_isBigO_box (hJ : (R.stratum α P).Nonempty) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hw : ∀ u ∈ faceBox P η, c₀ ≤ R.weight α u) :
    llcScale (R.stratumRlct α P) (R.stratumMult α P) =O[𝓝[>] (0 : ℝ)]
      fun ε ↦ (R.chartMeasure α (faceBox P η ∩ {u | R.cubeMonomial α u ≤ ε})).toReal := by
  set Z := zeroCoords P with hZ_def
  have hsub := R.faceBox_subset_cube α hP hηP hηb
  set A₂ : ℝ := ∏ j ∈ Zᶜ, R.b α ^ (2 * R.k α j) with hA₂_def
  have hA₂ : 0 < A₂ := Finset.prod_pos fun j _ ↦ pow_pos (R.b_pos α) _
  set c₂ : ℝ := ∏ j ∈ Zᶜ, faceShift P η j ^ (R.h α j : ℝ) with hc₂_def
  have hZc : ∀ j ∈ Zᶜ, P j ≠ 0 := fun j hj ↦ by simpa [hZ_def, zeroCoords] using hj
  have htpos : ∀ j ∈ Zᶜ, 0 < faceShift P η j := fun j hj ↦ by
    rw [faceShift_of_ne_zero (hZc j hj)]
    linarith [hηP j (hZc j hj)]
  have hc₂ : 0 < c₂ := Finset.prod_pos fun j hj ↦ Real.rpow_pos_of_pos (htpos j hj) _
  have hmono : ∀ u ∈ faceBox P η, R.cubeMonomial α u ≤ A₂ * R.faceMonomial α Z u := by
    intro u hu
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ ((hsub hu).1 j)
    have hub : ∀ j, u j ≤ R.b α := fun j ↦ ((hsub hu).2 j)
    rw [cubeMonomial, faceMonomial_eq, ← Finset.prod_mul_prod_compl Z, mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu0 j) _)
    exact Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hu0 j) _) fun j _ ↦
      pow_le_pow_left₀ (hu0 j) (hub j) _
  have hdens : ∀ u ∈ faceBox P η, c₂ * c₀ * R.faceDensity α Z u ≤ R.chartDensity α u := by
    intro u hu
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ ((hsub hu).1 j)
    have hS : ∀ j ∈ Zᶜ, faceShift P η j ≤ u j := fun j _ ↦ (hu j (mem_univ j)).1
    have hY : c₂ ≤ ∏ j ∈ Zᶜ, u j ^ (R.h α j : ℝ) :=
      Finset.prod_le_prod₀ (fun j hj ↦ Real.rpow_nonneg (htpos j hj).le _)
        fun j hj ↦ Real.rpow_le_rpow (htpos j hj).le (hS j hj) (Nat.cast_nonneg _)
    have hX : 0 ≤ ∏ j ∈ Z, u j ^ (R.h α j : ℝ) :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu0 j) _
    rw [chartDensity, faceDensity_eq, ← Finset.prod_mul_prod_compl Z]
    calc c₂ * c₀ * ∏ j ∈ Z, u j ^ (R.h α j : ℝ)
        = (∏ j ∈ Z, u j ^ (R.h α j : ℝ)) * c₂ * c₀ := by ring
      _ ≤ (∏ j ∈ Z, u j ^ (R.h α j : ℝ)) * (∏ j ∈ Zᶜ, u j ^ (R.h α j : ℝ)) * R.weight α u :=
          mul_le_mul (mul_le_mul_of_nonneg_left hY hX) (hw u hu) hc₀.le
            (mul_nonneg hX (hc₂.le.trans hY))
  have hkey : ∀ ε, c₂ * c₀ *
      sublevelVol (R.faceMeasure α Z) (cube d η) (R.faceMonomial α Z) (ε / A₂)
        ≤ (R.chartMeasure α (faceBox P η ∩ {u | R.cubeMonomial α u ≤ ε})).toReal := by
    intro ε
    rw [← R.sublevelVol_faceMeasure_box α Z (faceShift_zeroCoords P η) η]
    have hS₁ : MeasurableSet (faceBox P η ∩ {u | R.faceMonomial α Z u ≤ ε / A₂}) :=
      (measurableSet_faceBox P η).inter
        (measurableSet_le (R.measurable_faceMonomial α Z) measurable_const)
    have hsub' : faceBox P η ∩ {u | R.faceMonomial α Z u ≤ ε / A₂}
        ⊆ faceBox P η ∩ {u | R.cubeMonomial α u ≤ ε} := by
      rintro u ⟨hu, hf⟩
      refine ⟨hu, ?_⟩
      simp only [mem_ofPred_eq] at hf ⊢
      calc R.cubeMonomial α u ≤ A₂ * R.faceMonomial α Z u := hmono u hu
        _ ≤ A₂ * (ε / A₂) := by gcongr
        _ = ε := mul_div_cancel₀ _ hA₂.ne'
    rw [sublevelVol, ← ENNReal.toReal_ofReal (mul_pos hc₂ hc₀).le, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α)
      (measure_mono (inter_subset_left.trans hsub))) ?_
    calc ENNReal.ofReal (c₂ * c₀) * R.faceMeasure α Z (faceBox P η ∩
          {u | R.faceMonomial α Z u ≤ ε / A₂})
        = ∫⁻ u in faceBox P η ∩ {u | R.faceMonomial α Z u ≤ ε / A₂},
            ENNReal.ofReal (c₂ * c₀ * R.faceDensity α Z u) := by
          rw [faceMeasure, withDensity_apply _ hS₁, ← lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top]
          exact lintegral_congr fun u ↦ (ENNReal.ofReal_mul (mul_pos hc₂ hc₀).le).symm
      _ ≤ ∫⁻ u in faceBox P η ∩ {u | R.faceMonomial α Z u ≤ ε / A₂},
            ENNReal.ofReal (R.chartDensity α u) :=
          setLIntegral_mono' hS₁ fun u hu ↦ ENNReal.ofReal_le_ofReal (hdens u hu.1)
      _ = R.chartMeasure α (faceBox P η ∩ {u | R.faceMonomial α Z u ≤ ε / A₂}) :=
          (withDensity_apply _ hS₁).symm
      _ ≤ R.chartMeasure α (faceBox P η ∩ {u | R.cubeMonomial α u ≤ ε}) := measure_mono hsub'
  have hJ' : (Z ∩ R.activeSet α).Nonempty := by rwa [R.zeroSet_inter_activeSet α]
  have hF := R.hasLLCExponentsOn_faceMonomial α Z hJ' hη
  rw [R.zeroSet_inter_activeSet α] at hF
  have hcomp : (fun ε ↦ llcScale (R.stratumRlct α P) (R.stratumMult α P) (ε / A₂))
      =O[𝓝[>] (0 : ℝ)]
      fun ε ↦ sublevelVol (R.faceMeasure α Z) (cube d η) (R.faceMonomial α Z) (ε / A₂) :=
    hF.2.comp_tendsto (tendsto_div_const_nhdsGT_zero hA₂)
  refine ((isTheta_llcScale_comp_div hA₂).symm.1).trans (hcomp.trans (IsBigO.of_bound
    (c₂ * c₀)⁻¹ (Eventually.of_forall fun ε ↦ ?_)))
  rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _), Real.norm_of_nonneg ENNReal.toReal_nonneg,
    ← div_eq_inv_mul, le_div_iff₀ (mul_pos hc₂ hc₀)]
  linarith [hkey ε]

/-- The two-sided box `∏_j [P_j − η, P_j + η]` around `P`. -/
@[expose] def _root_.twoSidedBox (P : Fin d → ℝ) (η : ℝ) : Set (Fin d → ℝ) :=
  Icc (fun j ↦ P j - η) (fun j ↦ P j + η)

theorem _root_.measurableSet_twoSidedBox (P : Fin d → ℝ) (η : ℝ) : MeasurableSet
    (twoSidedBox P η) :=
  measurableSet_Icc

include hη hηP in
/-- **The upper box estimate.** The chart measure of `{u^{2k_α} ≤ ε}` in the two-sided box around
`P`, within the cube, is `O` of the stratum scale of `P`. -/
theorem chartMeasure_box_isBigO (hJ : (R.stratum α P).Nonempty) :
    (fun ε ↦ (R.chartMeasure α (twoSidedBox P η ∩ cube d (R.b α) ∩
      {u | R.cubeMonomial α u ≤ ε})).toReal) =O[𝓝[>] (0 : ℝ)]
        llcScale (R.stratumRlct α P) (R.stratumMult α P) := by
  set Z := zeroCoords P with hZ_def
  set E := twoSidedBox P η ∩ cube d (R.b α) with hE_def
  have hZc : ∀ j ∈ Zᶜ, P j ≠ 0 := fun j hj ↦ by simpa [hZ_def, zeroCoords] using hj
  have hZ0 : ∀ j ∈ Z, P j = 0 := fun j hj ↦ by simpa [hZ_def, zeroCoords] using hj
  -- the lower bound of the coordinates outside `Z`
  set c : ℝ := ∏ j ∈ Zᶜ, (P j - η) ^ (2 * R.k α j) with hc_def
  have hPη : ∀ j ∈ Zᶜ, 0 < P j - η := fun j hj ↦ by linarith [hηP j (hZc j hj)]
  have hc : 0 < c := Finset.prod_pos fun j hj ↦ pow_pos (hPη j hj) _
  obtain ⟨M, hM0, hM⟩ := R.exists_weight_le α
  set D : ℝ := M * ∏ j ∈ Zᶜ, R.b α ^ (R.h α j : ℝ) with hD_def
  have hD : 0 ≤ D := mul_nonneg hM0.le (Finset.prod_nonneg fun j _ ↦
    Real.rpow_nonneg (R.b_pos α).le _)
  -- on `E`: `c · f_Z ≤ f` and `chartDensity ≤ D · faceDensity`
  have hmono : ∀ u ∈ E, c * R.faceMonomial α Z u ≤ R.cubeMonomial α u := by
    rintro u ⟨hu, hcube⟩
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ hcube.1 j
    rw [cubeMonomial, faceMonomial_eq, ← Finset.prod_mul_prod_compl Z, mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu0 j) _)
    exact Finset.prod_le_prod₀ (fun j hj ↦ pow_nonneg (hPη j hj).le _) fun j hj ↦
      pow_le_pow_left₀ (hPη j hj).le (hu.1 j) _
  have hdens : ∀ u ∈ E, R.chartDensity α u ≤ D * R.faceDensity α Z u := by
    rintro u ⟨hu, hcube⟩
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ hcube.1 j
    have hX : 0 ≤ ∏ j ∈ Z, u j ^ (R.h α j : ℝ) :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu0 j) _
    have hY : ∏ j ∈ Zᶜ, u j ^ (R.h α j : ℝ) ≤ ∏ j ∈ Zᶜ, R.b α ^ (R.h α j : ℝ) :=
      Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (hu0 j) _) fun j _ ↦
        Real.rpow_le_rpow (hu0 j) (hcube.2 j) (Nat.cast_nonneg _)
    rw [chartDensity, faceDensity_eq, ← Finset.prod_mul_prod_compl Z]
    calc (∏ j ∈ Z, u j ^ (R.h α j : ℝ)) * (∏ j ∈ Zᶜ, u j ^ (R.h α j : ℝ)) * R.weight α u
        ≤ (∏ j ∈ Z, u j ^ (R.h α j : ℝ)) * (∏ j ∈ Zᶜ, R.b α ^ (R.h α j : ℝ)) * M :=
          mul_le_mul (mul_le_mul_of_nonneg_left hY hX) (hM u hcube) (R.weight_nonneg α u hcube)
            (mul_nonneg hX (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (R.b_pos α).le _))
      _ = D * ∏ j ∈ Z, u j ^ (R.h α j : ℝ) := by rw [hD_def]; ring
  -- `E ⊆ t + [0, 2η]^d` with `t = faceShift P η`
  have hEbox : E ⊆ pi univ fun j ↦ Icc (faceShift P η j) (faceShift P η j + 2 * η) := by
    rintro u ⟨hu, hcube⟩ j _
    have h1 : u j ∈ Icc (P j - η) (P j + η) := ⟨hu.1 j, hu.2 j⟩
    have h2 := mem_cube.1 hcube j
    rw [mem_Icc] at h1 h2 ⊢
    by_cases hj : P j = 0
    · rw [faceShift_of_zero hj]
      rw [hj] at h1
      constructor <;> linarith
    · rw [faceShift_of_ne_zero hj]
      constructor <;> linarith
  have hkey : ∀ ε, (R.chartMeasure α (E ∩ {u | R.cubeMonomial α u ≤ ε})).toReal
      ≤ D * sublevelVol (R.faceMeasure α Z) (cube d (2 * η)) (R.faceMonomial α Z) (ε / c) := by
    intro ε
    rw [← R.sublevelVol_faceMeasure_box α Z (faceShift_zeroCoords P η) (2 * η)]
    have hSE : MeasurableSet (E ∩ {u | R.cubeMonomial α u ≤ ε}) :=
      ((measurableSet_twoSidedBox P η).inter (R.measurableSet_cube α)).inter
        (measurableSet_le (R.measurable_cubeMonomial α) measurable_const)
    have hS₁ : MeasurableSet ((pi univ fun j ↦ Icc (faceShift P η j) (faceShift P η j + 2 * η)) ∩
        {u | R.faceMonomial α Z u ≤ ε / c}) :=
      (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc).inter
        (measurableSet_le (R.measurable_faceMonomial α Z) measurable_const)
    have hsub' : E ∩ {u | R.cubeMonomial α u ≤ ε} ⊆
        (pi univ fun j ↦ Icc (faceShift P η j) (faceShift P η j + 2 * η)) ∩
          {u | R.faceMonomial α Z u ≤ ε / c} := by
      rintro u ⟨hu, hf⟩
      refine ⟨hEbox hu, ?_⟩
      simp only [mem_ofPred_eq] at hf ⊢
      rw [le_div_iff₀ hc, mul_comm]
      exact (hmono u hu).trans hf
    have hfinZ : R.faceMeasure α Z
        ((pi univ fun j ↦ Icc (faceShift P η j) (faceShift P η j + 2 * η)) ∩
          {u | R.faceMonomial α Z u ≤ ε / c}) ≠ ⊤ := by
      refine ne_top_of_le_ne_top ?_ (measure_mono inter_subset_left)
      refine withDensity_ofReal_ne_top (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc)
        (isCompact_univ_pi fun _ ↦ isCompact_Icc).measure_lt_top.ne
        (C := ∏ j ∈ Z, (2 * η) ^ (R.h α j : ℝ)) fun u hu ↦ ?_
      rw [faceDensity_eq]
      refine Finset.prod_le_prod₀ (fun j hj ↦ ?_) fun j hj ↦ ?_
      · have := (hu j (mem_univ j)).1
        rw [faceShift_of_zero (hZ0 j hj)] at this
        exact Real.rpow_nonneg this _
      · have h := hu j (mem_univ j)
        rw [mem_Icc, faceShift_of_zero (hZ0 j hj), zero_add] at h
        exact Real.rpow_le_rpow h.1 h.2 (Nat.cast_nonneg _)
    rw [sublevelVol, ← ENNReal.toReal_ofReal hD, ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfinZ) ?_
    calc R.chartMeasure α (E ∩ {u | R.cubeMonomial α u ≤ ε})
        = ∫⁻ u in E ∩ {u | R.cubeMonomial α u ≤ ε}, ENNReal.ofReal (R.chartDensity α u) :=
          withDensity_apply _ hSE
      _ ≤ ∫⁻ u in E ∩ {u | R.cubeMonomial α u ≤ ε}, ENNReal.ofReal (D * R.faceDensity α Z u) :=
          setLIntegral_mono' hSE fun u hu ↦ ENNReal.ofReal_le_ofReal (hdens u hu.1)
      _ = ENNReal.ofReal D * R.faceMeasure α Z (E ∩ {u | R.cubeMonomial α u ≤ ε}) := by
          rw [faceMeasure, withDensity_apply _ hSE, ← lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top]
          exact lintegral_congr fun u ↦ ENNReal.ofReal_mul hD
      _ ≤ ENNReal.ofReal D * R.faceMeasure α Z
            ((pi univ fun j ↦ Icc (faceShift P η j) (faceShift P η j + 2 * η)) ∩
              {u | R.faceMonomial α Z u ≤ ε / c}) :=
          mul_le_mul_right (measure_mono hsub') _
  have hJ' : (Z ∩ R.activeSet α).Nonempty := by rwa [R.zeroSet_inter_activeSet α]
  have hF := R.hasLLCExponentsOn_faceMonomial α Z hJ' (by linarith : 0 < 2 * η)
  rw [R.zeroSet_inter_activeSet α] at hF
  have hcomp : (fun ε ↦ sublevelVol (R.faceMeasure α Z) (cube d (2 * η)) (R.faceMonomial α Z)
      (ε / c)) =O[𝓝[>] (0 : ℝ)]
      fun ε ↦ llcScale (R.stratumRlct α P) (R.stratumMult α P) (ε / c) :=
    hF.1.comp_tendsto (tendsto_div_const_nhdsGT_zero hc)
  refine (IsBigO.of_bound D (Eventually.of_forall fun ε ↦ ?_)).trans
    (hcomp.trans (isTheta_llcScale_comp_div hc).1)
  rw [Real.norm_of_nonneg ENNReal.toReal_nonneg, Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
  exact hkey ε

end Box

/-! ## The covering bound and the local type from an atlas -/

theorem stratum_nonempty_of_cubeMonomial_eq_zero (α : R.ι) {P : Fin d → ℝ}
    (hf : R.cubeMonomial α P = 0) : (R.stratum α P).Nonempty := by
  obtain ⟨j, -, hj⟩ := Finset.prod_eq_zero_iff.mp hf
  rw [pow_eq_zero_iff'] at hj
  refine ⟨j, ?_⟩
  simp only [stratum, activeSet, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨Nat.pos_of_ne_zero fun h ↦ hj.2 (by simp [h]), hj.1⟩

/-- Small `η` for the box around `P ∈ cube`: below `b_α` and below every nonzero coordinate. -/
theorem eventually_box_param (α : R.ι) {P : Fin d → ℝ} (hP : P ∈ cube d (R.b α)) :
    ∀ᶠ η in 𝓝[>] (0 : ℝ), (∀ j, P j ≠ 0 → η < P j) ∧ η ≤ R.b α := by
  refine (Filter.eventually_all.mpr fun j ↦ ?_).and
    (eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds (R.b_pos α)))
  by_cases hj : P j = 0
  · exact Eventually.of_forall fun _ h ↦ absurd hj h
  · exact (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds
      (lt_of_le_of_ne (hP.1 j) (Ne.symm hj)))).mono fun _ h _ ↦ h

/-- **The covering bound.** If every zero of `u^{2k_α}` in the compact `E ⊆ cube` has a stratum
type at most as singular as `(λ, m)`, the chart measure of `E ∩ {u^{2k_α} ≤ ε}` is
`O(ε^λ (−log ε)^{m−1})`. -/
theorem chartMeasure_isBigO_of_forall (α : R.ι) {E : Set (Fin d → ℝ)} (hE : IsCompact E)
    (hEc : E ⊆ cube d (R.b α)) {lam : ℝ} {m : ℕ}
    (hτ : ∀ P ∈ E, R.cubeMonomial α P = 0 →
      MoreSingular lam m (R.stratumRlct α P) (R.stratumMult α P)) :
    (fun ε ↦ (R.chartMeasure α (E ∩ {u | R.cubeMonomial α u ≤ ε})).toReal)
      =O[𝓝[>] (0 : ℝ)] llcScale lam m := by
  classical
  have hloc : ∀ P ∈ E, ∃ U ∈ 𝓝 P,
      (fun ε ↦ (R.chartMeasure α (U ∩ cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε})).toReal)
        =O[𝓝[>] (0 : ℝ)] llcScale lam m := by
    intro P hP
    by_cases hf : R.cubeMonomial α P = 0
    · have hJ := R.stratum_nonempty_of_cubeMonomial_eq_zero α hf
      obtain ⟨η, ⟨hηP, hηb⟩, hη⟩ := ((R.eventually_box_param α (hEc hP)).and
        eventually_mem_nhdsWithin).exists
      rw [mem_Ioi] at hη
      refine ⟨pi univ fun j ↦ Ioo (P j - η) (P j + η),
        set_pi_mem_nhds finite_univ fun j _ ↦ Ioo_mem_nhds (by linarith) (by linarith), ?_⟩
      have hsub : (pi univ fun j ↦ Ioo (P j - η) (P j + η)) ⊆ twoSidedBox P η :=
        fun u hu ↦ ⟨fun j ↦ (hu j (mem_univ j)).1.le, fun j ↦ (hu j (mem_univ j)).2.le⟩
      refine (IsBigO.of_bound 1 (Eventually.of_forall fun ε ↦ ?_)).trans
        ((R.chartMeasure_box_isBigO α hη hηP hJ).trans
          (moreSingular_iff_isBigO.mp (hτ P hP hf)))
      rw [one_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg,
        Real.norm_of_nonneg ENNReal.toReal_nonneg]
      refine ENNReal.toReal_mono (ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α)
        (measure_mono fun u hu ↦ hu.1.2)) (measure_mono ?_)
      exact inter_subset_inter_left _ (inter_subset_inter_left _ hsub)
    · have hpos : 0 < R.cubeMonomial α P := lt_of_le_of_ne (R.cubeMonomial_nonneg α P) (Ne.symm hf)
      refine ⟨{u | R.cubeMonomial α P / 2 < R.cubeMonomial α u},
        (isOpen_lt continuous_const (R.continuous_cubeMonomial α)).mem_nhds
          (by simp only [mem_ofPred_eq]; linarith), ?_⟩
      refine IsBigO.of_bound 0 ?_
      filter_upwards [Ioo_mem_nhdsGT (half_pos hpos)] with ε hε
      have hempty : {u | R.cubeMonomial α P / 2 < R.cubeMonomial α u} ∩ cube d (R.b α) ∩
          {u | R.cubeMonomial α u ≤ ε} = ∅ := by
        ext u
        simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
        intro h h'
        linarith [hε.2, h.1]
      rw [hempty, measure_empty, ENNReal.toReal_zero, norm_zero, zero_mul]
  choose U hU hO using hloc
  obtain ⟨t, ht⟩ := hE.elim_nhds_subcover' U hU
  have hsum : (fun ε ↦ t.sum fun P : E ↦ (R.chartMeasure α
      (U P.1 P.2 ∩ cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε})).toReal)
        =O[𝓝[>] (0 : ℝ)] llcScale lam m :=
    (IsBigO.sum fun P _ ↦ hO P.1 P.2).congr_left fun ε ↦ Finset.sum_apply ε t _
  refine (IsBigO.of_bound 1 (Eventually.of_forall fun ε ↦ ?_)).trans hsum
  rw [one_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg,
    Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ ENNReal.toReal_nonneg)]
  have hcover : E ∩ {u | R.cubeMonomial α u ≤ ε} ⊆
      ⋃ P ∈ t, U P.1 P.2 ∩ cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε} := by
    rintro u ⟨hu, hf⟩
    obtain ⟨P, hP, hu'⟩ := mem_iUnion₂.mp (ht hu)
    exact mem_iUnion₂.mpr ⟨P, hP, ⟨hu', hEc hu⟩, hf⟩
  rw [← ENNReal.toReal_sum fun P _ ↦ ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α)
    (measure_mono fun u hu ↦ hu.1.2)]
  refine ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun P _ ↦ ne_top_of_le_ne_top
    (R.chartMeasure_cube_ne_top α) (measure_mono fun u hu ↦ hu.1.2)) ?_
  exact (measure_mono hcover).trans (measure_biUnion_finset_le _ _)

open Classical in
/-- The *bad set* of a chart for a type `(λ, m)`: the points of the cube whose stratum type is
strictly more singular than `(λ, m)`, as the finite union of the coordinate faces
`cube ∩ {P | ∀ j ∈ J, P_j = 0}` over the nonempty sets `J` of active coordinates of type strictly
more singular than `(λ, m)`. -/
@[expose] noncomputable def badSet (α : R.ι) (lam : ℝ) (m : ℕ) : Set (Fin d → ℝ) :=
  ⋃ J ∈ (R.activeSet α).powerset.filter (fun J ↦ J.Nonempty ∧
      ¬ MoreSingular lam m (R.faceRlct α J) (R.faceMult α J)),
    cube d (R.b α) ∩ {P | ∀ j ∈ J, P j = 0}

theorem badSet_subset_cube (α : R.ι) (lam : ℝ) (m : ℕ) : R.badSet α lam m ⊆ cube d (R.b α) := by
  rw [badSet]
  exact iUnion₂_subset fun J _ ↦ inter_subset_left

theorem isCompact_badSet (α : R.ι) (lam : ℝ) (m : ℕ) : IsCompact (R.badSet α lam m) := by
  have hc : IsCompact (cube d (R.b α)) := isCompact_Icc
  refine hc.of_isClosed_subset ?_ (R.badSet_subset_cube α lam m)
  rw [badSet]
  refine (Finset.finite_toSet _).isClosed_biUnion fun J _ ↦ ?_
  refine isClosed_Icc.inter ?_
  have : {P : Fin d → ℝ | ∀ j ∈ J, P j = 0} = ⋂ j ∈ J, {P | P j = 0} := by
    ext P
    simp
  rw [this]
  exact isClosed_biInter fun j _ ↦ isClosed_eq (continuous_apply j) continuous_const

/-- A zero of `u^{2k_α}` in the cube whose stratum type is not at most as singular as `(λ, m)`
lies in the bad set. -/
theorem mem_badSet_of_not_moreSingular (α : R.ι) (lam : ℝ) (m : ℕ) {P : Fin d → ℝ}
    (hP : P ∈ cube d (R.b α)) (hf : R.cubeMonomial α P = 0)
    (h : ¬ MoreSingular lam m (R.stratumRlct α P) (R.stratumMult α P)) : P ∈ R.badSet α lam m := by
  rw [badSet]
  refine mem_iUnion₂.mpr ⟨R.stratum α P, ?_, hP, fun j hj ↦ ?_⟩
  · simp only [Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.filter_subset _ _, R.stratum_nonempty_of_cubeMonomial_eq_zero α hf, h⟩
  · simpa [stratum] using (Finset.mem_filter.mp hj).2

/-- Conversely, a point of the bad set has a stratum type strictly more singular than `(λ, m)`. -/
theorem not_moreSingular_of_mem_badSet (α : R.ι) (lam : ℝ) (m : ℕ) {P : Fin d → ℝ}
    (hP : P ∈ R.badSet α lam m) :
    ¬ MoreSingular lam m (R.stratumRlct α P) (R.stratumMult α P) := by
  rw [badSet] at hP
  obtain ⟨J, hJ, -, hPJ⟩ := mem_iUnion₂.mp hP
  simp only [Finset.mem_filter, Finset.mem_powerset] at hJ
  obtain ⟨hJa, hJne, hJbad⟩ := hJ
  have hJsub : J ⊆ R.stratum α P := fun j hj ↦
    Finset.mem_filter.mpr ⟨hJa hj, hPJ j hj⟩
  intro h
  exact hJbad (h.trans (R.moreSingular_faceType_of_subset α hJne hJsub))

/-- **The local singularity type from an atlas.** For a resolution atlas `R` of `(K, φ, W)` with
continuous chart maps and a point `x` with `K(x) = 0`: if `(λ, m)` is at least as singular as
the stratum type of every point of the fibre of `R` over `x`, and some fibre point realises
`(λ, m)` with positive weight, then `(λ, m)` is the local singularity type at `x`. -/
theorem hasLocalSingularityType_of_atlas (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφm : AEMeasurable φ (volume.restrict W))
    (hg : ∀ α, ContinuousOn (R.g α) (cube d (R.b α))) {x : Fin d → ℝ} (hx : K x = 0)
    {lam : ℝ} {m : ℕ}
    (hτ : ∀ α, ∀ P ∈ cube d (R.b α), R.g α P = x →
      MoreSingular lam m (R.stratumRlct α P) (R.stratumMult α P))
    (hrep : ∃ α, ∃ P ∈ cube d (R.b α), R.g α P = x ∧ R.stratumRlct α P = lam ∧
      R.stratumMult α P = m ∧ 0 < R.weight α P) :
    HasLocalSingularityType K φ W x lam m := by
  classical
  -- the bad sets miss the fibre, so their images miss a neighbourhood of `x`
  have hbad : ∀ α, ∀ᶠ r in 𝓝[>] (0 : ℝ),
      ∀ P ∈ R.badSet α lam m, R.g α P ∉ closedBall x r := by
    intro α
    have hcpt : IsCompact (R.g α '' R.badSet α lam m) :=
      (R.isCompact_badSet α lam m).image_of_continuousOn
        ((hg α).mono (R.badSet_subset_cube α lam m))
    have hxn : x ∉ R.g α '' R.badSet α lam m := by
      rintro ⟨P, hP, hPx⟩
      exact R.not_moreSingular_of_mem_badSet α lam m hP
        (hτ α P (R.badSet_subset_cube α lam m hP) hPx)
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hcpt.isClosed.isOpen_compl x hxn
    filter_upwards [Ioo_mem_nhdsGT hρ] with r hr P hP hPr
    exact hball (closedBall_subset_ball hr.2 hPr) ⟨P, hP, rfl⟩
  filter_upwards [Filter.eventually_all.mpr hbad, self_mem_nhdsWithin] with r hr hr0
  rw [mem_Ioi] at hr0
  have hA : MeasurableSet (W ∩ closedBall x r) := hW.inter measurableSet_closedBall
  rw [isSingularityType_iff hA (fun w hw ↦ hφ w hw.1)
    (hφm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)), HasLLCExponentsOn]
  -- the transport identity on `W ∩ B̄(x, r)`
  set E : R.ι → Set (Fin d → ℝ) := fun α ↦ cube d (R.b α) ∩ R.g α ⁻¹' closedBall x r with hE_def
  have hEeq : ∀ α, cube d (R.b α) ∩ R.g α ⁻¹' (W ∩ closedBall x r) = E α := fun α ↦ by
    ext u
    simp only [hE_def, mem_inter_iff, mem_preimage]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, R.g_mapsTo α h.1, h.2⟩⟩
  have hV : sublevelVol (priorMeasure φ Set.univ) (W ∩ closedBall x r) K =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε ↦ ∑ α, (R.chartMeasure α (E α ∩ {u | R.cubeMonomial α u ≤ ε})).toReal := by
    filter_upwards [Ioo_mem_nhdsGT R.δ_pos] with ε hε
    rw [sublevelVol, R.priorMeasure_inter_sublevel_eq_sum hW hKm hA inter_subset_left hε.2,
      ENNReal.toReal_sum fun α _ ↦ ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α)
        (measure_mono fun u hu ↦ hu.1.1)]
    simp only [hEeq]
  rw [Filter.EventuallyEq.isTheta_congr_left hV]
  obtain ⟨α₀, P₀, hP₀, hgP₀, hl₀, hm₀, hw₀⟩ := hrep
  refine isTheta_sum_of_isBigO α₀ (fun α ↦ ?_) ?_ fun α ↦ Eventually.of_forall fun _ ↦
    ENNReal.toReal_nonneg
  · -- upper bound: `E α` is compact and avoids the bad set
    have hcube : IsCompact (cube d (R.b α)) := isCompact_Icc
    have hEc : IsCompact (E α) :=
      hcube.of_isClosed_subset ((hg α).preimage_isClosed_of_isClosed
        isClosed_Icc isClosed_closedBall) inter_subset_left
    refine R.chartMeasure_isBigO_of_forall α hEc inter_subset_left fun P hP hf ↦ ?_
    by_contra hcon
    exact hr α P (R.mem_badSet_of_not_moreSingular α lam m hP.1 hf hcon) hP.2
  · -- lower bound: a box around the representative maps into the ball
    have hf₀ : R.cubeMonomial α₀ P₀ = 0 := by
      rw [cubeMonomial, ← R.monomial α₀ P₀ hP₀, hgP₀, hx]
    have hJ := R.stratum_nonempty_of_cubeMonomial_eq_zero α₀ hf₀
    set c₀ : ℝ := R.weight α₀ P₀ / 2 with hc₀_def
    have hc₀ : 0 < c₀ := by positivity
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousWithinAt_iff.mp (R.weight_continuousOn α₀ P₀ hP₀)
      c₀ hc₀
    obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousWithinAt_iff.mp (hg α₀ P₀ hP₀) r hr0
    obtain ⟨η, ⟨⟨hηP, hηb⟩, hη₁, hη₂⟩, hη⟩ := (((R.eventually_box_param α₀ hP₀).and
      ((eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ₁)).and
        (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ₂)))).and
      eventually_mem_nhdsWithin).exists
    rw [mem_Ioi] at hη
    have hsub := R.faceBox_subset_cube α₀ hP₀ hηP hηb
    have hdist : ∀ u ∈ faceBox P₀ η, dist u P₀ ≤ η := by
      intro u hu
      rw [dist_pi_le_iff hη.le]
      intro j
      have h := hu j (mem_univ j)
      rw [mem_Icc] at h
      rw [Real.dist_eq, abs_sub_le_iff]
      by_cases hj : P₀ j = 0
      · rw [faceShift_of_zero hj] at h
        rw [hj]
        constructor <;> linarith
      · rw [faceShift_of_ne_zero hj] at h
        constructor <;> linarith
    have hw : ∀ u ∈ faceBox P₀ η, c₀ ≤ R.weight α₀ u := fun u hu ↦ by
      have := hδ₁' (hsub hu) ((hdist u hu).trans_lt hη₁)
      rw [Real.dist_eq, abs_sub_lt_iff] at this
      linarith
    have hboxE : faceBox P₀ η ⊆ E α₀ := fun u hu ↦ by
      refine ⟨hsub hu, ?_⟩
      rw [mem_preimage, mem_closedBall, ← hgP₀]
      exact (hδ₂' (hsub hu) ((hdist u hu).trans_lt hη₂)).le
    have hlow := R.llcScale_stratum_isBigO_box α₀ hP₀ hη hηP hηb hJ hc₀ hw
    rw [hl₀, hm₀] at hlow
    refine hlow.trans (IsBigO.of_bound 1 (Eventually.of_forall fun ε ↦ ?_))
    rw [one_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg,
      Real.norm_of_nonneg ENNReal.toReal_nonneg]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α₀)
      (measure_mono fun u hu ↦ hu.1.1)) (measure_mono (inter_subset_inter_left _ hboxE))

/-- **A chart centred at `x` bounds the local type.** For a chart `α` with continuous chart map,
`g_α(0) = x` and positive weight at its origin, every ball `W ∩ B̄(x, r)`, `r > 0`, that has a
singularity type is at least as singular as the chart type `(λ_α, m_α)`. -/
theorem moreSingular_chartType_of_center (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφm : AEMeasurable φ (volume.restrict W)) (α : R.ι)
    (hg : ContinuousOn (R.g α) (cube d (R.b α))) {x : Fin d → ℝ} (hx : R.g α 0 = x)
    (hw : 0 < R.weight α 0) {r : ℝ} (hr : 0 < r) {lam : ℝ} {m : ℕ}
    (h : IsSingularityType K φ (W ∩ closedBall x r) lam m) :
    MoreSingular lam m (R.chartRlct α) (R.chartMult α) := by
  rw [moreSingular_iff_isBigO]
  have hA : MeasurableSet (W ∩ closedBall x r) := hW.inter measurableSet_closedBall
  have h0 : (0 : Fin d → ℝ) ∈ cube d (R.b α) := ⟨fun j ↦ le_rfl, fun j ↦ (R.b_pos α).le⟩
  have hJ : (R.stratum α 0).Nonempty := by rw [stratum_zero]; exact activeSet_nonempty R α
  set c₀ : ℝ := R.weight α 0 / 2 with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.continuousWithinAt_iff.mp (R.weight_continuousOn α 0 h0) c₀ hc₀
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.continuousWithinAt_iff.mp (hg 0 h0) r hr
  obtain ⟨η, ⟨⟨hηP, hηb⟩, hη₁, hη₂⟩, hη⟩ := (((R.eventually_box_param α h0).and
    ((eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ₁)).and
      (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ₂)))).and
    eventually_mem_nhdsWithin).exists
  rw [mem_Ioi] at hη
  have hsub := R.faceBox_subset_cube α h0 hηP hηb
  have hdist : ∀ u ∈ faceBox (0 : Fin d → ℝ) η, dist u (0 : Fin d → ℝ) ≤ η := by
    intro u hu
    rw [dist_pi_le_iff hη.le]
    intro j
    have hj := hu j (mem_univ j)
    rw [mem_Icc, faceShift_of_zero (Pi.zero_apply j)] at hj
    rw [Real.dist_eq, Pi.zero_apply, sub_zero, abs_le]
    constructor <;> linarith
  have hwb : ∀ u ∈ faceBox 0 η, c₀ ≤ R.weight α u := fun u hu ↦ by
    have := hδ₁' (hsub hu) ((hdist u hu).trans_lt hη₁)
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith
  have hlow := R.llcScale_stratum_isBigO_box α h0 hη hηP hηb hJ hc₀ hwb
  rw [stratumRlct, stratumMult, stratum_zero, faceRlct_activeSet, faceMult_activeSet] at hlow
  refine hlow.trans ((IsBigO.of_bound 1 ?_).trans h.isTheta.1)
  filter_upwards [Ioo_mem_nhdsGT R.δ_pos] with ε hε
  rw [one_mul, Real.norm_of_nonneg ENNReal.toReal_nonneg, ← sublevelVol_priorMeasure hA
    (fun w hw ↦ hφ w hw.1) (hφm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)),
    Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _), sublevelVol,
    R.priorMeasure_inter_sublevel_eq_sum hW hKm hA inter_subset_left hε.2,
    ENNReal.toReal_sum fun β _ ↦ ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top β)
      (measure_mono fun u hu ↦ hu.1.1)]
  refine le_trans ?_ (Finset.single_le_sum (fun β _ ↦ ENNReal.toReal_nonneg) (Finset.mem_univ α))
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α)
    (measure_mono fun u hu ↦ hu.1.1)) (measure_mono (inter_subset_inter_left _ fun u hu ↦ ?_))
  refine ⟨hsub hu, R.g_mapsTo α (hsub hu), ?_⟩
  rw [mem_closedBall, ← hx]
  exact (hδ₂' (hsub hu) ((hdist u hu).trans_lt hη₂)).le

end ResolutionAtlas

end SingularLearningTheory
