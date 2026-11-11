/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Assembly
public import SLT.Resolution.Surjective
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.BitVec

/-!
# Resolution charts for the optimizer

Finite signed coordinate faces supply active optimizer charts covering every
positive low sublevel, including feasible strata of prior measure zero. The prior
atlas embeds as the left summand of an auxiliary atlas with zero prior.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal Manifold ContDiff

variable {d : ℕ}

/-- A coordinate face is parametrized by a full cube, ignoring the masked coordinates. -/
@[expose] def _root_.faceMask (Z : Finset (Fin d)) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun j ↦ if j ∈ Z then 0 else u j

@[simp] theorem _root_.faceMask_empty (u : Fin d → ℝ) : faceMask ∅ u = u := by
  funext j
  simp [faceMask]

@[simp] theorem _root_.faceMask_zero (Z : Finset (Fin d)) :
    faceMask Z (0 : Fin d → ℝ) = 0 := by
  funext j
  simp [faceMask]

private theorem analyticOnNhd_faceMask (Z : Finset (Fin d)) :
    AnalyticOnNhd ℝ (faceMask Z) univ := by
  intro u _
  refine analyticAt_pi_iff.mpr fun j ↦ ?_
  by_cases hj : j ∈ Z
  · simpa [faceMask, hj] using (analyticAt_const : AnalyticAt ℝ (fun _ : Fin d → ℝ ↦ (0 : ℝ)) u)
  · have he : (fun x : Fin d → ℝ ↦ faceMask Z x j) =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j) := by
      funext x
      simp only [faceMask, if_neg hj, ContinuousLinearMap.proj_apply]
    rw [he]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).analyticAt u

private theorem faceMask_mapsTo_cube (Z : Finset (Fin d)) {b : ℝ} (hb : 0 ≤ b) :
    MapsTo (faceMask Z) (cube d b) (cube d b) := by
  intro u hu
  refine mem_cube.2 fun j ↦ ?_
  by_cases hjZ : j ∈ Z
  · simpa [faceMask, hjZ] using (show (0 : ℝ) ∈ Icc 0 b from ⟨le_rfl, hb⟩)
  · simpa [faceMask, hjZ] using mem_cube.1 hu j

private theorem prod_pow_faceMask (Z : Finset (Fin d)) (k : Fin d → ℕ)
    (hZ : ∀ j ∈ Z, k j = 0) (u : Fin d → ℝ) :
    (∏ j, faceMask Z u j ^ k j) = ∏ j, u j ^ k j := by
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ Z
  · simp [faceMask, hj, hZ j hj]
  · simp [faceMask, hj]

/-- The full stored resolution charts cover a low sublevel before open orthants
are filtered out. No prior-positive or full-dimensional point premise is needed. -/
theorem AtlasData.exists_monomial_coordinate_of_lt
    {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (A : AtlasData K φ W) {w : Fin d → ℝ} (hw : w ∈ W) (hKw : K w < A.δ) :
    ∃ σ : A.RC.ι, ∃ i : (A.C σ).I, ∃ v : Fin d → ℝ,
      v ∈ obox d ((A.C σ).a i) ∧ ((A.C σ).ch i).Γ v = w := by
  classical
  have hex : ∃ σ, A.ρO σ w ≠ 0 := by
    by_contra h
    push Not at h
    have hone := A.sum_ρO_eq_one w hw hKw
    simp [h] at hone
  obtain ⟨σ, hσ⟩ := hex
  have hwB : w ∈ A.Bcl σ := A.ρO_supp σ w hσ
  have hwRange : w ∈ Set.range (A.RC.resolution σ).π := by
    rw [(A.RC.resolution σ).range_π]
    exact A.Bcl_subset σ hwB
  obtain ⟨P, hP⟩ := hwRange
  have hsmall : P ∈ (A.C σ).smallUnion := A.Bcl_fibre σ (by
    change (A.RC.resolution σ).π P ∈ A.Bcl σ
    simpa [hP] using hwB)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hsmall
  obtain ⟨v, hv, hvP⟩ := hi
  refine ⟨σ, i, v, hv, ?_⟩
  change (A.RC.resolution σ).π (((A.C σ).ch i).e.symm v) = w
  rw [hvP, hP]

/-- Package arbitrary feasible active monomial charts for use by the existing
resolved-likelihood/MLE APIs. No posterior or singularity type is taken from this
auxiliary zero-prior atlas. -/
@[expose] noncomputable def ResolutionAtlas.optimizerZeroPriorAtlas
    {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {ι : Type} [Fintype ι] [Nonempty ι]
    (b : ι → ℝ) (hb : ∀ α, 0 < b α)
    (k : ι → Fin d → ℕ) (hk : ∀ α, ∃ j, 0 < k α j)
    (g : ι → (Fin d → ℝ) → (Fin d → ℝ))
    (hga : ∀ α, AnalyticOnNhd ℝ (g α) (cube d (b α)))
    (hgm : ∀ α, Measurable (g α))
    (hgW : ∀ α, MapsTo (g α) (cube d (b α)) W)
    (hKg : ∀ α, ∀ u ∈ cube d (b α), K (g α u) = ∏ j, u j ^ (2 * k α j)) :
    ResolutionAtlas K (fun _ ↦ 0) W where
  ι := ι
  b := b
  b_pos := hb
  k := k
  h := fun _ _ ↦ 0
  active := hk
  g := g
  g_analytic := hga
  g_measurable := hgm
  g_mapsTo := hgW
  monomial := hKg
  weight := fun _ _ ↦ 0
  weight_nonneg := fun _ _ _ ↦ le_rfl
  weight_contDiffOn := fun _ ↦ contDiffOn_const
  χ := fun _ ↦ 1
  χ_measurable := measurable_const
  χ_nonneg := fun _ ↦ zero_le_one
  χ_le_one := fun _ ↦ le_rfl
  δ := 1
  δ_pos := zero_lt_one
  χ_eq_one := fun _ _ _ ↦ rfl
  transport := by simp


private theorem continuous_faceMask (Z : Finset (Fin d)) : Continuous (faceMask Z) := by
  refine continuous_pi fun j ↦ ?_
  by_cases hj : j ∈ Z
  · simpa [faceMask, hj] using
      (continuous_const : Continuous (fun _ : Fin d → ℝ ↦ (0 : ℝ)))
  · simpa [faceMask, hj] using (continuous_apply j : Continuous (fun u : Fin d → ℝ ↦ u j))

/-- Every point of an open signed box is represented by a positive cube point
on a uniquely determined zero-coordinate face; the signs at zero are immaterial. -/
private theorem exists_signed_face_coordinates {a : ℝ} (ha : 0 < a)
    {v : Fin d → ℝ} (hv : v ∈ obox d a) :
    ∃ (ε : Fin d → Bool) (Z : Finset (Fin d)) (u : Fin d → ℝ),
      u ∈ ocube d (Real.sqrt a) ∧
      (∀ j, j ∈ Z ↔ v j = 0) ∧ orthantSq ε (faceMask Z u) = v := by
  classical
  let ε : Fin d → Bool := fun j ↦ decide (0 ≤ v j)
  let Z : Finset (Fin d) := Finset.univ.filter fun j ↦ v j = 0
  let u : Fin d → ℝ := fun j ↦ if v j = 0 then Real.sqrt a / 2 else Real.sqrt |v j|
  have hsa : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  refine ⟨ε, Z, u, ?_, ?_, ?_⟩
  · intro j _
    by_cases hj : v j = 0
    · change 0 < u j ∧ u j < Real.sqrt a
      simp only [u, if_pos hj]
      exact ⟨half_pos hsa, half_lt_self hsa⟩
    · have hjabs : |v j| < a := abs_lt.mpr (hv j (mem_univ j))
      change 0 < u j ∧ u j < Real.sqrt a
      simp only [u, if_neg hj]
      exact ⟨Real.sqrt_pos.mpr (abs_pos.mpr hj),
        Real.sqrt_lt_sqrt (abs_nonneg _) hjabs⟩
  · intro j
    simp [Z]
  · funext j
    by_cases hj : v j = 0
    · simp [orthantSq, faceMask, Z, u, hj]
    · by_cases hsign : 0 ≤ v j
      · simp [orthantSq, faceMask, Z, u, hj, ε, orthantSign, hsign,
          Real.sq_sqrt (abs_nonneg (v j)), abs_of_nonneg hsign]
      · have hneg : v j < 0 := lt_of_not_ge hsign
        simp [orthantSq, faceMask, Z, u, hj, ε, orthantSign, hsign,
          Real.sq_sqrt (abs_nonneg (v j)), abs_of_neg hneg,
          Real.sq_sqrt (neg_nonneg.mpr hneg.le)]

section LocalFaces

variable {N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {Kf φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ}
  {g : M → (Fin d → ℝ)} {P : M}

namespace MonomialChart

variable (c : MonomialChart Kf φ₂ H g P)

/-- The chart map on a signed coordinate face, parametrized by a full cube. -/
@[expose] noncomputable def faceChartMap (ε : Fin d → Bool) (Z : Finset (Fin d)) :
    (Fin d → ℝ) → (Fin d → ℝ) := fun u ↦ c.chartMap ε (faceMask Z u)

@[simp] theorem faceChartMap_empty (ε : Fin d → Bool) :
    c.faceChartMap ε ∅ = c.chartMap ε := by
  funext u
  simp [faceChartMap]

@[simp] theorem faceChartMap_zero (ε : Fin d → Bool) (Z : Finset (Fin d)) :
    c.faceChartMap ε Z 0 = g P := by
  simp [faceChartMap, c.chartMap_zero]

theorem faceChartMap_mem_range (ε : Fin d → Bool) (Z : Finset (Fin d)) (u : Fin d → ℝ) :
    c.faceChartMap ε Z u ∈ Set.range g := by
  classical
  unfold faceChartMap chartMap
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨P, rfl⟩

theorem faceMask_mem_obox {Z : Finset (Fin d)} {u : Fin d → ℝ}
    (hu : u ∈ cube d c.rad) : faceMask Z u ∈ obox d c.rad' :=
  c.cube_subset_obox (faceMask_mapsTo_cube Z c.rad_pos.le hu)

theorem faceSq_mem_O (ε : Fin d → Bool) (Z : Finset (Fin d))
    {u : Fin d → ℝ} (hu : u ∈ cube d c.rad) : orthantSq ε (faceMask Z u) ∈ c.O :=
  c.orthantSq_mem_O ε (c.faceMask_mem_obox hu)

theorem faceChartMap_eq (ε : Fin d → Bool) (Z : Finset (Fin d))
    {u : Fin d → ℝ} (hu : u ∈ cube d c.rad) :
    c.faceChartMap ε Z u = c.Γ (orthantSq ε (faceMask Z u)) :=
  c.chartMap_eq ε (c.faceMask_mem_obox hu)

theorem measurable_faceChartMap
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) (Z : Finset (Fin d)) :
    Measurable (c.faceChartMap ε Z) :=
  (c.measurable_chartMap hg ε).comp (continuous_faceMask Z).measurable

theorem analyticOnNhd_faceChartMap
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) (ε : Fin d → Bool) (Z : Finset (Fin d)) :
    AnalyticOnNhd ℝ (c.faceChartMap ε Z) (cube d c.rad) := by
  intro u hu
  exact AnalyticAt.comp (f := faceMask Z)
    (c.chartMap_analyticOnNhd hg ε _ (faceMask_mapsTo_cube Z c.rad_pos.le hu))
    (analyticOnNhd_faceMask Z u (mem_univ u))

/-- Goodness is tested on the relative-open signed face. -/
@[expose] def IsGoodFace (W : Set (Fin d → ℝ)) (ε : Fin d → Bool) (Z : Finset (Fin d)) : Prop :=
  ∀ u ∈ ocube d c.rad, c.faceChartMap ε Z u ∈ W

@[simp] theorem isGoodFace_empty (W : Set (Fin d → ℝ)) (ε : Fin d → Bool) :
    c.IsGoodFace W ε ∅ ↔ c.IsGood W ε := by
  simp [IsGoodFace, IsGood]

private theorem face_ocube_subset_cube : ocube d c.rad ⊆ cube d c.rad :=
  (Set.pi_mono fun _ _ ↦ Ioo_subset_Icc_self).trans (cube_eq_pi _ _).ge

private theorem face_prod_pow_pos {u : Fin d → ℝ} (hu : u ∈ ocube d c.rad)
    (k : Fin d → ℕ) : 0 < ∏ j, u j ^ (2 * k j) :=
  Finset.prod_pos fun j _ ↦ pow_pos (hu j (mem_univ j)).1 _

/-- Generalizes `isGood_or_disjoint`. A boundary monomial either vanishes on
this face or has a fixed sign there. The empty-mask specialization is the old lemma. -/
theorem isGoodFace_or_disjoint {W U : Set (Fin d → ℝ)}
    (hWH : ∀ w ∈ U, (w ∈ W ↔ ∀ i, 0 ≤ H i w))
    (ε : Fin d → Bool) (Z : Finset (Fin d))
    (hU : ∀ u ∈ ocube d c.rad, c.faceChartMap ε Z u ∈ U) :
    c.IsGoodFace W ε Z ∨ ∀ u ∈ ocube d c.rad, c.faceChartMap ε Z u ∉ W := by
  classical
  by_cases hex : ∃ u₀ ∈ ocube d c.rad, c.faceChartMap ε Z u₀ ∈ W
  · left
    obtain ⟨u₀, hu₀, hw₀⟩ := hex
    let Q : (Fin d → ℝ) → (Fin d → ℝ) := fun u ↦ orthantSq ε (faceMask Z u)
    have hQc : Continuous Q := by
      refine continuous_iff_continuousAt.mpr fun u ↦ ?_
      exact ((analyticOnNhd_orthantSq ε _ (mem_univ _)).comp
        (analyticOnNhd_faceMask Z u (mem_univ u))).continuousAt
    have himg : Q '' ocube d c.rad ⊆ c.O := by
      rintro _ ⟨u, hu, rfl⟩
      exact c.faceSq_mem_O ε Z (c.face_ocube_subset_cube hu)
    have hconn : IsPreconnected (Q '' ocube d c.rad) :=
      (convex_pi fun _ _ ↦ convex_Ioo _ _).isPreconnected.image Q hQc.continuousOn
    intro u hu
    refine (hWH _ (hU u hu)).mpr fun i ↦ ?_
    by_cases hvan : ∃ j ∈ Z, 0 < c.kH i j
    · obtain ⟨j, hjZ, hj⟩ := hvan
      have hp : (∏ l, faceMask Z u l ^ (2 * c.kH i l)) = 0 := by
        refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
        simp [faceMask, hjZ, show 2 * c.kH i j ≠ 0 by omega]
      change 0 ≤ H i (c.chartMap ε (faceMask Z u))
      rw [c.H_chartMap i ε (c.faceMask_mem_obox (c.face_ocube_subset_cube hu)), hp]
      simp
    · have hZ : ∀ j ∈ Z, c.kH i j = 0 := by
        intro j hj
        by_contra hk
        exact hvan ⟨j, hj, Nat.pos_of_ne_zero hk⟩
      have hZ2 : ∀ j ∈ Z, 2 * c.kH i j = 0 := fun j hj ↦ by simp only [hZ j hj, mul_zero]
      have hformula : ∀ v ∈ cube d c.rad,
          H i (c.faceChartMap ε Z v) =
            (c.cH i (Q v) * ∏ j, orthantSign ε j ^ c.kH i j) *
              ∏ j, v j ^ (2 * c.kH i j) := by
        intro v hv
        change H i (c.chartMap ε (faceMask Z v)) = _
        rw [c.H_chartMap i ε (c.faceMask_mem_obox hv), prod_pow_faceMask Z _ hZ2]
      have hne : ∀ v ∈ Q '' ocube d c.rad,
          c.cH i v * ∏ j, orthantSign ε j ^ c.kH i j ≠ 0 := fun v hv ↦
        mul_ne_zero (c.cH_ne i v (himg hv))
          (Finset.prod_ne_zero_iff.mpr fun j _ ↦ pow_ne_zero _ (orthantSign_ne_zero ε j))
      have hct : ContinuousOn (fun v ↦ c.cH i v * ∏ j, orthantSign ε j ^ c.kH i j)
          (Q '' ocube d c.rad) :=
        ((c.cH_analytic i).continuousOn.mono himg).mul continuousOn_const
      have hpos₀ : 0 < c.cH i (Q u₀) * ∏ j, orthantSign ε j ^ c.kH i j := by
        have hh := (hWH _ (hU u₀ hu₀)).mp hw₀ i
        rw [hformula u₀ (c.face_ocube_subset_cube hu₀)] at hh
        exact lt_of_le_of_ne
          (nonneg_of_mul_nonneg_left hh (c.face_prod_pow_pos hu₀ _))
          (hne _ (mem_image_of_mem Q hu₀)).symm
      rcases IsPreconnected.pos_or_neg_of_ne_zero hconn hct hne with hpos | hneg
      · rw [hformula u (c.face_ocube_subset_cube hu)]
        exact (mul_pos (hpos _ (mem_image_of_mem Q hu)) (c.face_prod_pow_pos hu _)).le
      · exact absurd hpos₀ (not_lt.mpr (hneg _ (mem_image_of_mem Q hu₀)).le)
  · right
    push Not at hex
    exact hex

/-- Closed faces remain feasible by continuity, even when W has empty interior
along the face. -/
theorem mapsTo_of_isGoodFace
    (hg : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g) {W : Set (Fin d → ℝ)} (hW : IsClosed W)
    {ε : Fin d → Bool} {Z : Finset (Fin d)} (hgood : c.IsGoodFace W ε Z) :
    MapsTo (c.faceChartMap ε Z) (cube d c.rad) W := by
  intro u hu
  have hcl : closure (ocube d c.rad) = cube d c.rad := by
    rw [ocube, cube_eq_pi]
    rw [closure_pi_set]
    exact Set.pi_congr rfl fun _ _ ↦ closure_Ioo c.rad_pos.ne
  have huc : u ∈ closure (ocube d c.rad) := by rwa [hcl]
  have hct : ContinuousWithinAt (c.faceChartMap ε Z) (ocube d c.rad) u :=
    (c.analyticOnNhd_faceChartMap hg ε Z u hu).continuousAt.continuousWithinAt
  rw [← hW.closure_eq]
  exact closure_mono (image_subset_iff.mpr hgood) (hct.mem_closure_image huc)

/-- A face that does not kill K retains the same active exponent q. -/
theorem Kf_faceChartMap_of_isGoodFace {W : Set (Fin d → ℝ)}
    (hK : ∀ w ∈ W, 0 ≤ Kf w) {ε : Fin d → Bool} {Z : Finset (Fin d)}
    (hZ : ∀ j ∈ Z, c.q j = 0) (hgood : c.IsGoodFace W ε Z)
    {u : Fin d → ℝ} (hu : u ∈ cube d c.rad) :
    Kf (c.faceChartMap ε Z u) = ∏ j, u j ^ (2 * c.q j) := by
  have hZ2 : ∀ j ∈ Z, 2 * c.q j = 0 := fun j hj ↦ by simp only [hZ j hj, mul_zero]
  have hformula : ∀ v ∈ cube d c.rad,
      Kf (c.faceChartMap ε Z v) =
        (c.S₀ * ∏ j, orthantSign ε j ^ c.q j) * ∏ j, v j ^ (2 * c.q j) := by
    intro v hv
    change Kf (c.chartMap ε (faceMask Z v)) = _
    rw [c.Kf_chartMap ε (c.faceMask_mem_obox hv), prod_pow_faceMask Z _ hZ2]
  have habs : |c.S₀ * ∏ j, orthantSign ε j ^ c.q j| = 1 := by
    have hS : |c.S₀| = 1 := by rcases c.S₀_sign with h | h <;> rw [h] <;> norm_num
    rw [abs_mul, Finset.abs_prod, hS, one_mul]
    exact Finset.prod_eq_one fun j _ ↦ by rw [abs_pow, abs_orthantSign, one_pow]
  have hhalf : (fun _ ↦ c.rad / 2 : Fin d → ℝ) ∈ ocube d c.rad :=
    fun _ _ ↦ ⟨half_pos c.rad_pos, half_lt_self c.rad_pos⟩
  have hh := hK _ (hgood _ hhalf)
  rw [hformula _ (c.face_ocube_subset_cube hhalf)] at hh
  have hsign : 0 ≤ c.S₀ * ∏ j, orthantSign ε j ^ c.q j :=
    nonneg_of_mul_nonneg_left hh (c.face_prod_pow_pos hhalf _)
  have hone : c.S₀ * ∏ j, orthantSign ε j ^ c.q j = 1 := by
    rcases (abs_eq zero_le_one).mp habs with h | h
    · exact h
    · linarith
  rw [hformula u hu, hone, one_mul]

/-- Positive-K feasible points in a smaller full coordinate box determine a good
face. Zero-only faces are intentionally excluded by hKpos. -/
theorem exists_goodFace_of_coordinate {W U : Set (Fin d → ℝ)}
    (hWH : ∀ w ∈ U, (w ∈ W ↔ ∀ i, 0 ≤ H i w))
    (hU : ∀ ε Z, ∀ u ∈ ocube d c.rad, c.faceChartMap ε Z u ∈ U)
    {a : ℝ} (ha : 0 < a) (hab : a < c.b) {v : Fin d → ℝ}
    (hv : v ∈ obox d a) (hw : c.Γ v ∈ W) (hKpos : 0 < Kf (c.Γ v)) :
    ∃ (ε : Fin d → Bool) (Z : Finset (Fin d)) (u : Fin d → ℝ),
      u ∈ cube d (Real.sqrt a) ∧ (∀ j ∈ Z, c.q j = 0) ∧
      c.IsGoodFace W ε Z ∧ c.faceChartMap ε Z u = c.Γ v := by
  obtain ⟨ε, Z, u, hu, hZiff, hsquare⟩ := exists_signed_face_coordinates ha hv
  have hrad : Real.sqrt a < c.rad := Real.sqrt_lt_sqrt ha.le hab
  have hu' : u ∈ ocube d c.rad :=
    Set.pi_mono (fun _ _ ↦ Ioo_subset_Ioo le_rfl hrad.le) hu
  have huc : u ∈ cube d c.rad := c.face_ocube_subset_cube hu'
  have hmap : c.faceChartMap ε Z u = c.Γ v := by
    rw [c.faceChartMap_eq ε Z huc, hsquare]
  have hgood : c.IsGoodFace W ε Z :=
    (c.isGoodFace_or_disjoint hWH ε Z (hU ε Z)).resolve_right fun hdisj ↦
      hdisj u hu' (hmap.symm ▸ hw)
  have hvO : v ∈ c.O := c.box_subset <| (box_eq_pi _ _).ge
    (Set.pi_mono (fun _ _ ↦ Ioo_subset_Icc_self.trans
      (Icc_subset_Icc (neg_le_neg hab.le) hab.le)) hv)
  have hZ : ∀ j ∈ Z, c.q j = 0 := by
    intro j hj
    by_contra hq
    have hzero : (∏ l, v l ^ c.q l) = 0 := by
      refine Finset.prod_eq_zero (Finset.mem_univ j) ?_
      rw [(hZiff j).mp hj, zero_pow hq]
    have hKzero : Kf (c.Γ v) = 0 := by
      change Kf (g (c.e.symm v)) = 0
      rw [c.K_eq v hvO, hzero, mul_zero]
    exact hKpos.ne' hKzero
  exact ⟨ε, Z, u, (cube_eq_pi _ _).ge (Set.pi_mono (fun _ _ ↦ Ioo_subset_Icc_self) hu), hZ, hgood,
    hmap⟩

end MonomialChart
end LocalFaces

namespace AtlasData

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (A : AtlasData K φ W)

/-- All feasible signed coordinate faces that retain the active K monomial. -/
@[expose] def FaceIndex : Type :=
  Σ σ : A.RC.ι, Σ i : (A.C σ).I,
    {p : (Fin d → Bool) × Finset (Fin d) //
      (∀ j ∈ p.2, ((A.C σ).ch i).q j = 0) ∧ ((A.C σ).ch i).IsGoodFace W p.1 p.2}

noncomputable instance : Fintype A.FaceIndex := by
  classical
  unfold FaceIndex
  infer_instance

/-- The side length $\sqrt{a_i}$ of the cube of the face chart `α`, the same as for the orthant
charts of the chart `i` of the cover that the face lies in
(`SingularLearningTheory.AtlasData.rad`). -/
@[expose] noncomputable def faceRad (α : A.FaceIndex) : ℝ := (A.C α.1).rad α.2.1

/-- The exponent of the face chart `α`: the exponent $q$ of the monomial
$K \circ g \circ e^{-1} = \pm v^q$ of its chart, so that $K(g_\alpha(u)) = u^{2q}$ on the cube
(`SingularLearningTheory.AtlasData.K_faceG`). -/
@[expose] def faceK (α : A.FaceIndex) : Fin d → ℕ := ((A.C α.1).ch α.2.1).q

/-- The chart map of the face chart `α`: the chart map of its orthant with the coordinates of its
face set to zero (`SingularLearningTheory.MonomialChart.faceChartMap`). It maps the cube into `W`
(`SingularLearningTheory.AtlasData.faceG_mapsTo`). -/
@[expose] noncomputable def faceG (α : A.FaceIndex) : (Fin d → ℝ) → (Fin d → ℝ) :=
  ((A.C α.1).ch α.2.1).faceChartMap α.2.2.1.1 α.2.2.1.2

theorem faceRad_pos (α : A.FaceIndex) : 0 < A.faceRad α := (A.C α.1).rad_pos α.2.1

theorem faceK_active (α : A.FaceIndex) : ∃ j, 0 < A.faceK α j :=
  ((A.C α.1).ch α.2.1).q_ne

theorem faceG_analytic (α : A.FaceIndex) :
    AnalyticOnNhd ℝ (A.faceG α) (cube d (A.faceRad α)) :=
  (((A.C α.1).ch α.2.1).analyticOnNhd_faceChartMap (A.RC.resolution α.1).analytic_π
    α.2.2.1.1 α.2.2.1.2).mono ((A.C α.1).cube_subset α.2.1)

theorem faceG_measurable (α : A.FaceIndex) : Measurable (A.faceG α) :=
  ((A.C α.1).ch α.2.1).measurable_faceChartMap (A.RC.resolution α.1).analytic_π _ _

theorem faceG_mapsTo (α : A.FaceIndex) : MapsTo (A.faceG α) (cube d (A.faceRad α)) W :=
  (((A.C α.1).ch α.2.1).mapsTo_of_isGoodFace (A.RC.resolution α.1).analytic_π
    A.W_compact.isClosed α.2.2.2.2).mono_left ((A.C α.1).cube_subset α.2.1)

theorem K_faceG (α : A.FaceIndex) {u : Fin d → ℝ} (hu : u ∈ cube d (A.faceRad α)) :
    K (A.faceG α u) = ∏ j, u j ^ (2 * A.faceK α j) :=
  ((A.C α.1).ch α.2.1).Kf_faceChartMap_of_isGoodFace A.K_nonneg
    α.2.2.2.1 α.2.2.2.2 ((A.C α.1).cube_subset α.2.1 hu)

/-- Finite face charts cover all positive near-zero energies, regardless of
whether the feasible stratum carries ambient volume. -/
theorem face_cover_pos {w : Fin d → ℝ} (hw : w ∈ W) (hKpos : 0 < K w) (hKw : K w < A.δ) :
    ∃ α : A.FaceIndex, ∃ u : cube d (A.faceRad α), A.faceG α u = w := by
  obtain ⟨σ, i, v, hv, hΓv⟩ := A.exists_monomial_coordinate_of_lt hw hKw
  have hU : ∀ ε Z, ∀ u ∈ ocube d ((A.C σ).ch i).rad,
      ((A.C σ).ch i).faceChartMap ε Z u ∈ A.U := by
    intro ε Z u _
    obtain ⟨P, hP⟩ := ((A.C σ).ch i).faceChartMap_mem_range ε Z u
    exact A.RC.U_subset σ (hP ▸ (A.RC.resolution σ).mem_U P)
  obtain ⟨ε, Z, u, hu, hZ, hgood, hmap⟩ :=
    ((A.C σ).ch i).exists_goodFace_of_coordinate A.domain_eq hU
      ((A.C σ).a_pos i) ((A.C σ).a_lt i) hv (hΓv.symm ▸ hw) (hΓv.symm ▸ hKpos)
  let α : A.FaceIndex := ⟨σ, i, ⟨(ε, Z), hZ, hgood⟩⟩
  exact ⟨α, ⟨u, hu⟩, hmap.trans hΓv⟩

/-- The auxiliary optimizer atlas contains the genuine prior atlas as a left
summand and every feasible active coordinate face as a right summand. Its zero
prior is bookkeeping only; singularity invariants must come from the prior atlas. -/
@[expose] noncomputable def optimizerAtlas [Nonempty A.ι] : ResolutionAtlas K (fun _ ↦ 0) W :=
  ResolutionAtlas.optimizerZeroPriorAtlas
    (ι := A.ι ⊕ A.FaceIndex)
    (Sum.elim A.rad A.faceRad)
    (fun α ↦ by cases α with
      | inl α => exact (A.C α.1).rad_pos α.2.1
      | inr α => exact A.faceRad_pos α)
    (Sum.elim A.expK A.faceK)
    (fun α ↦ by cases α with
      | inl α => exact ((A.C α.1).ch α.2.1).q_ne
      | inr α => exact A.faceK_active α)
    (Sum.elim A.chartMap A.faceG)
    (fun α ↦ by cases α with
      | inl α => exact A.analyticOnNhd_chartMap α
      | inr α => exact A.faceG_analytic α)
    (fun α ↦ by cases α with
      | inl α => exact A.measurable_chartMap α
      | inr α => exact A.faceG_measurable α)
    (fun α ↦ by cases α with
      | inl α => exact A.chartMap_mapsTo α
      | inr α => exact A.faceG_mapsTo α)
    (fun α ↦ by cases α with
      | inl α => exact fun _ hu ↦ A.K_chartMap α hu
      | inr α => exact fun _ hu ↦ A.K_faceG α hu)

@[simp] theorem optimizerAtlas_b_inl [Nonempty A.ι] (α : A.ι) :
    A.optimizerAtlas.b (Sum.inl α) = A.toResolutionAtlas.b α := rfl

@[simp] theorem optimizerAtlas_k_inl [Nonempty A.ι] (α : A.ι) :
    A.optimizerAtlas.k (Sum.inl α) = A.toResolutionAtlas.k α := rfl

@[simp] theorem optimizerAtlas_g_inl [Nonempty A.ι] (α : A.ι) :
    A.optimizerAtlas.g (Sum.inl α) = A.toResolutionAtlas.g α := rfl

theorem optimizerAtlas_cover_pos [Nonempty A.ι] :
    ∃ δ > 0, ∀ w ∈ W, 0 < K w → K w < δ →
      ∃ α, ∃ u : cube d (A.optimizerAtlas.b α), A.optimizerAtlas.g α u = w := by
  refine ⟨A.δ, A.δ_pos, fun w hw hKpos hKw ↦ ?_⟩
  obtain ⟨α, u, hmap⟩ := A.face_cover_pos hw hKpos hKw
  exact ⟨Sum.inr α, u, hmap⟩

end AtlasData
end SingularLearningTheory
