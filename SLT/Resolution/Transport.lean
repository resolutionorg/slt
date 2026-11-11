/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Chart.Map
public import SLT.Resolution.InnerPartition
public import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The transport identity of one resolution

[Hit26, Equation (3.3.5)] for one resolution `(V, M, g)`:
the integral over `W` against `ρO φ dw`, for an outer weight `ρO` supported in `Bcl`, equals
the sum over the charts `i` of the chart cover and the good orthants `ε` of the integrals over
the cubes `[0, √a_i]^d` against `u^{h_α} φ̃_α(u) du`, with `h_α = 2(p + r) + 1` and the chart
weight `φ̃_α = 2^d |b_J| (a_φ ε^r) (φ₁ ∘ g_α) (ρO ∘ g_α) (ρ_i ∘ e.symm ∘ (ε ⊙ ·²))`. The proof
changes variables chart by chart (`lintegral_image_orthantSq`), discarding the null set of the
coordinate hyperplanes' images; off it every point of `W ∩ Bcl` has a unique preimage in the
union of the small boxes, where the inner partition sums to `1`, and the bad orthants miss `W`.

| Thesis | Lean |
| --- | --- |
| [Hit26, Equation (3.3.5)], one resolution | |
| | `ChartCover.lintegral_transport` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff ENNReal

variable {d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {Kf φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ} {g : M → (Fin d → ℝ)}
  {T : Set (Fin d → ℝ)}

namespace ChartCover

variable (C : ChartCover Kf φ₂ H g T)

/-- The radius `√a_i` of the atlas cube of chart `i` ([Hit26]'s `b`). -/
@[expose] noncomputable def rad (i : C.I) : ℝ := Real.sqrt (C.a i)

theorem rad_pos (i : C.I) : 0 < C.rad i := Real.sqrt_pos.mpr (C.a_pos i)

theorem rad_lt (i : C.I) : C.rad i < (C.ch i).rad :=
  Real.sqrt_lt_sqrt (C.a_pos i).le (C.a_lt i)

theorem cube_subset (i : C.I) : cube d (C.rad i) ⊆ cube d (C.ch i).rad :=
  Icc_subset_Icc le_rfl fun _ ↦ (C.rad_lt i).le

theorem ocube_subset (i : C.I) : ocube d (C.rad i) ⊆ ocube d (C.ch i).rad :=
  Set.pi_mono fun _ _ ↦ Ioo_subset_Ioo le_rfl (C.rad_lt i).le

/-- The chart map of the atlas: chart `i`, orthant `ε`. -/
@[expose] noncomputable def gα (i : C.I) (ε : Fin d → Bool) : (Fin d → ℝ) → (Fin d → ℝ) :=
  (C.ch i).chartMap ε

/-- The exponent `k_α = q` of `K ∘ g_α = u^{2k_α}`. -/
@[expose] def expK (i : C.I) (j : Fin d) : ℕ := (C.ch i).q j

/-- The exponent `h_α = 2(p_j + r_j) + 1` of the weight (Jacobian, prior, and the substitution
`v = u²`). -/
@[expose] def expH (i : C.I) (j : Fin d) : ℕ := 2 * ((C.ch i).p j + (C.ch i).r j) + 1

/-- The chart weight `φ̃_α`. -/
@[expose] noncomputable def weight {Bcl : Set (Fin d → ℝ)} (ρ : InnerPartition C Bcl)
    (ρO φ₁ : (Fin d → ℝ) → ℝ) (i : C.I) (ε : Fin d → Bool) (u : Fin d → ℝ) : ℝ :=
  2 ^ d * |(C.ch i).bJ (orthantSq ε u)| *
    ((C.ch i).aφ (orthantSq ε u) * ∏ j, orthantSign ε j ^ (C.ch i).r j) *
    φ₁ (C.gα i ε u) * ρO (C.gα i ε u) * ρ.ρ i ((C.ch i).e.symm (orthantSq ε u))

open Classical in
/-- The good orthants of chart `i`. -/
@[expose] noncomputable def goodOrthants (W : Set (Fin d → ℝ)) (i : C.I) : Finset (Fin d → Bool) :=
  Finset.univ.filter fun ε ↦ (C.ch i).IsGood W ε

/-- The null set of parameter space to be discarded: the images of the coordinate hyperplanes
of every chart box. -/
@[expose] def Zset : Set (Fin d → ℝ) :=
  ⋃ i, (C.ch i).Γ '' {v | v ∈ obox d (C.ch i).b' ∧ ∃ j, v j = 0}

theorem volume_Zset {F : (Fin d → ℝ) → ℝ} {R : Resolution F} (C : ChartCover Kf φ₂ H R.π T) :
    volume C.Zset = 0 := by
  refine measure_iUnion_null fun i ↦ ?_
  have hsub : {v : Fin d → ℝ | v ∈ obox d (C.ch i).b' ∧ ∃ j, v j = 0} ⊆ (C.ch i).O :=
    fun v hv ↦ (C.ch i).box_b'_subset
      ((box_eq_pi _ _).ge (Set.pi_mono (fun _ _ ↦ Ioo_subset_Icc_self) hv.1))
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
    (((C.ch i).Γ_analyticOnNhd R.analytic_π).differentiableOn.mono hsub) ?_
  refine measure_mono_null (fun v hv ↦ mem_iUnion.mpr hv.2)
    (measure_iUnion_null (s := fun j ↦ {v : Fin d → ℝ | v j = 0}) fun j ↦ ?_)
  rw [volume_pi]
  exact Measure.pi_hyperplane (fun _ ↦ volume) j 0

/-- A point of the union of the small boxes lying over the zero set of `F` lies over `Zset`. -/
theorem mem_Zset_of_F_eq_zero {F : (Fin d → ℝ) → ℝ} {R : Resolution F}
    (C : ChartCover Kf φ₂ H R.π T)
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) {P : R.M}
    (hP : P ∈ C.smallUnion) (hFP : F (R.π P) = 0) : R.π P ∈ C.Zset := by
  have hP' : P ∈ ⋃ i, (C.ch i).e.symm '' obox d (C.a i) := hP
  obtain ⟨i, v, hv, rfl⟩ := mem_iUnion.mp hP'
  have hab' : C.a i ≤ (C.ch i).b' := ((C.a_lt i).trans (C.ch i).b_lt_b').le
  have hvb' : v ∈ obox d (C.ch i).b' :=
    Set.pi_mono (fun _ _ ↦ Ioo_subset_Ioo (neg_le_neg hab') hab') hv
  have hvO : v ∈ (C.ch i).O :=
    (C.ch i).box_b'_subset ((box_eq_pi _ _).ge (Set.pi_mono (fun _ _ ↦ Ioo_subset_Icc_self) hvb'))
  have hzero : ∃ j, v j = 0 := by
    by_contra h
    push Not at h
    exact (C.ch i).F_Γ_ne_zero R.mem_U hF hvO h hFP
  unfold Zset
  exact mem_iUnion.mpr ⟨i, v, ⟨hvb', hzero⟩, rfl⟩

/-- Change of variables on the open positive cube of one chart and orthant. -/
theorem lintegral_image_gα {F : (Fin d → ℝ) → ℝ} {R : Resolution F} (C : ChartCover Kf φ₂ H R.π T)
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) (i : C.I)
    (ε : Fin d → Bool) (G : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ w in C.gα i ε '' ocube d (C.rad i), G w
      = ∫⁻ u in cube d (C.rad i), G (C.gα i ε u) * ENNReal.ofReal
          (|(C.ch i).bJ (orthantSq ε u)| * (∏ j, u j ^ (2 * (C.ch i).p j)) * ∏ j, 2 * u j) := by
  have hcube : cube d (C.rad i) ⊆ obox d (C.ch i).rad' :=
    (C.cube_subset i).trans (C.ch i).cube_subset_obox
  have hsub : ocube d (C.rad i) ⊆ obox d (C.ch i).rad' := fun u hu ↦
    hcube ((cube_eq_pi _ _).ge (Set.pi_mono (fun _ _ ↦ Ioo_subset_Icc_self) hu))
  have himg : C.gα i ε '' ocube d (C.rad i) = ((C.ch i).Γ ∘ orthantSq ε) '' ocube d (C.rad i) :=
    Set.image_congr fun u hu ↦ (C.ch i).chartMap_eq ε (hsub hu)
  have hmemO : ∀ v ∈ orthantSq ε '' ocube d (C.rad i), v ∈ (C.ch i).O ∧ ∀ j, v j ≠ 0 := by
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨(C.ch i).orthantSq_mem_O ε (hsub hu), fun j ↦ ?_⟩
    exact mul_ne_zero (orthantSign_ne_zero ε j) (pow_ne_zero _ (hu j (mem_univ j)).1.ne')
  have hΓ : ∀ v ∈ orthantSq ε '' ocube d (C.rad i),
      HasFDerivAt (C.ch i).Γ (fderiv ℝ (C.ch i).Γ v) v := fun v hv ↦
    ((C.ch i).Γ_analyticOnNhd R.analytic_π v (hmemO v hv).1).differentiableAt.hasFDerivAt
  have hinj : InjOn (C.ch i).Γ (orthantSq ε '' ocube d (C.rad i)) :=
    ((C.ch i).Γ_injOn R.mem_U R.injOn hF).mono fun v hv ↦ hmemO v hv
  rw [himg, lintegral_image_orthantSq hΓ hinj G, restrict_ocube_eq]
  refine setLIntegral_congr_fun measurableSet_Icc fun u hu ↦ ?_
  have hvO : orthantSq ε u ∈ (C.ch i).O := (C.ch i).orthantSq_mem_O ε (hcube hu)
  have hG : (C.ch i).Γ (orthantSq ε u) = C.gα i ε u := ((C.ch i).chartMap_eq ε (hcube hu)).symm
  have hdet : (fderiv ℝ (C.ch i).Γ (orthantSq ε u)).det
      = (C.ch i).bJ (orthantSq ε u) * ∏ j, orthantSq ε u j ^ (C.ch i).p j :=
    (C.ch i).det_eq _ hvO
  have habs : |∏ j, orthantSq ε u j ^ (C.ch i).p j| = ∏ j, u j ^ (2 * (C.ch i).p j) := by
    rw [Finset.abs_prod]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [orthantSq, abs_pow, abs_mul, abs_orthantSign, one_mul, abs_pow, sq_abs, ← pow_mul]
  rw [hG, hdet, abs_mul, habs, mul_comm]

/-- The density of a good chart: Jacobian × prior × inner weight is `u^{h_α} φ̃_α(u)`. -/
theorem density_eq {F : (Fin d → ℝ) → ℝ} {R : Resolution F} (C : ChartCover Kf φ₂ H R.π T)
    {W Bcl : Set (Fin d → ℝ)}
    {φ φ₁ ρO : (Fin d → ℝ) → ℝ}
    (hφ₂W : ∀ w ∈ W, 0 ≤ φ₂ w) (hφ : ∀ w ∈ W, φ w = φ₁ w * φ₂ w)
    (hφ₁ : ∀ w ∈ W, 0 ≤ φ₁ w) (hρOnn : ∀ w, 0 ≤ ρO w) (ρ : InnerPartition C Bcl) {i : C.I}
    {ε : Fin d → Bool} (hε : (C.ch i).IsGood W ε) {u : Fin d → ℝ} (hu : u ∈ cube d (C.rad i))
    (hW : IsClosed W) :
    ENNReal.ofReal (|(C.ch i).bJ (orthantSq ε u)| * (∏ j, u j ^ (2 * (C.ch i).p j)) *
        ∏ j, 2 * u j) * ENNReal.ofReal (ρO (C.gα i ε u) * φ (C.gα i ε u)) *
        ENNReal.ofReal (ρ.ρ i ((C.ch i).e.symm (orthantSq ε u)))
      = ENNReal.ofReal ((∏ j, u j ^ (C.expH i j : ℝ)) * C.weight ρ ρO φ₁ i ε u) := by
  have hu' : u ∈ cube d (C.ch i).rad := C.cube_subset i hu
  have hW' : C.gα i ε u ∈ W := (C.ch i).mapsTo_of_isGood R.analytic_π hW hε hu'
  have hu0 : ∀ j, 0 ≤ u j := fun j ↦ hu.1 j
  have hφ₂ : φ₂ (C.gα i ε u) = (C.ch i).aφ (orthantSq ε u) *
      (∏ j, orthantSign ε j ^ (C.ch i).r j) * ∏ j, u j ^ (2 * (C.ch i).r j) :=
    (C.ch i).φ₂_chartMap ε ((C.ch i).cube_subset_obox hu')
  have hpos := (C.ch i).aφ_mul_sign_pos hφ₂W hε hu'
  have hA : 0 ≤ |(C.ch i).bJ (orthantSq ε u)| * (∏ j, u j ^ (2 * (C.ch i).p j)) * ∏ j, 2 * u j :=
    mul_nonneg (mul_nonneg (abs_nonneg _) (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu0 j) _))
      (Finset.prod_nonneg fun j _ ↦ mul_nonneg two_pos.le (hu0 j))
  have hB : 0 ≤ ρO (C.gα i ε u) * φ (C.gα i ε u) := by
    rw [hφ _ hW']
    exact mul_nonneg (hρOnn _) (mul_nonneg (hφ₁ _ hW') (hφ₂W _ hW'))
  have hprod : ∏ j, u j ^ ((C.expH i j : ℕ) : ℝ)
      = (∏ j, u j ^ (2 * (C.ch i).p j)) * (∏ j, u j ^ (2 * (C.ch i).r j)) * ∏ j, u j := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [Real.rpow_natCast, expH]
    ring
  have h2 : ∏ j, 2 * u j = 2 ^ d * ∏ j, u j := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← ENNReal.ofReal_mul hA, ← ENNReal.ofReal_mul (mul_nonneg hA hB), hφ _ hW', hφ₂, hprod, h2]
  unfold weight
  congr 1
  ring

/-- The open positive cube of chart `i` lies in the open cube where the chart map is the
analytic formula. -/
theorem ocube_subset_obox (i : C.I) : ocube d (C.rad i) ⊆ obox d (C.ch i).rad' := fun _ hu ↦
  (C.ch i).cube_subset_obox (C.cube_subset i (mem_cube.2 fun j ↦
    ⟨(hu j (mem_univ j)).1.le, (hu j (mem_univ j)).2.le⟩))

/-- Every point of the image of the open positive cube lies off the exceptional set. -/
theorem F_gα_ne_zero {F : (Fin d → ℝ) → ℝ} {R : Resolution F} (C : ChartCover Kf φ₂ H R.π T)
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) (i : C.I) (ε : Fin d → Bool) {u : Fin d → ℝ}
    (hu : u ∈ ocube d (C.rad i)) : F (C.gα i ε u) ≠ 0 := by
  have hu' := C.ocube_subset_obox i hu
  rw [gα, (C.ch i).chartMap_eq ε hu']
  refine (C.ch i).F_Γ_ne_zero R.mem_U hF ((C.ch i).orthantSq_mem_O ε hu') fun j ↦ ?_
  exact mul_ne_zero (orthantSign_ne_zero ε j) (pow_ne_zero _ (hu j (mem_univ j)).1.ne')

theorem measurableSet_image_ocube {F : (Fin d → ℝ) → ℝ} {R : Resolution F}
    (C : ChartCover Kf φ₂ H R.π T)
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) (i : C.I)
    (ε : Fin d → Bool) : MeasurableSet (C.gα i ε '' ocube d (C.rad i)) := by
  refine MeasurableSet.image_of_continuousOn_injOn
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo) ?_
    (((C.ch i).chartMap_injOn R.mem_U R.injOn hF ε).mono (C.ocube_subset i))
  exact ((C.ch i).chartMap_analyticOnNhd R.analytic_π ε).continuousOn.mono fun u hu ↦
    C.cube_subset i ⟨fun j ↦ (hu j (mem_univ j)).1.le, fun j ↦ (hu j (mem_univ j)).2.le⟩

/-- Images of the open positive cubes of distinct orthants are disjoint. -/
theorem disjoint_image_ocube {F : (Fin d → ℝ) → ℝ} {R : Resolution F} (C : ChartCover Kf φ₂ H R.π T)
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) (i : C.I)
    {ε ε' : Fin d → Bool} (hne : ε ≠ ε') :
    Disjoint (C.gα i ε '' ocube d (C.rad i)) (C.gα i ε' '' ocube d (C.rad i)) := by
  rw [Set.disjoint_left]
  rintro w ⟨u, hu, rfl⟩ ⟨u', hu', heq⟩
  have hu2 := C.ocube_subset_obox i hu
  have hu2' := C.ocube_subset_obox i hu'
  simp only [gα, (C.ch i).chartMap_eq ε hu2, (C.ch i).chartMap_eq ε' hu2'] at heq
  have hmem : ∀ (b : Fin d → Bool) (v : Fin d → ℝ), v ∈ ocube d (C.rad i) →
      orthantSq b v ∈ {v | v ∈ (C.ch i).O ∧ ∀ j, v j ≠ 0} := fun b v hv ↦
    ⟨(C.ch i).orthantSq_mem_O b (C.ocube_subset_obox i hv), fun j ↦
      mul_ne_zero (orthantSign_ne_zero b j) (pow_ne_zero _ (hv j (mem_univ j)).1.ne')⟩
  have hsq := (C.ch i).Γ_injOn R.mem_U R.injOn hF (hmem ε' u' hu') (hmem ε u hu) heq
  apply hne
  funext j
  have hj := congrFun hsq j
  simp only [orthantSq] at hj
  have hpos : 0 < u j ^ 2 := pow_pos (hu j (mem_univ j)).1 2
  have hpos' : 0 < u' j ^ 2 := pow_pos (hu' j (mem_univ j)).1 2
  by_contra hb
  have hsign : orthantSign ε j = -orthantSign ε' j := by
    cases hε : ε j <;> cases hε' : ε' j <;> simp_all [orthantSign]
  rw [hsign] at hj
  have h0 : orthantSign ε' j * (u j ^ 2 + u' j ^ 2) = 0 := by linarith
  rcases mul_eq_zero.mp h0 with h | h
  · exact orthantSign_ne_zero ε' j h
  · linarith

/-- A point `Γ v` with `v` in the open box `(-a_i, a_i)^d` off the coordinate hyperplanes lies in
the image of some open positive cube. -/
theorem exists_orthant_of_mem {i : C.I} {v : Fin d → ℝ} (hv : v ∈ obox d (C.a i))
    (hne : ∀ j, v j ≠ 0) :
    ∃ ε : Fin d → Bool, ∃ u ∈ ocube d (C.rad i), (C.ch i).Γ v = C.gα i ε u := by
  refine ⟨fun j ↦ decide (0 < v j), fun j ↦ Real.sqrt |v j|, fun j _ ↦ ?_, ?_⟩
  · refine ⟨Real.sqrt_pos.mpr (abs_pos.mpr (hne j)), ?_⟩
    rw [rad]
    exact Real.sqrt_lt_sqrt (abs_nonneg _) (abs_lt.mpr (hv j (mem_univ j)))
  · have hu : (fun j ↦ Real.sqrt |v j|) ∈ ocube d (C.rad i) := fun j _ ↦
      ⟨Real.sqrt_pos.mpr (abs_pos.mpr (hne j)),
        by rw [rad]; exact Real.sqrt_lt_sqrt (abs_nonneg _) (abs_lt.mpr (hv j (mem_univ j)))⟩
    rw [gα, (C.ch i).chartMap_eq _ (C.ocube_subset_obox i hu)]
    congr 1
    funext j
    simp only [orthantSq, orthantSign, Real.sq_sqrt (abs_nonneg _)]
    split_ifs with h
    · rw [abs_of_pos (of_decide_eq_true h)]; ring
    · have : v j < 0 := lt_of_le_of_ne (not_lt.mp (of_decide_eq_false (Bool.eq_false_iff.mpr h)))
        (hne j)
      rw [abs_of_neg this]; ring

/-- [Hit26, Equation (3.3.5)] for one resolution. -/
theorem lintegral_transport {F : (Fin d → ℝ) → ℝ} {R : Resolution F} (C : ChartCover Kf φ₂ H R.π T)
    {W Bcl : Set (Fin d → ℝ)} {φ φ₁ ρO : (Fin d → ℝ) → ℝ}
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) (hFc : ContinuousOn F R.U)
    (hWH : ∀ w ∈ R.U, (w ∈ W ↔ ∀ i, 0 ≤ H i w)) (hWc : IsClosed W)
    (hWm : MeasurableSet W)
    (hφ₂W : ∀ w ∈ W, 0 ≤ φ₂ w) (hφ : ∀ w ∈ W, φ w = φ₁ w * φ₂ w) (hφ₁ : ∀ w ∈ W, 0 ≤ φ₁ w)
    (hφm : Measurable φ) (hρOc : Continuous ρO) (hρOnn : ∀ w, 0 ≤ ρO w)
    (hρOsupp : ∀ w, ρO w ≠ 0 → w ∈ Bcl) (hBm : MeasurableSet Bcl) (hBV : Bcl ⊆ R.U)
    (hBO : R.π ⁻¹' Bcl ⊆ C.smallUnion)
    (ρ : InnerPartition C Bcl) (Fm : (Fin d → ℝ) → ℝ≥0∞) (hFm : Measurable Fm) :
    ∫⁻ w in W, Fm w * ENNReal.ofReal (ρO w * φ w)
      = ∑ i, ∑ ε ∈ C.goodOrthants W i, ∫⁻ u in cube d (C.rad i),
          Fm (C.gα i ε u) *
            ENNReal.ofReal ((∏ j, u j ^ (C.expH i j : ℝ)) * C.weight ρ ρO φ₁ i ε u) := by
  classical
  rcases isEmpty_or_nonempty R.M with hM | hM
  · -- no resolving manifold: `U` is empty, so are `Bcl` and the charts, and both sides vanish
    have hI : IsEmpty C.I := ⟨fun i ↦ isEmptyElim (C.P i)⟩
    have hρO : ∀ w, ρO w = 0 := fun w ↦ by
      by_contra h
      have hw : w ∈ range R.π := R.range_π.symm ▸ hBV (hρOsupp w h)
      obtain ⟨P, -⟩ := hw
      exact isEmptyElim P
    simp [hρO, Finset.univ_eq_empty]
  obtain ⟨ginv, hginv_smooth, hginv⟩ := R.exists_contMDiffOn_leftInvOn
  -- the open set `U ∩ {F ≠ 0}`, on which `ginv` is a continuous inverse of `π`
  have hVFo : IsOpen (R.U ∩ {w | F w ≠ 0}) := hFc.isOpen_inter_preimage R.isOpen_U isOpen_ne
  have hVF_eq : R.U ∩ {w | F w ≠ 0} = R.U \ {w | F w = 0} := by
    ext w; simp [Set.mem_sdiff]
  have hginv_cont : ContinuousOn ginv (R.U ∩ {w | F w ≠ 0}) := by
    rw [hVF_eq]; exact hginv_smooth.continuousOn
  have hg_ginv : ∀ w ∈ R.U ∩ {w | F w ≠ 0}, R.π (ginv w) = w := by
    intro w hw
    rw [hVF_eq, ← R.image_preimage_ne_zero] at hw
    obtain ⟨P, hP, rfl⟩ := hw
    rw [hginv P hP]
  have hginv_g : ∀ P, F (R.π P) ≠ 0 → ginv (R.π P) = P := fun P hP ↦ hginv P (by simpa using hP)
  -- the functions `ρ̂_i = ρ_i ∘ ginv` (zero off `U ∩ {F ≠ 0}`)
  obtain ⟨ρhat, hρhat_eq, hρhat_zero, hρhat_m⟩ : ∃ ρhat : C.I → (Fin d → ℝ) → ℝ,
      (∀ i, ∀ w ∈ R.U ∩ {w | F w ≠ 0}, ρhat i w = ρ.ρ i (ginv w)) ∧
        (∀ i, ∀ w ∉ R.U ∩ {w | F w ≠ 0}, ρhat i w = 0) ∧ ∀ i, Measurable (ρhat i) :=
    ⟨fun i ↦ (R.U ∩ {w | F w ≠ 0}).piecewise (fun w ↦ ρ.ρ i (ginv w)) fun _ ↦ 0,
      fun i w hw ↦ Set.piecewise_eq_of_mem _ _ _ hw,
      fun i w hw ↦ Set.piecewise_eq_of_notMem _ _ _ hw,
      fun i ↦ ((ρ.continuous i).comp_continuousOn hginv_cont).measurable_piecewise
        continuousOn_const hVFo.measurableSet⟩
  have hρhat_nn : ∀ i w, 0 ≤ ρhat i w := fun i w ↦ by
    by_cases hw : w ∈ R.U ∩ {w | F w ≠ 0}
    · rw [hρhat_eq i w hw]; exact ρ.nonneg _ _
    · rw [hρhat_zero i w hw]
  -- surjectivity onto `Bcl`, and points of `Bcl` off `Zset` lie in `U ∩ {F ≠ 0}`
  have hpre : ∀ w ∈ Bcl, ∃ P, R.π P = w := fun w hw ↦ by
    have : w ∈ range R.π := R.range_π ▸ hBV hw
    exact this
  have hZ := C.volume_Zset
  have hBcl_VF : ∀ w ∈ Bcl, w ∉ C.Zset → w ∈ R.U ∩ {w | F w ≠ 0} := by
    intro w hw hwZ
    obtain ⟨P, rfl⟩ := hpre w hw
    exact ⟨hBV hw, fun hFP ↦ hwZ (C.mem_Zset_of_F_eq_zero hF (hBO hw) hFP)⟩
  -- the `ρ̂_i` sum to `1` on `Bcl \ Zset`
  have hsum : ∀ w ∈ Bcl, w ∉ C.Zset → ∑ i, ρhat i w = 1 := by
    intro w hw hwZ
    have hwVF := hBcl_VF w hw hwZ
    obtain ⟨P, rfl⟩ := hpre w hw
    simp only [hρhat_eq _ _ hwVF, hginv_g P hwVF.2]
    exact ρ.sum_eq_one P hw
  -- where `ρ̂_i ≠ 0`, the point lies in the image of an open positive cube of chart `i`
  have hloc : ∀ i, ∀ w ∈ Bcl, w ∉ C.Zset → ρhat i w ≠ 0 →
      w ∈ ⋃ ε, C.gα i ε '' ocube d (C.rad i) := by
    intro i w hw hwZ hne
    have hwVF := hBcl_VF w hw hwZ
    rw [hρhat_eq i w hwVF] at hne
    obtain ⟨v, hv, hvP⟩ := ρ.support i _ hne
    have hw' : w = (C.ch i).Γ v := by
      rw [MonomialChart.Γ, Function.comp_apply, hvP, hg_ginv w hwVF]
    have hvb' : v ∈ obox d (C.ch i).b' := fun j _ ↦ by
      have h := hv j (mem_univ j)
      have hab : C.a i < (C.ch i).b' := (C.a_lt i).trans (C.ch i).b_lt_b'
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    have hne' : ∀ j, v j ≠ 0 := by
      intro j hj
      apply hwZ
      rw [hw']
      exact Set.mem_iUnion.mpr ⟨i, ⟨v, ⟨hvb', j, hj⟩, rfl⟩⟩
    obtain ⟨ε, u, hu, hΓ⟩ := C.exists_orthant_of_mem hv hne'
    exact Set.mem_iUnion.mpr ⟨ε, u, hu, by rw [← hΓ, hw']⟩
  -- the integrand and its vanishing off `Bcl`
  have hXm : Measurable fun w ↦ Fm w * ENNReal.ofReal (ρO w * φ w) :=
    hFm.mul (ENNReal.measurable_ofReal.comp (hρOc.measurable.mul hφm))
  have hX0 : ∀ w, w ∉ Bcl → Fm w * ENNReal.ofReal (ρO w * φ w) = 0 := fun w hw ↦ by
    have : ρO w = 0 := by
      by_contra h
      exact hw (hρOsupp w h)
    simp [this]
  have hSm : MeasurableSet (Bcl ∩ W) := hBm.inter hWm
  -- Step A: restrict to `Bcl ∩ W`
  have hA : ∫⁻ w in W, Fm w * ENNReal.ofReal (ρO w * φ w)
      = ∫⁻ w in Bcl ∩ W, Fm w * ENNReal.ofReal (ρO w * φ w) := by
    rw [← Measure.restrict_restrict hBm, ← lintegral_indicator hBm]
    refine lintegral_congr fun w ↦ ?_
    by_cases hw : w ∈ Bcl
    · rw [Set.indicator_of_mem hw]
    · rw [Set.indicator_of_notMem hw, hX0 w hw]
  -- almost every point of `Bcl ∩ W` is off `Zset`
  have hae : ∀ᵐ w ∂(volume.restrict (Bcl ∩ W)), w ∈ Bcl ∩ W ∧ w ∉ C.Zset := by
    have hZae : ∀ᵐ w ∂(volume : Measure (Fin d → ℝ)), w ∉ C.Zset := compl_mem_ae_iff.mpr hZ
    filter_upwards [ae_restrict_mem hSm, ae_restrict_of_ae hZae] with w h1 h2 using ⟨h1, h2⟩
  -- Step B: insert the partition `∑ ρ̂_i = 1`
  have hB : ∫⁻ w in Bcl ∩ W, Fm w * ENNReal.ofReal (ρO w * φ w)
      = ∫⁻ w in Bcl ∩ W, ∑ i, Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w) := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with w hw
    rw [← Finset.mul_sum, ← ENNReal.ofReal_sum_of_nonneg fun i _ ↦ hρhat_nn i w,
      hsum w hw.1.1 hw.2, ENNReal.ofReal_one, mul_one]
  -- Step C: sum out of the integral
  have hC : ∫⁻ w in Bcl ∩ W, ∑ i, Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w)
      = ∑ i, ∫⁻ w in Bcl ∩ W, Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w) :=
    lintegral_finsetSum _ fun i _ ↦ hXm.mul (ENNReal.measurable_ofReal.comp (hρhat_m i))
  -- Step D: one chart
  have hD : ∀ i, ∫⁻ w in Bcl ∩ W, Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w)
      = ∑ ε ∈ C.goodOrthants W i, ∫⁻ u in cube d (C.rad i),
          Fm (C.gα i ε u) *
            ENNReal.ofReal ((∏ j, u j ^ (C.expH i j : ℝ)) * C.weight ρ ρO φ₁ i ε u) := by
    intro i
    have hUim : MeasurableSet (⋃ ε, C.gα i ε '' ocube d (C.rad i)) :=
      MeasurableSet.iUnion fun ε ↦ C.measurableSet_image_ocube hF i ε
    -- D1: the integrand vanishes off the union of the orthant images
    have hD1 : ∫⁻ w in Bcl ∩ W, Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w)
        = ∫⁻ w in (⋃ ε, C.gα i ε '' ocube d (C.rad i)) ∩ (Bcl ∩ W),
            Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w) := by
      rw [← Measure.restrict_restrict hUim, ← lintegral_indicator hUim]
      refine lintegral_congr_ae ?_
      filter_upwards [hae] with w hw
      by_cases hwU : w ∈ ⋃ ε, C.gα i ε '' ocube d (C.rad i)
      · rw [Set.indicator_of_mem hwU]
      · rw [Set.indicator_of_notMem hwU]
        have : ρhat i w = 0 := by
          by_contra h
          exact hwU (hloc i w hw.1.1 hw.2 h)
        simp [this]
    -- D2: split over the orthants
    have hD2 : ∫⁻ w in (⋃ ε, C.gα i ε '' ocube d (C.rad i)) ∩ (Bcl ∩ W),
          Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w)
        = ∑ ε, ∫⁻ w in C.gα i ε '' ocube d (C.rad i) ∩ (Bcl ∩ W),
            Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w) := by
      rw [Set.iUnion_inter, lintegral_iUnion
        (fun ε ↦ (C.measurableSet_image_ocube hF i ε).inter hSm)
        (fun ε ε' hne ↦ (C.disjoint_image_ocube hF i hne).mono inter_subset_left
          inter_subset_left), tsum_fintype]
    -- D3: a single orthant
    have hD3 : ∀ ε, ∫⁻ w in C.gα i ε '' ocube d (C.rad i) ∩ (Bcl ∩ W),
          Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w)
        = if (C.ch i).IsGood W ε then ∫⁻ u in cube d (C.rad i), Fm (C.gα i ε u) *
            ENNReal.ofReal ((∏ j, u j ^ (C.expH i j : ℝ)) * C.weight ρ ρO φ₁ i ε u) else 0 := by
      intro ε
      split_ifs with hε
      · have himW : C.gα i ε '' ocube d (C.rad i) ⊆ W := by
          rintro _ ⟨u, hu, rfl⟩
          exact hε u (C.ocube_subset i hu)
        have hset : C.gα i ε '' ocube d (C.rad i) ∩ (Bcl ∩ W)
            = Bcl ∩ C.gα i ε '' ocube d (C.rad i) := by
          ext w
          simp only [mem_inter_iff]
          constructor
          · rintro ⟨h1, h2, -⟩; exact ⟨h2, h1⟩
          · rintro ⟨h2, h1⟩; exact ⟨h1, h2, himW h1⟩
        rw [hset, ← Measure.restrict_restrict hBm, ← lintegral_indicator hBm]
        have hind : ∀ w, Bcl.indicator
            (fun w ↦ Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w)) w
              = Fm w * ENNReal.ofReal (ρO w * φ w) * ENNReal.ofReal (ρhat i w) := by
          intro w
          by_cases hw : w ∈ Bcl
          · rw [Set.indicator_of_mem hw]
          · rw [Set.indicator_of_notMem hw, hX0 w hw, zero_mul]
        simp only [hind]
        rw [C.lintegral_image_gα hF i ε, ← restrict_ocube_eq]
        refine setLIntegral_congr_fun (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)
          fun u hu ↦ ?_
        have hu' : u ∈ cube d (C.rad i) := mem_cube.2 fun j ↦
          ⟨(hu j (mem_univ j)).1.le, (hu j (mem_univ j)).2.le⟩
        have hgu : C.gα i ε u = R.π ((C.ch i).e.symm (orthantSq ε u)) :=
          (C.ch i).chartMap_eq ε (C.ocube_subset_obox i hu)
        have hFu : F (C.gα i ε u) ≠ 0 := C.F_gα_ne_zero hF i ε hu
        have hρ : ρhat i (C.gα i ε u) = ρ.ρ i ((C.ch i).e.symm (orthantSq ε u)) := by
          have hVFu : C.gα i ε u ∈ R.U ∩ {w | F w ≠ 0} :=
            ⟨R.range_π ▸ ⟨_, hgu.symm⟩, hFu⟩
          rw [hρhat_eq i _ hVFu, hgu, hginv_g _ (hgu ▸ hFu)]
        rw [hρ, ← C.density_eq hφ₂W hφ hφ₁ hρOnn ρ hε hu' hWc]
        ring
      · have hdisj := ((C.ch i).isGood_or_disjoint hWH ε fun u hu ↦
          R.range_π ▸ ⟨_, ((C.ch i).chartMap_eq ε ((C.ch i).cube_subset_obox (mem_cube.2 fun j ↦
            ⟨(hu j (mem_univ j)).1.le, (hu j (mem_univ j)).2.le⟩))).symm⟩).resolve_left hε
        have hempty : C.gα i ε '' ocube d (C.rad i) ∩ (Bcl ∩ W) = ∅ := by
          ext w
          simp only [mem_inter_iff, mem_empty_iff_false, iff_false]
          rintro ⟨⟨u, hu, rfl⟩, -, hwW⟩
          exact hdisj u (C.ocube_subset i hu) hwW
        rw [hempty, Measure.restrict_empty, lintegral_zero_measure]
    rw [hD1, hD2, goodOrthants, Finset.sum_filter]
    exact Finset.sum_congr rfl fun ε _ ↦ hD3 ε
  rw [hA, hB, hC]
  exact Finset.sum_congr rfl fun i _ ↦ hD i

end ChartCover

end SingularLearningTheory
