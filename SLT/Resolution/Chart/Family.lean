/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Atlas
public import SLT.StandardForm.FundamentalConditionI
public import SLT.Resolution.MonomialChart
public import SLT.Resolution.Orthant
public import SLT.Resolution.Outer
import SLT.Resolution.Factorisation
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Algebra.Ring.IsFormallyReal
public import SLT.Resolution.Components
import Mathlib.Order.CompletePartialOrder
public import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Ring.Star
import Std.Tactic.BVDecide.Normalize.Prop
import Std.Tactic.BVDecide.Normalize.BitVec
public import SLT.Resolution.Defs

/-!
# Chart families of a resolution and their orthant pieces

The orthant form of [Wat09, Theorem 6.5] read off an `SLTResolution`: a `ChartFamily` is a finite
family of charts of the resolution whose open cubes cover the part `W̃ ∩ {K ≤ δ}` of the resolved
parameter set `W̃ = closure (π⁻¹ (interior W))`, and its *pieces* are the pairs of a chart and an
admissible orthant, each reflected onto `[0, r]^d`. The definitions are those of
`SLTChallenge/Resolution.lean`, restated verbatim, with the chart and resolution
invariants `rlct`, `mult` and `Piece.IsEssential`.

The lemmas here are the geometry the proofs use: a piece's map is analytic on a neighbourhood of
its cube, lands in `W` when `W` is closed and has `K = u^{2k}` there; every point of `W̃` in the
open cube of a chart lies in a closed admissible orthant of it, and the centre of a chart with an
admissible orthant lies in `W̃`; finitely many charts cover a sublevel of `K` over a compact `W`
(`SLTResolution.exists_finite_cover_sublevel`, whence `SLTResolution.exists_chartFamily'`); and a
chart family has subordinate smooth partitions of unity on its sublevel, including one equal to
`1` at the centre of a chosen chart.

| Thesis | Lean |
| --- | --- |
| [Wat09, Theorem 6.5] (1), finitely many local coordinates, from a global resolution | |
| | `SLTResolution.ChartFamily`, `SLTResolution.exists_chartFamily'` |
| [Wat09, Theorem 6.5] (4), the partition of unity | `SLTResolution.ChartFamily.exists_partitionOfUnity'` |
-/

public section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

namespace SingularLearningTheory

variable {d : ℕ}

/-! ## The reflections -/

section Orthants

variable {r : ℝ} {s : Fin d → Bool} {u : Fin d → ℝ}

/-- A point of an open orthant has no zero coordinate. -/
theorem ne_zero_of_mem_openOrthant (hu : u ∈ openOrthant r s) (j : Fin d) : u j ≠ 0 := by
  intro h0
  have h := (hu j).2
  split_ifs at h <;> simp [h0] at h

end Orthants

section Reflect

variable (s : Fin d → Bool)

@[simp] theorem reflectOrthant_apply (u : Fin d → ℝ) (j : Fin d) :
    reflectOrthant s u j = if s j then u j else -u j := rfl

@[simp] theorem reflectOrthant_reflectOrthant (u : Fin d → ℝ) :
    reflectOrthant s (reflectOrthant s u) = u := by
  funext j
  by_cases h : s j <;> simp [h]

theorem reflectOrthant_involutive : Function.Involutive (reflectOrthant s) :=
  reflectOrthant_reflectOrthant s

private theorem abs_reflectOrthant_apply (u : Fin d → ℝ) (j : Fin d) :
    |reflectOrthant s u j| = |u j| := by
  by_cases h : s j <;> simp [h]

theorem reflectOrthant_zero : reflectOrthant s (0 : Fin d → ℝ) = 0 := by
  funext j
  by_cases h : s j <;> simp [h]

/-- The reflection as a continuous linear equivalence. -/
@[expose] noncomputable def reflectOrthantCLE : (Fin d → ℝ) ≃L[ℝ] (Fin d → ℝ) :=
  { toFun := reflectOrthant s
    invFun := reflectOrthant s
    map_add' := fun u v ↦ by funext j; by_cases h : s j <;> simp [h]; ring
    map_smul' := fun c u ↦ by funext j; by_cases h : s j <;> simp [h]
    left_inv := reflectOrthant_reflectOrthant s
    right_inv := reflectOrthant_reflectOrthant s
    continuous_toFun := continuous_pi fun j ↦ by
      by_cases h : s j <;> simp only [reflectOrthant_apply, h, ite_true, Bool.false_eq_true,
        ite_false] <;> fun_prop
    continuous_invFun := continuous_pi fun j ↦ by
      by_cases h : s j <;> simp only [reflectOrthant_apply, h, ite_true, Bool.false_eq_true,
        ite_false] <;> fun_prop }

private theorem continuous_reflectOrthant : Continuous (reflectOrthant s : (Fin d → ℝ) → _) :=
  (reflectOrthantCLE s).continuous

/-- The reflection preserves Lebesgue measure. -/
theorem measurePreserving_reflectOrthant :
    MeasurePreserving (reflectOrthant s : (Fin d → ℝ) → _) volume volume := by
  have := volume_preserving_pi (α' := fun _ : Fin d ↦ ℝ) (β' := fun _ : Fin d ↦ ℝ)
    (f := fun j (x : ℝ) ↦ if s j then x else -x) fun j ↦ by
      by_cases h : s j
      · simp only [h, ite_true]
        exact MeasurePreserving.id volume
      · simp only [h, Bool.false_eq_true, ite_false]
        exact Measure.measurePreserving_neg (volume : Measure ℝ)
  exact this

/-- Even powers do not see the reflection. -/
private theorem prod_reflectOrthant_pow_two_mul (u : Fin d → ℝ) (k : Fin d → ℕ) :
    ∏ j, reflectOrthant s u j ^ (2 * k j) = ∏ j, u j ^ (2 * k j) := by
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  by_cases h : s j
  · simp [h]
  · simp [h, pow_mul]

/-- The absolute value of a monomial does not see the reflection. -/
theorem abs_prod_reflectOrthant_pow (u : Fin d → ℝ) (h : Fin d → ℕ) :
    |∏ j, reflectOrthant s u j ^ h j| = |∏ j, u j ^ h j| := by
  rw [Finset.abs_prod, Finset.abs_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [abs_pow, abs_pow, abs_reflectOrthant_apply]

/-- The reflection of the cube `[0, r]^d` lies in the box `[-r, r]^d`. -/
private theorem reflectOrthant_mem_box {r : ℝ} {u : Fin d → ℝ} (hu : u ∈ cube d r) :
    reflectOrthant s u ∈ Icc (fun _ ↦ -r) (fun _ ↦ r) := by
  refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;> obtain ⟨h0, h1⟩ := mem_cube.1 hu j <;>
    by_cases h : s j <;> simp [h] <;> linarith

/-- A point of the open positive cube `(0, r]^d` reflects into the open orthant. -/
theorem reflectOrthant_mem_openOrthant {r : ℝ} {u : Fin d → ℝ}
    (hu : ∀ j, 0 < u j ∧ u j ≤ r) : reflectOrthant s u ∈ openOrthant r s := by
  intro j
  obtain ⟨h0, h1⟩ := hu j
  by_cases h : s j <;> simp [h, abs_of_pos h0, h0, h1]

/-- Every point of an open orthant is the reflection of a point of the cube `[0, r]^d`. -/
theorem reflectOrthant_mem_cube_of_mem_openOrthant {r : ℝ} {v : Fin d → ℝ}
    (hv : v ∈ openOrthant r s) : reflectOrthant s v ∈ cube d r := by
  refine mem_cube.2 fun j ↦ ?_
  obtain ⟨h1, h2⟩ := hv j
  by_cases h : s j
  · simp only [reflectOrthant_apply, h, ite_true] at h2 ⊢
    exact ⟨h2.le, (le_abs_self _).trans h1⟩
  · simp only [reflectOrthant_apply, h, Bool.false_eq_true, ite_false] at h2 ⊢
    exact ⟨h2.le, (neg_le_abs _).trans h1⟩

end Reflect

/-- Points of the cube `[0, r]^d` are limits of points with all coordinates in `(0, r]`: the
segment to the centre of the cube. -/
private theorem exists_tendsto_cube_interior {r : ℝ} (hr : 0 < r) {u : Fin d → ℝ}
    (hu : u ∈ cube d r) :
    ∃ v : ℕ → Fin d → ℝ, (∀ n j, 0 < v n j ∧ v n j ≤ r) ∧ Tendsto v atTop (𝓝 u) := by
  set t : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 2)
  refine ⟨fun n j ↦ (1 - t n) * u j + t n * (r / 2), fun n j ↦ ?_, ?_⟩
  · obtain ⟨h0, h1⟩ := mem_cube.1 hu j
    have ht : 0 < t n := by positivity
    have ht1 : t n ≤ 1 / 2 := by
      simp only [t]
      gcongr
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    constructor <;> nlinarith
  · have ht : Tendsto t atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
      refine this.congr fun n ↦ ?_
      simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one, t]
      ring_nf
    refine tendsto_pi_nhds.mpr fun j ↦ ?_
    have := (((tendsto_const_nhds (x := (1 : ℝ))).sub ht).mul (tendsto_const_nhds (x := u j))).add
      (ht.mul (tendsto_const_nhds (x := r / 2)))
    simpa using this

/-- A nonempty open subset of `ℝ^d` contains a point with no zero coordinate. -/
private theorem exists_mem_forall_ne_zero_of_isOpen {O : Set (Fin d → ℝ)} (hO : IsOpen O)
    {p : Fin d → ℝ} (hp : p ∈ O) : ∃ v ∈ O, ∀ j, v j ≠ 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO p hp
  refine ⟨fun j ↦ if p j = 0 then ε / 2 else p j, hball ?_, fun j ↦ ?_⟩
  · rw [Metric.mem_ball, dist_pi_lt_iff hε]
    intro j
    by_cases h : p j = 0
    · simp [h, abs_of_pos hε, half_lt_self hε]
    · simp [h, hε]
  · by_cases h : p j = 0
    · simp [h, hε.ne']
    · simp [h]

/-- A point with no zero coordinate in the open cube `(-r, r)^d` lies in the open orthant of its
sign pattern. -/
theorem mem_openOrthant_sign {r : ℝ} {v : Fin d → ℝ} (hv : ∀ j, |v j| ≤ r)
    (h0 : ∀ j, v j ≠ 0) : v ∈ openOrthant r (fun j ↦ decide (0 < v j)) := by
  intro j
  refine ⟨hv j, ?_⟩
  by_cases h : 0 < v j
  · simp [h]
  · have : v j < 0 := lt_of_le_of_ne (not_lt.mp h) (h0 j)
    simp [h, this]

namespace SLTChart

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {π : M → (Fin d → ℝ)} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {z : M}
  (C : SLTChart π K φ W z)

theorem isOpen_openCube : IsOpen C.openCube :=
  C.extension.isOpen_inter_preimage (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo)

theorem mem_openCube : z ∈ C.openCube :=
  ⟨C.mem_source, by
    rw [mem_preimage, C.centered]
    exact fun _ _ ↦ ⟨neg_lt_zero.mpr C.radius_pos, C.radius_pos⟩⟩

theorem symm_zero : C.extension.symm 0 = z := by
  rw [← C.centered, C.extension.left_inv C.mem_source]

theorem zero_mem_target : (0 : Fin d → ℝ) ∈ C.extension.target :=
  C.centered ▸ C.extension.map_source C.mem_source

/-- The loss vanishes at the centre of a chart. -/
theorem loss_center (C : SLTChart π K φ W z) : K (π z) = 0 := by
  obtain ⟨j, hj⟩ := C.active
  rw [← C.symm_zero, C.loss_eq 0 C.zero_mem_target]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj.ne'])

theorem openOrthant_subset_target (s : Fin d → Bool) :
    openOrthant C.radius s ⊆ C.extension.target := fun _ hu ↦
  C.box_subset ⟨fun j ↦ neg_le_of_abs_le (hu j).1, fun j ↦ le_of_abs_le (hu j).1⟩

theorem reflectOrthant_mem_target (s : Fin d → Bool) {u : Fin d → ℝ} (hu : u ∈ cube d C.radius) :
    reflectOrthant s u ∈ C.extension.target :=
  C.box_subset (reflectOrthant_mem_box s hu)

end SLTChart

namespace SLTResolution

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : SLTResolution K φ W)

theorem continuous_π : Continuous R.π := R.analytic_π.continuous

theorem isClosed_resolvedParameterSet : IsClosed R.resolvedParameterSet := isClosed_closure

/-- Over a closed `W`, the resolved parameter set lies over `W`. -/
theorem resolvedParameterSet_subset (hW : IsClosed W) :
    R.resolvedParameterSet ⊆ R.π ⁻¹' W :=
  closure_minimal (preimage_mono interior_subset) (hW.preimage R.continuous_π)

/-- The analytic map of a chart composed with the resolution. -/
theorem analyticOnNhd_comp_symm {z : R.M} (C : R.Chart z) :
    AnalyticOnNhd ℝ (R.π ∘ C.extension.symm) C.extension.target :=
  analyticOnNhd_comp_symm_of_mem_maximalAtlas R.analytic_π C.extension_mem

/-- The centre of a chart with an admissible orthant lies in the resolved parameter set. -/
theorem center_mem_resolvedParameterSet {z : R.M} (C : R.Chart z) {s : Fin d → Bool}
    (hs : C.IsAdmissible s) : z ∈ R.resolvedParameterSet := by
  obtain ⟨v, hv, hlim⟩ := exists_tendsto_cube_interior C.radius_pos
    (⟨fun j ↦ le_rfl, fun j ↦ C.radius_pos.le⟩ : (0 : Fin d → ℝ) ∈ cube d C.radius)
  have hmem : ∀ n, reflectOrthant s (v n) ∈ openOrthant C.radius s := fun n ↦
    reflectOrthant_mem_openOrthant s (hv n)
  have hlim' : Tendsto (fun n ↦ C.extension.symm (reflectOrthant s (v n))) atTop (𝓝 z) := by
    have h0 : reflectOrthant s (0 : Fin d → ℝ) = 0 := reflectOrthant_zero s
    have hr := ((continuous_reflectOrthant s).tendsto 0).comp hlim
    rw [h0] at hr
    have hc := (C.extension.continuousAt_symm C.zero_mem_target).tendsto.comp hr
    rw [C.symm_zero] at hc
    exact hc
  exact mem_closure_of_tendsto hlim' (Eventually.of_forall fun n ↦ hs _ (hmem n))

/-- A point of the resolved parameter set in the open cube of a chart lies in a closed admissible
orthant of it: it is the reflection of a point of the cube `[0, r]^d` across an admissible
orthant. -/
theorem exists_admissible_of_mem {z : R.M} (C : R.Chart z) {y : R.M}
    (hy : y ∈ R.resolvedParameterSet) (hyC : y ∈ C.openCube) :
    ∃ s, C.IsAdmissible s ∧ ∃ u ∈ cube d C.radius,
      C.extension.symm (reflectOrthant s u) = y := by
  classical
  set A : Set (Fin d → ℝ) := ⋃ s ∈ {s : Fin d → Bool | C.IsAdmissible s},
    reflectOrthant s '' cube d C.radius
  have hAc : IsClosed A := Set.Finite.isClosed_biUnion (Set.toFinite _) fun s _ ↦
    (isCompact_Icc.image (continuous_reflectOrthant s)).isClosed
  set v := C.extension y
  suffices hv : v ∈ A by
    simp only [A, mem_iUnion, mem_image, mem_ofPred_eq, exists_prop] at hv
    obtain ⟨s, hs, u, hu, huv⟩ := hv
    refine ⟨s, hs, u, hu, ?_⟩
    rw [huv, C.extension.left_inv hyC.1]
  by_contra hvA
  -- a neighbourhood of `y` whose chart image misses `A` and lies in the open cube
  set N : Set (Fin d → ℝ) := Aᶜ ∩ Set.pi univ fun _ ↦ Ioo (-C.radius) C.radius
  have hNo : IsOpen N := hAc.isOpen_compl.inter (isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo)
  set O : Set R.M := C.extension.source ∩ C.extension ⁻¹' N
  have hOo : IsOpen O := C.extension.isOpen_inter_preimage hNo
  have hyO : y ∈ O := ⟨hyC.1, hvA, hyC.2⟩
  obtain ⟨y', hy'O, hy'W⟩ := mem_closure_iff.mp hy O hOo hyO
  -- the open set `O ∩ π⁻¹(interior W)` has an open chart image
  set O' : Set R.M := O ∩ R.π ⁻¹' interior W
  have hO'o : IsOpen O' := hOo.inter (isOpen_interior.preimage R.continuous_π)
  have himg : IsOpen (C.extension '' O') :=
    C.extension.isOpen_image_of_subset_source hO'o fun x hx ↦ hx.1.1
  obtain ⟨p, hp, hp0⟩ := exists_mem_forall_ne_zero_of_isOpen himg
    (mem_image_of_mem _ ⟨hy'O, hy'W⟩)
  obtain ⟨x, ⟨⟨hxs, hxN⟩, hxW⟩, rfl⟩ := hp
  have hbox : ∀ j, |C.extension x j| ≤ C.radius := fun j ↦
    abs_le.mpr ⟨(hxN.2 j (mem_univ j)).1.le, (hxN.2 j (mem_univ j)).2.le⟩
  have horth := mem_openOrthant_sign hbox hp0
  set s : Fin d → Bool := fun j ↦ decide (0 < C.extension x j)
  have hadm : C.IsAdmissible s := by
    rcases C.orthant_dichotomy s with h | h
    · exact h
    · exact absurd (interior_subset (by rwa [C.extension.left_inv hxs] : R.π
        (C.extension.symm (C.extension x)) ∈ interior W)) (h _ horth)
  apply hxN.1
  simp only [A, mem_iUnion, mem_image, mem_ofPred_eq, exists_prop]
  exact ⟨s, hadm, reflectOrthant s (C.extension x),
    reflectOrthant_mem_cube_of_mem_openOrthant s horth, reflectOrthant_reflectOrthant s _⟩

/-- **Finitely many charts cover a sublevel** of `K` over a compact `W`: the fibre of `π` over the
compact zero set `W ∩ {K = 0}` is compact, every point of it has a chart, and the complement of
the union of the open cubes in the compact `π⁻¹(W)` is compact with `K ∘ π > 0` on it. -/
theorem exists_finite_cover_sublevel (hW : IsCompact W) (hKc : ContinuousOn K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) :
    ∃ (ι : Type) (_ : Fintype ι) (centre : ι → R.M) (chart : ∀ i, R.Chart (centre i)) (δ : ℝ),
      0 < δ ∧ ∀ z, R.π z ∈ W → K (R.π z) ≤ δ → ∃ i, z ∈ (chart i).openCube := by
  classical
  have hWU : W ⊆ R.U := R.W_subset_U
  have hpre : IsCompact (R.π ⁻¹' W) := R.proper W hWU hW
  set Z : Set (Fin d → ℝ) := W ∩ K ⁻¹' {0}
  have hZc : IsCompact Z := hW.of_isClosed_subset
    (hKc.preimage_isClosed_of_isClosed hW.isClosed isClosed_singleton) inter_subset_left
  have hT : IsCompact (R.π ⁻¹' Z) := R.proper Z (inter_subset_left.trans hWU) hZc
  have hch : ∀ z : R.π ⁻¹' Z, Nonempty (R.Chart z) := fun z ↦ R.charts z z.2.1 z.2.2
  set C : ∀ z : R.π ⁻¹' Z, R.Chart z := fun z ↦ (hch z).some
  obtain ⟨t, ht⟩ := hT.elim_finite_subcover (fun z : R.π ⁻¹' Z ↦ (C z).openCube)
    (fun z ↦ (C z).isOpen_openCube) fun z hz ↦ mem_iUnion.mpr ⟨⟨z, hz⟩, (C ⟨z, hz⟩).mem_openCube⟩
  set O : Set R.M := ⋃ z ∈ t, (C z).openCube
  have hOo : IsOpen O := isOpen_biUnion fun z _ ↦ (C z).isOpen_openCube
  set S : Set R.M := R.π ⁻¹' W ∩ Oᶜ
  have hSc : IsCompact S := hpre.inter_right hOo.isClosed_compl
  have hKS : ContinuousOn (fun z ↦ K (R.π z)) S :=
    hKc.comp R.continuous_π.continuousOn fun z hz ↦ hz.1
  have hpos : ∀ z ∈ S, 0 < K (R.π z) := fun z hz ↦
    lt_of_le_of_ne (hK _ hz.1) fun h ↦ hz.2 (by
      have := ht (show z ∈ R.π ⁻¹' Z from ⟨hz.1, h.symm⟩)
      simpa [O] using this)
  -- `δ` below the minimum of `K ∘ π` on `S`
  obtain ⟨δ, hδ, hδS⟩ : ∃ δ > 0, ∀ z ∈ S, δ < K (R.π z) := by
    rcases S.eq_empty_or_nonempty with hSe | hSne
    · exact ⟨1, one_pos, by simp [hSe]⟩
    · obtain ⟨z₀, hz₀, hmin⟩ := hSc.exists_isMinOn hSne hKS
      exact ⟨K (R.π z₀) / 2, half_pos (hpos z₀ hz₀), fun z hz ↦
        (half_lt_self (hpos z₀ hz₀)).trans_le (hmin hz)⟩
  refine ⟨t, inferInstance, fun i ↦ i.1, fun i ↦ C i.1, δ, hδ, fun z hzW hzK ↦ ?_⟩
  have hzO : z ∈ O := by
    by_contra h
    exact (hδS z ⟨hzW, h⟩).not_ge hzK
  simp only [O, mem_iUnion, exists_prop] at hzO
  obtain ⟨y, hyt, hy⟩ := hzO
  exact ⟨⟨y, hyt⟩, hy⟩

/-- [Wat09, Theorem 6.5], the local coordinates: a resolution of `K ≥ 0` over a compact `W`
has a finite chart family. -/
theorem exists_chartFamily' (hW : IsCompact W) (hKc : ContinuousOn K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) : Nonempty R.ChartFamily := by
  obtain ⟨ι, _, centre, chart, δ, hδ, hcov⟩ := R.exists_finite_cover_sublevel hW hKc hK
  exact ⟨⟨ι, centre, chart, δ, hδ, fun z hz hzK ↦
    hcov z (R.resolvedParameterSet_subset hW.isClosed hz) hzK⟩⟩

variable {R}

namespace ChartFamily

variable (F : R.ChartFamily)

/-- Over a closed `W` with `K` continuous on it, the sublevel of a chart family is closed. -/
theorem isClosed_sublevel (hW : IsClosed W) (hKc : ContinuousOn K W) : IsClosed F.sublevel := by
  have hKπ : ContinuousOn (fun z ↦ K (R.π z)) R.resolvedParameterSet :=
    hKc.comp R.continuous_π.continuousOn (R.resolvedParameterSet_subset hW)
  exact hKπ.preimage_isClosed_of_isClosed R.isClosed_resolvedParameterSet isClosed_Iic

theorem sublevel_subset_iUnion : F.sublevel ⊆ ⋃ i, (F.chart i).openCube := fun z hz ↦
  mem_iUnion.mpr (F.covers z hz.1 hz.2)

/-- **[Wat09, Theorem 6.5] (4)**: a smooth partition of unity on the sublevel of a chart family,
subordinate to the open cubes, equal to `1` at the centre of the chart `i₀`. -/
theorem exists_partitionOfUnity_eq_one (hW : IsClosed W) (hKc : ContinuousOn K W) (i₀ : F.ι) :
    ∃ ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel,
      ρ.IsSubordinate (fun i ↦ (F.chart i).openCube) ∧
      (F.centre i₀ ∈ F.sublevel → ρ i₀ (F.centre i₀) = 1) := by
  classical
  have : IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ R.M := IsManifold.of_le (n := ω) le_top
  have : LocallyCompactSpace R.M := ChartedSpace.locallyCompactSpace (Fin d → ℝ) R.M
  have : SigmaCompactSpace R.M := sigmaCompactSpace_of_locallyCompact_secondCountable
  set V : F.ι → Set R.M := fun i ↦
    if i = i₀ then (F.chart i).openCube else (F.chart i).openCube \ {F.centre i₀}
  have hVo : ∀ i, IsOpen (V i) := fun i ↦ by
    by_cases h : i = i₀
    · subst h
      simpa [V] using (F.chart i).isOpen_openCube
    · simp only [V, h, ite_false]
      exact (F.chart i).isOpen_openCube.sdiff isClosed_singleton
  have hcov : F.sublevel ⊆ ⋃ i, V i := by
    intro z hz
    obtain ⟨i, hi⟩ := F.covers z hz.1 hz.2
    by_cases hz₀ : z = F.centre i₀
    · exact mem_iUnion.mpr ⟨i₀, by simpa [V, hz₀] using (F.chart i₀).mem_openCube⟩
    · refine mem_iUnion.mpr ⟨i, ?_⟩
      by_cases h : i = i₀
      · subst h
        simpa [V] using hi
      · simp only [V, h, ite_false]
        exact ⟨hi, hz₀⟩
  obtain ⟨ρ, hρ⟩ := SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin d → ℝ)
    (F.isClosed_sublevel hW hKc) V hVo hcov
  refine ⟨ρ, fun i ↦ (hρ i).trans ?_, fun hs ↦ ?_⟩
  · by_cases h : i = i₀
    · subst h
      simp [V]
    · simp [V, h]
  · have hzero : ∀ i ≠ i₀, ρ i (F.centre i₀) = 0 := fun i hi ↦ by
      refine image_eq_zero_of_notMem_tsupport fun hmem ↦ ?_
      have := hρ i hmem
      simp [V, hi] at this
    have hsum := ρ.sum_eq_one hs
    rw [finsum_eq_single _ i₀ hzero] at hsum
    exact hsum

/-- A partition of unity subordinate to a chart family. -/
theorem exists_partitionOfUnity' (hW : IsClosed W) (hKc : ContinuousOn K W) :
    ∃ ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel,
      ρ.IsSubordinate fun i ↦ (F.chart i).openCube := by
  classical
  have : IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ R.M := IsManifold.of_le (n := ω) le_top
  have : LocallyCompactSpace R.M := ChartedSpace.locallyCompactSpace (Fin d → ℝ) R.M
  have : SigmaCompactSpace R.M := sigmaCompactSpace_of_locallyCompact_secondCountable
  exact SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Fin d → ℝ)
    (F.isClosed_sublevel hW hKc) _ (fun i ↦ (F.chart i).isOpen_openCube) F.sublevel_subset_iUnion

end ChartFamily

/-! ## The piece maps -/

namespace ChartFamily.Piece

variable {F : R.ChartFamily} (α : F.Piece)

/-- The open set of orthant coordinates inside the chart. -/
@[expose] def domain : Set (Fin d → ℝ) :=
  reflectOrthant α.orthant ⁻¹' (F.chart α.chart).extension.target

theorem isOpen_domain : IsOpen α.domain :=
  (F.chart α.chart).extension.open_target.preimage (continuous_reflectOrthant _)

theorem cube_subset_domain : cube d α.radius ⊆ α.domain := fun _ hu ↦
  (F.chart α.chart).reflectOrthant_mem_target _ hu

theorem analyticOnNhd_map_domain : AnalyticOnNhd ℝ α.map α.domain := fun u hu ↦
  (R.analyticOnNhd_comp_symm (F.chart α.chart) _ hu).comp
    ((reflectOrthantCLE α.orthant).toContinuousLinearMap.analyticAt u)

theorem analyticOnNhd_map : AnalyticOnNhd ℝ α.map (cube d α.radius) :=
  α.analyticOnNhd_map_domain.mono α.cube_subset_domain

theorem continuousOn_map : ContinuousOn α.map α.domain :=
  α.analyticOnNhd_map_domain.continuousOn

/-- The loss on a piece is the monomial `u^{2k}`. -/
theorem loss_map {u : Fin d → ℝ} (hu : u ∈ cube d α.radius) :
    K (α.map u) = ∏ j, u j ^ (2 * α.k j) := by
  rw [Piece.map, Piece.point, (F.chart α.chart).loss_eq _ (α.cube_subset_domain hu),
    prod_reflectOrthant_pow_two_mul]

/-- The open positive cube of a piece lies over the interior of `W`. -/
theorem map_mem_interior {u : Fin d → ℝ} (hu : ∀ j, 0 < u j ∧ u j ≤ α.radius) :
    α.map u ∈ interior W :=
  α.admissible _ (reflectOrthant_mem_openOrthant _ hu)

/-- Over a closed `W`, a piece maps its closed cube into `W`. -/
theorem map_mem (hW : IsClosed W) {u : Fin d → ℝ} (hu : u ∈ cube d α.radius) : α.map u ∈ W := by
  obtain ⟨v, hv, hlim⟩ := exists_tendsto_cube_interior (F.chart α.chart).radius_pos hu
  have hc : ContinuousAt α.map u :=
    α.continuousOn_map.continuousAt (α.isOpen_domain.mem_nhds (α.cube_subset_domain hu))
  exact hW.mem_of_tendsto (hc.tendsto.comp hlim)
    (Eventually.of_forall fun n ↦ interior_subset (α.map_mem_interior (hv n)))

theorem point_zero : α.point 0 = F.centre α.chart := by
  rw [Piece.point, reflectOrthant_zero, (F.chart α.chart).symm_zero]

open scoped Classical in
/-- A measurable total extension of the piece map, equal to it on the open domain. -/
@[expose] noncomputable def extMap : (Fin d → ℝ) → (Fin d → ℝ) :=
  α.domain.piecewise α.map fun _ ↦ α.map 0

theorem extMap_eq {u : Fin d → ℝ} (hu : u ∈ α.domain) : α.extMap u = α.map u := by
  classical
  exact Set.piecewise_eq_of_mem _ _ _ hu

theorem measurable_extMap : Measurable α.extMap := by
  classical
  exact α.continuousOn_map.measurable_piecewise continuousOn_const α.isOpen_domain.measurableSet

theorem analyticOnNhd_extMap : AnalyticOnNhd ℝ α.extMap (cube d α.radius) := fun u hu ↦
  (α.analyticOnNhd_map u hu).congr (Filter.eventuallyEq_of_mem
    (α.isOpen_domain.mem_nhds (α.cube_subset_domain hu)) fun _ hv ↦ (α.extMap_eq hv).symm)

/-- The chart weight of a piece is smooth on its cube. -/
theorem contDiffOn_weight (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel) :
    ContDiffOn ℝ 1 (fun u ↦ ρ α.chart (α.point u) * α.densityUnit u) (cube d α.radius) := by
  set C := F.chart α.chart
  have h1 : ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (fun v ↦ ρ α.chart (C.extension.symm v))
      C.extension.target :=
    (ρ α.chart).2.comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas C.extension_mem).of_le le_top)
  have h2 : ContDiffOn ℝ ∞ (fun v ↦ ρ α.chart (C.extension.symm v)) C.extension.target :=
    contMDiffOn_iff_contDiffOn.mp h1
  have hr : ContDiff ℝ ∞ (reflectOrthant α.orthant : (Fin d → ℝ) → _) :=
    (reflectOrthantCLE α.orthant).contDiff
  have h3 := (h2.mul C.densityUnit_contDiffOn).comp hr.contDiffOn
    (fun u hu ↦ C.reflectOrthant_mem_target α.orthant hu)
  exact (h3.of_le (by exact_mod_cast le_top)).congr fun u _ ↦ rfl

end ChartFamily.Piece

end SLTResolution

end SingularLearningTheory
