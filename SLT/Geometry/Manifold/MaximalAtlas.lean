/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Atlas
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
public import Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# New charts from old, and inverses glued from local inverses

A chart of the maximal `C^n` atlas of a manifold modelled on a normed space `E`, restricted to an
open set and followed by an open partial homeomorphism of `E` that is `C^n` in both directions, is
again in the maximal atlas (`OpenPartialHomeomorph.restrOpen_trans_mem_maximalAtlas`);
`OpenPartialHomeomorph.restrOpen_trans_source_eq` and
`OpenPartialHomeomorph.restrOpen_trans_target_eq` compute its source and target when the
restriction is to the preimage of an open subset of the target.

A map that is a local diffeomorphism on the preimage of a set `t` and maps that preimage
bijectively onto `t` has an inverse that is `C^n` on `t`, the local inverses agreeing by
injectivity (`IsLocalDiffeomorphOn.exists_contMDiffOn_leftInvOn`); conversely, a `C^n` map with
a two-sided inverse over an open `t` that is `C^n` there is a local diffeomorphism on the preimage
of `t` (`IsLocalDiffeomorphOn.of_contMDiffOn_leftInvOn`).

A chart of the maximal atlas is a partial diffeomorphism
(`OpenPartialHomeomorph.toPartialDiffeomorph`). An analytic map read in a chart of the maximal
analytic atlas is analytic on the chart's target (`analyticOnNhd_comp_symm_of_mem_maximalAtlas`).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

namespace OpenPartialHomeomorph

section Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The source of `φ` restricted to the preimage of an open `B ⊆ e.source`, followed by `e`. -/
theorem restrOpen_trans_source_eq (φ : OpenPartialHomeomorph X Y) {B : Set Y} (hBo : IsOpen B)
    (e : OpenPartialHomeomorph Y Y) (hBe : B ⊆ e.source) :
    ((φ.restrOpen (φ.source ∩ φ ⁻¹' B) (φ.isOpen_inter_preimage hBo)).trans e).source =
      φ.source ∩ φ ⁻¹' B := by
  rw [trans_source, restrOpen_source, coe_restrOpen]
  ext x
  constructor
  · rintro ⟨⟨-, h2⟩, -⟩
    exact h2
  · intro h2
    exact ⟨⟨h2.1, h2⟩, hBe h2.2⟩

/-- The target of `φ` restricted to the preimage of an open `B ⊆ φ.target ∩ e.source`, followed
by `e`, is `e '' B`. -/
theorem restrOpen_trans_target_eq (φ : OpenPartialHomeomorph X Y) {B : Set Y} (hBo : IsOpen B)
    (hBt : B ⊆ φ.target) (e : OpenPartialHomeomorph Y Y) (hBe : B ⊆ e.source) :
    ((φ.restrOpen (φ.source ∩ φ ⁻¹' B) (φ.isOpen_inter_preimage hBo)).trans e).target =
      e '' B := by
  rw [← image_source_eq_target, trans_source, restrOpen_source, coe_restrOpen, coe_trans,
    coe_restrOpen, Set.image_comp]
  congr 1
  ext u
  constructor
  · rintro ⟨x, ⟨⟨-, -, hxB⟩, -⟩, rfl⟩
    exact hxB
  · intro hu
    refine ⟨φ.symm u, ⟨⟨φ.map_target (hBt hu), φ.map_target (hBt hu), ?_⟩, ?_⟩,
      φ.right_inv (hBt hu)⟩
    · rw [mem_preimage, φ.right_inv (hBt hu)]
      exact hu
    · rw [mem_preimage, φ.right_inv (hBt hu)]
      exact hBe hu

end Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {n : ℕ∞ω}
  [IsManifold 𝓘(𝕜, E) n M]

/-- A chart of the maximal `C^n` atlas, restricted to an open set and followed by an open partial
homeomorphism of the model space that is `C^n` in both directions, is in the maximal atlas. -/
theorem restrOpen_trans_mem_maximalAtlas {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) {s : Set M} (hs : IsOpen s)
    {e : OpenPartialHomeomorph E E} (he : ContDiffOn 𝕜 n e e.source)
    (he' : ContDiffOn 𝕜 n e.symm e.target) :
    (φ.restrOpen s hs).trans e ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M := by
  refine mem_maximalAtlas_of_contMDiffOn _ ?_ ?_
  · rw [coe_trans, coe_restrOpen, trans_source, restrOpen_source, coe_restrOpen]
    exact (contMDiffOn_iff_contDiffOn.mpr he).comp
      ((contMDiffOn_of_mem_maximalAtlas hφ).mono (inter_subset_left.trans inter_subset_left))
      fun _ hx ↦ hx.2
  · rw [coe_trans_symm, coe_restrOpen_symm, trans_target]
    refine (contMDiffOn_symm_of_mem_maximalAtlas hφ).comp
      ((contMDiffOn_iff_contDiffOn.mpr he').mono inter_subset_left) fun v hv ↦ ?_
    have h1 : (φ.restrOpen s hs).target ⊆ φ.target := by
      rw [← (φ.restrOpen s hs).image_source_eq_target, restrOpen_source, coe_restrOpen,
        ← φ.image_source_eq_target]
      exact Set.image_mono inter_subset_left
    exact h1 hv.2

/-- A chart of the maximal `C^n` atlas, as a partial diffeomorphism to the model space. -/
@[expose] def toPartialDiffeomorph {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) :
    PartialDiffeomorph 𝓘(𝕜, E) 𝓘(𝕜, E) M E n where
  toPartialEquiv := φ.toPartialEquiv
  open_source := φ.open_source
  open_target := φ.open_target
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas hφ
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas hφ

omit [IsManifold 𝓘(𝕜, E) n M] in
theorem coe_toPartialDiffeomorph {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) :
    (φ.toPartialDiffeomorph hφ : M → E) = φ :=
  (rfl)

omit [IsManifold 𝓘(𝕜, E) n M] in
theorem coe_toPartialDiffeomorph_symm {φ : OpenPartialHomeomorph M E}
    (hφ : φ ∈ IsManifold.maximalAtlas 𝓘(𝕜, E) n M) :
    ((φ.toPartialDiffeomorph hφ).symm : E → M) = φ.symm :=
  (rfl)

end OpenPartialHomeomorph

/-- `π ∘ e⁻¹` is analytic on the target of a chart `e` of the maximal analytic atlas when `π` is
analytic. -/
theorem analyticOnNhd_comp_symm_of_mem_maximalAtlas {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] {π : M → F} (hπ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, F) ω π)
    {e : OpenPartialHomeomorph M E} (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) ω M) :
    AnalyticOnNhd ℝ (π ∘ e.symm) e.target := by
  have h1 : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) ω (π ∘ e.symm) e.target :=
    hπ.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)
  exact e.open_target.analyticOn_iff_analyticOnNhd.mp
    ((contDiffOn_omega_iff_analyticOn e.open_target.uniqueDiffOn).mp h1.contDiffOn)

namespace IsLocalDiffeomorphOn

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {H : Type*}
  [TopologicalSpace H] {G : Type*} [TopologicalSpace G] {I : ModelWithCorners 𝕜 E H}
  {J : ModelWithCorners 𝕜 F G} {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {N : Type*}
  [TopologicalSpace N] [ChartedSpace G N] {n : WithTop ℕ∞}

/-- A local diffeomorphism on the preimage of `t` that maps it bijectively onto `t` has an inverse
that is `C^n` on `t`: near each point of `t` it agrees with a local inverse. -/
theorem exists_contMDiffOn_leftInvOn [Nonempty M] {f : M → N} {t : Set N}
    (hf : IsLocalDiffeomorphOn I J n f (f ⁻¹' t)) (hbij : BijOn f (f ⁻¹' t) t) :
    ∃ g : N → M, ContMDiffOn J I n g t ∧ ∀ x ∈ f ⁻¹' t, g (f x) = x := by
  classical
  refine ⟨Function.invFunOn f (f ⁻¹' t), fun y hy ↦ ?_, fun x hx ↦ hbij.invOn_invFunOn.1 hx⟩
  obtain ⟨x, hx, rfl⟩ := hbij.surjOn hy
  have hlx := hf ⟨x, hx⟩
  set L := hlx.localInverse
  -- near `f x`, within `t`, the inverse is the local inverse `L`
  have hagree : ∀ y' ∈ t ∩ L.source, Function.invFunOn f (f ⁻¹' t) y' = L y' := by
    rintro y' ⟨hy't, hy'L⟩
    have hfy : f (L y') = y' := hlx.localInverse_right_inv hy'L
    have hmem : L y' ∈ f ⁻¹' t := by rw [mem_preimage, hfy]; exact hy't
    conv_lhs => rw [← hfy]
    exact hbij.invOn_invFunOn.1 hmem
  have hL : ContMDiffWithinAt J I n L (t ∩ L.source) (f x) :=
    (hlx.contMDiffOn_localInverse _ hlx.localInverse_mem_source).mono inter_subset_right
  refine (hL.congr hagree (hagree _ ⟨hy, hlx.localInverse_mem_source⟩)).mono_of_mem_nhdsWithin ?_
  exact inter_mem_nhdsWithin _ (hlx.localInverse_open_source.mem_nhds hlx.localInverse_mem_source)

/-- Conversely, a `C^n` map with a left inverse that is `C^n` on an open `t` and a right inverse
there is a local diffeomorphism on the preimage of `t`: the map and the inverse form one
`PartialDiffeomorph` from `f⁻¹ t` onto `t`. -/
theorem of_contMDiffOn_leftInvOn {f : M → N} {g : N → M} {t : Set N} (ht : IsOpen t)
    (hf : ContMDiff I J n f) (hg : ContMDiffOn J I n g t) (hleft : ∀ x ∈ f ⁻¹' t, g (f x) = x)
    (hright : ∀ y ∈ t, f (g y) = y) : IsLocalDiffeomorphOn I J n f (f ⁻¹' t) := by
  let Φ : PartialDiffeomorph I J M N n :=
    { toFun := f
      invFun := g
      source := f ⁻¹' t
      target := t
      map_source' := fun _ hx ↦ hx
      map_target' := fun y hy ↦ by
        change f (g y) ∈ t
        rw [hright y hy]
        exact hy
      left_inv' := hleft
      right_inv' := hright
      open_source := ht.preimage hf.continuous
      open_target := ht
      contMDiffOn_toFun := hf.contMDiffOn
      contMDiffOn_invFun := hg }
  exact fun x ↦ Φ.isLocalDiffeomorphAt _ _ _ x.2

end IsLocalDiffeomorphOn
