/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Hironaka.Manifold.SigmaManifold
public import SLT.Resolution.Hironaka
-- exposes `IsLocalDiffeomorphAt` for `obtain`
import all Mathlib.Geometry.Manifold.LocalDiffeomorph

/-!
# One resolution over a finite union of components, as a disjoint union

Finitely many resolutions `(V i, M i, π i)` of one function `F` over pairwise disjoint open
sets assemble into a single resolution `(⋃ i, V i, Σ i, M i, π)` (`Resolution.sigma`), the
manifold structure of the disjoint union being hironaka's `ChartedSpace.sigma` /
`IsManifold.sigma`.

No thesis counterpart.
-/

public section

namespace SingularLearningTheory

open Set Filter Topology TopologicalSpace
open scoped Manifold ContDiff

section SigmaManifold

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {n : WithTop ℕ∞} {ι : Type*} {M : ι → Type*} [∀ i, TopologicalSpace (M i)]
  [∀ i, ChartedSpace H (M i)]

/-- A map out of the disjoint union is `C^n` as soon as its restriction to every summand is. -/
theorem _root_.contMDiff_sigma {f : (Σ i, M i) → N} (hf : ∀ i, ContMDiff I J n fun x ↦ f ⟨i, x⟩) :
    ContMDiff I J n f := by
  obtain (hH | hH) := isEmpty_or_nonempty H
  · rintro ⟨i, x⟩
    exact ((isEmpty_of_chartedSpace H (M := M i)).false x).elim
  rintro ⟨i, x⟩
  rw [contMDiffAt_iff]
  refine ⟨(continuous_sigma fun i ↦ (hf i).continuous).continuousAt, ?_⟩
  have h := hf i x
  rw [contMDiffAt_iff] at h
  have hpt : extChartAt I (⟨i, x⟩ : Σ i, M i) ⟨i, x⟩ = extChartAt I x x := by
    simp [extChartAt, ChartedSpace.sigma_chartAt, sigma_mk_injective.extend_apply (chartAt H x)]
  rw [hpt]
  refine h.2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦ ?_) ?_
  · simp only [extChartAt, ChartedSpace.sigma_chartAt, Function.comp]
    rfl
  · simp only [extChartAt, ChartedSpace.sigma_chartAt, Function.comp]
    rfl

/-- A chart of the maximal atlas of a summand, lifted along `Sigma.mk i`, is a chart of the
maximal atlas of the disjoint union. -/
theorem _root_.OpenPartialHomeomorph.lift_openEmbedding_sigmaMk_mem_maximalAtlas [Nonempty H]
    [∀ i, IsManifold I n (M i)]
    {i : ι} {e : OpenPartialHomeomorph (M i) H} (he : e ∈ IsManifold.maximalAtlas I n (M i)) :
    e.lift_openEmbedding IsOpenEmbedding.sigmaMk ∈ IsManifold.maximalAtlas I n (Σ i, M i) := by
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff]
  intro e' he'
  obtain ⟨j, f, hf, rfl⟩ := ChartedSpace.mem_atlas_sigma M he'
  by_cases hij : i = j
  · subst hij
    rw [e.lift_openEmbedding_trans f IsOpenEmbedding.sigmaMk,
      f.lift_openEmbedding_trans e IsOpenEmbedding.sigmaMk]
    exact ⟨IsManifold.compatible_of_mem_maximalAtlas he (IsManifold.subset_maximalAtlas hf),
      IsManifold.compatible_of_mem_maximalAtlas (IsManifold.subset_maximalAtlas hf) he⟩
  · constructor <;> apply ContDiffGroupoid.mem_of_source_eq_empty <;> ext x <;>
      refine ⟨fun ⟨_, hx₂⟩ ↦ ?_, fun hx ↦ hx.elim⟩ <;>
      rw [OpenPartialHomeomorph.lift_openEmbedding_source] at hx₂ <;>
      obtain ⟨y, -, hy⟩ := hx₂
    · exact hij (Sigma.mk.inj_iff.mp hy).1.symm
    · exact hij (Sigma.mk.inj_iff.mp hy).1

end SigmaManifold

variable {d : ℕ}

/-- The map of the disjoint union of resolutions is a local analytic diffeomorphism over
`{F ≠ 0}`: at a point of summand `i`, the local diffeomorphism of `R i` followed by
`Sigma.mk i`. Supports `Resolution.sigma`. -/
theorem Resolution.isLocalDiffeomorphOn_sigma {F : (Fin d → ℝ) → ℝ} {ι : Type}
    (R : ι → Resolution F) :
    IsLocalDiffeomorphOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω
      (fun p : Σ i, (R i).M ↦ (R p.1).π p.2)
      ((fun p : Σ i, (R i).M ↦ (R p.1).π p.2) ⁻¹' {w | F w ≠ 0}) := by
  rintro ⟨⟨i, x⟩, hx⟩
  have hloc : IsLocalDiffeomorphAt 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω (R i).π x :=
    (R i).isLocalDiffeomorphOn ⟨x, hx⟩
  obtain ⟨Φ, hxΦ, hEq⟩ := hloc
  let Ψ : PartialDiffeomorph 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) (Σ i, (R i).M) (Fin d → ℝ) ω :=
    { toFun := fun p ↦ (R p.1).π p.2
      invFun := fun z ↦ ⟨i, Φ.invFun z⟩
      source := Sigma.mk i '' Φ.source
      target := Φ.target
      map_source' := by
        rintro _ ⟨y, hy, rfl⟩
        change (R i).π y ∈ Φ.target
        rw [hEq hy]
        exact Φ.map_source' hy
      map_target' := fun z hz ↦ ⟨Φ.invFun z, Φ.map_target' hz, rfl⟩
      left_inv' := by
        rintro _ ⟨y, hy, rfl⟩
        change (⟨i, Φ.invFun ((R i).π y)⟩ : Σ i, (R i).M) = ⟨i, y⟩
        rw [hEq hy]
        exact congrArg (Sigma.mk i) (Φ.left_inv' hy)
      right_inv' := fun z hz ↦ by
        change (R i).π (Φ.invFun z) = z
        rw [hEq (Φ.map_target' hz)]
        exact Φ.right_inv' hz
      open_source := isOpenMap_sigmaMk _ Φ.open_source
      open_target := Φ.open_target
      contMDiffOn_toFun := (contMDiff_sigma fun i ↦ (R i).analytic_π).contMDiffOn
      contMDiffOn_invFun :=
        (ContMDiff.sigmaMk (I := 𝓘(ℝ, Fin d → ℝ)) (n := ω) (M := fun i ↦ (R i).M)
          i).comp_contMDiffOn
          Φ.contMDiffOn_invFun }
  exact ⟨Ψ, ⟨x, hxΦ, rfl⟩, fun p _ ↦ rfl⟩

/-- Finitely many resolutions of `F` over pairwise disjoint open sets are one resolution over
the union, on the disjoint union of the manifolds. -/
@[expose] noncomputable def Resolution.sigma {F : (Fin d → ℝ) → ℝ} {ι : Type} [Finite ι]
    (R : ι → Resolution F)
    (hR : Pairwise fun i j ↦ Disjoint (R i).U (R j).U) : Resolution F where
  U := ⋃ i, (R i).U
  isOpen_U := isOpen_iUnion fun i ↦ (R i).isOpen_U
  M := Σ i, (R i).M
  π p := (R p.1).π p.2
  analytic_π := contMDiff_sigma fun i ↦ (R i).analytic_π
  range_π := by
    ext w
    simp only [mem_range, Sigma.exists, mem_iUnion, ← (R _).range_π]
  proper C hC hCc := by
    have hCi : ∀ i, IsCompact (C ∩ (R i).U) := by
      intro i
      have : C ∩ (R i).U = C \ ⋃ j ∈ {j | j ≠ i}, (R j).U := by
        ext w
        constructor
        · rintro ⟨hwC, hwi⟩
          refine ⟨hwC, fun hw ↦ ?_⟩
          obtain ⟨j, hji, hwj⟩ := mem_iUnion₂.mp hw
          exact (hR hji).ne_of_mem hwj hwi rfl
        · rintro ⟨hwC, hw⟩
          refine ⟨hwC, ?_⟩
          obtain ⟨j, hwj⟩ := mem_iUnion.mp (hC hwC)
          by_contra hwi
          exact hw (mem_iUnion₂.mpr ⟨j, fun hji ↦ hwi (hji ▸ hwj), hwj⟩)
      rw [this]
      exact hCc.diff (isOpen_biUnion fun j _ ↦ (R j).isOpen_U)
    have hpre : (fun p : Σ i, (R i).M ↦ (R p.1).π p.2) ⁻¹' C =
        ⋃ i, Sigma.mk i '' ((R i).π ⁻¹' (C ∩ (R i).U)) := by
      ext ⟨i, x⟩
      simp only [mem_preimage, mem_iUnion, mem_image]
      constructor
      · intro hx
        exact ⟨i, x, ⟨hx, (R i).mem_U x⟩, rfl⟩
      · rintro ⟨j, y, ⟨hy, -⟩, hyx⟩
        cases hyx
        exact hy
    rw [hpre]
    exact isCompact_iUnion fun i ↦
      ((R i).proper _ inter_subset_right (hCi i)).image continuous_sigmaMk
  isLocalDiffeomorphOn := Resolution.isLocalDiffeomorphOn_sigma R
  bijOn := by
    refine ⟨fun p hp ↦ ⟨mem_iUnion.mpr ⟨p.1, (R p.1).mem_U p.2⟩, hp⟩, ?_, ?_⟩
    · rintro ⟨i, x⟩ hx ⟨j, y⟩ hy hxy
      change (R i).π x = (R j).π y at hxy
      obtain rfl : i = j := by
        by_contra hij
        exact (hR hij).ne_of_mem ((R i).mem_U x) ((R j).mem_U y) hxy
      exact congrArg (Sigma.mk i) ((R i).injOn hx hy hxy)
    · rintro w ⟨hwV, hw⟩
      obtain ⟨i, hwi⟩ := mem_iUnion.mp hwV
      obtain ⟨x, hx, rfl⟩ := (R i).bijOn.surjOn ⟨hwi, hw⟩
      exact ⟨⟨i, x⟩, hx, rfl⟩
  chart := by
    rintro ⟨i, x⟩ hx
    obtain ⟨e, he, hxe, he0, S, k, hexp, b, hS, hFg, hb, hb0, hdet⟩ := (R i).chart x hx
    refine ⟨e.lift_openEmbedding IsOpenEmbedding.sigmaMk,
      OpenPartialHomeomorph.lift_openEmbedding_sigmaMk_mem_maximalAtlas he, ⟨x, hxe, rfl⟩, ?_,
      S, k, hexp, b, hS, hFg, hb, hb0, hdet⟩
    rw [OpenPartialHomeomorph.lift_openEmbedding_apply]
    exact he0

end SingularLearningTheory
