/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# The finite subcover of the fibre and the covered neighbourhood

The point-set part of the passage from a monomial resolution to a chart family ([BM88, Theorem
4.4(3), p. 23]: compact subsets `L_j ⊆ W_j` with `K = ⋃ π_j(L_j)`): the compact fibre
`dom ∩ φ⁻¹{w}` of a chart box over the base point is covered by finitely many open cubes
`ball b (ϱ b)` centred at fibre points; the leftover `C = dom \ ⋃_{b ∈ T} ball b (ϱ b)` is
compact, its image is compact and misses `w`. Removing the finitely many compact images of the
leftovers from `interior N` gives an open neighbourhood `U` of `w`, the uncovered part
`N \ ⋃ φ_i '' dom i` of the compact `N` is measurable (its nullity is the `cover` field of the
partial resolution), and every point of `U` outside that null set is the image of a point of some
closed cube `closedBall b (ϱ b)`, `b ∈ T_i`. Everything here is stated for arbitrary chart maps
continuous on their compact boxes; the terminal-chart structure enters only through the choice of
the radii `ϱ` (`Chart.lean`).
-/

public section

open Set MeasureTheory
open scoped Topology

namespace SingularLearningTheory

variable {n : ℕ}

/-- The compact fibre over `w` of a box is covered by finitely many open cubes centred at fibre
points; the leftover of the box is compact, its image is compact and misses `w` (Mathlib's
`IsCompact.elim_finite_subcover`). -/
theorem _root_.IsCompact.exists_finset_fiber_cover {dom : Set (Fin n → ℝ)} (hdom : IsCompact dom)
    {φ : (Fin n → ℝ) → (Fin n → ℝ)} (hφ : ContinuousOn φ dom) (w : Fin n → ℝ)
    (ϱ : (Fin n → ℝ) → ℝ) (hϱ : ∀ b ∈ dom ∩ φ ⁻¹' {w}, 0 < ϱ b) :
    ∃ T : Finset (Fin n → ℝ), ↑T ⊆ dom ∩ φ ⁻¹' {w} ∧
      IsCompact (dom \ ⋃ b ∈ T, Metric.ball b (ϱ b)) ∧
      IsCompact (φ '' (dom \ ⋃ b ∈ T, Metric.ball b (ϱ b))) ∧
      w ∉ φ '' (dom \ ⋃ b ∈ T, Metric.ball b (ϱ b)) := by
  classical
  set F : Set (Fin n → ℝ) := dom ∩ φ ⁻¹' {w} with hF
  have hFc : IsCompact F :=
    hdom.of_isClosed_subset (hφ.preimage_isClosed_of_isClosed hdom.isClosed isClosed_singleton)
      inter_subset_left
  obtain ⟨t, ht⟩ := hFc.elim_finite_subcover (fun b : F => Metric.ball (b : Fin n → ℝ) (ϱ b))
    (fun _ => Metric.isOpen_ball) fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hϱ x hx)⟩
  refine ⟨t.image Subtype.val, ?_, ?_, ?_, ?_⟩
  · intro b hb
    obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hb)
    exact c.2
  · exact hdom.diff (isOpen_biUnion fun _ _ => Metric.isOpen_ball)
  · exact (hdom.diff (isOpen_biUnion fun _ _ => Metric.isOpen_ball)).image_of_continuousOn
      (hφ.mono sdiff_subset)
  · rintro ⟨y, ⟨hydom, hyC⟩, hyw⟩
    have hyF : y ∈ F := ⟨hydom, hyw⟩
    obtain ⟨c, hc, hyc⟩ := mem_iUnion₂.mp (ht hyF)
    exact hyC (mem_iUnion₂.mpr ⟨(c : Fin n → ℝ), Finset.mem_image_of_mem _ hc, hyc⟩)

variable {ι : Type} {N : Set (Fin n → ℝ)} {φ : ι → (Fin n → ℝ) → (Fin n → ℝ)}

/-- `interior N` minus the finitely many compact images of the leftovers is open. -/
theorem _root_.isOpen_interior_sdiff_iUnion_image [Finite ι] {C : ι → Set (Fin n → ℝ)}
    (hC : ∀ i, IsCompact (φ i '' C i)) : IsOpen (interior N \ ⋃ i, φ i '' C i) :=
  isOpen_interior.sdiff (isClosed_iUnion_of_finite fun i => (hC i).isClosed)

/-- The open set contains `w`. -/
theorem _root_.mem_interior_sdiff_iUnion_image {C : ι → Set (Fin n → ℝ)} {w : Fin n → ℝ}
    (hN : N ∈ 𝓝 w) (hw : ∀ i, w ∉ φ i '' C i) : w ∈ interior N \ ⋃ i, φ i '' C i :=
  ⟨mem_interior_iff_mem_nhds.mpr hN, fun h => by
    obtain ⟨i, hi⟩ := mem_iUnion.mp h
    exact hw i hi⟩

/-- The uncovered part of a compact `N` is measurable (its nullity is
`PartialResolution.cover`). -/
theorem _root_.IsCompact.measurableSet_sdiff_iUnion_image [Finite ι] (hN : IsCompact N)
    {dom : ι → Set (Fin n → ℝ)} (hdom : ∀ i, IsCompact (φ i '' dom i)) :
    MeasurableSet (N \ ⋃ i, φ i '' dom i) :=
  hN.isClosed.measurableSet.diff (MeasurableSet.iUnion fun i => (hdom i).isClosed.measurableSet)

/-- The open set minus the uncovered null set is covered by the images of the closed cubes. -/
theorem _root_.interior_sdiff_subset_iUnion_image_closedBall {dom : ι → Set (Fin n → ℝ)}
    (T : ι → Finset (Fin n → ℝ))
    (ϱ : ι → (Fin n → ℝ) → ℝ) :
    (interior N \ ⋃ i, φ i '' (dom i \ ⋃ b ∈ T i, Metric.ball b (ϱ i b))) \
        (N \ ⋃ i, φ i '' dom i) ⊆
      ⋃ i, ⋃ b ∈ T i, φ i '' Metric.closedBall b (ϱ i b) := by
  rintro x ⟨⟨hxN, hxC⟩, hxN0⟩
  have hxcov : x ∈ ⋃ i, φ i '' dom i := by
    by_contra hcon
    exact hxN0 ⟨interior_subset hxN, hcon⟩
  obtain ⟨i, hi⟩ := mem_iUnion.mp hxcov
  obtain ⟨y, hy, rfl⟩ := hi
  have hyball : y ∈ ⋃ b ∈ T i, Metric.ball b (ϱ i b) := by
    by_contra hcon
    exact hxC (mem_iUnion.mpr ⟨i, ⟨y, ⟨hy, hcon⟩, rfl⟩⟩)
  obtain ⟨b, hb, hyb⟩ := mem_iUnion₂.mp hyball
  exact mem_iUnion.mpr ⟨i, mem_iUnion₂.mpr ⟨b, hb, ⟨y, Metric.ball_subset_closedBall hyb, rfl⟩⟩⟩

end SingularLearningTheory
