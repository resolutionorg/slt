/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.PieceTransport
public import SLT.Resolution.Nondegenerate
public import SLT.SingularIntegrals.TypeOfAtlas
public import SLT.SingularIntegrals.Resolution
public import SLT.SingularIntegrals.SingularityType

/-!
# What the pieces of a chart family give

Consequences of the transport identity of `Resolution/PieceTransport.lean` for a chart family `F`
of an `SLTResolution` over a compact `W`:

* a point of the sublevel of `F` gives a piece (`ChartFamily.nonempty_piece_of_mem_sublevel`),
  and without pieces `W ∩ {K ≤ δ}` is null for a small `δ`
  (`ChartFamily.exists_volume_sublevel_eq_zero`);
* with a partition of unity equal to `1` at the centre of a chart attaining the minimal learning
  coefficient with the largest multiplicity, the atlas of the pieces is nondegenerate, so its
  `(λ, m)` is the singularity type (`ChartFamily.exists_isSingularityType`);
* a family extended by one more chart (`ChartFamily.insert`), with which the invariants of any
  chart are compared to those of the family;
* the prior-free atlas of the pieces (`ChartFamily.toZeroAtlas`), with weights `0`, for the
  theorems that do not involve the prior (maximum likelihood).

| Thesis | Lean |
| --- | --- |
| `λ`, `m` read off the local coordinates ([Wat09, Definition 6.4]) are the singularity type | |
| | `SLTResolution.ChartFamily.exists_isSingularityType` |
-/

public section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff ENNReal

namespace SingularLearningTheory

variable {d : ℕ}

namespace SLTResolution

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {R : SLTResolution K φ W}

namespace ChartFamily

variable {F : R.ChartFamily}

/-- A point of the sublevel of a chart family lies in a closed admissible orthant of one of its
charts, so the family has a piece. -/
theorem nonempty_piece_of_mem_sublevel {z : R.M} (hz : z ∈ F.sublevel) : Nonempty F.Piece := by
  obtain ⟨i, hi⟩ := F.covers z hz.1 hz.2
  obtain ⟨s, hs, -⟩ := R.exists_admissible_of_mem (F.chart i) hz.1 hi
  exact ⟨⟨i, s, hs⟩⟩

/-- The centre of the chart of a piece lies in the sublevel. -/
theorem center_mem_sublevel (α : F.Piece) : F.centre α.chart ∈ F.sublevel :=
  ⟨R.center_mem_resolvedParameterSet _ α.admissible, by
    show K (R.π (F.centre α.chart)) ≤ F.δ
    rw [(F.chart α.chart).loss_center]
    exact F.δ_pos.le⟩

/-- Without pieces, the part of `W` near the zeros of `K` is null. -/
theorem exists_volume_sublevel_eq_zero [IsEmpty F.Piece] (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) :
    ∃ δ > 0, volume (W ∩ {w | K w ≤ δ}) = 0 := by
  rcases isEmpty_or_nonempty R.M with hM | hM
  · refine ⟨1, one_pos, ?_⟩
    have : W = ∅ := by
      refine eq_empty_of_forall_notMem fun w hw ↦ ?_
      have := R.W_subset_U hw
      rw [← R.range_π] at this
      obtain ⟨z, -⟩ := this
      exact isEmptyElim z
    simp [this]
  obtain ⟨δ, hδ, -, hae⟩ := exists_ae_mem_sublevel (F := F) hW hKc hK
  refine ⟨δ, hδ, measure_eq_zero_iff_ae_notMem.mpr ?_⟩
  filter_upwards [hae] with w hw hmem
  exact isEmptyElim (nonempty_piece_of_mem_sublevel (hw hmem.1 hmem.2)).some

/-- **The singularity type of a chart family**: with a partition of unity equal to `1` at the
centre of the chart of an essential piece, the weight of that piece is positive at its origin,
so the atlas of the pieces is nondegenerate and its `(λ, m)` is the singularity type. -/
theorem exists_isSingularityType [Nonempty R.M] [Nonempty F.Piece] (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφc : ContinuousOn φ W) :
    ∃ (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
      (hρ : ρ.IsSubordinate fun i ↦ (F.chart i).openCube),
      IsSingularityType K φ W (toResolutionAtlas ρ hρ hW hKc hK hφc).rlct
        (toResolutionAtlas ρ hρ hW hKc hK hφc).mult := by
  classical
  obtain ⟨ρ₀, hρ₀⟩ := F.exists_partitionOfUnity' hW.isClosed hKc
  set A₀ := toResolutionAtlas ρ₀ hρ₀ hW hKc hK hφc
  -- an essential piece
  obtain ⟨α, hα, hαeq⟩ := Finset.exists_mem_eq_sup'
    (ResolutionAtlas.minimalCharts_nonempty A₀) A₀.chartMult
  have hess : A₀.IsEssential α := ⟨(Finset.mem_filter.mp hα).2, by rw [ResolutionAtlas.mult, hαeq]⟩
  obtain ⟨ρ, hρ, h1⟩ := F.exists_partitionOfUnity_eq_one hW.isClosed hKc α.chart
  set A := toResolutionAtlas ρ hρ hW hKc hK hφc
  have hessA : A.IsEssential α := hess
  have hw : 0 < A.weight α 0 := by
    change 0 < ρ α.chart (α.point 0) * α.densityUnit 0
    rw [α.point_zero, h1 (center_mem_sublevel α), one_mul]
    exact (F.chart α.chart).densityUnit_pos _ (by
      rw [reflectOrthant_zero]; exact (F.chart α.chart).zero_mem_target)
  let N : NondegenerateResolutionAtlas K φ W :=
    { A with traceMass_pos := ⟨α, hessA, A.essentialTraceMass_pos_of_weight_pos α hw⟩ }
  refine ⟨ρ, hρ, ?_⟩
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  have hagree : ∀ w ∈ W, K w = W.piecewise K 0 w := fun w hw ↦
    (Set.piecewise_eq_of_mem W _ _ hw).symm
  have hKm : Measurable (W.piecewise K 0) :=
    ContinuousOn.measurable_piecewise hKc continuousOn_const hWm
  exact ((N.congr hagree).isSingularityType hWm hKm hφ (hφc.aemeasurable hWm)).congr
    fun w hw ↦ (hagree w hw).symm

/-! ## One more chart -/

/-- The chart family `F` with the chart `C` added. -/
@[expose] def insert (F : R.ChartFamily) {z : R.M} (C : R.Chart z) : R.ChartFamily where
  ι := Option F.ι
  centre i := i.elim z F.centre
  chart i := match i with
    | none => C
    | some i => F.chart i
  δ := F.δ
  δ_pos := F.δ_pos
  covers y hy hK := by
    obtain ⟨i, hi⟩ := F.covers y hy hK
    exact ⟨some i, hi⟩

/-- A piece of `F` is a piece of `F` with one more chart. -/
@[expose] def Piece.toInsert {z : R.M} (C : R.Chart z) (α : F.Piece) : (F.insert C).Piece :=
  ⟨some α.chart, α.orthant, α.admissible⟩

/-- An admissible orthant of the added chart is a piece of the extended family. -/
@[expose] def insertPiece {z : R.M} (C : R.Chart z) {s : Fin d → Bool} (hs : C.IsAdmissible s) :
    (F.insert C).Piece :=
  ⟨none, s, hs⟩


/-! ## Coverage of a regular parameter set -/

/-- Over a compact `W`, every point of `closure (interior W)` lies under the resolved parameter
set: `π` maps the compact `W̃ ∩ π⁻¹(W)` onto a closed set containing `interior W`. -/
theorem _root_.SingularLearningTheory.SLTResolution.exists_mem_resolvedParameterSet
    (R : SLTResolution K φ W) (hW : IsCompact W) {w : Fin d → ℝ}
    (hw : w ∈ closure (interior W)) : ∃ z ∈ R.resolvedParameterSet, R.π z = w := by
  set C := R.resolvedParameterSet ∩ R.π ⁻¹' W
  have hC : IsCompact C := (R.proper W R.W_subset_U hW).of_isClosed_subset
    (R.isClosed_resolvedParameterSet.inter (hW.isClosed.preimage R.continuous_π))
    inter_subset_right
  have hcl : IsClosed (R.π '' C) := (hC.image R.continuous_π).isClosed
  have hsub : interior W ⊆ R.π '' C := by
    intro w' hw'
    have : w' ∈ range R.π := R.range_π ▸ R.W_subset_U (interior_subset hw')
    obtain ⟨z, rfl⟩ := this
    exact ⟨z, ⟨subset_closure hw', (interior_subset hw' : R.π z ∈ W)⟩, rfl⟩
  obtain ⟨z, hz, rfl⟩ := closure_minimal hsub hcl hw
  exact ⟨z, hz.1, rfl⟩

/-- Over a regular compact `W = closure (interior W)`, every point of `W ∩ {K ≤ δ}` is the image
of a point of the cube of a piece. -/
theorem exists_piece_map_eq (hW : IsCompact W) (hWreg : W = closure (interior W))
    {w : Fin d → ℝ} (hw : w ∈ W) (hK : K w ≤ F.δ) :
    ∃ α : F.Piece, ∃ u ∈ cube d α.radius, α.map u = w := by
  obtain ⟨z, hz, rfl⟩ := R.exists_mem_resolvedParameterSet hW (hWreg ▸ hw)
  obtain ⟨i, hi⟩ := F.covers z hz hK
  obtain ⟨s, hs, u, hu, huz⟩ := R.exists_admissible_of_mem (F.chart i) hz hi
  exact ⟨⟨i, s, hs⟩, u, hu, by rw [Piece.map, Piece.point, huz]⟩

/-! ## The prior-free atlas -/

/-- **The prior-free atlas of the pieces**: the piece maps with weights `0` and localization `1`,
for the prior `0`. The transport identity is `0 = 0`. It carries the chart data of the pieces to
the theorems that do not involve the prior. -/
@[expose] noncomputable def toZeroAtlas (F : R.ChartFamily) (hW : IsClosed W) [Nonempty F.Piece] :
    ResolutionAtlas K 0 W where
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
    exact α.map_mem hW hu
  monomial α u hu := by
    rw [α.extMap_eq (α.cube_subset_domain hu)]
    exact α.loss_map hu
  weight _ _ := 0
  weight_nonneg _ _ _ := le_rfl
  weight_contDiffOn _ := contDiffOn_const
  χ _ := 1
  χ_measurable := measurable_const
  χ_nonneg _ := zero_le_one
  χ_le_one _ := le_rfl
  δ := F.δ
  δ_pos := F.δ_pos
  χ_eq_one _ _ _ := rfl
  transport := by simp

end ChartFamily

end SLTResolution

end SingularLearningTheory
