/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Changing the model space of a manifold by a linear equivalence

A manifold `M` modelled on a normed space `E` is also modelled on any normed space `F` linearly
equivalent to `E`: compose every chart with `L : E ≃L[𝕜] F`
(`ChartedSpace.transContinuousLinearEquiv`). The transition maps change by conjugation with `L`, so
`M` stays a `C^n` manifold (`ChartedSpace.isManifold_transContinuousLinearEquiv`), and the identity
of `M` is `C^n` from either structure to the other
(`ChartedSpace.contMDiff_id_transContinuousLinearEquiv`,
`ChartedSpace.contMDiff_id_transContinuousLinearEquiv_symm`), so that a map is `C^n` for one
structure exactly when it is for the other.

## Main definitions

* `ChartedSpace.transContinuousLinearEquiv L M`: the charts of `M` composed with `L`.
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F] (L : E ≃L[𝕜] F)
  (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

namespace ChartedSpace

/-- The manifold `M` modelled on `F` instead of `E`: its charts composed with `L : E ≃L[𝕜] F`. -/
@[expose, instance_reducible]
def transContinuousLinearEquiv : ChartedSpace F M where
  atlas := (fun e ↦ e.transHomeomorph L.toHomeomorph) '' atlas E M
  chartAt x := (chartAt E x).transHomeomorph L.toHomeomorph
  mem_chart_source x := mem_chart_source E x
  chart_mem_atlas x := mem_image_of_mem _ (chart_mem_atlas E x)

variable {M}

theorem chartAt_transContinuousLinearEquiv (x : M) :
    (letI := transContinuousLinearEquiv L M; chartAt F x) =
      (chartAt E x).transHomeomorph L.toHomeomorph :=
  (rfl)

/-- The model space changed by a linear equivalence keeps the `C^n` structure: a transition map of
the new atlas is `L ∘ τ ∘ L⁻¹` for a transition map `τ` of the old one. -/
theorem isManifold_transContinuousLinearEquiv {n : ℕ∞ω} [IsManifold 𝓘(𝕜, E) n M] :
    letI := transContinuousLinearEquiv L M
    IsManifold 𝓘(𝕜, F) n M := by
  let := transContinuousLinearEquiv L M
  refine isManifold_of_contDiffOn 𝓘(𝕜, F) n M fun e' f' he' hf' ↦ ?_
  obtain ⟨e, he, rfl⟩ := he'
  obtain ⟨f, hf, rfl⟩ := hf'
  have hτ : ContDiffOn 𝕜 n (e.symm ≫ₕ f) (e.symm ≫ₕ f).source := by
    have h := (contDiffGroupoid n 𝓘(𝕜, E)).compatible (M := M) he hf
    simp only [contDiffGroupoid, mem_groupoid_of_pregroupoid, contDiffPregroupoid,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
      inter_univ, Function.comp_id, Function.id_comp] at h
    exact h.1
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.comp_id, Function.id_comp]
  refine ((L.contDiff.comp_contDiffOn hτ).comp L.symm.contDiff.contDiffOn ?_).congr ?_
  · intro y hy
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.transHomeomorph_target, OpenPartialHomeomorph.transHomeomorph_source,
      mem_inter_iff, mem_preimage,
      OpenPartialHomeomorph.transHomeomorph_symm_apply, Function.comp_apply] at hy ⊢
    exact hy
  · intro y _
    simp [OpenPartialHomeomorph.transHomeomorph_symm_apply]

variable {n : ℕ∞ω}

/-- The identity of `M` is `C^n` from the structure modelled on `E` to the one modelled on `F`: in
charts it is `L`. -/
theorem contMDiff_id_transContinuousLinearEquiv :
    letI := transContinuousLinearEquiv L M
    ContMDiff 𝓘(𝕜, E) 𝓘(𝕜, F) n (id : M → M) := by
  let := transContinuousLinearEquiv L M
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  set c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have heq : (extChartAt 𝓘(𝕜, F) x ∘ id ∘ (extChartAt 𝓘(𝕜, E) x).symm) =ᶠ[𝓝 (c x)] L := by
    filter_upwards [c.open_target.mem_nhds hx] with y hy
    simp [chartAt_transContinuousLinearEquiv, c,
      OpenPartialHomeomorph.transHomeomorph_apply, c.right_inv hy]
  simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp, range_id]
  exact (L.contDiff.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

/-- The identity of `M` is `C^n` from the structure modelled on `F` to the one modelled on `E`: in
charts it is `L⁻¹`. -/
theorem contMDiff_id_transContinuousLinearEquiv_symm :
    letI := transContinuousLinearEquiv L M
    ContMDiff 𝓘(𝕜, F) 𝓘(𝕜, E) n (id : M → M) := by
  let := transContinuousLinearEquiv L M
  intro x
  rw [contMDiffAt_iff]
  refine ⟨continuousAt_id, ?_⟩
  set c := chartAt E x
  have hx : c x ∈ c.target := c.map_source (mem_chart_source E x)
  have heq : (extChartAt 𝓘(𝕜, E) x ∘ id ∘ (extChartAt 𝓘(𝕜, F) x).symm) =ᶠ[𝓝 (L (c x))]
      L.symm := by
    have hmem : L.symm ⁻¹' c.target ∈ 𝓝 (L (c x)) :=
      L.symm.continuous.continuousAt.preimage_mem_nhds (by simpa using c.open_target.mem_nhds hx)
    filter_upwards [hmem] with y hy
    simp [chartAt_transContinuousLinearEquiv, c, OpenPartialHomeomorph.transHomeomorph_symm_apply,
      c.right_inv hy]
  have hpt : extChartAt 𝓘(𝕜, F) x x = L (c x) := by
    simp [chartAt_transContinuousLinearEquiv, c, OpenPartialHomeomorph.transHomeomorph_apply]
  simp only [hpt]
  exact (L.symm.contDiff.contDiffAt.congr_of_eventuallyEq heq).contDiffWithinAt

end ChartedSpace
