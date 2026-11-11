/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Geometry.Manifold.ContMDiff.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# `C^n` maps into open subsets, and analytic functions read in charts

A map into an open subset `U` of a manifold is `C^n` within a set at a point exactly when its
composite with the inclusion of `U` is (`contMDiffWithinAt_subtypeVal_comp_iff'`; Mathlib states
it for `n = ∞`). An analytic function on a manifold modelled on a normed space, read in the chart
at a point, is analytic there (`ContMDiffAt.analyticAt_comp_chartAt_symm`).
-/

public section

open Set Filter Topology
open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E E' H H' : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H]
  [TopologicalSpace H'] {I : ModelWithCorners 𝕜 E H} {I' : ModelWithCorners 𝕜 E' H'}
  {M M' : Type*} [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M']
  [ChartedSpace H' M'] {n : WithTop ℕ∞}

/-- A map into an open subset `U` of `M'` is `C^n` within `s` at `x` exactly when its composite
with the inclusion of `U` is. -/
theorem contMDiffWithinAt_subtypeVal_comp_iff' (U : TopologicalSpace.Opens M') (f : M → U)
    (s : Set M) (x : M) :
    ContMDiffWithinAt I I' n (Subtype.val ∘ f) s x ↔ ContMDiffWithinAt I I' n f s x :=
  ChartedSpace.liftPropWithinAt_subtypeVal_comp_iff ..

/-- An analytic function on a manifold modelled on a real normed space, read in the chart at `x`,
is analytic at the image of `x`. -/
theorem ContMDiffAt.analyticAt_comp_chartAt_symm {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {M : Type*} [TopologicalSpace M]
    [ChartedSpace E M] {u : M → F} {x : M} (hu : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, F) ω u x) :
    AnalyticAt ℝ (u ∘ (chartAt E x).symm) (chartAt E x x) := by
  have h := (contMDiffAt_iff.1 hu).2
  simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp,
    extChartAt_coe, extChartAt_coe_symm, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, range_id, contDiffWithinAt_univ] at h
  exact h.analyticAt
