/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.LinearAlgebra.Determinant

/-!
# Injectivity where the derivative is invertible

Let `f` be injective on the part `s ∩ f ⁻¹' t` of an open set `s` that it maps into `t`, and let
every value of `f` on `s` lie in the closure of `t`. Then `f` is injective on the points of `s`
at which it has a surjective strict derivative: two such points `x ≠ y` with `f x = f y` have
disjoint neighbourhoods whose images are both neighbourhoods of `f x` (the inverse function
theorem in the form `HasStrictFDerivAt.map_nhds_eq_of_surj`), so both images contain a common
point of `t`, whose two preimages contradict injectivity on `s ∩ f ⁻¹' t`.

## Main results

* `Set.InjOn.eq_of_hasStrictFDerivAt`: the two-point statement.
* `Set.InjOn.injOn_det_fderiv_ne_zero`: for a continuously differentiable self-map of a
  finite-dimensional space, injectivity on the points of `s` where the Jacobian determinant does
  not vanish.
-/

public section

open Set Filter
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- If `f` is injective on `s ∩ f ⁻¹' t` for an open `s`, two points of `s` at which `f` has
surjective strict derivatives and whose common value lies in the closure of `t` coincide. -/
theorem Set.InjOn.eq_of_hasStrictFDerivAt {f : E → F} {s : Set E} {t : Set F}
    (hinj : InjOn f (s ∩ f ⁻¹' t)) (hs : IsOpen s) {x y : E} (hx : x ∈ s) (hy : y ∈ s)
    {f'x f'y : E →L[ℝ] F} (hfx : HasStrictFDerivAt f f'x x) (hf'x : (f'x : E →ₗ[ℝ] F).range = ⊤)
    (hfy : HasStrictFDerivAt f f'y y) (hf'y : (f'y : E →ₗ[ℝ] F).range = ⊤) (hxy : f x = f y)
    (hcl : f x ∈ closure t) : x = y := by
  by_contra hne
  obtain ⟨u, v, hu, hv, huv⟩ := t2_separation_nhds hne
  have hA : f '' (u ∩ s) ∈ 𝓝 (f x) := by
    rw [← hfx.map_nhds_eq_of_surj hf'x]
    exact image_mem_map (inter_mem hu (hs.mem_nhds hx))
  have hB : f '' (v ∩ s) ∈ 𝓝 (f x) := by
    rw [hxy, ← hfy.map_nhds_eq_of_surj hf'y]
    exact image_mem_map (inter_mem hv (hs.mem_nhds hy))
  obtain ⟨z, ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩, hzt⟩ := mem_closure_iff_nhds.mp hcl _ (inter_mem hA hB)
  have hab : b = a := hinj ⟨hb.2, by rw [mem_preimage, hba]; exact hzt⟩ ⟨ha.2, hzt⟩ hba
  exact huv.ne_of_mem ha.1 hb.1 hab.symm

/-- A continuously differentiable self-map of a finite-dimensional space that is injective on
`s ∩ f ⁻¹' t` for an open `s`, and maps `s` into the closure of `t`, is injective on the points of
`s` where its Jacobian determinant does not vanish. -/
theorem Set.InjOn.injOn_det_fderiv_ne_zero [FiniteDimensional ℝ E] {f : E → E} {s t : Set E}
    (hinj : InjOn f (s ∩ f ⁻¹' t)) (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (hcl : MapsTo f s (closure t)) : InjOn f {x | x ∈ s ∧ (fderiv ℝ f x).det ≠ 0} := by
  have hstrict : ∀ x ∈ s, HasStrictFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    (hf.contDiffAt (hs.mem_nhds hx)).hasStrictFDerivAt one_ne_zero
  have hsurj : ∀ x, (fderiv ℝ f x).det ≠ 0 → ((fderiv ℝ f x : E →L[ℝ] E) : E →ₗ[ℝ] E).range = ⊤ :=
    fun x hx => LinearMap.range_eq_top.mpr ((Module.End.isUnit_iff _).mp
      ((LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hx))).2
  intro x hx y hy hxy
  exact hinj.eq_of_hasStrictFDerivAt hs hx.1 hy.1 (hstrict x hx.1) (hsurj x hx.2)
    (hstrict y hy.1) (hsurj y hy.2) hxy (hcl hx.1)
