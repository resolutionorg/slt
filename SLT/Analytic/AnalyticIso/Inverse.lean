/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.Analytic.AnalyticIso.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
import Hironaka.Analytic.Calculus.Det
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-!
# The analytic inverse function theorem over `K = ℝ` or `ℂ`

On a finite-dimensional normed space `E` over `𝕜` (`[RCLike 𝕜]`), a local analytic isomorphism
at `a` (`IsLocalAnalyticIsoAt`: analytic with invertible derivative) is the restriction of an
open partial homeomorphism `e` with `a` in its source and `⇑e = f`, `f` analytic with invertible
derivative on the source and `e.symm` analytic with invertible derivative on the target. The
proof assembles Mathlib's inverse function theorem: the strict derivative from analyticity
(`AnalyticAt.hasStrictFDerivAt`), the local homeomorphism
(`HasStrictFDerivAt.toOpenPartialHomeomorph`), the shrink by `restrOpen` to the open set where
`f` is analytic with invertible derivative (`AnalyticAt.eventually_analyticAt`; the invertible
endomorphisms of a Banach space are the units of `E →L[𝕜] E`, an open set, `Units.isOpen`), the
analyticity of the inverse (`OpenPartialHomeomorph.analyticAt_symm'`, from the formal inverse
series) and its derivative (`OpenPartialHomeomorph.hasFDerivAt_symm`). On `Fin n → 𝕜`
invertibility is `det ≠ 0` (`LinearMap.equivOfDetNeZero`, `LinearEquiv.isUnit_det'`). The charts
of an analytic manifold are extended with this theorem (`Hironaka/Manifold/Chart`). The sources
invoke the theorem without proof ("by the implicit function theorem", [BM97, §1]; [Hir64,
Chapter 0, §1, p. 121]).
-/

public section

namespace Analytic

open Filter Topology

variable {𝕜 : Type} [RCLike 𝕜] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- An endomorphism of a normed space is invertible iff it is a unit of `E →L[𝕜] E`. -/
theorem _root_.ContinuousLinearMap.isInvertible_iff_isUnit (L : E →L[𝕜] E) :
    L.IsInvertible ↔ IsUnit L := by
  constructor
  · rintro ⟨A, rfl⟩
    exact A.toUnit.isUnit
  · intro h
    exact ⟨ContinuousLinearEquiv.ofUnit h.unit, rfl⟩

/-- The invertible endomorphisms of a Banach space form an open set. -/
theorem _root_.ContinuousLinearMap.isOpen_setOf_isInvertible [CompleteSpace E] :
    IsOpen {L : E →L[𝕜] E | L.IsInvertible} := by
  simp only [ContinuousLinearMap.isInvertible_iff_isUnit]
  exact Units.isOpen

/-- On a finite-dimensional space, invertible means nonzero determinant. -/
theorem _root_.ContinuousLinearMap.isInvertible_iff_det_ne_zero [FiniteDimensional 𝕜 E]
    (L : E →L[𝕜] E) :
    L.IsInvertible ↔ L.det ≠ 0 := by
  constructor
  · rintro ⟨A, rfl⟩
    exact (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  · intro hdet
    refine ⟨(LinearMap.equivOfDetNeZero (L : E →ₗ[𝕜] E) hdet).toContinuousLinearEquiv, ?_⟩
    ext x
    rfl

/-- On `Fin n → 𝕜` a local analytic isomorphism at `a` is an analytic map with nonzero Jacobian
determinant at `a`. -/
theorem isLocalAnalyticIsoAt_iff_det_ne_zero {n : ℕ} (f : (Fin n → 𝕜) → (Fin n → 𝕜))
    (a : Fin n → 𝕜) : IsLocalAnalyticIsoAt 𝕜 f a ↔ AnalyticAt 𝕜 f a ∧ (fderiv 𝕜 f a).det ≠ 0 :=
  and_congr_right fun _ => ContinuousLinearMap.isInvertible_iff_det_ne_zero _

theorem IsLocalAnalyticIsoAt.det_ne_zero {n : ℕ} {f : (Fin n → 𝕜) → (Fin n → 𝕜)} {a : Fin n → 𝕜}
    (h : IsLocalAnalyticIsoAt 𝕜 f a) : (fderiv 𝕜 f a).det ≠ 0 :=
  ((isLocalAnalyticIsoAt_iff_det_ne_zero f a).1 h).2

theorem IsLocalAnalyticIsoAt.of_det_ne_zero {n : ℕ} {f : (Fin n → 𝕜) → (Fin n → 𝕜)}
    {a : Fin n → 𝕜} (hf : AnalyticAt 𝕜 f a) (h : (fderiv 𝕜 f a).det ≠ 0) :
    IsLocalAnalyticIsoAt 𝕜 f a :=
  (isLocalAnalyticIsoAt_iff_det_ne_zero f a).2 ⟨hf, h⟩

/-- The analytic inverse function theorem over `𝕜` on a finite-dimensional `E`: a local analytic
isomorphism at `a` is the restriction of an open partial homeomorphism `e` with `a` in its source
and `⇑e = f`, `f` analytic with invertible derivative on the source, `e.symm` analytic with
invertible derivative on the target. -/
theorem IsLocalAnalyticIsoAt.exists_openPartialHomeomorph [FiniteDimensional 𝕜 E] {f : E → E}
    {a : E} (h : IsLocalAnalyticIsoAt 𝕜 f a) :
    ∃ e : OpenPartialHomeomorph E E, a ∈ e.source ∧ (⇑e = f) ∧ AnalyticOnNhd 𝕜 f e.source ∧
      (∀ x ∈ e.source, (fderiv 𝕜 f x).IsInvertible) ∧ AnalyticOnNhd 𝕜 e.symm e.target ∧
      ∀ y ∈ e.target, (fderiv 𝕜 e.symm y).IsInvertible := by
  have : CompleteSpace E := FiniteDimensional.complete 𝕜 E
  obtain ⟨hf, hinv⟩ := h
  obtain ⟨L, hL⟩ := id hinv
  have hstrict : HasStrictFDerivAt f (L : E →L[𝕜] E) a := by
    rw [hL]
    exact hf.hasStrictFDerivAt
  have hev : ∀ᶠ x in 𝓝 a, AnalyticAt 𝕜 f x ∧ (fderiv 𝕜 f x).IsInvertible :=
    hf.eventually_analyticAt.and
      (hf.fderiv.continuousAt.preimage_mem_nhds
        (ContinuousLinearMap.isOpen_setOf_isInvertible.mem_nhds hinv))
  obtain ⟨t, ht, htopen, hat⟩ := eventually_nhds_iff.mp hev
  set e := (HasStrictFDerivAt.toOpenPartialHomeomorph f hstrict).restrOpen t htopen with he
  have hcoe : ⇑e = f := hstrict.toOpenPartialHomeomorph_coe
  have hsrc : e.source = (HasStrictFDerivAt.toOpenPartialHomeomorph f hstrict).source ∩ t :=
    OpenPartialHomeomorph.restrOpen_source _ t htopen
  have ha : a ∈ e.source := by
    rw [hsrc]
    exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hat⟩
  have hfs : AnalyticOnNhd 𝕜 f e.source := fun x hx => by
    rw [hsrc] at hx
    exact (ht x hx.2).1
  have hinvs : ∀ x ∈ e.source, (fderiv 𝕜 f x).IsInvertible := fun x hx => by
    rw [hsrc] at hx
    exact (ht x hx.2).2
  refine ⟨e, ha, hcoe, hfs, hinvs, ?_, ?_⟩
  · intro y hy
    have hx : e.symm y ∈ e.source := e.map_target hy
    obtain ⟨A, hA⟩ := hinvs _ hx
    have := e.analyticAt_symm' hx (by rw [hcoe]; exact hfs _ hx) (by rw [hcoe]; exact hA.symm)
    rwa [e.right_inv hy] at this
  · intro y hy
    have hx : e.symm y ∈ e.source := e.map_target hy
    obtain ⟨A, hA⟩ := hinvs _ hx
    have hd : HasFDerivAt (⇑e) (A : E →L[𝕜] E) (e.symm y) := by
      rw [hcoe, hA]
      exact (hfs _ hx).differentiableAt.hasFDerivAt
    rw [(e.hasFDerivAt_symm hy hd).fderiv]
    exact ContinuousLinearMap.isInvertible_equiv

end Analytic

/-! ### The real case -/

open Set
open scoped Topology

namespace Analytic

variable {n : ℕ}

/-- A continuous linear map of `ℝ^n` with nonzero determinant is a continuous linear equivalence
(`LinearMap.equivOfDetNeZero`). -/
theorem _root_.ContinuousLinearMap.exists_continuousLinearEquiv_eq_of_det_ne_zero
    (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hA : A.det ≠ 0) :
    ∃ L : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ), (L : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = A := by
  refine ⟨(LinearMap.equivOfDetNeZero (A : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    hA).toContinuousLinearEquiv, ?_⟩
  apply ContinuousLinearMap.coe_injective
  simp [LinearMap.equivOfDetNeZero]

/-- The Jacobians of a local homeomorphism and of its inverse multiply to `1` where both are
differentiable (chain rule on `e.symm ∘ e = id` near a source point). -/
theorem _root_.OpenPartialHomeomorph.det_fderiv_symm_mul_det_fderiv
    (e : OpenPartialHomeomorph (Fin n → ℝ) (Fin n → ℝ))
    {x : Fin n → ℝ} (hx : x ∈ e.source) (hd : DifferentiableAt ℝ e x)
    (hd' : DifferentiableAt ℝ e.symm (e x)) :
    (fderiv ℝ e.symm (e x)).det * (fderiv ℝ e x).det = 1 := by
  have hcomp : HasFDerivAt (⇑e.symm ∘ ⇑e) (fderiv ℝ e.symm (e x) ∘L fderiv ℝ e x) x :=
    hd'.hasFDerivAt.comp x hd.hasFDerivAt
  have hid : HasFDerivAt (id : (Fin n → ℝ) → (Fin n → ℝ))
      (fderiv ℝ e.symm (e x) ∘L fderiv ℝ e x) x :=
    hcomp.congr_of_eventuallyEq ((e.eventually_left_inverse hx).mono fun y hy => hy.symm)
  have heq := hid.unique (hasFDerivAt_id x)
  rw [← det_clm_comp, heq]
  simp [ContinuousLinearMap.det]

end Analytic
