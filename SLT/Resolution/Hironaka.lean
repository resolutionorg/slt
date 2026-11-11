/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
import SLT.Geometry.Manifold.MaximalAtlas

/-!
# Resolution of singularities of one analytic function

A `Resolution K` is a resolution of the singularities of `K : ℝ^d → ℝ` over an open set `U`, in
the form of [Wat09, Theorem 2.3] and [Hit26, Theorem 3.3.1] for one function: an analytic
`d`-manifold `M`, Hausdorff, with a proper analytic map `π : M → ℝ^d` onto `U` that is an
analytic isomorphism over the points of `U` where `K ≠ 0`, and around every point over a zero of
`K` a chart of the analytic atlas, centred at the point, in which `K ∘ π = ± u^k` and the
Jacobian determinant of `π` is an analytic unit times a monomial.

Its existence over an open set on which `K` is analytic and not identically zero near any point
is `exists_resolution_of_nonzero_germs` (`Resolution/Components.lean`).

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 3.3.1], the conditions on `(V, M, g)` | `Resolution` |
| [Hit26, Equation (3.3.1)] | `Resolution.chart` (`K ∘ π = S u^k`) |
| [Hit26, Equation (3.3.3)] | `Resolution.chart` (the Jacobian determinant) |

## Implementation notes

"Proper" is spelled out as [Hit26] defines it: the preimage of every compact subset of `U` is
compact. The analytic isomorphism over `{K ≠ 0}` is stated as in the hironaka package's
`exists_proper_analytic_monomialization`: `π` is a local analytic diffeomorphism at every point
of `π⁻¹ {K ≠ 0}` and a bijection from it onto `U \ {K = 0}`; the analytic inverse is glued from
the local inverses (`Resolution.exists_contMDiffOn_leftInvOn`). Second countability of `M`
follows from properness (`Resolution.secondCountableTopology`).
-/

public section

open Set
open scoped ContDiff Manifold

namespace SingularLearningTheory

variable {d : ℕ}

/-- A resolution of the singularities of `K` over an open set `U`, in the form of
[Wat09, Theorem 2.3] ([Hit26, Theorem 3.3.1] for one function): a proper analytic map `π` from an
analytic `d`-manifold onto `U`, an analytic isomorphism over `U \ {K = 0}`, with around every
point over a zero of `K` a centred chart of the analytic atlas in which `K ∘ π = ± u^k` and
`det π' = b u^h` with `b` an analytic unit. -/
structure Resolution (K : (Fin d → ℝ) → ℝ) where
  /-- The open set over which `K` is resolved. -/
  U : Set (Fin d → ℝ)
  isOpen_U : IsOpen U
  /-- The resolving manifold, analytic and Hausdorff. -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (Fin d → ℝ) M]
  [isManifold : IsManifold 𝓘(ℝ, Fin d → ℝ) ω M]
  [t2Space : T2Space M]
  /-- The resolution map. -/
  π : M → (Fin d → ℝ)
  analytic_π : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω π
  range_π : range π = U
  /-- `π` is proper: preimages of compact subsets of `U` are compact. -/
  proper : ∀ C ⊆ U, IsCompact C → IsCompact (π ⁻¹' C)
  /-- `π` is a local analytic diffeomorphism over `{K ≠ 0}` … -/
  isLocalDiffeomorphOn :
    IsLocalDiffeomorphOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω π (π ⁻¹' {w | K w ≠ 0})
  /-- … and a bijection from `π⁻¹ {K ≠ 0}` onto `U \ {K = 0}`. -/
  bijOn : BijOn π (π ⁻¹' {w | K w ≠ 0}) (U \ {w | K w = 0})
  /-- At every point `P` over a zero of `K`, a chart `e` of the analytic atlas with `e P = 0` in
  which `K ∘ π = S u^k` with `S = ±1` ([Hit26, Equation (3.3.1)]) and `det π'(u) = b(u) u^h` with
  `b` analytic and nonvanishing ([Hit26, Equation (3.3.3)]). -/
  chart : ∀ P, K (π P) = 0 →
    ∃ e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M, P ∈ e.source ∧ e P = 0 ∧
      ∃ (S : ℝ) (k h : Fin d → ℕ) (b : (Fin d → ℝ) → ℝ),
        (S = 1 ∨ S = -1) ∧
        (∀ u ∈ e.target, K (π (e.symm u)) = S * ∏ j, u j ^ k j) ∧
        AnalyticOnNhd ℝ b e.target ∧ (∀ u ∈ e.target, b u ≠ 0) ∧
        ∀ u ∈ e.target, (fderiv ℝ (π ∘ e.symm) u).det = b u * ∏ j, u j ^ h j

attribute [instance] Resolution.topologicalSpace Resolution.chartedSpace Resolution.isManifold
  Resolution.t2Space

namespace Resolution

variable {K : (Fin d → ℝ) → ℝ} (R : Resolution K)

theorem mem_U (x : R.M) : R.π x ∈ R.U := R.range_π ▸ mem_range_self x

theorem continuous_π : Continuous R.π := R.analytic_π.continuous

/-- The points of `M` over `U \ {K = 0}` are those over `{K ≠ 0}`. -/
theorem preimage_sdiff_zeroSet : R.π ⁻¹' (R.U \ {w | K w = 0}) = R.π ⁻¹' {w | K w ≠ 0} := by
  ext x
  simp [R.mem_U x]

/-- `π` is injective over `{K ≠ 0}`. -/
theorem injOn : InjOn R.π (R.π ⁻¹' {w | K w ≠ 0}) := R.bijOn.injOn

/-- `π` maps `π⁻¹ {K ≠ 0}` onto `U \ {K = 0}`. -/
theorem image_preimage_ne_zero : R.π '' (R.π ⁻¹' {w | K w ≠ 0}) = R.U \ {w | K w = 0} :=
  R.bijOn.image_eq

/-- A copy of `R` with the function, the open set and the map replaced by equal ones, to control
definitional equalities. -/
@[expose] protected def copy {K' : (Fin d → ℝ) → ℝ} (hK : K' = K) (U' : Set (Fin d → ℝ))
    (hU : U' = R.U) (π' : R.M → (Fin d → ℝ)) (hπ : π' = R.π) : Resolution K' where
  U := U'
  isOpen_U := hU ▸ R.isOpen_U
  M := R.M
  π := π'
  analytic_π := by subst hπ; exact R.analytic_π
  range_π := by subst hπ hU; exact R.range_π
  proper := by subst hπ hU; exact R.proper
  isLocalDiffeomorphOn := by subst hK hπ; exact R.isLocalDiffeomorphOn
  bijOn := by subst hK hπ hU; exact R.bijOn
  chart := by subst hK hπ; exact R.chart

/-- `π` has an analytic left inverse over `U \ {K = 0}`, glued from its local inverses: a total
function `ℝ^d → M`, which needs `M ≠ ∅`. -/
theorem exists_contMDiffOn_leftInvOn [Nonempty R.M] :
    ∃ g : (Fin d → ℝ) → R.M,
      ContMDiffOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω g (R.U \ {w | K w = 0}) ∧
        ∀ x ∈ R.π ⁻¹' {w | K w ≠ 0}, g (R.π x) = x := by
  have hloc := R.isLocalDiffeomorphOn
  have hbij := R.bijOn
  rw [← R.preimage_sdiff_zeroSet] at hloc hbij ⊢
  exact hloc.exists_contMDiffOn_leftInvOn hbij

end Resolution

end SingularLearningTheory
