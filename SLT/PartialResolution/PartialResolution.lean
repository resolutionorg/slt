/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Partial resolutions of a function on a compact set

The induction unit of the resolution of a function by blow-ups: a **partial resolution of a
function `F` on a compact set `K ⊆ ℝ^n`** is a finite family of charts `φ i`, each defined and
smooth on an open neighborhood of a compact domain `dom i`, with images inside `K` covering `K`
up to a set of measure zero, each injective with nonvanishing Jacobian off a closed null
exceptional set `E i` carried by the chart, and the family of finite multiplicity off a null
set. Each chart carries the pulled-back density `(ρ ∘ φ i) · |det D(φ i)|` (`pullbackDensity`, a
derived formula — the ambient density `ρ` varies over uses).

The domains are not required to be boxes: the coordinate changes of the resolution are shears, a
shear's one-chart refinement of a box `B` must live on the warped box `τ ⁻¹' B`, and the blow-up
charts refining a warped region must be clipped to it. All the definition needs — and all the
change-of-variables and composition proofs use — is compactness of the domains together with
smoothness on an open neighborhood; the boxes reappear as the special shape of the blow-up chart
domains. The containment clause `mapsTo` (images inside `K`) is the
box-relative form of the requirement that chart images stay in a fixed compact neighborhood;
composition (`Composition`) needs it so that composite charts stay where the outer chart is
smooth.

The **centered instance** is the special case `CenteredPartialResolution`: `K` a compact
neighborhood of a base point `w`, every chart domain containing the origin, every chart sending
the origin to `w`.

The change-of-variables identity is *derived* from this definition in `ChangeOfVariables` — the
transport predicate `TransportsToOn`, which the chart-family read-off uses, is supplied there,
not assumed here.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal Topology

namespace Analytic

/-- **A partial resolution.** A partial resolution of a
function `F` on a compact set `K ⊆ ℝ^n`: finitely many charts on compact
domains, each smooth on an open neighborhood of its domain, with images inside
`K` covering `K` up to a null set, each injective with nonvanishing Jacobian
off a closed null exceptional set carried by the chart, and the family of
finite multiplicity off a null set. The function `F` being resolved is a
parameter so that refinement statements (`Composition`) read naturally:
a chart `i` is refined by a partial resolution of the pulled-back function
`F ∘ φ i` on that chart's domain. -/
structure PartialResolution (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (K : Set (Fin n → ℝ)) where
  /-- The set being resolved is compact. -/
  K_compact : IsCompact K
  /-- The chart index. -/
  ι : Type
  /-- The chart family is finite. -/
  [fin : Fintype ι]
  /-- The chart domains ("boxes" in the blow-up instances). -/
  dom : ι → Set (Fin n → ℝ)
  dom_compact : ∀ i, IsCompact (dom i)
  /-- The chart maps. -/
  φ : ι → (Fin n → ℝ) → (Fin n → ℝ)
  /-- Each chart is smooth on an open neighborhood of its domain. -/
  smooth : ∀ i, ∃ U, IsOpen U ∧ dom i ⊆ U ∧ ContDiffOn ℝ (⊤ : ℕ∞) (φ i) U
  /-- Chart images lie in `K`: the images stay in a fixed compact neighborhood, in
  box-relative form; composition needs it. -/
  mapsTo : ∀ i, MapsTo (φ i) (dom i) K
  /-- The chart images cover `K` up to a set of measure zero. -/
  cover : volume (K \ ⋃ i, φ i '' dom i) = 0
  /-- The per-chart exceptional sets. -/
  E : ι → Set (Fin n → ℝ)
  /-- Each exceptional set is carried by its chart. -/
  E_subset : ∀ i, E i ⊆ dom i
  E_closed : ∀ i, IsClosed (E i)
  E_null : ∀ i, volume (E i) = 0
  /-- Each chart is injective off its exceptional set. -/
  inj : ∀ i, InjOn (φ i) (dom i \ E i)
  /-- Each chart has nonvanishing Jacobian off its exceptional set. -/
  jac_ne_zero : ∀ i, ∀ x ∈ dom i \ E i, (fderiv ℝ (φ i) x).det ≠ 0
  /-- The multiplicity bound of the family. -/
  mult : ℕ
  /-- The null set off which the multiplicity bound holds. -/
  multN : Set (Fin n → ℝ)
  multN_null : volume multN = 0
  /-- Off the null set, every point of `K` has at most `mult` preimages across
  the whole chart family. -/
  mult_bound : ∀ y ∈ K \ multN,
    {p : ι × (Fin n → ℝ) | p.2 ∈ dom p.1 ∧ φ p.1 p.2 = y}.encard ≤ mult

attribute [instance] PartialResolution.fin

namespace PartialResolution

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {K : Set (Fin n → ℝ)}

/-- Charts are smooth at every point of their domain. -/
theorem contDiffAt (R : PartialResolution n F K) (i : R.ι) {x : Fin n → ℝ}
    (hx : x ∈ R.dom i) : ContDiffAt ℝ (⊤ : ℕ∞) (R.φ i) x := by
  obtain ⟨U, hU, hsub, hsm⟩ := R.smooth i
  exact (hsm x (hsub hx)).contDiffAt (hU.mem_nhds (hsub hx))

/-- Charts are differentiable at every point of their domain. -/
theorem differentiableAt (R : PartialResolution n F K) (i : R.ι)
    {x : Fin n → ℝ} (hx : x ∈ R.dom i) :
    DifferentiableAt ℝ (R.φ i) x :=
  (R.contDiffAt i hx).differentiableAt (by simp)

/-- Charts are continuous on their domain. -/
theorem continuousOn (R : PartialResolution n F K) (i : R.ι) :
    ContinuousOn (R.φ i) (R.dom i) := fun _ hx =>
  (R.contDiffAt i hx).continuousAt.continuousWithinAt

/-- Chart domains are measurable. -/
theorem dom_measurable (R : PartialResolution n F K) (i : R.ι) :
    MeasurableSet (R.dom i) :=
  (R.dom_compact i).isClosed.measurableSet

/-- Chart domains have finite volume. -/
theorem volume_dom_lt_top (R : PartialResolution n F K) (i : R.ι) :
    volume (R.dom i) < ∞ :=
  (R.dom_compact i).measure_lt_top

/-- Chart images are compact. -/
theorem image_compact (R : PartialResolution n F K) (i : R.ι) :
    IsCompact (R.φ i '' R.dom i) :=
  (R.dom_compact i).image_of_continuousOn (R.continuousOn i)

/-- The set being resolved is measurable. -/
theorem K_measurable (R : PartialResolution n F K) : MeasurableSet K :=
  R.K_compact.isClosed.measurableSet

/-- The set being resolved has finite volume. -/
theorem volume_K_lt_top (R : PartialResolution n F K) : volume K < ∞ :=
  R.K_compact.measure_lt_top

/-- The absolute Jacobian of a chart. -/
noncomputable def jacAbs (R : PartialResolution n F K) (i : R.ι) :
    (Fin n → ℝ) → ℝ :=
  fun x => |(fderiv ℝ (R.φ i) x).det|

/-- The absolute Jacobian as an `ℝ≥0∞`-density. -/
noncomputable def jacDensity (R : PartialResolution n F K) (i : R.ι) :
    (Fin n → ℝ) → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (R.jacAbs i x)

/-- The Jacobian density is measurable: the full derivative of a fixed
function is a measurable function of the point, and determinant, absolute
value, and `ENNReal.ofReal` are continuous. -/
theorem jacDensity_measurable (R : PartialResolution n F K) (i : R.ι) :
    Measurable (R.jacDensity i) := by
  unfold jacDensity jacAbs
  exact ((ContinuousLinearMap.continuous_det.measurable.comp
    (measurable_fderiv ℝ (R.φ i))).abs).ennreal_ofReal

/-- **The pulled-back density carried by a chart**: the ambient density `ρ`
pulled back through the chart and weighted by the absolute Jacobian,
`(ρ ∘ φ i) · |det D(φ i)|`. -/
noncomputable def pullbackDensity (R : PartialResolution n F K)
    (ρ : (Fin n → ℝ) → ℝ≥0∞) (i : R.ι) : (Fin n → ℝ) → ℝ≥0∞ :=
  fun x => ρ (R.φ i x) * R.jacDensity i x

/-- The Jacobian of a chart does not vanish off the exceptional set, so the
Jacobian density is strictly positive there. -/
theorem jacDensity_pos (R : PartialResolution n F K) (i : R.ι)
    {x : Fin n → ℝ} (hx : x ∈ R.dom i \ R.E i) :
    0 < R.jacDensity i x := by
  have h := R.jac_ne_zero i x hx
  simpa [jacDensity, jacAbs, ENNReal.ofReal_pos] using abs_pos.mpr h

end PartialResolution

/-- **The centered instance.** A partial resolution of `F` at the base point `w`:
a partial resolution of `F` on a compact neighborhood `K` of `w` all of whose charts
are centered at `w` — the origin belongs to every chart domain and every chart sends
it to `w`.
Images lie in the fixed compact neighborhood `K` by the `mapsTo` clause of the
underlying partial resolution. -/
structure CenteredPartialResolution (n : ℕ) (F : (Fin n → ℝ) → ℝ)
    (w : Fin n → ℝ) where
  /-- The compact neighborhood of the base point on which `F` is resolved. -/
  K : Set (Fin n → ℝ)
  K_nbhd : K ∈ 𝓝 w
  /-- The underlying partial resolution of `F` on `K`. -/
  toPartialResolution : PartialResolution n F K
  /-- Every chart domain contains the origin. -/
  center_mem : ∀ i, (0 : Fin n → ℝ) ∈ toPartialResolution.dom i
  /-- Every chart sends the origin to the base point. -/
  center_map : ∀ i, toPartialResolution.φ i 0 = w

namespace CenteredPartialResolution

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ}

/-- The base point lies in the compact neighborhood. -/
theorem w_mem_K (C : CenteredPartialResolution n F w) : w ∈ C.K :=
  mem_of_mem_nhds C.K_nbhd

/-- The base point is in the image of every chart. -/
theorem w_mem_image (C : CenteredPartialResolution n F w)
    (i : C.toPartialResolution.ι) :
    w ∈ C.toPartialResolution.φ i '' C.toPartialResolution.dom i :=
  ⟨0, C.center_mem i, C.center_map i⟩

end CenteredPartialResolution

end Analytic
