/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLTChallenge.Setting
public import SLTChallenge.SingularIntegrals
public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# Resolution of singularities in the form singular learning theory uses

An `SLTResolution K φ W` is a global resolution of the loss `K` over an open neighbourhood `U`
of the parameter set `W`: a proper analytic map `π : M → U` from an analytic `d`-manifold,
which is an analytic isomorphism away from a null exceptional set and has, around every point
over `W₀ = {w ∈ W | K w = 0}`, a chart in which

* `K ∘ π = u^{2k}` exactly;
* over `W`, the pulled-back prior density `φ(π u) |det π'(u)|` is a positive smooth unit times
  `|u^h|`;
* on each open orthant of the chart's cube, `π` lands entirely in the interior of `W` or
  entirely outside `W`.

The last condition says that the closure of `π⁻¹(interior W)` meets the cube in a union of
closed orthants, all of them when `π z` is an interior point of `W`. It is stated for the
interior of `W` because the full preimage `π⁻¹(W)` is not such a union in general: it contains
the whole fibre over each point of `W`, including the parts of an exceptional fibre over a
boundary point of `W` that lie outside the closure of `π⁻¹(interior W)`. Lower-dimensional
parts of `W` are not seen by the charts.

The parameter set `W` enters only through the prior density and the orthant condition. The
functions that cut out `W` are resolved in the proof of `exists_sltResolution`, but they are
not part of the structure.
Likewise the prior enters only through its pulled-back density, so the factorisation
`φ = φ₁ φ₂` of fundamental condition (II) is a hypothesis of the existence theorem and not a
field.

**Deviations from [Wat09, Theorem 2.8].** The book's theorem is local, near one common zero of
the functions. Here the map is over the whole open set `U`, as in Atiyah's form of the theorem.
The loss is an exact monomial `u^{2k}` (the book's `f₀`); the prior and Jacobian are recorded
only through their product on `W`; the boundary functions of `W` are recorded only through the
orthant condition; and the charts are centred cubes `[-r, r]^d`.

## Orthant form

The statements of Chapter 6 work in the book's orthant form: finitely many local coordinates
`M_α = [0, b]^d` on which `K = u^{2k}` ([Wat09, Theorem 6.5]). Here they are derived from a
resolution in two steps. A `ChartFamily` is a finite family of charts of the resolution whose
open cubes cover the part `W̃ ∩ {K ≤ δ}` of the resolved parameter set
`W̃ = closure (π⁻¹ (interior W))`. Its *pieces* are the pairs of a chart and an admissible orthant
of it (one lying over the interior of `W`), each reflected onto `[0, r]^d`: these are the book's
`M_α`. The learning coefficient `λ` and multiplicity `m` are read off the resolution itself
(`SLTResolution.rlct`, `SLTResolution.mult`), as the minimum over all its charts at points of
`W̃` over zeros of `K`, and `SLTResolution.isSingularityType` identifies them with the singularity
type.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped Manifold ContDiff

namespace SingularLearningTheory

variable {d : ℕ}

/-- The open orthant of the cube `[-r, r]^d` with sign pattern `s`: the points whose coordinate
`j` is positive when `s j` is `true` and negative when it is `false`. Supports
`SLTChart.orthant_dichotomy`. -/
def openOrthant (r : ℝ) (s : Fin d → Bool) : Set (Fin d → ℝ) :=
  {u | ∀ j, |u j| ≤ r ∧ 0 < (if s j then u j else -u j)}

/-- The reflection taking the positive orthant to the orthant with sign pattern `s`: coordinate
`j` is negated when `s j` is `false`. It carries the cube `[0, r]^d` onto the closure of
`openOrthant r s`. -/
def reflectOrthant (s : Fin d → Bool) (u : Fin d → ℝ) : Fin d → ℝ :=
  fun j ↦ if s j then u j else -u j

/-- A chart of an `SLTResolution` centred at `z`, in the form of [Wat09, Theorem 2.8(3)] for the
loss `K` and the prior `φ` on `W`. The chart `extension` comes from the analytic atlas of `M`
and contains the closed cube `[-radius, radius]^d` in its target.

Relation to the source.
* **Translation.** `loss_eq` and `density_eq` are the forms of [Wat09, Theorem 2.8 (3)] for the loss
  and the prior: $K(g(u)) = u^{2k}$ is the book's exact monomial $f_0(g(u))$, and
  $\varphi(g(u))\,|g'(u)| = c(u)\,|u^h|$ collects the prior and the Jacobian determinant, with
  `densityUnit` the unit $c$. -/
structure SLTChart {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
    (π : M → (Fin d → ℝ)) (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) (z : M) where
  /-- The chart, a member of the analytic atlas of `M`. -/
  extension : OpenPartialHomeomorph M (Fin d → ℝ)
  extension_mem : extension ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M
  mem_source : z ∈ extension.source
  centered : extension z = 0
  /-- The half side length `r` of the chart's cube `[-r, r]^d`. -/
  radius : ℝ
  radius_pos : 0 < radius
  box_subset : Icc (fun _ ↦ -radius) (fun _ ↦ radius) ⊆ extension.target
  /-- Half the exponents of the loss: `K ∘ π = u^{2k}`. -/
  k : Fin d → ℕ
  /-- The chart sits over a genuine zero of `K`: `u^{2k}` is not the constant `1`. -/
  active : ∃ j, 0 < k j
  loss_eq : ∀ u ∈ extension.target, K (π (extension.symm u)) = ∏ j, u j ^ (2 * k j)
  /-- The exponents of the pulled-back prior density: `φ(π u) |det π'(u)| = c(u) |u^h|`. -/
  h : Fin d → ℕ
  /-- The unit `c` of the pulled-back prior density. -/
  densityUnit : (Fin d → ℝ) → ℝ
  densityUnit_contDiffOn : ContDiffOn ℝ ∞ densityUnit extension.target
  densityUnit_pos : ∀ u ∈ extension.target, 0 < densityUnit u
  density_eq : ∀ u ∈ extension.target, π (extension.symm u) ∈ W →
    φ (π (extension.symm u)) * |(fderiv ℝ (π ∘ extension.symm) u).det|
      = densityUnit u * |∏ j, u j ^ h j|
  /-- On each open orthant of the cube, `π` lands entirely in the interior of `W` or entirely
  outside `W`. -/
  orthant_dichotomy : ∀ s : Fin d → Bool,
    (∀ u ∈ openOrthant radius s, π (extension.symm u) ∈ interior W) ∨
    (∀ u ∈ openOrthant radius s, π (extension.symm u) ∉ W)

/-- A resolution of the loss `K` with prior `φ` over an open neighbourhood `U` of `W`, the
global form of [Wat09, Theorem 2.8] used in singular learning theory. The map `π` is proper,
analytic and onto `U`, an analytic isomorphism away from the null exceptional set, and has an
`SLTChart` around every point over a zero of `K` in `W`. The deviations from the book are
listed in the module docstring. -/
structure SLTResolution (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) where
  /-- The open neighbourhood of `W` that the resolution is over. -/
  U : Set (Fin d → ℝ)
  isOpen_U : IsOpen U
  W_subset_U : W ⊆ U
  /-- The resolving manifold, analytic, Hausdorff and second countable, with its Borel sets. -/
  M : Type
  [topologicalSpace : TopologicalSpace M]
  [chartedSpace : ChartedSpace (Fin d → ℝ) M]
  [isManifold : IsManifold 𝓘(ℝ, Fin d → ℝ) ω M]
  [t2Space : T2Space M]
  [secondCountable : SecondCountableTopology M]
  [measurableSpace : MeasurableSpace M]
  [borelSpace : BorelSpace M]
  /-- The resolution map. -/
  π : M → (Fin d → ℝ)
  analytic_π : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω π
  range_π : range π = U
  proper : ∀ C ⊆ U, IsCompact C → IsCompact (π ⁻¹' C)
  /-- A null set off which `π` is an analytic isomorphism. It contains the zeros of `K`. -/
  exceptional : Set (Fin d → ℝ)
  volume_exceptional : volume exceptional = 0
  zeros_subset_exceptional : {w | w ∈ U ∧ K w = 0} ⊆ exceptional
  bijOn_off_exceptional : BijOn π (π ⁻¹' exceptionalᶜ) (U \ exceptional)
  isLocalDiffeomorphOn_off_exceptional :
    IsLocalDiffeomorphOn 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin d → ℝ) ω π (π ⁻¹' exceptionalᶜ)
  /-- A chart around every point over a zero of `K` in `W`. -/
  charts : ∀ z, π z ∈ W → K (π z) = 0 → Nonempty (SLTChart π K φ W z)

attribute [instance] SLTResolution.topologicalSpace SLTResolution.chartedSpace
  SLTResolution.isManifold SLTResolution.t2Space SLTResolution.secondCountable
  SLTResolution.measurableSpace SLTResolution.borelSpace

/-- A chart of the resolution `R` centred at `z`. -/
abbrev SLTResolution.Chart {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : SLTResolution K φ W) (z : R.M) :=
  SLTChart R.π K φ W z

/-! ## Invariants of a chart -/

namespace SLTChart

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {π : M → (Fin d → ℝ)} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {z : M}

/-- The learning coefficient of a chart: the minimum of `(h_j + 1) / (2 k_j)` over the
coordinates with `k_j > 0`, the inner minimum of [Wat09, eq. (6.16)]. -/
noncomputable def rlct (C : SLTChart π K φ W z) : ℝ :=
  monomialRlct C.k C.h C.active

/-- The multiplicity of a chart: the number of coordinates attaining `C.rlct`, as in [Wat09, eq.
(6.17)]. -/
noncomputable def mult (C : SLTChart π K φ W z) : ℕ :=
  monomialMultiplicity C.k C.h C.active

/-- The open cube `(-r, r)^d` of the chart, as an open subset of `M`. -/
def openCube (C : SLTChart π K φ W z) : Set M :=
  C.extension.source ∩ C.extension ⁻¹' Set.pi univ fun _ ↦ Ioo (-C.radius) C.radius

/-- The orthant with sign pattern `s` lies over the interior of `W`: the first case of
`orthant_dichotomy`. -/
def IsAdmissible (C : SLTChart π K φ W z) (s : Fin d → Bool) : Prop :=
  ∀ u ∈ openOrthant C.radius s, π (C.extension.symm u) ∈ interior W

end SLTChart

/-! ## The resolved parameter set and the singularity type of a resolution -/

namespace SLTResolution

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- The resolved parameter set `W̃ = closure (π⁻¹ (interior W))`. Near a point over a zero of
`K` it is the union of the closed admissible orthants of a chart (see `SLTChart`). It leaves out
the parts of `π⁻¹(W)` over lower-dimensional parts of `W`, which carry no prior mass. -/
def resolvedParameterSet (R : SLTResolution K φ W) : Set R.M :=
  closure (R.π ⁻¹' interior W)

/-- The learning coefficient `λ` of a resolution, [Wat09, eq. (6.16)]: the minimum of the chart
learning coefficients over all charts of `R` centred at points of `W̃` over zeros of `K`. The
chart value depends only on the centre, and `SLTResolution.isSingularityType` shows the minimum
is the singularity type's `λ`.

Relation to the source.
* **Translation.** `R.rlct` and `R.mult` are the $\lambda$ and $m$ of [Wat09, eqs. (6.16), (6.17)],
  read off the resolution `R`. -/
noncomputable def rlct (R : SLTResolution K φ W) : ℝ :=
  sInf {l | ∃ z ∈ R.resolvedParameterSet, K (R.π z) = 0 ∧ ∃ C : R.Chart z, C.rlct = l}

/-- The multiplicity `m` of a resolution, [Wat09, eq. (6.17)]: the largest chart multiplicity
among the charts counted in `rlct` that attain it. -/
noncomputable def mult (R : SLTResolution K φ W) : ℕ :=
  sSup {m | ∃ z ∈ R.resolvedParameterSet, K (R.π z) = 0 ∧
    ∃ C : R.Chart z, C.rlct = R.rlct ∧ C.mult = m}

/-- A finite family of charts of `R` whose open cubes cover the part of the resolved parameter
set where `K ≤ δ`: the book's finitely many local coordinates ([Wat09, Theorem 6.5]). The
statements of Chapter 6 hold for every such family; `exists_chartFamily` shows one exists.

Relation to the source.
* **Translation.** The pieces `α : F.Piece`, with their cubes `cube d α.radius` and maps `α.map`,
  are the local coordinates $\mathcal{M}_\alpha = [0, b]^d$ and the maps $g_\alpha$ of [Wat09,
  Theorem 6.5 (1), (2)]; `(α : F.Piece) × cube d α.radius` is their disjoint union $\mathcal{M}$.
* **Gap.** Each chart has its own radius, where the book prints one $b$ for all local coordinates.
  Rescaling a chart to a common radius multiplies $K \circ g_\alpha$ by a constant and destroys the
  exact monomial. -/
structure ChartFamily (R : SLTResolution K φ W) where
  /-- The chart indices. -/
  ι : Type
  [fintype : Fintype ι]
  /-- The chart centres. -/
  centre : ι → R.M
  /-- The charts. -/
  chart : (i : ι) → R.Chart (centre i)
  /-- The sublevel of `K` that the family covers. -/
  δ : ℝ
  δ_pos : 0 < δ
  covers : ∀ z ∈ R.resolvedParameterSet, K (R.π z) ≤ δ → ∃ i, z ∈ (chart i).openCube

attribute [instance] ChartFamily.fintype

namespace ChartFamily

variable {R : SLTResolution K φ W}

/-- The part `W̃ ∩ {K ≤ δ}` of the resolved parameter set that the family covers, on which a
partition of unity subordinate to the family sums to one. -/
def sublevel (F : R.ChartFamily) : Set R.M :=
  R.resolvedParameterSet ∩ R.π ⁻¹' {w | K w ≤ F.δ}

/-- A piece of a chart family: a chart together with an admissible orthant of it, read in the
book's orthant coordinates `[0, r]^d` ([Wat09, Theorem 6.5]). -/
structure Piece (F : R.ChartFamily) where
  /-- The chart. -/
  chart : F.ι
  /-- The sign pattern of the orthant. -/
  orthant : Fin d → Bool
  admissible : (F.chart chart).IsAdmissible orthant

namespace Piece

variable {F : R.ChartFamily}

/-- The side length `r` of the piece's cube `[0, r]^d`. -/
abbrev radius (α : F.Piece) : ℝ := (F.chart α.chart).radius

/-- Half the exponents of the loss on the piece: `K = u^{2k}`. -/
abbrev k (α : F.Piece) : Fin d → ℕ := (F.chart α.chart).k

/-- The exponents of the prior density on the piece: `φ(g(u)) |g'(u)| = c(u) u^h`. -/
abbrev h (α : F.Piece) : Fin d → ℕ := (F.chart α.chart).h

/-- The point of `M` with orthant coordinates `u`. -/
def point (α : F.Piece) (u : Fin d → ℝ) : R.M :=
  (F.chart α.chart).extension.symm (reflectOrthant α.orthant u)

/-- The book's chart map `g_α : [0, r]^d → W` of the piece. -/
def map (α : F.Piece) (u : Fin d → ℝ) : Fin d → ℝ := R.π (α.point u)

/-- The unit `c` of the prior density on the piece. -/
def densityUnit (α : F.Piece) (u : Fin d → ℝ) : ℝ :=
  (F.chart α.chart).densityUnit (reflectOrthant α.orthant u)

/-- The piece is essential ([Wat09, Definition 6.4]): its chart attains the resolution's `λ`
with the resolution's multiplicity `m`. -/
def IsEssential (α : F.Piece) : Prop :=
  (F.chart α.chart).rlct = R.rlct ∧ (F.chart α.chart).mult = R.mult

end Piece

end ChartFamily

end SLTResolution

end SingularLearningTheory

namespace SingularLearningTheory

variable {d : ℕ}

/-- **Resolution of singularities**, in the global form of `SLTResolution`. Hypotheses: `W` is
semianalytic; `K` is analytic and nonnegative on an open `U ⊇ W` and not identically zero near any
point of `U`; and on `U` the prior factors as `φ = φ₁ φ₂` with `φ₁ > 0` smooth and `φ₂` analytic,
nonnegative on `W` and not identically zero near any point of `U`. The resolution is over an open
neighbourhood of `W` inside `U`, which is smaller than `U` when the semianalytic presentation of `W`
is given on a smaller open set.

Relation to the source.
* **Strengthening.** [Wat09, Theorem 2.8] is local, near a common zero of the functions; here the
  resolution is over an open neighbourhood of $W$, with a chart around every point over a zero of
  $K$ in $W$, as in Atiyah's form of the theorem.
* **Interpretation.** The book's hypothesis that each function vanishes at the point and is not
  constant is read, for a resolution over all of $U$, as `K` and `φ₂` not identically zero near any
  point of $U$.
* **Interpretation.** The prior and the Jacobian determinant are recorded only through their product
  on $W$, the functions cutting out $W$ only through the orthant condition, and the charts are
  centred cubes $[-r, r]^d$.

Source statement: [Wat09, Theorem 2.8] -/
theorem exists_sltResolution {d : ℕ} {K φ φ₁ φ₂ : (Fin d → ℝ) → ℝ} {W U : Set (Fin d → ℝ)}
    (hU : IsOpen U) (hWU : W ⊆ U) (hW : Semianalytic W)
    (hK : AnalyticOnNhd ℝ K U) (hK₀ : ∀ w ∈ U, 0 ≤ K w)
    (hKg : ∀ w ∈ U, ¬ K =ᶠ[𝓝 w] 0)
    (hφ₁ : ContDiffOn ℝ ∞ φ₁ U) (hφ₁₀ : ∀ w ∈ U, 0 < φ₁ w)
    (hφ₂ : AnalyticOnNhd ℝ φ₂ U) (hφ₂₀ : ∀ w ∈ W, 0 ≤ φ₂ w)
    (hφ₂g : ∀ w ∈ U, ¬ φ₂ =ᶠ[𝓝 w] 0)
    (hφ : ∀ w ∈ U, φ w = φ₁ w * φ₂ w) :
    ∃ R : SLTResolution K φ W, R.U ⊆ U :=
  sorry

open scoped Manifold ContDiff

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- Every resolution of `K ≥ 0` over a compact `W` has a finite chart family: finitely many of
its charts cover a sublevel of `K` in the resolved parameter set, as in the local coordinates of
[Wat09, Theorem 6.5]. `hK` is needed: `K ∘ π = u^{2k} ≥ 0` on every chart cube, so no chart covers
a point of `W̃` where `K < 0`.

Relation to the source.
* **Strengthening.** Every resolution of $K$ has a chart family, not only the resolution of
  $K(\varepsilon - K)\varphi_2 \prod_j \pi_j$ that [Wat09, Theorem 6.5] constructs.
* **Correction.** [Wat09, Theorem 6.5] is printed for an arbitrary $\varepsilon > 0$, which can
  fail: at a critical point $x$ of $K$ with $0 < K(x) \le \varepsilon$ no chart has
  $K \circ g = u^{2k}$ with $k \ne 0$ near a preimage of $x$. The family covers the sublevel
  $\{K \le \delta\}$ for some $\delta > 0$, as in [Wat09, Remark 6.1 (1)], "for a sufficiently small
  constant".
* **Formalisation note.** The unit of a chart is smooth and positive on the chart's target, which
  contains the closed cube, so it is bounded below on every piece ([Wat09, Theorem 6.5 (3)]). -/
theorem SLTResolution.exists_chartFamily
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : SLTResolution K φ W) (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w) : Nonempty R.ChartFamily :=
  sorry

/-- Every chart family has a smooth partition of unity on the resolving manifold, subordinate to
its open cubes and summing to one on the sublevel it covers: the partition of unity of [Wat09,
Theorem 6.5(4)].

Relation to the source.
* **Gap.** The change of variables of the prior along the pieces and the bounds (6.14) of [Wat09,
  Theorem 6.5 (4)] are not stated. -/
theorem SLTResolution.ChartFamily.exists_partitionOfUnity
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {R : SLTResolution K φ W}
    (F : R.ChartFamily) (hW : IsCompact W) (hKc : ContinuousOn K W) :
    ∃ ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel,
      ρ.IsSubordinate fun i ↦ (F.chart i).openCube :=
  sorry

/-- [Wat09, Definition 6.4], eqs. (6.16) and (6.17): the learning coefficient and multiplicity read
off any resolution are the singularity type of `K` and `φ` on `W`. `hvol` (every sublevel `{K < ε}`
has positive prior mass) rules out a resolution whose resolved parameter set misses the zeros of
`K`.

Relation to the source.
* **Strengthening.** [Wat09, Definition 6.4] reads $(\lambda, m)$ off the local coordinates of
  Theorem 6.5; here the pair read off any resolution is the singularity type, which
  `zetaFunction_meromorphic_continuation` identifies with the largest pole of the zeta function and
  its order. -/
theorem SLTResolution.isSingularityType
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : SLTResolution K φ W) (hW : IsCompact W)
    (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφc : ContinuousOn φ W)
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    IsSingularityType K φ W R.rlct R.mult :=
  sorry

end SingularLearningTheory
