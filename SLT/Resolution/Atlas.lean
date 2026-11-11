/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import SLT.EmpiricalProcess.Defs
public import SLT.SingularIntegrals.Defs

/-!
# The resolution atlas

The conclusion of Hironaka's theorem as [Hit26] applies it
([Hit26, Theorem 3.3.1] followed by the bookkeeping of
[Hit26, Section 3.3.1]), packaged as the structure
`ResolutionAtlas`, together with the invariants `λ`, `m` and the essential charts defined
from it. The theorems of this repository about the free energy are proved for an arbitrary
atlas; this directory derives an atlas from the resolution theorem
`exists_resolution_of_isConnected` (`Resolution/Components.lean`, about the `Resolution` of
`Resolution/Hironaka.lean`). Nothing in this file is proved from analyticity.

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 3.3.1], atlas form | `ResolutionAtlas` |
| [Hit26, Equation (3.3.5)] | `ResolutionAtlas.transport` |
| `λ_α`, `m_α` of a chart ([Hit26, Equation (5.2.1)]) | |
| | `ResolutionAtlas.chartRlct`, `ResolutionAtlas.chartMult` |
| `λ`, `m` (learning coefficient and multiplicity) | `ResolutionAtlas.rlct`, |
| | `ResolutionAtlas.mult` |
| essential chart, `A*` | `ResolutionAtlas.IsEssential` |
| `μ = h' − 2λk'` | |
| ([Hit26, Equation (5.2.5)]) | |
| | `ResolutionAtlas.secondaryExponent` |
| positive essential trace mass (not in [Hit26]) | `NondegenerateResolutionAtlas` |

## What [Hit26] proves, and what the atlas records

[Hit26] states the existence of the resolution (Hironaka's theorem, quoted as
[Hit26, Theorem 3.3.1]) and then, in
[Hit26, Section 3.3.1], covers a neighbourhood of
`W₀ = {K = 0}` by finitely many charts `g_α : [0, b_α)^d → W` on which `K ∘ g_α = u^{2k_α}` and
`φ(g_α u) |g_α'(u)| = a_α(u) u^{h_α}`, and rewrites the localised integral as a sum of chart
integrals with two partitions of unity. `ResolutionAtlas` records exactly the output of that
construction: the finite family of analytic chart maps, the exponents `k_α, h_α`, the chart
weights `φ̃_α` ([Hit26]'s `a_α ρ_α`), and the transport identity as an identity of measures
on parameter space. Hironaka's theorem itself is `exists_resolution_of_isConnected`, proved from
the hironaka package in `Resolution/Components.lean`; the atlas is derived from it in this
directory.

Two points where the atlas is not literally [Hit26]'s construction:

* **Smooth localization instead of the sharp cutoff.** [Hit26] localises to
  `W_ε = {K < ε}`; a sharp cutoff is not `C¹` on a chart, which [Wat09, Theorem 4.9] needs. The
  atlas carries instead a localization `χ` with `0 ≤ χ ≤ 1` and `χ = 1` on `{K < δ}`, so that the
  chart weights can be regular; the remainder `(1 − χ) φ` is supported on `{K ≥ δ}` and is handled
  by [Hit26]'s tail estimate unchanged.
* **Positive essential trace mass.** The invariants `λ, m` read off an atlas describe the
  leading order of `Z₀(n)` only if some essential chart carries mass along its essential face;
  a chart with weight `0` and large `k` lowers `λ` without changing `laplaceIntegral`, and [Hit26]'s
  argument only gives the upper bound `laplaceIntegral ≤ C (log n)^{m−1} n^{−λ}`.
  `NondegenerateResolutionAtlas` adds `Σ_{α ∈ A*} T_α > 0`; it is the hypothesis of the lower
  bound in [Hit26, Theorem 3.3.9] and of [Hit26, Theorem 5.2.9].

Existence caveats: an atlas does not exist under [Hit26]'s hypotheses as
literally stated (`K ≡ 0` on `W`; `W = {0} ∪ [1, 2]`, `K = w²`), and in those cases the free
energy formula with `λ > 0` is false; even exponents at boundary points of `W` need the
substitution `x_j = u_j²`. Existence is to be understood under the usual nontriviality and
accessibility assumptions, plus coordinate ramification.

Properness of `g_α`, the isomorphism off the exceptional set, the Jacobian and the unit factors
`a_α(u)` are not recorded: the proofs use them only through `transport`. The invariants
`λ_α`, `m_α` are computed over the *active* coordinates `k_α j > 0`; [Hit26]'s
`min_j (h_j + 1)/(2k_j)` is undefined at `k_j = 0`.
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

variable {d : ℕ}

theorem mem_cube {m : ℕ} {b : ℝ} {u : Fin m → ℝ} : u ∈ cube m b ↔ ∀ j, u j ∈ Icc 0 b :=
  ⟨fun h j ↦ ⟨h.1 j, h.2 j⟩, fun h ↦ ⟨fun j ↦ (h j).1, fun j ↦ (h j).2⟩⟩

/-- The cube as the product of its sides, for the product measure. -/
theorem cube_eq_pi (m : ℕ) (b : ℝ) : cube m b = univ.pi fun _ ↦ Icc 0 b :=
  (pi_univ_Icc _ _).symm

/-- [Hit26, Theorem 3.3.1] in the chart-atlas
form of [Hit26, Section 3.3.1], for the
potential `K ≥ 0` and prior `φ` on `W ⊆ ℝ^d`. A finite family of charts
`g_α : [0, b_α]^d → W` on which `K` is a monomial `u^{2k_α}`, together with chart weights
`φ̃_α` ([Hit26]'s `|g'_α| (φ ∘ g_α) ρ_α ρ̃_σ ∘ g_α`, absorbed into `u^{h_α} φ̃_α`) such
that the localised prior measure `χ φ dw` on `W` is the sum of the pushforwards of the
weighted cubes. -/
structure ResolutionAtlas (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) where
  /-- The chart indices `A`. -/
  ι : Type
  [fintype : Fintype ι]
  [nonempty : Nonempty ι]
  /-- The side length of the cube `U_α = [0, b_α]^d`. -/
  b : ι → ℝ
  b_pos : ∀ α, 0 < b α
  /-- The exponents of `K ∘ g_α = u^{2k_α}`. -/
  k : ι → Fin d → ℕ
  /-- The exponents of the weight, `h_α = h(1) + h(2)` in [Hit26]. -/
  h : ι → Fin d → ℕ
  /-- Every chart sits over a genuine zero of `K`: `u^{2k_α}` is not the constant `1`. -/
  active : ∀ α, ∃ j, 0 < k α j
  /-- The chart maps `g_α`. -/
  g : ι → (Fin d → ℝ) → (Fin d → ℝ)
  /-- The chart maps extend analytically around their closed cubes. -/
  g_analytic : ∀ α, AnalyticOnNhd ℝ (g α) (cube d (b α))
  g_measurable : ∀ α, Measurable (g α)
  g_mapsTo : ∀ α, MapsTo (g α) (cube d (b α)) W
  monomial : ∀ α, ∀ u ∈ cube d (b α), K (g α u) = ∏ j, u j ^ (2 * k α j)
  /-- The chart weights `φ̃_α` (after the monomial `u^{h_α}` has been split off). -/
  weight : ι → (Fin d → ℝ) → ℝ
  weight_nonneg : ∀ α, ∀ u ∈ cube d (b α), 0 ≤ weight α u
  /-- The chart weights are continuously differentiable on their closed cubes. -/
  weight_contDiffOn : ∀ α, ContDiffOn ℝ 1 (weight α) (cube d (b α))
  /-- The localization `χ` and the threshold `δ` below which it is `1`. -/
  χ : (Fin d → ℝ) → ℝ
  χ_measurable : Measurable χ
  χ_nonneg : ∀ w, 0 ≤ χ w
  χ_le_one : ∀ w, χ w ≤ 1
  /-- The threshold $\delta > 0$ such that $\chi = 1$ at the points of `W` where $K < \delta$. -/
  δ : ℝ
  δ_pos : 0 < δ
  χ_eq_one : ∀ w ∈ W, K w < δ → χ w = 1
  /-- [Hit26, Equation (3.3.5)], as an identity of
  measures: `χ φ dw` on `W` is the sum over charts of the pushforward of
  `u^{h_α} φ̃_α(u) du` on `[0, b_α]^d` along `g_α`. -/
  transport :
    (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (χ w * φ w))
      = ∑ α, Measure.map (g α) ((volume.restrict (cube d (b α))).withDensity
          fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (h α j : ℝ)) * weight α u))

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

attribute [instance] ResolutionAtlas.fintype ResolutionAtlas.nonempty

/-- Continuity follows from the regularity of the chart weights. -/
theorem weight_continuousOn (α : R.ι) : ContinuousOn (R.weight α) (cube d (R.b α)) :=
  (R.weight_contDiffOn α).continuousOn

/-- On the compact convex chart cube, C¹ regularity gives a Lipschitz bound. -/
theorem exists_lipschitzOnWith_weight (α : R.ι) :
    ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α)) :=
  (R.weight_contDiffOn α).exists_lipschitzOnWith (by simp)
    (convex_Icc _ _) isCompact_Icc

/-- The ratio `(h_j + 1) / (2 k_j)` of a coordinate of a chart. -/
@[expose] noncomputable def ratio (α : R.ι) (j : Fin d) : ℝ := (R.h α j + 1) / (2 * R.k α j)

/-- The coordinates on which `K ∘ g_α` actually depends. -/
@[expose] def activeSet (α : R.ι) : Finset (Fin d) := Finset.univ.filter fun j ↦ 0 < R.k α j

theorem activeSet_nonempty (α : R.ι) : (R.activeSet α).Nonempty := by
  obtain ⟨j, hj⟩ := R.active α
  exact ⟨j, by simp [activeSet, hj]⟩

/-- [Hit26, Equation (5.2.1)], `λ_α`: the smallest ratio `(h_j + 1) / (2 k_j)` over the active
coordinates of the chart, the `monomialRlct` of its exponents. -/
@[expose] noncomputable def chartRlct (α : R.ι) : ℝ := monomialRlct (R.k α) (R.h α) (R.active α)

theorem chartRlct_eq_inf' (α : R.ι) :
    R.chartRlct α = (R.activeSet α).inf' (R.activeSet_nonempty α) (R.ratio α) := rfl

/-- The primary coordinates of a chart: the active coordinates attaining `λ_α`, the
`criticalCoords` of its exponents. -/
@[expose] noncomputable def primary (α : R.ι) : Finset (Fin d) :=
  criticalCoords (R.k α) (R.h α) (R.active α)

theorem mem_primary {α : R.ι} {j : Fin d} :
    j ∈ R.primary α ↔ j ∈ R.activeSet α ∧ R.ratio α j = R.chartRlct α := by
  simp only [primary, criticalCoords, activeSet, ratio, chartRlct, Finset.mem_filter,
    Finset.mem_univ, true_and]

theorem primary_eq_filter (α : R.ι) :
    R.primary α = (R.activeSet α).filter fun j ↦ R.ratio α j = R.chartRlct α := by
  ext j
  rw [mem_primary, Finset.mem_filter]

/-- [Hit26, Equation (5.2.1)], `m_α`: the number of coordinates attaining `λ_α`, the
`monomialMultiplicity` of the chart's exponents. -/
@[expose] noncomputable def chartMult (α : R.ι) : ℕ :=
  monomialMultiplicity (R.k α) (R.h α) (R.active α)

theorem chartMult_eq_card (α : R.ι) : R.chartMult α = (R.primary α).card := rfl

/-- The learning coefficient `λ = min_α λ_α` ([Hit26,
Equation (5.2.1)]). -/
@[expose] noncomputable def rlct : ℝ := Finset.univ.inf' Finset.univ_nonempty R.chartRlct

/-- The charts attaining `λ`. -/
@[expose] noncomputable def minimalCharts : Finset R.ι :=
  Finset.univ.filter fun α ↦ R.chartRlct α = R.rlct

theorem minimalCharts_nonempty : R.minimalCharts.Nonempty := by
  obtain ⟨α, -, hα⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty R.chartRlct
  exact ⟨α, Finset.mem_filter.mpr ⟨Finset.mem_univ α, hα.symm⟩⟩

/-- The multiplicity `m = max {m_α | λ_α = λ}` ([Hit26,
Equation (5.2.1)]). -/
@[expose] noncomputable def mult : ℕ := R.minimalCharts.sup'
    (minimalCharts_nonempty R) R.chartMult

/-- An *essential chart*: `λ_α = λ` and `m_α = m` (the set `A*` of [Hit26]). -/
@[expose] def IsEssential (α : R.ι) : Prop := R.chartRlct α = R.rlct ∧ R.chartMult α = R.mult

/-- The exponent `μ_j = h_j − 2 λ k_j` of a secondary coordinate ([Hit26,
Equation (5.2.5)], `μ = h' − 2λk'`). -/
@[expose] noncomputable def secondaryExponent (α : R.ι) (j : Fin d) : ℝ :=
  R.h α j - 2 * R.k α j * R.rlct

/-- The *essential trace mass* of a chart: the integral over the secondary coordinates of
`v^μ · φ̃_α(0, v)`, the weight evaluated on the face where the primary coordinates vanish.
(The primary coordinates are integrated out over `[0, b_α]` as well, contributing the
harmless factor `b_α^{m_α}`.) -/
@[expose] noncomputable def essentialTraceMass (α : R.ι) : ℝ :=
  ∫ v in cube d (R.b α),
    (∏ j ∈ (R.primary α)ᶜ, v j ^ R.secondaryExponent α j) *
      R.weight α ((R.primary α)ᶜ.piecewise v 0)

/-- The point `(0, v)` of the chart `U_α`: the primary coordinates set to `0` and the
secondary coordinates of `v` clamped to `[0, b_α]` (a no-op for `v` in the cube). -/
@[expose] noncomputable def primaryZero (α : R.ι) (v : Fin d → ℝ) : cube d (R.b α) :=
  ⟨fun j ↦ if j ∈ R.primary α then 0 else max 0 (min (R.b α) (v j)), mem_cube.2 fun j ↦ by
    by_cases hj : j ∈ R.primary α
    · simp [hj, (R.b_pos α).le]
    · simp only [hj, ite_false, mem_Icc]
      exact ⟨le_max_left _ _, max_le (R.b_pos α).le (min_le_left _ _)⟩⟩

end ResolutionAtlas

/-- A resolution atlas some essential chart of which carries positive trace mass (all trace
masses are nonnegative, so this is `Σ_{α essential} T_α > 0`). This is
the hypothesis under which `λ, m` computed from the atlas are the true leading exponents
of `Z₀(n)`, hence the hypothesis for the lower bound in
[Hit26, Theorem 3.3.9] and for [Hit26, Theorem 5.2.9].
Not in [Hit26], which proves only the upper bound. -/
structure NondegenerateResolutionAtlas (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    extends ResolutionAtlas K φ W where
  traceMass_pos : ∃ α, toResolutionAtlas.IsEssential α ∧ 0 < toResolutionAtlas.essentialTraceMass α

end SingularLearningTheory
