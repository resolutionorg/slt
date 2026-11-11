/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import SLT.VolumeScaling.Defs
import SLT.ChartForm.Assembly
import SLT.ChartForm.Localize
import SLT.ChartForm.MonomialResolution
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Existence of the local learning coefficient

For an analytic `K` on an open `U ⊆ ℝ^d`, vanishing at `w ∈ U` with nonzero germ, there are a
positive rational `λ`, a multiplicity `θ ∈ {1, …, d}` and a radius `r₀ > 0` such that on every
closed cube `closedBall w r`, `0 < r ≤ r₀`, the volume of `{|K| ≤ ε}` is of the order
`ε^λ (log 1/ε)^{θ − 1}` as `ε ↓ 0` (`HasLLCExponentsOn`); the same for `K` in place of `|K|` when
`K ≥ 0` near `w`. These are the local learning coefficient and its multiplicity of [Watanabe's
singular learning theory][Wat09]. The statements, main theorems of the library, are
`exists_hasLLCExponentsAt_of_analyticOnNhd` and
`exists_hasLLCExponentsAt_of_analyticOnNhd_of_nonneg` at the end of this file, stated with
`HasLLCExponentsAt`, the relation on every small closed cube about `w`. Before them,
`exists_hasLLCExponentsOn_of_analyticOnNhd` and
`exists_hasLLCExponentsOn_of_analyticOnNhd_of_nonneg` state the same with an explicit radius `r₀`,
uniform over the cubes `closedBall w r`, `0 < r ≤ r₀`.

The volume computations need a globally measurable loss while `K` is analytic on `U` only: the
monomial resolution (`exists_monomialPartialResolution_at`, from Watanabe's Theorem 2.3) and its
chart family (`exists_monomialChartCover_of_isMonomial`) are taken for the globally measurable
modification `U.piecewise K 0`, which is analytic on `U`, vanishes at `w` and is not identically
zero near `w`; the family is cut down to the bounded open set `D.U ∩ ball w 1` (charts unchanged);
the general theorem localizes to every closed cube inside it, the exponents are a positive rational
and a multiplicity in `{1, …, d}` (every chart has dimension `d`), and the relation transfers to
`|K|`, and to `K` when `0 ≤ K` near `w`, on cubes where the functions agree.
-/

public section

section ChartForm

open MeasureTheory Set Filter SingularLearningTheory
open scoped Topology ENNReal

namespace SingularLearningTheory

/-- The local learning coefficient of `|K|` at a zero `w` with nonzero germ, with an explicit
radius: for `K` real-analytic on an open `U ⊆ ℝ^d` there are a positive rational `λ`, a natural
number `θ` with `1 ≤ θ ≤ d` and a radius `r₀ > 0` such that on every closed cube
`Metric.closedBall w r`, `0 < r ≤ r₀`, the sublevel volumes of `|K|` have the exponents `(λ, θ)`.
The form with `HasLLCExponentsAt` is `exists_hasLLCExponentsAt_of_analyticOnNhd`. -/
theorem exists_hasLLCExponentsOn_of_analyticOnNhd {d : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin d → ℝ} (hw : w ∈ U) (h0 : K w = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) :
    ∃ (lam : ℚ) (theta : ℕ) (r₀ : ℝ), 0 < lam ∧ 1 ≤ theta ∧ theta ≤ d ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        HasLLCExponentsOn volume (Metric.closedBall w r) (fun x ↦ |K x|)
          (lam : ℝ) (theta : ℝ) := by
  classical
  -- the globally measurable modification of the loss
  set K' : (Fin d → ℝ) → ℝ := U.piecewise K 0 with hK'def
  have hK'eq : EqOn K' K U := fun x hx ↦ Set.piecewise_eq_of_mem U K 0 hx
  have hK'meas : Measurable K' :=
    ContinuousOn.measurable_piecewise hK.continuousOn continuousOn_const hU.measurableSet
  have hK'an : AnalyticOnNhd ℝ K' U := hK.congr hU fun x hx ↦ (hK'eq hx).symm
  have h0' : K' w = 0 := by rw [hK'eq hw]; exact h0
  have hne' : ¬ ∀ᶠ x in 𝓝 w, K' x = 0 := by
    intro h
    apply hne
    filter_upwards [h, hU.mem_nhds hw] with x hx hxU
    rwa [hK'eq hxU] at hx
  -- the monomial resolution and its chart family for the modification, cut down to a bounded
  -- open set
  obtain ⟨N, -, hNn, R, hR⟩ := exists_monomialPartialResolution_at hU hK'an hw hne'
  obtain ⟨ι, hfin, hne'', D, hpins⟩ := exists_monomialChartCover_of_isMonomial hNn R hR h0'
  let D₁ := D.restrictU Metric.isOpen_ball (Metric.mem_ball_self (one_pos : (0 : ℝ) < 1))
  have hU₁ : volume D₁.U ≠ ⊤ :=
    ((measure_mono (inter_subset_right (s := D.U))).trans_lt measure_ball_lt_top).ne
  have hfmeas : Measurable fun x ↦ |K' x| := hK'meas.abs
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp D₁.U_open w D₁.w_mem_U
  obtain ⟨ε', hε', hε'U⟩ := Metric.isOpen_iff.mp hU w hw
  obtain ⟨q, hq, hqlam⟩ := D₁.exists_rat_combLam
  refine ⟨q, D₁.combTheta, min (ε / 2) (ε' / 2), hq, D₁.one_le_combTheta,
    D₁.combTheta_le_of_forall_d_eq fun α ↦ ?_, lt_min (half_pos hε) (half_pos hε'),
    fun r hr hrle ↦ ?_⟩
  · obtain ⟨_, _, _, _, _, _, -, -, -, -, -, -, ⟨hd, -, -⟩, -⟩ := hpins α
    exact hd
  · have hsubU₁ : Metric.closedBall w r ⊆ D₁.U :=
      (Metric.closedBall_subset_ball
        (hrle.trans_lt ((min_le_left _ _).trans_lt (half_lt_self hε)))).trans hεU
    have hsubU : Metric.closedBall w r ⊆ U :=
      (Metric.closedBall_subset_ball
        (hrle.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hε')))).trans hε'U
    have h1 := D₁.hasLLCExponentsOn_closedBall hfmeas hU₁ hr hsubU₁
    rw [hqlam]
    exact (hasLLCExponentsOn_congr_eqOn fun x hx ↦ by rw [hK'eq (hsubU hx)]).mp h1

/-- The local learning coefficient of a real-analytic `K` with `0 ≤ K` near its zero `w`, with an
explicit radius: there are a positive rational `λ`, a natural number `θ` with `1 ≤ θ ≤ d` and a
radius `r₀ > 0` such that on every closed cube `Metric.closedBall w r`, `0 < r ≤ r₀`, the sublevel
volumes of `K` have the exponents `(λ, θ)`. The form with `HasLLCExponentsAt` is
`exists_hasLLCExponentsAt_of_analyticOnNhd_of_nonneg`. -/
theorem exists_hasLLCExponentsOn_of_analyticOnNhd_of_nonneg {d : ℕ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin d → ℝ} (hw : w ∈ U)
    (h0 : K w = 0) (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) (hK0 : ∀ᶠ x in 𝓝 w, 0 ≤ K x) :
    ∃ (lam : ℚ) (theta : ℕ) (r₀ : ℝ), 0 < lam ∧ 1 ≤ theta ∧ theta ≤ d ∧ 0 < r₀ ∧
      ∀ r : ℝ, 0 < r → r ≤ r₀ →
        HasLLCExponentsOn volume (Metric.closedBall w r) K (lam : ℝ) (theta : ℝ) := by
  obtain ⟨lam, theta, r₀, hlam, h1, hn, hr₀, habs⟩ :=
    exists_hasLLCExponentsOn_of_analyticOnNhd hU hK hw h0 hne
  obtain ⟨ε, hε, hpos⟩ := Metric.eventually_nhds_iff.mp hK0
  refine ⟨lam, theta, min r₀ (ε / 2), hlam, h1, hn, lt_min hr₀ (half_pos hε), fun r hr hrle ↦ ?_⟩
  have hsub : Metric.closedBall w r ⊆ Metric.ball w ε :=
    Metric.closedBall_subset_ball (hrle.trans_lt ((min_le_right _ _).trans_lt (half_lt_self hε)))
  have h := habs r hr (hrle.trans (min_le_left _ _))
  exact (hasLLCExponentsOn_congr_eqOn fun x hx ↦
    abs_of_nonneg (hpos (Metric.mem_ball.mp (hsub hx)))).mp h

/-- **Existence of the local learning coefficient** of a real-analytic function, for the loss
`|K|`: the local form of Watanabe's learning coefficient and its order ([Wat09, Definition 2.7
(real log canonical threshold), Definition 6.4 eqs (6.16)–(6.17) (λ and its order as min and max
over charts), Theorem 7.1 (3)–(4), Corollary 4.3]), with `λ` a positive rational and `θ` a natural
number as in the free-energy expansion of [AW05].

Statement. Let `K` be real-analytic on an open set `U ⊆ ℝ^d` and `w ∈ U` a zero of `K` near which
`K` is not identically zero. Then there are a positive rational number `λ` and a natural number
`θ` with `1 ≤ θ ≤ d` such that `|K|` has the sublevel-volume exponents `(λ, θ)` at `w`
(`HasLLCExponentsAt volume (fun x => |K x|) w λ θ`): for every small enough radius `r > 0` (along
`𝓝[>] 0`, that is, every `0 < r ≤ r₀` for some `r₀ > 0`) the sublevel volumes of `|K|` on the
closed cube of half-side `r` about `w`,
`ε ↦ volume (Metric.closedBall w r ∩ {x | |K x| ≤ ε})`, are bounded above and below by positive
multiples of `ε^λ (−log ε)^(θ−1)` as `ε → 0⁺`
(`HasLLCExponentsOn volume (Metric.closedBall w r) (fun x => |K x|) λ θ`, an `IsTheta` relation
along `𝓝[>] 0`).

Conventions. `Metric.closedBall` is for the sup norm on `Fin d → ℝ`, so the localization sets are
cubes; they have finite measure, so nothing is lost in reading the sublevel measure as a real
number. The exponents `λ` and `θ` do not depend on the small radius `r`, which makes the pair an
invariant of the germ of `K` at `w`; the pair is determined by the relation
(`HasLLCExponentsOn.unique`). For `d = 0` the hypotheses contradict each other and the statement is
vacuous.

Relation to the source.
* **Gap.** `λ` and `θ` are the local counterparts of Watanabe's learning coefficient and its order
  [Wat09, Definitions 2.7 and 6.4], which are global, for a model and a prior.
* **Strengthening.** Watanabe's sublevel-volume asymptotics are stated for a nonnegative `K`. The
  statement here is for `|K|` with `K` of any sign; with `K` in place of `|K|` it fails for a
  sign-changing `K`, whose sublevel sets `{K ≤ ε}` contain the open set `{K < 0}`, whose volume does
  not tend to `0`. The nonnegative form is the corollary
  `exists_hasLLCExponentsAt_of_analyticOnNhd_of_nonneg`.

Source statement: [Wat09, Definition 2.7 (real log canonical threshold), Definition 6.4 eqs
(6.16)–(6.17) (λ and its order as min and max over charts), Theorem 7.1 (3)–(4), Corollary 4.3]
(local form, for the loss |K|) -/
theorem exists_hasLLCExponentsAt_of_analyticOnNhd {d : ℕ} {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin d → ℝ} (hw : w ∈ U) (h0 : K w = 0)
    (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) :
    ∃ (lam : ℚ) (theta : ℕ),
      -- `λ` is a positive rational number
      0 < lam ∧
      -- `θ` is a natural number with `1 ≤ θ ≤ d`
      1 ≤ theta ∧ theta ≤ d ∧
      -- on small balls about `w`, the sublevel volume of `|K|` is `Θ(ε^λ (−log ε)^(θ−1))`
      HasLLCExponentsAt volume (fun x ↦ |K x|) w (lam : ℝ) (theta : ℝ) := by
  obtain ⟨lam, theta, r₀, hlam, h1, hd, hr₀, h⟩ :=
    exists_hasLLCExponentsOn_of_analyticOnNhd hU hK hw h0 hne
  exact ⟨lam, theta, hlam, h1, hd, Filter.eventually_iff_exists_mem.mpr
    ⟨Set.Ioc 0 r₀, Ioc_mem_nhdsGT hr₀, fun r hr ↦ h r hr.1 hr.2⟩⟩

/-- **Existence of the local learning coefficient of a nonnegative real-analytic function**
([Wat09, Definition 2.7, Definition 6.4 eqs (6.16)–(6.17), Theorem 7.1 (3)–(4), Corollary 4.3];
`λ` a positive rational and `θ` a natural number as in [AW05]): the form for `K` itself.

Statement. Let `K` be real-analytic on an open set `U ⊆ ℝ^d`, `w ∈ U` a zero of `K` near which `K`
is not identically zero, and suppose `0 ≤ K` on a neighbourhood of `w`. Then there are a positive
rational number `λ` and a natural number `θ` with `1 ≤ θ ≤ d` such that
`HasLLCExponentsAt volume K w λ θ`: `HasLLCExponentsOn volume (Metric.closedBall w r) K λ θ` for
every small enough radius `r > 0` (every `0 < r ≤ r₀` for some `r₀ > 0`), that is, the
volumes of the sublevel sets `{K ≤ ε}` in the closed cube of half-side `r` about `w` are bounded
above and below by positive multiples of `ε^λ (−log ε)^(θ−1)` as `ε → 0⁺`.

Conventions. The nonnegativity is required near `w` only (`∀ᶠ x in 𝓝 w, 0 ≤ K x`); nonnegativity
on all of `U` is a special case. For `d = 0` the statement is vacuous, as before.

Relation to the source.
* **Gap.** As in `exists_hasLLCExponentsAt_of_analyticOnNhd`, `λ` and `θ` are the local counterparts
  of Watanabe's learning coefficient and its order, which are global, for a model and a prior;
  `K ≥ 0` near `w` is the setting of the sources.

Source statement: [Wat09, Definition 2.7 (real log canonical threshold), Definition 6.4 eqs
(6.16)–(6.17) (λ and its order as min and max over charts), Theorem 7.1 (3)–(4), Corollary 4.3]
(local form, for K ≥ 0 near w) -/
theorem exists_hasLLCExponentsAt_of_analyticOnNhd_of_nonneg {d : ℕ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {K : (Fin d → ℝ) → ℝ} (hK : AnalyticOnNhd ℝ K U) {w : Fin d → ℝ} (hw : w ∈ U)
    (h0 : K w = 0) (hne : ¬ ∀ᶠ x in 𝓝 w, K x = 0) (hK0 : ∀ᶠ x in 𝓝 w, 0 ≤ K x) :
    ∃ (lam : ℚ) (theta : ℕ),
      -- `λ` is a positive rational number
      0 < lam ∧
      -- `θ` is a natural number with `1 ≤ θ ≤ d`
      1 ≤ theta ∧ theta ≤ d ∧
      -- on small balls about `w`, the sublevel volume of `K` is `Θ(ε^λ (−log ε)^(θ−1))`
      HasLLCExponentsAt volume K w (lam : ℝ) (theta : ℝ) := by
  obtain ⟨lam, theta, r₀, hlam, h1, hd, hr₀, h⟩ :=
    exists_hasLLCExponentsOn_of_analyticOnNhd_of_nonneg hU hK hw h0 hne hK0
  exact ⟨lam, theta, hlam, h1, hd, Filter.eventually_iff_exists_mem.mpr
    ⟨Set.Ioc 0 r₀, Ioc_mem_nhdsGT hr₀, fun r hr ↦ h r hr.1 hr.2⟩⟩

end SingularLearningTheory

end ChartForm

end
