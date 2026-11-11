/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.Resolution.Chart.Family
public import SLT.Setting.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import SLT.EmpiricalProcess.Borel
import SLT.EmpiricalProcess.LimitOfAnalytic
import SLT.EmpiricalProcess.Transport
import SLT.FreeEnergy.Discharge
import SLT.Resolution.PieceTransport
public import SLT.StandardForm.Defs

/-!
# The standard form of the log likelihood ratio

The theorems of `SLTChallenge/StandardForm.lean`, proved from the library: the resolved form on
each piece from the library's chart representative
(`exists_chart_representative_with_analytic_of_chart`, fed the piece map), and the empirical
process limit on the pieces from `exists_empiricalProcessLimit_of_l2Expansion`. The definitions
are in `SLT/StandardForm/Defs.lean`.
-/

@[expose] public section

-- These statements mirror SLTChallenge word for word, so they keep hypotheses of the book
-- that the delegated proofs here don't need.
set_option linter.unusedVariables false

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open Real (exp log)
open scoped ENNReal

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

/-! ### Consequences of the standing assumptions

The standing assumptions give what singular learning theory usually assumes of the reference
parameter and the excess loss. The reference parameter `w₀` minimises `K` on `W`, and the average
log loss `L` when `log p(·|w₀)` is integrable. Every other minimiser of `K` in `W` has the same
model up to a `q`-null set, so it gives the same `K` and satisfies the standing assumptions too:
nothing depends on which minimiser is the reference parameter, and relatively finite variance
holds at every minimiser, as the book requires. Finally `K` is real analytic on an open
neighbourhood of `W`. -/

/-- The reference parameter minimises the excess loss on `W`: `K(w₀) = 0 ≤ K(w)` for every
`w ∈ W`, by relatively finite variance. -/
theorem StandingAssumptions.isMinOn_excessLoss {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    {W : Set (Fin d → ℝ)} {w₀ : Fin d → ℝ} (h : StandingAssumptions s q p W w₀) :
    excessLoss q p w₀ w₀ = 0 ∧ IsMinOn (excessLoss q p w₀) W w₀ := by
  refine ⟨excessLoss_self q p w₀, isMinOn_iff.mpr fun w hw ↦ ?_⟩
  rw [excessLoss_self q p w₀]
  exact h.rfv.excessLoss_nonneg w hw

/-- When `log p(·|w₀)` is `q`-integrable, the reference parameter minimises the average log loss
`L(w) = −E_q[log p(X|w)]` on `W`. Relatively finite variance makes every `log p(·|w)` with
`w ∈ W` integrable, so that `K = L − L(w₀)` on `W`. -/
theorem StandingAssumptions.isMinOn_expectedNegativeLogLikelihood {d : ℕ} {X : Type*}
    [MeasurableSpace X] {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} [IsProbabilityMeasure q]
    {p : (Fin d → ℝ) → X → ℝ} {W : Set (Fin d → ℝ)} {w₀ : Fin d → ℝ}
    (h : StandingAssumptions s q p W w₀) (hL : Integrable (fun x ↦ log (p w₀ x)) q) :
    IsMinOn (expectedNegativeLogLikelihood q p) W w₀ := by
  refine isMinOn_iff.mpr fun w hw ↦ ?_
  obtain ⟨C, hC, hb⟩ := h.rfv
  have hf : Integrable (fun x ↦ logDensityRatio p w₀ x w) q := (hb w hw).1.integrable one_le_two
  -- `log p(x|w) = log p(x|w₀) − f(x, w)` wherever both densities are positive
  have hlog : (fun x ↦ log (p w x)) =ᵐ[q] fun x ↦ log (p w₀ x) - logDensityRatio p w₀ x w := by
    filter_upwards [h.pos] with x hx
    rw [logDensityRatio, Real.log_div (hx w₀ h.mem).ne' (hx w hw).ne']
    ring
  have hK : 0 ≤ ∫ x, logDensityRatio p w₀ x w ∂q := h.rfv.excessLoss_nonneg w hw
  simp only [expectedNegativeLogLikelihood]
  rw [integral_congr_ae hlog, integral_sub hL hf]
  linarith

/-- Essential uniqueness ([Wat18, Definition 6 and Lemma 3]): every minimiser `w₀'` of the excess
loss in `W` has the same model as the reference parameter, `p(·|w₀') = p(·|w₀)` for `q`-almost
every `x`. -/
theorem StandingAssumptions.ae_eq_of_excessLoss_eq_zero {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    {W : Set (Fin d → ℝ)} {w₀ w₀' : Fin d → ℝ} (h : StandingAssumptions s q p W w₀)
    (hw₀' : w₀' ∈ W) (hK : excessLoss q p w₀ w₀' = 0) :
    p w₀' =ᵐ[q] p w₀ := by
  obtain ⟨C, hC, hb⟩ := h.rfv
  -- RFV at the zero `w₀'` of `K` forces `E_q[f(·, w₀')²] = 0`
  have h0 : 0 ≤ ∫ x, logDensityRatio p w₀ x w₀' ^ 2 ∂q := integral_nonneg fun x ↦ sq_nonneg _
  have h1 := (hb w₀' hw₀').2
  rw [hK] at h1
  have hsq : (fun x ↦ logDensityRatio p w₀ x w₀' ^ 2) =ᵐ[q] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun x ↦ sq_nonneg _) (hb w₀' hw₀').1.integrable_sq).mp
      (le_antisymm (by nlinarith) h0)
  filter_upwards [hsq, h.pos] with x hx hpos
  have hf : logDensityRatio p w₀ x w₀' = 0 := by simpa using hx
  rw [logDensityRatio, Real.log_div (hpos w₀ h.mem).ne' (hpos w₀' hw₀').ne', sub_eq_zero] at hf
  exact Real.log_injOn_pos (Set.mem_Ioi.2 (hpos w₀' hw₀')) (Set.mem_Ioi.2 (hpos w₀ h.mem)) hf.symm

/-- The standing assumptions do not depend on which minimiser is the reference parameter: another
minimiser `w₀'` of the excess loss in `W` gives the same excess loss and satisfies the standing
assumptions itself. The book observes after [Wat18, Lemma 3] that `f(x, w₀, w)` does not depend
on `w₀`. -/
theorem StandingAssumptions.of_excessLoss_eq_zero {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} {p : (Fin d → ℝ) → X → ℝ}
    {W : Set (Fin d → ℝ)} {w₀ w₀' : Fin d → ℝ} (h : StandingAssumptions s q p W w₀)
    (hw₀' : w₀' ∈ W) (hK : excessLoss q p w₀ w₀' = 0) :
    excessLoss q p w₀' = excessLoss q p w₀ ∧ StandingAssumptions s q p W w₀' := by
  have he := h.ae_eq_of_excessLoss_eq_zero hw₀' hK
  -- off one `q`-null set, `f` relative to `w₀'` and to `w₀` agree at every `w`
  have hf : ∀ᵐ x ∂q, ∀ w, logDensityRatio p w₀' x w = logDensityRatio p w₀ x w := by
    filter_upwards [he] with x hx w
    simp only [logDensityRatio, hx]
  have hKeq : excessLoss q p w₀' = excessLoss q p w₀ :=
    funext fun w ↦ integral_congr_ae (hf.mono fun x hx ↦ hx w)
  refine ⟨hKeq, h.measurable, h.compact, h.pos, hw₀', ?_, ?_, ?_⟩
  · obtain ⟨C, hC, hb⟩ := h.rfv
    refine ⟨C, hC, fun w hw ↦ ⟨(hb w hw).1.ae_eq (hf.mono fun x hx ↦ (hx w).symm), ?_⟩⟩
    have hsq : ∫ x, logDensityRatio p w₀' x w ^ 2 ∂q = ∫ x, logDensityRatio p w₀ x w ^ 2 ∂q :=
      integral_congr_ae (hf.mono fun x hx ↦ by simp only [hx w])
    rw [hKeq, hsq]
    exact (hb w hw).2
  · obtain ⟨hs, hKe, U, hU, hWU, F, hF, hFae⟩ := h.conditionI
    refine ⟨hs, fun w ↦ ?_, U, hU, hWU, F, hF,
      fun w hw ↦ (hFae w hw).trans (hf.mono fun x hx ↦ (hx w).symm)⟩
    rw [hKeq, hKe w]
    exact integral_congr_ae (hf.mono fun x hx ↦ (hx w).symm)
  · filter_upwards [h.continuousOn, hf] with x hc hx
    exact hc.congr fun w _ ↦ hx w

/-- The excess loss is real analytic on an open neighbourhood of `W`, by fundamental condition I:
`K = ∫ f(x, ·) q(dx)` composes the `L^s(q)`-valued analytic map `w ↦ f(·, w)` with integration
against `q`. -/
theorem StandingAssumptions.analyticOnNhd_excessLoss {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} [IsProbabilityMeasure q]
    {p : (Fin d → ℝ) → X → ℝ} {W : Set (Fin d → ℝ)} {w₀ : Fin d → ℝ}
    (h : StandingAssumptions s q p W w₀) :
    ∃ U : Set (Fin d → ℝ), IsOpen U ∧ W ⊆ U ∧ AnalyticOnNhd ℝ (excessLoss q p w₀) U := by
  exact h.conditionI.exists_analyticOnNhd_K

/-! ## The resolved log density ratio -/

section ResolvedLogDensityRatio

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- **Resolved form of the log density ratio** for a given resolution `R` and chart family `F`: the
log density ratio has resolved coefficients on every piece. The continuity of `f(x, ·)` on `W` for
q-a.e. `x` lets the coefficients be chosen continuous in `u`. `W` is closed, so that the closed cube
of every piece lies over `W`, where `f` is analytic: the closed admissible orthants lie over
`closure (interior W)`, and a chart of `F` may be centred over a boundary point of a non-closed `W`
at which `f(x, ·)` is unconstrained.

Relation to the source.
* **Strengthening.** Stated for every chart family of every resolution of $K$ and every index $s$,
  and $w_0$ need not lie in $W$.
* **Strengthening.** The factorisation holds for $q$-almost every $x$ simultaneously for every $u$,
  and $a(x, \cdot)$ is continuous on the cube for every $x$; the book's eq. (6.5) is an identity in
  $L^s(q)$ at each $u$.
* **Gap.** $W$ is assumed closed, and $f(x, \cdot)$ continuous on $W$ for $q$-almost every $x$.

Source statement: [Wat09, Theorem 6.1] -/
theorem exists_resolvedLogDensityRatio {d : ℕ} {X : Type*} [MeasurableSpace X]
    -- data distribution
    (q : Measure X) [IsProbabilityMeasure q]
    -- model and parameter space
    (p : (Fin d → ℝ) → X → ℝ)
    (W : Set (Fin d → ℝ)) (hWc : IsClosed W) (φ : (Fin d → ℝ) → ℝ)
    -- the index of fundamental condition I
    (s : ℝ≥0∞) [Fact (1 ≤ s)]
    -- `w₀` need not minimise `L`: RFV already gives `K ≥ 0` on `W`, even if `w₀ ∉ W`.
    -- A piece of `F` sits over a zero `w₀'` of `K` in `W`, and RFV then gives
    -- `p(x|w₀) = p(x|w₀')` for q-a.e. `x`.
    (w₀ : Fin d → ℝ)
    (I : FundamentalConditionI s q (logDensityRatio p w₀) (excessLoss q p w₀) W)
    (hRFV : RelativelyFiniteVariance q p w₀ W)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W)
    (R : SLTResolution (excessLoss q p w₀) φ W) (F : R.ChartFamily) :
    Nonempty (ResolvedLogDensityRatio s F q (logDensityRatio p w₀)) :=
  by
  classical
  obtain ⟨U, hU, hWU, Fa, hF, hFf⟩ := I.ls_analytic
  obtain ⟨C, hC, hRFV'⟩ := hRFV.exists_integral_sq_le_inv_mul
  have hcontg : ∀ α : F.Piece, ∀ᵐ x ∂q,
      Continuous fun u : cube d α.radius ↦ logDensityRatio p w₀ x (α.map u) := by
    intro α
    filter_upwards [hcont] with x hx
    exact hx.comp_continuous (α.analyticOnNhd_map.continuousOn.comp_continuous
      continuous_subtype_val fun u ↦ u.2) fun u ↦ α.map_mem hWc u.2
  have h := fun α : F.Piece ↦ exists_chart_representative_with_analytic_of_chart I.two_le I.K_eq
    hWU hF hFf hC hRFV' (F.chart α.chart).radius_pos α.analyticOnNhd_map
    (fun u hu ↦ α.map_mem hWc hu) (fun u hu ↦ α.loss_map hu) (hcontg α)
  choose A a hA ha_eq ha_meas ha_factor ha_mean ha_memLp ha_loc using h
  have hmem : ∀ α : F.Piece, ∀ u ∈ cube d α.radius, u ∈ cube d α.radius :=
    fun α u hu ↦ by assumption
  let a' : F.Piece → X → (Fin d → ℝ) → ℝ := fun α x u ↦
    if hu : u ∈ cube d α.radius then a α x ⟨u, hu⟩ else A α u x
  have ha' : ∀ α x (u : cube d α.radius), a' α x u = a α x u := by
    intro α x u
    simp only [a', dite_eq_left u.2]
  refine ⟨⟨a', ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro α u
    have hh : (fun x ↦ a' α x u) = fun x ↦ a α x ⟨u, hmem α u u.2⟩ :=
      funext fun x ↦ ha' α x ⟨u, hmem α u u.2⟩
    rw [hh]
    exact (continuous_eval_const (⟨u, hmem α u u.2⟩ :
      cube d α.radius)).measurable.comp (ha_meas α)
  · intro α x
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun u : cube d α.radius ↦ a' α x u)
    simpa only [ha'] using (a α x).continuous
  · intro α
    refine ⟨{u | AnalyticAt ℝ (A α) u}, isOpen_analyticAt ℝ (A α), hA α,
      A α, fun u hu ↦ hu, ?_⟩
    intro u _
    by_cases hu : u ∈ cube d α.radius
    · simpa only [a', dite_eq_left hu] using ha_eq α ⟨u, hu⟩
    · exact Filter.Eventually.of_forall fun x ↦ by simp only [a', dite_eq_right hu]
  · intro α
    filter_upwards [ha_factor α] with x hx u
    rw [hx ⟨u, hmem α u u.2⟩, ha' α x ⟨u, hmem α u u.2⟩]
  · intro α u
    rw [← ha_mean α ⟨u, hmem α u u.2⟩]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ha' α x ⟨u, hmem α u u.2⟩)

/-- **Limit of the resolved empirical process** for the resolved coefficients: their centred
empirical process `Ψ_n(u) = n^{-1/2} Σ (a(X_i, u) − E a(X, u))` on the pieces converges in law to a
Gaussian process `Ψ`, for every index `s ≥ 2`. The free energy statements use `ξ = −Ψ`.

Relation to the source.
* **Correction.** The standard form [Wat09, eq. (6.10)] and the empirical process [Wat09, eq.
  (6.11)] as printed have opposite signs: together they give $K_n(g(u)) = 2u^{2k} - K_n(g(u))$.
  [Wat09, eq. (1.18)] has the sign of (6.10). The process $\Psi_n$ here is (6.11) as printed, and
  the statements of [Wat09, §6.2–§6.4] use $\xi = -\Psi$, the sign of (6.10).
* **Unformalised.** The relative process $\psi_n$ on $\{K > \varepsilon\}$ of part (1) and the
  moments of part (2) have no statement here.

Source statement: [Wat09, Theorem 6.2(1)] -/
theorem exists_empiricalProcessLimit {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s)
    {q : Measure X} [IsProbabilityMeasure q]
    {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {f : X → (Fin d → ℝ) → ℝ} {R : SLTResolution K φ W} {F : R.ChartFamily}
    (L : ResolvedLogDensityRatio s F q f)
    {Ω : Type*} [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
    [IsProbabilityMeasure P] (hXs : IsIIDSample q Xs P) :
    ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P'),
      Nonempty (EmpiricalProcessLimit q
        (fun x (v : (α : F.Piece) × cube d α.radius) ↦ L.a v.1 x v.2)
        Xs P P') :=
  by
  have hX := hXs.measurePreserving
  have hIndep := hXs.indep
  let _ : MetricSpace ((α : F.Piece) × cube d α.radius) := Metric.Sigma.metricSpace
  have hs2 : (2 : ℝ≥0∞) ≤ s := hs
  -- local `L²(q)` expansions of `a_α` around every point of the cube, from its analyticity
  have hloc : ∀ α (u : cube d α.radius), ∃ B : Set (cube d α.radius), IsOpen B ∧ u ∈ B ∧
      Nonempty (L2Expansion q (fun x (v : cube d α.radius) ↦ L.a α x v) B) := by
    intro α u
    obtain ⟨U, -, hU, A, hA, hAeq⟩ := L.ls_analytic α
    obtain ⟨p, r, hpr⟩ := hA u (hU u.2)
    obtain ⟨ρ, hρ, hrep⟩ := HasFPowerSeriesOnBall.exists_l2Expansion hs2 hpr
      (fun v : cube d α.radius ↦ (v : Fin d → ℝ)) (fun x v ↦ L.a α x v)
      (fun v _ ↦ hAeq v (hU v.2))
    refine ⟨{v | dist (v : Fin d → ℝ) u < ρ},
      isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const,
      by simpa using hρ, ?_⟩
    obtain ⟨E, -⟩ := hrep _ (fun v hv ↦ le_of_lt hv)
      (fun v _ w _ ↦ le_of_eq (Subtype.dist_eq v w).symm)
    exact ⟨E⟩
  have hmemLp : ∀ α (u : cube d α.radius), MemLp (fun x ↦ L.a α x u) 2 q := by
    intro α u
    obtain ⟨U, -, hU, A, -, hA⟩ := L.ls_analytic α
    exact ((Lp.memLp (A u)).mono_exponent hs2).ae_eq (hA u (hU u.2))
  have hmean : Continuous fun v : (α : F.Piece) × cube d α.radius ↦ ∫ x, L.a v.1 x v.2 ∂q := by
    have : (fun v : (α : F.Piece) × cube d α.radius ↦ ∫ x, L.a v.1 x v.2 ∂q)
        = fun v ↦ ∏ j, (v.2 : Fin d → ℝ) j ^ v.1.k j := funext fun v ↦ L.mean v.1 v.2
    rw [this]
    refine continuous_sigma fun α ↦ ?_
    change Continuous fun a : cube d α.radius ↦ ∏ j, (a : Fin d → ℝ) j ^ α.k j
    exact continuous_finsetProd _ fun j _ ↦
      ((continuous_apply j).comp continuous_subtype_val).pow _
  have hloc' : ∀ v : (α : F.Piece) × cube d α.radius, ∃ B, IsOpen B ∧ v ∈ B ∧
      Nonempty (L2Expansion q (fun x (p : (α : F.Piece) × cube d α.radius) ↦ L.a p.1 x p.2) B) := by
    rintro ⟨α, u⟩
    obtain ⟨B, hBo, huB, ⟨E⟩⟩ := hloc α u
    have hι : ∀ u ∈ B, ∀ v ∈ B,
        dist (⟨α, u⟩ : (α : F.Piece) × cube d α.radius) ⟨α, v⟩ = dist u v := fun u _ v _ ↦ by
      change Metric.Sigma.dist _ _ = _
      simp [Metric.Sigma.dist]
    have hg : ∀ x, ∀ u ∈ B, (fun x (p : (α : F.Piece) × cube d α.radius) ↦ L.a p.1 x p.2) x
        (⟨α, u⟩ : (α : F.Piece) × cube d α.radius) = L.a α x u := fun _ _ _ ↦ rfl
    refine ⟨Sigma.mk α '' B, isOpenMap_sigmaMk _ hBo, ⟨u, huB, rfl⟩, ⟨?_⟩⟩
    exact E.image (fun v : cube d α.radius ↦ (⟨α, v⟩ : (α : F.Piece) × cube d α.radius)) hι _ hg
  obtain ⟨P', hP', ⟨E⟩⟩ := exists_empiricalProcessLimit_of_l2Expansion
    (f := fun x (v : (α : F.Piece) × cube d α.radius) ↦ L.a v.1 x v.2)
    (fun v ↦ L.a_measurable v.1 v.2)
    (Eventually.of_forall fun x ↦ continuous_sigma fun α ↦
      continuousOn_iff_continuous_domRestrict.mp (L.a_continuous α x))
    (fun v ↦ hmemLp v.1 v.2) hmean hloc' (fun i ↦ (hX i).measurable) (fun i ↦ (hX i).map_eq)
    hIndep
  exact ⟨_, inferInstance, P', hP', ⟨E⟩⟩

/-- **Standard form of the log likelihood ratio.** For resolved coefficients `a` on the pieces of a
chart family and an i.i.d. sample, almost surely, for every `n ≥ 1`, every piece `α` and every `u`
in its cube, `K_n(g_α(u)) = u^{2k} − n^{-1/2} u^k ξ_n(u)`, where
`ξ_n(u) = n^{-1/2} Σ_{i<n} (u^k − a(X_i, u))` is the negative of the empirical process of `a`.

Source statement: [Wat09, Main Theorem 6.1] -/
theorem empiricalExcessLoss_standardForm {d : ℕ} {X : Type*} [MeasurableSpace X]
    {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {p : (Fin d → ℝ) → X → ℝ} {w₀ : Fin d → ℝ} {R : SLTResolution K φ W} {F : R.ChartFamily}
    (L : ResolvedLogDensityRatio s F q (logDensityRatio p w₀))
    {Ω : Type*} [MeasurableSpace Ω] (Xs : ℕ → Ω → X) (P : Measure Ω)
    (hXs : IsIIDSample q Xs P) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ), 1 ≤ n → ∀ (α : F.Piece) (u : cube d α.radius),
      let uk := ∏ j, (u : Fin d → ℝ) j ^ α.k j
      -- the book's process of (6.10), with the sign of the standard form
      let ξn := -empiricalProcess q (L.a α) Xs n ω (u : Fin d → ℝ)
      empiricalExcessLoss p w₀ Xs n ω (α.map u) = uk ^ 2 - (√(n : ℝ))⁻¹ * uk * ξn := by
  have hfac : ∀ (α : F.Piece) (i : ℕ), ∀ᵐ ω ∂P, ∀ u : cube d α.radius,
      logDensityRatio p w₀ (Xs i ω) (α.map u) =
        (∏ j, (u : Fin d → ℝ) j ^ α.k j) * L.a α (Xs i ω) u :=
    fun α i ↦ (hXs.measurePreserving i).quasiMeasurePreserving.ae (L.factor α)
  have hall : ∀ᵐ ω ∂P, ∀ (α : F.Piece) (i : ℕ) (u : cube d α.radius),
      logDensityRatio p w₀ (Xs i ω) (α.map u) =
        (∏ j, (u : Fin d → ℝ) j ^ α.k j) * L.a α (Xs i ω) u := by
    rw [ae_all_iff]
    exact fun α ↦ ae_all_iff.mpr (hfac α)
  filter_upwards [hall] with ω hω n hn α u
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : (√(n : ℝ))⁻¹ * (√(n : ℝ))⁻¹ = (n : ℝ)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hn'.le]
  simp only [empiricalExcessLoss, empiricalProcess, L.mean α u]
  rw [Finset.sum_congr rfl fun i _ ↦ hω α i u, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, ← Finset.mul_sum]
  have : (√(n : ℝ))⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ α.k j) *
      -((√(n : ℝ))⁻¹ * ((∑ i ∈ Finset.range n, L.a α (Xs i ω) u) -
        n * ∏ j, (u : Fin d → ℝ) j ^ α.k j)) =
      -((√(n : ℝ))⁻¹ * (√(n : ℝ))⁻¹) * (∏ j, (u : Fin d → ℝ) j ^ α.k j) *
        ((∑ i ∈ Finset.range n, L.a α (Xs i ω) u) - n * ∏ j, (u : Fin d → ℝ) j ^ α.k j) := by
    ring
  rw [this, hs]
  field_simp
  ring

end ResolvedLogDensityRatio

end SingularLearningTheory
