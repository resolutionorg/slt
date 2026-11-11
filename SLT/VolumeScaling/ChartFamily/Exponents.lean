/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.ChartFamily.Basic
public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.Chart.Local
import SLT.VolumeScaling.Chart.Sandwich
import SLT.VolumeScaling.ScaleDominance
import SLT.VolumeScaling.SqueezeReadOff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# The general theorem: sublevel-volume exponents of a chart family

For any chart family (a `MonomialChartCover`), the loss on the covered neighborhood `U` has the
family's combinatorial sublevel-volume exponents `(combLam, combTheta)` against the ambient measure.
This is the theorem that turns a resolution of the loss, presented by charts with monomial bounds,
into its local learning coefficient ([Wat09]; [AW05]); the chart form of a real-analytic function
(`SLT.ChartForm.MonomialChartCoverExistence`) feeds it.

The proof squeezes the sublevel volume on `U` between two bounds, each of which scales as the
combinatorial coefficient:

* **Upper bound.** The cover `U \ N ⊆ ⋃_α φ_α '' K_α` gives
  `sublevelVol μ U f ε ≤ ∑_α sublevelVol μ (U ∩ φ_α '' K_α) f ε`
  (`sublevelVol_le_sum_of_cover_ae`). Each summand has the chart exponents `(λ_α, θ_α)` (the
  per-chart-image scaling, `chart_piece_scaling`), and the finite sum is governed by the least
  exponent with its multiplicity (`isTheta_finset_sum_of_dominant`), i.e. by
  `(combLam, combTheta)`.

* **Lower bound.** The leading chart's image piece `U ∩ φ_β '' K_β` (for a `β` realizing the
  coefficient, `exists_leading`) has the combinatorial exponents by the same per-chart-image
  scaling, and its sublevel volume is at most that on `U` (`sublevelVol_inter_le`).

The neighborhood is taken of finite measure as a hypothesis (the cover bound and the
set-monotonicity bound both need it); a bounded neighborhood satisfies it. The ambient loss is
taken measurable as a hypothesis (a polynomial or analytic loss is).
-/

public section

open Asymptotics _root_.Filter Set MeasureTheory
open scoped Topology ENNReal

namespace SingularLearningTheory

namespace MonomialChartCover

variable {Ambient : Type*} [MeasurableSpace Ambient] [TopologicalSpace Ambient]
  {μ : Measure Ambient} {f : Ambient → ℝ} {w : Ambient} {ι : Type*}
  [Fintype ι] [Nonempty ι]

/-- **The general theorem: the exponents of a chart family.** For a chart family
`D`, with the neighborhood of finite measure and the loss
measurable, the loss on the covered neighborhood `D.U` has the family's
combinatorial sublevel-volume exponents `(D.combLam, D.combTheta)` against the
ambient measure: `sublevelVol μ D.U f ε` is bounded above and below by constant
multiples of `ε^{combLam}(-log ε)^{combTheta-1}` as `ε ↓ 0` (`IsTheta`; the
constants are not identified). -/
theorem hasLLCExponentsOn_cover (D : MonomialChartCover Ambient μ f w ι)
    (hf : Measurable f) (hμU : μ D.U ≠ ∞) :
    HasLLCExponentsOn μ D.U f D.combLam (D.combTheta : ℝ) := by
  obtain ⟨β, hlamβ, hthetaβ⟩ := D.exists_leading
  -- Per-chart-image scaling: on each chart image clipped to the
  -- neighborhood, the loss has that chart's exponents.
  have hpiece : ∀ α, HasLLCExponentsOn μ (D.U ∩ (D.chart α).φ '' (D.chart α).K) f
      (D.chart α).lam ((D.chart α).theta : ℝ) := fun α => D.chart_piece_scaling α hf
  -- Upper bound: the finite sum over chart-image pieces is governed by the least
  -- exponent and its multiplicity, i.e. by the combinatorial coefficient.
  have hVhi : (fun ε => ∑ α, sublevelVol μ (D.U ∩ (D.chart α).φ '' (D.chart α).K) f ε)
      =Θ[𝓝[>] (0 : ℝ)] llcScale D.combLam (D.combTheta : ℝ) := by
    have hlam_dom : ∀ α, (D.chart β).lam ≤ (D.chart α).lam := fun α => by
      rw [hlamβ]; exact Finset.inf'_le _ (Finset.mem_univ α)
    have htheta_dom : ∀ α, (D.chart α).lam = (D.chart β).lam →
        ((D.chart α).theta : ℝ) ≤ ((D.chart β).theta : ℝ) := fun α hα => by
      have hαmin : (D.chart α).lam = D.combLam := hα.trans hlamβ
      have hle : (D.chart α).theta ≤ D.combTheta :=
        Finset.le_sup' (fun a => (D.chart a).theta)
          (Finset.mem_filter.mpr ⟨Finset.mem_univ α, hαmin⟩)
      rw [hthetaβ]; exact_mod_cast hle
    have hsum := isTheta_finset_sum_of_dominant
      (F := fun α ε => sublevelVol μ (D.U ∩ (D.chart α).φ '' (D.chart α).K) f ε)
      (lam := fun α => (D.chart α).lam) (theta := fun α => ((D.chart α).theta : ℝ)) β
      (fun α => hpiece α)
      (fun α => Filter.Eventually.of_forall fun ε => sublevelVol_nonneg μ _ f ε)
      hlam_dom htheta_dom
    rw [← hlamβ, ← hthetaβ]
    exact hsum
  -- Lower bound: the leading chart's image piece carries the combinatorial
  -- coefficient (the chart exponents equal it there).
  have hVlo : HasLLCExponentsOn μ (D.U ∩ (D.chart β).φ '' (D.chart β).K) f
      D.combLam (D.combTheta : ℝ) := by
    have hβ := hpiece β
    rwa [hlamβ, hthetaβ] at hβ
  -- Squeeze the sublevel volume on the neighborhood between the two bounds.
  exact HasLLCExponentsOn.of_squeeze hVlo hVhi
    (Filter.Eventually.of_forall fun ε => sublevelVol_nonneg μ _ f ε)
    (Filter.Eventually.of_forall fun ε => sublevelVol_inter_le hμU ε)
    (Filter.Eventually.of_forall fun ε =>
      sublevelVol_le_sum_of_cover_ae hμU D.N_null D.cover ε)

end MonomialChartCover

end SingularLearningTheory
