/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.FreeEnergy.FundamentalConditions

/-!
# Lowering the moment index of the analytic hypotheses

Fundamental condition (I) and an analytic resolved likelihood carry a moment index $s$: the log
density ratio is analytic as a map into $L^s(q)$, and the local expansions of its resolved
quotients on the charts have coefficients in $L^s(q)$. On a probability space
$L^s(q) \subseteq L^t(q)$ for $t \le s$, so the hypotheses at index $s$ give the same hypotheses
at a lower index $t$, with the same loss, parameter set and coefficient functions:
`SingularLearningTheory.FundamentalConditionI.monoExponent` for $2 \le t \le s$,
`SingularLearningTheory.ResolutionAtlas.AnalyticResolvedLikelihood.monoExponent`, and
`SingularLearningTheory.L2Expansion.HigherMoment.mono_exponent` for the local expansions. Results
stated at $s = 4$, such as those on maximum likelihood, then apply under hypotheses at $s = 6$.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

variable {X : Type*} [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

namespace L2Expansion

variable {A : Type*} [PseudoMetricSpace A] {f : X → A → ℝ} {B : Set A}
  {E : L2Expansion q f B} {s t : ℝ≥0∞}

/-- On a probability space, the local expansion's coefficient-sum bound decreases
when its moment exponent decreases. -/
theorem HigherMoment.mono_exponent (h : E.HigherMoment s) (hts : t ≤ s) : E.HigherMoment t := by
  refine ⟨fun i ↦ (h.1 i).mono_exponent hts, ?_⟩
  refine Summable.of_nonneg_of_le
    (fun i ↦ mul_nonneg (E.c_nonneg i) ENNReal.toReal_nonneg) (fun i ↦ ?_) h.2
  exact mul_le_mul_of_nonneg_left
    (ENNReal.toReal_mono (h.1 i).eLpNorm_ne_top (eLpNorm_le_eLpNorm_of_exponent_le hts))
    (E.c_nonneg i)

end L2Expansion

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {f : X → (Fin d → ℝ) → ℝ} {s t : ℝ≥0∞}

/-- A lower-moment fundamental condition, with the same K, f, W and analytic domain. -/
theorem FundamentalConditionI.monoExponent [Fact (1 ≤ s)] [Fact (1 ≤ t)]
    (I : FundamentalConditionI s q f K W) (ht2 : 2 ≤ t) (hts : t ≤ s) :
    FundamentalConditionI t q f K W := by
  obtain ⟨U, hU, hWU, F, hF, hFf⟩ := I.ls_analytic
  exact ⟨ht2, I.K_eq, U, hU, hWU, fun w ↦ lpInclusion q hts (F w),
    (lpInclusion q hts).comp_analyticOnNhd hF,
    fun w hw ↦ (coeFn_lpInclusion q hts (F w)).trans (hFf w hw)⟩

/-- Preserve the coefficient functions; only the local moment certificate changes. -/
@[expose] def ResolutionAtlas.AnalyticResolvedLikelihood.monoExponent {R : ResolutionAtlas K φ W}
    (L : R.AnalyticResolvedLikelihood s q f) (hts : t ≤ s) :
    R.AnalyticResolvedLikelihood t q f where
  toResolvedLikelihood := L.toResolvedLikelihood
  memLp := L.memLp
  loc := by
    intro α u
    obtain ⟨B, hB, hu, E, hE⟩ := L.loc α u
    exact ⟨B, hB, hu, E, hE.mono_exponent hts⟩

end SingularLearningTheory
