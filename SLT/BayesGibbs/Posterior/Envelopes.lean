/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Prior.FeatureEnvelope
public import SLT.BayesGibbs.Prior.AEEnvelope
public import SLT.BayesGibbs.EnvelopeSixthMoments
import SLT.BayesGibbs.SixthMoments
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.FreeEnergy.FundamentalConditions

/-!
# Envelopes for the posterior bounds

The bounds on the posterior observables assume a data envelope and an empirical envelope, both
relative to $\sqrt K$. This module builds them from fundamental condition (I) at $s = 6$, an
analytic resolution of the log density ratio $f$, and the empirical processes $\Psi^E_n$ of the
resolved quotients on the charts and $\Psi^T_n$ of $f/\sqrt K$ on the tail $\{K \ge \delta\}$,
which converge in law. It gives a measurable $A \in L^6(q)$ with $|f(x, w)| \le A(x)\sqrt{K(w)}$,
and the envelope $\Lambda_n = \max(\|\Psi^E_n\|, \|\Psi^T_n\|)$, with uniformly bounded sixth
moments and $\sqrt n|K_n(w) - K(w)| \le \Lambda_n\sqrt{K(w)}$, both almost everywhere for the
prior.

## Main results

* `SingularLearningTheory.BayesGibbs.restricted_prior_ne_zero_of_sublevel_pos`: if every sublevel set
  $\{K < \varepsilon\}$ has positive prior mass, the prior is not zero.
* `SingularLearningTheory.EmpiricalProcessLimit.max_empirical_norm_tight`: the maximum of the norms
of two
  empirical processes is bounded in probability, whatever their limit spaces.
* `SingularLearningTheory.BayesGibbs.exists_posterior_envelopes_six`: the two envelopes.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

/-- The positive sublevel-prior hypothesis implies nonzero restricted prior mass. -/
theorem restricted_prior_ne_zero_of_sublevel_pos {d : ℕ}
    {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)) ≠ 0 := by
  apply Measure.measure_univ_pos.mp
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (hvol 1 zero_lt_one).trans_le (lintegral_mono_set inter_subset_left)

/-- The maximum of two empirical-process norms is tight; their limit spaces
may differ, because only separate norm tightness is used. -/
theorem _root_.SingularLearningTheory.EmpiricalProcessLimit.max_empirical_norm_tight
    {X Ω Ω' ΩT U V : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace ΩT]
    [MetricSpace U] [CompactSpace U] [MetricSpace V] [CompactSpace V]
    {q : Measure X} {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {PT : Measure ΩT} [IsProbabilityMeasure PT]
    {f : X → U → ℝ} {g : X → V → ℝ} {Xs : ℕ → Ω → X}
    (E : EmpiricalProcessLimit q f Xs P P') (T : EmpiricalProcessLimit q g Xs P PT) :
    ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < |max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖|} ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨M₁, N₁, h₁⟩ := E.tendsto.eventually_measure_norm_gt_le (half_pos hη)
  obtain ⟨M₂, N₂, h₂⟩ := T.tendsto.eventually_measure_norm_gt_le (half_pos hη)
  refine ⟨max M₁ M₂, max N₁ N₂, fun n hn ↦ ?_⟩
  have hc : {ω | max M₁ M₂ < |max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖|} ⊆
      {ω | M₁ < ‖E.Ψ n ω‖} ∪ {ω | M₂ < ‖T.Ψ n ω‖} := by
    intro ω hω
    change max M₁ M₂ < |max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖| at hω
    rw [abs_of_nonneg (le_max_of_le_left (norm_nonneg _))] at hω
    rcases lt_max_iff.mp hω with h | h
    · exact Or.inl ((le_max_left _ _).trans_lt h)
    · exact Or.inr ((le_max_right _ _).trans_lt h)
  calc
    _ ≤ P ({ω | M₁ < ‖E.Ψ n ω‖} ∪ {ω | M₂ < ‖T.Ψ n ω‖}) := measure_mono hc
    _ ≤ P {ω | M₁ < ‖E.Ψ n ω‖} + P {ω | M₂ < ‖T.Ψ n ω‖} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
      add_le_add (h₁ n (le_of_max_le_left hn)) (h₂ n (le_of_max_le_right hn))
    _ = ENNReal.ofReal η := by rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- Assemble the data and empirical envelopes from the analytic
chart and tail processes. The final posterior estimates consume these bounds;
none of them is an extra statistical assumption. -/
theorem exists_posterior_envelopes_six
    {d : ℕ} {X Ω Ω' ΩT : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace ΩT]
    {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {PT : Measure ΩT} [IsProbabilityMeasure PT]
    {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (R : ResolutionAtlas K φ W) (I : FundamentalConditionI 6 q f K W)
    (L : R.AnalyticResolvedLikelihood 6 q f)
    (hW : IsCompact W) (hφi : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f))
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    [CompactSpace {w // w ∈ W ∧ R.δ ≤ K w}]
    (E : EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P PT) :
    let Λ := fun n ω ↦ max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖
    ∃ A : X → ℝ, Measurable A ∧ (∀ x, 0 ≤ A x) ∧ MemLp A 6 q ∧
      (∀ᵐ x ∂q, ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
        |f x w| ≤ A x * Real.sqrt (K w)) ∧
      (∀ n, Measurable (Λ n)) ∧ (∀ n ω, 0 ≤ Λ n ω) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ n, Integrable (fun ω ↦ Λ n ω ^ 6) P ∧
        (∫ ω, Λ n ω ^ 6 ∂P) ≤ C) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P,
        ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
          Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ Λ n ω * Real.sqrt (K w)) := by
  letI : MetricSpace ((α : R.ι) × cube d (R.b α)) := Metric.Sigma.metricSpace
  dsimp only
  obtain ⟨A, hAm, hA0, hA6, hAf⟩ :=
    exists_prior_feature_envelope_six R I L hW hφi hf hcont hX hlaw hind E T
  obtain ⟨CE, hCE, hE⟩ := EmpiricalProcessLimit.empirical_norm_sixth_moment
      (U := (α : R.ι) × cube d (R.b α)) E (L.momentBound_chart_six hX hlaw hind E)
  obtain ⟨CT, hCT, hT⟩ := EmpiricalProcessLimit.empirical_norm_sixth_moment
      (U := {w // w ∈ W ∧ R.δ ≤ K w}) T (I.momentBound_tail_six hW hcont R.δ_pos hX hlaw hind T)
  have hm := max_envelope_sixth_moment
    (F := fun n ω ↦ ‖E.Ψ n ω‖) (G := fun n ω ↦ ‖T.Ψ n ω‖)
    (fun n ↦ (E.Ψ_measurable n).norm) (fun n ↦ (T.Ψ_measurable n).norm)
    (fun n ↦ (hE n).1) (fun n ↦ (hT n).1) (fun n ↦ (hE n).2) (fun n ↦ (hT n).2)
  refine ⟨A, hAm, hA0, hA6, ?_, fun n ↦ (E.Ψ_measurable n).norm.max (T.Ψ_measurable n).norm,
    fun n ω ↦ le_max_of_le_left (norm_nonneg _), ⟨CE + CT, add_nonneg hCE hCT, hm⟩, ?_⟩
  · simpa only [mul_comm] using hAf
  · intro n hn
    simpa only [mul_comm] using ae_relative_envelope_of_chart_and_tail R L.toResolvedLikelihood
      hW.measurableSet hφi hf I.K_eq hX hlaw E T hn

end SingularLearningTheory.BayesGibbs
