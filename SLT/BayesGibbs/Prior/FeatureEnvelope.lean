/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FeatureEnvelopeSix
public import SLT.BayesGibbs.Prior.AETransport
import SLT.BayesGibbs.SixthMoments
import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.StandardForm.FundamentalConditionI
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# A sixth-moment envelope for the log density ratio under the prior

Under fundamental condition (I) at $s = 6$ and an analytic resolution of the log density ratio
$f$, with weak limits of the empirical processes on the charts and on the tail
$\{K \ge \delta\}$, there is one measurable data envelope $A \ge 0$ in $L^6(q)$ with
$|f(x, w)| \le \sqrt{K(w)}A(x)$ for $q$-almost every $x$ and prior-almost every $w$
(`SingularLearningTheory.BayesGibbs.exists_prior_feature_envelope_six`). The envelope is the sum of
envelopes of the chart feature $a(x, u)$, where $f(x, g(u)) = u^k a(x, u)$ and $\sqrt{K} = u^k$,
and of the tail feature $f / \sqrt{K}$. The transport of the prior to the charts, not
coverage of every parameter by the charts, joins the two. This is the envelope $A$ that the
bounds on the posterior observables of [Wat09, Theorem 6.8] take.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

/-- A single measurable L6 data envelope controls |f(x,w)|/√K(w)
prior-almost everywhere, simultaneously on a common q-full event. The prior
transport, not pointwise chart coverage, joins chart and tail controls. -/
theorem exists_prior_feature_envelope_six
    {d : ℕ} {X Ω Ω' ΩT : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace ΩT]
    {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {PT : Measure ΩT} [IsProbabilityMeasure PT]
    {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (R : ResolutionAtlas K φ W) (I : FundamentalConditionI 6 q f K W)
    (L : R.AnalyticResolvedLikelihood 6 q f)
    (hW : IsCompact W) (hφ : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f))
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    (E : EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P PT) :
    ∃ A : X → ℝ, Measurable A ∧ (∀ x, 0 ≤ A x) ∧ MemLp A 6 q ∧
      ∀ᵐ x ∂q, ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
        |f x w| ≤ Real.sqrt (K w) * A x := by
  letI : MetricSpace ((α : R.ι) × cube d (R.b α)) := Metric.Sigma.metricSpace
  haveI : CompactSpace {w // w ∈ W ∧ R.δ ≤ K w} :=
    isCompact_iff_compactSpace.mp (I.isCompact_tail hW R.δ)
  have hmeanE : Continuous fun u : (α : R.ι) × cube d (R.b α) ↦ ∫ x, L.a u.1 x u.2 ∂q := by
    have heq : (fun u : (α : R.ι) × cube d (R.b α) ↦ ∫ x, L.a u.1 x u.2 ∂q) =
        fun u ↦ ∏ j, (u.2 : Fin d → ℝ) j ^ R.k u.1 j := funext fun u ↦ L.mean u.1 u.2
    rw [heq]
    refine continuous_sigma fun α ↦ ?_
    change Continuous (fun u : cube d (R.b α) ↦ ∏ j, (u : Fin d → ℝ) j ^ R.k α j)
    exact continuous_finsetProd _ fun j _ ↦
      ((continuous_apply j).comp continuous_subtype_val).pow _
  obtain ⟨A₀, hA₀m, hA₀0, hA₀Lp, hA₀⟩ := EmpiricalProcessLimit.exists_feature_envelope_six E
    (L.momentBound_chart_six hX hlaw hind E) (hX 0) (hlaw 0)
    (fun u ↦ (continuous_eval_const u.2).measurable.comp (L.a_measurable u.1))
    (Eventually.of_forall fun x ↦ continuous_sigma fun α ↦ (L.a α x).continuous) hmeanE
  have hKT : Continuous fun w : {w // w ∈ W ∧ R.δ ≤ K w} ↦ K w :=
    I.continuousOn_K.comp_continuous continuous_subtype_val fun w ↦ w.2.1
  have hmeanT : Continuous fun w : {w // w ∈ W ∧ R.δ ≤ K w} ↦
      ∫ x, f x w / Real.sqrt (K w) ∂q := by
    have heq : (fun w : {w // w ∈ W ∧ R.δ ≤ K w} ↦ ∫ x, f x w / Real.sqrt (K w) ∂q) =
        fun w : {w // w ∈ W ∧ R.δ ≤ K w} ↦ K w / Real.sqrt (K w) := by
      funext w
      rw [integral_div, ← I.K_eq w]
    rw [heq]
    exact hKT.div (Real.continuous_sqrt.comp hKT)
      (fun w ↦ (Real.sqrt_pos.mpr (R.δ_pos.trans_le w.2.2)).ne')
  have hcontT : ∀ᵐ x ∂q, Continuous fun w : {w // w ∈ W ∧ R.δ ≤ K w} ↦
      f x w / Real.sqrt (K w) := by
    filter_upwards [I.ae_continuousOn_tail hcont R.δ_pos] with x hx
    exact continuousOn_iff_continuous_domRestrict.mp hx
  obtain ⟨A₁, hA₁m, hA₁0, hA₁Lp, hA₁⟩ := EmpiricalProcessLimit.exists_feature_envelope_six T
    (I.momentBound_tail_six hW hcont R.δ_pos hX hlaw hind T) (hX 0) (hlaw 0)
    (fun w ↦ hf.of_uncurry_right.div_const _) hcontT hmeanT
  refine ⟨fun x ↦ A₀ x + A₁ x, hA₀m.add hA₁m,
    fun x ↦ add_nonneg (hA₀0 x) (hA₁0 x), hA₀Lp.add hA₁Lp, ?_⟩
  have hKm : Measurable K := by
    rw [funext I.K_eq]
    exact hf.stronglyMeasurable.integral_prod_left.measurable
  have hfactor : ∀ᵐ x ∂q, ∀ α, ∀ u : cube d (R.b α),
      f x (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * L.a α x u :=
    ae_all_iff.mpr L.factor
  filter_upwards [hA₀, hA₁, hfactor] with x h₀ h₁ hx
  apply R.ae_prior_of_chart_and_tail hW.measurableSet hφ
    (measurableSet_le hf.of_uncurry_left.abs (hKm.sqrt.mul measurable_const))
  · intro α u hu
    let v : cube d (R.b α) := ⟨u, hu⟩
    have hmon : 0 ≤ ∏ j, u j ^ R.k α j :=
      Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu.1 j) _
    have hsq : K (R.g α u) = (∏ j, u j ^ R.k α j) ^ 2 := by
      rw [R.monomial α u hu, Finset.prod_pow_two_mul]
    change |f x (R.g α u)| ≤ Real.sqrt (K (R.g α u)) * (A₀ x + A₁ x)
    rw [hx α v, abs_mul, abs_of_nonneg hmon, hsq, Real.sqrt_sq hmon]
    exact mul_le_mul_of_nonneg_left
      ((h₀ ⟨α, v⟩).trans (le_add_of_nonneg_right (hA₁0 x))) hmon
  · intro w hw hδ
    have hs : 0 < Real.sqrt (K w) := Real.sqrt_pos.mpr (R.δ_pos.trans_le hδ)
    have hdiv := h₁ (⟨w, hw, hδ⟩ : {w // w ∈ W ∧ R.δ ≤ K w})
    rw [abs_div, abs_of_pos hs] at hdiv
    have hfw := (div_le_iff₀ hs).mp hdiv
    calc |f x w| ≤ A₁ x * Real.sqrt (K w) := hfw
      _ ≤ Real.sqrt (K w) * (A₀ x + A₁ x) := by nlinarith [hA₀0 x]

end SingularLearningTheory.BayesGibbs
