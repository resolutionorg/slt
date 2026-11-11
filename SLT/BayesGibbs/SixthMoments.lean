/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.Discharge
import SLT.EmpiricalProcess.FourthMoment
public import SLT.EmpiricalProcess.Transport
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.FreeEnergy.FundamentalConditions

/-!
# Sixth moments of the chart processes

The sixth-moment bound of the empirical process of each chart of an analytic resolved
likelihood, and of the tail quotient, from the even-moment theorem at `m = 3`.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory

variable {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {Xs : ℕ → Ω → X} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {f : X → (Fin d → ℝ) → ℝ}

namespace ResolutionAtlas

variable {R : ResolutionAtlas K φ W}

/-- The existing even-moment theorem at m=3, transported to the
sigma of chart cubes exactly as in `AnalyticResolvedLikelihood.momentBound_chart`. -/
theorem AnalyticResolvedLikelihood.momentBound_chart_six (L : R.AnalyticResolvedLikelihood 6 q f)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hind : iIndepFun Xs P) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (E : EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs P P') :
    E.MomentBound 6 := by
  letI : MetricSpace ((α : R.ι) × cube d (R.b α)) := Metric.Sigma.metricSpace
  refine E.momentBound_even hX hlaw hind (m := 3) (by norm_num)
    (Eventually.of_forall fun x ↦ continuous_sigma fun α ↦ (L.a α x).continuous) ?_
  rintro ⟨α, u⟩
  obtain ⟨B, hBo, huB, E', hE'⟩ := L.loc α u
  have hι : ∀ u ∈ B, ∀ v ∈ B,
      dist (⟨α, u⟩ : (α : R.ι) × cube d (R.b α)) ⟨α, v⟩ = dist u v :=
    fun u _ v _ ↦ R.sigma_dist_same α u v
  have hg : ∀ x, ∀ u ∈ B,
      (fun x (p : (α : R.ι) × cube d (R.b α)) ↦ L.a p.1 x p.2) x
        (⟨α, u⟩ : (α : R.ι) × cube d (R.b α)) = L.a α x u := fun _ _ _ ↦ rfl
  refine ⟨Sigma.mk α '' B, isOpenMap_sigmaMk _ hBo, ⟨u, huB, rfl⟩,
    E'.image (fun v : cube d (R.b α) ↦ (⟨α, v⟩ : (α : R.ι) × cube d (R.b α))) hι _ hg, ?_⟩
  simpa only [Nat.cast_ofNat, show (2 * (3 : ℝ≥0∞)) = 6 by norm_num] using hE'.image _ hι (fun x (p : (α : R.ι) × cube d (R.b α)) ↦ L.a p.1 x p.2) hg

end ResolutionAtlas

namespace FundamentalConditionI

/-- The tail quotient is L6-analytic, so the even-moment theorem
directly supplies the sixth moment. -/
theorem momentBound_tail_six (I : FundamentalConditionI 6 q f K W) (hW : IsCompact W)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W) {δ : ℝ} (hδ : 0 < δ)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hind : iIndepFun Xs P) {Ω' : Type*} [MeasurableSpace Ω']
    {P' : Measure Ω'} [IsProbabilityMeasure P']
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P P') :
    T.MomentBound 6 :=
  EmpiricalProcessLimit.momentBound_of_lsValuedAnalytic_even (W := {w | w ∈ W ∧ δ ≤ K w})
    (f := fun x w ↦ f x w / Real.sqrt (K w)) (I.isCompact_tail hW δ) T hX hlaw hind
    (I.ae_continuousOn_tail hcont hδ) (m := 3) (by norm_num) (by norm_num)
    (I.lsValuedAnalytic_tail hδ)

end FundamentalConditionI

end SingularLearningTheory
