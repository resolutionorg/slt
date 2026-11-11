/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.SixthMoments
public import SLT.EmpiricalProcess.Modification
public import SLT.FreeEnergy.FundamentalConditions
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# A sixth-moment envelope for a continuous feature

Let $f(x, u)$ be a feature on a compact metric space $U$, continuous in $u$ for $q$-almost every
$x$, whose empirical process has the moment bound
`SingularLearningTheory.EmpiricalProcessLimit.MomentBound` with $s = 6$. At $n = 1$ the empirical
process is the feature of one datum minus its mean, so the bound puts the feature itself, as a
random continuous function, in $L^6(q)$. Its sup norm is then a measurable envelope
$A \in L^6(q)$ with $|f(x, u)| \le A(x)$ for every $u$, for $q$-almost every $x$. Applied to the
features on the charts and on the tail, this gives the data envelope of the posterior bounds.

## Main results

* `SingularLearningTheory.BayesGibbs.continuous_rep_memLp_six`: a measurable representative of $f$ as
  a continuous function of $u$ lies in $L^6(q)$.
* `SingularLearningTheory.EmpiricalProcessLimit.exists_continuous_feature_rep_six`: such a
representative exists
  when $f$ is measurable in $x$ and its mean is continuous in $u$.
* `SingularLearningTheory.EmpiricalProcessLimit.exists_feature_envelope_six`: the envelope $A$.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.EmpiricalProcessLimit

variable {X Ω Ω' U : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [MeasurableSpace Ω'] [MetricSpace U] [CompactSpace U]
  {q : Measure X} {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {f : X → U → ℝ} {Xs : ℕ → Ω → X}

/-- The n=1 member of the sixth empirical-process moment bound controls the
sixth moment of the raw continuous feature itself. This avoids another
majorant/chaining proof for the data envelope. -/
private theorem continuous_rep_memLp_six
    (E : EmpiricalProcessLimit q f Xs P P') (hE : E.MomentBound 6)
    (hX : Measurable (Xs 0)) (hlaw : P.map (Xs 0) = q)
    (m : C(U, ℝ)) (hm : ∀ u, m u = ∫ x, f x u ∂q)
    (F : X → C(U, ℝ)) (hFm : Measurable F)
    (hF : ∀ᵐ x ∂q, ∀ u, F x u = f x u) : MemLp F 6 q := by
  obtain ⟨C, hC, hCn⟩ := hE
  have hΨint : ∫⁻ ω, ‖E.Ψ 1 ω‖ₑ ^ 6 ∂P ≤ C :=
    (lintegral_mono fun ω ↦ pow_le_pow_left' (ContinuousMap.enorm_le_iSup_enorm _) 6).trans (hCn 1)
  have hΨ : MemLp (E.Ψ 1) 6 P := by
    change eLpNorm (E.Ψ 1) 6 P < ⊤
    have heq : eLpNorm (E.Ψ 1) 6 P =
        (∫⁻ ω, ‖E.Ψ 1 ω‖ₑ ^ 6 ∂P) ^ (1 / 6 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (E.Ψ_measurable 1).aestronglyMeasurable]
      norm_num
    rw [heq]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_top_of_le_ne_top hC hΨint)
  have hFs : ∀ᵐ ω ∂P, ∀ u, F (Xs 0 ω) u = f (Xs 0 ω) u := by
    rw [← hlaw] at hF
    exact ae_of_ae_map hX.aemeasurable hF
  have heq : (fun ω ↦ E.Ψ 1 ω + m) =ᵐ[P] F ∘ Xs 0 := by
    filter_upwards [E.Ψ_ae_eq 1, hFs] with ω hψ hFω
    ext u
    dsimp only [Function.comp_def]
    rw [ContinuousMap.add_apply, hψ u, hFω u, hm u]
    simp [empiricalProcess]
  have hcomp : MemLp (F ∘ Xs 0) 6 P := (hΨ.add (memLp_const m)).ae_eq heq
  have hmap : MemLp F 6 (P.map (Xs 0)) :=
    (memLp_map_measure_iff hFm.aestronglyMeasurable hX.aemeasurable).mpr hcomp
  rwa [hlaw] at hmap

/-- A compact continuous feature family admits a measurable continuous-map
representative in L6, using the sixth empirical-process moment bound.
The representative agrees at all parameter points on one common q-a.e. event. -/
theorem exists_continuous_feature_rep_six
    (E : EmpiricalProcessLimit q f Xs P P') (hE : E.MomentBound 6)
    (hX : Measurable (Xs 0)) (hlaw : P.map (Xs 0) = q)
    (hf_meas : ∀ u, Measurable fun x ↦ f x u)
    (hf_cont : ∀ᵐ x ∂q, Continuous (f x))
    (hmean : Continuous fun u ↦ ∫ x, f x u ∂q) :
    ∃ F : X → C(U, ℝ), Measurable F ∧ MemLp F 6 q ∧
      ∀ᵐ x ∂q, ∀ u, F x u = f x u := by
  obtain ⟨G, hGm, hGq, hG⟩ := exists_measurable_continuity_set q f hf_cont
  let m : C(U, ℝ) := ⟨fun u ↦ ∫ x, f x u ∂q, hmean⟩
  let F : X → C(U, ℝ) := fun x ↦
    EmpiricalProcess.continuousModification q f (fun _ ↦ id) hG hmean 1 x + m
  have hFm : Measurable F :=
    (EmpiricalProcess.measurable_continuousModification hGm hG hmean hf_meas (fun _ ↦ measurable_id)
        1).add
      measurable_const
  have hF : ∀ᵐ x ∂q, ∀ u, F x u = f x u := by
    have hmod := EmpiricalProcess.ae_continuousModification_apply (q := q) (P := q)
        (Xs := fun _ ↦ id)
      (fun _ ↦ measurable_id) (fun _ ↦ Measure.map_id) hGq hG hmean 1
    filter_upwards [hmod] with x hx u
    change EmpiricalProcess.continuousModification q f (fun _ ↦ id) hG hmean 1 x u + m u = _
    rw [hx u]
    simp [empiricalProcess, m]
  have hFLp := continuous_rep_memLp_six E hE hX hlaw m (fun _ ↦ rfl) F hFm hF
  exact ⟨F, hFm, hFLp, hF⟩

/-- A compact continuous feature family has a measurable L6 sup envelope
once its centered empirical process has the sixth moment bound. The
common q-a.e. event contains all parameter points simultaneously. -/
theorem exists_feature_envelope_six
    (E : EmpiricalProcessLimit q f Xs P P') (hE : E.MomentBound 6)
    (hX : Measurable (Xs 0)) (hlaw : P.map (Xs 0) = q)
    (hf_meas : ∀ u, Measurable fun x ↦ f x u)
    (hf_cont : ∀ᵐ x ∂q, Continuous (f x))
    (hmean : Continuous fun u ↦ ∫ x, f x u ∂q) :
    ∃ A : X → ℝ, Measurable A ∧ (∀ x, 0 ≤ A x) ∧ MemLp A 6 q ∧
      ∀ᵐ x ∂q, ∀ u, |f x u| ≤ A x := by
  obtain ⟨F, hFm, hFLp, hF⟩ := exists_continuous_feature_rep_six E hE hX hlaw
    hf_meas hf_cont hmean
  refine ⟨fun x ↦ ‖F x‖, hFm.norm, fun x ↦ norm_nonneg _, hFLp.norm, ?_⟩
  filter_upwards [hF] with x hx u
  rw [← hx u, ← Real.norm_eq_abs]
  exact (F x).norm_coe_le_norm u

end SingularLearningTheory.EmpiricalProcessLimit
