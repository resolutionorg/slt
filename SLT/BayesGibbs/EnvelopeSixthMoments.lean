/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FeatureEnvelopeSix
public import SLT.BayesGibbs.FiniteSampleMoments
public import SLT.FreeEnergy.FundamentalConditions
import Mathlib.Topology.Metrizable.ContinuousMap

/-!
# Sixth moments of the envelopes

The bounds on the posterior observables are polynomial in an envelope of the empirical processes
and in a data envelope $A$, and their expectations are controlled through sixth moments. This
module turns the moment bound `SingularLearningTheory.EmpiricalProcessLimit.MomentBound` with $s = 6$
into a uniform bound on $E\|\Psi_n\|^6$, bounds the sixth moment of the maximum of two
envelopes, and bounds the expectation of the dominator $1 + L_n^6 + \frac1n\sum_{i<n} A(X_i)^6$
of the cubic residuals.

## Main results

* `SingularLearningTheory.EmpiricalProcessLimit.empirical_norm_sixth_moment`: under the moment bound
with
  $s = 6$, the sixth power of the sup norm $\|\Psi_n\|$ is integrable, with expectation bounded
  uniformly in $n$.
* `SingularLearningTheory.BayesGibbs.max_envelope_sixth_moment`: the sixth moment of
  $\max(F_n, G_n)$ is at most the sum of the bounds for $F_n$ and $G_n$, with no joint
  assumption on the two.
* `SingularLearningTheory.BayesGibbs.sixth_dominator_moment`: the expectation of
  $1 + L_n^6 + \frac1n\sum_{i<n} A(X_i)^6$ is at most $1 + C_L + E_q[A^6]$.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

variable {X Ω Ω' U : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [MeasurableSpace Ω'] [MetricSpace U] [CompactSpace U]
  {q : Measure X} {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {f : X → U → ℝ} {Xs : ℕ → Ω → X}

/-- Convert the ENNReal supremum moment certificate into the uniform
Bochner moments consumed by the posterior AUI and cubic L1 estimates. -/
theorem _root_.SingularLearningTheory.EmpiricalProcessLimit.empirical_norm_sixth_moment
    (E : EmpiricalProcessLimit q f Xs P P') (hE : E.MomentBound 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
      Integrable (fun ω ↦ ‖E.Ψ n ω‖ ^ 6) P ∧ ∫ ω, ‖E.Ψ n ω‖ ^ 6 ∂P ≤ C := by
  obtain ⟨C, hC, hCn⟩ := hE
  refine ⟨C.toReal, ENNReal.toReal_nonneg, fun n ↦ ?_⟩
  have hlin : ∫⁻ ω, ‖E.Ψ n ω‖ₑ ^ 6 ∂P ≤ C :=
    (lintegral_mono fun ω ↦ pow_le_pow_left' (ContinuousMap.enorm_le_iSup_enorm _) 6).trans (hCn n)
  have hLp : MemLp (E.Ψ n) 6 P := by
    change eLpNorm (E.Ψ n) 6 P < ⊤
    have heq : eLpNorm (E.Ψ n) 6 P =
        (∫⁻ ω, ‖E.Ψ n ω‖ₑ ^ 6 ∂P) ^ (1 / 6 : ℝ) := by
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
        (E.Ψ_measurable n).aestronglyMeasurable]
      norm_num
    rw [heq]
    exact ENNReal.rpow_lt_top_of_nonneg (by positivity) (ne_top_of_le_ne_top hC hlin)
  have hi : Integrable (fun ω ↦ ‖E.Ψ n ω‖ ^ 6) P := hLp.integrable_norm_pow'
  refine ⟨hi, ?_⟩
  have heq : ENNReal.ofReal (∫ ω, ‖E.Ψ n ω‖ ^ 6 ∂P) = ∫⁻ ω, ‖E.Ψ n ω‖ₑ ^ 6 ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (.of_forall fun ω ↦ by positivity)]
    apply lintegral_congr
    intro ω
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  have h := ENNReal.toReal_mono hC hlin
  rw [← heq, ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ by positivity)] at h
  exact h

/-- The max of the chart and tail envelopes has a uniform sixth moment.
This uses only their individual certificates, not joint convergence or
independence of the two empirical processes. -/
theorem max_envelope_sixth_moment {F G : ℕ → Ω → ℝ}
    (hFm : ∀ n, Measurable (F n)) (hGm : ∀ n, Measurable (G n))
    {CF CG : ℝ} (hFi : ∀ n, Integrable (fun ω ↦ F n ω ^ 6) P)
    (hGi : ∀ n, Integrable (fun ω ↦ G n ω ^ 6) P)
    (hFC : ∀ n, ∫ ω, F n ω ^ 6 ∂P ≤ CF)
    (hGC : ∀ n, ∫ ω, G n ω ^ 6 ∂P ≤ CG) :
    ∀ n, Integrable (fun ω ↦ (max (F n ω) (G n ω)) ^ 6) P ∧
      ∫ ω, (max (F n ω) (G n ω)) ^ 6 ∂P ≤ CF + CG := by
  intro n
  have hpt : ∀ ω, (max (F n ω) (G n ω)) ^ 6 ≤ F n ω ^ 6 + G n ω ^ 6 := by
    intro ω
    rcases le_total (F n ω) (G n ω) with h | h
    · rw [max_eq_right h]
      have hp : 0 ≤ F n ω ^ 6 := by positivity
      linarith
    · rw [max_eq_left h]
      have hp : 0 ≤ G n ω ^ 6 := by positivity
      linarith
  have hi : Integrable (fun ω ↦ (max (F n ω) (G n ω)) ^ 6) P :=
    ((hFi n).add (hGi n)).mono' (((hFm n).max (hGm n)).pow_const 6).aestronglyMeasurable
      (.of_forall fun ω ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (show 0 ≤ (max (F n ω) (G n ω)) ^ 6 by positivity)]
        exact hpt ω)
  refine ⟨hi, ?_⟩
  calc _ ≤ ∫ ω, (F n ω ^ 6 + G n ω ^ 6) ∂P := integral_mono hi ((hFi n).add (hGi n)) hpt
    _ = (∫ ω, F n ω ^ 6 ∂P) + ∫ ω, G n ω ^ 6 ∂P := integral_add (hFi n) (hGi n)
    _ ≤ _ := add_le_add (hFC n) (hGC n)

/-- The smaller sixth-moment dominator needed by cubic residuals. The sixth
sample average has its exact population expectation; no independence between
it and the process envelope is used. -/
theorem sixth_dominator_moment {L : ℕ → Ω → ℝ} {CL : ℝ}
    (hL6 : ∀ n, Integrable (fun ω ↦ L n ω ^ 6) P)
    (hL6C : ∀ n, ∫ ω, L n ω ^ 6 ∂P ≤ CL)
    {A : X → ℝ} (hAm : Measurable A) (hA6 : Integrable (fun x ↦ A x ^ 6) q)
    (hXm : ∀ j, Measurable (Xs j)) (hmap : ∀ j, P.map (Xs j) = q)
    {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ 1 + L n ω ^ 6 +
      (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 6) P ∧
    ∫ ω, (1 + L n ω ^ 6 + (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 6) ∂P ≤
      1 + CL + ∫ x, A x ^ 6 ∂q := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hi : ∀ i, Integrable (fun ω ↦ A (Xs i ω) ^ 6) P := fun i ↦
    (integrable_map_measure (hAm.pow_const 6).aestronglyMeasurable (hXm i).aemeasurable).mp
      (by rw [hmap i]; exact hA6)
  have hm : ∀ i, (∫ ω, A (Xs i ω) ^ 6 ∂P) = ∫ x, A x ^ 6 ∂q := fun i ↦ by
    rw [← hmap i, integral_map (hXm i).aemeasurable (hAm.pow_const 6).aestronglyMeasurable]
  have ha : Integrable (fun ω ↦ (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 6) P :=
    (integrable_finsetSum _ fun i _ ↦ hi i).const_mul _
  have hai : (∫ ω, (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, A (Xs i ω) ^ 6 ∂P) =
      ∫ x, A x ^ 6 ∂q := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hi i,
      Finset.sum_congr rfl fun i _ ↦ hm i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hbase : Integrable (fun ω ↦ 1 + L n ω ^ 6) P :=
    (integrable_const (1 : ℝ)).add (hL6 n)
  refine ⟨hbase.add ha, ?_⟩
  rw [integral_add hbase ha, integral_add (integrable_const _) (hL6 n), hai]
  simp only [integral_const, smul_eq_mul]
  simpa using add_le_add_right (add_le_add_left (hL6C n) 1) (∫ x, A x ^ 6 ∂q)

end SingularLearningTheory.BayesGibbs
