/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.GibbsWeightedNumerators
public import SLT.BayesGibbs.Weighted.GlobalTransport

/-!
# Limits of the numerators of the Gibbs errors

The posterior expectation of a function $a$ is the weighted partition function
$\int_W a(w)e^{-n\beta K_n(w)}\varphi(w)\,dw$ divided by the evidence. This module proves the
limits of the numerators for $a = K$, which gives the Gibbs generalization error, and for the
centered loss $a = \sqrt n(K - K_n)$, which gives the difference of the Gibbs generalization and
training errors. Scaled by $n^{\lambda + 1}/(\log n)^{m-1}$ and $n^{\lambda + 1/2}/(\log n)^{m-1}$,
the numerators approach, in probability, sums over the essential charts of marked radial limits
with radial degrees $1$ and $1/2$. On a chart the centered loss is $u^k\xi_n(u)$, so its mark is
the chart process $\xi_n$ itself.

## Main results

* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.population_loss_numerator_sub_limit_tendstoInMeasure`:
  the limit of the numerator for $K$.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.centered_loss_numerator_sub_limit_tendstoInMeasure`:
  the limit of the numerator for $\sqrt n(K - K_n)$, given $\sqrt n|K_n - K| \le L_n\sqrt K$
  almost everywhere for the prior, with $L_n$ bounded in probability.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {R : ResolutionAtlas K φ W} {β : ℝ} {Ω Ω' : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'}
  [IsProbabilityMeasure P] [IsProbabilityMeasure P'] (I : R.EmpiricalProcessInput β P P')

/-- The actual population-loss numerator, normalized at radial degree one. -/
theorem population_loss_numerator_sub_limit_tendstoInMeasure
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) (hKm : Measurable K) (hK0 : ∀ w ∈ W, 0 ≤ K w)
    {B : ℝ} (hB : 0 ≤ B) (hKB : ∀ w ∈ W, K w ≤ B) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) * I.weightedPartition K n ω -
        ∑ α, if R.IsEssential α then
          R.chartRadialLimit β 1 α (I.Ξ n ω α) (R.chartWeightCM α) else 0) atTop 0 := by
  have ha : ∀ w ∈ W, |K w| ≤ B := fun w hw ↦ by
    rw [abs_of_nonneg (hK0 w hw)]
    exact hKB w hw
  have hf : ∀ α (u : cube d (R.b α)), K (R.g α u) =
      (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ (1 : ℝ) * (1 : R.ChartFunctions) α u := by
    intro α u
    simpa using R.monomial α u u.2
  simpa using I.weightedPartition_sub_limit_tendstoInMeasure hW hφ hφi hβ hKm hB ha
    (by norm_num : (0 : ℝ) ≤ 1) (1 : R.ChartFunctions) hf

/-- The centered empirical-loss numerator. Prior-a.e. relative envelopes and their tightness give
the tail premises. On a chart
this is the self mark Ξ at radial degree one-half. -/
theorem centered_loss_numerator_sub_limit_tendstoInMeasure
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) (hKm : Measurable K) {B : ℝ}
    (hKB : ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)), K w ≤ B)
    {L : ℕ → Ω → ℝ} (hL0 : ∀ n ω, 0 ≤ L n ω)
    (hLtight : ∀ η > 0, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | C < |L n ω|} ≤ ENNReal.ofReal η)
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P,
      ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
        Real.sqrt n * |I.Kn n ω w - K w| ≤ L n ω * Real.sqrt (K w)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ (R.rlct + (1 / 2 : ℝ)) / Real.log n ^ (R.mult - 1) *
        I.weightedPartition (fun w ↦ Real.sqrt n * (K w - I.Kn n ω w)) n ω -
        ∑ α, if R.IsEssential α then R.chartRadialLimit β (1 / 2) α
          (I.Ξ n ω α) (R.chartWeightCM α * I.Ξ n ω α) else 0) atTop 0 := by
  let M := fun n ω ↦ L n ω * Real.sqrt (max 0 B)
  have hM : ∀ n ω, 0 ≤ M n ω := fun n ω ↦
    mul_nonneg (hL0 n ω) (Real.sqrt_nonneg _)
  have ha : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ᵐ w ∂(volume.restrict W).withDensity
      (fun w ↦ ENNReal.ofReal (φ w)),
      |Real.sqrt n * (K w - I.Kn n ω w)| ≤ M n ω := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact .of_forall fun ω ↦ .of_forall fun w ↦ by
        simpa only [Nat.cast_zero, Real.sqrt_zero, zero_mul, abs_zero] using hM 0 ω
    filter_upwards [he n hn] with ω hω
    filter_upwards [hω, hKB] with w hw hwB
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), abs_sub_comm]
    exact hw.trans (mul_le_mul_of_nonneg_left
      (Real.sqrt_le_sqrt (hwB.trans (le_max_right _ _))) (hL0 n ω))
  have hMtight : ∀ η > 0, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | C < |M n ω|} ≤ ENNReal.ofReal η := by
    intro η hη
    obtain ⟨C, N, hN⟩ := hLtight η hη
    refine ⟨(|C| + 1) * Real.sqrt (max 0 B), N, fun n hn ↦
      (measure_mono ?_).trans (hN n hn)⟩
    intro ω hω
    simp only [mem_setOf_eq, M, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] at hω ⊢
    by_contra h
    have hL : |L n ω| ≤ |C| + 1 := (le_of_not_gt h).trans (by linarith [le_abs_self C])
    exact hω.not_ge (mul_le_mul_of_nonneg_right hL (Real.sqrt_nonneg _))
  exact I.random_weightedPartition_sub_limit_tendstoInMeasure hW hφ hφi hβ
    (fun n ω ↦ (hKm.sub (I.Kn_measurable n).of_uncurry_left).const_mul _)
    hM ha hMtight (by norm_num : (0 : ℝ) ≤ 1 / 2) I.Ξ
    (fun n hn ↦ I.ae_centered_loss_chart_factor hn)
    (I.self_mark_radial_sum_sub_limit_tendstoInMeasure hβ)

end SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput
