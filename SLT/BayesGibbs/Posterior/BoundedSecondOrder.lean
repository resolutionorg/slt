/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Posterior.BoundedTaylor
public import SLT.Probability.Moments.TiltedSecondOrder
public import SLT.Probability.Moments.TiltedCumulant
public import SLT.BayesGibbs.LaplaceDoubling.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

/-!
# The predictive value from tilted second moments

For a probability measure $Q$ and a measurable $f$ bounded almost everywhere,
`SingularLearningTheory.BayesGibbs.abs_predictive_sub_mean_le_of_second_moment` bounds
$|-\log E_Q[e^{-f}] - E_Q[f]|$ by $C/2$ when $f^2$ has mean at most $C$ under every tilted
measure $e^{-tf}Q / E_Q[e^{-tf}]$ with $t \in [0, 1]$. The proof is a second-order Taylor bound
for $t \mapsto \log E_Q[e^{-tf}]$, applied to a clipped representative of $f$, so the bound on
$f$ is needed only almost everywhere. With $Q$ the tempered posterior, this bounds the gap
between the Bayes and the Gibbs loss at a datum.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.BayesGibbs

variable {W : Type*} [MeasurableSpace W] {Q : Measure W} [IsProbabilityMeasure Q]

/-- The second-order estimate under an a.e. bounded loss. The local calculus
uses a clipped representative, so no pointwise parameter coverage is required.
The exponential local dominator is not integrated over the data law. -/
theorem abs_predictive_sub_mean_le_of_second_moment {f : W → ℝ} (hf : Measurable f)
    {B C : ℝ} (hB : 0 ≤ B) (hb : ∀ᵐ w ∂Q, |f w| ≤ B)
    (hC : ∀ t ∈ Icc (0 : ℝ) 1,
      (∫ w, f w ^ 2 ∂Measure.expMeasure Q (fun w ↦ t * f w)) ≤ C) :
    |-(Real.log (∫ w, Real.exp (-f w) ∂Q)) - (∫ w, f w ∂Q)| ≤ C / 2 := by
  let f' : W → ℝ := fun w ↦ max (-B) (min B (f w))
  have hf' : Measurable f' := measurable_const.max (measurable_const.min hf)
  have hf'eq : f' =ᵐ[Q] f := hb.mono fun w hw ↦ by
    simp only [f', min_eq_right (abs_le.mp hw).2, max_eq_right (abs_le.mp hw).1]
  have hf'b : ∀ w, |f' w| ≤ B := fun w ↦ abs_le.mpr ⟨le_max_left _ _,
    max_le (by linarith) (min_le_left _ _)⟩
  have hbound : ∀ t ∈ Ioo (-1 : ℝ) 2, ∀ w,
      (1 + f' w ^ 2) * Real.exp (-(t * f' w)) ≤
        (1 + B ^ 2) * Real.exp (2 * B) := by
    intro t ht w
    have ht2 : |t| ≤ 2 := abs_le.mpr ⟨by linarith [ht.1], ht.2.le⟩
    have he : Real.exp (-(t * f' w)) ≤ Real.exp (2 * B) := by
      apply Real.exp_le_exp.mpr
      calc -(t * f' w) ≤ |t * f' w| := neg_le_abs _
        _ = |t| * |f' w| := abs_mul _ _
        _ ≤ 2 * B := mul_le_mul ht2 (hf'b w) (abs_nonneg _) (by norm_num)
    have hsq : f' w ^ 2 ≤ B ^ 2 := by
      nlinarith [(abs_le.mp (hf'b w)).1, (abs_le.mp (hf'b w)).2,
        sq_abs (f' w)]
    exact mul_le_mul (by linarith) he (Real.exp_pos _).le (by positivity)
  have hZ : ∀ t : ℝ, 0 < ∫ w, Real.exp (-(t * f w)) ∂Q := fun t ↦ by
    simpa only [ProbabilityTheory.mgfMoment, pow_zero, one_mul, Pi.neg_apply, mul_neg] using
      ProbabilityTheory.mgfMoment_zero_pos (Q := Q) hf.neg hB
          (by simpa only [Pi.neg_apply, abs_neg] using hb) t
  have hnum : ∀ t, ProbabilityTheory.tiltNum2 Q f' t = ∫ w, f w ^ 2 * Real.exp (-(t * f w)) ∂Q := by
    intro t
    apply integral_congr_ae
    filter_upwards [hf'eq] with w hw
    simp only [hw]
  have hden : ∀ t, ProbabilityTheory.tiltPartition Q f' t = ∫ w, Real.exp (-(t * f w)) ∂Q := by
    intro t
    apply integral_congr_ae
    filter_upwards [hf'eq] with w hw
    simp only [hw]
  have hvar : ∀ t ∈ Icc (0 : ℝ) 1, ProbabilityTheory.tiltVar Q f' t ≤ C := by
    intro t ht
    refine (ProbabilityTheory.tiltVar_le_second_moment (ρ := Q) (f := f') t).trans ?_
    rw [hnum t, hden t, ← integral_expMeasure Q (hf.const_mul t) _ (hZ t)]
    exact hC t ht
  have htaylor := ProbabilityTheory.abs_neg_tiltLogPartition_one_sub_tiltMean_zero_le hf'
    isOpen_Ioo (convex_Ioo (-1 : ℝ) 2)
    (integrable_const ((1 + B ^ 2) * Real.exp (2 * B))) hbound
    (by norm_num : (0 : ℝ) ∈ Ioo (-1 : ℝ) 2)
    (by norm_num : (1 : ℝ) ∈ Ioo (-1 : ℝ) 2) hvar
  have hmean : ProbabilityTheory.tiltMean Q f' 0 = ∫ w, f w ∂Q := by
    have he : (∫ w, f' w ∂Q) = ∫ w, f w ∂Q := integral_congr_ae hf'eq
    simpa [ProbabilityTheory.tiltMean, ProbabilityTheory.tiltNum, ProbabilityTheory.tiltPartition]
        using he
  rw [hmean, ProbabilityTheory.tiltLogPartition, hden 1] at htaylor
  simpa only [one_mul] using htaylor

end SingularLearningTheory.BayesGibbs
