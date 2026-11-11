/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.GlobalTransport
public import SLT.BayesGibbs.TightProducts

/-!
# Transport of random weights

Deterministic tail bounds with an explicit same-sample tail bound. They allow random marks
without diagonalizing an uncountable family of almost-everywhere statements.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {R : ResolutionAtlas K φ W}

namespace EmpiricalProcessInput

variable {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

theorem weightedTail_integrable_and_bound_of_prior_ae
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : (Fin d → ℝ) → ℝ} (ham : Measurable a)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)), |a w| ≤ M) (n : ℕ) (ω : Ω)
    (hτ : ∀ w ∈ W, R.χ w < 1 →
      n * R.δ / 2 - I.B n ω ^ 2 / 2 ≤ n * I.Kn n ω w) :
      IntegrableOn (fun w ↦ a w * Real.exp (-(n * β * I.Kn n ω w)) *
        ((1 - R.χ w) * φ w)) W ∧ |I.weightedTail a n ω| ≤ M * I.tail n ω := by
  have ha' := (ae_withDensity_iff' hφi.aemeasurable.ennreal_ofReal).mp ha
  let e : (Fin d → ℝ) → ℝ := fun w ↦
    Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)
  have hem : AEStronglyMeasurable e (volume.restrict W) :=
    ((I.Kn_measurable n).of_uncurry_left.const_mul _).neg.exp.aestronglyMeasurable.mul
      ((measurable_const.sub R.χ_measurable).aestronglyMeasurable.mul hφi.aestronglyMeasurable)
  have he0 : ∀ᵐ w ∂(volume.restrict W), 0 ≤ e w := by
    filter_upwards [ae_restrict_mem hW] with w hw
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (sub_nonneg.mpr (R.χ_le_one w)) (hφ w hw))
  have hei : Integrable e (volume.restrict W) :=
    Integrable.mono' (hφi.const_mul (Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2))) hem (by
      filter_upwards [ae_restrict_mem hW, he0] with w hw hew
      rw [Real.norm_eq_abs, abs_of_nonneg hew]
      exact I.exp_mul_tail_weight_le hτ hβ.le hw (hφ w hw))
  have hpt : ∀ᵐ w ∂(volume.restrict W), ‖a w * e w‖ ≤ M * e w := by
    filter_upwards [ae_restrict_mem hW, he0, ha'] with w hw hew haw
    by_cases hφw : φ w = 0
    · simp [e, hφw]
    · have hφpos : 0 < φ w := lt_of_le_of_ne (hφ w hw) (Ne.symm hφw)
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hew]
      exact mul_le_mul_of_nonneg_right (haw (ENNReal.ofReal_pos.mpr hφpos).ne') hew
  have hai : Integrable (fun w ↦ a w * e w) (volume.restrict W) :=
    (hei.const_mul M).mono' (ham.aestronglyMeasurable.mul hem) hpt
  refine ⟨hai.congr (Eventually.of_forall fun w ↦ by dsimp [e]; ring), ?_⟩
  have hb := norm_integral_le_of_norm_le (hei.const_mul M) hpt
  rw [integral_const_mul, Real.norm_eq_abs] at hb
  simpa only [weightedTail, tail, e, mul_assoc] using hb

/-- A tight prior-a.e. bound on a random mark preserves exponential tail
negligibility under every polynomial normalization. -/
theorem random_mark_tail_tendsto
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : ℕ → Ω → (Fin d → ℝ) → ℝ}
    (ham : ∀ n ω, Measurable (a n ω)) {M : ℕ → Ω → ℝ}
    (hM : ∀ n ω, 0 ≤ M n ω)
    (ha : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ w ∂(volume.restrict W).withDensity
      (fun w ↦ ENNReal.ofReal (φ w)), |a n ω w| ≤ M n ω)
    (hMtight : ∀ η > 0, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | C < |M n ω|} ≤ ENNReal.ofReal η) (lam : ℝ) (m : ℕ) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (n : ℝ) ^ lam / Real.log n ^ (m - 1) *
      I.weightedTail (a n ω) n ω) atTop 0 := by
  have hsmall := tendstoInMeasure_mul_zero_of_tight hMtight
    (I.tail_tendsto hW hφ hφi hβ lam m)
  apply tendstoInMeasure_zero_of_abs_le (Z := fun n ω ↦ M n ω *
    ((n : ℝ) ^ lam / Real.log n ^ (m - 1) * I.tail n ω)) (fun n ↦ ?_) hsmall
  filter_upwards [I.tail_bound n, ha n] with ω hτω haω
  have hb := (I.weightedTail_integrable_and_bound_of_prior_ae hW hφ hφi hβ
    (ham n ω) (hM n ω) haω n ω hτω).2
  have hs : 0 ≤ (n : ℝ) ^ lam / Real.log n ^ (m - 1) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (Real.log_natCast_nonneg n) _)
  rw [abs_mul, abs_of_nonneg hs]
  calc _ ≤ (n : ℝ) ^ lam / Real.log n ^ (m - 1) * (M n ω * I.tail n ω) :=
      mul_le_mul_of_nonneg_left hb hs
    _ = _ := by ring

end EmpiricalProcessInput
end SingularLearningTheory.ResolutionAtlas
