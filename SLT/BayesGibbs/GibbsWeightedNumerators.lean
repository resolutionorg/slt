/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.RandomWeightedTransport
public import SLT.BayesGibbs.Weighted.ChartProbability
public import SLT.BayesGibbs.Weighted.GlobalTransport
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# Gibbs-weighted numerators

Same-sample transport of the Gibbs-weighted numerators for random marks.
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

theorem weightedPartition_eq_radial_of_identity
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : (Fin d → ℝ) → ℝ} (ham : Measurable a)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)), |a w| ≤ M)
    {p : ℝ} (hp : 0 ≤ p) (A : R.ChartFunctions)
    (hfactor : ∀ α (u : cube d (R.b α)), a (R.g α u) =
      (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ p * A α u)
    {n : ℕ} (hn : 1 ≤ n) (ω : Ω)
    (hω : ∀ α, ∀ u : cube d (R.b α),
      I.Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * I.Ξ n ω α u)
    (hτ : ∀ w ∈ W, R.χ w < 1 →
      n * R.δ / 2 - I.B n ω ^ 2 / 2 ≤ n * I.Kn n ω w) :
    I.weightedPartition a n ω =
      (∑ α, R.chartRadialInsertion α β p n (I.Ξ n ω α) (R.chartWeightCM α * A α)) +
        I.weightedTail a n ω := by
  have htail := I.weightedTail_integrable_and_bound_of_prior_ae hW hφ hφi hβ ham hM ha n ω hτ
  have hFm : Measurable fun w ↦ a w * Real.exp (-(n * β * I.Kn n ω w)) :=
    ham.mul (((I.Kn_measurable n).of_uncurry_left.const_mul _).neg.exp)
  have hFb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α),
      |a (R.g α u) * Real.exp (-(n * β * I.Kn n ω (R.g α u)))| ≤ C := by
    intro α
    let F : C(cube d (R.b α), ℝ) := ⟨fun u ↦
      (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ p * A α u,
      ((Real.continuous_rpow_const hp).comp
        (continuous_finsetProd _ fun j _ ↦
          ((continuous_apply j).comp continuous_subtype_val).pow _)).mul (A α).continuous⟩
    refine ⟨‖F‖ * Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2), fun u hu ↦ ?_⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _), I.exp_Kn_comp_g n ω α (hω α) hu]
    have hFa : |a (R.g α u)| ≤ ‖F‖ := by
      rw [hfactor α ⟨u, hu⟩]
      exact (show ‖F ⟨u, hu⟩‖ ≤ ‖F‖ from F.norm_coe_le_norm _)
    exact mul_le_mul hFa (I.exp_chart_le n ω α hβ.le u)
      (Real.exp_pos _).le (norm_nonneg _)
  obtain ⟨hint, heq⟩ := R.integral_localized_eq_sum_of_bounded hW hφ hφi hFm hFb
  have hsplit : ∀ w, a w * Real.exp (-(n * β * I.Kn n ω w)) * φ w =
      (a w * Real.exp (-(n * β * I.Kn n ω w))) * (R.χ w * φ w) +
      a w * Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w) := fun w ↦ by ring
  simp only [weightedPartition, weightedTail]
  simp_rw [hsplit]
  rw [integral_add hint htail.1, heq]
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [chartRadialInsertion]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu ↦ ?_
  rw [hfactor α ⟨u, hu⟩, I.exp_Kn_comp_g n ω α (hω α) hu, R.clamp_of_mem hu]
  simp only [ContinuousMap.mul_apply, chartWeightCM_apply]
  ring

/-- Global transport of a random mark with a tight prior bound. Every chart
factorization and tail certificate is kept on the same sample event. -/
theorem random_weightedPartition_sub_limit_tendstoInMeasure
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : ℕ → Ω → (Fin d → ℝ) → ℝ}
    (ham : ∀ n ω, Measurable (a n ω)) {M : ℕ → Ω → ℝ}
    (hM : ∀ n ω, 0 ≤ M n ω)
    (ha : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ w ∂(volume.restrict W).withDensity
      (fun w ↦ ENNReal.ofReal (φ w)), |a n ω w| ≤ M n ω)
    (hMtight : ∀ η > 0, ∃ C : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | C < |M n ω|} ≤ ENNReal.ofReal η)
    {p : ℝ} (hp : 0 ≤ p) (A : ℕ → Ω → R.ChartFunctions)
    (hfactor : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, ∀ α (u : cube d (R.b α)),
      a n ω (R.g α u) =
        (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ p * A n ω α u)
    (hlocal : TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        (∑ α, R.chartRadialInsertion α β p n (I.Ξ n ω α) (R.chartWeightCM α * A n ω α)) -
        ∑ α, if R.IsEssential α then
          R.chartRadialLimit β p α (I.Ξ n ω α) (R.chartWeightCM α * A n ω α) else 0)
        atTop 0) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) * I.weightedPartition (a n ω) n ω -
        ∑ α, if R.IsEssential α then
          R.chartRadialLimit β p α (I.Ξ n ω α) (R.chartWeightCM α * A n ω α) else 0)
      atTop 0 := by
  have htail := I.random_mark_tail_tendsto hW hφ hφi hβ ham hM ha hMtight (R.rlct + p) R.mult
  refine (tendstoInMeasure_add_zero hlocal htail).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hci : ∀ᵐ ω ∂P, ∀ α, ∀ u : cube d (R.b α),
      I.Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * I.Ξ n ω α u :=
    ae_all_iff.mpr fun α ↦ I.chart_identity n hn α
  filter_upwards [hci, I.tail_bound n, ha n, hfactor n hn] with ω hω hτ hMa hFa
  rw [I.weightedPartition_eq_radial_of_identity hW hφ hφi hβ (ham n ω)
    (hM n ω) hMa hp (A n ω) hFa hn ω hω hτ]
  ring

/-- The actual centered empirical loss has the half-radial self-field mark. -/
theorem ae_centered_loss_chart_factor {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, ∀ α (u : cube d (R.b α)),
      Real.sqrt n * (K (R.g α u) - I.Kn n ω (R.g α u)) =
        (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ (1 / 2 : ℝ) * I.Ξ n ω α u := by
  have hci : ∀ᵐ ω ∂P, ∀ α, ∀ u : cube d (R.b α),
      I.Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * I.Ξ n ω α u :=
    ae_all_iff.mpr fun α ↦ I.chart_identity n hn α
  filter_upwards [hci] with ω hω
  intro α u
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  have hmon : 0 ≤ ∏ j, (u : Fin d → ℝ) j ^ R.k α j :=
    Finset.prod_nonneg fun j _ ↦ pow_nonneg (u.2.1 j) _
  have hp : (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ (1 / 2 : ℝ) =
      ∏ j, (u : Fin d → ℝ) j ^ R.k α j := by
    rw [← Real.sqrt_eq_rpow, Finset.prod_pow_two_mul, Real.sqrt_sq hmon]
  rw [R.monomial α u u.2, hω α u, hp]
  field_simp
  ring

/-- Summed self-mark chart approximation for the training Gibbs numerator. -/
theorem self_mark_radial_sum_sub_limit_tendstoInMeasure (hβ : 0 < β) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ (R.rlct + (1 / 2 : ℝ)) / Real.log n ^ (R.mult - 1) *
        (∑ α, R.chartRadialInsertion α β (1 / 2) n (I.Ξ n ω α)
          (R.chartWeightCM α * I.Ξ n ω α)) -
        ∑ α, if R.IsEssential α then R.chartRadialLimit β (1 / 2) α
          (I.Ξ n ω α) (R.chartWeightCM α * I.Ξ n ω α) else 0) atTop 0 := by
  have hα : ∀ α, TendstoInMeasure P (fun (n : ℕ) ω ↦
      (n : ℝ) ^ (R.rlct + (1 / 2 : ℝ)) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β (1 / 2) n (I.Ξ n ω α)
          (R.chartWeightCM α * I.Ξ n ω α) -
        (if R.IsEssential α then R.chartRadialLimit β (1 / 2) α
          (I.Ξ n ω α) (R.chartWeightCM α * I.Ξ n ω α) else 0)) atTop 0 := by
    intro α
    obtain ⟨L, hL⟩ := R.exists_lipschitzOnWith_weight α
    apply I.self_mark_radial_insertion_sub_limit_tendstoInMeasure α hβ
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (R.chartWeightCM α)
    intro u
    simpa only [chartWeightCM_apply] using R.weight_sub_primaryZero_le hL u.2
  convert tendstoInMeasure_finset_sum_zero Finset.univ (fun α _ ↦ hα α) using 1
  ext n ω
  simp only [Finset.sum_sub_distrib, Finset.mul_sum]

end EmpiricalProcessInput
end SingularLearningTheory.ResolutionAtlas
