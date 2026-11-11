/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Density.AtlasChart
import SLT.SingularIntegrals.TypeOfAtlas
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# State-density asymptotics through a resolution atlas

The chart derivatives add below the atlas's localization threshold. Essential
charts contribute their exact coefficients; the other power-log scales vanish.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.ResolutionAtlas
open SliceDensity

variable {n : ℕ} {K φ : (Fin (n + 1) → ℝ) → ℝ} {W : Set (Fin (n + 1) → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- A nonessential chart's power-log scale is negligible at the atlas scale. -/
theorem tendsto_chartScale_ratio_zero {α : R.ι} (hα : ¬ R.IsEssential α) :
    Tendsto (fun t : ℝ ↦
      (t ^ R.chartRlct α * (-Real.log t) ^ (R.chartMult α - 1)) /
        (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0) (𝓝 0) := by
  let F : ℝ → ℝ := fun x ↦ if 2 ≤ x then
    Real.log x ^ (R.chartMult α - 1) / x ^ R.chartRlct α else 0
  have hF0 : ∀ x, 0 ≤ F x := by
    intro x
    dsimp [F]
    split_ifs with hx
    · exact div_nonneg (pow_nonneg (Real.log_nonneg (by linarith)) _)
        (Real.rpow_nonneg (by linarith) _)
    · rfl
  have hmlt : R.chartRlct α = R.rlct → R.chartMult α ≤ R.mult - 1 := by
    intro heq
    rcases (R.not_isEssential_iff α).mp hα with hlt | ⟨_, hlt⟩
    · exact (hlt.ne' heq).elim
    · omega
  have h := NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le (F := F) (C := 1) (q := 0)
    (lam := R.rlct) (r := R.mult - 1) (thr := R.chartRlct α)
    zero_le_one hF0 (fun x hx ↦ by simp [F, hx])
    (R.rlct_le_chartRlct α) (R.chartMult_pos α) hmlt
  have hi := h.comp tendsto_inv_nhdsGT_zero
  refine hi.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    tendsto_inv_nhdsGT_zero.eventually (eventually_ge_atTop (2 : ℝ))] with t ht h2
  simp only [Function.comp_apply, F, h2, ite_true, add_zero, Real.inv_rpow ht.le,
    Real.log_inv, div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

open Classical in
theorem tendsto_chartStateDensity_global (α : R.ι) :
    Tendsto (fun t ↦ t * R.chartStateDensity α t /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0)
      (𝓝 (if R.IsEssential α then R.rlct * R.sublevelChartCoefficient α else 0)) := by
  classical
  split_ifs with hα
  · simpa only [hα.1, hα.2, R.densityAtlas_coefficient hα.1] using
      R.tendsto_chartStateDensity α
  · have h := (R.tendsto_chartStateDensity α).mul (R.tendsto_chartScale_ratio_zero hα)
    simp only [mul_zero] at h
    refine h.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with t ht
    have hp : t ^ R.chartRlct α ≠ 0 := (Real.rpow_pos_of_pos ht.1 _).ne'
    have hl : (-Real.log t) ^ (R.chartMult α - 1) ≠ 0 :=
      pow_ne_zero _ (neg_pos.mpr (Real.log_neg ht.1 ht.2)).ne'
    field_simp

theorem tendsto_sum_chartStateDensity :
    Tendsto (fun t ↦ t * (∑ α, R.chartStateDensity α t) /
      (t ^ R.rlct * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0)
      (𝓝 (R.rlct * R.sublevelCoefficient)) := by
  classical
  have h := tendsto_finsetSum (Finset.univ : Finset R.ι)
    fun α _ ↦ R.tendsto_chartStateDensity_global α
  simpa only [sublevelCoefficient, Finset.mul_sum, Finset.sum_div,
    mul_ite, mul_zero] using h

/-- Below the cutoff, the sublevel volume is exactly the sum of chart volumes. -/
theorem sublevelVolume_eq_sum_chartVolume (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    {t : ℝ} (ht : 0 < t) (hδ : t < R.δ) :
    sublevelVolume K φ W t = ∑ α, sublevelVolume
      (fun u ↦ ∏ j, u j ^ (2 * R.k α j))
      (fun u ↦ (∏ j, u j ^ (R.h α j : ℝ)) * R.densityWeight α u)
      (cube (n + 1) (R.b α)) t := by
  have h := R.sublevelVolume_inv_eq_sum hW hKm hφ hφi (inv_pos.mpr ht)
    (by simpa only [inv_inv] using hδ)
  rw [inv_inv] at h
  refine h.trans (Finset.sum_congr rfl fun α _ ↦ ?_)
  unfold sublevelChartMass sublevelVolume
  apply setIntegral_congr_fun (R.measurableSet_cube α)
  intro u hu
  have hc : t⁻¹ * (∏ j, u j ^ (2 * R.k α j)) ≤ 1 ↔
      (∏ j, u j ^ (2 * R.k α j)) ≤ t := by
    rw [← div_eq_inv_mul, div_le_iff₀ ht, one_mul]
  by_cases hle : (∏ j, u j ^ (2 * R.k α j)) ≤ t
  · simp [SublevelVolume.cutoff, Set.indicator, R.densityWeight_eq hu, hle, hc.mpr hle]
  · simp [SublevelVolume.cutoff, Set.indicator, hle, mt hc.mp hle]

/-- On a positive neighborhood of zero, the chart densities sum to the derivative. -/
theorem eventually_hasDerivAt_sublevelVolume (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) :
    ∀ᶠ t in 𝓝[>] 0, HasDerivAt (sublevelVolume K φ W)
      (∑ α, R.chartStateDensity α t) t := by
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ α : R.ι,
      t < R.b α ^ aExp (R.k α) (R.densityCoordinate α) := by
    apply eventually_all.mpr
    intro α
    exact (eventually_lt_nhds (Real.rpow_pos_of_pos (R.b_pos α) _)).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [Ioo_mem_nhdsGT R.δ_pos, hsmall] with t ht hs
  have hd := HasDerivAt.fun_sum (u := Finset.univ) fun α _ ↦
    R.hasDerivAt_chartVolume α ht.1 (hs α)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
  exact R.sublevelVolume_eq_sum_chartVolume hW hKm hφ hφi hs.1 hs.2

theorem tendsto_deriv_sublevelVolume (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) :
    (∀ᶠ t in 𝓝[>] 0, DifferentiableAt ℝ (sublevelVolume K φ W) t) ∧
      Tendsto (fun t ↦ deriv (sublevelVolume K φ W) t /
        (t ^ (R.rlct - 1) * (-Real.log t) ^ (R.mult - 1))) (𝓝[>] 0)
        (𝓝 (R.rlct * R.sublevelCoefficient)) := by
  have hd := R.eventually_hasDerivAt_sublevelVolume hW hKm hφ hφi
  refine ⟨hd.mono fun _ h ↦ h.differentiableAt, R.tendsto_sum_chartStateDensity.congr' ?_⟩
  filter_upwards [hd, self_mem_nhdsWithin] with t ht ht0
  rw [ht.deriv, Real.rpow_sub_one (show 0 < t from ht0).ne']
  field_simp

end SingularLearningTheory.ResolutionAtlas
