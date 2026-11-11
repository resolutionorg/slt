/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.FinitePenalty.Geometry
public import SLT.FreeEnergy.Discharge
public import SLT.MaximumLikelihood.Penalty.Functionals

/-!
# PenaltySelection

Compactness selects the penalty-minimizing part of the resolved zero set.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.ResolutionAtlas

open SingularLearningTheory.MaximumLikelihood

variable {d : ℕ} {K φ σ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

private theorem chartPenalty_eq_min_of_mem (hσ : Continuous (chartPenalty R σ))
    {v : Domain R} (hv : v ∈ resolvedPenaltyMinimizers R σ) :
    chartPenalty R σ v = penaltyMinimum R σ := by
  obtain ⟨w, hw, heq⟩ := exists_penaltyMinimum_eq R hσ
  apply le_antisymm
  · have hp := hv.2 w hw
    simpa only [heq] using hp
  · exact penaltyMinimum_le R hσ hv.1

theorem selectedReward_sub_penaltyMinimum_le (hσ : Continuous (chartPenalty R σ))
    (a : ℝ) (Ψ : C(Domain R, ℝ)) :
    likelihoodRewardSup R (resolvedPenaltyMinimizers R σ) Ψ - a * penaltyMinimum R σ ≤
      penalizedLikelihoodRewardSup R σ a Ψ := by
  have hZc := isCompact_resolvedPenaltyMinimizers R hσ
  have hZne := resolvedPenaltyMinimizers_nonempty R hσ
  obtain ⟨v, hv, heq⟩ := exists_positiveMaxOn_eq R _ hZc hZne Ψ
  rw [likelihoodRewardSup_eq_positiveMaxOn_sq R _ hZc hZne Ψ, heq]
  have hp := le_penalizedMax R (chartPenalty R σ) hσ a Ψ hv.1
  rw [chartPenalty_eq_min_of_mem R hσ hv] at hp
  exact hp

/-- A deterministic near-minimum threshold works uniformly over every path whose
within-chart Lipschitz constant is bounded by C. It is independent of the norm of Ψ. -/
theorem exists_penalty_selection_threshold (hσ : Continuous (chartPenalty R σ))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ δ > 0, ∀ (C : ℝ), 0 ≤ C → ∀ Ψ : C(Domain R, ℝ),
      (∀ α (u v : cube d (R.b α)), |Ψ ⟨α, u⟩ - Ψ ⟨α, v⟩| ≤ C * dist u v) →
      ∀ v ∈ resolvedZeroSet R, chartPenalty R σ v ≤ penaltyMinimum R σ + δ →
        max 0 (-Ψ v) ≤ positiveMaxOn R (resolvedPenaltyMinimizers R σ) Ψ + C * ε := by
  classical
  letI : MetricSpace (Domain R) := Metric.Sigma.metricSpace
  let laplaceIntegral := resolvedPenaltyMinimizers R σ
  have hZc := isCompact_resolvedZeroSet R
  have hO : IsOpen (Metric.thickening ε laplaceIntegral) := Metric.isOpen_thickening
  have hminO : ∀ z ∈ resolvedZeroSet R, chartPenalty R σ z = penaltyMinimum R σ →
      z ∈ Metric.thickening ε laplaceIntegral := by
    intro z hz heq
    have hz0 : z ∈ laplaceIntegral := by
      refine ⟨hz, fun v hv ↦ ?_⟩
      rw [heq]
      exact penaltyMinimum_le R hσ hv
    exact Metric.mem_thickening_iff.mpr ⟨z, hz0, by simpa using hε⟩
  obtain ⟨δ, hδ, hnear⟩ := IsCompact.near_minimum_subset_open hZc hσ.continuousOn
    (fun z hz ↦ penaltyMinimum_le R hσ hz) hO hminO
  refine ⟨δ, hδ, fun C hC Ψ hLip v hv hp ↦ ?_⟩
  obtain ⟨w, hw, hd⟩ := Metric.mem_thickening_iff.mp (hnear v hv hp)
  have hi := Metric.Sigma.fst_eq_of_dist_lt_one v w (hd.trans_le hε1)
  rcases v with ⟨α, u⟩
  rcases w with ⟨β, v⟩
  change α = β at hi
  subst β
  rw [R.sigma_dist_same] at hd
  have hfield := (hLip α u v).trans (mul_le_mul_of_nonneg_left hd.le hC)
  have hm := le_positiveMaxOn R laplaceIntegral (isCompact_resolvedPenaltyMinimizers R hσ) Ψ hw
  have hm0 := positiveMaxOn_nonneg R laplaceIntegral (isCompact_resolvedPenaltyMinimizers R hσ)
    (resolvedPenaltyMinimizers_nonempty R hσ) Ψ
  have hvmax := le_max_right 0 (-Ψ ⟨α, v⟩)
  have hlow := (abs_le.mp hfield).1
  exact max_le (by nlinarith [mul_nonneg hC hε.le]) (by linarith)

end SingularLearningTheory.ResolutionAtlas

namespace SingularLearningTheory.MaximumLikelihood

/-- Pure algebra extracting the selected reward from an almost-maximal foot.
G and q are unshifted; F may be negative. -/
theorem abs_sub_sq_div_four_le_and_abs_add_sq_div_four_le
    {G q F p pz m mz M B a c gap e t κ : ℝ}
    (ha : 0 < a) (hc : 0 ≤ c) (hgap : 0 ≤ gap) (hκ : 0 ≤ κ)
    (hmz0 : 0 ≤ mz) (hmzB : mz ≤ B) (hM0 : 0 ≤ M) (hMB : M ≤ B)
    (hmin : m ≤ pz) (hF0 : M ^ 2 / 4 - a * m ≤ F)
    (hFz : mz ^ 2 / 4 - a * pz ≤ F)
    (hfoot : F - (mz ^ 2 / 4 - a * pz) ≤ gap)
    (hpen : |a * p - a * pz| ≤ c)
    (hG : |G - mz ^ 2 / 4| ≤ e) (hT : |q + a * p + F| ≤ t)
    (hselect : pz ≤ m + (B ^ 2 / 4 + gap) / a → mz ≤ M + κ) :
    |G - M ^ 2 / 4| ≤ e + gap + B * κ / 2 + κ ^ 2 / 4 ∧
      |q + M ^ 2 / 4| ≤ t + c + 2 * gap + B * κ / 2 + κ ^ 2 / 4 := by
  have hmz2 := pow_le_pow_left₀ hmz0 hmzB 2
  have hnear : pz ≤ m + (B ^ 2 / 4 + gap) / a := by
    have hmul : a * (pz - m) ≤ B ^ 2 / 4 + gap := by nlinarith [sq_nonneg M]
    have hp := (le_div_iff₀ ha).mpr (by nlinarith only [hmul] : (pz - m) * a ≤ B ^ 2 / 4 + gap)
    linarith
  have hmzM := hselect hnear
  have hmzM2 := pow_le_pow_left₀ hmz0 hmzM 2
  have hMκ := mul_le_mul_of_nonneg_right hMB hκ
  have hpenmin := mul_le_mul_of_nonneg_left hmin ha.le
  have hrewardlo : M ^ 2 / 4 - mz ^ 2 / 4 ≤ gap := by linarith
  have hrewardhi : mz ^ 2 / 4 - M ^ 2 / 4 ≤ B * κ / 2 + κ ^ 2 / 4 := by nlinarith
  have hreward : |mz ^ 2 / 4 - M ^ 2 / 4| ≤ gap + B * κ / 2 + κ ^ 2 / 4 := by
    rw [abs_le]
    constructor <;> nlinarith [mul_nonneg (hM0.trans hMB) hκ, sq_nonneg κ]
  have hFabs : |F - (mz ^ 2 / 4 - a * pz)| ≤ gap := by
    rw [abs_of_nonneg (sub_nonneg.mpr hFz)]
    exact hfoot
  constructor
  · have h := abs_add_le (G - mz ^ 2 / 4) (mz ^ 2 / 4 - M ^ 2 / 4)
    have he : G - mz ^ 2 / 4 + (mz ^ 2 / 4 - M ^ 2 / 4) = G - M ^ 2 / 4 := by ring
    rw [he] at h
    linarith
  · have hp : |q + mz ^ 2 / 4| ≤ t + c + gap := by
      have h1 := abs_add_le (q + a * p + F) (-(a * p - a * pz))
      have h2 := abs_add_le (q + a * p + F - (a * p - a * pz))
        (-(F - (mz ^ 2 / 4 - a * pz)))
      simp only [abs_neg] at h1 h2
      have he : q + a * p + F - (a * p - a * pz) -
          (F - (mz ^ 2 / 4 - a * pz)) = q + mz ^ 2 / 4 := by ring
      simp only [← sub_eq_add_neg] at h1 h2
      rw [he] at h2
      linarith
    have h := abs_add_le (q + mz ^ 2 / 4) (M ^ 2 / 4 - mz ^ 2 / 4)
    rw [abs_sub_comm (M ^ 2 / 4)] at h
    have he : q + mz ^ 2 / 4 + (M ^ 2 / 4 - mz ^ 2 / 4) = q + M ^ 2 / 4 := by ring
    rw [he] at h
    linarith

end SingularLearningTheory.MaximumLikelihood
