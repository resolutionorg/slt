/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.SingularityType
public import SLT.VolumeScaling.Invariance
import SLT.VolumeScaling.Laplace.Asymptotic
import SLT.VolumeScaling.Laplace.Model
public import SLT.VolumeScaling.Laplace.Scale
public import SLT.SingularIntegrals.Transforms
import Mathlib.Algebra.Ring.IsFormallyReal
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Consequences of a precise sublevel-volume limit

The caller supplies the volume limit proved by the resolution-chart argument.
The exponent `m - 1` in the interface is a natural exponent, matching the challenge statement.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology SingularLearningTheory
open scoped ENNReal

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- Local continuity suffices to replace the indicator definition by a sublevel-set integral. -/
private theorem sublevelVolume_eq_setIntegral_of_continuousOn
    (hW : IsCompact W) (hKc : ContinuousOn K W) (t : ℝ) :
    sublevelVolume K φ W t = ∫ w in W ∩ {w | K w ≤ t}, φ w := by
  classical
  have hS : MeasurableSet (W ∩ {w | K w ≤ t}) :=
    (hW.isClosed.isClosed_le hKc continuousOn_const).measurableSet
  calc
    sublevelVolume K φ W t =
        ∫ w in W, (W ∩ {w | K w ≤ t}).indicator φ w := by
      unfold sublevelVolume
      refine setIntegral_congr_fun hW.measurableSet fun w hw ↦ ?_
      simp only [Set.indicator_apply, Set.mem_inter_iff, Set.mem_ofPred_eq, hw, true_and]
    _ = ∫ w in W ∩ (W ∩ {w | K w ≤ t}), φ w := setIntegral_indicator hS
    _ = ∫ w in W ∩ {w | K w ≤ t}, φ w := by rw [← inter_assoc, inter_self]

/-- The sharp Laplace coefficient and both logarithmic limits follow from the sharp volume
coefficient. Positivity of `lam` is unnecessary for this implication: the library's finite-mass
Abelian theorem already infers `0 ≤ lam` from the volume limit. -/
theorem sublevelVolume_limit_consequences
    (hW : IsCompact W) (hKc : ContinuousOn K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) {lam C : ℝ} {m : ℕ}
    (hm : 1 ≤ m) (hC : 0 < C)
    (hV : Tendsto (fun t ↦ sublevelVolume K φ W t /
      (t ^ lam * (-Real.log t) ^ (m - 1))) (𝓝[>] 0) (𝓝 C)) :
    (∀ β > 0, Tendsto
      (fun n : ℝ ↦ n ^ lam / Real.log n ^ (m - 1) *
        normalizedPartitionFunction K φ W β n)
      atTop (𝓝 (C * Real.Gamma (lam + 1) / β ^ lam))) ∧
    Tendsto (fun n : ℝ ↦
      -Real.log (normalizedPartitionFunction K φ W 1 n) / Real.log n)
      atTop (𝓝 lam) ∧
    (∀ a : ℝ, 0 < a → a ≠ 1 → Tendsto
      (fun t ↦ Real.log (sublevelVolume K φ W (a * t) /
        sublevelVolume K φ W t) / Real.log a)
      (𝓝[>] 0) (𝓝 lam)) := by
  let μ := priorMeasure φ Set.univ
  have hWm := hW.measurableSet
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
    rw [Nat.cast_sub hm, Nat.cast_one]
  have hpow (x : ℝ) : x ^ ((m : ℝ) - 1) = x ^ (m - 1) := by
    rw [← hmcast, Real.rpow_natCast]
  have hVs (t : ℝ) : sublevelVol μ W K t = sublevelVolume K φ W t :=
    (sublevelVol_priorMeasure hWm hφ hφi.aemeasurable t).trans
      (sublevelVolume_eq_setIntegral_of_continuousOn hW hKc t).symm
  have hratio : Tendsto
      (fun t ↦ sublevelVolume K φ W t / llcScale lam (m : ℝ) t)
      (𝓝[>] 0) (𝓝 C) := by
    simpa only [llcScale, hpow] using hV
  have htype : HasLLCOn μ W K lam (m : ℝ) C := by
    unfold HasLLCOn
    simpa only [hVs] using hratio
  have hfin : μ W ≠ ⊤ := priorMeasure_ne_top hWm hφi
  have hac : μ.restrict W ≪ volume.restrict W := by
    change (priorMeasure φ Set.univ).restrict W ≪ volume.restrict W
    rw [priorMeasure, Measure.restrict_univ, restrict_withDensity hWm]
    exact withDensity_absolutelyContinuous _ _
  have hf : AEMeasurable K (μ.restrict W) :=
    (hKc.aemeasurable hWm).mono_ac hac
  have hf0 : 0 ≤ᵐ[μ.restrict W] K :=
    hac.ae_le ((ae_restrict_iff' hWm).mpr (.of_forall hK))
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ
    have hdil := tendsto_div_const_nhdsGT_zero hβ
    have hsub (t : ℝ) :
        sublevelVol μ W (fun w ↦ β * K w) t = sublevelVol μ W K (t / β) := by
      have hset : W ∩ {w | β * K w ≤ t} = W ∩ {w | K w ≤ t / β} := by
        ext w
        simp only [mem_inter_iff, mem_ofPred_eq, le_div_iff₀ hβ, mul_comm (K w) β]
      change (μ (W ∩ {w | β * K w ≤ t})).toReal =
        (μ (W ∩ {w | K w ≤ t / β})).toReal
      rw [hset]
    have hβtype : HasLLCOn μ W (fun w ↦ β * K w) lam (m : ℝ) (C / β ^ lam) := by
      have hbase : Tendsto (fun t ↦ sublevelVol μ W K t / llcScale lam (m : ℝ) t)
          (𝓝[>] 0) (𝓝 C) := htype
      have hh := (hbase.comp hdil).mul
        (tendsto_llcScale_div_const_ratio (lam := lam) (theta := (m : ℝ)) hβ)
      have hc : C * β ^ (-lam) = C / β ^ lam := by
        rw [Real.rpow_neg hβ.le, div_eq_mul_inv]
      rw [hc] at hh
      unfold HasLLCOn
      refine hh.congr' ?_
      filter_upwards [hdil.eventually
        (llcScale_eventually_pos (lam := lam) (theta := (m : ℝ)))] with t ht
      change (sublevelVol μ W K (t / β) / llcScale lam (m : ℝ) (t / β)) *
          (llcScale lam (m : ℝ) (t / β) / llcScale lam (m : ℝ) t) =
        sublevelVol μ W (fun w ↦ β * K w) t / llcScale lam (m : ℝ) t
      rw [hsub, div_mul_div_cancel₀ ht.ne']
    have hh := hβtype.laplace_div_tendsto
      (div_pos hC (Real.rpow_pos_of_pos hβ lam)) (hf.const_mul β)
      (hf0.mono fun w hw ↦ mul_nonneg hβ.le hw) hfin
    have hc : (C / β ^ lam) * Real.Gamma (lam + 1) =
        C * Real.Gamma (lam + 1) / β ^ lam := by ring
    rw [hc] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    rw [normalizedPartitionFunction_eq_integral_priorMeasure hWm hφ hφi β n]
    simp only [laplaceScale, hpow, Real.rpow_neg (one_pos.trans hn).le]
    have hp : n ^ lam ≠ 0 := (Real.rpow_pos_of_pos (one_pos.trans hn) lam).ne'
    have hl : Real.log n ^ (m - 1) ≠ 0 := pow_ne_zero _ (Real.log_pos hn).ne'
    field_simp [hp, hl] <;> ring
  · have hrem := (htype.log_laplace_tendsto hC hf hf0 hfin).div_atTop
      Real.tendsto_log_atTop
    have hll : Tendsto (fun n : ℝ ↦ Real.log (Real.log n) / Real.log n)
        atTop (𝓝 0) := by
      simpa only [Function.comp_def, Real.rpow_one] using
        (Real.tendsto_log_rpow_div_atTop 1).comp Real.tendsto_log_atTop
    have hh := ((tendsto_const_nhds (α := ℝ) (x := lam)).sub
      (hll.const_mul ((m : ℝ) - 1))).sub hrem
    simp only [mul_zero, sub_zero] at hh
    refine hh.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with n hn
    rw [normalizedPartitionFunction_eq_integral_priorMeasure hWm hφ hφi 1 n]
    simp only [one_mul]
    have hl : Real.log n ≠ 0 := (Real.log_pos hn).ne'
    field_simp [hl] <;> ring
  · intro a ha ha1
    have hdil : Tendsto (fun t : ℝ ↦ a * t) (𝓝[>] 0) (𝓝[>] 0) := by
      simpa only [div_inv_eq_mul, mul_comm] using
        (tendsto_div_const_nhdsGT_zero (inv_pos.mpr ha))
    have hscale : Tendsto
        (fun t ↦ llcScale lam (m : ℝ) (a * t) / llcScale lam (m : ℝ) t)
        (𝓝[>] 0) (𝓝 (a ^ lam)) := by
      simpa only [div_inv_eq_mul, mul_comm, Real.inv_rpow ha.le,
        Real.rpow_neg ha.le, inv_inv] using
        (tendsto_llcScale_div_const_ratio (lam := lam) (theta := (m : ℝ))
          (inv_pos.mpr ha))
    have hh := ((hratio.comp hdil).div hratio hC.ne').mul hscale
    simp only [div_self hC.ne', one_mul] at hh
    have hquot : Tendsto
        (fun t ↦ sublevelVolume K φ W (a * t) / sublevelVolume K φ W t)
        (𝓝[>] 0) (𝓝 (a ^ lam)) := by
      refine hh.congr' ?_
      filter_upwards [llcScale_eventually_pos (lam := lam) (theta := (m : ℝ)),
        hdil.eventually (llcScale_eventually_pos (lam := lam) (theta := (m : ℝ)))]
        with t ht hat
      change (sublevelVolume K φ W (a * t) / llcScale lam (m : ℝ) (a * t)) /
          (sublevelVolume K φ W t / llcScale lam (m : ℝ) t) *
          (llcScale lam (m : ℝ) (a * t) / llcScale lam (m : ℝ) t) =
        sublevelVolume K φ W (a * t) / sublevelVolume K φ W t
      by_cases hv : sublevelVolume K φ W t = 0
      · simp [hv]
      · field_simp [ht.ne', hat.ne', hv] <;> ring
    have hlog := (hquot.log (Real.rpow_pos_of_pos ha lam).ne').div_const (Real.log a)
    simpa only [Real.log_rpow ha,
      mul_div_cancel_right₀ _ (Real.log_ne_zero_of_pos_of_ne_one ha ha1)] using hlog

end SingularLearningTheory
