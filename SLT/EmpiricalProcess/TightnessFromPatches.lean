/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.PatchMajorants
public import SLT.MeasureTheory.Integral.Lebesgue.Minkowski
import SLT.EmpiricalProcess.Tightness
public import SLT.EmpiricalProcess.Defs
import Mathlib.Order.CompletePartialOrder
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Tightness from majorants on a finite open cover

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 4.2.9] (1), the tightness argument from | |
| [Hit26, Lemma 4.2.4] and | |
| [Hit26, Lemma 4.2.8] |
`SingularLearningTheory.EmpiricalProcess.isTightMeasureSet_of_patchMajorants` |

Given majorants on each set of a finite open cover of the compact metric space `U`, the sup norm
of `Ψ_n` is bounded in probability (Markov on `Σ_i S_{i,n}`) and, below a Lebesgue number of
the cover, the increments of `Ψ_n` are controlled by `Σ_i R_{i,n}` times the distance (Markov
again), uniformly in `n`; `MeasureTheory.isTightMeasureSet_of_bounded_of_equicontinuous` concludes.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {Ω U : Type*} [MeasurableSpace Ω] [MetricSpace U] [CompactSpace U]

omit [MetricSpace U] [CompactSpace U] in
/-- Markov's inequality for a second moment: if `∫ T² ≤ ε c²` then `P {c ≤ T} ≤ ε`.
No thesis counterpart; used by `EmpiricalProcess.isTightMeasureSet_of_patchMajorants`. -/
theorem _root_.MeasureTheory.measure_le_of_lintegral_sq_le {P : Measure Ω} {T : Ω → ℝ≥0∞}
    (hT : Measurable T)
    {c ε : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤) (hint : ∫⁻ ω, T ω ^ 2 ∂P ≤ ε * c ^ 2) :
    P {ω | c ≤ T ω} ≤ ε := by
  have hsub : {ω | c ≤ T ω} ⊆ {ω | c ^ 2 ≤ T ω ^ 2} :=
    fun ω hω ↦ show c ^ 2 ≤ T ω ^ 2 from pow_le_pow_left' hω 2
  rw [← ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hc) (ENNReal.pow_ne_top hc')]
  calc c ^ 2 * P {ω | c ≤ T ω} ≤ c ^ 2 * P {ω | c ^ 2 ≤ T ω ^ 2} :=
        mul_le_mul_right (measure_mono hsub) _
    _ ≤ ∫⁻ ω, T ω ^ 2 ∂P := mul_meas_ge_le_lintegral₀ (hT.pow_const 2).aemeasurable _
    _ ≤ ε * c ^ 2 := hint
    _ = c ^ 2 * ε := mul_comm _ _

omit [MetricSpace U] [CompactSpace U] in
/-- Minkowski for the sum of the patch majorants: `∫ (Σ_i g_i)² ≤ (Σ_i C_i^{1/2})²` when
`∫ g_i² ≤ C_i`. No thesis counterpart; used by
`EmpiricalProcess.isTightMeasureSet_of_patchMajorants`. -/
theorem _root_.MeasureTheory.lintegral_sum_sq_le_of_le {P : Measure Ω} {ι : Type*} [Fintype ι]
    {g : ι → Ω → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) {C : ι → ℝ≥0∞} (hC : ∀ i, ∫⁻ ω, g i ω ^ 2 ∂P ≤ C i) :
    ∫⁻ ω, (∑ i, g i ω) ^ 2 ∂P ≤ (∑ i, C i ^ (1 / 2 : ℝ)) ^ 2 :=
  (lintegral_sum_sq_le hg Finset.univ).trans <| pow_le_pow_left'
    (Finset.sum_le_sum fun i _ ↦ ENNReal.rpow_le_rpow (hC i) (by norm_num)) 2

/-- Tightness of `Ψ_n` in `C(U, ℝ)` from majorants on a finite open cover of `U`. -/
theorem EmpiricalProcess.isTightMeasureSet_of_patchMajorants {P : Measure Ω}
    [IsProbabilityMeasure P]
    {ι : Type*} [Finite ι] {B : ι → Set U} (hBo : ∀ i, IsOpen (B i)) (hBc : ⋃ i, B i = univ)
    {Ψ : ℕ → Ω → C(U, ℝ)} (hΨ : ∀ n, Measurable (Ψ n)) (M : ∀ i, EmpiricalProcess.PatchMajorants Ψ P
        (B i)) :
    IsTightMeasureSet (Set.range fun n ↦ P.map (Ψ n)) := by
  cases nonempty_fintype ι
  have hsum_ne_top : ∀ C : ι → ℝ≥0∞, (∀ i, C i ≠ ⊤) → (∑ i, C i ^ (1 / 2 : ℝ)) ^ 2 ≠ ⊤ :=
    fun C hC ↦ ENNReal.pow_ne_top <| ENNReal.sum_ne_top.mpr fun i _ ↦
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hC i)
  apply isTightMeasureSet_of_bounded_of_equicontinuous hΨ
  · intro ε hε
    set C : ℝ≥0∞ := (∑ i, (M i).CS ^ (1 / 2 : ℝ)) ^ 2 with hC
    have hCtop : C ≠ ⊤ := hsum_ne_top _ fun i ↦ (M i).CS_ne_top
    refine ⟨Real.sqrt (C.toReal / ε) + 1, fun n ↦ ?_⟩
    set K : ℝ := Real.sqrt (C.toReal / ε) + 1 with hK
    have hK0 : 0 < K := by positivity
    have hKC : C.toReal ≤ K ^ 2 * ε := by
      rw [← div_le_iff₀ hε, ← Real.sq_sqrt (div_nonneg ENNReal.toReal_nonneg hε.le)]
      exact pow_le_pow_left₀ (Real.sqrt_nonneg _) (le_add_of_nonneg_right zero_le_one) 2
    have hae : ∀ᵐ ω ∂P, ∀ i, ∀ u ∈ B i, ‖Ψ n ω u‖ₑ ≤ (M i).S n ω :=
      ae_all_iff.mpr fun i ↦ (M i).enorm_le n
    calc P {ω | K < ‖Ψ n ω‖} ≤ P {ω | ENNReal.ofReal K ≤ ∑ i, (M i).S n ω} := by
          refine measure_mono_ae ?_
          filter_upwards [hae] with ω hω hKω
          have h := (ContinuousMap.norm_le _ hK0.le).not.mp (not_le.mpr hKω)
          simp only [not_forall, not_le] at h
          obtain ⟨u, hu⟩ := h
          obtain ⟨i, hi⟩ := mem_iUnion.mp (hBc ▸ mem_univ u)
          calc ENNReal.ofReal K ≤ ENNReal.ofReal ‖Ψ n ω u‖ := ENNReal.ofReal_le_ofReal hu.le
            _ = ‖Ψ n ω u‖ₑ := ofReal_norm _
            _ ≤ (M i).S n ω := hω i u hi
            _ ≤ ∑ i, (M i).S n ω :=
              Finset.single_le_sum (f := fun i ↦ (M i).S n ω) (fun _ _ ↦ zero_le)
                (Finset.mem_univ i)
      _ ≤ ENNReal.ofReal ε := by
          refine measure_le_of_lintegral_sq_le
            (Finset.measurable_sum _ fun i _ ↦ (M i).S_measurable n)
            (ENNReal.ofReal_pos.mpr hK0).ne' ENNReal.ofReal_ne_top ?_
          refine (lintegral_sum_sq_le_of_le (fun i ↦ (M i).S_measurable n)
            fun i ↦ (M i).lintegral_S_sq_le n).trans ?_
          rw [← hC, ← ENNReal.ofReal_pow hK0.le, ← ENNReal.ofReal_mul hε.le,
            ← ENNReal.ofReal_toReal hCtop]
          exact ENNReal.ofReal_le_ofReal (by rw [mul_comm]; exact hKC)
  · intro ε hε a ha
    obtain ⟨l, hl, hball⟩ := lebesgue_number_lemma_of_metric isCompact_univ hBo (by rw [hBc])
    set C : ℝ≥0∞ := (∑ i, (M i).CR ^ (1 / 2 : ℝ)) ^ 2 with hC
    have hCtop : C ≠ ⊤ := hsum_ne_top _ fun i ↦ (M i).CR_ne_top
    have hC0 : 0 ≤ C.toReal := ENNReal.toReal_nonneg
    set δ : ℝ := min (l / 2) (Real.sqrt (ε * a ^ 2 / (C.toReal + 1))) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (Real.sqrt_pos.mpr (by positivity))
    have hδl : δ < l := (min_le_left _ _).trans_lt (half_lt_self hl)
    have hδsq : δ ^ 2 ≤ ε * a ^ 2 / (C.toReal + 1) := by
      rw [← Real.sq_sqrt (by positivity : 0 ≤ ε * a ^ 2 / (C.toReal + 1))]
      exact pow_le_pow_left₀ hδ0.le (min_le_right _ _) 2
    have hδC : C.toReal * δ ^ 2 ≤ ε * a ^ 2 :=
      calc C.toReal * δ ^ 2 ≤ (C.toReal + 1) * (ε * a ^ 2 / (C.toReal + 1)) :=
            mul_le_mul (by linarith) hδsq (by positivity) (by positivity)
        _ = ε * a ^ 2 := mul_div_cancel₀ _ (by positivity)
    refine ⟨δ, hδ0, fun n ↦ ?_⟩
    have hae : ∀ᵐ ω ∂P, ∀ i, ∀ u ∈ B i, ∀ v ∈ B i,
        ‖Ψ n ω u - Ψ n ω v‖ₑ ≤ (M i).R n ω * edist u v :=
      ae_all_iff.mpr fun i ↦ (M i).enorm_sub_le n
    calc P {ω | ∃ u v : U, dist u v ≤ δ ∧ a < |Ψ n ω u - Ψ n ω v|}
        ≤ P {ω | ENNReal.ofReal a ≤ (∑ i, (M i).R n ω) * ENNReal.ofReal δ} := by
          refine measure_mono_ae ?_
          filter_upwards [hae] with ω hω
          rintro ⟨u, v, huv, hlt⟩
          obtain ⟨i, hi⟩ := hball u (mem_univ u)
          have hu : u ∈ B i := hi (Metric.mem_ball_self hl)
          have hv : v ∈ B i := hi (by rw [Metric.mem_ball, dist_comm]; exact huv.trans_lt hδl)
          calc ENNReal.ofReal a ≤ ENNReal.ofReal |Ψ n ω u - Ψ n ω v| :=
                ENNReal.ofReal_le_ofReal hlt.le
            _ = ‖Ψ n ω u - Ψ n ω v‖ₑ := (Real.enorm_eq_ofReal_abs _).symm
            _ ≤ (M i).R n ω * edist u v := hω i u hu v hv
            _ ≤ (∑ i, (M i).R n ω) * ENNReal.ofReal δ :=
              mul_le_mul' (Finset.single_le_sum (f := fun i ↦ (M i).R n ω) (fun _ _ ↦ zero_le)
                (Finset.mem_univ i)) (by rw [edist_dist]; exact ENNReal.ofReal_le_ofReal huv)
      _ ≤ ENNReal.ofReal ε := by
          refine measure_le_of_lintegral_sq_le
            ((Finset.measurable_sum _ fun i _ ↦ (M i).R_measurable n).mul_const _)
            (ENNReal.ofReal_pos.mpr ha).ne' ENNReal.ofReal_ne_top ?_
          simp_rw [mul_pow]
          rw [lintegral_mul_const _
            ((Finset.measurable_sum _ fun i _ ↦ (M i).R_measurable n).pow_const 2)]
          refine (mul_le_mul_left (lintegral_sum_sq_le_of_le (fun i ↦ (M i).R_measurable n)
            fun i ↦ (M i).lintegral_R_sq_le n) _).trans ?_
          rw [← hC, ← ENNReal.ofReal_pow hδ0.le, ← ENNReal.ofReal_pow ha.le,
            ← ENNReal.ofReal_mul hε.le, ← ENNReal.ofReal_toReal hCtop,
            ← ENNReal.ofReal_mul hC0]
          exact ENNReal.ofReal_le_ofReal hδC

end SingularLearningTheory
