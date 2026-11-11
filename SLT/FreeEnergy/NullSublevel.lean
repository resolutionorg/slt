/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.StochasticAsymptotics
public import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.FundamentalConditions

/-!
# The evidence when `W` carries no mass near the zeros of `K`

If `W ∩ {K ≤ δ}` is null for some `δ > 0`, the normalised evidence
`Z_n^0 = ∫_W e^{-nβ K_n} φ` tends to `0` in probability
(`SingularLearningTheory.FundamentalConditionI.tendstoInMeasure_evidence_of_null_sublevel`): off a
null set every point of `W` has `K > δ`, where
`n K_n ≥ nδ/2 − B_n²/2` with `B_n = sup_{K ≥ δ} |ψ_n|` bounded in probability (the tail estimate of
the proof of [Hit26, Theorem 5.2.6], without the localised part). It is the
degenerate case of [Wat09, Theorem 6.7] for a resolution whose resolved parameter set misses the
zeros of `K`, where the limit is `Y = 0`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

omit [MeasurableSpace X] in
/-- [Hit26, Lemma 5.2.4] at a point where `K ≥ δ`:
`n K_n = n K + √n √K ψ_n ≥ nδ/2 − ψ_n²/2`. -/
private theorem le_mul_empiricalLoss_of_abs_tailProcess_le {Ω : Type*} {K : (Fin d → ℝ) → ℝ}
    {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X} {δ : ℝ} (hδ : 0 < δ) {n : ℕ} {ω : Ω}
    {w : Fin d → ℝ} {B : ℝ} (hKδ : δ ≤ K w) (hψ : |tailProcess K f Xs n ω w| ≤ B) :
    n * δ / 2 - B ^ 2 / 2 ≤ n * empiricalLoss f Xs n ω w := by
  have hKpos : 0 < K w := hδ.trans_le hKδ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_mul, zero_div, zero_sub]
    have := sq_nonneg B
    linarith
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hsq : Real.sqrt n * Real.sqrt (K w) * tailProcess K f Xs n ω w
        = ∑ i ∈ Finset.range n, (f (Xs i ω) w - K w) := by
      rw [tailProcess, mul_comm, div_mul_cancel₀ _ (by positivity)]
    have hid : n * empiricalLoss f Xs n ω w
        = n * K w + Real.sqrt n * Real.sqrt (K w) * tailProcess K f Xs n ω w := by
      rw [hsq, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        empiricalLoss, mul_div_cancel₀ _ hn0.ne']
      ring
    have h1 : (Real.sqrt n * Real.sqrt (K w)) ^ 2 = n * K w := by
      rw [mul_pow, Real.sq_sqrt hn0.le, Real.sq_sqrt hKpos.le]
    have hyoung := sq_nonneg (Real.sqrt n * Real.sqrt (K w) + tailProcess K f Xs n ω w)
    have hψ2 : tailProcess K f Xs n ω w ^ 2 ≤ B ^ 2 :=
      sq_le_sq' (abs_le.mp hψ).1 (abs_le.mp hψ).2
    have hnδ : n * δ ≤ n * K w := mul_le_mul_of_nonneg_left hKδ hn0.le
    rw [hid]
    nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] {q : Measure X} [IsProbabilityMeasure q]
  {P : Measure Ω} [IsProbabilityMeasure P] {Xs : ℕ → Ω → X}
  {s : ℝ≥0∞} [Fact (1 ≤ s)] {f : X → (Fin d → ℝ) → ℝ} {K φ : (Fin d → ℝ) → ℝ}
  {W : Set (Fin d → ℝ)}

/-- **The evidence without mass near the zeros**: if `W ∩ {K ≤ δ}` is null, then
`∫_W e^{-nβ K_n} φ → 0` in probability. -/
theorem FundamentalConditionI.tendstoInMeasure_evidence_of_null_sublevel
    (I : FundamentalConditionI s q f K W)
    (hW : IsCompact W) (hf : Measurable (Function.uncurry f))
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W) {δ : ℝ} (hδ : 0 < δ)
    (hnull : volume (W ∩ {w | K w ≤ δ}) = 0) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    {β : ℝ} (hβ : 0 < β) (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hind : iIndepFun Xs P) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      ∫ w in W, Real.exp (-(n * β * empiricalLoss f Xs n ω w)) * φ w) atTop 0 := by
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  have : CompactSpace {w // w ∈ W ∧ δ ≤ K w} :=
    isCompact_iff_compactSpace.mp (I.isCompact_tail hW δ)
  obtain ⟨P₂, hP₂, ⟨T⟩⟩ := I.exists_tail_empiricalProcessLimit hW
    (fun w ↦ hf.comp (measurable_id.prodMk measurable_const)) hcont hδ hX hlaw hind
  set B : ℕ → Ω → ℝ := fun n ω ↦ ‖T.Ψ n ω‖
  set c := ∫ w in W, φ w
  have hc : 0 ≤ c := setIntegral_nonneg hWm hφ
  have hae : ∀ᵐ w ∂(volume.restrict W), δ < K w := by
    rw [ae_restrict_iff' hWm]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with w hw hwW
    exact lt_of_not_ge fun h ↦ hw ⟨hwW, h⟩
  have hnonneg : ∀ (n : ℕ) ω,
      0 ≤ ∫ w in W, Real.exp (-(n * β * empiricalLoss f Xs n ω w)) * φ w := fun n ω ↦
    setIntegral_nonneg hWm fun w hw ↦ mul_nonneg (Real.exp_pos _).le (hφ w hw)
  have hbound : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∫ w in W, Real.exp (-(n * β * empiricalLoss f Xs n ω w)) * φ w
        ≤ Real.exp (-(n * β * δ / 2)) * Real.exp (β * B n ω ^ 2 / 2) * c := by
    intro n
    filter_upwards [T.Ψ_ae_eq n] with ω hω
    rw [← integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hφi.const_mul _) ?_
    · filter_upwards [ae_restrict_mem hWm] with w hw
      exact mul_nonneg (Real.exp_pos _).le (hφ w hw)
    · filter_upwards [hae, ae_restrict_mem hWm] with w hKw hw
      have hψ : |tailProcess K f Xs n ω w| ≤ B n ω := by
        have : T.Ψ n ω ⟨w, hw, hKw.le⟩ = tailProcess K f Xs n ω w := by
          rw [hω, tailProcess_eq_empiricalProcess I.K_eq]
          rfl
        rw [← this, ← Real.norm_eq_abs]
        exact ContinuousMap.norm_coe_le_norm _ _
      have h1 := le_mul_empiricalLoss_of_abs_tailProcess_le hδ hKw.le hψ
      have h2 : Real.exp (-(n * β * empiricalLoss f Xs n ω w))
          ≤ Real.exp (-(n * β * δ / 2)) * Real.exp (β * B n ω ^ 2 / 2) := by
        rw [← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have := mul_le_mul_of_nonneg_left h1 hβ.le
        nlinarith
      calc Real.exp (-(n * β * empiricalLoss f Xs n ω w)) * φ w
          ≤ Real.exp (-(n * β * δ / 2)) * Real.exp (β * B n ω ^ 2 / 2) * φ w :=
            mul_le_mul_of_nonneg_right h2 (hφ w hw)
        _ = _ := by ring
  have hZ := tendstoInMeasure_of_uniform_on (P := P) (B := fun j : ℕ ↦ {x : ℝ | |x| ≤ j})
    (X := B) (G := fun _ ↦ (0 : ℝ))
    (F := fun (n : ℕ) (x : ℝ) ↦ Real.exp (-(n * β * δ / 2)) * Real.exp (β * x ^ 2 / 2) * c)
    (fun j ε hε ↦ ?_) (fun η hη ↦ ?_)
  · refine tendstoInMeasure_zero_of_abs_le (fun n ↦ ?_) hZ
    filter_upwards [hbound n] with ω hω
    simp only [sub_zero]
    rw [abs_of_nonneg (hnonneg n ω)]
    exact hω
  · have h := ((Real.tendsto_normalization_mul_exp 0 0
      (div_pos (mul_pos hβ hδ) two_pos)).mul_const (Real.exp (β * (j : ℝ) ^ 2 / 2) * c))
    rw [zero_mul] at h
    obtain ⟨N, hN⟩ := eventually_atTop.mp (h.eventually (eventually_le_nhds hε))
    refine ⟨N, fun n hn x hx ↦ ?_⟩
    have hx2 : x ^ 2 ≤ (j : ℝ) ^ 2 := sq_le_sq' (abs_le.mp hx).1 (abs_le.mp hx).2
    simp only [sub_zero]
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) hc)]
    have hNn := hN n hn
    simp only [Real.rpow_zero, Nat.zero_sub, pow_zero, div_one, one_mul] at hNn
    calc Real.exp (-(n * β * δ / 2)) * Real.exp (β * x ^ 2 / 2) * c
        ≤ Real.exp (-(n * β * δ / 2)) * Real.exp (β * (j : ℝ) ^ 2 / 2) * c := by gcongr
      _ = Real.exp (-(n * (β * δ / 2))) * (Real.exp (β * (j : ℝ) ^ 2 / 2) * c) := by
          rw [show (n : ℝ) * β * δ / 2 = n * (β * δ / 2) by ring]; ring
      _ ≤ ε := hNn
  · obtain ⟨M, N, hMN⟩ := T.tendsto.eventually_measure_norm_gt_le hη
    refine ⟨⌈M⌉₊, N, fun n hn ↦ (measure_mono fun ω hω ↦ ?_).trans (hMN n hn)⟩
    simp only [mem_ofPred_eq, not_le] at hω ⊢
    simp only [B, abs_norm] at hω
    exact (Nat.le_ceil M).trans_lt hω

end SingularLearningTheory
