/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Penalty.Selection
public import SLT.MaximumLikelihood.DivergingPenalty.Envelope
import SLT.MaximumLikelihood.FinitePenalty.Geometry
public import SLT.MaximumLikelihood.Penalty.Functionals
public import SLT.MaximumLikelihood.Assembly

/-!
# DivergingPenaltyApproximation

Joint approximation by the reward on the penalty-minimizing zero set.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.MaximumLikelihood

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

private theorem penalty_mul_chartRadius_tendsto_zero (Q : ℝ) {aSeq : ℕ → ℝ}
    (hslow : ∀ r : ℝ, 0 < r → Tendsto (fun n : ℕ ↦ aSeq n / (n : ℝ) ^ r) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ aSeq n * ResolutionAtlas.chartRadius R Q n) atTop (𝓝 0) := by
  have hterm : ∀ α, Tendsto (fun n : ℕ ↦ aSeq n * (Q ^ 2 / (n : ℝ)) ^
      (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹)) atTop (𝓝 0) := by
    intro α
    have hs := sum_k_ne_zero (R.active α)
    have hc : (0 : ℝ) < (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) := by positivity
    have ht := (hslow _ hc).mul_const ((Q ^ 2) ^
      (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹))
    convert ht using 1
    · funext n
      rw [Real.div_rpow (sq_nonneg Q) (Nat.cast_nonneg n)]
      ring
    · simp
  have heq : (fun n : ℕ ↦ aSeq n * ResolutionAtlas.chartRadius R Q n) =
      fun n : ℕ ↦ ∑ α, aSeq n * (Q ^ 2 / (n : ℝ)) ^
        (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) := by
    funext n
    simp only [ResolutionAtlas.chartRadius, Finset.mul_sum]
  rw [heq]
  convert tendsto_finsetSum (Finset.univ : Finset R.ι) (fun α _ ↦ hterm α) using 1
  simp

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {σ : (Fin d → ℝ) → ℝ}
  {Ψ : ℕ → Ω → C(ResolutionAtlas.Domain R, ℝ)} {H : ℕ → Ω → ℝ}
  {S : ℕ → Ω → (Fin d → ℝ) → ℝ} {ŵ : ℕ → Ω → Fin d → ℝ}

/-- Joint unshifted approximation at the penalty-minimizing zero set. -/
theorem divergingPenalty_jointError_tendstoInMeasure
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ w ∈ W, K w < δ → ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hσ : Continuous (ResolutionAtlas.chartPenalty R σ)) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hσLip : ∀ α (u v : cube d (R.b α)),
      |σ (R.g α u) - σ (R.g α v)| ≤ Λ * dist u v)
    {aSeq : ℕ → ℝ} (haSeq : ∀ n, 0 ≤ aSeq n) (ha : Tendsto aSeq atTop atTop)
    (hslow : ∀ r : ℝ, 0 < r → Tendsto (fun n : ℕ ↦ aSeq n / (n : ℝ) ^ r) atTop (𝓝 0))
    (hH0 : ∀ n ω, 0 ≤ H n ω) (hNorm : ∀ n ω, ‖Ψ n ω‖ ≤ H n ω)
    (hTail : ∀ η > 0, ∃ B > 0, ∀ n : ℕ, P {ω | B < H n ω} ≤ ENNReal.ofReal η)
    (hLip : ∀ η > 0, ∃ C > 0, ∀ n : ℕ,
      P {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
        |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} ≤ ENNReal.ofReal η)
    (hS : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ α (u : cube d (R.b α)),
      S n ω (R.g α u) = (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ n ω ⟨α, u⟩)
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      S n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤ S n ω w + aSeq n * σ w)
    (hsharp : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P, (n : ℝ) * K (ŵ n ω) ≤ 4 * (H n ω) ^ 2 + 8) :
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω) -
          ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedPenaltyMinimizers R σ)
              (Ψ n ω),
        S n ω (ŵ n ω) + ResolutionAtlas.likelihoodRewardSup R
            (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω))) atTop 0 := by
  classical
  have hZc := ResolutionAtlas.isCompact_resolvedPenaltyMinimizers R hσ
  have hZne := ResolutionAtlas.resolvedPenaltyMinimizers_nonempty R hσ
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact ⟨0, fun n _ ↦ le_top⟩
  have hηR : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨B, hB, hBTail⟩ := hTail (η.toReal / 2) (half_pos hηR)
  obtain ⟨C, hC, hCLip⟩ := hLip (η.toReal / 2) (half_pos hηR)
  let κ := min 1 (ε / (2 * (B + 1)))
  have hκ : 0 < κ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hκ1 : κ ≤ 1 := min_le_left _ _
  have hκe : κ * (2 * (B + 1)) ≤ ε :=
    (le_div_iff₀ (by positivity : 0 < 2 * (B + 1))).mp (min_le_right _ _)
  let γ := κ / (C + 1)
  have hγ : 0 < γ := div_pos hκ (by positivity)
  have hγκ : C * γ ≤ κ := by
    dsimp [γ]
    have hh : κ / (C + 1) * (C + 1) = κ := div_mul_cancel₀ _ (by positivity)
    have hz : 0 ≤ κ / (C + 1) := div_nonneg hκ.le (by positivity)
    nlinarith
  have hγ1 : γ ≤ 1 := by
    dsimp [γ]
    rw [div_le_one (by positivity)]
    linarith
  have hκterm : B * κ / 2 + κ ^ 2 / 4 < ε := by
    nlinarith [mul_nonneg hκ.le (sub_nonneg.mpr hκ1)]
  obtain ⟨δs, hδs, hselect⟩ := ResolutionAtlas.exists_penalty_selection_threshold R hσ hγ hγ1
  let Q := Real.sqrt (4 * B ^ 2 + 8)
  have hQ2 : Q ^ 2 = 4 * B ^ 2 + 8 := Real.sq_sqrt (by positivity)
  have hBQ : B ^ 2 ≤ Q ^ 2 := by rw [hQ2]; nlinarith [sq_nonneg B]
  let θ := fun n ↦ C * ResolutionAtlas.chartRadius R Q n
  let c := fun n ↦ aSeq n * Λ * ResolutionAtlas.chartRadius R Q n
  let gap := fun n ↦ B * θ n + (θ n) ^ 2 / 4 + 2 * c n
  have hθ : Tendsto θ atTop (𝓝 0) := by
    simpa only [mul_zero] using (ResolutionAtlas.chartRadius_tendsto_zero R Q).const_mul C
  have hc : Tendsto c atTop (𝓝 0) := by
    convert (penalty_mul_chartRadius_tendsto_zero R Q hslow).mul_const Λ using 1
    · funext n; dsimp [c]; ring
    · simp
  have hgap : Tendsto gap atTop (𝓝 0) := by
    have ht := ((hθ.const_mul B).add ((hθ.pow 2).div_const 4)).add (hc.const_mul 2)
    simpa using ht
  have htol : Tendsto (fun n ↦ (B ^ 2 / 4 + gap n) / aSeq n) atTop (𝓝 0) := by
    have hinv := tendsto_inv_atTop_zero.comp ha
    have ht := ((tendsto_const_nhds (x := B ^ 2 / 4)).add hgap).mul hinv
    simpa only [Function.comp_def, add_zero, mul_zero, div_eq_mul_inv] using ht
  let errG := fun n ↦ mleErr' B (θ n) (B * θ n / 2 + 2 * c n) +
    gap n + B * κ / 2 + κ ^ 2 / 4
  let errT := fun n ↦ B * θ n / 2 + (θ n) ^ 2 / 4 + c n + c n +
    2 * gap n + B * κ / 2 + κ ^ 2 / 4
  have hecore : Tendsto (fun n ↦ mleErr' B (θ n) (B * θ n / 2 + 2 * c n)) atTop (𝓝 0) := by
    have hcont : Continuous (fun p : ℝ × ℝ ↦ mleErr' B p.1 (B * p.1 / 2 + 2 * p.2)) := by
      unfold mleErr'; fun_prop
    have ht := (hcont.tendsto (0, 0)).comp (hθ.prodMk_nhds hc)
    simpa [Function.comp_def, mleErr'_zero] using ht
  have hErrG : Tendsto errG atTop (𝓝 (B * κ / 2 + κ ^ 2 / 4)) := by
    have ht := ((hecore.add hgap).add_const (B * κ / 2)).add_const (κ ^ 2 / 4)
    simpa [errG] using ht
  have hErrT : Tendsto errT atTop (𝓝 (B * κ / 2 + κ ^ 2 / 4)) := by
    have ht := ((((((hθ.const_mul B).div_const 2).add ((hθ.pow 2).div_const 4)).add hc).add hc).add
      (hgap.const_mul 2)).add_const (B * κ / 2) |>.add_const (κ ^ 2 / 4)
    simpa [errT] using ht
  have hevδ := (tendsto_const_div_atTop_nhds_zero_nat (Q ^ 2)).eventually (eventually_lt_nhds hδ)
  have hdiv4 : Tendsto (fun n : ℕ ↦ B ^ 2 / (4 * (n : ℝ))) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (B ^ 2 / 4) using 1
    funext n
    rw [div_div]
  have hevlev : ∀ᶠ n : ℕ in atTop, ∀ α,
      B ^ 2 / (4 * (n : ℝ)) ≤ ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2 := by
    rw [eventually_all]
    intro α
    exact (hdiv4.eventually (eventually_lt_nhds
      (pow_pos (pow_pos (half_pos (R.b_pos α)) _) _))).mono fun n hn ↦ hn.le
  have hevsel := htol.eventually (eventually_lt_nhds hδs)
  have hevG := hErrG.eventually (eventually_lt_nhds hκterm)
  have hevT := hErrT.eventually (eventually_lt_nhds hκterm)
  have heva : ∀ᶠ n in atTop, 0 < aSeq n := ha.eventually (eventually_gt_atTop 0)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop 1, hevδ, hevlev, hevsel, hevG, hevT, heva, hsharp]
    with n hn hnδ hnlev hnsel hnG hnT hna hnsharp
  have hincl : ∀ᵐ ω ∂P,
      ω ∈ {ω | ε ≤ ‖((n : ℝ) * K (ŵ n ω) - ResolutionAtlas.likelihoodRewardSup R
          (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω),
        S n ω (ŵ n ω) + ResolutionAtlas.likelihoodRewardSup R
            (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω)) - 0‖} →
      ω ∈ {ω | B < H n ω} ∪ {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
        |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} := by
    filter_upwards [hS n hn, hŵW n, hmin n, hnsharp] with ω hSω hŵω hminω hlocω hbad
    by_contra hout
    change ¬ (B < H n ω ∨ ¬ ∀ α, ∀ u v : cube d (R.b α),
      |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v) at hout
    have hHB : H n ω ≤ B := not_lt.mp (not_or.mp hout).1
    have hL := not_not.mp (not_or.mp hout).2
    have hMB : ResolutionAtlas.positiveMax R (Ψ n ω) ≤ B :=
      (ResolutionAtlas.positiveMax_le_norm R _).trans ((hNorm n ω).trans hHB)
    have hlocQ : (n : ℝ) * K (ŵ n ω) ≤ Q ^ 2 := by
      rw [hQ2]
      have hp := pow_le_pow_left₀ (hH0 n ω) hHB 2
      linarith
    obtain ⟨hTω, -, v, hv, hpen, hfoot, hcore⟩ :=
      ResolutionAtlas.finitePenalty_core_at_and_exists_resolvedZero R
      (by omega : 0 < n) (Ψ n ω) hSω hcover hσ hΛ hσLip (haSeq n) hB.le
      (ResolutionAtlas.chartRadius_nonneg R Q n) hC.le hBQ (ResolutionAtlas.le_chartRadius R Q n)
          hnδ hnlev hL hŵω hminω hlocQ hMB
    let M := ResolutionAtlas.positiveMaxOn R (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω)
    have hM0 : 0 ≤ M := ResolutionAtlas.positiveMaxOn_nonneg R _ hZc hZne _
    have hMB' : M ≤ B := (ResolutionAtlas.positiveMaxOn_le_norm R _ hZc hZne _).trans
        ((hNorm n ω).trans hHB)
    have hF0 := ResolutionAtlas.selectedReward_sub_penaltyMinimum_le R hσ (aSeq n) (Ψ n ω)
    rw [ResolutionAtlas.likelihoodRewardSup_eq_positiveMaxOn_sq R _ hZc hZne] at hF0
    have hmzB : max 0 (-Ψ n ω v) ≤ B := (ResolutionAtlas.le_positiveMax R _ hv).trans hMB
    have hselv : ResolutionAtlas.chartPenalty R σ v ≤ ResolutionAtlas.penaltyMinimum R σ +
        (B ^ 2 / 4 + gap n) / aSeq n →
        max 0 (-Ψ n ω v) ≤ M + κ := by
      intro hp
      have hvnear : ResolutionAtlas.chartPenalty R σ v ≤ ResolutionAtlas.penaltyMinimum R σ + δs :=
          by linarith
      have hh := hselect C hC.le (Ψ n ω) hL v hv hvnear
      exact hh.trans (add_le_add le_rfl hγκ)
    have hrad0 := ResolutionAtlas.chartRadius_nonneg R Q n
    have han0 := haSeq n
    obtain ⟨hGω, hTω'⟩ := abs_sub_sq_div_four_le_and_abs_add_sq_div_four_le hna
      (show 0 ≤ c n by dsimp [c]; positivity)
      (show 0 ≤ gap n by dsimp [gap, θ, c]; positivity) hκ.le
      (le_max_left _ _) hmzB hM0 hMB'
      (ResolutionAtlas.penaltyMinimum_le R hσ hv) hF0
      (ResolutionAtlas.le_penalizedMax R (ResolutionAtlas.chartPenalty R σ) hσ (aSeq n) (Ψ n ω) hv)
      hfoot hpen hcore hTω hselv
    have hreward : ResolutionAtlas.likelihoodRewardSup R (ResolutionAtlas.resolvedPenaltyMinimizers
        R σ) (Ψ n ω) = M ^ 2 / 4 :=
      ResolutionAtlas.likelihoodRewardSup_eq_positiveMaxOn_sq R _ hZc hZne _
    have hGfinal : |(n : ℝ) * K (ŵ n ω) - ResolutionAtlas.likelihoodRewardSup R
        (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω)| < ε := by
      rw [hreward]
      exact hGω.trans_lt hnG
    have hTfinal : |S n ω (ŵ n ω) + ResolutionAtlas.likelihoodRewardSup R
        (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω)| < ε := by
      rw [hreward]
      exact hTω'.trans_lt hnT
    have hb := max_lt_iff.mpr ⟨hGfinal, hTfinal⟩
    have hbad' : ε ≤ max
        |(n : ℝ) * K (ŵ n ω) - ResolutionAtlas.likelihoodRewardSup R
            (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω)|
        |S n ω (ŵ n ω) + ResolutionAtlas.likelihoodRewardSup R
            (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω)| := by
      simpa only [Set.mem_ofPred_eq, sub_zero, Prod.norm_mk, Real.norm_eq_abs] using hbad
    exact (not_le.mpr hb) hbad'
  calc P {ω | ε ≤ ‖((n : ℝ) * K (ŵ n ω) - ResolutionAtlas.likelihoodRewardSup R
      (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω),
          S n ω (ŵ n ω) + ResolutionAtlas.likelihoodRewardSup R
              (ResolutionAtlas.resolvedPenaltyMinimizers R σ) (Ψ n ω)) - 0‖}
      ≤ P ({ω | B < H n ω} ∪ {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
          |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v}) := measure_mono_ae hincl
    _ ≤ P {ω | B < H n ω} + P {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
          |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η.toReal / 2) + ENNReal.ofReal (η.toReal / 2) := add_le_add (hBTail n) (hCLip n)
    _ = η := by
      rw [← ENNReal.ofReal_add (half_pos hηR).le (half_pos hηR).le, add_halves,
        ENNReal.ofReal_toReal hηtop]

end SingularLearningTheory.MaximumLikelihood
