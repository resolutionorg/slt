/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Envelope
public import SLT.MaximumLikelihood.Geometry
import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.FreeEnergy.FundamentalConditions

/-!
# Joint maximum-likelihood convergence

The chart error vanishes in probability on events controlling both the process
norm and its Lipschitz constants. One joint approximation gives both limiting
errors; fourth-moment domination then transfers their expectations.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.ResolutionAtlas

open SingularLearningTheory.MaximumLikelihood

section EnvelopeTail

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A uniform fourth-moment bound gives a uniform tail bound for a nonnegative envelope.
The threshold for Markov is B, using H^4 >= H on H > B >= 1. -/
theorem _root_.MeasureTheory.uniform_tail_of_fourth_moment {H : ℕ → Ω → ℝ}
    (hm : ∀ n : ℕ, Measurable (H n)) (h0 : ∀ (n : ℕ) ω, 0 ≤ H n ω)
    {D : ℝ≥0∞} (hD : D ≠ ⊤) (hfour : ∀ n : ℕ, ∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P ≤ D)
    {η : ℝ} (hη : 0 < η) :
    ∃ B : ℝ, 0 < B ∧ ∀ n : ℕ, P {ω | B < H n ω} ≤ ENNReal.ofReal η := by
  let B : ℝ := max 1 (D.toReal / η)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB1
  have hBne : ENNReal.ofReal B ≠ 0 := (ENNReal.ofReal_pos.mpr hB0).ne'
  refine ⟨B, hB0, fun (n : ℕ) ↦ ?_⟩
  have hsub : {ω | B < H n ω} ⊆ {ω | ENNReal.ofReal B ≤ ‖H n ω‖ₑ ^ 4} := by
    intro ω hω
    have hH1 : 1 ≤ H n ω := hB1.trans hω.le
    have hp : H n ω ≤ (H n ω) ^ 4 := by
      simpa only [pow_one] using pow_le_pow_right₀ hH1 (by norm_num : 1 ≤ 4)
    change ENNReal.ofReal B ≤ ‖H n ω‖ₑ ^ 4
    rw [← enorm_pow, Real.enorm_eq_ofReal_abs, abs_of_nonneg (pow_nonneg (h0 n ω) _)]
    exact ENNReal.ofReal_le_ofReal (hω.le.trans hp)
  calc P {ω | B < H n ω}
      ≤ P {ω | ENNReal.ofReal B ≤ ‖H n ω‖ₑ ^ 4} := measure_mono hsub
    _ ≤ (∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P) / ENNReal.ofReal B :=
      meas_ge_le_lintegral_div ((hm n).enorm.pow_const 4).aemeasurable
        hBne ENNReal.ofReal_ne_top
    _ ≤ D / ENNReal.ofReal B := by
      gcongr
      exact hfour n
    _ ≤ ENNReal.ofReal η := by
      rw [ENNReal.div_le_iff hBne ENNReal.ofReal_ne_top,
        ← ENNReal.ofReal_mul hη.le, ← ENNReal.ofReal_toReal hD]
      apply ENNReal.ofReal_le_ofReal
      have hb : D.toReal / η ≤ B := le_max_right _ _
      have h := (div_le_iff₀ hη).mp hb
      linarith

end EnvelopeTail

section Radius

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The radius $\sum_\alpha (B^2/n)^{1/(2|k_\alpha|)}$, where $|k_\alpha| = \sum_j k_{\alpha j}$
is the degree of the half monomial of chart $\alpha$. Its term for $\alpha$ bounds the
sup-distance to the zero slice from a point of chart $\alpha$ where $n (u^{k_\alpha})^2 \le B^2$,
so the radius bounds this distance in every chart
(`SingularLearningTheory.ResolutionAtlas.le_chartRadius`). It tends to zero as $n \to \infty$
(`SingularLearningTheory.ResolutionAtlas.chartRadius_tendsto_zero`). -/
@[expose] noncomputable def chartRadius (B : ℝ) (n : ℕ) : ℝ :=
  ∑ α, (B ^ 2 / (n : ℝ)) ^ (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹)

theorem chartRadius_nonneg (B : ℝ) (n : ℕ) : 0 ≤ chartRadius R B n :=
  Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (div_nonneg (sq_nonneg B) (Nat.cast_nonneg n)) _

theorem le_chartRadius (B : ℝ) (n : ℕ) (α : R.ι) :
    (B ^ 2 / (n : ℝ)) ^ (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹)
      ≤ chartRadius R B n :=
  Finset.single_le_sum (f := fun a ↦
    (B ^ 2 / (n : ℝ)) ^ (((2 : ℝ) * ((∑ j, R.k a j : ℕ) : ℝ))⁻¹))
    (fun _ _ ↦ Real.rpow_nonneg
      (div_nonneg (sq_nonneg B) (Nat.cast_nonneg n)) _) (Finset.mem_univ α)

theorem chartRadius_tendsto_zero (B : ℝ) :
    Tendsto (chartRadius R B) atTop (𝓝 0) := by
  have hdiv : Tendsto (fun n : ℕ ↦ B ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (B ^ 2)
  have hterm : ∀ α : R.ι, Tendsto
      (fun n : ℕ ↦ (B ^ 2 / (n : ℝ)) ^
        (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹)) atTop (𝓝 0) := by
    intro α
    have hs : (∑ j, R.k α j) ≠ 0 := sum_k_ne_zero (R.active α)
    have hc : (0 : ℝ) < ((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹ := by positivity
    have h := (Real.continuousAt_rpow_const 0 _ (Or.inr hc.le)).tendsto.comp hdiv
    simpa only [Function.comp_def, Real.zero_rpow hc.ne'] using h
  unfold chartRadius
  convert tendsto_finsetSum (Finset.univ : Finset R.ι) (fun α _ ↦ hterm α) using 1
  simp only [Finset.sum_const_zero]

end Radius

section Approximation

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
  {Ψ : ℕ → Ω → C(Domain R, ℝ)} {H : ℕ → Ω → ℝ}
  {S : ℕ → Ω → (Fin d → ℝ) → ℝ} {ŵ : ℕ → Ω → Fin d → ℝ}

/-- The good-event argument controls both coordinates at once, hence yields a
joint approximation, not merely two marginal convergence statements. -/
private theorem mle_jointError_tendstoInMeasure
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ w ∈ W, K w < δ → ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hH0 : ∀ (n : ℕ) ω, 0 ≤ H n ω)
    (hNorm : ∀ (n : ℕ) ω, ‖Ψ n ω‖ ≤ H n ω)
    (hTail : ∀ η > 0, ∃ B > 0, ∀ n : ℕ, P {ω | B < H n ω} ≤ ENNReal.ofReal η)
    (hLip : ∀ η > 0, ∃ C > 0, ∀ n : ℕ,
      P {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
        |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} ≤ ENNReal.ofReal η)
    (hS : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ α (u : cube d (R.b α)),
      S n ω (R.g α u) = (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ n ω ⟨α, u⟩)
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W, S n ω (ŵ n ω) ≤ S n ω w)
    (hloc : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, (n : ℝ) * K (ŵ n ω) ≤ (H n ω) ^ 2) :
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω) - likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω),
        S n ω (ŵ n ω) + likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω))) atTop 0 := by
  classical
  rw [tendstoInMeasure_iff_norm]
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero]
  intro η hη
  rcases eq_or_ne η ⊤ with rfl | hηtop
  · exact ⟨0, fun n _ ↦ le_top⟩
  have hηR : 0 < η.toReal := ENNReal.toReal_pos hη.ne' hηtop
  obtain ⟨B, hB, hBTail⟩ := hTail (η.toReal / 2) (half_pos hηR)
  obtain ⟨C, hC, hCLip⟩ := hLip (η.toReal / 2) (half_pos hηR)
  have hdiv : Tendsto (fun n : ℕ ↦ B ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (B ^ 2)
  have hdiv4 : Tendsto (fun n : ℕ ↦ B ^ 2 / (4 * (n : ℝ))) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (B ^ 2 / 4) using 1
    funext n
    rw [div_div]
  have hω : Tendsto (fun (n : ℕ) ↦ C * chartRadius R B n) atTop (𝓝 0) := by
    simpa only [mul_zero] using (chartRadius_tendsto_zero R B).const_mul C
  have hErrG : Tendsto (fun (n : ℕ) ↦ mleErr B (C * chartRadius R B n)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mleErr_zero] using
      (continuous_mleErr B).continuousAt.tendsto.comp hω
  have hErrT : Tendsto
      (fun (n : ℕ) ↦ B * (C * chartRadius R B n) / 2 + (C * chartRadius R B n) ^ 2 / 4)
      atTop (𝓝 0) := by
    have hc : Continuous (fun x : ℝ ↦ B * x / 2 + x ^ 2 / 4) := by fun_prop
    simpa only [Function.comp_def, mul_zero, zero_pow two_ne_zero, zero_div, add_zero]
      using (hc.tendsto 0).comp hω
  have hevδ : ∀ᶠ n : ℕ in atTop, B ^ 2 / (n : ℝ) < δ :=
    hdiv.eventually (eventually_lt_nhds hδ)
  have hevlev : ∀ᶠ n : ℕ in atTop, ∀ α,
      B ^ 2 / (4 * (n : ℝ)) ≤ ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2 := by
    rw [eventually_all]
    intro α
    have hp : 0 < ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2 :=
      pow_pos (pow_pos (half_pos (R.b_pos α)) _) _
    exact (hdiv4.eventually (eventually_lt_nhds hp)).mono fun n hn ↦ hn.le
  have hevG := hErrG.eventually (eventually_lt_nhds (half_pos hε))
  have hevT := hErrT.eventually (eventually_lt_nhds (half_pos hε))
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop 1, hevδ, hevlev, hevG, hevT] with n hn hnδ hnlev hnG hnT
  have hincl : ∀ᵐ ω ∂P,
      ω ∈ {ω | ε ≤ ‖((n : ℝ) * K (ŵ n ω) - likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω),
        S n ω (ŵ n ω) + likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω)) - 0‖} →
      ω ∈ {ω | B < H n ω} ∪ {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
        |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} := by
    filter_upwards [hS n hn, hŵW n, hmin n, hloc n hn] with ω hSω hŵω hminω hlocω hbad
    by_contra hout
    change ¬ (B < H n ω ∨ ¬ ∀ α, ∀ u v : cube d (R.b α),
      |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v) at hout
    have hHB : H n ω ≤ B := not_lt.mp (not_or.mp hout).1
    have hL := not_not.mp (not_or.mp hout).2
    have hMB : positiveMax R (Ψ n ω) ≤ B :=
      (positiveMax_le_norm R _).trans ((hNorm n ω).trans hHB)
    have hlocB : (n : ℝ) * K (ŵ n ω) ≤ B ^ 2 :=
      hlocω.trans (pow_le_pow_left₀ (hH0 n ω) hHB 2)
    obtain ⟨hTω, hGω⟩ := mle_core_at_le R (by omega : 0 < n) (Ψ n ω)
      hSω hcover hB.le (chartRadius_nonneg R B n) hC.le
      (le_chartRadius R B n) hnδ hnlev hL hŵω hminω hlocB hMB
    have hb : max
        |(n : ℝ) * K (ŵ n ω) - likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω)|
        |S n ω (ŵ n ω) + likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω)| < ε :=
      max_lt_iff.mpr ⟨(hGω.trans_lt hnG).trans (half_lt_self hε),
        (hTω.trans_lt hnT).trans (half_lt_self hε)⟩
    have hbad' : ε ≤ max
        |(n : ℝ) * K (ŵ n ω) - likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω)|
        |S n ω (ŵ n ω) + likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω)| := by
      simpa only [Set.mem_ofPred_eq, sub_zero, Prod.norm_mk, Real.norm_eq_abs] using hbad
    exact (not_le.mpr hb) hbad'
  calc P {ω | ε ≤ ‖((n : ℝ) * K (ŵ n ω) - likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω),
          S n ω (ŵ n ω) + likelihoodRewardSup R (resolvedZeroSet R) (Ψ n ω)) - 0‖}
      ≤ P ({ω | B < H n ω} ∪ {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
          |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v}) := measure_mono_ae hincl
    _ ≤ P {ω | B < H n ω} + P {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
          |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η.toReal / 2) + ENNReal.ofReal (η.toReal / 2) :=
      add_le_add (hBTail n) (hCLip n)
    _ = η := by
      rw [← ENNReal.ofReal_add (half_pos hηR).le (half_pos hηR).le, add_halves,
        ENNReal.ofReal_toReal hηtop]

end Approximation

section Assembly

variable {d : ℕ} {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [MeasurableSpace Ω'] {q : Measure X} [IsProbabilityMeasure q]
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {f : X → (Fin d → ℝ) → ℝ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- Maximum-likelihood asymptotics at s=4, for the given empirical process and the probability
space of its limit. -/
theorem _root_.SingularLearningTheory.MaximumLikelihood.maximumLikelihood_asymptotics_with_approx
    (I : FundamentalConditionI 4 q f K W) (L : R.AnalyticResolvedLikelihood 4 q f)
    (hf : Measurable (Function.uncurry f)) (hW : IsCompact W)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hcover : ∃ δ > 0, ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {Xs : ℕ → Ω → X} (hX : ∀ i, MeasurePreserving (Xs i) P q) (hIndep : iIndepFun Xs P)
    (E : EmpiricalProcessLimit q (fun x (u : Domain R) ↦ L.a u.1 x u.2) Xs P P')
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n : ℕ, Measurable (ŵ n))
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalLoss f Xs n ω (ŵ n ω) ≤ empiricalLoss f Xs n ω w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * K (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)
    let M := fun ω' ↦ likelihoodRewardSup R (resolvedZeroSet R) (E.Ψlim ω')
    Integrable M P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (M ω', -M ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', M ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) ∧
      TendstoInMeasure P (fun (n : ℕ) ω ↦
        (G n ω - likelihoodRewardSup R (resolvedZeroSet R) (E.Ψ n ω),
          T n ω + likelihoodRewardSup R (resolvedZeroSet R) (E.Ψ n ω))) atTop 0 := by
  dsimp only
  have hXm : ∀ i, Measurable (Xs i) := fun i ↦ (hX i).measurable
  have hlaw : ∀ i, P.map (Xs i) = q := fun i ↦ (hX i).map_eq
  obtain ⟨δ, hδ, hcoverδ⟩ := hcover
  obtain ⟨H, hHm, hH0, hNorm, ⟨D, hD, hfour⟩, henv⟩ :=
    exists_relative_envelope_fourth R I L hW (fun w ↦ hf.comp (measurable_id.prodMk measurable_const))
      hcont hδ hcoverδ hXm hlaw hIndep E
  have hloc := fun (n : ℕ) hn ↦ mle_localization_ae hK0 hH0 henv hw₀ hw₀K hŵW hmin
    (n := n) hn
  have hA := mle_aui_of_relative_envelope hK0 hH0 hD hfour henv hw₀ hw₀K hŵW hmin
  have htail := fun η hη ↦ uniform_tail_of_fourth_moment hHm hH0 hD hfour (η := η) hη
  have hlip := L.chartLipschitzTight hXm hlaw hIndep E.Ψ_ae_eq
  have hchart := fun (n : ℕ) hn ↦ sampleLoss_chart_ae R L.toResolvedLikelihood hXm hlaw E (n := n) hn
  have hminS : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) ≤
        (n : ℝ) * empiricalLoss f Xs n ω w := by
    intro n
    filter_upwards [hmin n] with ω hω w hw
    exact mul_le_mul_of_nonneg_left (hω w hw) (Nat.cast_nonneg n)
  have happrox := mle_jointError_tendstoInMeasure R
    (S := fun n ω w ↦ (n : ℝ) * empiricalLoss f Xs n ω w) hδ hcoverδ hH0 hNorm htail hlip
    hchart hŵW hminS (fun n hn ↦ (hloc n hn).mono fun ω hω ↦ hω.2.1)
  have hC : Continuous fun Ψ : C(Domain R, ℝ) ↦
      (likelihoodRewardSup R (resolvedZeroSet R) Ψ, -likelihoodRewardSup R (resolvedZeroSet R) Ψ) :=
    continuous_jointLikelihoodReward R _ (isCompact_resolvedZeroSet R) (resolvedZeroSet_nonempty R)
  have hreward := E.tendsto.continuous_comp hC
  have hKm : Measurable K := measurable_K_of_integral hf I.K_eq
  have hGm := fun (n : ℕ) ↦ measurable_scaled_generalization hKm hŵ n
  have hTm := fun (n : ℕ) ↦ measurable_scaled_training hf hXm hŵ n
  have happrox' : TendstoInMeasure P
      ((fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω), (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω))) -
        (fun (n : ℕ) ω ↦ (likelihoodRewardSup R (resolvedZeroSet R) (E.Ψ n ω),
          -likelihoodRewardSup R (resolvedZeroSet R) (E.Ψ n ω)))) atTop 0 := by
    convert happrox using 1
    funext n ω
    exact Prod.ext rfl (sub_neg_eq_add _ _)
  have hjoint := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω), (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)))
    (fun ω' ↦ (likelihoodRewardSup R (resolvedZeroSet R) (E.Ψlim ω'),
      -likelihoodRewardSup R (resolvedZeroSet R) (E.Ψlim ω')))
    hreward happrox' (fun (n : ℕ) ↦ ((hGm n).prodMk (hTm n)).aemeasurable)
  have hGdist := hjoint.continuous_comp (g := Prod.fst) continuous_fst
  have hTdist := hjoint.continuous_comp (g := Prod.snd) continuous_snd
  refine ⟨hA.1.integrable_limit hGdist,
    mle_eventually_integrable_of_aui hf I.K_eq hXm hŵ hA.1 hA.2,
    hjoint, hA.1.tendsto_integral hGdist, ?_, happrox⟩
  simpa only [Function.comp_def, integral_neg] using hA.2.tendsto_integral hTdist

/-- The original public API, obtained by forgetting the common-process approximation. -/
theorem _root_.SingularLearningTheory.MaximumLikelihood.maximumLikelihood_asymptotics
    (I : FundamentalConditionI 4 q f K W) (L : R.AnalyticResolvedLikelihood 4 q f)
    (hf : Measurable (Function.uncurry f)) (hW : IsCompact W)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hcover : ∃ δ > 0, ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {Xs : ℕ → Ω → X} (hX : ∀ i, MeasurePreserving (Xs i) P q) (hIndep : iIndepFun Xs P)
    (E : EmpiricalProcessLimit q (fun x (u : Domain R) ↦ L.a u.1 x u.2) Xs P P')
    (ŵ : ℕ → Ω → Fin d → ℝ) (hŵ : ∀ n : ℕ, Measurable (ŵ n))
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      empiricalLoss f Xs n ω (ŵ n ω) ≤ empiricalLoss f Xs n ω w) :
    let G := fun (n : ℕ) ω ↦ (n : ℝ) * K (ŵ n ω)
    let T := fun (n : ℕ) ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)
    let M := fun ω' ↦ likelihoodRewardSup R (resolvedZeroSet R) (E.Ψlim ω')
    Integrable M P' ∧
      (∀ᶠ n : ℕ in atTop, Integrable (G n) P ∧ Integrable (T n) P) ∧
      TendstoInDistribution (fun (n : ℕ) ω ↦ (G n ω, T n ω)) atTop
        (fun ω' ↦ (M ω', -M ω')) (fun _ ↦ P) P' ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, G n ω ∂P) atTop (𝓝 (∫ ω', M ω' ∂P')) ∧
      Tendsto (fun (n : ℕ) ↦ ∫ ω, T n ω ∂P) atTop (𝓝 (-(∫ ω', M ω' ∂P'))) := by
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := maximumLikelihood_asymptotics_with_approx R I L
    hf hW hK0 hcont hw₀ hw₀K hcover hX hIndep E ŵ hŵ hŵW hmin
  exact ⟨h1, h2, h3, h4, h5⟩

end Assembly

end SingularLearningTheory.ResolutionAtlas
