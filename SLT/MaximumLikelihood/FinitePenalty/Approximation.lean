/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.FinitePenalty.Geometry
public import SLT.MaximumLikelihood.Penalty.Envelope
public import SLT.MaximumLikelihood.Penalty.Functionals
import SLT.MaximumLikelihood.Assembly

/-!
# The penalized estimator and the penalized reward

Let $\hat w_n$ minimize $S_n(w) + a_n\sigma(w)$ over $W$, where on every chart
$S_n(g_\alpha(u)) = n(u^{k_\alpha})^2 + \sqrt n\,u^{k_\alpha}\Psi_n(\alpha, u)$, as for $n$
times the empirical loss, and let the weights $a_n \ge 0$ converge to $a$. This module proves that
$nK(\hat w_n) - a\sigma(\hat w_n) - M_n$ and $S_n(\hat w_n) + a\sigma(\hat w_n) + M_n$ tend to
zero jointly in probability, where $M_n$ is the penalized reward
`SingularLearningTheory.ResolutionAtlas.penalizedLikelihoodRewardSup` of $\Psi_n$: the supremum of
$\max(0, -\Psi_n)^2/4 - a\sigma$ over the zeros of $K$ in the charts. It assumes that the charts
cover $\{K < \delta\}$, that $\sigma$ is bounded and Lipschitz on the charts, that $\Psi_n$ and
its Lipschitz constants are bounded in probability, and that
$nK(\hat w_n) \le 2H_n^2 + 4a_nS$ with $H_n \ge \|\Psi_n\|$ and $|\sigma| \le S$ on $W$. With the
convergence in law of $\Psi_n$, this gives the asymptotics of estimators with a penalty of finite
weight.

## Main results

* `SingularLearningTheory.MaximumLikelihood.finitePenalty_jointError_tendstoInMeasure`: the
  approximation in probability.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.MaximumLikelihood

variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {K φ σ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
  {Ψ : ℕ → Ω → C(ResolutionAtlas.Domain R, ℝ)} {H : ℕ → Ω → ℝ}
  {S : ℕ → Ω → (Fin d → ℝ) → ℝ} {ŵ : ℕ → Ω → Fin d → ℝ}

/-- Joint approximation at the final fixed weight a. -/
theorem finitePenalty_jointError_tendstoInMeasure
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ w ∈ W, K w < δ → ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hσ : Continuous (ResolutionAtlas.chartPenalty R σ))
    {Λ Sg : ℝ} (hΛ : 0 ≤ Λ) (hSg : 0 ≤ Sg)
    (hσLip : ∀ α (u v : cube d (R.b α)),
      |σ (R.g α u) - σ (R.g α v)| ≤ Λ * dist u v)
    (hσb : ∀ w ∈ W, |σ w| ≤ Sg)
    {aSeq : ℕ → ℝ} (haSeq : ∀ n, 0 ≤ aSeq n)
    {a A : ℝ} (hA : 0 ≤ A) (hcap : ∀ᶠ n : ℕ in atTop, aSeq n ≤ A)
    (ha : Tendsto aSeq atTop (𝓝 a))
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
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      S n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤ S n ω w + aSeq n * σ w)
    (hloc : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P,
      (n : ℝ) * K (ŵ n ω) ≤ 2 * (H n ω) ^ 2 + 4 * aSeq n * Sg) :
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦ ((n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω) -
          ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (Ψ n ω),
        S n ω (ŵ n ω) + a * σ (ŵ n ω) + ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (Ψ n ω)))
      atTop 0 := by
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
  let Q := Real.sqrt (2 * B ^ 2 + 4 * A * Sg)
  have hQ2 : Q ^ 2 = 2 * B ^ 2 + 4 * A * Sg := Real.sq_sqrt (by positivity)
  have hBQ : B ^ 2 ≤ Q ^ 2 := by rw [hQ2]; nlinarith [sq_nonneg B, mul_nonneg hA hSg]
  let errT := fun r : ℝ ↦ B * (C * r) / 2 + (C * r) ^ 2 / 4 + A * Λ * r
  let errG := fun r : ℝ ↦ mleErr' B (C * r) (B * (C * r) / 2 + 2 * (A * Λ * r)) +
    B * (C * r) + (C * r) ^ 2 / 4 + 3 * (A * Λ * r)
  have hcT : Continuous errT := by dsimp [errT]; fun_prop
  have hcG : Continuous errG := by dsimp [errG, mleErr']; fun_prop
  have hT0 : errT 0 = 0 := by simp [errT]
  have hG0 : errG 0 = 0 := by simp [errG, mleErr'_zero]
  have hdiv : Tendsto (fun n : ℕ ↦ Q ^ 2 / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat _
  have hdiv4 : Tendsto (fun n : ℕ ↦ B ^ 2 / (4 * (n : ℝ))) atTop (𝓝 0) := by
    convert tendsto_const_div_atTop_nhds_zero_nat (B ^ 2 / 4) using 1
    funext n
    rw [div_div]
  have hcorr : Tendsto (fun n : ℕ ↦ 2 * |aSeq n - a| * Sg) atTop (𝓝 0) := by
    convert (((ha.sub tendsto_const_nhds).abs.const_mul 2).mul_const Sg) using 1 <;> simp
  have hErrT : Tendsto (fun n : ℕ ↦ errT (ResolutionAtlas.chartRadius R Q n) + 2 * |aSeq n - a| *
      Sg)
      atTop (𝓝 0) := by
    have ht := (hcT.tendsto 0).comp (ResolutionAtlas.chartRadius_tendsto_zero R Q)
    rw [hT0] at ht
    simpa only [Function.comp_def, zero_add] using ht.add hcorr
  have hErrG : Tendsto (fun n : ℕ ↦ errG (ResolutionAtlas.chartRadius R Q n) + 2 * |aSeq n - a| *
      Sg)
      atTop (𝓝 0) := by
    have ht := (hcG.tendsto 0).comp (ResolutionAtlas.chartRadius_tendsto_zero R Q)
    rw [hG0] at ht
    simpa only [Function.comp_def, zero_add] using ht.add hcorr
  have hevδ := hdiv.eventually (eventually_lt_nhds hδ)
  have hevlev : ∀ᶠ n : ℕ in atTop, ∀ α,
      B ^ 2 / (4 * (n : ℝ)) ≤ ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2 := by
    rw [eventually_all]
    intro α
    have hp : 0 < ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2 :=
      pow_pos (pow_pos (half_pos (R.b_pos α)) _) _
    exact (hdiv4.eventually (eventually_lt_nhds hp)).mono fun n hn ↦ hn.le
  have hevG := hErrG.eventually (eventually_lt_nhds hε)
  have hevT := hErrT.eventually (eventually_lt_nhds hε)
  apply eventually_atTop.mp
  filter_upwards [eventually_ge_atTop 1, hcap, hevδ, hevlev, hevG, hevT]
    with n hn hnA hnδ hnlev hnG hnT
  have hincl : ∀ᵐ ω ∂P,
      ω ∈ {ω | ε ≤ ‖((n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω) -
        ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (Ψ n ω),
        S n ω (ŵ n ω) + a * σ (ŵ n ω) + ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (Ψ n ω))
            - 0‖} →
      ω ∈ {ω | B < H n ω} ∪ {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
        |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} := by
    filter_upwards [hS n hn, hŵW n, hmin n, hloc n hn] with ω hSω hŵω hminω hlocω hbad
    by_contra hout
    change ¬ (B < H n ω ∨ ¬ ∀ α, ∀ u v : cube d (R.b α),
      |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v) at hout
    have hHB : H n ω ≤ B := not_lt.mp (not_or.mp hout).1
    have hL := not_not.mp (not_or.mp hout).2
    have hMB : ResolutionAtlas.positiveMax R (Ψ n ω) ≤ B :=
      (ResolutionAtlas.positiveMax_le_norm R _).trans ((hNorm n ω).trans hHB)
    have hlocQ : (n : ℝ) * K (ŵ n ω) ≤ Q ^ 2 := by
      rw [hQ2]
      have hHsq := pow_le_pow_left₀ (hH0 n ω) hHB 2
      have hAsg := mul_le_mul_of_nonneg_right hnA hSg
      nlinarith only [hlocω, hHsq, hAsg]
    obtain ⟨hTω, hGω⟩ := ResolutionAtlas.finitePenalty_core_at R (by omega : 0 < n) (Ψ n ω)
      hSω hcover hσ hΛ hσLip (haSeq n) hB.le (ResolutionAtlas.chartRadius_nonneg R Q n) hC.le hBQ
      (ResolutionAtlas.le_chartRadius R Q n) hnδ hnlev hL hŵω hminω hlocQ hMB
    have hc : aSeq n * Λ * ResolutionAtlas.chartRadius R Q n ≤ A * Λ * ResolutionAtlas.chartRadius R
        Q n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnA hΛ)
          (ResolutionAtlas.chartRadius_nonneg R Q n)
    have hT' : |S n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) +
        ResolutionAtlas.penalizedLikelihoodRewardSup R σ (aSeq n) (Ψ n ω)| ≤ errT
            (ResolutionAtlas.chartRadius R Q n) := by
      dsimp [errT]
      linarith
    have hmerr := mleErr'_mono hB.le
      (mul_nonneg hC.le (ResolutionAtlas.chartRadius_nonneg R Q n))
      (show 0 ≤ B * (C * ResolutionAtlas.chartRadius R Q n) / 2 +
        2 * (aSeq n * Λ * ResolutionAtlas.chartRadius R Q n) by
          have := haSeq n
          have := ResolutionAtlas.chartRadius_nonneg R Q n
          positivity)
      (le_refl B) (le_refl (C * ResolutionAtlas.chartRadius R Q n))
      (show B * (C * ResolutionAtlas.chartRadius R Q n) / 2 + 2 *
          (aSeq n * Λ * ResolutionAtlas.chartRadius R Q n) ≤
        B * (C * ResolutionAtlas.chartRadius R Q n) / 2 + 2 *
            (A * Λ * ResolutionAtlas.chartRadius R Q n) by linarith)
    have hG' : |(n : ℝ) * K (ŵ n ω) - aSeq n * σ (ŵ n ω) -
        ResolutionAtlas.penalizedLikelihoodRewardSup R σ (aSeq n) (Ψ n ω)| ≤ errG
            (ResolutionAtlas.chartRadius R Q n) := by
      dsimp [errG]
      linarith
    obtain ⟨hGc, hTc⟩ := ResolutionAtlas.finitePenalty_weight_correction R hσ hσb hŵω (Ψ n ω)
      a (aSeq n) ((n : ℝ) * K (ŵ n ω)) (S n ω (ŵ n ω))
    have hb : max
        |(n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω) - ResolutionAtlas.penalizedLikelihoodRewardSup R σ a
            (Ψ n ω)|
        |S n ω (ŵ n ω) + a * σ (ŵ n ω) + ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (Ψ n ω)|
            < ε := by
      exact max_lt_iff.mpr ⟨(hGc.trans (add_le_add hG' le_rfl)).trans_lt hnG,
        (hTc.trans (add_le_add hT' le_rfl)).trans_lt hnT⟩
    have hbad' : ε ≤ max
        |(n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω) - ResolutionAtlas.penalizedLikelihoodRewardSup R σ a
            (Ψ n ω)|
        |S n ω (ŵ n ω) + a * σ (ŵ n ω) + ResolutionAtlas.penalizedLikelihoodRewardSup R σ a
            (Ψ n ω)| := by
      simpa only [Set.mem_ofPred_eq, sub_zero, Prod.norm_mk, Real.norm_eq_abs] using hbad
    exact (not_le.mpr hb) hbad'
  calc P {ω | ε ≤ ‖((n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω) -
          ResolutionAtlas.penalizedLikelihoodRewardSup R σ a (Ψ n ω),
          S n ω (ŵ n ω) + a * σ (ŵ n ω) + ResolutionAtlas.penalizedLikelihoodRewardSup R σ a
              (Ψ n ω)) - 0‖}
      ≤ P ({ω | B < H n ω} ∪ {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
          |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v}) := measure_mono_ae hincl
    _ ≤ P {ω | B < H n ω} + P {ω | ¬ ∀ α, ∀ u v : cube d (R.b α),
          |Ψ n ω ⟨α, u⟩ - Ψ n ω ⟨α, v⟩| ≤ C * dist u v} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η.toReal / 2) + ENNReal.ofReal (η.toReal / 2) :=
      add_le_add (hBTail n) (hCLip n)
    _ = η := by
      rw [← ENNReal.ofReal_add (half_pos hηR).le (half_pos hηR).le, add_halves,
        ENNReal.ofReal_toReal hηtop]

end SingularLearningTheory.MaximumLikelihood
