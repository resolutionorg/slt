/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Resolution
public import SLT.SingularIntegrals.Transforms
public import SLT.FreeEnergy.TechnicalResults
public import SLT.SingularIntegrals.NormalCrossing
import SLT.Analysis.SpecialFunctions.Pow.LogBounds

/-!
# The deterministic free energy formula

Formalises [Hit26, Section 3.3.1] and
[Hit26, Theorem 3.3.9], given a resolution atlas.

| Thesis | Lean |
| --- | --- |
| `Z_α(n)` ([Hit26, Section 3.3.1]) | `chartIntegral` |
| [Hit26, Equation (3.3.5)] | `integral_localized_eq_sum` |
| the tail estimate for `Z₀^{≥ε}(n)` | `integral_tail_le` |
| `0 ≤ Z_α(n) ≤ C (log n)^{m_α - 1} / n^{λ_α}` | `chartIntegral_le` |
| `n^λ Z_α(n) ≤ C (log n)^{m-1}` for every chart | `rpow_mul_chartIntegral_le` |
| [Hit26, Theorem 3.3.9], upper bound on `laplaceIntegral` | |
| | `rpow_mul_normalizedPartitionFunction_le` |
| [Hit26, Theorem 3.3.9], lower bound on `laplaceIntegral` | |
| (`NondegenerateResolutionAtlas`) | `rpow_mul_normalizedPartitionFunction_ge` |
| [Hit26, Theorem 3.3.9], thesis form | |
| `F₀ = λ log n − (m−1) log log n + O(1)` (`NondegenerateResolutionAtlas`) | |
| | `deterministic_free_energy` |

All names live in the `ResolutionAtlas` namespace.

## What is proved

[Hit26]'s argument establishes `0 ≤ n^λ Z₀(n) / (log n)^{m-1} ≤ C`, an *upper* bound
on `Z₀(n)`, equivalently the lower bound `F₀(n) ≥ λ log n − (m − 1) log log n − log C`
on the free energy; this is `rpow_mul_normalizedPartitionFunction_le`, for any atlas. The
matching lower bound on `Z₀(n)`, which the theorem's `O(1)` asserts, is not proved in the
thesis and is false for an arbitrary atlas;
it holds for a `NondegenerateResolutionAtlas` (positive essential trace mass), which is
`rpow_mul_normalizedPartitionFunction_ge`. The ambient hypotheses (`W` measurable, `K`
measurable and `≥ 0` on `W`, `φ ≥ 0` and integrable on `W`) hold in [Hit26]'s setting.
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

open SingularLearningTheory.NormalCrossing

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The chart integral `Z_α(n) = ∫_{[0,b_α]^d} e^{-nβ u^{2k_α}} u^{h_α} φ̃_α(u) du` of
[Hit26, Section 3.3.1]. -/
@[expose] noncomputable def chartIntegral (α : R.ι) (β n : ℝ) : ℝ :=
  ∫ u in cube d (R.b α),
    Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) * ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)

/-- The transport identity [Hit26, Equation (3.3.5)] for a
general measurable integrand `F` on parameter space that is bounded on every chart image:
`∫_W F χ φ = Σ_α ∫_{[0,b_α]^d} (F ∘ g_α) u^{h_α} φ̃_α`, together with the integrability of
the left-hand side. The ambient hypotheses are not part of the atlas: `W` measurable and
`φ ≥ 0` on `W` are needed because `ENNReal.ofReal` truncates a signed density. Used with
`F = e^{-nβK}` (deterministic) and `F = e^{-nβK_n(ω, ·)}` ([Hit26,
Theorem 5.2.6]). -/
theorem integral_smul_localized_eq_sum_of_bounded
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) {F : (Fin d → ℝ) → E} (hFm : StronglyMeasurable F)
    (hFb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α), ‖F (R.g α u)‖ ≤ C) :
    IntegrableOn (fun w ↦ (R.χ w * φ w) • F w) W ∧
      ∫ w in W, (R.χ w * φ w) • F w
        = ∑ α, ∫ u in cube d (R.b α),
            ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u) • F (R.g α u) := by
  have hcube : ∀ α, MeasurableSet (cube d (R.b α)) := fun _ ↦
    measurableSet_Icc
  have hcpt : ∀ α, IsCompact (cube d (R.b α)) := fun _ ↦ isCompact_Icc
  have hρc : ∀ α, ContinuousOn (fun u : Fin d → ℝ ↦ (∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)
      (cube d (R.b α)) := fun α ↦
    (continuousOn_finsetProd _ fun j _ ↦
      ((Real.continuous_rpow_const (Nat.cast_nonneg _)).comp (continuous_apply j)).continuousOn).mul
      (R.weight_continuousOn α)
  have hρm : ∀ α, AEMeasurable
      (fun u : Fin d → ℝ ↦ ENNReal.ofReal ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u))
      (volume.restrict (cube d (R.b α))) := fun α ↦
    ((hρc α).aemeasurable (hcube α)).ennreal_ofReal
  have hGeq : ∀ α, (fun u : Fin d → ℝ ↦
      (ENNReal.ofReal ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)).toReal • F (R.g α u))
        =ᵐ[volume.restrict (cube d (R.b α))] fun u ↦
      ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u) • F (R.g α u) := by
    intro α
    filter_upwards [ae_restrict_mem (hcube α)] with u hu
    have hρ0 : 0 ≤ (∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u :=
      mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
        (R.weight_nonneg α u hu)
    rw [ENNReal.toReal_ofReal hρ0]
  have hWeq : (fun w ↦ (ENNReal.ofReal (R.χ w * φ w)).toReal • F w)
      =ᵐ[volume.restrict W] fun w ↦ (R.χ w * φ w) • F w := by
    filter_upwards [ae_restrict_mem hW] with w hw
    rw [ENNReal.toReal_ofReal (mul_nonneg (R.χ_nonneg w) (hφ w hw))]
  have hχφ : AEMeasurable (fun w ↦ ENNReal.ofReal (R.χ w * φ w)) (volume.restrict W) :=
    (R.χ_measurable.aemeasurable.mul hφi.aemeasurable).ennreal_ofReal
  -- integrability of `(F ∘ g_α) u^h φ̃_α` on the chart cube
  have hGint : ∀ α, IntegrableOn
      (fun u ↦ ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u) • F (R.g α u)) (cube d (R.b α)) := by
    intro α
    obtain ⟨C, hC⟩ := hFb α
    refine ((hρc α).integrableOn_compact (hcpt α)).smul_bdd C
      ((hFm.comp_measurable (R.g_measurable α)).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem (hcube α)] with u hu
    exact hC u hu
  have h3 : ∀ α, Integrable F (Measure.map (R.g α) ((volume.restrict (cube d (R.b α))).withDensity
      fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u))) := by
    intro α
    rw [integrable_map_measure hFm.aestronglyMeasurable (R.g_measurable α).aemeasurable,
      integrable_withDensity_iff_integrable_smul₀' (hρm α)
        (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    exact (hGint α).congr (hGeq α).symm
  have h2 : ∀ α, ∫ w, F w ∂(Measure.map (R.g α) ((volume.restrict (cube d (R.b α))).withDensity
      fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)))
        = ∫ u in cube d (R.b α), ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u) • F (R.g α u) := by
    intro α
    rw [integral_map (R.g_measurable α).aemeasurable hFm.aestronglyMeasurable,
      integral_withDensity_eq_integral_toReal_smul₀ (hρm α)
        (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    exact integral_congr_ae (hGeq α)
  have hint : Integrable F
      ((volume.restrict W).withDensity fun w ↦ ENNReal.ofReal (R.χ w * φ w)) := by
    rw [R.transport, integrable_finsetSum_measure]
    exact fun α _ ↦ h3 α
  refine ⟨?_, ?_⟩
  · have := (integrable_withDensity_iff_integrable_smul₀' hχφ
      (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)).mp hint
    exact this.congr hWeq
  calc ∫ w in W, (R.χ w * φ w) • F w
      = ∫ w, F w ∂((volume.restrict W).withDensity fun w ↦ ENNReal.ofReal (R.χ w * φ w)) := by
        rw [integral_withDensity_eq_integral_toReal_smul₀ hχφ
          (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
        exact (integral_congr_ae hWeq).symm
    _ = ∫ w, F w ∂(∑ α, Measure.map (R.g α) ((volume.restrict (cube d (R.b α))).withDensity
          fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u))) := by
        rw [R.transport]
    _ = ∑ α, ∫ w, F w ∂(Measure.map (R.g α) ((volume.restrict (cube d (R.b α))).withDensity
          fun u ↦ ENNReal.ofReal ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u))) :=
        integral_finsetSum_measure fun α _ ↦ h3 α
    _ = _ := Finset.sum_congr rfl fun α _ ↦ h2 α

/-- Real-valued form of the atlas transport identity. -/
theorem integral_localized_eq_sum_of_bounded (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) {F : (Fin d → ℝ) → ℝ} (hFm : Measurable F)
    (hFb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α), |F (R.g α u)| ≤ C) :
    IntegrableOn (fun w ↦ F w * (R.χ w * φ w)) W ∧
      ∫ w in W, F w * (R.χ w * φ w)
        = ∑ α, ∫ u in cube d (R.b α),
            F (R.g α u) * ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u) := by
  simpa only [smul_eq_mul, mul_comm] using
    R.integral_smul_localized_eq_sum_of_bounded hW hφ hφi hFm.stronglyMeasurable hFb

/-- [Hit26, Equation (3.3.5)]: the localised part of
`Z₀(n)` is the sum of the chart integrals. `integral_localized_eq_sum_of_bounded` with
`F = e^{-nβK}`, which is `e^{-nβu^{2k_α}} ≤ 1` on the charts by `monomial`; `K` measurable
because the integrand lives on parameter space. -/
theorem integral_localized_eq_sum (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) (β n : ℝ) :
    ∫ w in W, Real.exp (-(n * β * K w)) * (R.χ w * φ w) = ∑ α, R.chartIntegral α β n := by
  have hFm : Measurable fun w ↦ Real.exp (-(n * β * K w)) :=
    Real.measurable_exp.comp (measurable_const.mul hKm).neg
  have hFb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α), |Real.exp (-(n * β * K (R.g α u)))| ≤ C := by
    intro α
    refine ⟨Real.exp (|n * β| * R.b α ^ (2 * ∑ j, R.k α j)), fun u hu ↦ ?_⟩
    rw [abs_of_pos (Real.exp_pos _), R.monomial α u hu]
    refine Real.exp_le_exp.mpr ?_
    have h1 : 0 ≤ ∏ j, u j ^ (2 * R.k α j) :=
      Finset.prod_nonneg fun j _ ↦ Even.pow_nonneg (even_two_mul _) _
    have h2 : ∏ j, u j ^ (2 * R.k α j) ≤ R.b α ^ (2 * ∑ j, R.k α j) :=
      Finset.prod_pow_le_of_mem_Icc (R.k α) fun j ↦ ⟨hu.1 j, hu.2 j⟩
    calc -(n * β * ∏ j, u j ^ (2 * R.k α j)) ≤ |n * β * ∏ j, u j ^ (2 * R.k α j)| :=
          neg_le_abs _
      _ = |n * β| * ∏ j, u j ^ (2 * R.k α j) := by rw [abs_mul, abs_of_nonneg h1]
      _ ≤ |n * β| * R.b α ^ (2 * ∑ j, R.k α j) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
  rw [(R.integral_localized_eq_sum_of_bounded hW hφ hφi hFm hFb).2]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  refine setIntegral_congr_fun measurableSet_Icc fun u hu ↦ ?_
  simp only [R.monomial α u hu]

/-- The tail: where `χ ≠ 1` we have `K ≥ δ`, so `e^{-nβK} ≤ e^{-nβδ}`. This is the estimate
`0 ≤ Z₀^{≥ε}(n) ≤ e^{-nβε}` of [Hit26] (with `∫_W φ = 1` for a probability density). -/
theorem integral_tail_le (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    {β n : ℝ} (hβ : 0 < β) (hn : 0 ≤ n) :
    ∫ w in W, Real.exp (-(n * β * K w)) * ((1 - R.χ w) * φ w)
      ≤ Real.exp (-(n * β * R.δ)) * ∫ w in W, φ w := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg ?_ (hφi.const_mul _) ?_
  · filter_upwards [ae_restrict_mem hW] with w hw
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) (hφ w hw))
  · filter_upwards [ae_restrict_mem hW] with w hw
    by_cases hlt : K w < R.δ
    · rw [R.χ_eq_one w hw hlt, sub_self, zero_mul, mul_zero]
      exact mul_nonneg (Real.exp_pos _).le (hφ w hw)
    · replace hlt := not_lt.mp hlt
      have hnβ : 0 ≤ n * β := mul_nonneg hn hβ.le
      have h1 : Real.exp (-(n * β * K w)) ≤ Real.exp (-(n * β * R.δ)) :=
        Real.exp_le_exp.2 (neg_le_neg (mul_le_mul_of_nonneg_left hlt hnβ))
      calc Real.exp (-(n * β * K w)) * ((1 - R.χ w) * φ w)
          ≤ Real.exp (-(n * β * R.δ)) * (1 * φ w) :=
            mul_le_mul h1
              (mul_le_mul_of_nonneg_right (sub_le_self _ (R.χ_nonneg w)) (hφ w hw))
              (mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) (hφ w hw)) (Real.exp_pos _).le
        _ = Real.exp (-(n * β * R.δ)) * φ w := by rw [one_mul]

/-- Each active coordinate has `ratio > 0`, so `λ_α > 0`. -/
theorem chartRlct_pos (α : R.ι) : 0 < R.chartRlct α := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (activeSet_nonempty R α) (R.ratio α)
  have hk : (0 : ℝ) < R.k α j := by exact_mod_cast (Finset.mem_filter.mp hj).2
  rw [chartRlct_eq_inf', hjeq, ratio]
  positivity

/-- `λ > 0`: the minimum of the positive `λ_α`. -/
theorem rlct_pos : 0 < R.rlct := by
  obtain ⟨α₀, -, hα₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty R.chartRlct
  rw [rlct, hα₀]; exact R.chartRlct_pos α₀

/-- Chart integrals are nonnegative. -/
theorem chartIntegral_nonneg (α : R.ι) (β n : ℝ) : 0 ≤ R.chartIntegral α β n := by
  unfold chartIntegral
  refine setIntegral_nonneg measurableSet_Icc fun u hu ↦ ?_
  refine mul_nonneg (Real.exp_pos _).le (mul_nonneg ?_ (R.weight_nonneg α u hu))
  exact Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _

/-- No thesis counterpart. A primary coordinate is active. -/
theorem k_pos_of_mem_primary {α : R.ι} {j : Fin d} (hj : j ∈ R.primary α) : 0 < R.k α j :=
  (Finset.mem_filter.mp (R.mem_primary.mp hj).1).2

/-- No thesis counterpart. A primary coordinate attains `λ_α`. -/
theorem ratio_eq_of_mem_primary {α : R.ι} {j : Fin d} (hj : j ∈ R.primary α) :
    (R.h α j + 1) / (2 * R.k α j) = R.chartRlct α :=
  (R.mem_primary.mp hj).2

/-- No thesis counterpart. A secondary coordinate has `2 k_j λ_α < h_j + 1`: either it is
inactive (`k_j = 0`), or its ratio exceeds the minimum. -/
theorem two_mul_k_mul_chartRlct_lt_of_notMem_primary {α : R.ι} {j : Fin d}
    (hj : j ∉ R.primary α) : 2 * R.k α j * R.chartRlct α < R.h α j + 1 := by
  by_cases hk : 0 < R.k α j
  · have hact : j ∈ R.activeSet α := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hk⟩
    have hle : R.chartRlct α ≤ R.ratio α j := Finset.inf'_le _ hact
    have hne : R.ratio α j ≠ R.chartRlct α := fun heq ↦ hj (R.mem_primary.mpr ⟨hact, heq⟩)
    have hlt : R.chartRlct α < (R.h α j + 1) / (2 * R.k α j) := lt_of_le_of_ne hle hne.symm
    rw [lt_div_iff₀ (by positivity)] at hlt
    linarith
  · have hk0 : R.k α j = 0 := by omega
    simp only [hk0, Nat.cast_zero, mul_zero, zero_mul]
    positivity

/-- No thesis counterpart. The secondary exponent `μ_j = h_j − 2 λ k_j` exceeds `−1` for
every non-primary coordinate (using `λ ≤ λ_α`). -/
theorem neg_one_lt_secondaryExponent {α : R.ι} {j : Fin d} (hj : j ∉ R.primary α) :
    -1 < R.secondaryExponent α j := by
  have h1 := R.two_mul_k_mul_chartRlct_lt_of_notMem_primary hj
  have h2 : 2 * R.k α j * R.rlct ≤ 2 * R.k α j * R.chartRlct α :=
    mul_le_mul_of_nonneg_left (R.rlct_le_chartRlct α) (by positivity)
  unfold secondaryExponent
  linarith

/-- A chart integral is bounded by `‖φ̃_α‖ Z^0(n)` for the normal-crossing data of the
chart: primary coordinates are those attaining `λ_α`, the rest are secondary. The
coordinates are permuted into the block form `(Fin m_α → ℝ) × (Fin (d - m_α) → ℝ)` that
`normalCrossingIntegral₀` uses; the permutation preserves Lebesgue measure and the cube. -/
theorem chartIntegral_le_blockIntegral₀ (α : R.ι) {β : ℝ} (hβ : 0 < β) :
    ∃ (r : ℕ) (k₁ : Fin (r + 1) → ℕ) (h₁ : Fin (r + 1) → ℝ) (k₂ : Fin (d - (r + 1)) → ℕ)
      (h₂ : Fin (d - (r + 1)) → ℝ) (M : ℝ),
      r + 1 = R.chartMult α ∧ (∀ j, 0 < k₁ j) ∧
      (∀ j, (h₁ j + 1) / (2 * k₁ j) = R.chartRlct α) ∧
      (∀ j, 2 * k₂ j * R.chartRlct α < h₂ j + 1) ∧ 0 ≤ M ∧
      ∀ n : ℝ, 0 ≤ n → R.chartIntegral α β n ≤ M * NormalCrossing.blockIntegral₀ k₁ h₁ k₂ h₂
          (R.b α) β 0 n := by
  obtain ⟨r, hr⟩ : ∃ r, r + 1 = R.chartMult α :=
    ⟨_, Nat.succ_pred_eq_of_pos (R.chartMult_pos α)⟩
  have hcardP : Fintype.card {j // j ∈ R.primary α} = r + 1 := by
    rw [Fintype.card_coe, hr]; rfl
  have hcardS : Fintype.card {j // j ∉ R.primary α} = d - (r + 1) := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardP]
  let eP : Fin (r + 1) ≃ {j // j ∈ R.primary α} := (Fintype.equivFinOfCardEq hcardP).symm
  let eS : Fin (d - (r + 1)) ≃ {j // j ∉ R.primary α} := (Fintype.equivFinOfCardEq hcardS).symm
  have hb := R.b_pos α
  have hcube : MeasurableSet (cube d (R.b α)) := measurableSet_Icc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (R.weight_continuousOn α)
  refine ⟨r, fun i ↦ R.k α (eP i), fun i ↦ (R.h α (eP i) : ℝ), fun i ↦ R.k α (eS i),
    fun i ↦ (R.h α (eS i) : ℝ), M, hr, fun i ↦ ?_, fun i ↦ ?_, fun i ↦ ?_, ?_, fun n hn ↦ ?_⟩
  · exact R.k_pos_of_mem_primary (eP i).2
  · exact R.ratio_eq_of_mem_primary (eP i).2
  · exact R.two_mul_k_mul_chartRlct_lt_of_notMem_primary (eS i).2
  · have h0 : (0 : Fin d → ℝ) ∈ cube d (R.b α) := by
      exact ⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩
    exact (norm_nonneg _).trans (hM 0 h0)
  · have hμ : ∀ j, -1 < (R.h α j : ℝ) := fun j ↦ neg_one_lt_zero.trans_le (Nat.cast_nonneg _)
    have hexp_nonneg : ∀ u : Fin d → ℝ, 0 ≤ Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) :=
      fun u ↦ (Real.exp_pos _).le
    have hexp_le : ∀ u : Fin d → ℝ, Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) ≤ 1 := by
      intro u
      refine Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg hn hβ.le) ?_))
      exact Finset.prod_nonneg fun j _ ↦ Even.pow_nonneg (even_two_mul _) _
    have hmeas : Measurable fun u : Fin d → ℝ ↦
        Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) := by fun_prop
    have hint : IntegrableOn (fun u : Fin d → ℝ ↦
        Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) * ∏ j, u j ^ (R.h α j : ℝ))
        (cube d (R.b α)) := by
      refine (integrableOn_cube_rpow hμ hb).bdd_mul (c := 1) hmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun u ↦ ?_)
      rw [Real.norm_of_nonneg (hexp_nonneg u)]
      exact hexp_le u
    rw [chartIntegral, ← integral_cube_eq_blockIntegral₀ eP eS (R.k α) (R.h α), ←
        integral_const_mul]
    refine integral_mono_of_nonneg ?_ (hint.const_mul M) ?_
    · refine ae_restrict_of_forall_mem hcube fun u hu ↦ ?_
      have hu' : ∀ j, 0 ≤ u j := fun j ↦ hu.1 j
      exact mul_nonneg (hexp_nonneg u) (mul_nonneg
        (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu' j) _) (R.weight_nonneg α u hu))
    · refine ae_restrict_of_forall_mem hcube fun u hu ↦ ?_
      have hu' : ∀ j, 0 ≤ u j := fun j ↦ hu.1 j
      have hw : R.weight α u ≤ M := (Real.le_norm_self _).trans (hM u hu)
      have hprod : 0 ≤ ∏ j, u j ^ (R.h α j : ℝ) :=
        Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu' j) _
      calc Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) *
            ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)
          ≤ Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) * ((∏ j, u j ^ (R.h α j : ℝ)) * M) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hw hprod) (hexp_nonneg u)
        _ = _ := by ring

/-- [Hit26, Section 3.3.1], the chart
estimate `0 ≤ Z_α(n) ≤ C (log n)^{m_α - 1} / n^{λ_α}` for `n ≥ 2` ([Wat09, Theorem 4.7]). -/
theorem chartIntegral_le (α : R.ι) {β : ℝ} (hβ : 0 < β) :
    ∃ C, ∀ n : ℝ, 2 ≤ n →
      R.chartIntegral α β n ≤ C * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α := by
  obtain ⟨r, k₁, h₁, k₂, h₂, M, hr, hk₁, hlam, hsec, hM, hle⟩ :=
      R.chartIntegral_le_blockIntegral₀ α hβ
  obtain ⟨a₂, ha₂, hZ⟩ := blockIntegral₀_upper_bound hk₁ hlam (R.chartRlct_pos α) hsec (R.b_pos α)
      hβ le_rfl
  refine ⟨M * a₂, fun n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) ≤ n := by linarith
  calc R.chartIntegral α β n
        ≤ M * NormalCrossing.blockIntegral₀ k₁ h₁ k₂ h₂ (R.b α) β 0 n := hle n hn0
    _ ≤ M * (a₂ * Real.log n ^ r / n ^ (R.chartRlct α + 0)) :=
        mul_le_mul_of_nonneg_left (hZ n hn) hM
    _ = M * a₂ * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α := by
        rw [add_zero, ← hr, Nat.add_sub_cancel]
        ring

/-- For every chart, `n^λ Z_α(n) ≤ C (log n)^{m-1}` for `n ≥ 2`: essential charts by [Wat09, Theorem
4.7] directly, non-essential ones by [Hit26, Lemma 5.1.2]. -/
theorem rpow_mul_chartIntegral_le (α : R.ι) {β : ℝ} (hβ : 0 < β) :
    ∃ C, ∀ n : ℝ, 2 ≤ n →
      n ^ R.rlct * R.chartIntegral α β n ≤ C * Real.log n ^ (R.mult - 1) := by
  obtain ⟨C₁, hC₁⟩ := R.chartIntegral_le α hβ
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rcases (R.rlct_le_chartRlct α).lt_or_eq with hlt | heq
  · -- `λ_α > λ`: `(log n)^{m_α - 1} / n^{λ_α} ≤ C (log n)^{m-1} / n^λ`
    obtain ⟨C₂, hC₂0, hC₂⟩ := Real.exists_log_pow_div_rpow_le (R.chartMult α - 1) (R.mult - 1)
      (lam := R.rlct) (delta := R.chartRlct α - R.rlct) R.rlct_pos (by linarith)
    refine ⟨C₁ * C₂, fun n hn ↦ ?_⟩
    have hn0 : 0 < n := by linarith
    have hnpos : 0 < n ^ R.rlct := Real.rpow_pos_of_pos hn0 _
    have h := hC₂ n hn
    rw [add_sub_cancel] at h
    have hC₁n := hC₁ n hn
    rcases le_or_gt 0 C₁ with hC₁0 | hC₁0
    · calc n ^ R.rlct * R.chartIntegral α β n
          ≤ n ^ R.rlct * (C₁ * (Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α)) := by
            gcongr; rw [mul_div_assoc] at hC₁n; exact hC₁n
        _ ≤ n ^ R.rlct * (C₁ * (C₂ * (Real.log n ^ (R.mult - 1) / n ^ R.rlct))) := by gcongr
        _ = C₁ * C₂ * Real.log n ^ (R.mult - 1) := by field_simp
    · -- `C₁ < 0` is impossible: the chart integral is nonnegative.
      have hZ0 := R.chartIntegral_nonneg α β n
      have : C₁ * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α < 0 := by
        have : 0 < Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α := by
          have := Real.log_pos (by linarith : (1 : ℝ) < n)
          positivity
        rw [mul_div_assoc]; exact mul_neg_of_neg_of_pos hC₁0 this
      linarith
  · -- `λ_α = λ`: `m_α ≤ m`
    obtain ⟨C₂, hC₂0, hC₂⟩ :=
      Real.exists_log_pow_le (Nat.sub_le_sub_right (R.chartMult_le_mult heq.symm) 1)
    refine ⟨|C₁| * C₂, fun n hn ↦ ?_⟩
    have hn0 : 0 < n := by linarith
    have hnpos : 0 < n ^ R.rlct := Real.rpow_pos_of_pos hn0 _
    have hC₁n := hC₁ n hn
    rw [← heq] at hC₁n
    have hlog : 0 ≤ Real.log n ^ (R.chartMult α - 1) := pow_nonneg (Real.log_nonneg (by linarith)) _
    calc n ^ R.rlct * R.chartIntegral α β n
        ≤ n ^ R.rlct * (C₁ * Real.log n ^ (R.chartMult α - 1) / n ^ R.rlct) := by gcongr
      _ = C₁ * Real.log n ^ (R.chartMult α - 1) := by field_simp
      _ ≤ |C₁| * Real.log n ^ (R.chartMult α - 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self C₁) hlog
      _ ≤ |C₁| * (C₂ * Real.log n ^ (R.mult - 1)) :=
          mul_le_mul_of_nonneg_left (hC₂ n hn) (abs_nonneg _)
      _ = |C₁| * C₂ * Real.log n ^ (R.mult - 1) := by ring

/-- [Hit26, Theorem 3.3.9], the half [Hit26] proves: there
is `C` with `n^λ Z₀(n) ≤ C (log n)^{m-1}` for all `n ≥ 2`, i.e.
`F₀(n) ≥ λ log n − (m − 1) log log n − log C`. Essential charts contribute
`O((log n)^{m-1} / n^λ)`; non-essential charts (`λ_α > λ`, or `λ_α = λ` and `m_α < m`)
and the tail contribute less, by [Hit26, Lemma 5.1.2]. -/
theorem rpow_mul_normalizedPartitionFunction_le (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hK : ∀ w ∈ W, 0 ≤ K w) {β : ℝ} (hβ : 0 < β) :
    ∃ C, ∀ n : ℝ, 2 ≤ n →
      n ^ R.rlct * normalizedPartitionFunction K φ W β n ≤ C * Real.log n ^ (R.mult - 1) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  choose Cα hCα using fun α ↦ R.rpow_mul_chartIntegral_le α hβ
  obtain ⟨Ct, hCt⟩ := Real.exists_rpow_mul_exp_neg_le (lam := R.rlct) (mul_pos hβ R.δ_pos)
  have hφ0 : 0 ≤ ∫ w in W, φ w :=
    setIntegral_nonneg hW hφ
  refine ⟨∑ α, Cα α + Ct * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1), fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by linarith
  have hnβ : 0 ≤ n * β := by positivity
  have hlogn : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos hn
  have hlogpow : Real.log 2 ^ (R.mult - 1) ≤ Real.log n ^ (R.mult - 1) :=
    pow_le_pow_left₀ hl2.le hlogn _
  -- split `Z₀(n)` into the localised part and the tail
  have hsplit : normalizedPartitionFunction K φ W β n
      = (∫ w in W, Real.exp (-(n * β * K w)) * (R.χ w * φ w)) +
        ∫ w in W, Real.exp (-(n * β * K w)) * ((1 - R.χ w) * φ w) := by
    rw [normalizedPartitionFunction, ← integral_add]
    · refine setIntegral_congr_fun hW fun w _ ↦ ?_
      ring
    · have h1 : Integrable (fun w ↦ (Real.exp (-(n * β * K w)) * R.χ w) * φ w)
          (volume.restrict W) := by
        refine hφi.bdd_mul (c := 1) ((Real.measurable_exp.comp
          ((hKm.const_mul _).neg)).mul R.χ_measurable).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem hW] with w hw
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (R.χ_nonneg w))]
        exact (mul_le_of_le_one_left (R.χ_nonneg w)
          (Real.exp_le_one_iff.mpr (by nlinarith [hK w hw]))).trans (R.χ_le_one w)
      exact h1.congr (Filter.Eventually.of_forall fun w ↦ by ring)
    · have h1 : Integrable (fun w ↦ (Real.exp (-(n * β * K w)) * (1 - R.χ w)) * φ w)
          (volume.restrict W) := by
        refine hφi.bdd_mul (c := 1) ((Real.measurable_exp.comp
          ((hKm.const_mul _).neg)).mul (measurable_const.sub R.χ_measurable)).aestronglyMeasurable
          ?_
        filter_upwards [ae_restrict_mem hW] with w hw
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
          (by linarith [R.χ_le_one w]))]
        exact (mul_le_of_le_one_left (by linarith [R.χ_le_one w])
          (Real.exp_le_one_iff.mpr (by nlinarith [hK w hw]))).trans (by linarith [R.χ_nonneg w])
      exact h1.congr (Filter.Eventually.of_forall fun w ↦ by ring)
  rw [hsplit, R.integral_localized_eq_sum hW hKm hφ hφi, mul_add, Finset.mul_sum, add_mul,
    Finset.sum_mul]
  have htail := R.integral_tail_le hW hφ hφi hβ hn0.le
  have hnpos : 0 < n ^ R.rlct := Real.rpow_pos_of_pos hn0 _
  gcongr ?_ + ?_
  · exact Finset.sum_le_sum fun α _ ↦ hCα α n hn
  · calc n ^ R.rlct * ∫ w in W, Real.exp (-(n * β * K w)) * ((1 - R.χ w) * φ w)
        ≤ n ^ R.rlct * (Real.exp (-(n * β * R.δ)) * ∫ w in W, φ w) := by gcongr
      _ = (n ^ R.rlct * Real.exp (-(β * R.δ * n))) * ∫ w in W, φ w := by ring_nf
      _ ≤ Ct * ∫ w in W, φ w := by
          gcongr
          exact hCt n (by linarith)
      _ = Ct * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) * Real.log 2 ^ (R.mult - 1) := by
          field_simp
      _ ≤ Ct * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) * Real.log n ^ (R.mult - 1) := by
          gcongr
          -- `Ct ≥ 0` since it bounds a positive quantity
          have := hCt 1 le_rfl
          have h1 : (0 : ℝ) < 1 ^ R.rlct * Real.exp (-(β * R.δ * 1)) := by positivity
          have hCt0 : 0 ≤ Ct := h1.le.trans this
          positivity

end ResolutionAtlas

/-! ## The lower bound, for a nondegenerate atlas -/

/-- No thesis counterpart. Translating a box `∏ [t_j, t_j + η]` back to the cube `[0, η]^d`. -/
private theorem integral_box_eq_integral_cube {d : ℕ} (g : (Fin d → ℝ) → ℝ) (t : Fin d → ℝ)
    (η : ℝ) :
    ∫ u in pi univ fun j ↦ Icc (t j) (t j + η), g u = ∫ u in cube d η, g (u + t) := by
  have hpre : (fun u : Fin d → ℝ ↦ u + t) ⁻¹' (pi univ fun j ↦ Icc (t j) (t j + η)) = cube d η := by
    ext u
    rw [mem_preimage, mem_cube]
    simp only [mem_univ_pi, Pi.add_apply, mem_Icc]
    constructor <;> intro H j <;> have := H j <;> constructor <;> linarith
  rw [← (measurePreserving_add_right volume t).setIntegral_preimage_emb
    (measurableEmbedding_addRight t), hpre]

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- No thesis counterpart. `Z₀(n) ≥ Z_α(n)` for every chart: the tail and the other charts
are nonnegative. -/
theorem chartIntegral_le_normalizedPartitionFunction (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) (hK : ∀ w ∈ W, 0 ≤ K w) (α : R.ι) {β n : ℝ}
    (hβ : 0 < β) (hn : 0 ≤ n) :
    R.chartIntegral α β n ≤ normalizedPartitionFunction K φ W β n := by
  have hexp : ∀ w ∈ W, Real.exp (-(n * β * K w)) ≤ 1 := fun w hw ↦
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (mul_nonneg hn hβ.le) (hK w hw)))
  have hsplit : normalizedPartitionFunction K φ W β n
      = (∫ w in W, Real.exp (-(n * β * K w)) * (R.χ w * φ w)) +
        ∫ w in W, Real.exp (-(n * β * K w)) * ((1 - R.χ w) * φ w) := by
    rw [normalizedPartitionFunction, ← integral_add]
    · exact setIntegral_congr_fun hW fun w _ ↦ by ring
    · have h1 : Integrable (fun w ↦ (Real.exp (-(n * β * K w)) * R.χ w) * φ w)
          (volume.restrict W) := by
        refine hφi.bdd_mul (c := 1) ((Real.measurable_exp.comp
          ((hKm.const_mul _).neg)).mul R.χ_measurable).aestronglyMeasurable ?_
        filter_upwards [ae_restrict_mem hW] with w hw
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (R.χ_nonneg w))]
        exact (mul_le_of_le_one_left (R.χ_nonneg w) (hexp w hw)).trans (R.χ_le_one w)
      exact h1.congr (Filter.Eventually.of_forall fun w ↦ by ring)
    · have h1 : Integrable (fun w ↦ (Real.exp (-(n * β * K w)) * (1 - R.χ w)) * φ w)
          (volume.restrict W) := by
        refine hφi.bdd_mul (c := 1) ((Real.measurable_exp.comp
          ((hKm.const_mul _).neg)).mul (measurable_const.sub R.χ_measurable)).aestronglyMeasurable
          ?_
        filter_upwards [ae_restrict_mem hW] with w hw
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le
          (by linarith [R.χ_le_one w]))]
        exact (mul_le_of_le_one_left (by linarith [R.χ_le_one w]) (hexp w hw)).trans
          (by linarith [R.χ_nonneg w])
      exact h1.congr (Filter.Eventually.of_forall fun w ↦ by ring)
  have htail : 0 ≤ ∫ w in W, Real.exp (-(n * β * K w)) * ((1 - R.χ w) * φ w) :=
    setIntegral_nonneg hW fun w hw ↦ mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (sub_nonneg.2 (R.χ_le_one w)) (hφ w hw))
  rw [hsplit, R.integral_localized_eq_sum hW hKm hφ hφi]
  calc R.chartIntegral α β n
      ≤ ∑ α', R.chartIntegral α' β n :=
        Finset.single_le_sum (fun α' _ ↦ R.chartIntegral_nonneg α' β n) (Finset.mem_univ α)
    _ ≤ _ := le_add_of_nonneg_right htail

/-- No thesis counterpart. Positive essential trace mass gives a point of the essential face
(primary coordinates `0`, secondary coordinates in `(0, b_α)`) where the weight is positive. -/
theorem exists_weight_pos_of_traceMass_pos {α : R.ι} (hT : 0 < R.essentialTraceMass α) :
    ∃ w₀ ∈ cube d (R.b α), (∀ j ∈ R.primary α, w₀ j = 0) ∧
      (∀ j ∉ R.primary α, w₀ j ∈ Ioo 0 (R.b α)) ∧ 0 < R.weight α w₀ := by
  rw [essentialTraceMass] at hT
  set F : (Fin d → ℝ) → ℝ := fun v ↦ (∏ j ∈ (R.primary α)ᶜ, v j ^ R.secondaryExponent α j) *
    R.weight α ((R.primary α)ᶜ.piecewise v 0) with hF
  have hex : ∃ v ∈ ocube d (R.b α), 0 < F v := by
    by_contra hcon
    push Not at hcon
    have h0 : ∫ v in ocube d (R.b α), F v ≤ 0 :=
      setIntegral_nonpos (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo) hcon
    rw [restrict_ocube_eq] at h0
    exact absurd hT (not_lt.mpr h0)
  obtain ⟨v, hv, hFv⟩ := hex
  have hv' : ∀ j, v j ∈ Ioo 0 (R.b α) := fun j ↦ hv j (mem_univ j)
  have hnot : ∀ j ∈ R.primary α, j ∉ (R.primary α)ᶜ := fun j hj ↦ by simpa using hj
  refine ⟨(R.primary α)ᶜ.piecewise v 0, mem_cube.2 fun j ↦ ?_, fun j hj ↦ ?_, fun j hj ↦ ?_, ?_⟩
  · by_cases hj : j ∈ R.primary α
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (hnot j hj)]
      exact ⟨le_rfl, (R.b_pos α).le⟩
    · rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_compl.mpr hj)]
      exact Ioo_subset_Icc_self (hv' j)
  · exact Finset.piecewise_eq_of_notMem _ _ _ (hnot j hj)
  · rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_compl.mpr hj)]
    exact hv' j
  · exact pos_of_mul_pos_right hFv
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv' j).1.le _)

/-- No thesis counterpart. The primary-only normal-crossing integral over `[0, η]^d`
(secondary exponents set to `0`) has the [Wat09, Theorem 4.7] lower bound
`a₁ (log n)^{m_α - 1} / n^{λ_α}`. -/
theorem primary_integral_lower_bound (α : R.ι) {η β' : ℝ} (hη : 0 < η) (hβ' : 0 < β') :
    ∃ a₁ > 0, ∀ n : ℝ, 1 < n →
      a₁ * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α ≤
        ∫ u in cube d η,
          Real.exp (-(n * β' * ∏ j, u j ^ (2 * if j ∈ R.primary α then R.k α j else 0))) *
            ∏ j, u j ^ ((if j ∈ R.primary α then R.h α j else 0 : ℕ) : ℝ) := by
  obtain ⟨r, hr⟩ : ∃ r, r + 1 = R.chartMult α :=
    ⟨_, Nat.succ_pred_eq_of_pos (R.chartMult_pos α)⟩
  have hcardP : Fintype.card {j // j ∈ R.primary α} = r + 1 := by
    rw [Fintype.card_coe, hr]; rfl
  have hcardS : Fintype.card {j // j ∉ R.primary α} = d - (r + 1) := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardP]
  let eP : Fin (r + 1) ≃ {j // j ∈ R.primary α} := (Fintype.equivFinOfCardEq hcardP).symm
  let eS : Fin (d - (r + 1)) ≃ {j // j ∉ R.primary α} := (Fintype.equivFinOfCardEq hcardS).symm
  set k' : Fin d → ℕ := fun j ↦ if j ∈ R.primary α then R.k α j else 0 with hk'
  set h' : Fin d → ℕ := fun j ↦ if j ∈ R.primary α then R.h α j else 0 with hh'
  have hk : ∀ i, 0 < k' (eP i) := fun i ↦ by
    simp only [hk', ite_eq_left (eP i).2]
    exact R.k_pos_of_mem_primary (eP i).2
  have hlam : ∀ i, ((h' (eP i) : ℝ) + 1) / (2 * k' (eP i)) = R.chartRlct α := fun i ↦ by
    simp only [hk', hh', ite_eq_left (eP i).2]
    exact R.ratio_eq_of_mem_primary (eP i).2
  have hsec : ∀ i, 2 * (k' (eS i) : ℝ) * R.chartRlct α < (h' (eS i) : ℝ) + 1 := fun i ↦ by
    simp [hk', hh', ite_eq_right (eS i).2]
  obtain ⟨a₁, ha₁, hZ⟩ := blockIntegral₀_lower_bound hk hlam (R.chartRlct_pos α) hsec hη hβ' le_rfl
  refine ⟨a₁, ha₁, fun n hn ↦ ?_⟩
  have h := hZ n hn
  rw [add_zero] at h
  rw [← hr, Nat.add_sub_cancel]
  calc a₁ * Real.log n ^ r / n ^ R.chartRlct α
      ≤ NormalCrossing.blockIntegral₀ (fun i ↦ k' (eP i)) (fun i ↦ (h' (eP i) : ℝ))
          (fun i ↦ k' (eS i))
          (fun i ↦ (h' (eS i) : ℝ)) η β' 0 n := h
    _ = _ := (integral_cube_eq_blockIntegral₀ eP eS k' h' η β' n).symm

/-- No thesis counterpart. The chart lower bound `c (log n)^{m_α - 1} / n^{λ_α} ≤ Z_α(n)` for a
chart with positive essential trace mass. -/
theorem le_chartIntegral_of_traceMass_pos {α : R.ι} (hT : 0 < R.essentialTraceMass α) {β : ℝ}
    (hβ : 0 < β) :
    ∃ c > 0, ∀ n : ℝ, 1 < n →
      c * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α ≤ R.chartIntegral α β n := by
  obtain ⟨w₀, hw₀, hw₀P, hw₀S, hw₀pos⟩ := R.exists_weight_pos_of_traceMass_pos hT
  have hb := R.b_pos α
  have hcube : MeasurableSet (cube d (R.b α)) := measurableSet_Icc
  -- the weight is at least `c₀ = φ̃_α(w₀) / 2` near `w₀`
  set c₀ : ℝ := R.weight α w₀ / 2 with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.continuousWithinAt_iff.mp (R.weight_continuousOn α w₀ hw₀) c₀ hc₀
  -- the box half-width `η`
  have hev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Ioi 0),
      η < δ₀ ∧ η ≤ R.b α ∧ ∀ j ∈ (R.primary α)ᶜ, η < w₀ j := by
    refine (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ₀)).and
      ((eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hb)).and ?_)
    rw [Filter.eventually_all_finset]
    intro j hj
    exact eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (hw₀S j (Finset.mem_compl.mp hj)).1)
  obtain ⟨η, ⟨hηδ, hηb, hηS⟩, hη⟩ := (hev.and eventually_mem_nhdsWithin).exists
  rw [mem_Ioi] at hη
  -- the box `∏ [t_j, t_j + η]`: `[0, η]` on primary, `[w₀_j - η, w₀_j]` on secondary coordinates
  set t : Fin d → ℝ := fun j ↦ if j ∈ R.primary α then 0 else w₀ j - η with ht_def
  set Box : Set (Fin d → ℝ) := pi univ fun j ↦ Icc (t j) (t j + η) with hBox_def
  have hBoxmeas : MeasurableSet Box := MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hBoxcpt : IsCompact Box := isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hBox_P : ∀ u ∈ Box, ∀ j ∈ R.primary α, u j ∈ Icc 0 η := fun u hu j hj ↦ by
    have := hu j (mem_univ j)
    simpa [ht_def, hj] using this
  have hBox_S : ∀ u ∈ Box, ∀ j ∉ R.primary α, u j ∈ Icc (w₀ j - η) (w₀ j) := fun u hu j hj ↦ by
    have := hu j (mem_univ j)
    simpa [ht_def, hj] using this
  have hBox_sub : Box ⊆ cube d (R.b α) := fun u hu ↦ mem_cube.2 fun j ↦ by
    by_cases hj : j ∈ R.primary α
    · obtain ⟨h1, h2⟩ := hBox_P u hu j hj
      exact ⟨h1, h2.trans hηb⟩
    · obtain ⟨h1, h2⟩ := hBox_S u hu j hj
      have := hηS j (Finset.mem_compl.mpr hj)
      have := (hw₀S j hj).2
      constructor <;> linarith
  have hBox_weight : ∀ u ∈ Box, c₀ ≤ R.weight α u := fun u hu ↦ by
    have hdist : dist u w₀ < δ₀ := by
      rw [dist_pi_lt_iff hδ₀]
      intro j
      rw [Real.dist_eq, abs_sub_lt_iff]
      by_cases hj : j ∈ R.primary α
      · obtain ⟨h1, h2⟩ := hBox_P u hu j hj
        rw [hw₀P j hj]
        constructor <;> linarith
      · obtain ⟨h1, h2⟩ := hBox_S u hu j hj
        constructor <;> linarith
    have := hδ (hBox_sub hu) hdist
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith
  -- the secondary constants
  set A₂ : ℝ := ∏ j ∈ (R.primary α)ᶜ, R.b α ^ (2 * R.k α j) with hA₂_def
  have hA₂ : 0 < A₂ := Finset.prod_pos fun j _ ↦ by positivity
  set c₂ : ℝ := ∏ j ∈ (R.primary α)ᶜ, (w₀ j - η) ^ (R.h α j : ℝ) with hc₂_def
  have hc₂ : 0 < c₂ := Finset.prod_pos fun j hj ↦
    Real.rpow_pos_of_pos (sub_pos.mpr (hηS j hj)) _
  -- the primary-only exponents
  set k' : Fin d → ℕ := fun j ↦ if j ∈ R.primary α then R.k α j else 0 with hk'
  set h' : Fin d → ℕ := fun j ↦ if j ∈ R.primary α then R.h α j else 0 with hh'
  have hprodk : ∀ u : Fin d → ℝ,
      ∏ j, u j ^ (2 * k' j) = ∏ j ∈ R.primary α, u j ^ (2 * R.k α j) := by
    intro u
    rw [← Finset.prod_mul_prod_compl (R.primary α)]
    have h1 : ∏ j ∈ R.primary α, u j ^ (2 * k' j) = ∏ j ∈ R.primary α, u j ^ (2 * R.k α j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [hk', hj]
    have h2 : ∏ j ∈ (R.primary α)ᶜ, u j ^ (2 * k' j) = 1 :=
      Finset.prod_eq_one fun j hj ↦ by simp [hk', Finset.mem_compl.mp hj]
    rw [h1, h2, mul_one]
  have hprodh : ∀ u : Fin d → ℝ,
      ∏ j, u j ^ (h' j : ℝ) = ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ) := by
    intro u
    rw [← Finset.prod_mul_prod_compl (R.primary α)]
    have h1 : ∏ j ∈ R.primary α, u j ^ (h' j : ℝ) = ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [hh', hj]
    have h2 : ∏ j ∈ (R.primary α)ᶜ, u j ^ (h' j : ℝ) = 1 :=
      Finset.prod_eq_one fun j hj ↦ by simp [hh', Finset.mem_compl.mp hj]
    rw [h1, h2, mul_one]
  obtain ⟨a₁, ha₁, hZ⟩ := R.primary_integral_lower_bound α hη (mul_pos hβ hA₂)
  refine ⟨c₂ * c₀ * a₁, by positivity, fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by linarith
  -- the chart integrand `G` and the primary-only integrand `g`
  set G : (Fin d → ℝ) → ℝ := fun u ↦
    Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) * ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)
    with hG
  set g : (Fin d → ℝ) → ℝ := fun u ↦
    Real.exp (-(n * (β * A₂) * ∏ j, u j ^ (2 * k' j))) * ∏ j, u j ^ (h' j : ℝ) with hg
  have hZn : a₁ * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α ≤ ∫ u in cube d η, g u :=
    hZ n hn
  have hGc : ContinuousOn G (cube d (R.b α)) :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _)).neg).continuousOn.mul
      ((continuousOn_finsetProd _ fun j _ ↦
        ((Real.continuous_rpow_const (Nat.cast_nonneg _)).comp
          (continuous_apply j)).continuousOn).mul (R.weight_continuousOn α))
  have hgc : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul
      (continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _)).neg).mul
      (continuous_finsetProd _ fun j _ ↦
        (Real.continuous_rpow_const (Nat.cast_nonneg _)).comp (continuous_apply j))
  have hGint : IntegrableOn G (cube d (R.b α)) :=
    hGc.integrableOn_compact isCompact_Icc
  have hGnonneg : 0 ≤ᵐ[volume.restrict (cube d (R.b α))] G := by
    refine ae_restrict_of_forall_mem hcube fun u hu ↦ ?_
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
      (R.weight_nonneg α u hu))
  -- `g` is invariant under the translation by `t`
  have hgt : ∀ u : Fin d → ℝ, g (u + t) = g u := by
    intro u
    have h1 : ∏ j ∈ R.primary α, (u + t) j ^ (2 * R.k α j)
        = ∏ j ∈ R.primary α, u j ^ (2 * R.k α j) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [ht_def, hj]
    have h2 : ∏ j ∈ R.primary α, (u + t) j ^ (R.h α j : ℝ)
        = ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ) :=
      Finset.prod_congr rfl fun j hj ↦ by simp [ht_def, hj]
    simp only [hg, hprodk, hprodh, h1, h2]
  -- pointwise on the box, `G ≥ c₂ c₀ g`
  have hpt : ∀ u ∈ Box, c₂ * c₀ * g u ≤ G u := by
    intro u hu
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ (hBox_sub hu).1 j
    have hub : ∀ j, u j ≤ R.b α := fun j ↦ (hBox_sub hu).2 j
    have hS : ∀ j ∈ (R.primary α)ᶜ, w₀ j - η ≤ u j := fun j hj ↦
      (hBox_S u hu j (Finset.mem_compl.mp hj)).1
    have hE : Real.exp (-(n * (β * A₂) * ∏ j, u j ^ (2 * k' j)))
        ≤ Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) := by
      rw [Real.exp_le_exp, neg_le_neg_iff, hprodk, ← Finset.prod_mul_prod_compl (R.primary α)]
      have hV : ∏ j ∈ (R.primary α)ᶜ, u j ^ (2 * R.k α j) ≤ A₂ :=
        Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hu0 j) _) fun j _ ↦
          pow_le_pow_left₀ (hu0 j) (hub j) _
      have hU : 0 ≤ ∏ j ∈ R.primary α, u j ^ (2 * R.k α j) :=
        Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu0 j) _
      have hnβ : 0 ≤ n * β := by positivity
      calc n * β * ((∏ j ∈ R.primary α, u j ^ (2 * R.k α j)) *
            ∏ j ∈ (R.primary α)ᶜ, u j ^ (2 * R.k α j))
          ≤ n * β * ((∏ j ∈ R.primary α, u j ^ (2 * R.k α j)) * A₂) := by gcongr
        _ = _ := by ring
    have hY : c₂ ≤ ∏ j ∈ (R.primary α)ᶜ, u j ^ (R.h α j : ℝ) :=
      Finset.prod_le_prod₀ (fun j hj ↦ Real.rpow_nonneg (sub_pos.mpr (hηS j hj)).le _) fun j hj ↦
        Real.rpow_le_rpow (sub_pos.mpr (hηS j hj)).le (hS j hj) (Nat.cast_nonneg _)
    have hX : 0 ≤ ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ) :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu0 j) _
    have hW := hBox_weight u hu
    simp only [hg, hG, hprodh]
    rw [← Finset.prod_mul_prod_compl (R.primary α) fun j ↦ u j ^ (R.h α j : ℝ)]
    calc c₂ * c₀ * (Real.exp (-(n * (β * A₂) * ∏ j, u j ^ (2 * k' j))) *
          ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ))
        = Real.exp (-(n * (β * A₂) * ∏ j, u j ^ (2 * k' j))) *
          ((∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ)) * c₂ * c₀) := by ring
      _ ≤ Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j))) *
          ((∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ)) *
            (∏ j ∈ (R.primary α)ᶜ, u j ^ (R.h α j : ℝ)) * R.weight α u) :=
        mul_le_mul hE (mul_le_mul (mul_le_mul_of_nonneg_left hY hX) hW hc₀.le
          (mul_nonneg hX (hc₂.le.trans hY))) (mul_nonneg (mul_nonneg hX hc₂.le) hc₀.le)
          (Real.exp_pos _).le
  have hgint : IntegrableOn (fun u ↦ c₂ * c₀ * g u) Box :=
    (continuous_const.mul hgc).continuousOn.integrableOn_compact hBoxcpt
  calc c₂ * c₀ * a₁ * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α
      = c₂ * c₀ * (a₁ * Real.log n ^ (R.chartMult α - 1) / n ^ R.chartRlct α) := by ring
    _ ≤ c₂ * c₀ * ∫ u in cube d η, g u := by gcongr
    _ = ∫ u in Box, c₂ * c₀ * g u := by
        rw [integral_const_mul, hBox_def, integral_box_eq_integral_cube]
        simp only [hgt]
    _ ≤ ∫ u in Box, G u := setIntegral_mono_on hgint (hGint.mono_set hBox_sub) hBoxmeas hpt
    _ ≤ ∫ u in cube d (R.b α), G u := setIntegral_mono_set hGint hGnonneg hBox_sub.eventuallyLE
    _ = R.chartIntegral α β n := rfl

end ResolutionAtlas

namespace NondegenerateResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : NondegenerateResolutionAtlas K φ W)

/-- [Hit26, Theorem 3.3.9], lower bound on `laplaceIntegral`: for a
nondegenerate atlas, `c (log n)^{m-1} ≤ n^λ Z₀(n)` for `n ≥ 2`. Not proved in [Hit26];
needs the positive essential trace mass. -/
theorem rpow_mul_normalizedPartitionFunction_ge (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) (hK : ∀ w ∈ W, 0 ≤ K w) {β : ℝ}
    (hβ : 0 < β) :
    ∃ c > 0, ∀ n : ℝ, 2 ≤ n →
      c * Real.log n ^ (R.mult - 1) ≤ n ^ R.rlct * normalizedPartitionFunction K φ W β n := by
  obtain ⟨α, ⟨hlam, hm⟩, hT⟩ := R.traceMass_pos
  obtain ⟨c, hc, hle⟩ := R.toResolutionAtlas.le_chartIntegral_of_traceMass_pos hT hβ
  refine ⟨c, hc, fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by linarith
  have hnpos : 0 < n ^ R.rlct := Real.rpow_pos_of_pos hn0 _
  have h1 := hle n (by linarith)
  rw [hlam, hm] at h1
  have h2 := R.toResolutionAtlas.chartIntegral_le_normalizedPartitionFunction hW hKm hφ hφi hK α hβ
    hn0.le
  calc c * Real.log n ^ (R.mult - 1)
      = n ^ R.rlct * (c * Real.log n ^ (R.mult - 1) / n ^ R.rlct) := by field_simp
    _ ≤ n ^ R.rlct * normalizedPartitionFunction K φ W β n := by
        gcongr
        exact h1.trans h2

/-- [Hit26, Theorem 3.3.9] in [Hit26]'s form: with
`F₀(n) = −log Z₀(n)`, `F₀(n) = λ log n − (m − 1) log log n + O(1)`, for a nondegenerate
atlas. The `O(1)` is a bound uniform over `n ≥ 3`. -/
theorem deterministic_free_energy (hW : MeasurableSet W) (hKm : Measurable K)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W) (hK : ∀ w ∈ W, 0 ≤ K w) {β : ℝ}
    (hβ : 0 < β) :
    ∃ C, ∀ n : ℝ, 3 ≤ n →
      |(-Real.log (normalizedPartitionFunction K φ W β n)) -
        (R.rlct * Real.log n - (R.mult - 1 : ℕ) * Real.log (Real.log n))| ≤ C := by
  obtain ⟨c, hc, hlow⟩ := R.rpow_mul_normalizedPartitionFunction_ge hW hKm hφ hφi hK hβ
  obtain ⟨C', hupp⟩ := R.toResolutionAtlas.rpow_mul_normalizedPartitionFunction_le hW hKm hφ hφi
    hK hβ
  refine ⟨max |Real.log c| |Real.log C'|, fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hL : 0 < Real.log n ^ (R.mult - 1) := pow_pos hlog _
  have hnl : 0 < n ^ R.rlct := Real.rpow_pos_of_pos hn0 _
  set Z := normalizedPartitionFunction K φ W β n with hZ
  have h1 := hlow n (by linarith)
  have h2 := hupp n (by linarith)
  have hZpos : 0 < Z := by
    have : 0 < n ^ R.rlct * Z := lt_of_lt_of_le (by positivity) h1
    exact pos_of_mul_pos_right this hnl.le
  have hC' : 0 < C' := by
    have : 0 < C' * Real.log n ^ (R.mult - 1) := lt_of_lt_of_le (by positivity) (h1.trans h2)
    exact pos_of_mul_pos_left this hL.le
  -- take logarithms
  have hlog1 := Real.log_le_log (by positivity) h1
  have hlog2 := Real.log_le_log (by positivity) h2
  rw [Real.log_mul hc.ne' hL.ne', Real.log_pow, Real.log_mul hnl.ne' hZpos.ne',
    Real.log_rpow hn0] at hlog1
  rw [Real.log_mul hnl.ne' hZpos.ne', Real.log_rpow hn0, Real.log_mul hC'.ne' hL.ne',
    Real.log_pow] at hlog2
  rw [abs_le]
  constructor
  · have := le_max_right |Real.log c| |Real.log C'|
    have := le_abs_self (Real.log C')
    linarith
  · have := le_max_left |Real.log c| |Real.log C'|
    have := neg_le_abs (Real.log c)
    linarith

end NondegenerateResolutionAtlas


end SingularLearningTheory
