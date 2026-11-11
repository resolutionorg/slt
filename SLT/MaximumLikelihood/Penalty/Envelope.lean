/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Assembly
public import SLT.MaximumLikelihood.Penalty.Core
public import SLT.MaximumLikelihood.Penalty.Functionals
public import SLT.MeasureTheory.Function.AsympUnifIntegrable

/-!
# Localization and uniform integrability of penalized estimators

Let $\hat w$ minimize $nK_n(w) + a_n\sigma(w)$ over $W$, with $a_n \ge 0$, $|\sigma| \le S$ on $W$,
a zero $w_0$ of $K$ in $W$ and a relative envelope $\sqrt n\,|K_n - K| \le H_n\sqrt K$ on $W$.
This module bounds $nK(\hat w)$ and $nK_n(\hat w)$ by affine functions of $H_n^2$ and derives
asymptotic uniform integrability of the shifted errors from a uniform bound on $E[H_n^4]$. It
feeds the asymptotics of the estimator with a finite penalty.

## Main results

* `SingularLearningTheory.MaximumLikelihood.penalized_localization_ae`: almost surely
  $0 \le nK(\hat w) \le 2H_n^2 + 4a_nS$ and $|nK_n(\hat w)| \le 2nK(\hat w) + H_n^2$.
* `SingularLearningTheory.MaximumLikelihood.asympUnifIntegrable_affine_square`: an affine function of
  $H_n^2$ is asymptotically uniformly integrable when $E[H_n^4]$ is bounded.
* `SingularLearningTheory.MaximumLikelihood.finitePenalty_aui`: for eventually bounded $a_n$, the
  shifted errors $nK(\hat w) - a\sigma(\hat w)$ and $nK_n(\hat w) + a\sigma(\hat w)$ are
  asymptotically uniformly integrable.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.MaximumLikelihood

section Localization
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {K σ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {Kn : ℕ → Ω → (Fin d → ℝ) → ℝ} {H : ℕ → Ω → ℝ}
  {ŵ : ℕ → Ω → Fin d → ℝ} {aSeq : ℕ → ℝ}

/-- Penalized localization, retaining the universal event before substituting ŵ. -/
theorem penalized_localization_ae
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hH0 : ∀ n ω, 0 ≤ H n ω)
    (henv : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ w ∈ W,
      Real.sqrt n * |Kn n ω w - K w| ≤ Real.sqrt (K w) * H n ω)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (haSeq : ∀ n : ℕ, 0 ≤ aSeq n) {Sg : ℝ} (hSg : 0 ≤ Sg)
    (hσb : ∀ w ∈ W, |σ w| ≤ Sg)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      (n : ℝ) * Kn n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤
        (n : ℝ) * Kn n ω w + aSeq n * σ w)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, 0 ≤ (n : ℝ) * K (ŵ n ω) ∧
      (n : ℝ) * K (ŵ n ω) ≤ 2 * (H n ω) ^ 2 + 4 * aSeq n * Sg ∧
      |(n : ℝ) * Kn n ω (ŵ n ω)| ≤ 2 * ((n : ℝ) * K (ŵ n ω)) + (H n ω) ^ 2 := by
  filter_upwards [henv n hn, hŵW n, hmin n] with ω he hw hm
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hK : 0 ≤ K (ŵ n ω) := hK0 _ hw
  have hzero := he w₀ hw₀
  rw [hw₀K, Real.sqrt_zero, zero_mul, sub_zero] at hzero
  have hKn0 : Kn n ω w₀ = 0 := by
    have hab : |Kn n ω w₀| ≤ 0 := by nlinarith [abs_nonneg (Kn n ω w₀)]
    exact abs_nonpos_iff.mp hab
  have hcmp := hm w₀ hw₀
  rw [hKn0, mul_zero, zero_add] at hcmp
  have hσ0 := (abs_le.mp (hσb w₀ hw₀)).2
  have hσw := (abs_le.mp (hσb _ hw)).1
  have hq : (n : ℝ) * Kn n ω (ŵ n ω) ≤ 2 * aSeq n * Sg := by
    have h1 := mul_le_mul_of_nonneg_left hσ0 (haSeq n)
    have h2 := mul_le_mul_of_nonneg_left hσw (haSeq n)
    nlinarith only [hcmp, h1, h2]
  let x := Real.sqrt n * Real.sqrt (K (ŵ n ω))
  have hx0 : 0 ≤ x := mul_nonneg hsn.le (Real.sqrt_nonneg _)
  have hx2 : x ^ 2 = (n : ℝ) * K (ŵ n ω) := by
    dsimp [x]
    rw [mul_pow, Real.sq_sqrt hn'.le, Real.sq_sqrt hK]
  have hdev : |(n : ℝ) * Kn n ω (ŵ n ω) - x ^ 2| ≤ x * H n ω := by
    have h := mul_le_mul_of_nonneg_left (he _ hw) hsn.le
    rw [← mul_assoc, Real.mul_self_sqrt hn'.le] at h
    rw [hx2, ← mul_sub, abs_mul, abs_of_nonneg hn'.le]
    simpa only [x, mul_assoc] using h
  obtain ⟨hG, hT⟩ := penalized_localization_bounds hx0 (hH0 n ω) (haSeq n) hSg hdev hq
  rw [hx2] at hG hT
  exact ⟨mul_nonneg hn'.le hK, hG, hT⟩

end Localization

section AUI
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- An affine function of H² is AUI from the existing uniform fourth moment.
This replaces the donor's sixth-moment/3/2-moment detour. -/
theorem asympUnifIntegrable_affine_square {H : ℕ → Ω → ℝ}
    (hHm : ∀ n : ℕ, Measurable (H n)) {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (hfour : ∀ n : ℕ, ∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P ≤ D)
    (c₁ c₂ : ℝ) : AsympUnifIntegrable P (fun n ω ↦ c₁ * (H n ω) ^ 2 + c₂) := by
  apply asympUnifIntegrable_of_lintegral_sq_le
    (C := ENNReal.ofReal (2 * c₁ ^ 2) * D + ENNReal.ofReal (2 * c₂ ^ 2))
    (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hD, ENNReal.ofReal_ne_top⟩)
  refine Filter.Eventually.of_forall fun n ↦ ?_
  have hp : ∀ ω, ‖c₁ * (H n ω) ^ 2 + c₂‖ₑ ^ 2 ≤
      ENNReal.ofReal (2 * c₁ ^ 2) * ‖H n ω‖ₑ ^ 4 + ENNReal.ofReal (2 * c₂ ^ 2) := by
    intro ω
    have hreal : (c₁ * (H n ω) ^ 2 + c₂) ^ 2 ≤
        2 * c₁ ^ 2 * (H n ω) ^ 4 + 2 * c₂ ^ 2 := by
      nlinarith [sq_nonneg (c₁ * (H n ω) ^ 2 - c₂)]
    calc ‖c₁ * (H n ω) ^ 2 + c₂‖ₑ ^ 2
        = ENNReal.ofReal ((c₁ * (H n ω) ^ 2 + c₂) ^ 2) := by
            rw [← enorm_pow, Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
      _ ≤ ENNReal.ofReal (2 * c₁ ^ 2 * (H n ω) ^ 4 + 2 * c₂ ^ 2) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (2 * c₁ ^ 2) * ‖H n ω‖ₑ ^ 4 + ENNReal.ofReal (2 * c₂ ^ 2) := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (by positivity), ← enorm_pow,
            Real.enorm_eq_ofReal_abs, abs_of_nonneg (by positivity : 0 ≤ (H n ω) ^ 4)]
  calc ∫⁻ ω, ‖c₁ * (H n ω) ^ 2 + c₂‖ₑ ^ 2 ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (2 * c₁ ^ 2) * ‖H n ω‖ₑ ^ 4 +
          ENNReal.ofReal (2 * c₂ ^ 2)) ∂P := lintegral_mono hp
    _ = ENNReal.ofReal (2 * c₁ ^ 2) * (∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P) +
          ENNReal.ofReal (2 * c₂ ^ 2) := by
        rw [lintegral_add_left (show Measurable (fun ω : Ω ↦
          ENNReal.ofReal (2 * c₁ ^ 2) * ‖H n ω‖ₑ ^ 4) from
            measurable_const.mul ((hHm n).enorm.pow_const 4)),
          lintegral_const_mul _ ((hHm n).enorm.pow_const 4)]
        simp
    _ ≤ ENNReal.ofReal (2 * c₁ ^ 2) * D + ENNReal.ofReal (2 * c₂ ^ 2) := by
        gcongr
        exact hfour n

variable {d : ℕ} {K σ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {Kn : ℕ → Ω → (Fin d → ℝ) → ℝ} {H : ℕ → Ω → ℝ}
  {ŵ : ℕ → Ω → Fin d → ℝ} {aSeq : ℕ → ℝ}

/-- A bounded penalty sequence adds only a constant to the H² domination. -/
theorem finitePenalty_aui
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hH0 : ∀ n ω, 0 ≤ H n ω)
    (hHm : ∀ n : ℕ, Measurable (H n)) {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (hfour : ∀ n : ℕ, ∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P ≤ D)
    (henv : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ w ∈ W,
      Real.sqrt n * |Kn n ω w - K w| ≤ Real.sqrt (K w) * H n ω)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hŵW : ∀ n : ℕ, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (haSeq : ∀ n : ℕ, 0 ≤ aSeq n) {A Sg : ℝ} (hA : 0 ≤ A) (hSg : 0 ≤ Sg)
    (hcap : ∀ᶠ n : ℕ in atTop, aSeq n ≤ A) (hσb : ∀ w ∈ W, |σ w| ≤ Sg)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      (n : ℝ) * Kn n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤
        (n : ℝ) * Kn n ω w + aSeq n * σ w) (a : ℝ) :
    AsympUnifIntegrable P (fun n ω ↦ (n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω)) ∧
      AsympUnifIntegrable P (fun n ω ↦ (n : ℝ) * Kn n ω (ŵ n ω) + a * σ (ŵ n ω)) := by
  have hdom := asympUnifIntegrable_affine_square hHm hD hfour 5 ((8 * A + |a|) * Sg)
  have hbounds : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      |(n : ℝ) * K (ŵ n ω) - a * σ (ŵ n ω)| ≤ 5 * (H n ω) ^ 2 + (8 * A + |a|) * Sg ∧
      |(n : ℝ) * Kn n ω (ŵ n ω) + a * σ (ŵ n ω)| ≤ 5 * (H n ω) ^ 2 + (8 * A + |a|) * Sg := by
    filter_upwards [eventually_ge_atTop 1, hcap] with n hn hnA
    filter_upwards [penalized_localization_ae hK0 hH0 henv hw₀ hw₀K hŵW haSeq hSg hσb hmin hn,
      hŵW n] with ω hb hw
    have hσa : |a * σ (ŵ n ω)| ≤ |a| * Sg := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hσb _ hw) (abs_nonneg _)
    have hcap' := mul_le_mul_of_nonneg_right hnA hSg
    have hG := abs_sub ((n : ℝ) * K (ŵ n ω)) (a * σ (ŵ n ω))
    rw [abs_of_nonneg hb.1] at hG
    have hT := abs_add_le ((n : ℝ) * Kn n ω (ŵ n ω)) (a * σ (ŵ n ω))
    constructor <;> nlinarith [hb.2.1, hb.2.2, sq_nonneg (H n ω), mul_nonneg hA hSg]
  exact ⟨hdom.of_abs_le (hbounds.mono fun n hn ↦ hn.mono fun ω hω ↦ hω.1),
    hdom.of_abs_le (hbounds.mono fun n hn ↦ hn.mono fun ω hω ↦ hω.2)⟩

end AUI
end SingularLearningTheory.MaximumLikelihood
