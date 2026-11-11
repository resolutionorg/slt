/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.TechnicalResults
import SLT.Analysis.SpecialFunctions.Pow.LogBounds
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# The frozen-kernel approximation (qualitative [Wat09, Theorem 4.9])

[Hit26, Theorem 5.1.3] ([Wat09, Theorem 4.9]) estimates
`|Z^p(n, ξ, φ) − Y^p(n, ξ, φ)|` with an explicit rate `(log n)^{m-2} / n^{λ+p}`. The proof
of [Hit26, Theorem 5.2.6] only uses it in the qualitative form

    n^λ Z^0(n, ξ_n, φ) / (log n)^{m-1} − Y(ξ_n(0,·), φ(0,·)) → 0   in probability,

which is what this module proves deterministically, uniformly over `ξ` with bounded sup
norm and bounded Lipschitz constant in the primary coordinates, and without [Wat09, Corollary 4.3]
or the rate. The proof proceeds as follows:

1. *Freeze the primary variables.* With `ξ₀(v) = ξ(0, v)`, `φ₀(v) = φ(0, v)`, [Wat09, Theorem 4.6]
   in the form `integral_cube_monomial` (with `a = n v^{2k'}`) gives the exact identity
   `n^λ Z⁰(n, ξ₀, φ₀) / (log n)^r = γ ∫_v v^μ φ₀(v) ∫_t t^{λ-1} e^{-βt + β√t ξ₀(v)} R_n(t, v)`
   with `R_n(t, v) = (log (n A(v) / t) / log n)^r 𝟙(t < n A(v))`, `A(v) = b^{2|k|} v^{2k'}`,
   `μ = h' − 2λk'`. Since `R_n → 1` pointwise with an integrable dominator, the scalar error
   `E(n) = ∫_v v^μ ∫_t t^{λ-1} e^{-βt/2} |R_n(t, v) − 1|` tends to `0`, and
   `|n^λ Z⁰/(log n)^r − Y(ξ₀, φ₀)| ≤ γ P e^{βM²/2} E(n)` for `|ξ₀| ≤ M`, `|φ₀| ≤ P`.
2. *Unfreeze.* `|e^{cx} a − e^{cy} b| ≤ e^{cM} (|a − b| + c |b| |x − y|)` bounds
   `|Z⁰(n, ξ, φ) − Z⁰(n, ξ₀, φ₀)|` by shifted-weight integrals `T_j^q(n)` (the weight
   `u^{h + e_j}`), which are negligible by [Wat09, Theorem 4.7] applied to the shifted exponents.

| Thesis | Lean |
| --- | --- |
| `A(v)`, `R_n(t, v)` (no thesis counterpart) |
`SingularLearningTheory.NormalCrossing.secondaryScale`,
`SingularLearningTheory.NormalCrossing.logRatio` |
| `v^μ` with `μ = h' − 2λk'` (proof of [Wat09, Theorem 4.9]) |
`SingularLearningTheory.NormalCrossing.secondaryWeight` |
| `Y⁰(n, ξ, φ)` of [Hit26, Equation (5.1.2)], | `frozenLimit` |
| normalised by `(log n)^{m-1} / n^λ` | |
| the scalar error `E(n)` (no thesis counterpart) |
`SingularLearningTheory.NormalCrossing.frozenError`,
`SingularLearningTheory.NormalCrossing.frozenError_tendsto` |
| [Wat09, Theorem 4.9], frozen part, qualitative |
`SingularLearningTheory.NormalCrossing.abs_frozen_sub_frozenLimit_le` |
| [Wat09, Theorem 4.9], unfreezing part (mean value estimate) |
`SingularLearningTheory.NormalCrossing.abs_blockIntegral_sub_frozen_le` |
| `Z̃_j^p(n) ≤ …` in the proof of [Wat09, Theorem 4.9] |
`SingularLearningTheory.NormalCrossing.shifted_negligible` |
| [Wat09, Theorem 4.9], qualitative form | `uniform_approx` |
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

open SingularLearningTheory.NormalCrossing

theorem NormalCrossing.exists_small_exponent {m' : ℕ} {k' : Fin m' → ℕ} {h' : Fin m' → ℝ} {lam : ℝ}
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) :
    ∃ δ : ℝ, 0 < δ ∧ δ < lam ∧ ∀ j, 2 * k' j * δ < h' j - 2 * k' j * lam + 1 := by
  have h1 : ∀ᶠ δ : ℝ in 𝓝[>] 0, 0 < δ := self_mem_nhdsWithin
  have h2 : ∀ᶠ δ : ℝ in 𝓝[>] 0, δ < lam :=
    eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hlam0)
  have h3 : ∀ᶠ δ : ℝ in 𝓝[>] 0, ∀ j, 2 * k' j * δ < h' j - 2 * k' j * lam + 1 := by
    rw [eventually_all]
    intro j
    apply eventually_nhdsWithin_of_eventually_nhds
    have hc : Tendsto (fun δ : ℝ ↦ 2 * k' j * δ) (𝓝 0) (𝓝 0) := by
      have h : Continuous fun δ : ℝ ↦ 2 * (k' j : ℝ) * δ := continuous_const.mul continuous_id
      simpa using h.tendsto 0
    exact hc.eventually_lt_const (by linarith [hsec j])
  obtain ⟨δ, hδ0, hδlam, hδ⟩ := (h1.and (h2.and h3)).exists
  exact ⟨δ, hδ0, hδlam, hδ⟩

/-- `|log x|^r ≤ C (x^δ + x^{-δ})` for every `δ > 0`, with a constant depending only on
`δ` and `r`. No thesis counterpart. -/
theorem _root_.Real.exists_abs_log_pow_le {δ : ℝ} (hδ : 0 < δ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → |Real.log x| ^ r ≤ C * (x ^ δ + x ^ (-δ)) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    refine ⟨1, zero_le_one, fun x hx ↦ ?_⟩
    rw [pow_zero, one_mul]
    rcases le_total 1 x with h | h
    · have := Real.one_le_rpow h hδ.le
      have := Real.rpow_nonneg hx.le (-δ)
      linarith
    · have := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx h (by linarith : -δ ≤ 0)
      have := Real.rpow_nonneg hx.le δ
      linarith
  · have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have hε : 0 < δ / r := by positivity
    refine ⟨(2 / (δ / r)) ^ r, by positivity, fun x hx ↦ ?_⟩
    have := Real.abs_log_pow_le_rpow_add_rpow_neg hx hε r
    rwa [div_mul_cancel₀ _ hr', neg_mul, div_mul_cancel₀ _ hr'] at this

/-- `t^a e^{-βt/2}` is integrable on `(0, ∞)` for `a > -1`, `β > 0`. No thesis counterpart. -/
theorem _root_.integrableOn_rpow_mul_exp_neg_half {a β : ℝ} (ha : -1 < a) (hβ : 0 < β) :
    IntegrableOn (fun t : ℝ ↦ t ^ a * Real.exp (-(β * t / 2))) (Ioi 0) := by
  have := integrableOn_rpow_mul_exp_neg_mul_rpow ha one_pos (half_pos hβ)
  refine this.congr_fun (fun t _ ↦ ?_) measurableSet_Ioi
  simp only [Real.rpow_one]
  ring_nf

theorem NormalCrossing.exp_frozen_le {β t ξ M : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hξ : |ξ| ≤ M) :
    Real.exp (-(β * t) + β * Real.sqrt t * ξ)
      ≤ Real.exp (β * M ^ 2 / 2) * Real.exp (-(β * t / 2)) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hsq : ξ ^ 2 ≤ M ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hξ 2
  have habs := (abs_le.mp (Real.abs_sqrt_mul_le ht ξ)).2
  have h1 := mul_le_mul_of_nonneg_left habs hβ
  have h2 := mul_le_mul_of_nonneg_left hsq hβ
  nlinarith

section Frozen

variable {r m' : ℕ} (k : Fin (r + 1) → ℕ) (h : Fin (r + 1) → ℝ) (k' : Fin m' → ℕ)
  (h' : Fin m' → ℝ) (lam b β : ℝ)

/-- `A(v) = b^{2|k|} v^{2k'}`: the upper end of the `t`-range after [Wat09, Theorem 4.6] with
`a = n v^{2k'}` is `n A(v)`. -/
@[expose] noncomputable def NormalCrossing.secondaryScale (v : Fin m' → ℝ) : ℝ :=
  b ^ (2 * ∑ j, k j) * ∏ j, v j ^ (2 * k' j)

/-- `R_n(t, v) = (log (n A(v) / t) / log n)^r` for `0 < t < n A(v)`, else `0`. -/
@[expose] noncomputable def NormalCrossing.logRatio (n : ℝ) (v : Fin m' → ℝ) (t : ℝ) : ℝ :=
  (Ioo 0 (n * NormalCrossing.secondaryScale k k' b v)).indicator
    (fun t ↦ (Real.log (n * NormalCrossing.secondaryScale k k' b v / t) / Real.log n) ^ r) t

/-- The secondary weight `v^μ`, `μ_j = h'_j − 2 λ k'_j`. -/
@[expose] noncomputable def NormalCrossing.secondaryWeight (v : Fin m' → ℝ) : ℝ :=
  ∏ j, v j ^ (h' j - 2 * k' j * lam)

/-- The scalar error `E(n) = ∫_v v^μ ∫₀^∞ t^{λ-1} e^{-βt/2} |R_n(t, v) − 1| dt dv`. -/
@[expose] noncomputable def NormalCrossing.frozenError (n : ℝ) : ℝ :=
  ∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v *
    ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t -
        1|

/-- The limit functional `Y(ξ₀, φ₀) = γ ∫_v v^μ φ₀(v) ∫₀^∞ t^{λ-1} e^{-βt + β√t ξ₀(v)} dt dv`
([Hit26, Equation (5.2.5)] for one
chart, and `Y⁰(n, ξ, φ)` of [Hit26, Equation (5.1.2)] divided
by `(log n)^{m-1} / n^λ`). -/
@[expose] noncomputable def frozenLimit (ξ₀ φ₀ : (Fin m' → ℝ) → ℝ) : ℝ :=
  NormalCrossing.gammaConst k h lam b *
    ∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
    ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v)

variable {k h k' h' lam b β}

private theorem measurable_secondaryScale : Measurable (NormalCrossing.secondaryScale k k'
    b) := by
  unfold NormalCrossing.secondaryScale
  exact measurable_const.mul
    (Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _)

theorem NormalCrossing.measurable_secondaryWeight : Measurable
    (NormalCrossing.secondaryWeight k' h' lam) := by
  unfold NormalCrossing.secondaryWeight
  exact Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _

/-- `A(v) > 0` when every `v_j > 0`. -/
theorem NormalCrossing.secondaryScale_pos (hb : 0 < b) {v : Fin m' → ℝ} (hv : ∀ j, 0 < v j) :
    0 < NormalCrossing.secondaryScale k k' b v :=
  mul_pos (by positivity) (Finset.prod_pos fun j _ ↦ pow_pos (hv j) _)

/-- `A(v) ≤ b^{2|k| + 2|k'|}` on the cube. -/
private theorem secondaryScale_le (hb : 0 < b) {v : Fin m' → ℝ} (hv : ∀ j, v j ∈ Icc 0 b) :
    NormalCrossing.secondaryScale k k' b v ≤ b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j) :=
  mul_le_mul_of_nonneg_left (Finset.prod_pow_le_of_mem_Icc k' hv) (by positivity)

theorem NormalCrossing.secondaryWeight_nonneg {v : Fin m' → ℝ} (hv : ∀ j, 0 ≤ v j) :
    0 ≤ NormalCrossing.secondaryWeight k' h' lam v :=
  Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv j) _

/-- `R_n(·, v)` as a jointly measurable function of `(v, t)`. -/
theorem NormalCrossing.measurable_logRatio_uncurry (n : ℝ) :
    Measurable fun p : (Fin m' → ℝ) × ℝ ↦ NormalCrossing.logRatio k k' b n p.1 p.2 := by
  have hA : Measurable fun p : (Fin m' → ℝ) × ℝ ↦ n * NormalCrossing.secondaryScale k k' b p.1 :=
    (measurable_secondaryScale.comp measurable_fst).const_mul n
  have hS : MeasurableSet {p : (Fin m' → ℝ) × ℝ | p.2 ∈ Ioo 0
      (n * NormalCrossing.secondaryScale k k' b p.1)} := by
    have : {p : (Fin m' → ℝ) × ℝ | p.2 ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b p.1)}
        = {p | 0 < p.2} ∩ {p | p.2 < n * NormalCrossing.secondaryScale k k' b p.1} := Set.ext fun p
            ↦ Iff.rfl
    rw [this]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd hA)
  have : (fun p : (Fin m' → ℝ) × ℝ ↦ NormalCrossing.logRatio k k' b n p.1 p.2)
      = {p : (Fin m' → ℝ) × ℝ | p.2 ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b
          p.1)}.indicator
          fun p ↦ (Real.log (n * NormalCrossing.secondaryScale k k' b p.1 / p.2) / Real.log n) ^
              r := by
    ext p
    unfold NormalCrossing.logRatio
    by_cases hp : p.2 ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b p.1)
    · rw [indicator_of_mem hp, indicator_of_mem (show p ∈ {p : (Fin m' → ℝ) × ℝ |
        p.2 ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b p.1)} from hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (show p ∉ {p : (Fin m' → ℝ) × ℝ |
        p.2 ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b p.1)} from hp)]
  rw [this]
  exact (((Real.measurable_log.comp (hA.div measurable_snd)).div_const _).pow_const _).indicator hS

private theorem measurable_logRatio (n : ℝ) (v : Fin m' → ℝ) : Measurable
    (NormalCrossing.logRatio k k' b n v) := by
  unfold NormalCrossing.logRatio
  exact Measurable.indicator (by fun_prop) measurableSet_Ioo

/-- `R_n ≥ 0` for `n > 1`. -/
private theorem logRatio_nonneg {n : ℝ} (hn : 1 < n) (v : Fin m' → ℝ) (t : ℝ) :
    0 ≤ NormalCrossing.logRatio k k' b n v t := by
  unfold NormalCrossing.logRatio
  refine indicator_nonneg (fun t ht ↦ ?_) t
  exact pow_nonneg (div_nonneg (Real.log_div_nonneg_of_mem_Ioo ht) (Real.log_nonneg hn.le)) r

/-- `t^{λ-1} R_n(t, v) = 𝟙_{(0, nA)} t^{λ-1} (log (nA/t))^r / (log n)^r`. -/
private theorem rpow_mul_logRatio_eq (n : ℝ) (v : Fin m' → ℝ) (t : ℝ) :
    t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t
      = (Ioo 0 (n * NormalCrossing.secondaryScale k k' b v)).indicator
          (fun t ↦ t ^ (lam - 1) * Real.log (n * NormalCrossing.secondaryScale k k' b v / t) ^ r) t
              /
        Real.log n ^ r := by
  unfold NormalCrossing.logRatio
  by_cases ht : t ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b v)
  · rw [indicator_of_mem ht, indicator_of_mem ht, div_pow]; ring
  · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp

theorem NormalCrossing.integrableOn_rpow_mul_logRatio (hlam0 : 0 < lam) {n : ℝ} (hn : 0 < n)
    {v : Fin m' → ℝ}
    (hA : 0 < NormalCrossing.secondaryScale k k' b v) :
    IntegrableOn (fun t ↦ t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t) (Ioi 0) := by
  simp_rw [rpow_mul_logRatio_eq]
  exact (((integrableOn_rpow_mul_log_pow_Ioo hlam0 (by positivity) r).integrable_indicator
    measurableSet_Ioo).div_const _).integrableOn

/-- `∫₀^∞ t^{λ-1} R_n(t, v) dt = r! (nA(v))^λ / (λ^{r+1} (log n)^r)` ([Wat09, Example 4.7]). -/
private theorem integral_rpow_mul_logRatio (hlam0 : 0 < lam) {n : ℝ} (hn : 0 < n) {v : Fin m' → ℝ}
    (hA : 0 < NormalCrossing.secondaryScale k k' b v) :
    ∫ t in Ioi 0, t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t
      = (r.factorial : ℝ) * (n * NormalCrossing.secondaryScale k k' b v) ^ lam / lam ^ (r + 1) /
          Real.log n ^ r := by
  simp_rw [rpow_mul_logRatio_eq]
  rw [integral_div, setIntegral_indicator measurableSet_Ioo,
    inter_eq_right.mpr Ioo_subset_Ioi_self, integral_rpow_mul_log_pow (by positivity) hlam0 r]

/-- No thesis counterpart. The frozen integrand on the open cube, rearranged so that
`u ↦ f (a u^{2k}) u^h` with `a = n v^{2k'}` is visible. -/
private theorem frozen_integrand_eq {n β U V ξ P Q φ : ℝ} (hn : 0 ≤ n) :
    Real.exp (-(n * β * (U * V)) + Real.sqrt n * β * Real.sqrt (U * V) * ξ) * (P * Q) * φ
      = Real.exp (-(β * (n * V * U)) + β * Real.sqrt (n * V * U) * ξ) * P * (Q * φ) := by
  rw [show n * V * U = n * (U * V) by ring, Real.sqrt_mul hn,
    show -(β * (n * (U * V))) + β * (Real.sqrt n * Real.sqrt (U * V)) * ξ
      = -(n * β * (U * V)) + Real.sqrt n * β * Real.sqrt (U * V) * ξ by ring]
  ring

/-- The inner identity of `frozen_identity` for a fixed secondary point `v` of the open cube:
`n^λ / (log n)^r ∫_u K^0 e^{-nβK + √n β √K ξ₀(v)} u^h v^{h'} φ₀(v) du
  = γ v^μ φ₀(v) ∫_t t^{λ-1} e^{-βt + β√t ξ₀(v)} R_n(t, v) dt`. -/
private theorem frozen_inner (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hb : 0 < b) (hβ : 0 < β) {ξ₀ φ₀ : (Fin m' → ℝ) → ℝ} {M : ℝ}
    (hξ : ∀ v ∈ cube m' b, |ξ₀ v| ≤ M) {n : ℝ} (hn : 1 < n) {v : Fin m' → ℝ}
    (hv : ∀ j, v j ∈ Ioo 0 b) :
    n ^ lam / Real.log n ^ r * ∫ u in ocube (r + 1) b,
        potential k k' (u, v) ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' (u, v)) +
            Real.sqrt n * β * Real.sqrt (potential k k' (u, v)) * ξ₀ v) *
          NormalCrossing.monomialWeight h h' (u, v) * φ₀ v
      = NormalCrossing.gammaConst k h lam b * (NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
            NormalCrossing.logRatio k k' b n v t) := by
  have hv0 : ∀ j, 0 < v j := fun j ↦ (hv j).1
  have hvc : v ∈ cube m' b := mem_cube.2 fun j ↦ Ioo_subset_Icc_self (hv j)
  have hn0 : 0 < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos hn
  have hV : 0 < ∏ j, v j ^ (2 * k' j) := Finset.prod_pos fun j _ ↦ pow_pos (hv0 j) _
  set a : ℝ := n * ∏ j, v j ^ (2 * k' j) with ha_def
  have ha : 0 < a := by positivity
  have hc : a * b ^ (2 * ∑ j, k j) = n * NormalCrossing.secondaryScale k k' b v := by
    rw [ha_def, NormalCrossing.secondaryScale]; ring
  set f : ℝ → ℝ := fun t ↦ Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) with hf_def
  have hfm : Measurable f := by rw [hf_def]; fun_prop
  -- Step A: rewrite the `u`-integrand on the open cube.
  have hre : ∫ u in ocube (r + 1) b,
        potential k k' (u, v) ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' (u, v)) +
            Real.sqrt n * β * Real.sqrt (potential k k' (u, v)) * ξ₀ v) *
          NormalCrossing.monomialWeight h h' (u, v) * φ₀ v
      = (∫ u in cube (r + 1) b, f (a * ∏ j, u j ^ (2 * k j)) * ∏ j, u j ^ h j) *
          ((∏ j, v j ^ h' j) * φ₀ v) := by
    rw [← integral_mul_const, ← restrict_ocube_eq]
    refine setIntegral_congr_fun (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)
      fun u _ ↦ ?_
    simp only [potential, NormalCrossing.monomialWeight, Real.rpow_zero, one_mul, hf_def]
    exact frozen_integrand_eq hn0.le
  -- Step B: [Wat09, Theorem 4.6] for the `u`-integral.
  set ν : ℝ → ℝ := (Ioo 0 (a * b ^ (2 * ∑ j, k j))).indicator
    (fun t ↦ NormalCrossing.gammaConst k h lam b * t ^ (lam - 1) / a ^ lam *
      Real.log (a * b ^ (2 * ∑ j, k j) / t) ^ r) with hν_def
  have hνint : Integrable ν := by
    rw [hν_def, integrable_indicator_iff measurableSet_Ioo]
    have := ((integrableOn_rpow_mul_log_pow_Ioo hlam0
      (by positivity : 0 < a * b ^ (2 * ∑ j, k j)) r).const_mul
          (NormalCrossing.gammaConst k h lam b / a ^ lam))
    exact IntegrableOn.congr_fun this (fun t _ ↦ by ring) measurableSet_Ioo
  have hν0 : ∀ t, 0 ≤ ν t := by
    intro t
    rw [hν_def]
    refine indicator_nonneg (fun t ht ↦ ?_) t
    have hlog := Real.log_div_nonneg_of_mem_Ioo ht
    have ha' : 0 < a ^ lam := Real.rpow_pos_of_pos ha _
    have hγ := gammaConst_pos h lam hk hb
    have := ht.1
    positivity
  have hint : Integrable fun t ↦ f t * ν t := by
    refine (hνint.const_mul (Real.exp (β * M ^ 2 / 2))).mono'
      (hfm.aestronglyMeasurable.mul hνint.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t ↦ ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hν0 t), abs_of_pos (Real.exp_pos _)]
    by_cases ht : t ∈ Ioo 0 (a * b ^ (2 * ∑ j, k j))
    · refine mul_le_mul_of_nonneg_right ?_ (hν0 t)
      refine (NormalCrossing.exp_frozen_le hβ.le ht.1.le (hξ v hvc)).trans ?_
      exact mul_le_of_le_one_right (Real.exp_pos _).le
        (Real.exp_le_one_iff.mpr (by nlinarith [ht.1]))
    · simp [hν_def, indicator_of_notMem ht]
  have step3 := integral_cube_monomial (r := r) (a := a) hk hlam ha hb (f := f)
    hfm.aestronglyMeasurable hint
  -- Step C: identify the density with `R_n` and pull out the constants.
  have hpt : ∀ t, f t * ν t
      = NormalCrossing.gammaConst k h lam b / a ^ lam * Real.log n ^ r *
        (t ^ (lam - 1) * f t * NormalCrossing.logRatio k k' b n v t) := by
    intro t
    rw [hν_def, NormalCrossing.logRatio, hc]
    by_cases ht : t ∈ Ioo 0 (n * NormalCrossing.secondaryScale k k' b v)
    · rw [indicator_of_mem ht, indicator_of_mem ht, div_pow]
      have ha' : 0 < a ^ lam := Real.rpow_pos_of_pos ha _
      field_simp
    · rw [indicator_of_notMem ht, indicator_of_notMem ht]; simp
  have hpull : ∫ t in Ioi 0, f t * ν t
      = NormalCrossing.gammaConst k h lam b / a ^ lam * Real.log n ^ r *
        ∫ t in Ioi 0, t ^ (lam - 1) * f t * NormalCrossing.logRatio k k' b n v t := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall hpt)
  -- the secondary weight: `v^{h'} / (v^{2k'})^λ = v^μ`
  have hVpow : (∏ j, v j ^ (2 * k' j)) ^ lam = ∏ j, v j ^ (2 * k' j * lam) := by
    rw [← Real.finsetProd_rpow _ _ fun j _ ↦ pow_nonneg (hv0 j).le _]
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (hv0 j).le]
    push_cast
    ring_nf
  have hvw : (∏ j, v j ^ h' j) / (∏ j, v j ^ (2 * k' j)) ^ lam = NormalCrossing.secondaryWeight k'
      h' lam v := by
    rw [hVpow, ← Finset.prod_div_distrib, NormalCrossing.secondaryWeight]
    exact Finset.prod_congr rfl fun j _ ↦ (Real.rpow_sub (hv0 j) _ _).symm
  have hapow : a ^ lam = n ^ lam * (∏ j, v j ^ (2 * k' j)) ^ lam := by
    rw [ha_def]; exact Real.mul_rpow hn0.le hV.le
  have hnl : 0 < n ^ lam := Real.rpow_pos_of_pos hn0 _
  have hVl : 0 < (∏ j, v j ^ (2 * k' j)) ^ lam := Real.rpow_pos_of_pos hV _
  rw [hre, step3, hpull, ← hvw, hapow]
  simp only [hf_def]
  generalize (∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
    NormalCrossing.logRatio k k' b n v t) = J
  field_simp

/-- Parametric integrals over `(0, ∞)` of jointly measurable functions are measurable. -/
theorem _root_.MeasureTheory.stronglyMeasurable_integral_Ioi {G : (Fin m' → ℝ) × ℝ → ℝ}
    (hG : Measurable G) :
    StronglyMeasurable fun v ↦ ∫ t in Ioi 0, G (v, t) :=
  hG.stronglyMeasurable.integral_prod_right'

/-- The frozen exponent is bounded by `e^{βM²/2}` on `t ≥ 0`. -/
private theorem exp_frozen_le' {β t ξ M : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) (hξ : |ξ| ≤ M) :
    Real.exp (-(β * t) + β * Real.sqrt t * ξ) ≤ Real.exp (β * M ^ 2 / 2) :=
  (NormalCrossing.exp_frozen_le hβ ht hξ).trans (mul_le_of_le_one_right (Real.exp_pos _).le
    (Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hβ ht])))

/-- `t^{λ-1} e^{-βt + β√t ξ}` is integrable on `(0, ∞)` for `|ξ| ≤ M`. -/
theorem NormalCrossing.integrableOn_rpow_mul_exp_frozen (hlam0 : 0 < lam) (hβ : 0 < β) {ξ M : ℝ}
    (hξ : |ξ| ≤ M) :
    IntegrableOn (fun t : ℝ ↦ t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ))
      (Ioi 0) := by
  refine ((integrableOn_rpow_mul_exp_neg_half (a := lam - 1) (by linarith) hβ).const_mul
    (Real.exp (β * M ^ 2 / 2))).mono' (by fun_prop : Measurable fun t : ℝ ↦
      t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ)
      ≤ t ^ (lam - 1) * (Real.exp (β * M ^ 2 / 2) * Real.exp (-(β * t / 2))) :=
        mul_le_mul_of_nonneg_left (NormalCrossing.exp_frozen_le hβ.le ht.le hξ)
            (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

/-- `|∫₀^∞ t^{λ-1} e^{-βt + β√t ξ}| ≤ e^{βM²/2} ∫₀^∞ t^{λ-1} e^{-βt/2}` for `|ξ| ≤ M`. -/
theorem NormalCrossing.abs_integral_rpow_mul_exp_frozen_le (hlam0 : 0 < lam) (hβ : 0 < β) {ξ M : ℝ}
    (hξ : |ξ| ≤ M) :
    |∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ)|
      ≤ Real.exp (β * M ^ 2 / 2) * ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) := by
  rw [← Real.norm_eq_abs, ← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun t ↦ norm_nonneg _)
    ((integrableOn_rpow_mul_exp_neg_half (a := lam - 1) (by linarith) hβ).const_mul _) ?_)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ)
      ≤ t ^ (lam - 1) * (Real.exp (β * M ^ 2 / 2) * Real.exp (-(β * t / 2))) :=
        mul_le_mul_of_nonneg_left (NormalCrossing.exp_frozen_le hβ.le ht.le hξ)
            (Real.rpow_nonneg ht.le _)
    _ = _ := by ring

/-- `t^{λ-1} e^{-βt + β√t ξ} R_n(t, v)` is integrable on `(0, ∞)`. -/
private theorem integrableOn_rpow_mul_exp_frozen_mul_logRatio (hlam0 : 0 < lam) (hb : 0 < b)
    (hβ : 0 < β)
    {n : ℝ} (hn : 1 < n) {v : Fin m' → ℝ} (hv0 : ∀ j, 0 < v j) {ξ M : ℝ} (hξ : |ξ| ≤ M) :
    IntegrableOn (fun t : ℝ ↦ t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ) *
      NormalCrossing.logRatio k k' b n v t) (Ioi 0) := by
  have hR := NormalCrossing.integrableOn_rpow_mul_logRatio (k := k) (k' := k') hlam0
      (by linarith : (0 : ℝ) < n)
    (NormalCrossing.secondaryScale_pos hb hv0)
  refine (hR.const_mul (Real.exp (β * M ^ 2 / 2))).mono'
    ((by fun_prop : Measurable fun t : ℝ ↦
      t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ)).mul
      (measurable_logRatio n v)).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht : 0 < t := ht
  have hR0 := logRatio_nonneg (k := k) (k' := k') (b := b) hn v t
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hR0)]
  calc t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t *
      ξ) * NormalCrossing.logRatio k k' b n v t
      ≤ t ^ (lam - 1) * Real.exp (β * M ^ 2 / 2) * NormalCrossing.logRatio k k' b n v t :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (exp_frozen_le' hβ.le ht.le hξ) (Real.rpow_nonneg ht.le _))
          hR0
    _ = _ := by ring

/-- The pointwise domination of the integrand of `NormalCrossing.frozenError`:
`t^{λ-1} e^{-βt/2} |R_n − 1| ≤ t^{λ-1} R_n + t^{λ-1} e^{-βt/2}`. -/
private theorem frozenError_integrand_le (hβ : 0 < β) {n : ℝ} (hn : 1 < n) (v : Fin m' → ℝ) {t : ℝ}
    (ht : 0 < t) :
    t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t + t ^ (lam - 1) * Real.exp
          (-(β * t / 2)) := by
  have hR0 := logRatio_nonneg (k := k) (k' := k') (b := b) hn v t
  have habs : |NormalCrossing.logRatio k k' b n v t - 1| ≤ NormalCrossing.logRatio k k' b n v t +
      1 := by
    rw [abs_le]; constructor <;> linarith
  have hX : 0 ≤ t ^ (lam - 1) * Real.exp (-(β * t / 2)) := by positivity
  have h1 : t ^ (lam - 1) * Real.exp (-(β * t / 2)) * NormalCrossing.logRatio k k' b n v t
      ≤ t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t := by
    calc t ^ (lam - 1) * Real.exp (-(β * t / 2)) * NormalCrossing.logRatio k k' b n v t
        ≤ t ^ (lam - 1) * 1 * NormalCrossing.logRatio k k' b n v t :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (Real.exp_le_one_iff.mpr (by nlinarith [mul_pos hβ ht])) (Real.rpow_nonneg ht.le _)) hR0
      _ = _ := by ring
  calc t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ t ^ (lam - 1) * Real.exp (-(β * t / 2)) * (NormalCrossing.logRatio k k' b n v t + 1) :=
        mul_le_mul_of_nonneg_left habs hX
    _ = t ^ (lam - 1) * Real.exp (-(β * t / 2)) * NormalCrossing.logRatio k k' b n v t +
          t ^ (lam - 1) * Real.exp (-(β * t / 2)) := by ring
    _ ≤ t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t + t ^ (lam - 1) * Real.exp
        (-(β * t / 2)) := by
        linarith

/-- The `t`-integrand of `NormalCrossing.frozenError` is integrable for every `v` in the open cube.
-/
theorem NormalCrossing.integrableOn_frozenError_inner (hlam0 : 0 < lam) (hb : 0 < b) (hβ : 0 < β)
    {n : ℝ}
    (hn : 1 < n) {v : Fin m' → ℝ} (hv0 : ∀ j, 0 < v j) :
    IntegrableOn (fun t : ℝ ↦ t ^ (lam - 1) * Real.exp (-(β * t / 2)) *
      |NormalCrossing.logRatio k k' b n v t - 1|) (Ioi 0) := by
  have hR := NormalCrossing.integrableOn_rpow_mul_logRatio (k := k) (k' := k') hlam0
      (by linarith : (0 : ℝ) < n)
    (NormalCrossing.secondaryScale_pos hb hv0)
  refine (hR.add (integrableOn_rpow_mul_exp_neg_half (a := lam - 1) (by linarith) hβ)).mono'
    ((by fun_prop : Measurable fun t : ℝ ↦ t ^ (lam - 1) * Real.exp (-(β * t / 2))).mul
      (continuous_abs.measurable.comp ((measurable_logRatio n v).sub
        measurable_const))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht : 0 < t := ht
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Pi.add_apply]
  exact frozenError_integrand_le hβ hn v ht

/-- The `t`-integral of `NormalCrossing.frozenError` is bounded uniformly in `v`:
`∫₀^∞ t^{λ-1} e^{-βt/2} |R_n − 1| ≤ r! (n b^{2|k|+2|k'|})^λ / (λ^{r+1} (log n)^r) + Γ-term`. -/
private theorem frozenError_inner_le (hlam0 : 0 < lam) (hb : 0 < b) (hβ : 0 < β) {n : ℝ}
    (hn : 1 < n)
    {v : Fin m' → ℝ} (hv : ∀ j, v j ∈ Ioo 0 b) :
    ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t -
        1|
      ≤ (r.factorial : ℝ) * (n * (b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j))) ^ lam /
            lam ^ (r + 1) / Real.log n ^ r
        + ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) := by
  have hv0 : ∀ j, 0 < v j := fun j ↦ (hv j).1
  have hn0 : 0 < n := by linarith
  have hA := NormalCrossing.secondaryScale_pos (k := k) (k' := k') hb hv0
  have hR := NormalCrossing.integrableOn_rpow_mul_logRatio (k := k) hlam0 hn0 hA
  have hG := integrableOn_rpow_mul_exp_neg_half (a := lam - 1) (by linarith) hβ
  calc ∫ t in Ioi 0, t ^ (lam -
      1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ ∫ t in Ioi 0, (t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t +
          t ^ (lam - 1) * Real.exp (-(β * t / 2))) := by
        refine integral_mono_of_nonneg ?_ (hR.add hG) ?_
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          have ht : 0 < t := ht
          positivity
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact frozenError_integrand_le hβ hn v ht
    _ = (∫ t in Ioi 0, t ^ (lam - 1) * NormalCrossing.logRatio k k' b n v t) +
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) := integral_add hR hG
    _ ≤ _ := by
        rw [integral_rpow_mul_logRatio hlam0 hn0 hA]
        have hlogn : 0 < Real.log n := Real.log_pos hn
        have hAle := secondaryScale_le (k := k) (k' := k') hb fun j ↦ Ioo_subset_Icc_self (hv j)
        have hpow : (n * NormalCrossing.secondaryScale k k' b v) ^ lam
            ≤ (n * (b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j))) ^ lam :=
          Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hAle hn0.le) hlam0.le
        have hdiv := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ r.factorial))
          (by positivity : (0 : ℝ) ≤ lam ^ (r + 1))) (pow_nonneg hlogn.le r)
        linarith

/-- The integrand of `NormalCrossing.frozenError` is integrable over the secondary cube: the
`t`-integral is
measurable in `v` and bounded uniformly, and `v^μ` is integrable. -/
theorem NormalCrossing.integrable_frozenError_integrand (hlam0 : 0 < lam)
    (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β) {n : ℝ} (hn : 1 < n) :
    IntegrableOn (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v *
      ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t
          - 1|)
      (cube m' b) := by
  have hμ : ∀ j, -1 < h' j - 2 * k' j * lam := fun j ↦ by linarith [hsec j]
  have hGE : Measurable fun p : (Fin m' → ℝ) × ℝ ↦
      p.2 ^ (lam - 1) * Real.exp (-(β * p.2 / 2)) * |NormalCrossing.logRatio k k' b n p.1 p.2 -
          1| :=
    (by fun_prop : Measurable fun p : (Fin m' → ℝ) × ℝ ↦
      p.2 ^ (lam - 1) * Real.exp (-(β * p.2 / 2))).mul
      (continuous_abs.measurable.comp ((NormalCrossing.measurable_logRatio_uncurry n).sub
          measurable_const))
  have hE := stronglyMeasurable_integral_Ioi hGE
  have hwint : IntegrableOn (NormalCrossing.secondaryWeight k' h' lam) (cube m' b) :=
      integrableOn_cube_rpow hμ hb
  refine (hwint.const_mul
    ((r.factorial : ℝ) * (n * (b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j))) ^ lam /
        lam ^ (r + 1) / Real.log n ^ r
      + ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)))).mono'
    (measurable_secondaryWeight.stronglyMeasurable.mul hE).aestronglyMeasurable ?_
  rw [← restrict_ocube_eq]
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)] with v hv
  have hv' : ∀ j, v j ∈ Ioo 0 b := fun j ↦ hv j (mem_univ j)
  have hw := NormalCrossing.secondaryWeight_nonneg (k' := k') (h' := h') (lam := lam) fun j
      ↦ (hv' j).1.le
  have hE0 : 0 ≤ ∫ t in Ioi 0,
      t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1| :=
    setIntegral_nonneg measurableSet_Ioi fun t ht ↦ by
      have ht : 0 < t := ht
      positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw hE0)]
  exact (mul_comm _ _).le.trans
    (mul_le_mul_of_nonneg_right (frozenError_inner_le hlam0 hb hβ hn hv') hw)

/-- The pointwise (in `v`) estimate behind `NormalCrossing.abs_frozen_sub_frozenLimit_le`:
`|v^μ φ₀ (J_n(v) − J_∞(v))| ≤ P e^{βM²/2} v^μ E_n(v)`. -/
private theorem frozen_pointwise_bound (hlam0 : 0 < lam) (hb : 0 < b) (hβ : 0 < β)
    {ξ₀ φ₀ : (Fin m' → ℝ) → ℝ} {M P : ℝ} (hξ : ∀ v ∈ cube m' b, |ξ₀ v| ≤ M)
    (hφ : ∀ v ∈ cube m' b, |φ₀ v| ≤ P) {n : ℝ} (hn : 1 < n) {v : Fin m' → ℝ}
    (hv : ∀ j, v j ∈ Ioo 0 b) :
    |(NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
        ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
          NormalCrossing.logRatio k k' b n v t)
      - NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
        ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v)|
      ≤ P * Real.exp (β * M ^ 2 / 2) * (NormalCrossing.secondaryWeight k' h' lam v *
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) *
            |NormalCrossing.logRatio k k' b n v t - 1|) := by
  have hv0 : ∀ j, 0 < v j := fun j ↦ (hv j).1
  have hvc : v ∈ cube m' b := mem_cube.2 fun j ↦ Ioo_subset_Icc_self (hv j)
  have hw := NormalCrossing.secondaryWeight_nonneg (k' := k') (h' := h') (lam := lam) fun j
      ↦ (hv0 j).le
  have hξv := hξ v hvc
  have hP := hφ v hvc
  have hP0 : 0 ≤ P := (abs_nonneg _).trans hP
  have h1 :=
    integrableOn_rpow_mul_exp_frozen_mul_logRatio (k := k) (k' := k') hlam0 hb hβ hn hv0 hξv
  have h2 := NormalCrossing.integrableOn_rpow_mul_exp_frozen hlam0 hβ hξv
  have hE := NormalCrossing.integrableOn_frozenError_inner (k := k) (k' := k') hlam0 hb hβ hn hv0
  have hJ : |∫ t in Ioi 0, (t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
        NormalCrossing.logRatio k k' b n v t
        - t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v))|
      ≤ Real.exp (β * M ^ 2 / 2) * ∫ t in Ioi 0,
          t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1| := by
    rw [← Real.norm_eq_abs, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t ↦ norm_nonneg _) (hE.const_mul _) ?_)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : 0 < t := ht
    rw [Real.norm_eq_abs, show t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
          NormalCrossing.logRatio k k' b n v t
        - t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v)
      = t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
          (NormalCrossing.logRatio k k' b n v t - 1) by ring,
      abs_mul, abs_of_nonneg (by positivity)]
    calc t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
          |NormalCrossing.logRatio k k' b n v t - 1|
        ≤ t ^ (lam - 1) * (Real.exp (β * M ^ 2 / 2) * Real.exp (-(β * t / 2))) *
          |NormalCrossing.logRatio k k' b n v t - 1| :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (NormalCrossing.exp_frozen_le hβ.le ht.le hξv) (Real.rpow_nonneg ht.le _))
                (abs_nonneg _)
      _ = _ := by ring
  rw [← mul_sub, ← integral_sub h1 h2, abs_mul, abs_mul, abs_of_nonneg hw]
  calc NormalCrossing.secondaryWeight k' h' lam v * |φ₀ v| * |∫ t in Ioi 0,
        (t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) * NormalCrossing.logRatio k k'
            b n v t
          - t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v))|
      ≤ NormalCrossing.secondaryWeight k' h' lam v * P * (Real.exp (β * M ^ 2 / 2) * ∫ t in Ioi 0,
          t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1|) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hP hw) hJ (abs_nonneg _) (mul_nonneg hw hP0)
    _ = _ := by ring

private theorem logRatio_tendsto {v : Fin m' → ℝ} (hA : 0 < NormalCrossing.secondaryScale k k' b v)
    {t : ℝ}
    (ht : 0 < t) : Tendsto (fun n : ℝ ↦ NormalCrossing.logRatio k k' b n v t) atTop (𝓝 1) := by
  set A := NormalCrossing.secondaryScale k k' b v
  have h1 : Tendsto (fun n : ℝ ↦ 1 + Real.log (A / t) / Real.log n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := Real.log (A / t))).div_atTop Real.tendsto_log_atTop
    simpa using this.const_add 1
  have h2 := h1.pow r
  rw [one_pow] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop 1, eventually_gt_atTop (t / A)] with n hn1 hn
  have hn0 : 0 < n := by linarith
  have hmem : t ∈ Ioo 0 (n * A) := ⟨ht, by rwa [div_lt_iff₀ hA] at hn⟩
  rw [NormalCrossing.logRatio, indicator_of_mem hmem]
  congr 1
  rw [mul_div_assoc, Real.log_mul hn0.ne' (div_pos hA ht).ne', add_div,
    div_self (Real.log_pos hn1).ne']

/-- Domination of `|R_n(t, v) − 1|` uniformly in `n ≥ 2`:
`|R_n − 1| ≤ 1 + 2^r (1 + (|log (A(v)/t)| / log 2)^r)`. No thesis counterpart. -/
private theorem abs_logRatio_sub_one_le {v : Fin m' → ℝ} (hA : 0 < NormalCrossing.secondaryScale k
    k' b v) {n : ℝ}
    (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ 1 + 2 ^ r * (1 + (|Real.log (NormalCrossing.secondaryScale k k' b v / t)| / Real.log 2) ^
          r) := by
  set A := NormalCrossing.secondaryScale k k' b v
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : 0 < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hX : 0 ≤ (|Real.log (A / t)| / Real.log 2) ^ r := by positivity
  have h2r : (0 : ℝ) ≤ 2 ^ r := by positivity
  by_cases hmem : t ∈ Ioo 0 (n * A)
  · rw [NormalCrossing.logRatio, indicator_of_mem hmem]
    have hq0 : 0 ≤ Real.log (n * A / t) / Real.log n :=
      div_nonneg (Real.log_div_nonneg_of_mem_Ioo hmem) hlogn.le
    have hq : Real.log (n * A / t) / Real.log n ≤ 1 + |Real.log (A / t)| / Real.log 2 := by
      rw [mul_div_assoc, Real.log_mul hn0.ne' (div_pos hA ht).ne', add_div,
        div_self hlogn.ne']
      have : Real.log (A / t) / Real.log n ≤ |Real.log (A / t)| / Real.log 2 :=
        calc Real.log (A / t) / Real.log n ≤ |Real.log (A / t)| / Real.log n :=
              div_le_div_of_nonneg_right (le_abs_self _) hlogn.le
          _ ≤ |Real.log (A / t)| / Real.log 2 :=
              div_le_div_of_nonneg_left (abs_nonneg _) hlog2 hlog2n
      linarith
    have hR0 : 0 ≤ (Real.log (n * A / t) / Real.log n) ^ r := pow_nonneg hq0 r
    have hR : (Real.log (n * A / t) / Real.log n) ^ r
        ≤ 2 ^ r * (1 + (|Real.log (A / t)| / Real.log 2) ^ r) := by
      calc (Real.log (n * A / t) / Real.log n) ^ r
          ≤ (1 + |Real.log (A / t)| / Real.log 2) ^ r := pow_le_pow_left₀ hq0 hq r
        _ ≤ 2 ^ r * (1 ^ r + (|Real.log (A / t)| / Real.log 2) ^ r) :=
            add_pow_le_two_pow_mul_add_pow zero_le_one (by positivity) r
        _ = _ := by rw [one_pow]
    rw [abs_le]
    constructor <;> nlinarith
  · rw [NormalCrossing.logRatio, indicator_of_notMem hmem, zero_sub, abs_neg, abs_one]
    nlinarith

/-- No thesis counterpart. -/
theorem _root_.Real.rpow_mul_div_rpow {A t : ℝ} (hA : 0 < A) (ht : 0 < t) (a δ : ℝ) :
    t ^ a * (A / t) ^ δ = A ^ δ * t ^ (a - δ) := by
  rw [Real.div_rpow hA.le ht.le, Real.rpow_sub ht]
  ring

/-- On the open cube, `v^μ A(v)^δ = (b^{2|k|})^δ v^{μ + 2δk'}`. No thesis counterpart. -/
theorem NormalCrossing.secondaryWeight_mul_secondaryScale_rpow {v : Fin m' → ℝ} (hv : ∀ j, 0 < v j)
    (hb : 0 < b) (δ : ℝ) :
    NormalCrossing.secondaryWeight k' h' lam v * NormalCrossing.secondaryScale k k' b v ^ δ
      = (b ^ (2 * ∑ j, k j)) ^ δ * ∏ j, v j ^ (h' j - 2 * k' j * lam + 2 * k' j * δ) := by
  have e := Real.prod_pow_rpow_mul_prod_rpow k' (fun j ↦ h' j - 2 * k' j * lam) δ hv
  rw [← e, NormalCrossing.secondaryWeight, NormalCrossing.secondaryScale,
    Real.mul_rpow (pow_nonneg hb.le _) (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hv j).le _)]
  ring

/-- The integrand of `E(n)` in `t` is dominated, uniformly in `n ≥ 2`, by a combination of
three monomial kernels. No thesis counterpart. -/
private theorem frozen_inner_bound {δ C : ℝ}
    (hC : ∀ x : ℝ, 0 < x → |Real.log x| ^ r ≤ C * (x ^ δ + x ^ (-δ)))
    {v : Fin m' → ℝ} (hA : 0 < NormalCrossing.secondaryScale k k' b v) {n : ℝ} (hn : 2 ≤ n) {t : ℝ}
    (ht : 0 < t) :
    t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ (1 + 2 ^ r) * (t ^ (lam - 1) * Real.exp (-(β * t / 2)))
        + 2 ^ r * C / Real.log 2 ^ r *
          (NormalCrossing.secondaryScale k k' b v ^ δ * (t ^ (lam - 1 - δ) * Real.exp
              (-(β * t / 2)))
            + NormalCrossing.secondaryScale k k' b v ^ (-δ) *
                (t ^ (lam - 1 + δ) * Real.exp (-(β * t / 2)))) := by
  set A := NormalCrossing.secondaryScale k k' b v
  have hT : 0 ≤ t ^ (lam - 1) * Real.exp (-(β * t / 2)) := by positivity
  have hL : 0 < Real.log 2 ^ r := pow_pos (Real.log_pos (by norm_num)) r
  have h1 := abs_logRatio_sub_one_le hA hn ht
  have h2 := hC (A / t) (div_pos hA ht)
  have h3 : |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ 1 + 2 ^ r + 2 ^ r * C / Real.log 2 ^ r * ((A / t) ^ δ + (A / t) ^ (-δ)) := by
    calc |NormalCrossing.logRatio k k' b n v t - 1|
        ≤ 1 + 2 ^ r * (1 + |Real.log (A / t)| ^ r / Real.log 2 ^ r) := by rwa [div_pow] at h1
      _ = 1 + 2 ^ r + 2 ^ r / Real.log 2 ^ r * |Real.log (A / t)| ^ r := by ring
      _ ≤ 1 + 2 ^ r + 2 ^ r / Real.log 2 ^ r * (C * ((A / t) ^ δ + (A / t) ^ (-δ))) := by
          gcongr
      _ = _ := by ring
  calc t ^ (lam - 1) * Real.exp (-(β * t / 2)) * |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ t ^ (lam - 1) * Real.exp (-(β * t / 2)) *
          (1 + 2 ^ r + 2 ^ r * C / Real.log 2 ^ r * ((A / t) ^ δ + (A / t) ^ (-δ))) :=
        mul_le_mul_of_nonneg_left h3 hT
    _ = (1 + 2 ^ r) * (t ^ (lam - 1) * Real.exp (-(β * t / 2)))
        + 2 ^ r * C / Real.log 2 ^ r *
          (t ^ (lam - 1) * (A / t) ^ δ * Real.exp (-(β * t / 2))
            + t ^ (lam - 1) * (A / t) ^ (-δ) * Real.exp (-(β * t / 2))) := by ring
    _ = _ := by
        rw [Real.rpow_mul_div_rpow hA ht, Real.rpow_mul_div_rpow hA ht, sub_neg_eq_add]
        ring

/-- Almost every point of `[0,b]^m × (0, ∞)` has all cube coordinates in `(0, b)` and a
positive last coordinate. No thesis counterpart. -/
theorem ae_cube_prod_Ioi {m : ℕ} (b : ℝ) :
    ∀ᵐ z : (Fin m → ℝ) × ℝ ∂((volume.restrict (cube m b)).prod (volume.restrict (Ioi 0))),
      (∀ j, z.1 j ∈ Ioo 0 b) ∧ 0 < z.2 := by
  rw [← restrict_ocube_eq, Measure.prod_restrict]
  filter_upwards [ae_restrict_mem ((MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo).prod
    measurableSet_Ioi)] with z hz
  exact ⟨fun j ↦ hz.1 j (mem_univ j), hz.2⟩

/-- An integrable dominator for the integrand of `E(n)`, uniform in `n ≥ 2`. No thesis
counterpart. -/
private theorem exists_frozen_dominator (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1)
    (hb : 0 < b) (hβ : 0 < β) :
    ∃ G : (Fin m' → ℝ) × ℝ → ℝ,
      Integrable G ((volume.restrict (cube m' b)).prod (volume.restrict (Ioi 0))) ∧
      ∀ n : ℝ, 2 ≤ n → ∀ z : (Fin m' → ℝ) × ℝ, (∀ j, z.1 j ∈ Ioo 0 b) → 0 < z.2 →
        ‖NormalCrossing.secondaryWeight k' h' lam z.1 *
          (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) * |NormalCrossing.logRatio k k' b n z.1 z.2 -
              1|)‖
          ≤ G z := by
  obtain ⟨δ, hδ0, hδlam, hδ⟩ := NormalCrossing.exists_small_exponent hlam0 hsec
  obtain ⟨C, -, hC⟩ := Real.exists_abs_log_pow_le hδ0 r
  have hμ0 : ∀ j, -1 < h' j - 2 * k' j * lam := fun j ↦ by linarith [hsec j]
  have hμ1 : ∀ j, -1 < h' j - 2 * k' j * lam + 2 * k' j * δ := fun j ↦ by
    have : 0 ≤ 2 * (k' j : ℝ) * δ := by positivity
    linarith [hsec j]
  have hμ2 : ∀ j, -1 < h' j - 2 * k' j * lam + 2 * k' j * (-δ) := fun j ↦ by linarith [hδ j]
  refine ⟨fun z ↦ (1 + 2 ^ r) * ((∏ j, z.1 j ^ (h' j - 2 * k' j * lam)) *
      (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2))))
    + 2 ^ r * C / Real.log 2 ^ r *
      ((b ^ (2 * ∑ j, k j)) ^ δ * ((∏ j, z.1 j ^ (h' j - 2 * k' j * lam + 2 * k' j * δ)) *
          (z.2 ^ (lam - 1 - δ) * Real.exp (-(β * z.2 / 2))))
        + (b ^ (2 * ∑ j, k j)) ^ (-δ) *
          ((∏ j, z.1 j ^ (h' j - 2 * k' j * lam + 2 * k' j * (-δ))) *
            (z.2 ^ (lam - 1 + δ) * Real.exp (-(β * z.2 / 2))))), ?_, ?_⟩
  · refine (((integrableOn_cube_rpow hμ0 hb).mul_prod
        (integrableOn_rpow_mul_exp_neg_half (by linarith) hβ)).const_mul _).add
      (((((integrableOn_cube_rpow hμ1 hb).mul_prod
        (integrableOn_rpow_mul_exp_neg_half (by linarith) hβ)).const_mul _).add
        (((integrableOn_cube_rpow hμ2 hb).mul_prod
          (integrableOn_rpow_mul_exp_neg_half (by linarith) hβ)).const_mul _)).const_mul _)
  · intro n hn z hz ht
    have hv : ∀ j, 0 < z.1 j := fun j ↦ (hz j).1
    have hA : 0 < NormalCrossing.secondaryScale k k' b z.1 := NormalCrossing.secondaryScale_pos hb
        hv
    have hW0 : 0 ≤ NormalCrossing.secondaryWeight k' h' lam z.1 :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv j).le _
    have e0 : NormalCrossing.secondaryWeight k' h' lam z.1 = ∏ j, z.1 j ^ (h' j - 2 * k' j * lam) :=
        rfl
    have e1 := NormalCrossing.secondaryWeight_mul_secondaryScale_rpow (k := k) (k' := k') (h' := h')
      (lam := lam) hv hb δ
    have e2 := NormalCrossing.secondaryWeight_mul_secondaryScale_rpow (k := k) (k' := k') (h' := h')
      (lam := lam) hv hb (-δ)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW0 (by positivity))]
    calc NormalCrossing.secondaryWeight k' h' lam z.1 *
          (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) * |NormalCrossing.logRatio k k' b n z.1 z.2 -
              1|)
        ≤ NormalCrossing.secondaryWeight k' h' lam z.1 *
          ((1 + 2 ^ r) * (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)))
            + 2 ^ r * C / Real.log 2 ^ r *
              (NormalCrossing.secondaryScale k k' b z.1 ^ δ *
                  (z.2 ^ (lam - 1 - δ) * Real.exp (-(β * z.2 / 2)))
                + NormalCrossing.secondaryScale k k' b z.1 ^ (-δ) *
                  (z.2 ^ (lam - 1 + δ) * Real.exp (-(β * z.2 / 2))))) :=
          mul_le_mul_of_nonneg_left (frozen_inner_bound hC hA hn ht) hW0
      _ = _ := by
          linear_combination
            ((1 + 2 ^ r) * (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)))) * e0
            + (2 ^ r * C / Real.log 2 ^ r * (z.2 ^ (lam - 1 - δ) * Real.exp (-(β * z.2 / 2)))) * e1
            + (2 ^ r * C / Real.log 2 ^ r * (z.2 ^ (lam - 1 + δ) * Real.exp (-(β * z.2 / 2)))) * e2

/-- The exact identity behind the frozen approximation: for `n > 1` and bounded measurable
`ξ₀, φ₀` of the secondary variables,
`n^λ Z⁰(n, ξ₀, φ₀) / (log n)^r = γ ∫_v v^μ φ₀ ∫_t t^{λ-1} e^{-βt + β√t ξ₀(v)} R_n(t, v)`.
[Wat09, Theorem 4.6] with `a = n v^{2k'}` and Fubini. -/
private theorem frozen_identity (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    {ξ₀ φ₀ : (Fin m' → ℝ) → ℝ} {M P : ℝ} (hξm : Measurable ξ₀) (hφm : Measurable φ₀)
    (hξ : ∀ v ∈ cube m' b, |ξ₀ v| ≤ M) (hφ : ∀ v ∈ cube m' b, |φ₀ v| ≤ P) {n : ℝ} (hn : 1 < n) :
    n ^ lam / Real.log n ^ r *
        NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ₀ z.2) (fun z ↦ φ₀ z.2)
      = NormalCrossing.gammaConst k h lam b *
        ∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
            NormalCrossing.logRatio k k' b n v t := by
  obtain ⟨hh, hh', -, -⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec (le_refl (0 : ℝ))
  have hn0 : 0 < n := by linarith
  have hint := integrable_blockIntegral_integrand k k' (p := 0) (ξ := fun z ↦ ξ₀ z.2)
      (f := fun z ↦ φ₀ z.2)
    hh hh' hb hβ.le le_rfl hn0.le (hξm.comp measurable_snd) (hφm.comp measurable_snd)
    (fun z hz ↦ hξ z.2 hz.2) (fun z hz ↦ hφ z.2 hz.2)
  have hZ : NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ₀ z.2) (fun z ↦ φ₀ z.2)
      = ∫ z, potential k k' z ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' z) +
            Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ₀ z.2) *
          NormalCrossing.monomialWeight h h' z * φ₀ z.2
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) := by
    rw [NormalCrossing.blockIntegral, restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict]
    rfl
  rw [hZ, integral_prod_symm _ hint, ← integral_const_mul (n ^ lam / Real.log n ^ r),
    ← restrict_ocube_eq (m := m'), ← integral_const_mul (NormalCrossing.gammaConst k h lam b)]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)] with v hv
  exact frozen_inner hk hlam hlam0 hb hβ hξ hn fun j ↦ hv j (mem_univ j)

/-! ## The frozen error bound -/

/-- The scalar error is finite and tends to `0`: `R_n → 1` pointwise, dominated by
`C_r (1 + |log (A(v)/t)|^r)`, and dominated convergence. -/
theorem NormalCrossing.frozenError_tendsto (_hk : ∀ j, 0 < k j) (hlam0 : 0 < lam)
    (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β) :
    Tendsto (NormalCrossing.frozenError k k' h' lam b β) atTop (𝓝 0) := by
  obtain ⟨G, hGint, hG⟩ := exists_frozen_dominator (k := k) hlam0 hsec hb hβ
  set P := (volume.restrict (cube m' b)).prod (volume.restrict (Ioi (0 : ℝ))) with hP
  set Φ : ℝ → (Fin m' → ℝ) × ℝ → ℝ := fun n z ↦ NormalCrossing.secondaryWeight k' h' lam z.1 *
    (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) * |NormalCrossing.logRatio k k' b n z.1 z.2 - 1|)
        with hΦ
  have hΦmeas : ∀ n, AEStronglyMeasurable (Φ n) P := fun n ↦ by
    have hR := NormalCrossing.measurable_logRatio_uncurry (k := k) (k' := k') (b := b) n
    have hW : Measurable (NormalCrossing.secondaryWeight k' h' lam) := by
      unfold NormalCrossing.secondaryWeight
      exact Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _
    exact (by fun_prop : Measurable (Φ n)).aestronglyMeasurable
  have hbound : ∀ n : ℝ, 2 ≤ n → ∀ᵐ z ∂P, ‖Φ n z‖ ≤ G z := fun n hn ↦ by
    filter_upwards [ae_cube_prod_Ioi (m := m') b] with z hz
    exact hG n hn z hz.1 hz.2
  have hint : ∀ n : ℝ, 2 ≤ n → Integrable (Φ n) P := fun n hn ↦
    hGint.mono' (hΦmeas n) (hbound n hn)
  have heq : ∀ n : ℝ, 2 ≤ n → NormalCrossing.frozenError k k' h' lam b β n = ∫ z, Φ n z ∂P := by
    intro n hn
    rw [hP, integral_prod _ (hint n hn), NormalCrossing.frozenError]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    exact (integral_const_mul _ _).symm
  have hlim : Tendsto (fun n ↦ ∫ z, Φ n z ∂P) atTop (𝓝 0) := by
    have := tendsto_integral_filter_of_dominated_convergence (μ := P) (F := Φ)
      (f := fun _ ↦ 0) G (Eventually.of_forall hΦmeas)
      ((eventually_ge_atTop 2).mono hbound) hGint ?_
    · simpa using this
    filter_upwards [ae_cube_prod_Ioi (m := m') b] with z hz
    have hA : 0 < NormalCrossing.secondaryScale k k' b z.1 := NormalCrossing.secondaryScale_pos hb
        fun j ↦ (hz.1 j).1
    have := (((logRatio_tendsto hA hz.2).sub_const 1).abs.const_mul
      (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)))).const_mul
          (NormalCrossing.secondaryWeight k' h' lam z.1)
    simpa using this
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact (heq n hn).symm

/-- [Wat09, Theorem 4.9], frozen part, qualitative: for `n ≥ 2`, `|ξ₀| ≤ M`, `|φ₀| ≤ P`,
`|n^λ Z⁰(n, ξ₀, φ₀)/(log n)^r − Y(ξ₀, φ₀)| ≤ γ P e^{βM²/2} E(n)`. -/
theorem NormalCrossing.abs_frozen_sub_frozenLimit_le (hk : ∀ j, 0 < k j)
    (hlam : ∀ j, (h j + 1) / (2 * k j) = lam) (hlam0 : 0 < lam)
    (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    {ξ₀ φ₀ : (Fin m' → ℝ) → ℝ} {M P : ℝ} (hξm : Measurable ξ₀) (hφm : Measurable φ₀)
    (hξ : ∀ v ∈ cube m' b, |ξ₀ v| ≤ M) (hφ : ∀ v ∈ cube m' b, |φ₀ v| ≤ P) {n : ℝ} (hn : 2 ≤ n) :
    |n ^ lam / Real.log n ^ r * NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ₀ z.2)
        (fun z ↦ φ₀ z.2)
        - frozenLimit k h k' h' lam b β ξ₀ φ₀|
      ≤ NormalCrossing.gammaConst k h lam b * P * Real.exp (β * M ^ 2 / 2) *
          NormalCrossing.frozenError k k' h' lam
          b β n := by
  have hn1 : 1 < n := by linarith
  have hγ := gammaConst_pos h lam hk hb
  have hμ : ∀ j, -1 < h' j - 2 * k' j * lam := fun j ↦ by linarith [hsec j]
  rw [frozen_identity hk hlam hlam0 hsec hb hβ hξm hφm hξ hφ hn1, frozenLimit, ← mul_sub,
    abs_mul, abs_of_pos hγ, NormalCrossing.frozenError]
  -- measurability of the parametric integrals
  have hR := NormalCrossing.measurable_logRatio_uncurry (k := k) (k' := k') (b := b) (r := r) n
  have hGinf : Measurable fun p : (Fin m' → ℝ) × ℝ ↦
      p.2 ^ (lam - 1) * Real.exp (-(β * p.2) + β * Real.sqrt p.2 * ξ₀ p.1) := by fun_prop
  have hGn : Measurable fun p : (Fin m' → ℝ) × ℝ ↦
      p.2 ^ (lam - 1) * Real.exp (-(β * p.2) + β * Real.sqrt p.2 * ξ₀ p.1) *
        NormalCrossing.logRatio k k' b n p.1 p.2 := hGinf.mul hR
  have hJn := stronglyMeasurable_integral_Ioi hGn
  have hJinf := stronglyMeasurable_integral_Ioi hGinf
  have hwm := NormalCrossing.measurable_secondaryWeight (k' := k') (h' := h') (lam := lam)
  have hae : ∀ᵐ v ∂(volume.restrict (cube m' b)), ∀ j, v j ∈ Ioo 0 b := by
    rw [← restrict_ocube_eq]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo)] with v hv
    exact fun j ↦ hv j (mem_univ j)
  have hintE := NormalCrossing.integrable_frozenError_integrand (k := k) (h' := h') hlam0 hsec hb hβ
      hn1
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hφ 0 ⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩)
  -- integrability in `v` of the two terms
  have hwint : IntegrableOn (NormalCrossing.secondaryWeight k' h' lam) (cube m' b) :=
      integrableOn_cube_rpow hμ hb
  have hIinf : Integrable (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
      ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v))
      (volume.restrict (cube m' b)) := by
    refine (hwint.const_mul (P * (Real.exp (β * M ^ 2 / 2) *
      ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2))))).mono'
      ((hwm.stronglyMeasurable.mul hφm.stronglyMeasurable).mul hJinf).aestronglyMeasurable ?_
    filter_upwards [hae] with v hv
    have hvc : v ∈ cube m' b := mem_cube.2 fun j ↦ Ioo_subset_Icc_self (hv j)
    have hw := NormalCrossing.secondaryWeight_nonneg (k' := k') (h' := h') (lam := lam) fun j
        ↦ (hv j).1.le
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hw]
    calc NormalCrossing.secondaryWeight k' h' lam v * |φ₀ v| *
          |∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v)|
        ≤ NormalCrossing.secondaryWeight k' h' lam v * P * (Real.exp (β * M ^ 2 / 2) *
            ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hφ v hvc) hw)
            (NormalCrossing.abs_integral_rpow_mul_exp_frozen_le hlam0 hβ (hξ v hvc)) (abs_nonneg _)
            (mul_nonneg hw hP0)
      _ = _ := by ring
  have hIdiff : Integrable (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
      (∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
        NormalCrossing.logRatio k k' b n v t)
      - NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
        ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v))
      (volume.restrict (cube m' b)) := by
    refine (hintE.const_mul (P * Real.exp (β * M ^ 2 / 2))).mono'
      (((hwm.stronglyMeasurable.mul hφm.stronglyMeasurable).mul hJn).sub
        ((hwm.stronglyMeasurable.mul hφm.stronglyMeasurable).mul hJinf)).aestronglyMeasurable ?_
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs]
    exact frozen_pointwise_bound (k := k) (k' := k') (h' := h') hlam0 hb hβ hξ hφ hn1 hv
  have hIn : Integrable (fun v ↦ NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
      ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
        NormalCrossing.logRatio k k' b n v t) (volume.restrict (cube m' b)) := by
    refine (hIdiff.add hIinf).congr (Filter.Eventually.of_forall fun v ↦ ?_)
    simp only [Pi.add_apply]
    ring
  -- the estimate
  have key : |(∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
        ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) *
          NormalCrossing.logRatio k k' b n v t)
      - ∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
        ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v)|
      ≤ P * Real.exp (β * M ^ 2 / 2) * ∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v
          *
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) *
            |NormalCrossing.logRatio k k' b n v t - 1| := by
    rw [← integral_sub hIn hIinf, ← Real.norm_eq_abs, ← integral_const_mul]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun v ↦ norm_nonneg _) (hintE.const_mul _) ?_)
    filter_upwards [hae] with v hv
    rw [Real.norm_eq_abs]
    exact frozen_pointwise_bound (k := k) (k' := k') (h' := h') hlam0 hb hβ hξ hφ hn1 hv
  calc NormalCrossing.gammaConst k h lam b * |_| ≤ NormalCrossing.gammaConst k h lam b *
      (P * Real.exp (β * M ^ 2 / 2) *
        ∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v *
          ∫ t in Ioi 0, t ^ (lam - 1) * Real.exp (-(β * t / 2)) *
            |NormalCrossing.logRatio k k' b n v t - 1|) := mul_le_mul_of_nonneg_left key hγ.le
    _ = _ := by ring

end Frozen

/-- `|e^s − e^t| ≤ e^M |s − t|` for `s, t ≤ M`. No thesis counterpart. -/
theorem _root_.Real.abs_exp_sub_exp_le {s t M : ℝ} (hs : s ≤ M) (ht : t ≤ M) :
    |Real.exp s - Real.exp t| ≤ Real.exp M * |s - t| := by
  have key : ∀ s t : ℝ, t ≤ s → s ≤ M → Real.exp s - Real.exp t ≤ Real.exp M * (s - t) := by
    intro s t hts hsM
    have h1 : Real.exp t = Real.exp s * Real.exp (t - s) := by rw [← Real.exp_add]; ring_nf
    have h2 := Real.add_one_le_exp (t - s)
    have h3 : Real.exp s ≤ Real.exp M := Real.exp_le_exp.mpr hsM
    have h4 := Real.exp_pos s
    nlinarith
  rcases le_total t s with hts | hst
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hts)),
      abs_of_nonneg (sub_nonneg.mpr hts)]
    exact key s t hts hs
  · rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hst)), abs_sub_comm s,
      abs_of_nonneg (sub_nonneg.mpr hst)]
    exact key t s hst ht

/-- The scalar estimate behind the unfreezing step of [Wat09, Theorem 4.9]:
`|e^{cx} a − e^{cy} b| ≤ e^{cM} (|a − b| + c |b| |x − y|)` for `c, M ≥ 0`, `|x|, |y| ≤ M`.
No thesis counterpart ([Hit26] uses the mean value theorem instead). -/
private theorem abs_exp_mul_sub_exp_mul_le {c M x y a b : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ M)
    (hy : |y| ≤ M) :
    |Real.exp (c * x) * a - Real.exp (c * y) * b|
      ≤ Real.exp (c * M) * (|a - b| + c * |b| * |x - y|) := by
  have hcx : c * x ≤ c * M := mul_le_mul_of_nonneg_left ((le_abs_self x).trans hx) hc
  have hcy : c * y ≤ c * M := mul_le_mul_of_nonneg_left ((le_abs_self y).trans hy) hc
  have h1 : |Real.exp (c * x)| ≤ Real.exp (c * M) := by
    rw [abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr hcx
  have h2 : |Real.exp (c * x) - Real.exp (c * y)| ≤ Real.exp (c * M) * (c * |x - y|) := by
    have := Real.abs_exp_sub_exp_le hcx hcy
    rwa [← mul_sub, abs_mul, abs_of_nonneg hc] at this
  calc |Real.exp (c * x) * a - Real.exp (c * y) * b|
      = |Real.exp (c * x) * (a - b) + (Real.exp (c * x) - Real.exp (c * y)) * b| := by ring_nf
    _ ≤ |Real.exp (c * x) * (a - b)| + |(Real.exp (c * x) - Real.exp (c * y)) * b| :=
        abs_add_le _ _
    _ = |Real.exp (c * x)| * |a - b| + |Real.exp (c * x) - Real.exp (c * y)| * |b| := by
        rw [abs_mul, abs_mul]
    _ ≤ Real.exp (c * M) * |a - b| + Real.exp (c * M) * (c * |x - y|) * |b| := by
        gcongr
    _ = _ := by ring

/-! ## Coordinate blocks and the threshold of a general exponent vector

No thesis counterpart. `normalCrossingIntegral₀` for the shifted weight `h + e_j` is bounded by
[Wat09, Theorem 4.7] after regrouping the coordinates by their new ratios. -/

section SumBlock

variable {d r s : ℕ} (e : Fin r ⊕ Fin s ≃ Fin d)

/-- The block coordinates `(u ∘ e ∘ inl, u ∘ e ∘ inr) ↦ u`, as a measurable equivalence.
No thesis counterpart. -/
@[expose] noncomputable def _root_.MeasurableEquiv.sumBlockEquiv : (Fin r → ℝ) × (Fin s → ℝ) ≃ᵐ
    (Fin d → ℝ) :=
  (MeasurableEquiv.sumPiEquivProdPi fun _ : Fin r ⊕ Fin s ↦ ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) e)

@[simp] theorem _root_.MeasurableEquiv.sumBlockEquiv_apply_inl (z : (Fin r → ℝ) × (Fin s → ℝ))
    (i : Fin r) :
    MeasurableEquiv.sumBlockEquiv e z (e (Sum.inl i)) = z.1 i :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) e
    ((MeasurableEquiv.sumPiEquivProdPi fun _ : Fin r ⊕ Fin s ↦ ℝ).symm z) (Sum.inl i)

@[simp] theorem _root_.MeasurableEquiv.sumBlockEquiv_apply_inr (z : (Fin r → ℝ) × (Fin s → ℝ))
    (i : Fin s) :
    MeasurableEquiv.sumBlockEquiv e z (e (Sum.inr i)) = z.2 i :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) e
    ((MeasurableEquiv.sumPiEquivProdPi fun _ : Fin r ⊕ Fin s ↦ ℝ).symm z) (Sum.inr i)

private theorem sumBlockEquiv_measurePreserving :
    MeasurePreserving (MeasurableEquiv.sumBlockEquiv e) volume volume :=
  (volume_measurePreserving_sumPiEquivProdPi_symm _).trans
    (volume_measurePreserving_piCongrLeft _ _)

private theorem sumBlockEquiv_preimage_cube (b : ℝ) :
    MeasurableEquiv.sumBlockEquiv e ⁻¹' cube d b = cube r b ×ˢ cube s b := by
  ext z
  simp only [mem_preimage, mem_cube, mem_prod]
  constructor
  · intro H
    exact ⟨fun i ↦ by simpa using H (e (Sum.inl i)), fun i ↦ by simpa using H (e (Sum.inr i))⟩
  · rintro ⟨H₁, H₂⟩ j
    obtain ⟨t, rfl⟩ := e.surjective j
    rcases t with i | i
    · simpa using H₁ i
    · simpa using H₂ i

private theorem prod_sumBlockEquiv (f : Fin d → ℝ → ℝ) (z : (Fin r → ℝ) × (Fin s → ℝ)) :
    ∏ j, f j (MeasurableEquiv.sumBlockEquiv e z j)
      = (∏ i, f (e (Sum.inl i)) (z.1 i)) * ∏ i, f (e (Sum.inr i)) (z.2 i) := by
  rw [← e.prod_comp fun j ↦ f j (MeasurableEquiv.sumBlockEquiv e z j), Fintype.prod_sum_type]
  simp

/-- The integrand of `Z^q(n)` written on `ℝ^d`. No thesis counterpart. -/
@[expose] noncomputable def cubeIntegrand {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ) (β q n : ℝ)
    (u : Fin d → ℝ) : ℝ :=
  (∏ j, u j ^ (2 * k j)) ^ q * Real.exp (-(n * β * ∏ j, u j ^ (2 * k j))) * ∏ j, u j ^ h j

/-- The integral of `u^{2kq} e^{-nβ u^{2k}} u^h` over `[0, b]^d` is `Z^q(n)` for the block
data `(k ∘ e ∘ inl, h ∘ e ∘ inl, k ∘ e ∘ inr, h ∘ e ∘ inr)`. Real-exponent, `q`-general
version of `integral_cube_eq_blockIntegral₀`. -/
private theorem NormalCrossing.integral_cube_eq_blockIntegral₀_sum (k : Fin d → ℕ) (h : Fin d → ℝ)
    (b β q n : ℝ) :
    ∫ u in cube d b, cubeIntegrand k h β q n u
      = NormalCrossing.blockIntegral₀ (fun i ↦ k (e (Sum.inl i))) (fun i ↦ h (e (Sum.inl i)))
          (fun i ↦ k (e (Sum.inr i)))
          (fun i ↦ h (e (Sum.inr i))) b β q n := by
  rw [← (sumBlockEquiv_measurePreserving e).setIntegral_preimage_emb
    (MeasurableEquiv.sumBlockEquiv e).measurableEmbedding, sumBlockEquiv_preimage_cube,
        NormalCrossing.blockIntegral₀]
  congr 1
  funext z
  simp only [cubeIntegrand, potential, NormalCrossing.monomialWeight]
  rw [prod_sumBlockEquiv e fun j x ↦ x ^ (2 * k j), prod_sumBlockEquiv e fun j x ↦ x ^ h j]

end SumBlock

/-! ## Threshold and multiplicity of a bare exponent vector

The `λ_α`, `m_α` of `ResolutionAtlas.chartRlct` / `chartMult` for a bare pair `(k, h)`.
No thesis counterpart as separate definitions. -/

section Threshold

variable {d : ℕ} (k : Fin d → ℕ) (h : Fin d → ℝ)

/-- The active coordinates `{j | k_j > 0}`. -/
@[expose] def activeIdx : Finset (Fin d) := Finset.univ.filter fun j ↦ 0 < k j

/-- The ratio `(h_j + 1) / (2 k_j)`. -/
@[expose] noncomputable def expRatio (j : Fin d) : ℝ := (h j + 1) / (2 * k j)

variable (hact : (activeIdx k).Nonempty)

/-- The threshold `min_{k_j > 0} (h_j + 1) / (2 k_j)`. -/
@[expose] noncomputable def expThreshold : ℝ := (activeIdx k).inf' hact (expRatio k h)

/-- The primary coordinates: the active coordinates attaining the threshold. -/
@[expose] noncomputable def expPrimary : Finset (Fin d) :=
  (activeIdx k).filter fun j ↦ expRatio k h j = expThreshold k h hact

/-- The multiplicity: the number of primary coordinates. -/
@[expose] noncomputable def expMult : ℕ := (expPrimary k h hact).card

private theorem expMult_pos : 0 < expMult k h hact := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hact (expRatio k h)
  exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr ⟨hj, hjeq.symm⟩⟩

theorem expThreshold_le {j : Fin d} (hj : 0 < k j) : expThreshold k h hact ≤ expRatio k h j :=
  Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

private theorem expThreshold_pos (hh : ∀ j, -1 < h j) : 0 < expThreshold k h hact := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' hact (expRatio k h)
  have hk : (0 : ℝ) < k j := by exact_mod_cast (Finset.mem_filter.mp hj).2
  rw [expThreshold, hjeq, expRatio]
  have : 0 < h j + 1 := by linarith [hh j]
  positivity

/-- [Wat09, Theorem 4.7] for an arbitrary exponent vector ([Hit26,
Theorem 3.2.6] in coordinate form): with `thr` the minimum of `(h_j +
1)/(2 k_j)` over the active coordinates and `mlt` the number of active coordinates attaining it,

`a₁ (log n)^{mlt-1} / n^{thr+q} ≤ ∫_{[0,b]^d} u^{2kq} e^{-nβ u^{2k}} u^h
  ≤ a₂ (log n)^{mlt-1} / n^{thr+q}`

for `n ≥ 2`. The coordinates are permuted into the block form of `normalCrossingIntegral₀` as in
`ResolutionAtlas.chartIntegral_le_blockIntegral₀`; coordinates with `k_j = 0` are
secondary. -/
theorem integral_cube_bounds_general (hh : ∀ j, -1 < h j) {b β q : ℝ} (hb : 0 < b)
    (hβ : 0 < β) (hq : 0 ≤ q) :
    ∃ a₁ > 0, ∃ a₂ > 0, ∀ n : ℝ, 2 ≤ n →
      a₁ * Real.log n ^ (expMult k h hact - 1) / n ^ (expThreshold k h hact + q)
        ≤ ∫ u in cube d b, cubeIntegrand k h β q n u ∧
      ∫ u in cube d b, cubeIntegrand k h β q n u
        ≤ a₂ * Real.log n ^ (expMult k h hact - 1) / n ^ (expThreshold k h hact + q) := by
  obtain ⟨r, hr⟩ : ∃ r, r + 1 = expMult k h hact :=
    ⟨_, Nat.succ_pred_eq_of_pos (expMult_pos k h hact)⟩
  have hcardP : Fintype.card {j // j ∈ expPrimary k h hact} = r + 1 := by
    rw [Fintype.card_coe, hr]; rfl
  have hcardS : Fintype.card {j // j ∉ expPrimary k h hact} = d - (r + 1) := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardP]
  let eP : Fin (r + 1) ≃ {j // j ∈ expPrimary k h hact} := (Fintype.equivFinOfCardEq hcardP).symm
  let eS : Fin (d - (r + 1)) ≃ {j // j ∉ expPrimary k h hact} :=
    (Fintype.equivFinOfCardEq hcardS).symm
  have hk₁ : ∀ i, 0 < k (Equiv.blockIndex eP eS (Sum.inl i)) := fun i ↦
    (Finset.mem_filter.mp (Finset.mem_filter.mp (eP i).2).1).2
  have hlam : ∀ i, (h (Equiv.blockIndex eP eS (Sum.inl i)) + 1) /
      (2 * k (Equiv.blockIndex eP eS (Sum.inl i)))
      = expThreshold k h hact := fun i ↦ (Finset.mem_filter.mp (eP i).2).2
  have hsec : ∀ i, 2 * k (Equiv.blockIndex eP eS (Sum.inr i)) * expThreshold k h hact
      < h (Equiv.blockIndex eP eS (Sum.inr i)) + 1 := by
    intro i
    have hj : (eS i : Fin d) ∉ expPrimary k h hact := (eS i).2
    simp only [Equiv.blockIndex_inr]
    generalize (eS i : Fin d) = j at hj ⊢
    by_cases hkj : 0 < k j
    · have hact' : j ∈ activeIdx k := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hkj⟩
      have hle : expThreshold k h hact ≤ expRatio k h j := Finset.inf'_le _ hact'
      have hne : expRatio k h j ≠ expThreshold k h hact := fun heq ↦
        hj (Finset.mem_filter.mpr ⟨hact', heq⟩)
      have hlt : expThreshold k h hact < (h j + 1) / (2 * k j) := lt_of_le_of_ne hle hne.symm
      rw [lt_div_iff₀ (by positivity)] at hlt
      linarith
    · have hk0 : k j = 0 := by omega
      simp only [hk0, Nat.cast_zero, mul_zero, zero_mul]
      linarith [hh j]
  obtain ⟨a₁, ha₁, hZ₁⟩ :=
    blockIntegral₀_lower_bound hk₁ hlam (expThreshold_pos k h hact hh) hsec hb hβ hq
  obtain ⟨a₂, ha₂, hZ₂⟩ :=
    blockIntegral₀_upper_bound hk₁ hlam (expThreshold_pos k h hact hh) hsec hb hβ hq
  refine ⟨a₁, ha₁, a₂, ha₂, fun n hn ↦ ?_⟩
  rw [integral_cube_eq_blockIntegral₀_sum (Equiv.blockIndex eP eS), ← hr, Nat.add_sub_cancel]
  exact ⟨hZ₁ n (by linarith), hZ₂ n hn⟩

/-- The upper bound of `integral_cube_bounds_general`. -/
private theorem integral_cube_upper_bound_general (hh : ∀ j, -1 < h j) {b β q : ℝ} (hb : 0 < b)
    (hβ : 0 < β) (hq : 0 ≤ q) :
    ∃ C, ∀ n : ℝ, 2 ≤ n →
      ∫ u in cube d b, cubeIntegrand k h β q n u
        ≤ C * Real.log n ^ (expMult k h hact - 1) / n ^ (expThreshold k h hact + q) := by
  obtain ⟨a₁, -, a₂, -, H⟩ := integral_cube_bounds_general k h hact hh hb hβ hq
  exact ⟨a₂, fun n hn ↦ (H n hn).2⟩

end Threshold

/-! ## `Z^q(n)` as a cube integral of the concatenated data -/

/-- `Z^q(n)` for `(k, h, k', h')` is the cube integral on `ℝ^{m+m'}` of the concatenated
exponent vectors. No thesis counterpart. -/
private theorem NormalCrossing.blockIntegral₀_eq_integral_cube_append {m m' : ℕ} (k : Fin m → ℕ)
    (h : Fin m → ℝ)
    (k' : Fin m' → ℕ)
    (h' : Fin m' → ℝ) (b β q n : ℝ) :
    NormalCrossing.blockIntegral₀ k h k' h' b β q n
      = ∫ u in cube (m + m') b, cubeIntegrand (Fin.append k k') (Fin.append h h') β q n u := by
  rw [integral_cube_eq_blockIntegral₀_sum finSumFinEquiv]
  simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.append_left,
    Fin.append_right]

/-- `Z^q(n) ≥ 0`. No thesis counterpart. -/
private theorem NormalCrossing.blockIntegral₀_nonneg {m m' : ℕ} (k : Fin m → ℕ) (h : Fin m → ℝ)
    (k' : Fin m' → ℕ)
    (h' : Fin m' → ℝ)
    (b β q n : ℝ) : 0 ≤ NormalCrossing.blockIntegral₀ k h k' h' b β q n := by
  unfold NormalCrossing.blockIntegral₀
  refine setIntegral_nonneg (measurableSet_Icc.prod
    measurableSet_Icc) fun z hz ↦ ?_
  have hu : ∀ j, 0 ≤ z.1 j := fun j ↦ hz.1.1 j
  have hv : ∀ j, 0 ≤ z.2 j := fun j ↦ hz.2.1 j
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (potential_nonneg k k' hu hv) _)
    (Real.exp_pos _).le) (monomialWeight_nonneg h h' hu hv)

/-! ## The shifted weight `u^{h + e_j}` -/

section Shifted

variable {r m' : ℕ} {k : Fin (r + 1) → ℕ} {h : Fin (r + 1) → ℝ} {k' : Fin m' → ℕ}
  {h' : Fin m' → ℝ} {lam : ℝ}

/-- After the shift `h_j ↦ h_j + 1`, every active coordinate of the concatenated data has
ratio `≥ λ`, with equality only at the unshifted primary coordinates `i' ≠ j`. -/
private theorem shifted_ratio (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (j : Fin (r + 1)) (i : Fin (r + 1 + m'))
    (hi : 0 < Fin.append k k' i) :
    lam ≤ expRatio (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') i ∧
      (expRatio (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') i = lam →
        ∃ i' : Fin (r + 1), i' ≠ j ∧ i = Fin.castAdd m' i') := by
  induction i using Fin.addCases with
  | left i' =>
    simp only [expRatio, Fin.append_left] at hi ⊢
    have hki : (0 : ℝ) < k i' := by exact_mod_cast hi
    by_cases hij : i' = j
    · subst hij
      rw [Function.update_self]
      have key : h i' + 1 = lam * (2 * k i') := by
        have := hlam i'
        rwa [div_eq_iff (by positivity)] at this
      have hlt : lam < (h i' + 1 + 1) / (2 * k i') := by
        rw [lt_div_iff₀ (by positivity)]; linarith
      exact ⟨hlt.le, fun heq ↦ absurd heq hlt.ne'⟩
    · rw [Function.update_of_ne hij]
      exact ⟨(hlam i').ge, fun _ ↦ ⟨i', hij, rfl⟩⟩
  | right i' =>
    simp only [expRatio, Fin.append_right] at hi ⊢
    have hki : (0 : ℝ) < k' i' := by exact_mod_cast hi
    have hlt : lam < (h' i' + 1) / (2 * k' i') := by
      rw [lt_div_iff₀ (by positivity)]; linarith [hsec i']
    exact ⟨hlt.le, fun heq ↦ absurd heq hlt.ne'⟩

end Shifted

/-- The limit computation behind `NormalCrossing.shifted_negligible`: if `0 ≤ F n ≤ C (log
n)^{mlt-1} / n^{thr+q}`
for `n ≥ 2` with `thr ≥ λ`, `mlt ≥ 1`, and `mlt ≤ r` whenever `thr = λ`, then
`n^{λ+q} F n / (log n)^r → 0`. No thesis counterpart. -/
theorem NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le {F : ℝ → ℝ} {C lam q thr : ℝ} {r mlt : ℕ}
    (hC0 : 0 ≤ C) (hF0 : ∀ n, 0 ≤ F n)
    (hF : ∀ n : ℝ, 2 ≤ n → F n ≤ C * Real.log n ^ (mlt - 1) / n ^ (thr + q))
    (hthr : lam ≤ thr) (hmlt1 : 1 ≤ mlt) (hmlt : thr = lam → mlt ≤ r) :
    Tendsto (fun n : ℝ ↦ n ^ (lam + q) / Real.log n ^ r * F n) atTop (𝓝 0) := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hlow : ∀ᶠ n : ℝ in atTop, 0 ≤ n ^ (lam + q) / Real.log n ^ r * F n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : 0 < Real.log n := Real.log_pos (by linarith)
    exact mul_nonneg (by positivity) (hF0 n)
  rcases hthr.lt_or_eq with hlt | heq
  · -- `thr > λ`: the extra power `n^{thr-λ}` beats every power of `log n`.
    have hδ : 0 < thr - lam := sub_pos.mpr hlt
    have hg : Tendsto (fun n : ℝ ↦ C / Real.log 2 ^ r *
        (Real.log n ^ (mlt - 1) / n ^ (thr - lam))) atTop (𝓝 0) := by
      have := (isLittleO_log_rpow_rpow_atTop ((mlt - 1 : ℕ) : ℝ) hδ).tendsto_div_nhds_zero
      simp only [Real.rpow_natCast] at this
      simpa using tendsto_const_nhds.mul this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg hlow ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : 0 < Real.log n := Real.log_pos (by linarith)
    have hnq : 0 < n ^ (lam + q) := Real.rpow_pos_of_pos hn0 _
    have hN : 0 < n ^ (thr - lam) := Real.rpow_pos_of_pos hn0 _
    have hpow : n ^ (thr + q) = n ^ (lam + q) * n ^ (thr - lam) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    have hlog2 : Real.log 2 ^ r ≤ Real.log n ^ r :=
      pow_le_pow_left₀ hl2.le (Real.log_le_log two_pos hn) r
    calc n ^ (lam + q) / Real.log n ^ r * F n
        ≤ n ^ (lam + q) / Real.log n ^ r * (C * Real.log n ^ (mlt - 1) / n ^ (thr + q)) :=
          mul_le_mul_of_nonneg_left (hF n hn) (by positivity)
      _ = C * (Real.log n ^ (mlt - 1) / n ^ (thr - lam)) / Real.log n ^ r := by
          rw [hpow]; field_simp
      _ ≤ C * (Real.log n ^ (mlt - 1) / n ^ (thr - lam)) / Real.log 2 ^ r :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlog2
      _ = _ := by ring
  · -- `thr = λ`: then `mlt ≤ r`, and `(log n)^{mlt-1} / (log n)^r ≤ C' / log n`.
    have hmr : mlt ≤ r := hmlt heq.symm
    rw [← heq] at hF
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨C', -, hC'⟩ := Real.exists_log_pow_le (show mlt - 1 ≤ r' by omega)
    have hg : Tendsto (fun n : ℝ ↦ C * C' / Real.log n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hg hlow ?_
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : 0 < Real.log n := Real.log_pos (by linarith)
    have hnq : 0 < n ^ (lam + q) := Real.rpow_pos_of_pos hn0 _
    calc n ^ (lam + q) / Real.log n ^ (r' + 1) * F n
        ≤ n ^ (lam + q) / Real.log n ^ (r' + 1) *
            (C * Real.log n ^ (mlt - 1) / n ^ (lam + q)) :=
          mul_le_mul_of_nonneg_left (hF n hn) (by positivity)
      _ = C * Real.log n ^ (mlt - 1) / Real.log n ^ (r' + 1) := by field_simp
      _ ≤ C * (C' * Real.log n ^ r') / Real.log n ^ (r' + 1) := by
          gcongr
          exact hC' n hn
      _ = C * C' / Real.log n := by rw [pow_succ]; field_simp

section Unfreeze

variable {r m' : ℕ} {k : Fin (r + 1) → ℕ} {h : Fin (r + 1) → ℝ} {k' : Fin m' → ℕ}
  {h' : Fin m' → ℝ} {lam b β : ℝ}

/-- Shifting one primary exponent by `1` multiplies the weight by that coordinate:
`u^{h + e_j} v^{h'} = u_j · u^h v^{h'}` for `u_j ≠ 0`. No thesis counterpart. -/
theorem NormalCrossing.monomialWeight_update {m m' : ℕ} (h : Fin m → ℝ) (h' : Fin m' → ℝ)
    (j : Fin m)
    {z : (Fin m → ℝ) × (Fin m' → ℝ)} (hz : z.1 j ≠ 0) :
    NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z = z.1 j *
        NormalCrossing.monomialWeight h h' z := by
  unfold NormalCrossing.monomialWeight
  have : ∏ i, z.1 i ^ Function.update h j (h j + 1) i
      = ∏ i, (z.1 i ^ h i * if i = j then z.1 i else 1) := by
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    by_cases hij : i = j
    · subst hij; rw [Function.update_self, ite_eq_left rfl, Real.rpow_add_one hz]
    · rw [Function.update_of_ne hij, ite_eq_right hij, mul_one]
  rw [this, Finset.prod_mul_distrib, Finset.prod_ite_eq', ite_eq_left (Finset.mem_univ _)]
  ring

/-- The pointwise estimate behind the unfreezing step, on the open cube. No thesis
counterpart as a separate statement. -/
private theorem unfreeze_pointwise (hb : 0 < b) (hβ : 0 < β)
    {ξ φ : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ} {M P Lξ Lφ : ℝ}
    (hξ : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z| ≤ M)
    (hφ : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z| ≤ P)
    (hξL : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z - ξ (0, z.2)| ≤ Lξ * ∑ j, z.1 j)
    (hφL : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z - φ (0, z.2)| ≤ Lφ * ∑ j, z.1 j)
    {n : ℝ} (hn : 0 ≤ n) {z : (Fin (r + 1) → ℝ) × (Fin m' → ℝ)}
    (hz : (∀ j, z.1 j ∈ Ioo 0 b) ∧ ∀ j, z.2 j ∈ Ioo 0 b) :
    |potential k k' z ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' z) +
            Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
          NormalCrossing.monomialWeight h h' z * φ z
        - potential k k' z ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' z) +
            Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ (0, z.2)) *
          NormalCrossing.monomialWeight h h' z * φ (0, z.2)|
      ≤ Real.exp (β * M ^ 2 / 2) * ∑ j,
          (Lφ * (potential k k' z ^ (0 : ℝ) *
              Real.exp (-(n * (β / 2) * potential k k' z)) *
              NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z) +
            β * P * Lξ * Real.sqrt n * (potential k k' z ^ (1 / 2 : ℝ) *
              Real.exp (-(n * (β / 2) * potential k k' z)) *
              NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z)) := by
  have hu : ∀ j, 0 < z.1 j := fun j ↦ (hz.1 j).1
  have hv : ∀ j, 0 < z.2 j := fun j ↦ (hz.2 j).1
  have hzS : z ∈ cube (r + 1) b ×ˢ cube m' b :=
    ⟨mem_cube.2 fun j ↦ Ioo_subset_Icc_self (hz.1 j), mem_cube.2 fun j ↦ Ioo_subset_Icc_self
        (hz.2 j)⟩
  have h0S : ((0 : Fin (r + 1) → ℝ), z.2) ∈ cube (r + 1) b ×ˢ cube m' b :=
    ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, hzS.2⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hξ z hzS)
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hφ z hzS)
  have hLξ : 0 ≤ Lξ * ∑ j, z.1 j := (abs_nonneg _).trans (hξL z hzS)
  have hLφ : 0 ≤ Lφ * ∑ j, z.1 j := (abs_nonneg _).trans (hφL z hzS)
  have hupd : ∀ j, NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z
      = z.1 j * NormalCrossing.monomialWeight h h' z := fun j ↦ monomialWeight_update h h' j
          (hu j).ne'
  set K := potential k k' z
  set w := NormalCrossing.monomialWeight h h' z
  have hK0 : 0 ≤ K := potential_nonneg k k' (fun j ↦ (hu j).le) fun j ↦ (hv j).le
  have hw0 : 0 ≤ w := monomialWeight_nonneg h h' (fun j ↦ (hu j).le) fun j ↦ (hv j).le
  have hc : 0 ≤ Real.sqrt n * β * Real.sqrt K := by positivity
  -- the scalar estimate
  have hsc := abs_exp_mul_sub_exp_mul_le (a := φ z) (b := φ (0, z.2)) hc (hξ z hzS) (hξ _ h0S)
  -- the exponent estimate `e^{-nβK} e^{√n β √K M} ≤ e^{-nβK/2} e^{βM²/2}`
  have hE : Real.exp (-(n * β * K)) * Real.exp (Real.sqrt n * β * Real.sqrt K * M)
      ≤ Real.exp (-(n * (β / 2) * K)) * Real.exp (β * M ^ 2 / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (NormalCrossing.exponent_bounds hK0 hn hβ.le (abs_of_nonneg hM0).le).2
  -- the Lipschitz estimates
  have hdiff : |φ z - φ (0, z.2)| + Real.sqrt n * β * Real.sqrt K * |φ (0, z.2)| *
        |ξ z - ξ (0, z.2)|
      ≤ Lφ * ∑ j, z.1 j + Real.sqrt n * β * Real.sqrt K * P * (Lξ * ∑ j, z.1 j) :=
    add_le_add (hφL z hzS)
      (mul_le_mul (mul_le_mul_of_nonneg_left (hφ _ h0S) hc) (hξL z hzS) (abs_nonneg _)
        (by positivity))
  have hnn : 0 ≤ Lφ * ∑ j, z.1 j + Real.sqrt n * β * Real.sqrt K * P * (Lξ * ∑ j, z.1 j) :=
    add_nonneg hLφ (mul_nonneg (mul_nonneg hc hP0) hLξ)
  -- rewrite the right-hand side
  have hR : Real.exp (β * M ^ 2 / 2) * ∑ j,
        (Lφ * (K ^ (0 : ℝ) * Real.exp (-(n * (β / 2) * K)) *
            NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z) +
          β * P * Lξ * Real.sqrt n * (K ^ (1 / 2 : ℝ) * Real.exp (-(n * (β / 2) * K)) *
            NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z))
      = w * (Real.exp (-(n * (β / 2) * K)) * Real.exp (β * M ^ 2 / 2)) *
          (Lφ * ∑ j, z.1 j + Real.sqrt n * β * Real.sqrt K * P * (Lξ * ∑ j, z.1 j)) := by
    simp only [hupd, Real.rpow_zero, one_mul]
    have hterm : ∀ i, Lφ * (Real.exp (-(n * (β / 2) * K)) * (z.1 i * w)) +
        β * P * Lξ * Real.sqrt n *
          (K ^ (1 / 2 : ℝ) * Real.exp (-(n * (β / 2) * K)) * (z.1 i * w))
        = z.1 i * (w * Real.exp (-(n * (β / 2) * K)) *
            (Lφ + β * P * Lξ * Real.sqrt n * K ^ (1 / 2 : ℝ))) := fun i ↦ by ring
    rw [Finset.sum_congr rfl fun i _ ↦ hterm i, ← Finset.sum_mul, Real.sqrt_eq_rpow K]
    ring
  have hL : Real.exp (-(n * β * K) + Real.sqrt n * β * Real.sqrt K * ξ z) * w * φ z
        - Real.exp (-(n * β * K) + Real.sqrt n * β * Real.sqrt K * ξ (0, z.2)) * w * φ (0, z.2)
      = w * Real.exp (-(n * β * K)) *
          (Real.exp (Real.sqrt n * β * Real.sqrt K * ξ z) * φ z
            - Real.exp (Real.sqrt n * β * Real.sqrt K * ξ (0, z.2)) * φ (0, z.2)) := by
    rw [Real.exp_add, Real.exp_add]; ring
  rw [hR]
  simp only [Real.rpow_zero, one_mul]
  rw [hL, abs_mul, abs_of_nonneg (mul_nonneg hw0 (Real.exp_pos _).le)]
  calc w * Real.exp (-(n * β * K)) *
        |Real.exp (Real.sqrt n * β * Real.sqrt K * ξ z) * φ z
          - Real.exp (Real.sqrt n * β * Real.sqrt K * ξ (0, z.2)) * φ (0, z.2)|
      ≤ w * Real.exp (-(n * β * K)) * (Real.exp (Real.sqrt n * β * Real.sqrt K * M) *
          (|φ z - φ (0, z.2)| + Real.sqrt n * β * Real.sqrt K * |φ (0, z.2)| *
            |ξ z - ξ (0, z.2)|)) :=
        mul_le_mul_of_nonneg_left hsc (mul_nonneg hw0 (Real.exp_pos _).le)
    _ ≤ w * Real.exp (-(n * β * K)) * (Real.exp (Real.sqrt n * β * Real.sqrt K * M) *
          (Lφ * ∑ j, z.1 j + Real.sqrt n * β * Real.sqrt K * P * (Lξ * ∑ j, z.1 j))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le)
          (mul_nonneg hw0 (Real.exp_pos _).le)
    _ = w * (Real.exp (-(n * β * K)) * Real.exp (Real.sqrt n * β * Real.sqrt K * M)) *
          (Lφ * ∑ j, z.1 j + Real.sqrt n * β * Real.sqrt K * P * (Lξ * ∑ j, z.1 j)) := by
        ring
    _ ≤ _ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE hw0) hnn

/-- [Wat09, Theorem 4.9], unfreezing part: if `ξ, φ` are bounded by `M, P` and Lipschitz in the
primary coordinates towards their traces `ξ(0, v), φ(0, v)` with constants `Lξ, Lφ`, then
`|Z⁰(n, ξ, φ) − Z⁰(n, ξ₀, φ₀)| ≤ e^{βM²/2} Σ_j (Lφ T_j^0(n) + β P Lξ √n T_j^{1/2}(n))`, where
`T_j^q(n) = Z^q(n)` at inverse temperature `β/2` with weight `u^{h + e_j}`
([Hit26]'s `Z̃_j^p(n/2)`). -/
theorem NormalCrossing.abs_blockIntegral_sub_frozen_le (hk : ∀ j, 0 < k j)
    (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    {ξ φ : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ} {M P Lξ Lφ : ℝ}
    (hξm : Measurable ξ) (hφm : Measurable φ)
    (hξ : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z| ≤ M)
    (hφ : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z| ≤ P)
    (hξL : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z - ξ (0, z.2)| ≤ Lξ * ∑ j, z.1 j)
    (hφL : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z - φ (0, z.2)| ≤ Lφ * ∑ j, z.1 j)
    {n : ℝ} (hn : 0 ≤ n) :
    |NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ
        - NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2)) (fun z ↦ φ (0, z.2))|
      ≤ Real.exp (β * M ^ 2 / 2) * ∑ j,
          (Lφ * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n
              +
            β * P * Lξ * Real.sqrt n *
              NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2)
                  (1 / 2) n) := by
  obtain ⟨hh, hh', -, -⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec (p := 0) le_rfl
  have h0S : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b,
      ((0 : Fin (r + 1) → ℝ), z.2) ∈ cube (r + 1) b ×ˢ cube m' b :=
    fun z hz ↦ ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, hz.2⟩
  have hξ₀m : Measurable fun z : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) ↦ ξ (0, z.2) :=
    hξm.comp (measurable_const.prodMk measurable_snd)
  have hφ₀m : Measurable fun z : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) ↦ φ (0, z.2) :=
    hφm.comp (measurable_const.prodMk measurable_snd)
  have hhj : ∀ j i, -1 < Function.update h j (h j + 1) i := by
    intro j i
    rcases eq_or_ne i j with rfl | hij
    · rw [Function.update_self]; linarith [hh i]
    · rw [Function.update_of_ne hij]; exact hh i
  -- integrability of the two integrands and of the dominating function
  have hF := integrable_blockIntegral_integrand (p := 0) k k' hh hh' hb hβ.le le_rfl hn hξm hφm hξ
      hφ
  have hG := integrable_blockIntegral_integrand (p := 0) k k' hh hh' hb hβ.le le_rfl hn hξ₀m hφ₀m
    (fun z hz ↦ hξ _ (h0S z hz)) (fun z hz ↦ hφ _ (h0S z hz))
  have hT0 : ∀ j, Integrable (fun z ↦ potential k k' z ^ (0 : ℝ) *
      Real.exp (-(n * (β / 2) * potential k k' z)) *
      NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z)
      ((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) :=
    fun j ↦ integrable_blockIntegral₀_integrand k k' (hhj j) hh' hb (by positivity) le_rfl hn
  have hT1 : ∀ j, Integrable (fun z ↦ potential k k' z ^ (1 / 2 : ℝ) *
      Real.exp (-(n * (β / 2) * potential k k' z)) *
      NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z)
      ((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) :=
    fun j ↦ integrable_blockIntegral₀_integrand k k' (hhj j) hh' hb (by positivity) (by norm_num) hn
  have hTj : ∀ j ∈ (Finset.univ : Finset (Fin (r + 1))), Integrable (fun z ↦
      Lφ * (potential k k' z ^ (0 : ℝ) *
          Real.exp (-(n * (β / 2) * potential k k' z)) *
          NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z) +
        β * P * Lξ * Real.sqrt n * (potential k k' z ^ (1 / 2 : ℝ) *
          Real.exp (-(n * (β / 2) * potential k k' z)) *
          NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z))
      ((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) :=
    fun j _ ↦ ((hT0 j).const_mul _).add ((hT1 j).const_mul _)
  -- the integrals as integrals against the product of the open-cube measures
  have hZξ : ∀ ξ' φ' : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ,
      NormalCrossing.blockIntegral k h k' h' b β 0 n ξ' φ'
      = ∫ z, potential k k' z ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' z) +
            Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ' z) *
          NormalCrossing.monomialWeight h h' z * φ' z
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) := by
    intro ξ' φ'
    rw [NormalCrossing.blockIntegral, restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict]
    rfl
  rw [hZξ, hZξ, ← integral_sub hF hG]
  calc |∫ z, _ ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b)))|
      ≤ ∫ z, |potential k k' z ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' z) +
            Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
          NormalCrossing.monomialWeight h h' z * φ z
        - potential k k' z ^ (0 : ℝ) *
          Real.exp (-(n * β * potential k k' z) +
            Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ (0, z.2)) *
          NormalCrossing.monomialWeight h h' z * φ (0, z.2)|
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (μ := (volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b)))
          (fun z ↦ potential k k' z ^ (0 : ℝ) *
            Real.exp (-(n * β * potential k k' z) +
              Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
            NormalCrossing.monomialWeight h h' z * φ z
          - potential k k' z ^ (0 : ℝ) *
            Real.exp (-(n * β * potential k k' z) +
              Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ (0, z.2)) *
            NormalCrossing.monomialWeight h h' z * φ (0, z.2))
    _ ≤ ∫ z, Real.exp (β * M ^ 2 / 2) * ∑ j,
          (Lφ * (potential k k' z ^ (0 : ℝ) *
              Real.exp (-(n * (β / 2) * potential k k' z)) *
              NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z) +
            β * P * Lξ * Real.sqrt n * (potential k k' z ^ (1 / 2 : ℝ) *
              Real.exp (-(n * (β / 2) * potential k k' z)) *
              NormalCrossing.monomialWeight (Function.update h j (h j + 1)) h' z))
        ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) := by
        refine integral_mono_ae (hF.sub hG).abs
          ((integrable_finsetSum _ hTj).const_mul _) ?_
        filter_upwards [ae_prod_ocube (m := r + 1) (m' := m') b] with z hz
        exact unfreeze_pointwise hb hβ hξ hφ hξL hφL hn hz
    _ = _ := by
        rw [integral_const_mul, integral_finsetSum _ hTj]
        congr 1
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [integral_add ((hT0 j).const_mul _) ((hT1 j).const_mul _), integral_const_mul,
          integral_const_mul, blockIntegral₀_eq_integral_prod, blockIntegral₀_eq_integral_prod]

/-- [Wat09, Theorem 4.7] for the shifted weight `h + e_j`: `T_j^q(n) ≤ C (log n)^{mlt-1} /
n^{thr+q}` for `n ≥ 2`, where the threshold `thr` of the shifted data is `≥ λ`, with multiplicity
`mlt ≤ r` when `thr = λ`. After the shift `h_j ↦ h_j + 1` the coordinate `j` is no longer primary:
for `m ≥ 2` the threshold stays `λ` with multiplicity `m − 1`; for `m = 1` the threshold increases.
[Wat09, Theorem 4.7] on the regrouped coordinates. -/
theorem NormalCrossing.shifted_bound (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    (j : Fin (r + 1)) {q : ℝ} (hq : 0 ≤ q) :
    ∃ (thr : ℝ) (mlt : ℕ) (C : ℝ), 0 ≤ C ∧ lam ≤ thr ∧ 1 ≤ mlt ∧ (thr = lam → mlt ≤ r) ∧
      ∀ n : ℝ, 2 ≤ n → NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b
          (β / 2) q n
        ≤ C * Real.log n ^ (mlt - 1) / n ^ (thr + q) := by
  obtain ⟨hh, hh', -, -⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec hq
  have hact : (activeIdx (Fin.append k k')).Nonempty :=
    ⟨Fin.castAdd m' j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using hk j⟩⟩
  have hH : ∀ i, -1 < Fin.append (Function.update h j (h j + 1)) h' i := by
    intro i
    induction i using Fin.addCases with
    | left i' =>
      rw [Fin.append_left]
      by_cases hij : i' = j
      · subst hij; rw [Function.update_self]; linarith [hh i']
      · rw [Function.update_of_ne hij]; exact hh i'
    | right i' => rw [Fin.append_right]; exact hh' i'
  obtain ⟨C, hC⟩ := integral_cube_upper_bound_general (Fin.append k k')
    (Fin.append (Function.update h j (h j + 1)) h') hact hH hb (half_pos hβ) hq
  have hthr : lam ≤ expThreshold (Fin.append k k')
      (Fin.append (Function.update h j (h j + 1)) h') hact :=
    Finset.le_inf' hact _ fun i hi ↦
      (shifted_ratio hlam hsec j i (Finset.mem_filter.mp hi).2).1
  have hmlt : expThreshold (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') hact
        = lam →
      expMult (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') hact ≤ r := by
    intro heq
    have hsub : expPrimary (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') hact
        ⊆ (Finset.univ.erase j).map (Fin.castAddEmb m') := by
      intro i hi
      obtain ⟨hi, hieq⟩ := Finset.mem_filter.mp hi
      obtain ⟨i', hi'j, rfl⟩ :=
        (shifted_ratio hlam hsec j i (Finset.mem_filter.mp hi).2).2 (hieq.trans heq)
      exact Finset.mem_map.mpr ⟨i', Finset.mem_erase.mpr ⟨hi'j, Finset.mem_univ _⟩, rfl⟩
    calc expMult (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') hact
        ≤ ((Finset.univ.erase j).map (Fin.castAddEmb m')).card := Finset.card_le_card hsub
      _ = r := by
          rw [Finset.card_map, Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ,
            Fintype.card_fin, Nat.add_sub_cancel]
  have hC' : ∀ n : ℝ, 2 ≤ n →
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) q n
        ≤ max C 0 * Real.log n ^
            (expMult (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') hact - 1) /
          n ^ (expThreshold (Fin.append k k') (Fin.append (Function.update h j (h j + 1)) h') hact
            + q) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : 0 < Real.log n := Real.log_pos (by linarith)
    rw [blockIntegral₀_eq_integral_cube_append]
    refine (hC n hn).trans ?_
    gcongr
    exact le_max_left _ _
  exact ⟨_, _, max C 0, le_max_right C 0, hthr, expMult_pos _ _ hact, hmlt, hC'⟩

/-- The shifted-weight integrals are negligible: `n^{λ+q} T_j^q(n) / (log n)^r → 0`
(`NormalCrossing.shifted_bound` and `NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le`). -/
theorem NormalCrossing.shifted_negligible (hk : ∀ j, 0 < k j)
    (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    (j : Fin (r + 1)) {q : ℝ} (hq : 0 ≤ q) :
    Tendsto (fun n : ℝ ↦ n ^ (lam + q) / Real.log n ^ r *
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) q n) atTop
          (𝓝 0) := by
  obtain ⟨thr, mlt, C, hC0, hthr, hmlt1, hmlt, hC⟩ := NormalCrossing.shifted_bound hk hlam hlam0
      hsec hb hβ j hq
  exact NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le hC0
      (fun n ↦ blockIntegral₀_nonneg _ _ _ _ _ _ _ _) hC
      hthr hmlt1
    hmlt

/-- [Wat09, Theorem 4.9] in the qualitative form used by [Hit26, Theorem 5.2.6]:
uniformly over `ξ, φ` bounded by `M, P` and Lipschitz in the primary coordinates with constants
`Lξ, Lφ`, `n^λ Z⁰(n, ξ, φ)/(log n)^{m-1} − Y(ξ(0,·), φ(0,·)) → 0`. -/
theorem uniform_approx (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    (M P Lξ Lφ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℝ, ∀ n : ℝ, N ≤ n → ∀ ξ φ : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ,
      Measurable ξ → Measurable φ →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z| ≤ M) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z| ≤ P) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z - ξ (0, z.2)| ≤ Lξ * ∑ j, z.1 j) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z - φ (0, z.2)| ≤ Lφ * ∑ j, z.1 j) →
      |n ^ lam / Real.log n ^ r * NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ
          - frozenLimit k h k' h' lam b β (fun v ↦ ξ (0, v)) (fun v ↦ φ (0, v))| ≤ ε := by
  set a : ℝ → ℝ := fun n ↦ n ^ lam / Real.log n ^ r with ha_def
  -- the deterministic majorant `D n` and its convergence to `0`
  have hE := NormalCrossing.frozenError_tendsto (k := k) (k' := k') (h' := h') (lam := lam) (b := b)
      (β := β)
    hk hlam0 hsec hb hβ
  have hT0 : ∀ j, Tendsto (fun n : ℝ ↦ a n *
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n) atTop
          (𝓝 0) := fun j
          ↦ by
    have := NormalCrossing.shifted_negligible hk hlam hlam0 hsec hb hβ j (q := 0) le_rfl
    simpa [ha_def] using this
  have hT1 : ∀ j, Tendsto (fun n : ℝ ↦ a n * Real.sqrt n *
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) (1 / 2) n)
          atTop (𝓝 0) :=
          fun j ↦ by
    have := NormalCrossing.shifted_negligible hk hlam hlam0 hsec hb hβ j (q := 1 / 2) (by norm_num)
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with n hn
    rw [ha_def]
    simp only
    rw [Real.sqrt_eq_rpow, Real.rpow_add hn]
    ring
  set D : ℝ → ℝ := fun n ↦ NormalCrossing.gammaConst k h lam b * P * Real.exp (β * M ^ 2 / 2) *
      NormalCrossing.frozenError k k' h' lam b β n +
    a n * (Real.exp (β * M ^ 2 / 2) * ∑ j,
      (Lφ * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n +
        β * P * Lξ * Real.sqrt n *
          NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) (1 / 2)
              n))
    with hD_def
  have hD : Tendsto D atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ NormalCrossing.gammaConst k h lam b * P * Real.exp (β * M ^ 2 / 2) *
        NormalCrossing.frozenError k k' h' lam b β n) atTop (𝓝 0) := by
      simpa using hE.const_mul (NormalCrossing.gammaConst k h lam b * P * Real.exp (β * M ^ 2 / 2))
    have h2 : Tendsto (fun n ↦ a n * (Real.exp (β * M ^ 2 / 2) * ∑ j,
        (Lφ * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n +
          β * P * Lξ * Real.sqrt n *
            NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) (1 / 2)
                n)))
        atTop (𝓝 0) := by
      have : Tendsto (fun n ↦ Real.exp (β * M ^ 2 / 2) * ∑ j,
          (Lφ * (a n * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b
              (β / 2) 0 n) +
            β * P * Lξ * (a n * Real.sqrt n *
              NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2)
                  (1 / 2) n)))
          atTop (𝓝 0) := by
        have hsum : Tendsto (fun n ↦ ∑ j : Fin (r + 1),
            (Lφ * (a n * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b
                (β / 2) 0 n) +
              β * P * Lξ * (a n * Real.sqrt n *
                NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2)
                    (1 / 2) n)))
            atTop (𝓝 (∑ j : Fin (r + 1), (0 : ℝ))) := by
          refine tendsto_finsetSum _ fun j _ ↦ ?_
          simpa using ((hT0 j).const_mul Lφ).add ((hT1 j).const_mul (β * P * Lξ))
        simpa using hsum.const_mul (Real.exp (β * M ^ 2 / 2))
      refine this.congr fun n ↦ ?_
      rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      ring
    have := h1.add h2
    rw [add_zero] at this
    exact this
  -- pick `N` with `D n ≤ ε` for `n ≥ N`, and also `n ≥ 2`
  have hev : ∀ᶠ n : ℝ in atTop, D n ≤ ε ∧ 2 ≤ n :=
    (hD.eventually (eventually_le_nhds hε)).and (eventually_ge_atTop 2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn ξ φ hξm hφm hξ hφ hξL hφL ↦ ?_⟩
  obtain ⟨hDn, hn2⟩ := hN n hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have ha0 : 0 ≤ a n := by rw [ha_def]; positivity
  have h0S : ∀ v ∈ cube m' b, ((0 : Fin (r + 1) → ℝ), v) ∈ cube (r + 1) b ×ˢ cube m' b :=
    fun v hv ↦ ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, hv⟩
  have hξ₀m : Measurable fun v : Fin m' → ℝ ↦ ξ (0, v) :=
    hξm.comp (measurable_const.prodMk measurable_id)
  have hφ₀m : Measurable fun v : Fin m' → ℝ ↦ φ (0, v) :=
    hφm.comp (measurable_const.prodMk measurable_id)
  have hfr := NormalCrossing.abs_frozen_sub_frozenLimit_le hk hlam hlam0 hsec hb hβ
    (ξ₀ := fun v ↦ ξ (0, v)) (φ₀ := fun v ↦ φ (0, v)) hξ₀m hφ₀m
    (fun v hv ↦ hξ _ (h0S v hv)) (fun v hv ↦ hφ _ (h0S v hv)) hn2
  have hun := NormalCrossing.abs_blockIntegral_sub_frozen_le hk hlam hlam0 hsec hb hβ hξm hφm hξ hφ
      hξL hφL
      hn0
  calc |n ^ lam / Real.log n ^ r * NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ
        - frozenLimit k h k' h' lam b β (fun v ↦ ξ (0, v)) (fun v ↦ φ (0, v))|
      = |a n * (NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ
          - NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2))
              (fun z ↦ φ (0, z.2))) +
        (a n * NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2))
            (fun z ↦ φ (0, z.2))
          - frozenLimit k h k' h' lam b β (fun v ↦ ξ (0, v)) (fun v ↦ φ (0, v)))| := by
        rw [ha_def]; ring_nf
    _ ≤ |a n * (NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ
          - NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2))
              (fun z ↦ φ (0, z.2)))| +
        |a n * NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2))
            (fun z ↦ φ (0, z.2))
          - frozenLimit k h k' h' lam b β (fun v ↦ ξ (0, v)) (fun v ↦ φ (0, v))| :=
        abs_add_le _ _
    _ ≤ a n * (Real.exp (β * M ^ 2 / 2) * ∑ j,
          (Lφ * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n
              +
            β * P * Lξ * Real.sqrt n *
              NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2)
                  (1 / 2) n)) +
        NormalCrossing.gammaConst k h lam b * P * Real.exp (β * M ^ 2 / 2) *
            NormalCrossing.frozenError k k' h' lam
            b β n := by
        refine add_le_add ?_ ?_
        · rw [abs_mul, abs_of_nonneg ha0]
          exact mul_le_mul_of_nonneg_left hun ha0
        · simpa [ha_def] using hfr
    _ = D n := by simp only [hD_def]; ring
    _ ≤ ε := hDn

end Unfreeze

end SingularLearningTheory
