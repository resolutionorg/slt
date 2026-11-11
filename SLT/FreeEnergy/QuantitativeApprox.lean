/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.FrozenKernel
import SLT.Analysis.SpecialFunctions.Pow.LogBounds
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# [Wat09, Theorem 4.9], quantitative: the rate `(log n)^{m−2} / n^λ`

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 5.1.3] ([Wat09, Theorem 4.9]), block form, `p = 0` | |
| | `quantitative_approx` |
| [Hit26, Equation (5.1.3)], frozen part | |
| | `abs_frozen_sub_frozenLimit_le_div_log` |
| [Hit26, Equation (5.1.5)], unfreezing part | |
| | `abs_normalCrossingIntegral_sub_frozen_le_div_log` |

`FrozenKernel.lean` proves [Wat09, Theorem 4.9] qualitatively: the error `E(n)` of the frozen kernel
and the shifted-weight integrals `T_j^q(n)` are `o((log n)^{m−1} / n^λ)`. Here both are `O(1/log n)`
relative to `(log n)^{m−1} / n^λ`, giving [Hit26]'s rate `(log n)^{m−2} / n^{λ}` for `n ≥ 2`
(the exponent `m − 2` is real: `(log n)^{m−1} / log n`, also for `m = 1`).

The frozen part differs from [Hit26]'s route (binomial expansion of `(log (nA/t))^{m−1}` and
a sublevel-volume estimate for the cutoff tail): with `x = log (A(v)/t)`, the kernel ratio is
`R_n = (1 + x / log n)^{m−1}` below the cutoff and `0` above it, and both `|R_n − 1|` and the
tail indicator `1_{t ≥ nA(v)} ≤ log (t/A(v)) / log n` are bounded by
`(m |x| (1 + |x| / log 2)^{m−1}) / log n`; the remaining `n`-free double integral is finite by the
log-power dominators of `FrozenKernel.lean`. The unfreezing part is
`SingularLearningTheory.NormalCrossing.shifted_bound` ([Wat09, Theorem
4.7] for the shifted weights, threshold `≥ λ` with multiplicity `≤ m − 1` at equality) and the
simple bounds of `TechnicalResults.lean`.
-/

public section

namespace SingularLearningTheory

open SingularLearningTheory.NormalCrossing

open MeasureTheory Set Filter Topology

/-! ## Elementary bounds -/

/-- `|(1 + y)^r − 1| ≤ r |y| (1 + |y|)^r`. No thesis counterpart. -/
private theorem abs_one_add_pow_sub_one_le (y : ℝ) (r : ℕ) :
    |(1 + y) ^ r - 1| ≤ r * |y| * (1 + |y|) ^ r := by
  have hgeom := geom_sum_mul (1 + y) r
  rw [add_sub_cancel_left] at hgeom
  rw [← hgeom, abs_mul]
  have h1 : ∀ i ∈ Finset.range r, |(1 + y) ^ i| ≤ (1 + |y|) ^ r := fun i hi ↦ by
    rw [abs_pow]
    calc |1 + y| ^ i ≤ (1 + |y|) ^ i :=
          pow_le_pow_left₀ (abs_nonneg _) (by simpa using abs_add_le 1 y) i
      _ ≤ (1 + |y|) ^ r :=
          pow_le_pow_right₀ (by linarith [abs_nonneg y]) (Finset.mem_range.mp hi).le
  calc |∑ i ∈ Finset.range r, (1 + y) ^ i| * |y|
      ≤ (∑ i ∈ Finset.range r, |(1 + y) ^ i|) * |y| :=
        mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg y)
    _ ≤ (∑ _i ∈ Finset.range r, (1 + |y|) ^ r) * |y| :=
        mul_le_mul_of_nonneg_right (Finset.sum_le_sum h1) (abs_nonneg y)
    _ = r * |y| * (1 + |y|) ^ r := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- `1 ≤ (x^δ + x^{-δ}) / 2`. No thesis counterpart. -/
private theorem two_le_rpow_add_rpow_neg {x : ℝ} (hx : 0 < x) (δ : ℝ) : 2 ≤ x ^ δ + x ^ (-δ) := by
  rw [Real.rpow_neg hx.le]
  have ha : 0 < x ^ δ := Real.rpow_pos_of_pos hx δ
  rw [← sub_nonneg]
  have : x ^ δ + (x ^ δ)⁻¹ - 2 = (x ^ δ - 1) ^ 2 / x ^ δ := by field_simp; ring
  rw [this]
  positivity

/-- `|log x| (1 + |log x| / log 2)^r ≤ C (x^δ + x^{-δ})` for every `δ > 0`, with a constant
depending only on `δ` and `r`. No thesis counterpart. -/
private theorem exists_abs_log_mul_pow_le {δ : ℝ} (hδ : 0 < δ) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      |Real.log x| * (1 + |Real.log x| / Real.log 2) ^ r ≤ C * (x ^ δ + x ^ (-δ)) := by
  obtain ⟨C, hC0, hC⟩ := Real.exists_abs_log_pow_le hδ (r + 1)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2' : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  refine ⟨2 ^ r * (1 + 2 * C) / Real.log 2 ^ r, by positivity, fun x hx ↦ ?_⟩
  set L := |Real.log x| with hL
  have hL0 : 0 ≤ L := abs_nonneg _
  have h1 : 1 + L / Real.log 2 ≤ (1 + L) / Real.log 2 := by
    rw [add_div]
    have : (1 : ℝ) ≤ 1 / Real.log 2 := by rw [le_div_iff₀ hlog2]; linarith
    linarith
  have h2 : L * (1 + L / Real.log 2) ^ r ≤ (1 + L) ^ (r + 1) / Real.log 2 ^ r := by
    calc L * (1 + L / Real.log 2) ^ r ≤ (1 + L) * ((1 + L) / Real.log 2) ^ r := by
          gcongr
          linarith
      _ = (1 + L) ^ (r + 1) / Real.log 2 ^ r := by rw [div_pow, pow_succ]; ring
  have h3 : (1 + L) ^ (r + 1) ≤ 2 ^ (r + 1) * (1 + L ^ (r + 1)) := by
    have := add_pow_le_two_pow_mul_add_pow zero_le_one hL0 (r + 1)
    simpa using this
  have h4 := two_le_rpow_add_rpow_neg hx δ
  have h5 : L ^ (r + 1) ≤ C * (x ^ δ + x ^ (-δ)) := hC x hx
  have hS : 0 ≤ x ^ δ + x ^ (-δ) := by linarith
  calc L * (1 + L / Real.log 2) ^ r ≤ (1 + L) ^ (r + 1) / Real.log 2 ^ r := h2
    _ ≤ 2 ^ (r + 1) * (1 + L ^ (r + 1)) / Real.log 2 ^ r := by gcongr
    _ ≤ 2 ^ (r + 1) * ((x ^ δ + x ^ (-δ)) / 2 + C * (x ^ δ + x ^ (-δ))) / Real.log 2 ^ r := by
        gcongr
        linarith
    _ = _ := by rw [pow_succ]; ring

section Rate

variable {r m' : ℕ} {k : Fin (r + 1) → ℕ} {h : Fin (r + 1) → ℝ} {k' : Fin m' → ℕ}
  {h' : Fin m' → ℝ} {lam b β : ℝ}

/-! ## The frozen kernel: `|R_n − 1| = O(1 / log n)` -/

/-- `|R_n(t, v) − 1| ≤ (r + 1) |x| (1 + |x| / log 2)^r / log n` for `n ≥ 2`, `x = log (A(v)/t)`:
below the cutoff `R_n = (1 + x / log n)^r`, above it `R_n = 0` and `1 ≤ −x / log n`. -/
private theorem abs_logRatio_sub_one_le_div_log {v : Fin m' → ℝ}
    (hA : 0 < NormalCrossing.secondaryScale k k' b v)
    {n : ℝ} (hn : 2 ≤ n) {t : ℝ} (ht : 0 < t) :
    |NormalCrossing.logRatio k k' b n v t - 1|
      ≤ (r + 1) * (|Real.log (NormalCrossing.secondaryScale k k' b v / t)| *
          (1 + |Real.log (NormalCrossing.secondaryScale k k' b v / t)| / Real.log 2) ^ r) / Real.log
              n := by
  set A := NormalCrossing.secondaryScale k k' b v
  set L := Real.log (A / t) with hL
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hn0 : 0 < n := by linarith
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hlog2n : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn
  have hL2 : |L| / Real.log n ≤ |L| / Real.log 2 :=
    div_le_div_of_nonneg_left (abs_nonneg _) hlog2 hlog2n
  have hW : 1 ≤ (1 + |L| / Real.log 2) ^ r :=
    one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  by_cases hmem : t ∈ Ioo 0 (n * A)
  · rw [NormalCrossing.logRatio, indicator_of_mem hmem]
    have hq : Real.log (n * A / t) / Real.log n = 1 + L / Real.log n := by
      rw [mul_div_assoc, Real.log_mul hn0.ne' (div_pos hA ht).ne', add_div, div_self hlogn.ne']
    rw [hq]
    calc |(1 + L / Real.log n) ^ r - 1|
        ≤ r * |L / Real.log n| * (1 + |L / Real.log n|) ^ r := abs_one_add_pow_sub_one_le _ r
      _ = r * (|L| / Real.log n) * (1 + |L| / Real.log n) ^ r := by
          rw [abs_div, abs_of_pos hlogn]
      _ ≤ (r + 1) * (|L| / Real.log n) * (1 + |L| / Real.log 2) ^ r := by
          gcongr
          linarith
      _ = _ := by ring
  · rw [NormalCrossing.logRatio, indicator_of_notMem hmem, zero_sub, abs_neg, abs_one]
    have hge : n * A ≤ t := by
      by_contra hlt
      exact hmem ⟨ht, lt_of_not_ge hlt⟩
    have hL' : Real.log n ≤ -L := by
      rw [hL, ← Real.log_inv, inv_div]
      exact Real.log_le_log hn0 ((le_div_iff₀ hA).mpr hge)
    have h1 : 1 ≤ |L| / Real.log n := by
      rw [le_div_iff₀ hlogn, one_mul]
      exact hL'.trans (neg_le_abs L)
    have h2 : (1 : ℝ) ≤ (r + 1) * (1 + |L| / Real.log 2) ^ r :=
      one_le_mul_of_one_le_of_one_le (by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]) hW
    calc (1 : ℝ) ≤ |L| / Real.log n := h1
      _ ≤ |L| / Real.log n * ((r + 1) * (1 + |L| / Real.log 2) ^ r) :=
          le_mul_of_one_le_right (by positivity) h2
      _ = _ := by ring

/-- An integrable dominator `G` with `‖E_n-integrand‖ ≤ G / log n` for `n ≥ 2`. Quantitative
version of `exists_frozen_dominator`. No thesis counterpart. -/
private theorem exists_frozen_dominator_div_log (hlam0 : 0 < lam)
    (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β) :
    ∃ G : (Fin m' → ℝ) × ℝ → ℝ,
      Integrable G ((volume.restrict (cube m' b)).prod (volume.restrict (Ioi 0))) ∧
      ∀ n : ℝ, 2 ≤ n → ∀ z : (Fin m' → ℝ) × ℝ, (∀ j, z.1 j ∈ Ioo 0 b) → 0 < z.2 →
        ‖NormalCrossing.secondaryWeight k' h' lam z.1 *
          (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) * |NormalCrossing.logRatio k k' b n z.1 z.2 -
              1|)‖
          ≤ G z / Real.log n := by
  obtain ⟨δ, hδ0, hδlam, hδ⟩ := NormalCrossing.exists_small_exponent hlam0 hsec
  obtain ⟨C, hC0, hC⟩ := exists_abs_log_mul_pow_le hδ0 r
  have hμ1 : ∀ j, -1 < h' j - 2 * k' j * lam + 2 * k' j * δ := fun j ↦ by
    have : 0 ≤ 2 * (k' j : ℝ) * δ := by positivity
    linarith [hsec j]
  have hμ2 : ∀ j, -1 < h' j - 2 * k' j * lam + 2 * k' j * (-δ) := fun j ↦ by linarith [hδ j]
  refine ⟨fun z ↦ (r + 1) * C *
      ((b ^ (2 * ∑ j, k j)) ^ δ * ((∏ j, z.1 j ^ (h' j - 2 * k' j * lam + 2 * k' j * δ)) *
          (z.2 ^ (lam - 1 - δ) * Real.exp (-(β * z.2 / 2))))
        + (b ^ (2 * ∑ j, k j)) ^ (-δ) *
          ((∏ j, z.1 j ^ (h' j - 2 * k' j * lam + 2 * k' j * (-δ))) *
            (z.2 ^ (lam - 1 + δ) * Real.exp (-(β * z.2 / 2))))), ?_, ?_⟩
  · exact ((((integrableOn_cube_rpow hμ1 hb).mul_prod
        (integrableOn_rpow_mul_exp_neg_half (by linarith) hβ)).const_mul _).add
        (((integrableOn_cube_rpow hμ2 hb).mul_prod
          (integrableOn_rpow_mul_exp_neg_half (by linarith) hβ)).const_mul _)).const_mul _
  · intro n hn z hz ht
    have hv : ∀ j, 0 < z.1 j := fun j ↦ (hz j).1
    have hA : 0 < NormalCrossing.secondaryScale k k' b z.1 := NormalCrossing.secondaryScale_pos hb
        hv
    have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
    have hW0 : 0 ≤ NormalCrossing.secondaryWeight k' h' lam z.1 :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv j).le _
    have hT : 0 ≤ z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) := by positivity
    have e1 := NormalCrossing.secondaryWeight_mul_secondaryScale_rpow (k := k) (k' := k') (h' := h')
      (lam := lam) hv hb δ
    have e2 := NormalCrossing.secondaryWeight_mul_secondaryScale_rpow (k := k) (k' := k') (h' := h')
      (lam := lam) hv hb (-δ)
    set A := NormalCrossing.secondaryScale k k' b z.1
    have hR := abs_logRatio_sub_one_le_div_log (k := k) (r := r) hA hn ht
    have hL := hC (A / z.2) (div_pos hA ht)
    have hpt : z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) * |NormalCrossing.logRatio k k' b n z.1
        z.2 - 1|
        ≤ (r + 1) * C * (A ^ δ * (z.2 ^ (lam - 1 - δ) * Real.exp (-(β * z.2 / 2)))
            + A ^ (-δ) * (z.2 ^ (lam - 1 + δ) * Real.exp (-(β * z.2 / 2)))) / Real.log n := by
      calc z.2 ^ (lam -
          1) * Real.exp (-(β * z.2 / 2)) * |NormalCrossing.logRatio k k' b n z.1 z.2 - 1|
          ≤ z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) *
            ((r + 1) * (|Real.log (A / z.2)| *
              (1 + |Real.log (A / z.2)| / Real.log 2) ^ r) / Real.log n) :=
            mul_le_mul_of_nonneg_left hR hT
        _ ≤ z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) *
            ((r + 1) * (C * ((A / z.2) ^ δ + (A / z.2) ^ (-δ))) / Real.log n) := by
            gcongr
        _ = (r + 1) * C * (z.2 ^ (lam - 1) * (A / z.2) ^ δ * Real.exp (-(β * z.2 / 2))
              + z.2 ^ (lam - 1) * (A / z.2) ^ (-δ) * Real.exp (-(β * z.2 / 2))) / Real.log n := by
            ring
        _ = _ := by
            rw [Real.rpow_mul_div_rpow hA ht, Real.rpow_mul_div_rpow hA ht, sub_neg_eq_add]
            ring
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hW0 (by positivity))]
    calc NormalCrossing.secondaryWeight k' h' lam z.1 *
          (z.2 ^ (lam - 1) * Real.exp (-(β * z.2 / 2)) * |NormalCrossing.logRatio k k' b n z.1 z.2 -
              1|)
        ≤ NormalCrossing.secondaryWeight k' h' lam z.1 *
          ((r + 1) * C * (A ^ δ * (z.2 ^ (lam - 1 - δ) * Real.exp (-(β * z.2 / 2)))
            + A ^ (-δ) * (z.2 ^ (lam - 1 + δ) * Real.exp (-(β * z.2 / 2)))) / Real.log n) :=
          mul_le_mul_of_nonneg_left hpt hW0
      _ = _ := by
          linear_combination
            ((r + 1) * C * (z.2 ^ (lam - 1 - δ) * Real.exp (-(β * z.2 / 2))) / Real.log n) * e1
            + ((r + 1) * C * (z.2 ^ (lam - 1 + δ) * Real.exp (-(β * z.2 / 2))) / Real.log n) * e2

/-- The frozen error is `O(1 / log n)`: there is `D ≥ 0` with `E(n) ≤ D / log n` for `n ≥ 2`. -/
private theorem frozenError_le_div_log (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1)
    (hb : 0 < b) (hβ : 0 < β) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ n : ℝ, 2 ≤ n → NormalCrossing.frozenError k k' h' lam b β n ≤ D / Real.log
        n := by
  obtain ⟨G, hGint, hG⟩ := exists_frozen_dominator_div_log (k := k) hlam0 hsec hb hβ
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
  have hbound : ∀ n : ℝ, 2 ≤ n → ∀ᵐ z ∂P, ‖Φ n z‖ ≤ ‖G z‖ / Real.log n := fun n hn ↦ by
    filter_upwards [ae_cube_prod_Ioi (m := m') b] with z hz
    exact (hG n hn z hz.1 hz.2).trans (div_le_div_of_nonneg_right (le_abs_self _)
      (Real.log_nonneg (by linarith)))
  refine ⟨∫ z, ‖G z‖ ∂P, integral_nonneg fun z ↦ norm_nonneg _, fun n hn ↦ ?_⟩
  have hlogn : 0 < Real.log n := Real.log_pos (by linarith)
  have hint : Integrable (Φ n) P :=
    (hGint.norm.div_const _).mono' (hΦmeas n) (hbound n hn)
  have heq : NormalCrossing.frozenError k k' h' lam b β n = ∫ z, Φ n z ∂P := by
    rw [hP, integral_prod _ hint, NormalCrossing.frozenError]
    refine integral_congr_ae (Eventually.of_forall fun v ↦ ?_)
    exact (integral_const_mul _ _).symm
  rw [heq, ← integral_div]
  refine integral_mono_ae hint (hGint.norm.div_const _) ?_
  filter_upwards [hbound n hn] with z hz
  exact (le_abs_self _).trans hz

/-! ## The shifted weights: `n^{λ+q} T_j^q(n) / (log n)^r = O(1 / log n)` -/

/-- `(log n)^r ≤ A n^δ` for `n ≥ 2` and `δ > 0` (the first step of
`Real.exists_log_pow_div_rpow_le`). No thesis counterpart. -/
private theorem exists_log_pow_le_mul_rpow (r : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℝ, 2 ≤ n → Real.log n ^ r ≤ A * n ^ δ := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨1, one_pos, fun n hn ↦ by
      simpa using Real.one_le_rpow (by linarith) hδ.le⟩
  · refine ⟨(r / δ) ^ r, pow_pos (div_pos (by exact_mod_cast hr) hδ) r, fun n hn ↦ ?_⟩
    have hn1 : (1 : ℝ) ≤ n := by linarith
    have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
    have hstep : Real.log n ≤ (r / δ) * n ^ (δ / r) := by
      have h := Real.log_le_rpow_div (zero_le_one.trans hn1) (div_pos hδ hrpos)
      calc Real.log n ≤ n ^ (δ / r) / (δ / r) := h
        _ = (r / δ) * n ^ (δ / r) := by field_simp
    have hpow := pow_le_pow_left₀ (Real.log_nonneg hn1) hstep r
    rw [mul_pow, ← Real.rpow_natCast (n ^ (δ / (r : ℝ))) r, ← Real.rpow_mul (by linarith),
      div_mul_cancel₀ _ hrpos.ne'] at hpow
    exact hpow

/-- Quantitative version of `NormalCrossing.tendsto_rpow_div_log_pow_mul_of_le`: if
`F n ≤ C (log n)^{mlt-1} / n^{thr+q}` for `n ≥ 2` with `thr ≥ λ`, `mlt ≥ 1`, and `mlt ≤ r`
whenever `thr = λ`, then `n^{λ+q} F n / (log n)^r ≤ C' / log n` for `n ≥ 2`. No thesis
counterpart. -/
private theorem rpow_div_log_pow_mul_le_div_log {F : ℝ → ℝ} {C lam q thr : ℝ} {r mlt : ℕ}
    (hC0 : 0 ≤ C) (hF : ∀ n : ℝ, 2 ≤ n → F n ≤ C * Real.log n ^ (mlt - 1) / n ^ (thr + q))
    (hthr : lam ≤ thr) (hmlt1 : 1 ≤ mlt) (hmlt : thr = lam → mlt ≤ r) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ n : ℝ, 2 ≤ n →
      n ^ (lam + q) / Real.log n ^ r * F n ≤ C' / Real.log n := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  rcases hthr.lt_or_eq with hlt | heq
  · -- `thr > λ`: the extra power `n^{thr-λ}` beats every power of `log n`.
    have hδ : 0 < thr - lam := sub_pos.mpr hlt
    obtain ⟨A, hA0, hA⟩ := exists_log_pow_le_mul_rpow mlt hδ
    refine ⟨C * A / Real.log 2 ^ r, by positivity, fun n hn ↦ ?_⟩
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : 0 < Real.log n := Real.log_pos (by linarith)
    have hnq : 0 < n ^ (lam + q) := Real.rpow_pos_of_pos hn0 _
    have hN : 0 < n ^ (thr - lam) := Real.rpow_pos_of_pos hn0 _
    have hpow : n ^ (thr + q) = n ^ (lam + q) * n ^ (thr - lam) := by
      rw [← Real.rpow_add hn0]; congr 1; ring
    have hlog2 : Real.log 2 ^ r ≤ Real.log n ^ r :=
      pow_le_pow_left₀ hl2.le (Real.log_le_log two_pos hn) r
    rw [le_div_iff₀ hl0]
    calc n ^ (lam + q) / Real.log n ^ r * F n * Real.log n
        ≤ n ^ (lam + q) / Real.log n ^ r * (C * Real.log n ^ (mlt - 1) / n ^ (thr + q)) *
          Real.log n := by gcongr; exact hF n hn
      _ = C * Real.log n ^ mlt / (Real.log n ^ r * n ^ (thr - lam)) := by
          rw [hpow]
          have : Real.log n ^ mlt = Real.log n ^ (mlt - 1) * Real.log n := by
            rw [← pow_succ, Nat.sub_add_cancel hmlt1]
          rw [this]
          field_simp
      _ ≤ C * (A * n ^ (thr - lam)) / (Real.log n ^ r * n ^ (thr - lam)) := by
          gcongr
          exact hA n hn
      _ = C * A / Real.log n ^ r := by field_simp
      _ ≤ C * A / Real.log 2 ^ r :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hlog2
  · -- `thr = λ`: then `mlt ≤ r`, and `(log n)^{mlt-1} / (log n)^r ≤ C' / log n`.
    have hmr : mlt ≤ r := hmlt heq.symm
    rw [← heq] at hF
    obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
    obtain ⟨C', hC'0, hC'⟩ := Real.exists_log_pow_le (show mlt - 1 ≤ r' by omega)
    refine ⟨C * C', by positivity, fun n hn ↦ ?_⟩
    have hn0 : (0 : ℝ) < n := by linarith
    have hl0 : 0 < Real.log n := Real.log_pos (by linarith)
    have hnq : 0 < n ^ (lam + q) := Real.rpow_pos_of_pos hn0 _
    calc n ^ (lam + q) / Real.log n ^ (r' + 1) * F n
        ≤ n ^ (lam + q) / Real.log n ^ (r' + 1) *
            (C * Real.log n ^ (mlt - 1) / n ^ (lam + q)) := by gcongr; exact hF n hn
      _ = C * Real.log n ^ (mlt - 1) / Real.log n ^ (r' + 1) := by field_simp
      _ ≤ C * (C' * Real.log n ^ r') / Real.log n ^ (r' + 1) := by
          gcongr
          exact hC' n hn
      _ = C * C' / Real.log n := by rw [pow_succ]; field_simp

/-- The shifted-weight integrals are `O((log n)^r / (n^{λ+q} log n))`:
`NormalCrossing.shifted_bound` and
`rpow_div_log_pow_mul_le_div_log`. -/
private theorem shifted_le_div_log (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    (j : Fin (r + 1)) {q : ℝ} (hq : 0 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 2 ≤ n → n ^ (lam + q) / Real.log n ^ r *
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) q n ≤ C /
          Real.log n := by
  obtain ⟨thr, mlt, C, hC0, hthr, hmlt1, hmlt, hC⟩ := NormalCrossing.shifted_bound hk hlam hlam0
      hsec hb hβ j hq
  exact rpow_div_log_pow_mul_le_div_log hC0 hC hthr hmlt1 hmlt

/-! ## [Wat09, Theorem 4.9], block form -/

/-- [Hit26, Theorem 5.1.3] ([Wat09, Theorem 4.9]) in block form for `p =
0`, quantitative: there is `C ≥ 0` such that for all measurable `ξ, φ` on the cube, bounded by
`M, P` and Lipschitz in the primary coordinates towards their traces with constants
`Lξ, Lφ ≥ 0`, and all `n ≥ 2`,

`|Z⁰(n, ξ, φ) − (log n)^{m−1}/n^λ · Y(ξ(0,·), φ(0,·))|
  ≤ C (log n)^{m−1} / (n^λ log n) · e^{βM²/2} (β Lξ P + Lφ + P)`.

The unfreezing part is `NormalCrossing.abs_blockIntegral_sub_frozen_le` with the shifted-weight
integrals bounded by `shifted_le_div_log`; the frozen part is
`NormalCrossing.abs_frozen_sub_frozenLimit_le` with `frozenError_le_div_log`. -/
theorem quantitative_approx (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ξ φ : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ) (M P Lξ Lφ : ℝ),
      Measurable ξ → Measurable φ → 0 ≤ Lξ → 0 ≤ Lφ →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z| ≤ M) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z| ≤ P) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z - ξ (0, z.2)| ≤ Lξ * ∑ j, z.1 j) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |φ z - φ (0, z.2)| ≤ Lφ * ∑ j, z.1 j) →
      ∀ n : ℝ, 2 ≤ n →
        |NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ - Real.log n ^ r / n ^ lam *
            frozenLimit k h k' h' lam b β (fun v ↦ ξ (0, v)) (fun v ↦ φ (0, v))|
          ≤ C * Real.log n ^ r / (n ^ lam * Real.log n) * Real.exp (β * M ^ 2 / 2) *
            (β * Lξ * P + Lφ + P) := by
  obtain ⟨D, hD0, hD⟩ := frozenError_le_div_log (k := k) hlam0 hsec hb hβ
  have hγ := gammaConst_pos h lam hk hb
  have hT0 : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 2 ≤ n → n ^ lam / Real.log n ^ r *
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n ≤ C /
          Real.log n :=
          fun j ↦ by
    simpa using shifted_le_div_log hk hlam hlam0 hsec hb hβ j (q := 0) le_rfl
  choose C0 hC00 hC0 using hT0
  have hT1 : ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℝ, 2 ≤ n → n ^ (lam + 1 / 2) / Real.log n ^ r *
      NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) (1 / 2) n ≤
        C / Real.log n :=
    fun j ↦ shifted_le_div_log hk hlam hlam0 hsec hb hβ j (q := 1 / 2) (by norm_num)
  choose C1 hC10 hC1 using hT1
  have hS0 : 0 ≤ ∑ j, C0 j := Finset.sum_nonneg fun j _ ↦ hC00 j
  have hS1 : 0 ≤ ∑ j, C1 j := Finset.sum_nonneg fun j _ ↦ hC10 j
  refine ⟨NormalCrossing.gammaConst k h lam b * D + ∑ j, C0 j + ∑ j, C1 j, by positivity,
    fun ξ φ M P Lξ Lφ hξm hφm hLξ hLφ hξ hφ hξL hφL n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) < n := by linarith
  have hl0 : 0 < Real.log n := Real.log_pos (by linarith)
  have hnl : 0 < n ^ lam := Real.rpow_pos_of_pos hn0 _
  have h0mem : ((0 : Fin (r + 1) → ℝ), (0 : Fin m' → ℝ)) ∈ cube (r + 1) b ×ˢ cube m' b :=
    ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, ⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hξ _ h0mem)
  have hP0 : 0 ≤ P := (abs_nonneg _).trans (hφ _ h0mem)
  have hzero : ∀ v ∈ cube m' b, ((0 : Fin (r + 1) → ℝ), v) ∈ cube (r + 1) b ×ˢ cube m' b :=
    fun v hv ↦ ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, hv⟩
  set a := Real.log n ^ r / n ^ lam with ha_def
  have ha : 0 < a := by positivity
  have hainv : n ^ lam / Real.log n ^ r = a⁻¹ := by rw [ha_def, inv_div]
  set E := Real.exp (β * M ^ 2 / 2) with hE_def
  set ξ₀ : (Fin m' → ℝ) → ℝ := fun v ↦ ξ (0, v) with hξ₀
  set φ₀ : (Fin m' → ℝ) → ℝ := fun v ↦ φ (0, v) with hφ₀
  -- the frozen part
  have hfrozen := NormalCrossing.abs_frozen_sub_frozenLimit_le hk hlam hlam0 hsec hb hβ (ξ₀ := ξ₀)
      (φ₀ := φ₀)
    (hξm.comp (measurable_const.prodMk measurable_id))
    (hφm.comp (measurable_const.prodMk measurable_id))
    (fun v hv ↦ hξ _ (hzero v hv)) (fun v hv ↦ hφ _ (hzero v hv)) hn
  -- the unfreezing part
  have hunf := NormalCrossing.abs_blockIntegral_sub_frozen_le hk hlam hlam0 hsec hb hβ hξm hφm hξ
      hφ hξL hφL
      hn0.le
  have hT0' : ∀ j, NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2)
      0 n
      ≤ a * (C0 j / Real.log n) := fun j ↦ by
    have hT := hC0 j n hn
    rw [hainv, inv_mul_le_iff₀ ha] at hT
    exact hT
  have hT1' : ∀ j, Real.sqrt n * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k'
      h' b
      (β / 2) (1 / 2) n
      ≤ a * (C1 j / Real.log n) := fun j ↦ by
    have hT := hC1 j n hn
    rw [Real.rpow_add hn0, ← Real.sqrt_eq_rpow, mul_div_right_comm, mul_assoc, hainv,
      inv_mul_le_iff₀ ha] at hT
    exact hT
  -- the sum of the unfreezing terms
  have hsum : ∑ j,
      (Lφ * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n +
        β * P * Lξ * Real.sqrt n * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1))
            k' h' b
            (β / 2) (1 / 2) n)
      ≤ a / Real.log n * (Lφ * ∑ j, C0 j + β * P * Lξ * ∑ j, C1 j) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ ↦ ?_
    have h1 := mul_le_mul_of_nonneg_left (hT0' j) hLφ
    have h2 := mul_le_mul_of_nonneg_left (hT1' j) (by positivity : 0 ≤ β * P * Lξ)
    calc Lφ * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n +
          β * P * Lξ * Real.sqrt n * NormalCrossing.blockIntegral₀ k
              (Function.update h j (h j + 1)) k' h' b
              (β / 2) (1 / 2) n
        = Lφ * NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) 0 n +
          β * P * Lξ * (Real.sqrt n *
            NormalCrossing.blockIntegral₀ k (Function.update h j (h j + 1)) k' h' b (β / 2) (1 / 2)
                n) := by
                ring
      _ ≤ Lφ * (a * (C0 j / Real.log n)) + β * P * Lξ * (a * (C1 j / Real.log n)) :=
          add_le_add h1 h2
      _ = _ := by ring
  -- the frozen difference, rescaled
  have hfro' : |NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2))
      (fun z ↦ φ (0, z.2)) -
        a * frozenLimit k h k' h' lam b β ξ₀ φ₀|
      ≤ a / Real.log n * (NormalCrossing.gammaConst k h lam b * P * E * D) := by
    have hid : NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2))
        (fun z ↦ φ (0, z.2)) -
        a * frozenLimit k h k' h' lam b β ξ₀ φ₀
        = a * (n ^ lam / Real.log n ^ r *
            NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2))
                (fun z ↦ φ (0, z.2)) -
          frozenLimit k h k' h' lam b β ξ₀ φ₀) := by
      rw [hainv, mul_sub, ← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    rw [hid, abs_mul, abs_of_pos ha]
    calc a * |n ^ lam / Real.log n ^ r *
          NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2)) (fun z ↦ φ (0, z.2)) -
          frozenLimit k h k' h' lam b β ξ₀ φ₀|
        ≤ a * (NormalCrossing.gammaConst k h lam b * P * E *
            NormalCrossing.frozenError k k' h' lam b β n) :=
          mul_le_mul_of_nonneg_left hfrozen ha.le
      _ ≤ a * (NormalCrossing.gammaConst k h lam b * P * E * (D / Real.log n)) := by
          gcongr
          exact hD n hn
      _ = _ := by ring
  -- assemble
  have hCtot : NormalCrossing.gammaConst k h lam b * D * P + (∑ j, C0 j) * Lφ + (∑ j, C1 j) *
      (β * Lξ * P)
      ≤ (NormalCrossing.gammaConst k h lam b * D + ∑ j, C0 j + ∑ j, C1 j) *
          (β * Lξ * P + Lφ + P) := by
    have h1 : 0 ≤ NormalCrossing.gammaConst k h lam b * D := by positivity
    have h2 : 0 ≤ β * Lξ * P := by positivity
    nlinarith [mul_nonneg h1 h2, mul_nonneg h1 hLφ, mul_nonneg hS0 h2, mul_nonneg hS0 hP0,
      mul_nonneg hS1 hLφ, mul_nonneg hS1 hP0]
  calc |NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ -
        a * frozenLimit k h k' h' lam b β ξ₀ φ₀|
      ≤ |NormalCrossing.blockIntegral k h k' h' b β 0 n ξ φ -
          NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2)) (fun z ↦ φ (0, z.2))|
              +
        |NormalCrossing.blockIntegral k h k' h' b β 0 n (fun z ↦ ξ (0, z.2)) (fun z ↦ φ (0, z.2)) -
          a * frozenLimit k h k' h' lam b β ξ₀ φ₀| := abs_sub_le _ _ _
    _ ≤ E * (a / Real.log n * (Lφ * ∑ j, C0 j + β * P * Lξ * ∑ j, C1 j)) +
        a / Real.log n * (NormalCrossing.gammaConst k h lam b * P * E * D) :=
        add_le_add (hunf.trans (mul_le_mul_of_nonneg_left hsum (Real.exp_pos _).le)) hfro'
    _ = a / Real.log n * E *
        (NormalCrossing.gammaConst k h lam b * D * P + (∑ j, C0 j) * Lφ + (∑ j, C1 j) *
            (β * Lξ * P)) := by
        ring
    _ ≤ a / Real.log n * E *
        ((NormalCrossing.gammaConst k h lam b * D + ∑ j, C0 j + ∑ j, C1 j) *
            (β * Lξ * P + Lφ + P)) :=
        mul_le_mul_of_nonneg_left hCtot (by positivity)
    _ = _ := by rw [ha_def]; ring

/-! ## General `p`: the weight shift `h ↦ h + 2kp`

`K^p u^h v^{h'} = u^{h + 2kp} v^{h' + 2k'p}` on the open cube, so `Z^p(n, ξ, φ)` for
`(k, h, k', h')` is `Z⁰(n, ξ, φ)` for the shifted weights, whose threshold is `λ + p` with the
same primary coordinates; the frozen limit of the shifted data is [Hit26]'s `Y^p` (the
constant and the secondary weight are unchanged). -/

/-- `Z^p(n, ξ, φ) = Z⁰(n, ξ, φ)` for the weights `h + 2kp`, `h' + 2k'p`. -/
theorem NormalCrossing.blockIntegral_shift (k : Fin (r + 1) → ℕ) (h : Fin (r + 1) → ℝ)
    (k' : Fin m' → ℕ)
    (h' : Fin m' → ℝ) (b β p n : ℝ) (ξ φ : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ) :
    NormalCrossing.blockIntegral k h k' h' b β p n ξ φ
      = NormalCrossing.blockIntegral k (fun j ↦ h j + 2 * k j * p) k' (fun j ↦ h' j + 2 * k' j * p)
          b β 0 n
          ξ φ := by
  have hopen : ∀ F : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ,
      ∫ z in cube (r + 1) b ×ˢ cube m' b, F z
        = ∫ z, F z ∂((volume.restrict (ocube (r + 1) b)).prod (volume.restrict (ocube m' b))) := by
    intro F
    rw [restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict]
    rfl
  unfold NormalCrossing.blockIntegral
  rw [hopen, hopen]
  refine integral_congr_ae ?_
  filter_upwards [ae_prod_ocube (m := r + 1) (m' := m') b] with z hz
  have hu : ∀ j, 0 < z.1 j := fun j ↦ (hz.1 j).1
  have hv : ∀ j, 0 < z.2 j := fun j ↦ (hz.2 j).1
  have hU : 0 ≤ ∏ j, z.1 j ^ (2 * k j) := Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu j).le _
  have hV : 0 ≤ ∏ j, z.2 j ^ (2 * k' j) := Finset.prod_nonneg fun j _ ↦ pow_nonneg (hv j).le _
  have e1 := Real.prod_pow_rpow_mul_prod_rpow k h p hu
  have e2 := Real.prod_pow_rpow_mul_prod_rpow k' h' p hv
  simp only [potential, NormalCrossing.monomialWeight, Real.rpow_zero, one_mul] at e1 e2 ⊢
  rw [Real.mul_rpow hU hV, ← e1, ← e2]
  ring

/-- The frozen limit of the shifted data is [Hit26]'s `Y^p`: the constant `γ_b` and the
secondary weight `v^μ` are those of the unshifted data, the kernel is `t^{λ+p−1}`. -/
theorem frozenLimit_shift (k : Fin (r + 1) → ℕ) (h : Fin (r + 1) → ℝ) (k' : Fin m' → ℕ)
    (h' : Fin m' → ℝ) (lam b β p : ℝ) (ξ₀ φ₀ : (Fin m' → ℝ) → ℝ) :
    frozenLimit k (fun j ↦ h j + 2 * k j * p) k' (fun j ↦ h' j + 2 * k' j * p) (lam + p) b β ξ₀ φ₀
      = NormalCrossing.gammaConst k h lam b *
        ∫ v in cube m' b, NormalCrossing.secondaryWeight k' h' lam v * φ₀ v *
          ∫ t in Ioi 0, t ^ (lam + p - 1) * Real.exp (-(β * t) + β * Real.sqrt t * ξ₀ v) := by
  have hγ : NormalCrossing.gammaConst k (fun j ↦ h j + 2 * k j * p) (lam + p) b =
      NormalCrossing.gammaConst k h lam b := by
    unfold NormalCrossing.gammaConst
    congr 2
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    push_cast
    ring
  have hW : ∀ v, NormalCrossing.secondaryWeight k' (fun j ↦ h' j + 2 * k' j * p) (lam + p) v
      = NormalCrossing.secondaryWeight k' h' lam v := fun v ↦ by
    unfold NormalCrossing.secondaryWeight
    refine Finset.prod_congr rfl fun j _ ↦ ?_
    congr 1
    ring
  unfold frozenLimit
  rw [hγ]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun v _ ↦ ?_
  rw [hW]

end Rate

end SingularLearningTheory
