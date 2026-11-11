/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.FiberIdentity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# The strict peel

If `g : K → [0,1]` has volume-scaling exponents `(λ, θ)` and the new weighted coordinate's
exponent `b = (h+1)/p` is strictly larger than `λ`, then the fiber identity's integral term
(`FiberIdentity`) is `O(ε^λ(−log ε)^{θ−1})` — so multiplying by one strict coordinate preserves
`(λ, θ)` exactly (`hasLLCExponentsOn_mul_strict_coord`); `StrictFamily` iterates it.

The estimate is by dyadic shells `S_m = {2^m ε < g ≤ 2^{m+1} ε}`, with a single geometric sum:
on every shell the integrand is at most `2^{-mb}`, and the shell mass is bounded either by the
`V_g`-bound (low shells, `2^{m+1}ε < ε₀`) or trivially by `ν K` with the spare factor
`2^{-mλ} < (2ε/ε₀)^λ` (high shells) — each shell satisfies the SUM of the two bounds, so no
minimal-index bookkeeping is needed.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace SingularLearningTheory

variable {γ : Type*} [MeasurableSpace γ] {ν : Measure γ} {K : Set γ}

omit [MeasurableSpace γ] in
/-- The dyadic shells cover the strict region. -/
theorem strict_subset_iUnion_shells {g : γ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (_hg1 : ∀ y ∈ K, g y ≤ 1) :
    K ∩ {y | ε < g y} ⊆
      ⋃ m : ℕ, K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε} := by
  rintro y ⟨hyK, (hy : ε < g y)⟩
  have hgpos : 0 < g y := hε.trans hy
  -- the least m with g y ≤ 2^(m+1) ε exists since 2^m ε → ∞
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (g y / ε)
    (by norm_num : (1 : ℝ) < 2)
  have hex : ∃ m : ℕ, g y ≤ 2 ^ (m + 1) * ε := by
    refine ⟨n, ?_⟩
    have h2 : g y / ε < 2 ^ n := hn
    have h3 : g y < 2 ^ n * ε := by
      rw [div_lt_iff₀ hε] at h2
      exact h2
    have h4 : (2 : ℝ) ^ n ≤ 2 ^ (n + 1) :=
      pow_le_pow_right₀ (by norm_num) (Nat.le_succ n)
    nlinarith
  classical
  set m := Nat.find hex with hm
  have hub : g y ≤ 2 ^ (m + 1) * ε := Nat.find_spec hex
  have hlb : 2 ^ m * ε < g y := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · rw [hm0]
      simpa using hy
    · have hnot := Nat.find_min hex (Nat.pred_lt hmpos.ne')
      have hpred : (Nat.find hex).pred + 1 = Nat.find hex :=
        Nat.succ_pred_eq_of_pos (hm ▸ hmpos)
      rw [hpred] at hnot
      rw [hm]
      exact not_le.mp hnot
  exact mem_iUnion.mpr ⟨m, hyK, hlb, hub⟩

omit [MeasurableSpace γ] in
/-- On the `m`-th shell the integrand is at most `2^{-mb}`. -/
theorem shell_integrand_bound {g : γ → ℝ} {ε b : ℝ} (hε : 0 < ε)
    (hb : 0 < b) {m : ℕ} {y : γ} (hy : 2 ^ m * ε < g y) :
    (ε / g y) ^ b ≤ ((2 : ℝ) ^ m)⁻¹ ^ b := by
  have hgpos : 0 < g y :=
    lt_of_le_of_lt (by positivity) hy
  refine Real.rpow_le_rpow (by positivity) ?_ hb.le
  rw [div_le_iff₀ hgpos, inv_mul_eq_div, le_div_iff₀
    (pow_pos two_pos m), mul_comm]
  exact hy.le

private theorem two_pow_inv_rpow (m : ℕ) (a : ℝ) :
    ((2 : ℝ) ^ m)⁻¹ ^ a = (2 : ℝ) ^ (-(m : ℝ) * a) := by
  rw [← Real.rpow_natCast 2 m, ← Real.rpow_neg (by norm_num),
    ← Real.rpow_mul (by norm_num)]

private theorem two_pow_rpow (m : ℕ) (a : ℝ) :
    ((2 : ℝ) ^ m) ^ a = (2 : ℝ) ^ ((m : ℝ) * a) := by
  rw [← Real.rpow_natCast 2 m, ← Real.rpow_mul (by norm_num)]

private theorem two_rpow_pow (c : ℝ) (m : ℕ) :
    ((2 : ℝ) ^ c) ^ m = (2 : ℝ) ^ (c * (m : ℝ)) := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ c) m, ← Real.rpow_mul (by norm_num)]

/-- The per-shell bound, unified across low and high shells: every
shell's contribution is at most `q^m · D · llcScale λ θ ε` with
`q = 2^{-(b-λ)}` and `D = C·2^λ + (2/ε₀)^λ·(ν K).toReal`. -/
theorem shell_term_bound {g : γ → ℝ} (hgm : Measurable g)
    (hK : MeasurableSet K)
    {b lam theta C eps0 : ℝ} (hlam : 0 < lam) (hb : lam < b)
    (htheta : 1 ≤ theta) (hC : 0 < C) (heps0 : eps0 ∈ Ioo (0 : ℝ) 1)
    (hνK : ν K ≠ ⊤)
    (hV : ∀ t ∈ Ioo (0 : ℝ) eps0,
      (ν (K ∩ {y | g y ≤ t})).toReal ≤ C * llcScale lam theta t)
    {ε : ℝ} (hε0 : 0 < ε) (hεe : ε < Real.exp (-1)) (hεs : ε < eps0)
    (m : ℕ) :
    ∫⁻ y in K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε},
      ENNReal.ofReal ((ε / g y) ^ b) ∂ν
    ≤ ENNReal.ofReal ((((2 : ℝ) ^ (-(b - lam))) ^ m)
        * ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
          * llcScale lam theta ε)) := by
  have hbpos : 0 < b := hlam.trans hb
  have heps0pos : (0 : ℝ) < eps0 := heps0.1
  have hε1 : ε < 1 := lt_trans hεs heps0.2
  have hlog : 1 ≤ -Real.log ε := by
    have h1 : Real.log ε < Real.log (Real.exp (-1)) :=
      Real.log_lt_log hε0 hεe
    rw [Real.log_exp] at h1
    linarith
  have hlogpow : (1 : ℝ) ≤ (-Real.log ε) ^ (theta - 1) := by
    calc (1 : ℝ) = 1 ^ (theta - 1) := (Real.one_rpow _).symm
    _ ≤ (-Real.log ε) ^ (theta - 1) :=
        Real.rpow_le_rpow zero_le_one hlog (by linarith)
  have hllc : 0 < llcScale lam theta ε := llcScale_pos ⟨hε0, hε1⟩
  have hSm : MeasurableSet
      (K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε}) := by
    refine hK.inter ?_
    have h1 : {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε}
        = g ⁻¹' (Ioc (2 ^ m * ε) (2 ^ (m + 1) * ε)) := rfl
    rw [h1]
    exact hgm measurableSet_Ioc
  -- step 1: bound the integrand by the shell constant
  have hstep1 : ∫⁻ y in K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε},
      ENNReal.ofReal ((ε / g y) ^ b) ∂ν
      ≤ ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹ ^ b)
        * ν (K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε}) := by
    have hpt : ∀ᵐ y ∂(ν.restrict
        (K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε})),
        ENNReal.ofReal ((ε / g y) ^ b)
          ≤ ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹ ^ b) :=
      (ae_restrict_iff' hSm).mpr (Filter.Eventually.of_forall
        fun y hy => ENNReal.ofReal_le_ofReal
          (shell_integrand_bound hε0 hbpos hy.2.1))
    refine le_trans (lintegral_mono_ae hpt) ?_
    rw [setLIntegral_const]
  -- step 2: the shell sits below the next threshold
  have hstep2 : ν (K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε})
      ≤ ν (K ∩ {y | g y ≤ 2 ^ (m + 1) * ε}) :=
    measure_mono fun y hy => ⟨hy.1, hy.2.2⟩
  have hfin : ν (K ∩ {y | g y ≤ 2 ^ (m + 1) * ε}) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono inter_subset_left)
      (lt_top_iff_ne_top.mpr hνK)).ne
  -- the two shell regimes
  rcases lt_or_ge ((2 : ℝ) ^ (m + 1) * ε) eps0 with hlow | hhigh
  · -- LOW: the V-bound applies at the next threshold
    have hmem : (2 : ℝ) ^ (m + 1) * ε ∈ Ioo (0 : ℝ) eps0 :=
      ⟨by positivity, hlow⟩
    have hb1 : ν (K ∩ {y | g y ≤ 2 ^ (m + 1) * ε})
        ≤ ENNReal.ofReal (C * llcScale lam theta (2 ^ (m + 1) * ε)) := by
      rw [← ENNReal.ofReal_toReal hfin]
      exact ENNReal.ofReal_le_ofReal (hV _ hmem)
    have hscale : llcScale lam theta (2 ^ (m + 1) * ε)
        ≤ ((2 : ℝ) ^ (m + 1)) ^ lam * llcScale lam theta ε := by
      unfold llcScale
      rw [Real.mul_rpow (by positivity) hε0.le, mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_
        (Real.rpow_nonneg hε0.le _)) (by positivity)
      refine Real.rpow_le_rpow ?_ ?_ (by linarith)
      · have hlt1 : (2 : ℝ) ^ (m + 1) * ε < 1 := lt_trans hlow heps0.2
        have := Real.log_neg (by positivity) hlt1
        linarith
      · have h2 : Real.log ε ≤ Real.log ((2 : ℝ) ^ (m + 1) * ε) :=
          Real.log_le_log hε0 (le_mul_of_one_le_left hε0.le
            (one_le_pow₀ (by norm_num)))
        linarith
    calc ∫⁻ y in K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε},
        ENNReal.ofReal ((ε / g y) ^ b) ∂ν
        ≤ ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹ ^ b)
          * ENNReal.ofReal (C * llcScale lam theta (2 ^ (m + 1) * ε)) :=
          le_trans hstep1 (mul_le_mul_right (hstep2.trans hb1) _)
      _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ (-(b - lam))) ^ m)
          * ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
            * llcScale lam theta ε)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hkey : ((2 : ℝ) ^ m)⁻¹ ^ b
              * (C * llcScale lam theta (2 ^ (m + 1) * ε))
              ≤ ((2 : ℝ) ^ m)⁻¹ ^ b
                * (C * (((2 : ℝ) ^ (m + 1)) ^ lam
                  * llcScale lam theta ε)) := by
            refine mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hscale hC.le) (by positivity)
          refine le_trans hkey ?_
          have halg : ((2 : ℝ) ^ m)⁻¹ ^ b * ((2 : ℝ) ^ (m + 1)) ^ lam
              = (((2 : ℝ) ^ (-(b - lam))) ^ m) * 2 ^ lam := by
            rw [two_pow_inv_rpow, two_pow_rpow, two_rpow_pow,
              ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
            congr 1
            push_cast
            ring
          calc ((2 : ℝ) ^ m)⁻¹ ^ b
              * (C * (((2 : ℝ) ^ (m + 1)) ^ lam * llcScale lam theta ε))
              = (((2 : ℝ) ^ m)⁻¹ ^ b * ((2 : ℝ) ^ (m + 1)) ^ lam)
                * (C * llcScale lam theta ε) := by ring
            _ = (((2 : ℝ) ^ (-(b - lam))) ^ m) * 2 ^ lam
                * (C * llcScale lam theta ε) := by rw [halg]
            _ = (((2 : ℝ) ^ (-(b - lam))) ^ m)
                * ((C * 2 ^ lam) * llcScale lam theta ε) := by ring
            _ ≤ (((2 : ℝ) ^ (-(b - lam))) ^ m)
                * ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
                  * llcScale lam theta ε) := by
                refine mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right ?_ hllc.le)
                  (by positivity)
                have hnn : 0 ≤ (2 / eps0) ^ lam * (ν K).toReal := by
                  have := ENNReal.toReal_nonneg (a := ν K)
                  positivity
                linarith
  · -- HIGH: the trivial bound with the spare λ-factor
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have h2inv : ((2 : ℝ) ^ m)⁻¹ ≤ 2 * ε / eps0 := by
      have hps : (2 : ℝ) ^ (m + 1) = 2 ^ m * 2 := pow_succ 2 m
      have key : eps0 ≤ 2 ^ m * (2 * ε) := by
        have := hhigh
        rw [hps] at this
        nlinarith
      calc ((2 : ℝ) ^ m)⁻¹ = (2 * ε) / (2 ^ m * (2 * ε)) := by
            field_simp
        _ ≤ (2 * ε) / eps0 :=
            div_le_div_of_nonneg_left (by positivity) heps0.1 key
    have hsplit : ((2 : ℝ) ^ m)⁻¹ ^ b
        = (((2 : ℝ) ^ (-(b - lam))) ^ m) * ((2 : ℝ) ^ m)⁻¹ ^ lam := by
      rw [two_pow_inv_rpow, two_pow_inv_rpow, two_rpow_pow,
        ← Real.rpow_add (by norm_num)]
      congr 1
      ring
    have hpow : ((2 : ℝ) ^ m)⁻¹ ^ b
        ≤ (((2 : ℝ) ^ (-(b - lam))) ^ m)
          * ((2 / eps0) ^ lam * ε ^ lam) := by
      rw [hsplit]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : ((2 : ℝ) ^ m)⁻¹ ^ lam ≤ (2 * ε / eps0) ^ lam :=
        Real.rpow_le_rpow (by positivity) h2inv hlam.le
      calc ((2 : ℝ) ^ m)⁻¹ ^ lam ≤ (2 * ε / eps0) ^ lam := h1
        _ = (2 / eps0 * ε) ^ lam := by
            congr 1
            ring
        _ = (2 / eps0) ^ lam * ε ^ lam :=
            Real.mul_rpow (by positivity) hε0.le
    have hb2 : ν (K ∩ {y | g y ≤ 2 ^ (m + 1) * ε})
        ≤ ENNReal.ofReal ((ν K).toReal) := by
      rw [ENNReal.ofReal_toReal hνK]
      exact measure_mono inter_subset_left
    calc ∫⁻ y in K ∩ {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε},
        ENNReal.ofReal ((ε / g y) ^ b) ∂ν
        ≤ ENNReal.ofReal (((2 : ℝ) ^ m)⁻¹ ^ b)
          * ENNReal.ofReal ((ν K).toReal) :=
          le_trans hstep1 (mul_le_mul_right (hstep2.trans hb2) _)
      _ ≤ ENNReal.ofReal ((((2 : ℝ) ^ (-(b - lam))) ^ m)
          * ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
            * llcScale lam theta ε)) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hKnn : (0 : ℝ) ≤ (ν K).toReal := ENNReal.toReal_nonneg
          calc ((2 : ℝ) ^ m)⁻¹ ^ b * (ν K).toReal
              ≤ ((((2 : ℝ) ^ (-(b - lam))) ^ m)
                * ((2 / eps0) ^ lam * ε ^ lam)) * (ν K).toReal :=
              mul_le_mul_of_nonneg_right hpow hKnn
            _ = (((2 : ℝ) ^ (-(b - lam))) ^ m)
                * (((2 / eps0) ^ lam * (ν K).toReal) * ε ^ lam) := by
                ring
            _ ≤ (((2 : ℝ) ^ (-(b - lam))) ^ m)
                * (((2 / eps0) ^ lam * (ν K).toReal)
                  * llcScale lam theta ε) := by
                refine mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_left ?_ (by positivity))
                  (by positivity)
                unfold llcScale
                exact le_mul_of_one_le_right
                  (Real.rpow_nonneg hε0.le _) hlogpow
            _ ≤ (((2 : ℝ) ^ (-(b - lam))) ^ m)
                * ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
                  * llcScale lam theta ε) := by
                refine mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right ?_ hllc.le)
                  (by positivity)
                nlinarith [Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) lam, hC]

/-- **The strict-tail estimate**: the fiber identity's integral term is
`O(llcScale λ θ ε)` when the new coordinate is strict (`b > λ`). -/
theorem strict_integral_bound {g : γ → ℝ} (hgm : Measurable g)
    (hK : MeasurableSet K) (hg1 : ∀ y ∈ K, g y ≤ 1)
    {b lam theta C eps0 : ℝ} (hlam : 0 < lam) (hb : lam < b)
    (htheta : 1 ≤ theta) (hC : 0 < C) (heps0 : eps0 ∈ Ioo (0 : ℝ) 1)
    (hνK : ν K ≠ ⊤)
    (hV : ∀ t ∈ Ioo (0 : ℝ) eps0,
      (ν (K ∩ {y | g y ≤ t})).toReal ≤ C * llcScale lam theta t)
    {ε : ℝ} (hε0 : 0 < ε) (hεe : ε < Real.exp (-1)) (hεs : ε < eps0) :
    (∫⁻ y in K ∩ {y | ε < g y},
      ENNReal.ofReal ((ε / g y) ^ b) ∂ν).toReal
    ≤ ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
        * (1 - (2 : ℝ) ^ (-(b - lam)))⁻¹) * llcScale lam theta ε := by
  have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(b - lam)) :=
    Real.rpow_nonneg (by norm_num) _
  have hq1 : (2 : ℝ) ^ (-(b - lam)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hKnn : (0 : ℝ) ≤ (ν K).toReal := ENNReal.toReal_nonneg
  have heps0pos : (0 : ℝ) < eps0 := heps0.1
  have hDpos : 0 < C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal := by
    have h1 : (0 : ℝ) < C * 2 ^ lam := by positivity
    have h2 : (0 : ℝ) ≤ (2 / eps0) ^ lam * (ν K).toReal := by positivity
    linarith
  have hllc : 0 < llcScale lam theta ε :=
    llcScale_pos ⟨hε0, lt_trans hεs heps0.2⟩
  have hchain : ∫⁻ y in K ∩ {y | ε < g y},
      ENNReal.ofReal ((ε / g y) ^ b) ∂ν
      ≤ ENNReal.ofReal
          (((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
            * (1 - (2 : ℝ) ^ (-(b - lam)))⁻¹) * llcScale lam theta ε) := by
    calc ∫⁻ y in K ∩ {y | ε < g y},
        ENNReal.ofReal ((ε / g y) ^ b) ∂ν
        ≤ ∫⁻ y in ⋃ m : ℕ, K ∩
            {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε},
            ENNReal.ofReal ((ε / g y) ^ b) ∂ν :=
          lintegral_mono_set (strict_subset_iUnion_shells hε0 hg1)
      _ ≤ ∑' m : ℕ, ∫⁻ y in K ∩
            {y | 2 ^ m * ε < g y ∧ g y ≤ 2 ^ (m + 1) * ε},
            ENNReal.ofReal ((ε / g y) ^ b) ∂ν :=
          lintegral_iUnion_le _ _
      _ ≤ ∑' m : ℕ, ENNReal.ofReal ((((2 : ℝ) ^ (-(b - lam))) ^ m)
            * ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
              * llcScale lam theta ε)) :=
          ENNReal.tsum_le_tsum fun m => shell_term_bound hgm hK hlam hb
            htheta hC heps0 hνK hV hε0 hεe hεs m
      _ = ∑' m : ℕ, ENNReal.ofReal ((((2 : ℝ) ^ (-(b - lam))) ^ m))
            * ENNReal.ofReal
              ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
                * llcScale lam theta ε) :=
          tsum_congr fun m => ENNReal.ofReal_mul (pow_nonneg hq0 m)
      _ = (∑' m : ℕ, ENNReal.ofReal ((((2 : ℝ) ^ (-(b - lam))) ^ m)))
            * ENNReal.ofReal
              ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
                * llcScale lam theta ε) :=
          ENNReal.tsum_mul_right
      _ = ENNReal.ofReal ((1 - (2 : ℝ) ^ (-(b - lam)))⁻¹)
            * ENNReal.ofReal
              ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
                * llcScale lam theta ε) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg
            (fun m => pow_nonneg hq0 m)
            (summable_geometric_of_lt_one hq0 hq1),
            tsum_geometric_of_lt_one hq0 hq1]
      _ = ENNReal.ofReal
            (((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
              * (1 - (2 : ℝ) ^ (-(b - lam)))⁻¹) * llcScale lam theta ε) := by
          rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (by linarith))]
          congr 1
          ring
  calc (∫⁻ y in K ∩ {y | ε < g y},
      ENNReal.ofReal ((ε / g y) ^ b) ∂ν).toReal
      ≤ (ENNReal.ofReal
          (((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
            * (1 - (2 : ℝ) ^ (-(b - lam)))⁻¹)
            * llcScale lam theta ε)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top hchain
    _ = ((C * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
          * (1 - (2 : ℝ) ^ (-(b - lam)))⁻¹) * llcScale lam theta ε := by
        refine ENNReal.toReal_ofReal ?_
        have h1 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-(b - lam)))⁻¹ :=
          inv_nonneg.mpr (by linarith)
        exact mul_nonneg (mul_nonneg hDpos.le h1) hllc.le

/-- **The strict peel**: multiplying by one strict weighted
coordinate (`(h+1)/p > λ`) preserves the volume-scaling exponents
exactly. -/
theorem hasLLCExponentsOn_mul_strict_coord [SFinite ν]
    (hK : MeasurableSet K)
    {g : γ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ y ∈ K, 0 ≤ g y) (hg1 : ∀ y ∈ K, g y ≤ 1)
    {p h lam theta : ℝ} (hp : 0 < p) (hh : 0 ≤ h)
    (hlam : 0 < lam) (htheta : 1 ≤ theta)
    (hstrict : lam < (h + 1) / p) (hνK : ν K ≠ ⊤)
    (hg : HasLLCExponentsOn ν K g lam theta) :
    HasLLCExponentsOn
      ((volume.withDensity fun x => ENNReal.ofReal (|x| ^ h)).prod ν)
      (Icc (-1 : ℝ) 1 ×ˢ K)
      (fun z => |z.1| ^ p * g z.2) lam theta := by
  have hh1 : (0 : ℝ) < h + 1 := by linarith
  have hbpos : (0 : ℝ) < (h + 1) / p := hlam.trans hstrict
  rw [hasLLCExponentsOn_iff_eventually_bounds] at hg ⊢
  obtain ⟨c₁, hc₁, c₂, hc₂, hgb⟩ := hg
  obtain ⟨u, hu, hsub⟩ :=
    mem_nhdsGT_iff_exists_Ioo_subset.mp hgb
  set eps0 : ℝ := min u 1 / 2 with heps0def
  have hmin01 : (0 : ℝ) < min u 1 := lt_min hu zero_lt_one
  have heps0 : eps0 ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · positivity
    · have h1 : min u 1 ≤ 1 := min_le_right _ _
      rw [heps0def]
      linarith
  have heps0u : eps0 < u := by
    have h2 : min u 1 ≤ u := min_le_left _ _
    rw [heps0def]
    linarith
  have hVbound : ∀ t ∈ Ioo (0 : ℝ) eps0,
      (ν (K ∩ {y | g y ≤ t})).toReal ≤ c₂ * llcScale lam theta t :=
    fun t ht => (hsub ⟨ht.1, lt_trans ht.2 heps0u⟩).2
  set Dc : ℝ := (c₂ * 2 ^ lam + (2 / eps0) ^ lam * (ν K).toReal)
      * (1 - (2 : ℝ) ^ (-((h + 1) / p - lam)))⁻¹ with hDcdef
  have hq1 : (2 : ℝ) ^ (-((h + 1) / p - lam)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hDcnn : 0 ≤ Dc := by
    have h1 : (0 : ℝ) ≤ (1 - (2 : ℝ) ^ (-((h + 1) / p - lam)))⁻¹ :=
      inv_nonneg.mpr (by linarith)
    have h2 : (0 : ℝ) < c₂ * 2 ^ lam := by positivity
    have h3 : (0 : ℝ) ≤ (2 / eps0) ^ lam * (ν K).toReal := by
      have h4 := heps0.1
      have h5 := ENNReal.toReal_nonneg (a := ν K)
      positivity
    rw [hDcdef]
    exact mul_nonneg (by linarith) h1
  refine ⟨2 / (h + 1) * c₁, by positivity,
    2 / (h + 1) * (c₂ + Dc), by positivity, ?_⟩
  have hwin : Ioo (0 : ℝ) (min eps0 (Real.exp (-1)))
      ∈ nhdsWithin (0 : ℝ) (Ioi 0) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr
      ⟨min eps0 (Real.exp (-1)),
        lt_min heps0.1 (Real.exp_pos _), fun t ht => ht⟩
  filter_upwards [hgb, hwin] with ε hgbε hε
  have hε0 : 0 < ε := hε.1
  have hεs : ε < eps0 := hε.2.trans_le (min_le_left _ _)
  have hεe : ε < Real.exp (-1) := hε.2.trans_le (min_le_right _ _)
  have hm2' : MeasurableSet (K ∩ {y | ε < g y}) :=
    hK.inter (hgm measurableSet_Ioi)
  have hid := prod_weighted_fiber_measure ν hK hgm hp hh hε0 hg0
  have hAfin : ν (K ∩ {y | g y ≤ ε}) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono inter_subset_left)
      (lt_top_iff_ne_top.mpr hνK)).ne
  have hint_le : ∫⁻ y in K ∩ {y | ε < g y},
      ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν
      ≤ ν (K ∩ {y | ε < g y}) := by
    have hpt : ∀ᵐ y ∂(ν.restrict (K ∩ {y | ε < g y})),
        ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ≤ 1 := by
      refine (ae_restrict_iff' hm2').mpr
        (Filter.Eventually.of_forall fun y hy => ?_)
      have hgy : ε < g y := hy.2
      have hgpos : 0 < g y := hε0.trans hgy
      refine ENNReal.ofReal_le_one.mpr ?_
      exact Real.rpow_le_one (by positivity)
        ((div_le_one hgpos).mpr hgy.le) hbpos.le
    refine le_trans (lintegral_mono_ae hpt) ?_
    rw [lintegral_one, Measure.restrict_apply_univ]
  have hBfin : (∫⁻ y in K ∩ {y | ε < g y},
      ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν) ≠ ⊤ :=
    (lt_of_le_of_lt hint_le (lt_of_le_of_lt
      (measure_mono inter_subset_left)
      (lt_top_iff_ne_top.mpr hνK))).ne
  have hVF : sublevelVol
      ((volume.withDensity fun x => ENNReal.ofReal (|x| ^ h)).prod ν)
      (Icc (-1 : ℝ) 1 ×ˢ K) (fun z => |z.1| ^ p * g z.2) ε
      = 2 / (h + 1) * ((ν (K ∩ {y | g y ≤ ε})).toReal
        + (∫⁻ y in K ∩ {y | ε < g y},
            ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν).toReal) := by
    unfold sublevelVol
    rw [hid, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_add hAfin hBfin]
  constructor
  · rw [hVF]
    have h1 : c₁ * llcScale lam theta ε
        ≤ (ν (K ∩ {y | g y ≤ ε})).toReal := hgbε.1
    have h2 : (0 : ℝ) ≤ (∫⁻ y in K ∩ {y | ε < g y},
        ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν).toReal :=
      ENNReal.toReal_nonneg
    calc 2 / (h + 1) * c₁ * llcScale lam theta ε
        = 2 / (h + 1) * (c₁ * llcScale lam theta ε) := by ring
      _ ≤ 2 / (h + 1) * ((ν (K ∩ {y | g y ≤ ε})).toReal
          + (∫⁻ y in K ∩ {y | ε < g y},
              ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν).toReal) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
  · rw [hVF]
    have h1 : (ν (K ∩ {y | g y ≤ ε})).toReal
        ≤ c₂ * llcScale lam theta ε := hgbε.2
    have h2 := strict_integral_bound hgm hK hg1 hlam hstrict htheta
      hc₂ heps0 hνK hVbound hε0 hεe hεs
    calc 2 / (h + 1) * ((ν (K ∩ {y | g y ≤ ε})).toReal
        + (∫⁻ y in K ∩ {y | ε < g y},
            ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν).toReal)
        ≤ 2 / (h + 1) * (c₂ * llcScale lam theta ε
          + Dc * llcScale lam theta ε) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have h3 : (∫⁻ y in K ∩ {y | ε < g y},
              ENNReal.ofReal ((ε / g y) ^ ((h + 1) / p)) ∂ν).toReal
              ≤ Dc * llcScale lam theta ε := by
            rw [hDcdef]
            exact h2
          linarith
      _ = 2 / (h + 1) * (c₂ + Dc) * llcScale lam theta ε := by ring

end SingularLearningTheory
