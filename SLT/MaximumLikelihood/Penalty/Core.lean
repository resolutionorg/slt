/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.MaximumLikelihood.Core
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Quadratic bounds with a penalty

The slack term records the penalty change along projection
and recovery; both shifted errors are controlled without selecting an optimizer.
-/

public section

open Filter Topology Real

namespace SingularLearningTheory.MaximumLikelihood

/-- The error functional with slack: `D + (M + ω)√D + (2Mω + ω²)/4`, `D = Mω + ω²/4 + s`. -/
@[expose] noncomputable def mleErr' (M ω s : ℝ) : ℝ :=
  (M * ω + ω ^ 2 / 4 + s) + (M + ω) * Real.sqrt (M * ω + ω ^ 2 / 4 + s) + (2 * M * ω + ω ^ 2) / 4

theorem mleErr'_zero (M : ℝ) : mleErr' M 0 0 = 0 := by simp [mleErr']

private theorem continuous_mleErr'_diag (M : ℝ) : Continuous fun t ↦ mleErr' M t t := by
  unfold mleErr'
  fun_prop

/-- Monotone in `M`, `ω` and `s` on the nonnegative cone. -/
theorem mleErr'_mono {M M' ω ω' s s' : ℝ} (hM : 0 ≤ M) (hω : 0 ≤ ω) (hs : 0 ≤ s) (hMM : M ≤ M')
    (hωω : ω ≤ ω') (hss : s ≤ s') : mleErr' M ω s ≤ mleErr' M' ω' s' := by
  unfold mleErr'
  have h1 : M * ω + ω ^ 2 / 4 + s ≤ M' * ω' + ω' ^ 2 / 4 + s' := by nlinarith
  have h2 : Real.sqrt (M * ω + ω ^ 2 / 4 + s) ≤ Real.sqrt (M' * ω' + ω' ^ 2 / 4 + s') :=
    Real.sqrt_le_sqrt h1
  have h3 : 0 ≤ Real.sqrt (M * ω + ω ^ 2 / 4 + s) := Real.sqrt_nonneg _
  have h4 : (M + ω) * Real.sqrt (M * ω + ω ^ 2 / 4 + s)
      ≤ (M' + ω') * Real.sqrt (M' * ω' + ω' ^ 2 / 4 + s') :=
    mul_le_mul (by linarith) h2 h3 (by linarith)
  nlinarith

theorem exists_mleErr'_le (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ > 0, ∀ t, 0 ≤ t → t ≤ θ → mleErr' M t t ≤ δ := by
  have h := (continuous_mleErr'_diag M).tendsto 0
  rw [mleErr'_zero] at h
  obtain ⟨θ, hθ, hθδ⟩ := Metric.tendsto_nhds.mp h δ hδ |> Metric.eventually_nhds_iff.mp
  refine ⟨θ / 2, half_pos hθ, fun t ht0 htθ ↦ ?_⟩
  have := hθδ (y := t) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht0]
    linarith)
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- **The deterministic core with slack.** -/
private theorem mle_core_bounds' {x y z q M ω s : ℝ} (hx : 0 ≤ x) (hω : 0 ≤ ω) (hM : 0 ≤ M)
    (hs : 0 ≤ s)
    (hq : q = x ^ 2 + x * z) (hy : y = max 0 (-z)) (hproj : y ≤ M + ω)
    (hrec : q ≤ -(M ^ 2) / 4 + M * ω / 2 + s) :
    |q + M ^ 2 / 4| ≤ M * ω / 2 + ω ^ 2 / 4 + s ∧ |x ^ 2 - M ^ 2 / 4| ≤ mleErr' M ω s := by
  have hy0 : 0 ≤ y := hy ▸ le_max_left _ _
  have hsq : (x - y / 2) ^ 2 ≤ q + y ^ 2 / 4 := by
    rcases le_or_gt (-z) 0 with hz | hz
    · have hy' : y = 0 := by rw [hy, max_eq_left hz]
      rw [hy', hq]
      nlinarith [mul_nonneg hx (neg_nonpos.mp hz)]
    · have hy' : y = -z := by rw [hy, max_eq_right hz.le]
      rw [hy', hq]
      ring_nf
      exact le_rfl
  have hy2 : y ^ 2 ≤ (M + ω) ^ 2 := pow_le_pow_left₀ hy0 hproj 2
  obtain ⟨Dv, hD⟩ : ∃ Dv : ℝ, Dv = M * ω + ω ^ 2 / 4 + s := ⟨_, rfl⟩
  have hD0 : 0 ≤ Dv := hD ▸ by positivity
  have hxyD : (x - y / 2) ^ 2 ≤ Dv := by rw [hD]; nlinarith
  have hylow : M ^ 2 - 2 * M * ω - 4 * s ≤ y ^ 2 := by nlinarith [sq_nonneg (x - y / 2)]
  constructor
  · rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (x - y / 2)]
    · nlinarith
  · obtain ⟨t, ht⟩ : ∃ t : ℝ, t = Real.sqrt Dv := ⟨_, rfl⟩
    have ht0 : 0 ≤ t := ht ▸ Real.sqrt_nonneg _
    have htt : t ^ 2 = Dv := ht ▸ Real.sq_sqrt hD0
    have habs : |x - y / 2| ≤ t := ht ▸ Real.abs_le_sqrt hxyD
    have hErr : mleErr' M ω s = Dv + (M + ω) * t + (2 * M * ω + ω ^ 2) / 4 := by
      rw [mleErr', ht, hD]
    rw [hErr, abs_le]
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    constructor
    · rcases le_or_gt t (y / 2) with hty | hty
      · have hx' : y / 2 - t ≤ x := by linarith
        have hx'0 : 0 ≤ y / 2 - t := by linarith
        have hx2 : (y / 2 - t) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hx'0 hx' 2
        nlinarith [mul_nonneg hy0 ht0, mul_nonneg hω ht0, mul_nonneg hM ht0]
      · have : y ^ 2 < 4 * Dv := by nlinarith
        nlinarith [sq_nonneg x, mul_nonneg hM ht0, mul_nonneg hω ht0]
    · have hxu : x ≤ y / 2 + t := by linarith
      have hx2 : x ^ 2 ≤ (y / 2 + t) ^ 2 := pow_le_pow_left₀ hx hxu 2
      nlinarith [mul_nonneg hy0 ht0, mul_nonneg hω ht0, mul_nonneg hM ht0]

/-- **Subpolynomial growth**: if `aₙ ≥ 0` and `aₙ / n^p → 0` for every `p > 0`, then
`aₙ ((1 + aₙ)/n)^c → 0` for every `c > 0`. -/
private theorem tendsto_mul_rpow_div_of_subpoly {a : ℕ → ℝ} (ha0 : ∀ n, 0 ≤ a n)
    (hsub : ∀ p : ℝ, 0 < p → Tendsto (fun n : ℕ ↦ a n / (n : ℝ) ^ p) atTop (𝓝 0)) {c : ℝ}
    (hc : 0 < c) :
    Tendsto (fun n : ℕ ↦ a n * ((1 + a n) / (n : ℝ)) ^ c) atTop (𝓝 0) := by
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = c / (2 * (1 + c)) := ⟨_, rfl⟩
  have hp0 : 0 < p := hp ▸ by positivity
  have hexp : p + (p - 1) * c = -(c / 2) := by
    rw [hp]
    field_simp
    ring
  -- eventually `aₙ ≤ n^p`
  have hev : ∀ᶠ n : ℕ in atTop, a n ≤ (n : ℝ) ^ p := by
    have h := (hsub p hp0).eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [h, eventually_gt_atTop 0] with n hn hn0
    have hnp : 0 < (n : ℝ) ^ p := Real.rpow_pos_of_pos (by exact_mod_cast hn0) _
    rw [div_lt_iff₀ hnp, one_mul] at hn
    exact hn.le
  -- the bound `2^c n^{-c/2}`
  have hbound : Tendsto (fun n : ℕ ↦ (2 : ℝ) ^ c * (n : ℝ) ^ (-(c / 2))) atTop (𝓝 0) := by
    have := (tendsto_rpow_neg_atTop (half_pos hc)).comp tendsto_natCast_atTop_atTop
    have h2 := this.const_mul ((2 : ℝ) ^ c)
    rw [mul_zero] at h2
    exact h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun n ↦ mul_nonneg (ha0 n) (Real.rpow_nonneg
      (div_nonneg (by linarith [ha0 n]) (Nat.cast_nonneg n)) _)) ?_
  filter_upwards [hev, eventually_gt_atTop 0] with n hn hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ p := Real.one_le_rpow (by exact_mod_cast hn0) hp0.le
  have h1 : (1 + a n) / (n : ℝ) ≤ 2 * (n : ℝ) ^ (p - 1) := by
    rw [div_le_iff₀ hn', Real.rpow_sub_one hn'.ne', mul_assoc, div_mul_cancel₀ _ hn'.ne']
    linarith
  have hq0 : 0 ≤ (1 + a n) / (n : ℝ) := div_nonneg (by linarith [ha0 n]) hn'.le
  have h2 : ((1 + a n) / (n : ℝ)) ^ c ≤ (2 * (n : ℝ) ^ (p - 1)) ^ c :=
    Real.rpow_le_rpow hq0 h1 hc.le
  calc a n * ((1 + a n) / (n : ℝ)) ^ c ≤ (n : ℝ) ^ p * (2 * (n : ℝ) ^ (p - 1)) ^ c :=
        mul_le_mul hn h2 (Real.rpow_nonneg hq0 _) (by positivity)
    _ = (2 : ℝ) ^ c * (n : ℝ) ^ (p + (p - 1) * c) := by
        rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul hn'.le,
          Real.rpow_add hn']
        ring
    _ = (2 : ℝ) ^ c * (n : ℝ) ^ (-(c / 2)) := by rw [hexp]

/-- **The deterministic core of regime (2), pure real form.** With `q = x² + xz`,
`y = max{0, −z} ≤ m_z + ω`, the foot value `F_z = ¼m_z² − p_z ≤ F`, `|p̂ − p_z| ≤ c` and the
recovery bound `q + p̂ ≤ −F + Mω/2 + c` (`0 ≤ m_z ≤ M`):
`|q + p̂ + F| ≤ Mω/2 + ω²/4 + c` and
`|x² − p̂ − F| ≤ mleErr' M ω (Mω/2 + 2c) + Mω + ω²/4 + 3c`. -/
theorem penalized_core_bounds {x y z q M mz pŵ pz F Fz ω c : ℝ} (hx : 0 ≤ x) (hω : 0 ≤ ω)
    (hmz : 0 ≤ mz) (hmzM : mz ≤ M) (hc : 0 ≤ c) (hq : q = x ^ 2 + x * z) (hy : y = max 0 (-z))
    (hproj : y ≤ mz + ω) (hFz : Fz = mz ^ 2 / 4 - pz) (hFzF : Fz ≤ F) (hp : |pŵ - pz| ≤ c)
    (hrec : q + pŵ ≤ -F + M * ω / 2 + c) :
    |q + pŵ + F| ≤ M * ω / 2 + ω ^ 2 / 4 + c ∧
      |x ^ 2 - pŵ - F| ≤ mleErr' M ω (M * ω / 2 + 2 * c) + M * ω + ω ^ 2 / 4 + 3 * c ∧
      F - Fz ≤ M * ω + ω ^ 2 / 4 + 2 * c ∧
      |x ^ 2 - mz ^ 2 / 4| ≤ mleErr' M ω (M * ω / 2 + 2 * c) := by
  have hM : 0 ≤ M := hmz.trans hmzM
  have hy0 : 0 ≤ y := hy ▸ le_max_left _ _
  have hxz : -(x * y) ≤ x * z := by
    have : -z ≤ y := hy ▸ le_max_right _ _
    nlinarith
  have hqlow : -(y ^ 2) / 4 ≤ q := by
    rw [hq]
    nlinarith [sq_nonneg (x - y / 2)]
  have hy2 : y ^ 2 ≤ (mz + ω) ^ 2 := pow_le_pow_left₀ hy0 hproj 2
  have hp1 := (abs_le.mp hp).1
  have hp2 := (abs_le.mp hp).2
  -- the lower bound on the penalised value
  have hlow : -(Fz) - mz * ω / 2 - ω ^ 2 / 4 - c ≤ q + pŵ := by
    rw [hFz]
    nlinarith
  -- the foot is a near-maximiser
  have hgap : F - Fz ≤ M * ω + ω ^ 2 / 4 + 2 * c := by
    have hmω : mz * ω / 2 ≤ M * ω / 2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmzM hω) (by norm_num)
    linarith
  -- the recovery bound in the form of `mle_core_bounds'` with `M := m_z`
  have hcore : |x ^ 2 - mz ^ 2 / 4| ≤ mleErr' M ω (M * ω / 2 + 2 * c) := by
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (M - mz) * ω / 2 + 2 * c := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by
      rw [hs]
      have : 0 ≤ (M - mz) * ω := mul_nonneg (by linarith) hω
      linarith
    have hrec' : q ≤ -(mz ^ 2) / 4 + mz * ω / 2 + s := by
      rw [hs]
      have : q ≤ -F - pŵ + M * ω / 2 + c := by linarith
      have h2 : -F - pŵ ≤ -Fz - pz + c := by linarith
      rw [hFz] at h2
      linarith
    obtain ⟨-, hb⟩ := mle_core_bounds' hx hω hmz hs0 hq hy hproj hrec'
    have hmono : mleErr' mz ω s ≤ mleErr' M ω (M * ω / 2 + 2 * c) := by
      refine mleErr'_mono hmz hω hs0 hmzM le_rfl ?_
      rw [hs]
      have : 0 ≤ mz * ω := mul_nonneg hmz hω
      linarith
    exact hb.trans hmono
  refine ⟨?_, ?_, hgap, hcore⟩
  · rw [abs_le]
    constructor
    · have hmω : mz * ω / 2 ≤ M * ω / 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmzM hω) (by norm_num)
      linarith
    · linarith [sq_nonneg ω]
  · have e : x ^ 2 - pŵ - F = (x ^ 2 - mz ^ 2 / 4) + (Fz - F) + (pz - pŵ) := by
      rw [hFz]; ring
    rw [e]
    calc |(x ^ 2 - mz ^ 2 / 4) + (Fz - F) + (pz - pŵ)|
        ≤ |x ^ 2 - mz ^ 2 / 4| + |Fz - F| + |pz - pŵ| :=
          (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ mleErr' M ω (M * ω / 2 + 2 * c) + (M * ω + ω ^ 2 / 4 + 2 * c) + c := by
          refine add_le_add (add_le_add hcore ?_) ?_
          · rw [abs_sub_comm, abs_of_nonneg (by linarith)]
            exact hgap
          · rw [abs_sub_comm]
            exact hp
      _ = mleErr' M ω (M * ω / 2 + 2 * c) + M * ω + ω ^ 2 / 4 + 3 * c := by ring


/-- Crude penalized localization from the relative envelope and comparison with a
feasible zero. Here x=sqrt(n*K(ŵ)) and q=n*Kn(ŵ). -/
theorem penalized_localization_bounds {x q H a Sg : ℝ}
    (hx : 0 ≤ x) (hH : 0 ≤ H) (ha : 0 ≤ a) (hSg : 0 ≤ Sg)
    (hdev : |q - x ^ 2| ≤ x * H) (hcmp : q ≤ 2 * a * Sg) :
    x ^ 2 ≤ 2 * H ^ 2 + 4 * a * Sg ∧ |q| ≤ 2 * x ^ 2 + H ^ 2 := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp hdev
  constructor
  · nlinarith [sq_nonneg (x - H), mul_nonneg ha hSg]
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (x - H)]

end SingularLearningTheory.MaximumLikelihood
