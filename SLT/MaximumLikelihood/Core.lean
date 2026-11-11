/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The deterministic core of maximum-likelihood asymptotics

Only nonnegativity on the feasible parameter set is used.

On a chart, with `x = √n u^k ≥ 0` at the estimator, `z = ξCM(û)`, `y = max{0, −z}` its positive
part, `q = nKₙ(ŵ) = x² + x z`, `M = max_Z max{0, −ξCM}` the slice maximum and `ω` a bound for the
oscillation of the field between the estimator and the zero slice (projection: `y ≤ M + ω`) and
between the maximiser and its recovery point (`q ≤ −M²/4 + Mω/2`), the errors are controlled by
`D = Mω + ω²/4`:
```
|q + M²/4| ≤ Mω/2 + ω²/4,      |x² − M²/4| ≤ D + (M + ω)√D + (2Mω + ω²)/4 .
```
The square-root term is genuine: a quadratic objective gap of size `D` controls the displacement
only by `√D` (the book's (6.86) states an `O(‖R₁‖)` bound for `nR_g`; the cross term must be kept).
-/

public section

open Real

namespace SingularLearningTheory.MaximumLikelihood

/-- The error functional of the deterministic core, `D + (M + ω)√D + (2Mω + ω²)/4`,
`D = Mω + ω²/4`. -/
@[expose] noncomputable def mleErr (M ω : ℝ) : ℝ :=
  (M * ω + ω ^ 2 / 4) + (M + ω) * Real.sqrt (M * ω + ω ^ 2 / 4) + (2 * M * ω + ω ^ 2) / 4

theorem mleErr_nonneg {M ω : ℝ} (hM : 0 ≤ M) (hω : 0 ≤ ω) : 0 ≤ mleErr M ω := by
  unfold mleErr
  positivity

theorem mleErr_zero (M : ℝ) : mleErr M 0 = 0 := by
  simp [mleErr]

theorem mleErr_mono_left {M M' ω : ℝ} (hω : 0 ≤ ω) (hM : 0 ≤ M) (hMM : M ≤ M') :
    mleErr M ω ≤ mleErr M' ω := by
  unfold mleErr
  have h1 : M * ω + ω ^ 2 / 4 ≤ M' * ω + ω ^ 2 / 4 := by nlinarith
  have h2 : Real.sqrt (M * ω + ω ^ 2 / 4) ≤ Real.sqrt (M' * ω + ω ^ 2 / 4) :=
    Real.sqrt_le_sqrt h1
  have h3 : 0 ≤ Real.sqrt (M * ω + ω ^ 2 / 4) := Real.sqrt_nonneg _
  have h4 : (M + ω) * Real.sqrt (M * ω + ω ^ 2 / 4)
      ≤ (M' + ω) * Real.sqrt (M' * ω + ω ^ 2 / 4) :=
    mul_le_mul (by linarith) h2 h3 (by linarith)
  nlinarith

theorem continuous_mleErr (M : ℝ) : Continuous fun ω ↦ mleErr M ω := by
  unfold mleErr
  fun_prop

/-- For every `M` and `δ > 0` there is `θ > 0` with `mleErr M ω ≤ δ` for `0 ≤ ω ≤ θ`. -/
theorem exists_mleErr_le (M : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ θ > 0, ∀ ω, 0 ≤ ω → ω ≤ θ → mleErr M ω ≤ δ := by
  have h := (continuous_mleErr M).tendsto 0
  rw [mleErr_zero] at h
  obtain ⟨θ, hθ, hθδ⟩ := Metric.tendsto_nhds.mp h δ hδ |> Metric.eventually_nhds_iff.mp
  refine ⟨θ / 2, half_pos hθ, fun ω hω0 hωθ ↦ ?_⟩
  have := hθδ (y := ω) (by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hω0]
    linarith)
  rw [Real.dist_eq, sub_zero] at this
  exact (le_abs_self _).trans this.le

/-- **The deterministic core.** -/
theorem mle_core_bounds {x y z q M ω : ℝ} (hx : 0 ≤ x) (hω : 0 ≤ ω) (hM : 0 ≤ M)
    (hq : q = x ^ 2 + x * z) (hy : y = max 0 (-z)) (hproj : y ≤ M + ω)
    (hrec : q ≤ -(M ^ 2) / 4 + M * ω / 2) :
    |q + M ^ 2 / 4| ≤ M * ω / 2 + ω ^ 2 / 4 ∧ |x ^ 2 - M ^ 2 / 4| ≤ mleErr M ω := by
  have hy0 : 0 ≤ y := hy ▸ le_max_left _ _
  -- `(x − y/2)² ≤ q + y²/4`
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
  obtain ⟨Dv, hD⟩ : ∃ Dv : ℝ, Dv = M * ω + ω ^ 2 / 4 := ⟨_, rfl⟩
  have hD0 : 0 ≤ Dv := hD ▸ by positivity
  have hxyD : (x - y / 2) ^ 2 ≤ Dv := by rw [hD]; nlinarith
  have hylow : M ^ 2 - 2 * M * ω ≤ y ^ 2 := by nlinarith [sq_nonneg (x - y / 2)]
  constructor
  · rw [abs_le]
    constructor
    · nlinarith [sq_nonneg (x - y / 2)]
    · nlinarith
  · obtain ⟨s, hs⟩ : ∃ s : ℝ, s = Real.sqrt Dv := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := hs ▸ Real.sqrt_nonneg _
    have hss : s ^ 2 = Dv := hs ▸ Real.sq_sqrt hD0
    have habs : |x - y / 2| ≤ s := hs ▸ Real.abs_le_sqrt hxyD
    have hErr : mleErr M ω = Dv + (M + ω) * s + (2 * M * ω + ω ^ 2) / 4 := by
      rw [mleErr, hs, hD]
    rw [hErr, abs_le]
    obtain ⟨h1, h2⟩ := abs_le.mp habs
    constructor
    · -- lower bound: `M²/4 − x² ≤ …`
      rcases le_or_gt s (y / 2) with hsy | hsy
      · have hx' : y / 2 - s ≤ x := by linarith
        have hx'0 : 0 ≤ y / 2 - s := by linarith
        have hx2 : (y / 2 - s) ^ 2 ≤ x ^ 2 := pow_le_pow_left₀ hx'0 hx' 2
        nlinarith [mul_nonneg hy0 hs0, mul_nonneg hω hs0, mul_nonneg hM hs0]
      · -- `y/2 < s`: then `M² < 4D + 2Mω`
        have : y ^ 2 < 4 * Dv := by nlinarith
        nlinarith [sq_nonneg x, mul_nonneg hM hs0, mul_nonneg hω hs0]
    · have hxu : x ≤ y / 2 + s := by linarith
      have hx2 : x ^ 2 ≤ (y / 2 + s) ^ 2 := pow_le_pow_left₀ hx hxu 2
      nlinarith [mul_nonneg hy0 hs0, mul_nonneg hω hs0, mul_nonneg hM hs0]



/-- Localization of a minimizer from a relative fluctuation envelope.
Only nonnegativity on the feasible set is needed. -/
theorem mle_localization {A : Type*} {K : A → ℝ} {W : Set A}
    (hK0 : ∀ w ∈ W, 0 ≤ K w) {n : ℕ} (hn : 0 < n) {L : ℝ}
    (hL : 0 ≤ L) {S pre : A → ℝ}
    (hS : ∀ w ∈ W, S w = (n : ℝ) * K w + Real.sqrt n * pre w)
    (henv : ∀ w ∈ W, |pre w| ≤ Real.sqrt (K w) * L)
    {w₀ : A} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    {ŵ : A} (hŵ : ŵ ∈ W) (hmin : ∀ w ∈ W, S ŵ ≤ S w) :
    (n : ℝ) * K ŵ ≤ L ^ 2 ∧ -(L ^ 2) / 4 ≤ S ŵ ∧ S ŵ ≤ 0 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpre0 : pre w₀ = 0 := by
    have := henv w₀ hw₀
    rw [hw₀K, Real.sqrt_zero, zero_mul] at this
    exact abs_nonpos_iff.mp this
  have hS0 : S w₀ = 0 := by rw [hS w₀ hw₀, hw₀K, hpre0]; ring
  have hle : S ŵ ≤ 0 := hS0 ▸ hmin w₀ hw₀
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt ((n : ℝ) * K ŵ) := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ Real.sqrt_nonneg _
  have hxsq : x ^ 2 = (n : ℝ) * K ŵ :=
    hx ▸ Real.sq_sqrt (mul_nonneg hn'.le (hK0 ŵ hŵ))
  have hsqrt : Real.sqrt n * Real.sqrt (K ŵ) = x := by
    rw [hx, ← Real.sqrt_mul hn'.le]
  have hlow : x ^ 2 - x * L ≤ S ŵ := by
    rw [hS ŵ hŵ, ← hxsq]
    have h := henv ŵ hŵ
    have h' : -(Real.sqrt (K ŵ) * L) ≤ pre ŵ := (abs_le.mp h).1
    have : Real.sqrt n * pre ŵ ≥ -(Real.sqrt n * Real.sqrt (K ŵ) * L) := by
      have := mul_le_mul_of_nonneg_left h' (Real.sqrt_nonneg (n : ℝ))
      linarith
    rw [hsqrt] at this
    linarith
  have hxL : x ≤ L := by nlinarith
  refine ⟨?_, ?_, hle⟩
  · rw [← hxsq]
    exact pow_le_pow_left₀ hx0 hxL 2
  · nlinarith [sq_nonneg (x - L / 2)]

end SingularLearningTheory.MaximumLikelihood
