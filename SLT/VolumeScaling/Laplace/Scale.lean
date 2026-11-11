/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Defs
import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


/-!
# The Laplace-side model scale `s^(−λ) (log s)^(θ−1)`

The deterministic Laplace asymptotic compares the Laplace
integral `∫_K e^{−s·f} dμ` of a function with `HasLLCOn` volume scaling
`(λ, θ)` against the target scale

  `SingularLearningTheory.laplaceScale lam theta s = s^(−λ) · (log s)^(θ−1)`  at `atTop`.

This file holds the scale's basic lemmas: positivity on `(1, ∞)`, the
bridge to the ε-side scale (`laplaceScale lam theta s = llcScale lam theta
s⁻¹`), and the exponential domination: any fixed-rate
exponential `e^{−ε₀·s}` is `=o[atTop]` of every `SingularLearningTheory.laplaceScale`.
-/

public section

open Filter Asymptotics Set
open scoped Topology

namespace SingularLearningTheory

open SingularLearningTheory

/-- The Laplace-side model scale `s^(−λ) (log s)^(θ−1)` (real powers). Only
its germ at `atTop` matters; there both `rpow` bases are eventually
positive, so no guards are needed. -/
@[expose] noncomputable def laplaceScale (lam theta : ℝ) (s : ℝ) : ℝ :=
  s ^ (-lam) * Real.log s ^ (theta - 1)

theorem laplaceScale_pos {lam theta s : ℝ} (hs : 1 < s) :
    0 < laplaceScale lam theta s :=
  mul_pos (Real.rpow_pos_of_pos (one_pos.trans hs) _)
    (Real.rpow_pos_of_pos (Real.log_pos hs) _)

/-- Load-bearing positivity: the scale is eventually strictly positive at
`atTop`. -/
theorem laplaceScale_eventually_pos {lam theta : ℝ} :
    ∀ᶠ s in atTop, 0 < laplaceScale lam theta s := by
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  exact laplaceScale_pos hs

/-- The bridge to the ε-side scale: `laplaceScale λ θ s = llcScale λ θ s⁻¹`
for `s > 0`. This transports the `llcScale` lemmas to the Laplace
side. -/
theorem laplaceScale_eq_llcScale_inv {lam theta s : ℝ} (hs : 0 < s) :
    laplaceScale lam theta s = llcScale lam theta s⁻¹ := by
  unfold laplaceScale llcScale
  rw [Real.log_inv, neg_neg, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le]

/-- The ratio form of exponential domination: `e^{−s·ε₀} / laplaceScale → 0`
at `atTop`, for any `ε₀ > 0` and any exponents. -/
theorem tendsto_exp_neg_mul_div_laplaceScale {lam theta : ℝ} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    Tendsto (fun s => Real.exp (-(s * ε₀)) / laplaceScale lam theta s)
      atTop (𝓝 0) := by
  have hbound : Tendsto (fun s : ℝ => s ^ (lam + |1 - theta|) * Real.exp (-ε₀ * s))
      atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ ε₀ hε₀
  refine squeeze_zero' ?_ ?_ hbound
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
    exact div_nonneg (Real.exp_nonneg _) (laplaceScale_pos hs).le
  · filter_upwards [eventually_ge_atTop (Real.exp 1)] with s hs
    have hs1 : 1 < s := lt_of_lt_of_le (by
      have := Real.exp_one_gt_d9
      linarith) hs
    have hs0 : 0 < s := one_pos.trans hs1
    have hlog1 : 1 ≤ Real.log s := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hs
    have hlogpos : 0 < Real.log s := lt_of_lt_of_le one_pos hlog1
    -- Rewrite the ratio as `e^{−s·ε₀} · s^λ · (log s)^(1−θ)`.
    have hratio : Real.exp (-(s * ε₀)) / laplaceScale lam theta s
        = Real.exp (-(s * ε₀)) * s ^ lam * Real.log s ^ (1 - theta) := by
      unfold laplaceScale
      rw [div_eq_mul_inv, mul_inv, ← Real.rpow_neg hs0.le, neg_neg,
        ← Real.rpow_neg hlogpos.le, mul_assoc]
      ring_nf
    rw [hratio]
    -- `(log s)^(1−θ) ≤ s^|1−θ|`.
    have hlogpow : Real.log s ^ (1 - theta) ≤ s ^ |1 - theta| := by
      rcases le_total 0 (1 - theta) with hθ | hθ
      · rw [abs_of_nonneg hθ]
        exact Real.rpow_le_rpow (Real.log_nonneg hs1.le)
          ((Real.log_le_sub_one_of_pos hs0).trans (by linarith)) hθ
      · calc Real.log s ^ (1 - theta)
            ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hlog1 hθ
          _ ≤ s ^ |1 - theta| :=
            Real.one_le_rpow hs1.le (abs_nonneg _)
    calc Real.exp (-(s * ε₀)) * s ^ lam * Real.log s ^ (1 - theta)
        ≤ Real.exp (-(s * ε₀)) * s ^ lam * s ^ |1 - theta| := by
          have h1 : 0 ≤ Real.exp (-(s * ε₀)) * s ^ lam :=
            mul_nonneg (Real.exp_nonneg _) (Real.rpow_nonneg hs0.le _)
          exact mul_le_mul_of_nonneg_left hlogpow h1
      _ = s ^ (lam + |1 - theta|) * Real.exp (-ε₀ * s) := by
          rw [Real.rpow_add hs0, show -(s * ε₀) = -ε₀ * s by ring]
          ring

/-- **Exponential half.** A fixed-rate exponential is little-o of
every Laplace scale: `e^{−s·ε₀} =o[atTop] s^{−λ}(log s)^{θ−1}`. -/
theorem isLittleO_exp_neg_laplaceScale {lam theta : ℝ} {ε₀ : ℝ}
    (hε₀ : 0 < ε₀) :
    (fun s => Real.exp (-(s * ε₀))) =o[atTop] laplaceScale lam theta := by
  rw [isLittleO_iff_tendsto']
  · exact tendsto_exp_neg_mul_div_laplaceScale hε₀
  · filter_upwards [laplaceScale_eventually_pos (lam := lam) (theta := theta)]
      with s hs h0
    exact absurd h0 hs.ne'

end SingularLearningTheory
