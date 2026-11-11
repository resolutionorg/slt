/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import Mathlib.MeasureTheory.Order.Group.Lattice
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Integral.IntegrableOn
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
# Analytic helper lemmas

Elementary real-analysis facts with no thesis counterpart, shared by the
singular-integrals and free-energy chapters: `log n ≤ n^c / c`, the domination of
powers of `|log t|` by monomials, and the convergence of Gamma-type integrals with
logarithmic weights `∫₀^∞ t^(s-1) e^{-t} |log t|^r dt`.
-/

public section

open MeasureTheory Set

namespace Real

/-- No thesis counterpart; used by `integrableOn_rpow_mul_exp_neg_mul_abs_log_pow`. For
`x, y ≥ 0`, `(x + y)^r ≤ 2^r (x^r + y^r)`. -/
theorem _root_.add_pow_le_two_pow_mul_add_pow {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (r : ℕ) :
    (x + y) ^ r ≤ 2 ^ r * (x ^ r + y ^ r) := by
  have h2 : (0 : ℝ) ≤ 2 ^ r := pow_nonneg (by norm_num) r
  rcases le_total x y with h | h
  · calc (x + y) ^ r ≤ (2 * y) ^ r := pow_le_pow_left₀ (by linarith) (by linarith) r
      _ = 2 ^ r * y ^ r := mul_pow 2 y r
      _ ≤ 2 ^ r * (x ^ r + y ^ r) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (pow_nonneg hx r)) h2
  · calc (x + y) ^ r ≤ (2 * x) ^ r := pow_le_pow_left₀ (by linarith) (by linarith) r
      _ = 2 ^ r * x ^ r := mul_pow 2 x r
      _ ≤ 2 ^ r * (x ^ r + y ^ r) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (pow_nonneg hy r)) h2

/-- No thesis counterpart; used by `integrableOn_rpow_mul_exp_neg_mul_abs_log_pow`. For
`t > 0` and `ε > 0`, `|log t| ≤ (t^ε + t^(-ε)) / ε`: on `t ≥ 1` the first term dominates,
on `t ≤ 1` the second (apply `Real.log_le_rpow_div` to `1/t`). -/
private theorem abs_log_le_rpow_add_rpow_neg_div {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    |Real.log t| ≤ (t ^ ε + t ^ (-ε)) / ε := by
  have h1 : 0 ≤ t ^ ε / ε := div_nonneg (Real.rpow_nonneg ht.le ε) hε.le
  have h2 : 0 ≤ t ^ (-ε) / ε := div_nonneg (Real.rpow_nonneg ht.le (-ε)) hε.le
  rw [add_div]
  rcases le_total 1 t with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h)]
    linarith [Real.log_le_rpow_div (zero_le_one.trans h) hε]
  · rw [abs_of_nonpos (Real.log_nonpos ht.le h), ← Real.log_inv]
    have hinv : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr h
    have := Real.log_le_rpow_div (zero_le_one.trans hinv) hε
    rw [Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this
    linarith

/-- No thesis counterpart; used by `integrableOn_rpow_mul_exp_neg_mul_abs_log_pow`. Powers of
`|log t|` are dominated by a pair of monomials `t^(±εr)`. -/
theorem abs_log_pow_le_rpow_add_rpow_neg {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) (r : ℕ) :
    |Real.log t| ^ r ≤ (2 / ε) ^ r * (t ^ (ε * r) + t ^ (-ε * r)) := by
  calc |Real.log t| ^ r ≤ ((t ^ ε + t ^ (-ε)) / ε) ^ r :=
        pow_le_pow_left₀ (abs_nonneg _) (abs_log_le_rpow_add_rpow_neg_div ht hε) r
    _ = (t ^ ε + t ^ (-ε)) ^ r / ε ^ r := div_pow _ _ _
    _ ≤ 2 ^ r * ((t ^ ε) ^ r + (t ^ (-ε)) ^ r) / ε ^ r := by
        gcongr
        exact add_pow_le_two_pow_mul_add_pow (Real.rpow_nonneg ht.le _)
          (Real.rpow_nonneg ht.le _) r
    _ = (2 / ε) ^ r * (t ^ (ε * r) + t ^ (-ε * r)) := by
        rw [div_pow, ← Real.rpow_natCast (t ^ ε), ← Real.rpow_natCast (t ^ (-ε)),
          ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le]
        ring

/-- The Gamma-type integral with a logarithmic weight converges: for `s > 0` and `r : ℕ`,
`∫₀^∞ t^(s-1) e^{-t} |log t|^r dt < ∞`. No thesis counterpart; used for the upper bound in
[Hit26, Theorem 3.2.6]. -/
theorem _root_.integrableOn_rpow_mul_exp_neg_mul_abs_log_pow {s : ℝ} (hs : 0 < s) (r : ℕ) :
    IntegrableOn (fun t : ℝ ↦ t ^ (s - 1) * Real.exp (-t) * |Real.log t| ^ r) (Ioi 0) := by
  set ε : ℝ := s / (2 * (r + 1)) with hε_def
  have hε : 0 < ε := by positivity
  have hrε : ε * r < s := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  have hpos : 0 < s + ε * r := by positivity
  have hneg : 0 < s - ε * r := by linarith
  have hg : IntegrableOn (fun t : ℝ ↦ (2 / ε) ^ r *
      (Real.exp (-t) * t ^ (s + ε * r - 1) + Real.exp (-t) * t ^ (s - ε * r - 1))) (Ioi 0) :=
    ((Real.GammaIntegral_convergent hpos).add (Real.GammaIntegral_convergent hneg)).const_mul _
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      t ^ (s - 1) * Real.exp (-t) * |Real.log t| ^ r).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    have ht : 0 < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc t ^ (s - 1) * Real.exp (-t) * |Real.log t| ^ r
        ≤ t ^ (s - 1) * Real.exp (-t) * ((2 / ε) ^ r * (t ^ (ε * r) + t ^ (-ε * r))) := by
          gcongr
          exact abs_log_pow_le_rpow_add_rpow_neg ht hε r
      _ = (2 / ε) ^ r * (Real.exp (-t) * (t ^ (s - 1) * t ^ (ε * r))
            + Real.exp (-t) * (t ^ (s - 1) * t ^ (-ε * r))) := by ring
      _ = _ := by
          rw [← Real.rpow_add ht, ← Real.rpow_add ht]
          ring_nf

/-- As `integrableOn_rpow_mul_exp_neg_mul_abs_log_pow`, with the logarithm shifted by a
positive constant: `∫₀^∞ t^(s-1) e^{-t} |log (c/t)|^r dt < ∞`. No thesis counterpart; used for
the upper bound in [Hit26, Theorem 3.2.6]. -/
theorem _root_.integrableOn_rpow_mul_exp_neg_mul_abs_log_div_pow {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (r : ℕ) :
    IntegrableOn (fun t : ℝ ↦ t ^ (s - 1) * Real.exp (-t) * |Real.log (c / t)| ^ r)
      (Ioi 0) := by
  have hg : IntegrableOn (fun t : ℝ ↦
      2 ^ r * |Real.log c| ^ r * (Real.exp (-t) * t ^ (s - 1))
        + 2 ^ r * (t ^ (s - 1) * Real.exp (-t) * |Real.log t| ^ r)) (Ioi 0) :=
    ((Real.GammaIntegral_convergent hs).const_mul _).add
      ((integrableOn_rpow_mul_exp_neg_mul_abs_log_pow hs r).const_mul _)
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Measurable fun t : ℝ ↦
      t ^ (s - 1) * Real.exp (-t) * |Real.log (c / t)| ^ r).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Filter.Eventually.of_forall fun t ht ↦ ?_
    have ht : 0 < t := ht
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hlog : |Real.log (c / t)| ^ r ≤ 2 ^ r * (|Real.log c| ^ r + |Real.log t| ^ r) := by
      calc |Real.log (c / t)| ^ r ≤ (|Real.log c| + |Real.log t|) ^ r := by
            gcongr
            rw [Real.log_div hc.ne' ht.ne']
            exact abs_sub _ _
        _ ≤ _ := add_pow_le_two_pow_mul_add_pow (abs_nonneg _) (abs_nonneg _) r
    calc t ^ (s - 1) * Real.exp (-t) * |Real.log (c / t)| ^ r
        ≤ t ^ (s - 1) * Real.exp (-t) * (2 ^ r * (|Real.log c| ^ r + |Real.log t| ^ r)) := by
          gcongr
      _ = _ := by ring

/-- `n^λ e^{-cn}` is bounded for `n ≥ 0`, `c > 0`, `λ ≥ 0`. No thesis counterpart; used for the
tail term in [Hit26, Theorem 3.3.9]. -/
theorem exists_rpow_mul_exp_neg_le {lam c : ℝ} (hc : 0 < c) :
    ∃ C, ∀ n : ℝ, 1 ≤ n → n ^ lam * Real.exp (-(c * n)) ≤ C := by
  set N : ℕ := ⌈lam⌉₊
  refine ⟨(N.factorial : ℝ) / c ^ N, fun n hn ↦ ?_⟩
  have hn0 : 0 < n := by linarith
  have h1 : n ^ lam ≤ n ^ (N : ℝ) := Real.rpow_le_rpow_of_exponent_le hn (Nat.le_ceil lam)
  have h2 : (c * n) ^ N / (N.factorial : ℝ) ≤ Real.exp (c * n) :=
    Real.pow_div_factorial_le_exp _ (by positivity) N
  rw [Real.rpow_natCast] at h1
  have hexp : 0 < Real.exp (c * n) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hexp]
  calc n ^ lam ≤ n ^ N := h1
    _ = (c * n) ^ N / c ^ N := by rw [mul_pow, mul_div_cancel_left₀ _ (pow_pos hc N).ne']
    _ ≤ Real.exp (c * n) * (N.factorial : ℝ) / c ^ N := by
        gcongr
        rwa [div_le_iff₀ (by positivity)] at h2
    _ = (N.factorial : ℝ) / c ^ N * Real.exp (c * n) := by ring

end Real
