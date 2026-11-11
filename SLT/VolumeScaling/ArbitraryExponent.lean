/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
import SLT.VolumeScaling.Invariance
import SLT.VolumeScaling.SpectatorFactor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Arbitrary-exponent monomial read-off

The even-exponent read-off `hasLLCExponentsOn_weighted_monomial_support` (`SpectatorFactor`)
proves the sublevel-volume scaling of a weighted monomial only for an **even** exponent `2k`.
This file removes the evenness restriction: for an arbitrary natural exponent vector
`e : Fin n → ℕ`, the monomial `∏ᵢ |xᵢ|^{eᵢ}` on a centered cube, against the product of
one-dimensional power densities `|x|^{hᵢ}`, has the expected sublevel-volume exponents.

The proof is the square-threshold transfer (`HasLLCExponentsOn.of_sq`) applied to the even
read-off at the doubled exponent `2e`: since `∏ᵢ |xᵢ|^{2eᵢ} = (∏ᵢ |xᵢ|^{eᵢ})²`, the even
read-off at `2e` (with model exponent `lam/2`) gives the square's exponents, and `of_sq` peels
the square. Halving the model exponent preserves both the least ratio and the count of
coordinates attaining it, so the multiplicity is unchanged. This is the form of the read-off
that the chart-local computation (`ChartLocal`) uses.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal NNReal

namespace SingularLearningTheory

/-- **Arbitrary-exponent monomial read-off.** For an arbitrary natural exponent
vector `e`, the monomial `∏ᵢ |xᵢ|^{eᵢ}` on the centered cube `[-R,R]ⁿ`, against
the product of one-dimensional `|x|^{hᵢ}`-weighted Lebesgue measures, has
sublevel-volume exponent `lam` (assumed to be the least of `(hᵢ+1)/eᵢ` over
coordinates with `eᵢ ≠ 0`, via `hmin`/`hatt`) and multiplicity the number of
coordinates attaining it. Derived from the even-exponent read-off at `2e` by the
square-threshold transfer. -/
theorem hasLLCExponentsOn_weighted_monomial_support_nat {n : ℕ}
    (e : Fin n → ℕ) (h : Fin n → ℝ) (hh : ∀ i, 0 ≤ h i) {lam : ℝ}
    (hmin : ∀ i, 0 < e i → lam ≤ (h i + 1) / (e i : ℝ))
    (hatt : ∃ i, 0 < e i ∧ (h i + 1) / (e i : ℝ) = lam)
    {R : ℝ} (hR : 0 < R) :
    HasLLCExponentsOn
      (Measure.pi fun i => volume.withDensity fun x => ENNReal.ofReal (|x| ^ h i))
      (Set.univ.pi fun _ : Fin n => Icc (-R) R)
      (fun x => ∏ i, |x i| ^ (e i : ℝ))
      lam ((Finset.univ.filter fun i => 0 < e i ∧ (h i + 1) / (e i : ℝ) = lam).card) := by
  classical
  -- Per-coordinate ratio identity, valid where `eᵢ ≠ 0`.
  have hratio : ∀ i, 0 < e i →
      ((h i + 1) / (2 * (e i : ℝ)) = lam / 2 ↔ (h i + 1) / (e i : ℝ) = lam) := by
    intro i hei
    have he0 : (e i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hei.ne'
    have h2e0 : (2 * (e i : ℝ)) ≠ 0 := mul_ne_zero two_ne_zero he0
    rw [div_eq_iff he0, div_eq_iff h2e0]
    constructor <;> intro H <;> linear_combination H
  -- Translate the hypotheses to the even (doubled-exponent) form.
  have hlam : 0 < lam := by
    obtain ⟨i, hei, hi⟩ := hatt
    rw [← hi]
    exact div_pos (by linarith [hh i]) (by exact_mod_cast hei)
  have hlam2 : 0 < lam / 2 := by linarith
  have hmin2 : ∀ i, 0 < e i → lam / 2 ≤ (h i + 1) / (2 * (e i : ℝ)) := by
    intro i hei
    have he0 : (e i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hei.ne'
    have heq : (h i + 1) / (2 * (e i : ℝ)) = ((h i + 1) / (e i : ℝ)) / 2 := by
      rw [div_div, mul_comm (e i : ℝ) 2]
    rw [heq]; linarith [hmin i hei]
  have hatt2 : ∃ i, 0 < e i ∧ (h i + 1) / (2 * (e i : ℝ)) = lam / 2 := by
    obtain ⟨i, hei, hr⟩ := hatt
    exact ⟨i, hei, (hratio i hei).mpr hr⟩
  -- The even read-off at exponent `2e`, model exponent `lam/2`.
  have hbase := hasLLCExponentsOn_weighted_monomial_support e h hh hmin2 hatt2 hR
  -- Its function is the square of the target monomial.
  have hfun : (fun x : Fin n → ℝ => ∏ i, |x i| ^ (2 * (e i : ℝ)))
      = fun x => (∏ i, |x i| ^ (e i : ℝ)) ^ 2 := by
    funext x
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Real.rpow_natCast (|x i| ^ (e i : ℝ)) 2,
      ← Real.rpow_mul (abs_nonneg (x i))]
    congr 1
    push_cast; ring
  rw [hfun] at hbase
  -- Halving preserves the multiplicity: rewrite the goal's count to the even one.
  have htheta : (Finset.univ.filter fun i => 0 < e i ∧ (h i + 1) / (e i : ℝ) = lam).card
      = (Finset.univ.filter fun i =>
          0 < e i ∧ (h i + 1) / (2 * (e i : ℝ)) = lam / 2).card := by
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    refine and_congr_right fun hei => ?_
    exact (hratio i hei).symm
  rw [htheta]
  -- Peel the square.
  exact HasLLCExponentsOn.of_sq
    (fun x _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) hbase

end SingularLearningTheory
