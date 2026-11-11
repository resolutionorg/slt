/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Analytic.ConvergenceRadius
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
# Monomials of a power series in `ℝ^d`

No thesis counterpart; the elementary estimates behind
[Hit26, Definition 4.2.2] as used in the proofs of
[Hit26, Lemma 4.2.4] and [Hit26, Lemma 4.2.8]:
a continuous `k`-linear map on `ℝ^d` evaluated on the diagonal is a sum of `d^k` monomials
`∏ᵢ v_{jᵢ}` with coefficients `p(e_{j₁}, …, e_{j_k})` of norm `≤ ‖p‖`; the monomials are bounded by
`ρ^k` and `k ρ^{k−1}`-Lipschitz on the sup-norm ball of radius `ρ`; and the weighted coefficient
series converge for `2(d+1)ρ` below the radius of convergence.
-/

public section

namespace ContinuousMultilinearMap

open Filter Topology

/-- `|∏ aᵢ| ≤ ρ^k` when every `|aᵢ| ≤ ρ`. -/
theorem _root_.Finset.abs_prod_le_pow {k : ℕ} {ρ : ℝ} (a : Fin k → ℝ) (ha : ∀ i, |a i| ≤ ρ) :
    |∏ i, a i| ≤ ρ ^ k := by
  rw [Finset.abs_prod]
  calc ∏ i, |a i| ≤ ∏ _i : Fin k, ρ :=
        Finset.prod_le_prod₀ (fun i _ ↦ abs_nonneg _) (fun i _ ↦ ha i)
    _ = ρ ^ k := by simp

/-- `|∏ aᵢ − ∏ a'ᵢ| ≤ k ρ^{k−1} δ` when every `|aᵢ|, |a'ᵢ| ≤ ρ` and `|aᵢ − a'ᵢ| ≤ δ`
(telescoping). -/
theorem _root_.Finset.abs_prod_sub_prod_le {k : ℕ} {ρ δ : ℝ} (hρ : 0 ≤ ρ) (a a' : Fin k → ℝ)
    (ha : ∀ i, |a i| ≤ ρ) (ha' : ∀ i, |a' i| ≤ ρ) (hd : ∀ i, |a i - a' i| ≤ δ) :
    |∏ i, a i - ∏ i, a' i| ≤ k * ρ ^ (k - 1) * δ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ]
    have h1 := ih (fun i ↦ a i.succ) (fun i ↦ a' i.succ) (fun i ↦ ha _) (fun i ↦ ha' _)
      (fun i ↦ hd _)
    have h2 := Finset.abs_prod_le_pow (fun i ↦ a i.succ) (fun i ↦ ha _)
    have hδ : 0 ≤ δ := (abs_nonneg _).trans (hd 0)
    have e : a 0 * ∏ i : Fin k, a i.succ - a' 0 * ∏ i : Fin k, a' i.succ
        = (a 0 - a' 0) * ∏ i : Fin k, a i.succ
          + a' 0 * (∏ i : Fin k, a i.succ - ∏ i : Fin k, a' i.succ) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    calc |a 0 - a' 0| * |∏ i : Fin k, a i.succ|
          + |a' 0| * |∏ i : Fin k, a i.succ - ∏ i : Fin k, a' i.succ|
        ≤ δ * ρ ^ k + ρ * (k * ρ ^ (k - 1) * δ) :=
          add_le_add (mul_le_mul (hd 0) h2 (abs_nonneg _) hδ)
            (mul_le_mul (ha' 0) h1 (abs_nonneg _) hρ)
      _ = ((k + 1 : ℕ) : ℝ) * ρ ^ (k + 1 - 1) * δ := by
          rcases k with _ | k
          · simp
          · rw [Nat.add_sub_cancel, Nat.add_sub_cancel, pow_succ]; push_cast; ring

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k d : ℕ}

/-- A continuous `k`-linear map on `ℝ^d`, on the diagonal, as a sum of monomials. -/
theorem apply_const_eq_sum
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ (Fin d → ℝ)) E) (v : Fin d → ℝ) :
    p (fun _ ↦ v) = ∑ j : Fin k → Fin d, (∏ i, v (j i)) • p (fun i ↦ Pi.single (j i) 1) := by
  have hv : v = ∑ j : Fin d, v j • (Pi.single j (1 : ℝ) : Fin d → ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  calc p (fun _ ↦ v) = p (fun _ ↦ ∑ j : Fin d, v j • (Pi.single j (1 : ℝ) : Fin d → ℝ)) := by
        rw [← hv]
    _ = ∑ j : Fin k → Fin d, p (fun i ↦ v (j i) • (Pi.single (j i) (1 : ℝ) : Fin d → ℝ)) :=
        p.map_sum (fun _ j ↦ v j • (Pi.single j (1 : ℝ) : Fin d → ℝ))
    _ = ∑ j : Fin k → Fin d, (∏ i, v (j i)) • p (fun i ↦ Pi.single (j i) 1) := by
        simp_rw [ContinuousMultilinearMap.map_smul_univ]

/-- The monomial coefficients are bounded by the operator norm. -/
theorem norm_apply_single_le
    (p : ContinuousMultilinearMap ℝ (fun _ : Fin k ↦ (Fin d → ℝ)) E) (j : Fin k → Fin d) :
    ‖p (fun i ↦ Pi.single (j i) 1)‖ ≤ ‖p‖ := by
  refine (p.le_opNorm _).trans ?_
  simp [Pi.norm_single]

/-- Summability of the amplitude and Lipschitz weights of the monomial expansion inside the
radius of convergence: `Σ ‖p_k‖ d^k ρ^k` and `Σ ‖p_k‖ d^k k ρ^{k−1}` converge when
`2(d+1)ρ ≤ R < radius`. -/
theorem _root_.FormalMultilinearSeries.summable_weights (p : FormalMultilinearSeries ℝ (Fin d → ℝ)
    E) {R : ℝ} (hR : 0 < R)
    (hRr : ENNReal.ofReal R < p.radius) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρR : 2 * (d + 1) * ρ ≤ R) :
    Summable (fun k ↦ ‖p k‖ * (d : ℝ) ^ k * ρ ^ k) ∧
      Summable (fun k ↦ ‖p k‖ * (d : ℝ) ^ k * (k * ρ ^ (k - 1))) := by
  have hS : Summable fun k ↦ ‖p k‖ * R ^ k := by
    have := p.summable_norm_mul_pow (r := Real.toNNReal R) hRr
    simpa [Real.coe_toNNReal R hR.le] using this
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 : 2 * ((d : ℝ) * ρ) ≤ R := by nlinarith
  constructor
  · refine hS.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
    rw [mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) k)
      (norm_nonneg _)
  · refine (hS.mul_left (2 * d / R)).of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_)
    rcases k with _ | k
    · have : (0 : ℝ) ≤ 2 * d / R * ‖p 0‖ := by positivity
      simpa using this
    · have hk : (k : ℝ) + 1 ≤ 2 ^ k := by
        exact_mod_cast Nat.succ_le_of_lt Nat.lt_two_pow_self
      have key : ((k : ℝ) + 1) * ((d : ℝ) * ρ) ^ k ≤ R ^ k :=
        calc ((k : ℝ) + 1) * ((d : ℝ) * ρ) ^ k ≤ 2 ^ k * ((d : ℝ) * ρ) ^ k :=
              mul_le_mul_of_nonneg_right hk (by positivity)
          _ = (2 * ((d : ℝ) * ρ)) ^ k := by ring
          _ ≤ R ^ k := pow_le_pow_left₀ (by positivity) h2 k
      have e1 : ‖p (k + 1)‖ * (d : ℝ) ^ (k + 1) * (((k + 1 : ℕ) : ℝ) * ρ ^ (k + 1 - 1))
          = ‖p (k + 1)‖ * d * (((k : ℝ) + 1) * ((d : ℝ) * ρ) ^ k) := by
        rw [Nat.add_sub_cancel, pow_succ, mul_pow]; push_cast; ring
      have e2 : 2 * (d : ℝ) / R * (‖p (k + 1)‖ * R ^ (k + 1))
          = ‖p (k + 1)‖ * d * (2 * R ^ k) := by
        field_simp; ring
      rw [e1, e2]
      have hRk : 0 ≤ R ^ k := pow_nonneg hR.le k
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end ContinuousMultilinearMap
