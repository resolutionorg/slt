/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import Mathlib.Probability.Independence.Integration
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
# [Wat09, Theorem 5.7] (2) for every even `s`

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 4.2.3] (2), `s = 2m` | |
| | `ProbabilityTheory.rpow_lintegral_enorm_pow_empiricalSum_le` |

For an i.i.d. sample `X_i ∼ q` and `b ∈ L^{2m}(q)`, the centred normalised sum
`n^{-1/2} Σ_{i<n} (b(X_i) − E b)` has `L^{2m}(P)`-norm at most `2^{m+1} ‖b‖_{2m}`, uniformly in
`n`. Route (not [Hit26]'s): with `Y_n = Σ_{i<n} Z_i` for the centred `Z_i = b(X_i) − E b`,
independence and `E Z = 0` give
`E[(Y_n + Z)^{2m}] = E[Y_n^{2m}] + Σ_{k=2}^{2m} C(2m, k) E[Y_n^{2m−k}] E[Z^k]`; Jensen bounds
`E[Y^j] ≤ ‖Y‖_{2m}^j`; the elementary inequality
`A^{2m} + Σ_{k=2}^{2m} C(2m, k) A^{2m−k} B^k ≤ (A² + 4^m B²)^m` (`A, B ≥ 0`) then gives
`‖Y_{n+1}‖_{2m}² ≤ ‖Y_n‖_{2m}² + 4^m ‖Z‖_{2m}²`, hence `‖Y_n‖_{2m} ≤ 2^m √n ‖Z‖_{2m}`, and
`‖b − E b‖_{2m} ≤ 2 ‖b‖_{2m}`.

**Deviation from the source:** [Hit26]'s constant is `s − 1`; here it is `2^{s/2 + 1}` (the
thesis's inductive argument with the sharp constant is not formalised; only finiteness of the
constant is used downstream).
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {q : Measure X}
  [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P] {Xs : ℕ → Ω → X}

/-- No thesis counterpart. On a finite measure, an `L^s` function has integrable powers `f ^ a`
for `a ≤ s`, via `|f|^a ≤ 1 + |f|^s`. -/
theorem _root_.MeasureTheory.integrable_pow_of_memLp {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    {s : ℕ}
    (hs : 1 ≤ s) (hf : MemLp f s μ) {a : ℕ} (ha : a ≤ s) : Integrable (fun ω ↦ f ω ^ a) μ := by
  have hsa : Integrable (fun ω ↦ |f ω| ^ s) μ := by
    refine (hf.integrable_norm_rpow (by exact_mod_cast (by omega : s ≠ 0))
      (ENNReal.natCast_ne_top s)).congr (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp [Real.norm_eq_abs, Real.rpow_natCast]
  refine Integrable.mono' ((integrable_const 1).add hsa)
    ((continuous_pow a).comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow]
  rcases le_or_gt |f ω| 1 with h | h
  · exact (pow_le_one₀ (abs_nonneg _) h).trans (le_add_of_nonneg_right (by positivity))
  · exact (pow_le_pow_right₀ h.le ha).trans (le_add_of_nonneg_left zero_le_one)

private lemma integrable_pow_of_memLp_two_mul {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    {m : ℕ} (hm : 1 ≤ m) (hf : MemLp f (2 * m : ℝ≥0∞) μ) {a : ℕ} (ha : a ≤ 2 * m) :
    Integrable (fun ω ↦ f ω ^ a) μ :=
  integrable_pow_of_memLp (by omega) (by rw [Nat.cast_mul, Nat.cast_ofNat]; exact hf) ha

private lemma lintegral_enorm_rpow_natCast_eq {μ : Measure Ω} {f : Ω → ℝ} {k : ℕ}
    (hf : Integrable (fun ω ↦ |f ω| ^ k) μ) :
    ∫⁻ ω, ‖f ω‖ₑ ^ (k : ℝ) ∂μ = ENNReal.ofReal (∫ ω, |f ω| ^ k ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall fun ω ↦ by positivity)]
  refine lintegral_congr fun ω ↦ ?_
  rw [Real.enorm_eq_ofReal_abs, ← Real.rpow_natCast,
    ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (Nat.cast_nonneg _)]

private lemma eLpNorm_natCast_toReal_eq {μ : Measure Ω} {f : Ω → ℝ} {k : ℕ} (hk : k ≠ 0)
    (hfm : AEStronglyMeasurable f μ) (hf : Integrable (fun ω ↦ |f ω| ^ k) μ) :
    (eLpNorm f k μ).toReal = (∫ ω, |f ω| ^ k ∂μ) ^ ((k : ℝ)⁻¹) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by exact_mod_cast hk) (ENNReal.natCast_ne_top k) hfm,
    ENNReal.toReal_natCast, lintegral_enorm_rpow_natCast_eq hf, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (integral_nonneg fun ω ↦ by positivity), one_div]

/-- `|E[f^j]| ≤ (E[|f|^s])^{j/s}` for `f ∈ L^s(P)`, `j ≤ s`, on a probability space. -/
private lemma abs_integral_pow_le_aux {f : Ω → ℝ} {s : ℕ} (hs : s ≠ 0) (hf : MemLp f s P)
    {j : ℕ} (hj : j ≤ s) :
    |∫ ω, f ω ^ j ∂P| ≤ (∫ ω, |f ω| ^ s ∂P) ^ ((j : ℝ) / s) := by
  have hfj : Integrable (fun ω ↦ |f ω| ^ j) P :=
    (integrable_pow_of_memLp (by omega) hf hj).abs.congr
      (Filter.Eventually.of_forall fun ω ↦ abs_pow _ _)
  have hfs : Integrable (fun ω ↦ |f ω| ^ s) P :=
    (integrable_pow_of_memLp (by omega) hf le_rfl).abs.congr
      (Filter.Eventually.of_forall fun ω ↦ abs_pow _ _)
  have hI0 : 0 ≤ ∫ ω, |f ω| ^ s ∂P := integral_nonneg fun ω ↦ by positivity
  rcases Nat.eq_zero_or_pos j with hj0 | hj0
  · subst hj0
    simp
  calc |∫ ω, f ω ^ j ∂P| ≤ ∫ ω, |f ω ^ j| ∂P := abs_integral_le_integral_abs
    _ = ∫ ω, |f ω| ^ j ∂P := integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ abs_pow _ _)
    _ = ((∫ ω, |f ω| ^ j ∂P) ^ ((j : ℝ)⁻¹)) ^ j :=
        (Real.rpow_inv_natCast_pow (integral_nonneg fun ω ↦ by positivity) hj0.ne').symm
    _ = (eLpNorm f j P).toReal ^ j := by
        rw [eLpNorm_natCast_toReal_eq hj0.ne' hf.aestronglyMeasurable hfj]
    _ ≤ (eLpNorm f s P).toReal ^ j :=
        pow_le_pow_left₀ ENNReal.toReal_nonneg (ENNReal.toReal_mono hf.eLpNorm_ne_top
          (eLpNorm_le_eLpNorm_of_exponent_le (Nat.cast_le.mpr hj))) j
    _ = ((∫ ω, |f ω| ^ s ∂P) ^ ((s : ℝ)⁻¹)) ^ j := by
        rw [eLpNorm_natCast_toReal_eq hs hf.aestronglyMeasurable hfs]
    _ = (∫ ω, |f ω| ^ s ∂P) ^ ((j : ℝ) / s) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hI0, inv_mul_eq_div]

/-- The absolute-value form of `integral_pow_le_rpow_integral_pow`, used for the odd cross terms. -/
private lemma abs_integral_pow_le_rpow_integral_pow {f : Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : MemLp f (2 * m : ℝ≥0∞) P) {j : ℕ} (hj : j ≤ 2 * m) :
    |∫ ω, f ω ^ j ∂P| ≤ (∫ ω, f ω ^ (2 * m) ∂P) ^ ((j : ℝ) / (2 * m)) := by
  have h := abs_integral_pow_le_aux (s := 2 * m) (by omega)
    (by rw [Nat.cast_mul, Nat.cast_ofNat]; exact hf) hj
  have h2m : ∫ ω, |f ω| ^ (2 * m) ∂P = ∫ ω, f ω ^ (2 * m) ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ (even_two_mul m).pow_abs _)
  rw [h2m] at h
  push_cast at h
  exact h

/-- No thesis counterpart; Jensen on a probability space: for `f ∈ L^{2m}(P)` and `j ≤ 2m`,
`E[f^j] ≤ (E[f^{2m}])^{j/(2m)}`. -/
private theorem integral_pow_le_rpow_integral_pow {f : Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hf : MemLp f (2 * m : ℝ≥0∞) P) {j : ℕ} (hj : j ≤ 2 * m) :
    ∫ ω, f ω ^ j ∂P ≤ (∫ ω, f ω ^ (2 * m) ∂P) ^ ((j : ℝ) / (2 * m)) := by
  exact (le_abs_self _).trans (abs_integral_pow_le_rpow_integral_pow hm hf hj)

private lemma rpow_div_eq_pow_rpow {x : ℝ} (hx : 0 ≤ x) {m j : ℕ} :
    x ^ ((j : ℝ) / (2 * m)) = (x ^ ((1 : ℝ) / (2 * m))) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, one_div, inv_mul_eq_div]

private lemma rpow_two_mul_pow {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 1 ≤ m) :
    (x ^ ((1 : ℝ) / (2 * m))) ^ (2 * m) = x := by
  have : (1 : ℝ) / (2 * m) = ((2 * m : ℕ) : ℝ)⁻¹ := by push_cast; rw [one_div]
  rw [this]
  exact Real.rpow_inv_natCast_pow hx (by omega)

private lemma pow_rpow_two_mul {x : ℝ} (hx : 0 ≤ x) {m : ℕ} (hm : 1 ≤ m) :
    (x ^ (2 * m)) ^ ((1 : ℝ) / (2 * m)) = x := by
  have : (1 : ℝ) / (2 * m) = ((2 * m : ℕ) : ℝ)⁻¹ := by push_cast; rw [one_div]
  rw [this]
  exact Real.pow_rpow_inv_natCast hx (by omega)

private lemma sum_range_two_mul_succ (g : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m) :
    ∑ k ∈ Finset.range (2 * m + 1), g k = g 0 + g 1 + ∑ k ∈ Finset.Icc 2 (2 * m), g k := by
  rw [← Nat.Ico_zero_eq_range,
    ← Finset.sum_Ico_consecutive g (Nat.zero_le 2) (by omega : 2 ≤ 2 * m + 1)]
  congr 1
  rw [Nat.Ico_zero_eq_range]
  simp [Finset.sum_range_succ]

/-- No thesis counterpart; the moment recursion. For independent `S`, `Z` in `L^{2m}(P)` with
`E Z = 0`, writing `A = (E S^{2m})^{1/(2m)}` and `B = (E Z^{2m})^{1/(2m)}`,
`E[(S + Z)^{2m}] ≤ A^{2m} + Σ_{k=2}^{2m} C(2m, k) A^{2m−k} B^k`. -/
private theorem integral_add_pow_even_le {S Z : Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hS : MemLp S (2 * m : ℝ≥0∞) P) (hZ : MemLp Z (2 * m : ℝ≥0∞) P) (hind : IndepFun S Z P)
    (hEZ : ∫ ω, Z ω ∂P = 0) :
    ∫ ω, (S ω + Z ω) ^ (2 * m) ∂P
      ≤ ∫ ω, S ω ^ (2 * m) ∂P + ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) *
          ((∫ ω, S ω ^ (2 * m) ∂P) ^ ((1 : ℝ) / (2 * m))) ^ (2 * m - k) *
          ((∫ ω, Z ω ^ (2 * m) ∂P) ^ ((1 : ℝ) / (2 * m))) ^ k := by
  have hSa : ∀ a, a ≤ 2 * m → Integrable (fun ω ↦ S ω ^ a) P := fun a ha ↦
    integrable_pow_of_memLp_two_mul hm hS ha
  have hZa : ∀ a, a ≤ 2 * m → Integrable (fun ω ↦ Z ω ^ a) P := fun a ha ↦
    integrable_pow_of_memLp_two_mul hm hZ ha
  have hindab : ∀ a b : ℕ, IndepFun (fun ω ↦ Z ω ^ a) (fun ω ↦ S ω ^ b) P := fun a b ↦
    hind.symm.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
  have hterm : ∀ k ∈ Finset.range (2 * m + 1),
      Integrable (fun ω ↦ Z ω ^ k * S ω ^ (2 * m - k) * ((2 * m).choose k : ℝ)) P := fun k hk ↦ by
    have hk' : k ≤ 2 * m := by simpa [Nat.lt_succ_iff] using hk
    exact ((hindab k (2 * m - k)).integrable_mul (hZa k hk') (hSa _ (Nat.sub_le _ _))).mul_const _
  have hint : ∀ k ∈ Finset.range (2 * m + 1),
      ∫ ω, Z ω ^ k * S ω ^ (2 * m - k) * ((2 * m).choose k : ℝ) ∂P
        = ((2 * m).choose k : ℝ) * ((∫ ω, S ω ^ (2 * m - k) ∂P) * ∫ ω, Z ω ^ k ∂P) := fun k hk ↦ by
    have hk' : k ≤ 2 * m := by simpa [Nat.lt_succ_iff] using hk
    rw [integral_mul_const, (hindab k (2 * m - k)).integral_fun_mul_eq_mul_integral
      (hZa k hk').aestronglyMeasurable (hSa _ (Nat.sub_le _ _)).aestronglyMeasurable]
    ring
  have hexp : ∀ ω, (S ω + Z ω) ^ (2 * m)
      = ∑ k ∈ Finset.range (2 * m + 1), Z ω ^ k * S ω ^ (2 * m - k) * ((2 * m).choose k : ℝ) :=
    fun ω ↦ by rw [add_comm, add_pow]
  simp only [hexp]
  rw [integral_finsetSum _ hterm, Finset.sum_congr rfl hint, sum_range_two_mul_succ _ hm]
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero, pow_zero, integral_const,
    probReal_univ, one_smul, mul_one, pow_one, hEZ, mul_zero, add_zero]
  have hS0 : 0 ≤ ∫ ω, S ω ^ (2 * m) ∂P := integral_nonneg fun ω ↦ (even_two_mul m).pow_nonneg _
  have hZ0 : 0 ≤ ∫ ω, Z ω ^ (2 * m) ∂P := integral_nonneg fun ω ↦ (even_two_mul m).pow_nonneg _
  refine add_le_add_right ?_ _
  refine Finset.sum_le_sum fun k hk ↦ ?_
  rw [Finset.mem_Icc] at hk
  have h1 := abs_integral_pow_le_rpow_integral_pow hm hS (Nat.sub_le (2 * m) k)
  have h2 := abs_integral_pow_le_rpow_integral_pow hm hZ hk.2
  rw [rpow_div_eq_pow_rpow hS0] at h1
  rw [rpow_div_eq_pow_rpow hZ0] at h2
  calc ((2 * m).choose k : ℝ) * ((∫ ω, S ω ^ (2 * m - k) ∂P) * ∫ ω, Z ω ^ k ∂P)
      ≤ ((2 * m).choose k : ℝ) * (|∫ ω, S ω ^ (2 * m - k) ∂P| * |∫ ω, Z ω ^ k ∂P|) :=
        mul_le_mul_of_nonneg_left (by rw [← abs_mul]; exact le_abs_self _) (by positivity)
    _ ≤ ((2 * m).choose k : ℝ) * (((∫ ω, S ω ^ (2 * m) ∂P) ^ ((1 : ℝ) / (2 * m))) ^ (2 * m - k) *
          ((∫ ω, Z ω ^ (2 * m) ∂P) ^ ((1 : ℝ) / (2 * m))) ^ k) := by gcongr
    _ = _ := by ring

private lemma pow_mul_pow_le_of_two_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {m k : ℕ}
    (hk2 : 2 ≤ k) (hk : k ≤ 2 * m) :
    A ^ (2 * m - k) * B ^ k ≤ A ^ (2 * m - 2) * B ^ 2 + B ^ (2 * m) := by
  rcases le_total B A with hBA | hAB
  · calc A ^ (2 * m - k) * B ^ k = A ^ (2 * m - k) * (B ^ 2 * B ^ (k - 2)) := by
          rw [← pow_add, Nat.add_sub_cancel' hk2]
      _ ≤ A ^ (2 * m - k) * (B ^ 2 * A ^ (k - 2)) := by gcongr
      _ = A ^ (2 * m - 2) * B ^ 2 := by
          rw [show A ^ (2 * m - 2) = A ^ (2 * m - k) * A ^ (k - 2) by
            rw [← pow_add]; congr 1; omega]
          ring
      _ ≤ A ^ (2 * m - 2) * B ^ 2 + B ^ (2 * m) := le_add_of_nonneg_right (by positivity)
  · calc A ^ (2 * m - k) * B ^ k ≤ B ^ (2 * m - k) * B ^ k := by gcongr
      _ = B ^ (2 * m) := by rw [← pow_add, Nat.sub_add_cancel hk]
      _ ≤ A ^ (2 * m - 2) * B ^ 2 + B ^ (2 * m) := le_add_of_nonneg_left (by positivity)

/-- `(x + y)^{m+1} ≥ x^{m+1} + (m+1) x^m y + y^{m+1}` for `x, y ≥ 0`, `m ≥ 1`. -/
private lemma add_pow_succ_ge {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {m : ℕ} (hm : 1 ≤ m) :
    x ^ (m + 1) + (m + 1 : ℝ) * x ^ m * y + y ^ (m + 1) ≤ (x + y) ^ (m + 1) := by
  induction m, hm using Nat.le_induction with
  | base => exact le_of_eq (by push_cast; ring)
  | succ m _ ih =>
    have h1 : 0 ≤ (m : ℝ) * (x ^ m * y ^ 2) := by positivity
    have h2 : 0 ≤ x ^ m * y ^ 2 := by positivity
    have h3 : 0 ≤ x * y ^ (m + 1) := by positivity
    have hexp : (x + y) * (x ^ (m + 1) + (m + 1 : ℝ) * x ^ m * y + y ^ (m + 1))
        = x ^ (m + 1 + 1) + ((m + 1 : ℕ) + 1 : ℝ) * x ^ (m + 1) * y + y ^ (m + 1 + 1)
          + (x * y ^ (m + 1) + (m : ℝ) * (x ^ m * y ^ 2) + x ^ m * y ^ 2) := by
      push_cast
      ring
    calc x ^ (m + 1 + 1) + ((m + 1 : ℕ) + 1 : ℝ) * x ^ (m + 1) * y + y ^ (m + 1 + 1)
        ≤ (x + y) * (x ^ (m + 1) + (m + 1 : ℝ) * x ^ m * y + y ^ (m + 1)) := by
          rw [hexp]; linarith
      _ ≤ (x + y) * (x + y) ^ (m + 1) := mul_le_mul_of_nonneg_left ih (by positivity)
      _ = (x + y) ^ (m + 1 + 1) := by ring

/-- `x^{m+1} + c (x^m y + y^{m+1}) ≤ (x + c y)^{m+1}` for `x, y ≥ 0`, `c ≥ 1`, `m ≥ 1`. -/
private lemma add_mul_pow_le_add_mul_pow {x y c : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 1 ≤ c)
    {m : ℕ} (hm : 1 ≤ m) :
    x ^ (m + 1) + c * (x ^ m * y + y ^ (m + 1)) ≤ (x + c * y) ^ (m + 1) := by
  have hc0 : 0 ≤ c := zero_le_one.trans hc
  have H := add_pow_succ_ge hx (mul_nonneg hc0 hy) hm
  have h0 : 0 ≤ c * (x ^ m * y) := by positivity
  have h1 : c * (x ^ m * y) ≤ (m + 1 : ℝ) * x ^ m * (c * y) := by
    have : (1 : ℝ) ≤ m + 1 := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    calc c * (x ^ m * y) = 1 * (c * (x ^ m * y)) := by ring
      _ ≤ (m + 1 : ℝ) * (c * (x ^ m * y)) := mul_le_mul_of_nonneg_right this h0
      _ = (m + 1 : ℝ) * x ^ m * (c * y) := by ring
  have h2 : c * y ^ (m + 1) ≤ (c * y) ^ (m + 1) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right (le_self_pow₀ hc (by omega)) (pow_nonneg hy _)
  linarith

/-- No thesis counterpart; the elementary inequality behind the `√n` growth:
`A^{2m} + Σ_{k=2}^{2m} C(2m, k) A^{2m−k} B^k ≤ (A² + 4^m B²)^m` for `A, B ≥ 0`. -/
private theorem pow_add_sum_choose_le {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) {m : ℕ} (hm : 1 ≤ m) :
    A ^ (2 * m) + ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) * A ^ (2 * m - k) * B ^ k
      ≤ (A ^ 2 + 4 ^ m * B ^ 2) ^ m := by
  have hsum : ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) * A ^ (2 * m - k) * B ^ k
      ≤ 4 ^ m * (A ^ (2 * m - 2) * B ^ 2 + B ^ (2 * m)) := by
    calc ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) * A ^ (2 * m - k) * B ^ k
        ≤ ∑ k ∈ Finset.Icc 2 (2 * m),
            ((2 * m).choose k : ℝ) * (A ^ (2 * m - 2) * B ^ 2 + B ^ (2 * m)) := by
          refine Finset.sum_le_sum fun k hk ↦ ?_
          rw [Finset.mem_Icc] at hk
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (pow_mul_pow_le_of_two_le hA hB hk.1 hk.2)
            (by positivity)
      _ = (∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ)) *
            (A ^ (2 * m - 2) * B ^ 2 + B ^ (2 * m)) := by rw [Finset.sum_mul]
      _ ≤ 4 ^ m * (A ^ (2 * m - 2) * B ^ 2 + B ^ (2 * m)) := by
          gcongr
          calc ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ)
              ≤ ∑ k ∈ Finset.range (2 * m + 1), ((2 * m).choose k : ℝ) := by
                refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ ↦ by positivity
                intro k hk
                simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
                omega
            _ = 4 ^ m := by
                rw [← Nat.cast_sum, Nat.sum_range_choose, pow_mul]
                norm_num
  rcases Nat.lt_or_ge m 2 with hm2 | hm2
  · obtain rfl : m = 1 := by omega
    simp only [mul_one, Finset.Icc_self, Finset.sum_singleton, Nat.choose_self, Nat.cast_one,
      Nat.sub_self, pow_zero, one_mul, pow_one]
    nlinarith [sq_nonneg B]
  · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have hm' : 1 ≤ m' := by omega
    have h22 : 2 * (m' + 1) - 2 = 2 * m' := by omega
    rw [h22, pow_mul, pow_mul] at hsum
    rw [pow_mul]
    have hc : (1 : ℝ) ≤ 4 ^ (m' + 1) := one_le_pow₀ (by norm_num)
    have key := add_mul_pow_le_add_mul_pow (sq_nonneg A) (sq_nonneg B) hc hm'
    linarith

/-- No thesis counterpart; the induction. For independent centred `Z l ∈ L^{2m}(P)` with
`E[Z_l^{2m}] ≤ B^{2m}`, the partial sums satisfy `E[(Σ_{l<n} Z_l)^{2m}] ≤ (4^m n B²)^m`. -/
private theorem integral_pow_sum_range_le {Z : ℕ → Ω → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hZm : ∀ l, Measurable (Z l)) (hZ : ∀ l, MemLp (Z l) (2 * m : ℝ≥0∞) P) (hind : iIndepFun Z P)
    (hE : ∀ l, ∫ ω, Z l ω ∂P = 0) {B : ℝ} (hB : 0 ≤ B)
    (hZB : ∀ l, ∫ ω, Z l ω ^ (2 * m) ∂P ≤ B ^ (2 * m)) (n : ℕ) :
    ∫ ω, (∑ l ∈ Finset.range n, Z l ω) ^ (2 * m) ∂P ≤ (4 ^ m * n * B ^ 2) ^ m := by
  have hm0 : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  induction n with
  | zero => simp [zero_pow (by omega : 2 * m ≠ 0), zero_pow (by omega : m ≠ 0)]
  | succ n ih =>
    have hY : MemLp (fun ω ↦ ∑ l ∈ Finset.range n, Z l ω) (2 * m : ℝ≥0∞) P :=
      memLp_finsetSum _ fun l _ ↦ hZ l
    have hYZ : IndepFun (fun ω ↦ ∑ l ∈ Finset.range n, Z l ω) (Z n) P := by
      convert hind.indepFun_sum_range_succ hZm n using 1
      ext ω
      simp [Finset.sum_apply]
    have h := integral_add_pow_even_le hm hY (hZ n) hYZ (hE n)
    simp only [Finset.sum_range_succ]
    refine h.trans ?_
    obtain ⟨a, ha⟩ : ∃ a, a = ∫ ω, (∑ l ∈ Finset.range n, Z l ω) ^ (2 * m) ∂P := ⟨_, rfl⟩
    obtain ⟨z, hz⟩ : ∃ z, z = ∫ ω, Z n ω ^ (2 * m) ∂P := ⟨_, rfl⟩
    rw [← ha, ← hz]
    rw [← ha] at ih
    have ha0 : 0 ≤ a := by rw [ha]; exact integral_nonneg fun ω ↦ (even_two_mul m).pow_nonneg _
    have hz0 : 0 ≤ z := by rw [hz]; exact integral_nonneg fun ω ↦ (even_two_mul m).pow_nonneg _
    have hA0 : 0 ≤ a ^ ((1 : ℝ) / (2 * m)) := Real.rpow_nonneg ha0 _
    have hB'0 : 0 ≤ z ^ ((1 : ℝ) / (2 * m)) := Real.rpow_nonneg hz0 _
    have hB' : z ^ ((1 : ℝ) / (2 * m)) ≤ B := by
      calc z ^ ((1 : ℝ) / (2 * m)) ≤ (B ^ (2 * m)) ^ ((1 : ℝ) / (2 * m)) :=
            Real.rpow_le_rpow hz0 (by rw [hz]; exact hZB n) (by positivity)
        _ = B := pow_rpow_two_mul hB hm
    have hsum : ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) *
          (a ^ ((1 : ℝ) / (2 * m))) ^ (2 * m - k) * (z ^ ((1 : ℝ) / (2 * m))) ^ k
        ≤ ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) *
          (a ^ ((1 : ℝ) / (2 * m))) ^ (2 * m - k) * B ^ k :=
      Finset.sum_le_sum fun k _ ↦ by gcongr
    have hkey := pow_add_sum_choose_le hA0 hB hm
    rw [rpow_two_mul_pow ha0 hm] at hkey
    have hA2 : (a ^ ((1 : ℝ) / (2 * m))) ^ 2 ≤ 4 ^ m * n * B ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ha0]
      calc a ^ ((1 : ℝ) / (2 * m) * ((2 : ℕ) : ℝ)) = a ^ ((m : ℝ)⁻¹) := by
            congr 1
            push_cast
            field_simp
        _ ≤ ((4 ^ m * n * B ^ 2) ^ m) ^ ((m : ℝ)⁻¹) := Real.rpow_le_rpow ha0 ih (by positivity)
        _ = 4 ^ m * n * B ^ 2 := Real.pow_rpow_inv_natCast (by positivity) (by omega)
    calc a + ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) *
          (a ^ ((1 : ℝ) / (2 * m))) ^ (2 * m - k) * (z ^ ((1 : ℝ) / (2 * m))) ^ k
        ≤ a + ∑ k ∈ Finset.Icc 2 (2 * m), ((2 * m).choose k : ℝ) *
          (a ^ ((1 : ℝ) / (2 * m))) ^ (2 * m - k) * B ^ k := add_le_add_right hsum _
      _ ≤ ((a ^ ((1 : ℝ) / (2 * m))) ^ 2 + 4 ^ m * B ^ 2) ^ m := hkey
      _ ≤ (4 ^ m * n * B ^ 2 + 4 ^ m * B ^ 2) ^ m :=
          pow_le_pow_left₀ (by positivity) (by linarith) m
      _ = (4 ^ m * ((n : ℝ) + 1) * B ^ 2) ^ m := by ring
      _ = (4 ^ m * ((n + 1 : ℕ) : ℝ) * B ^ 2) ^ m := by push_cast; rfl

/-- [Hit26, Lemma 4.2.3] (2) for `s = 2m`: the `L^{2m}(P)`-norm of the
centred normalised sum is at most `2^{m+1} ‖b‖_{L^{2m}(q)}`, for every `n`. -/
theorem _root_.ProbabilityTheory.rpow_lintegral_enorm_pow_empiricalSum_le
    (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {b : X → ℝ} (hm : Measurable b)
    {m : ℕ} (hm1 : 1 ≤ m) (hb : MemLp b (2 * m : ℝ≥0∞) q) (n : ℕ) :
    (∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q)‖ₑ ^ (2 * m) ∂P)
        ^ (1 / (2 * m : ℝ))
      ≤ 2 ^ (m + 1) * eLpNorm b (2 * m : ℝ≥0∞) q := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ x, b x ∂q := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℕ → Ω → ℝ, Z = fun l ω ↦ b (Xs l ω) - c := ⟨_, rfl⟩
  have hZapp : ∀ l ω, b (Xs l ω) - ∫ x, b x ∂q = Z l ω := fun l ω ↦ by rw [hZdef, hc]
  simp only [hZapp]
  -- the exponent
  have h2mcast : ((2 * m : ℕ) : ℝ≥0∞) = 2 * m := by push_cast; rfl
  have h2m0 : (2 * m : ℝ≥0∞) ≠ 0 := by
    rw [← h2mcast]; exact_mod_cast (by omega : 2 * m ≠ 0)
  have h2mtop : (2 * m : ℝ≥0∞) ≠ ⊤ := by rw [← h2mcast]; exact ENNReal.natCast_ne_top _
  have h2mreal : (2 * m : ℝ≥0∞).toReal = 2 * m := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_natCast]
  have h12m : (1 : ℝ≥0∞) ≤ 2 * m := by
    rw [← h2mcast]; exact_mod_cast (by omega : 1 ≤ 2 * m)
  -- the centred variables
  have hbc : MemLp (fun x ↦ b x - c) (2 * m : ℝ≥0∞) q := hb.sub (memLp_const c)
  have hbcm : Measurable (fun x ↦ b x - c) := hm.sub measurable_const
  have hZm : ∀ l, Measurable (Z l) := fun l ↦ by rw [hZdef]; exact hbcm.comp (hX l)
  have hZ : ∀ l, MemLp (Z l) (2 * m : ℝ≥0∞) P := fun l ↦ by
    rw [hZdef]
    exact (memLp_map_measure_iff hbcm.aestronglyMeasurable (hX l).aemeasurable).1
      (by rw [hlaw l]; exact hbc)
  have hindZ : iIndepFun Z P := by
    rw [hZdef]; exact hind.comp (fun _ x ↦ b x - c) fun _ ↦ hbcm
  have hmom : ∀ l (k : ℕ), ∫ ω, Z l ω ^ k ∂P = ∫ x, (b x - c) ^ k ∂q := fun l k ↦ by
    rw [hZdef, ← hlaw l, integral_map (hX l).aemeasurable (hbcm.pow_const k).aestronglyMeasurable]
  have hE : ∀ l, ∫ ω, Z l ω ∂P = 0 := fun l ↦ by
    have := hmom l 1
    simp only [pow_one] at this
    rw [this, integral_sub (hb.integrable h12m) (integrable_const _), integral_const,
      probReal_univ, one_smul, hc, sub_self]
  -- `B = ‖b − c‖_{2m}`
  obtain ⟨μ, hμ⟩ : ∃ μ : ℝ, μ = ∫ x, (b x - c) ^ (2 * m) ∂q := ⟨_, rfl⟩
  have hμ0 : 0 ≤ μ := by rw [hμ]; exact integral_nonneg fun x ↦ (even_two_mul m).pow_nonneg _
  have hp0 : (0 : ℝ) ≤ 1 / (2 * m) := by positivity
  have hB0 : 0 ≤ μ ^ ((1 : ℝ) / (2 * m)) := Real.rpow_nonneg hμ0 _
  have hZB : ∀ l, ∫ ω, Z l ω ^ (2 * m) ∂P ≤ (μ ^ ((1 : ℝ) / (2 * m))) ^ (2 * m) := fun l ↦ by
    rw [rpow_two_mul_pow hμ0 hm1, hmom, hμ]
  have hYn := integral_pow_sum_range_le hm1 hZm hZ hindZ hE hB0 hZB n
  -- the real `2m`-th moment of the normalised sum
  have hreal : ∫ ω, ((√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω) ^ (2 * m) ∂P
      ≤ (2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) ^ (2 * m) := by
    rw [show ∫ ω, ((√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω) ^ (2 * m) ∂P
        = ((√(n : ℝ))⁻¹) ^ (2 * m) * ∫ ω, (∑ l ∈ Finset.range n, Z l ω) ^ (2 * m) ∂P by
      rw [← integral_const_mul]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ mul_pow _ _ _)]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp only [Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_pow (by omega : 2 * m ≠ 0), zero_mul]
      positivity
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hsq : ((√(n : ℝ))⁻¹) ^ (2 * m) = ((n : ℝ) ^ m)⁻¹ := by
        rw [inv_pow, pow_mul, Real.sq_sqrt hn'.le]
      have h4 : (4 : ℝ) ^ m = (2 ^ m) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      rw [hsq]
      rw [h4] at hYn
      calc ((n : ℝ) ^ m)⁻¹ * ∫ ω, (∑ l ∈ Finset.range n, Z l ω) ^ (2 * m) ∂P
          ≤ ((n : ℝ) ^ m)⁻¹ * ((2 ^ m) ^ 2 * n * (μ ^ ((1 : ℝ) / (2 * m))) ^ 2) ^ m :=
            mul_le_mul_of_nonneg_left hYn (by positivity)
        _ = (2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) ^ (2 * m) := by
          field_simp
          ring
  have hS : Integrable (fun ω ↦ ((√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω) ^ (2 * m)) P :=
    integrable_pow_of_memLp_two_mul hm1 ((memLp_finsetSum _ fun l _ ↦ hZ l).const_mul _) le_rfl
  -- pass to `ℝ≥0∞`
  have hpt : ∀ y : ℝ, ‖y‖ₑ ^ (2 * m) = ENNReal.ofReal (y ^ (2 * m)) := fun y ↦ by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), (even_two_mul m).pow_abs]
  have hL : ∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω‖ₑ ^ (2 * m) ∂P
      ≤ ENNReal.ofReal ((2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) ^ (2 * m)) := by
    simp only [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal hS
      (Filter.Eventually.of_forall fun ω ↦ (even_two_mul m).pow_nonneg _)]
    exact ENNReal.ofReal_le_ofReal hreal
  have hroot : (∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω‖ₑ ^ (2 * m) ∂P)
        ^ (1 / (2 * m : ℝ))
      ≤ ENNReal.ofReal (2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) := by
    calc (∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω‖ₑ ^ (2 * m) ∂P) ^ (1 / (2 * m : ℝ))
        ≤ (ENNReal.ofReal ((2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) ^ (2 * m))) ^ (1 / (2 * m : ℝ)) :=
          ENNReal.rpow_le_rpow hL (by positivity)
      _ = ENNReal.ofReal (((2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) ^ (2 * m)) ^ (1 / (2 * m : ℝ))) :=
          ENNReal.ofReal_rpow_of_nonneg (x := (2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) ^ (2 * m))
            (by positivity) hp0
      _ = ENNReal.ofReal (2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) := by
          rw [pow_rpow_two_mul (by positivity) hm1]
  -- `ofReal B = ‖b − c‖_{2m}`
  have hbc_int : Integrable (fun x ↦ (b x - c) ^ (2 * m)) q :=
    integrable_pow_of_memLp_two_mul hm1 hbc le_rfl
  have hBnorm : ENNReal.ofReal (μ ^ ((1 : ℝ) / (2 * m)))
      = eLpNorm (fun x ↦ b x - c) (2 * m : ℝ≥0∞) q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2m0 h2mtop (hm.sub_const c).aestronglyMeasurable,
      h2mreal,
      ← ENNReal.ofReal_rpow_of_nonneg hμ0 hp0, hμ,
      ofReal_integral_eq_lintegral_ofReal hbc_int
        (Filter.Eventually.of_forall fun x ↦ (even_two_mul m).pow_nonneg _)]
    congr 1
    refine lintegral_congr fun x ↦ ?_
    have : (2 * (m : ℝ)) = ((2 * m : ℕ) : ℝ) := by push_cast; ring
    rw [this, ENNReal.rpow_natCast, hpt]
  -- `‖b − c‖_{2m} ≤ 2 ‖b‖_{2m}`
  have hc_le : ‖c‖ₑ ≤ eLpNorm b (2 * m : ℝ≥0∞) q := by
    calc ‖c‖ₑ = ‖∫ x, b x ∂q‖ₑ := by rw [hc]
      _ ≤ ∫⁻ x, ‖b x‖ₑ ∂q := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm b 1 q := (eLpNorm_one_eq_lintegral_enorm hm.aestronglyMeasurable).symm
      _ ≤ eLpNorm b (2 * m : ℝ≥0∞) q :=
          eLpNorm_le_eLpNorm_of_exponent_le h12m
  have hsub : eLpNorm (fun x ↦ b x - c) (2 * m : ℝ≥0∞) q ≤ 2 * eLpNorm b (2 * m : ℝ≥0∞) q := by
    have hfun : (fun x ↦ b x - c) = b - fun _ ↦ c := by ext x; simp
    calc eLpNorm (fun x ↦ b x - c) (2 * m : ℝ≥0∞) q
        = eLpNorm (b - fun _ ↦ c) (2 * m : ℝ≥0∞) q := by rw [hfun]
      _ ≤ eLpNorm b (2 * m : ℝ≥0∞) q + eLpNorm (fun _ ↦ c) (2 * m : ℝ≥0∞) q :=
          eLpNorm_sub_le h12m
      _ = eLpNorm b (2 * m : ℝ≥0∞) q + ‖c‖ₑ := by
          rw [eLpNorm_const c h2m0 (IsProbabilityMeasure.ne_zero q), measure_univ,
            ENNReal.one_rpow, mul_one]
      _ ≤ eLpNorm b (2 * m : ℝ≥0∞) q + eLpNorm b (2 * m : ℝ≥0∞) q := add_le_add_right hc_le _
      _ = 2 * eLpNorm b (2 * m : ℝ≥0∞) q := (two_mul _).symm
  calc (∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω‖ₑ ^ (2 * m) ∂P) ^ (1 / (2 * m : ℝ))
      ≤ ENNReal.ofReal (2 ^ m * μ ^ ((1 : ℝ) / (2 * m))) := hroot
    _ = 2 ^ m * ENNReal.ofReal (μ ^ ((1 : ℝ) / (2 * m))) := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
          ENNReal.ofReal_ofNat]
    _ = 2 ^ m * eLpNorm (fun x ↦ b x - c) (2 * m : ℝ≥0∞) q := by rw [hBnorm]
    _ ≤ 2 ^ m * (2 * eLpNorm b (2 * m : ℝ≥0∞) q) := by gcongr
    _ = 2 ^ (m + 1) * eLpNorm b (2 * m : ℝ≥0∞) q := by ring

end SingularLearningTheory
