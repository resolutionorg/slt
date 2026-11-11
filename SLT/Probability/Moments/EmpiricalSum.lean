/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import Mathlib.Probability.Moments.Variance
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
# [Wat09, Theorem 5.7] for `s = 2`

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 4.2.3] (1) | `lintegral_enorm_sq_empiricalSum_le` |
| [Hit26, Lemma 4.2.3] (2), `s = 4` | |
| | `rpow_lintegral_enorm_pow_four_empiricalSum_le` |

For an i.i.d. sample `X_i ∼ q` and `b ∈ L²(q)`, the centred normalised sum
`n^{-1/2} Σ_{i<n} (b(X_i) − E b)` has second moment `Var_q(b) ≤ ‖b‖₂²`, uniformly in `n`
(`iIndepFun.variance_sum`). For `b ∈ L⁴(q)` its fourth moment is
`n^{-2} (n μ₄ + 3n(n−1) σ⁴) ≤ 3 μ₄` with `μ₄ = E(b − Eb)⁴`, `σ² = Var b` (the odd cross terms
vanish by independence and centring), so its `L⁴(P)`-norm is at most a constant times `‖b‖₄`;
[Hit26] proves the general even `s` by induction with the constant `s − 1`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {q : Measure X}
  [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P] {Xs : ℕ → Ω → X}

/-- [Hit26, Lemma 4.2.3] (1): `E[(n^{-1/2} Σ_{i<n} (b(X_i) − E b))²]
= Var_q(b) ≤ ∫ b² dq`, for every `n`. -/
private theorem lintegral_enorm_sq_empiricalSum_le (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {b : X → ℝ} (hm : Measurable b)
    (hb : MemLp b 2 q) (n : ℕ) :
    ∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q)‖ₑ ^ 2 ∂P
      ≤ ∫⁻ x, ‖b x‖ₑ ^ 2 ∂q := by
  have hbl : ∀ l, MemLp (fun ω ↦ b (Xs l ω)) 2 P := fun l ↦
    (memLp_map_measure_iff hm.aestronglyMeasurable (hX l).aemeasurable).1 (by rw [hlaw l]; exact hb)
  have hZ : ∀ l, MemLp (fun ω ↦ b (Xs l ω) - ∫ x, b x ∂q) 2 P := fun l ↦
    (hbl l).sub (memLp_const _)
  have hmean : ∀ l, ∫ ω, b (Xs l ω) ∂P = ∫ x, b x ∂q := fun l ↦ by
    rw [← hlaw l, integral_map (hX l).aemeasurable hm.aestronglyMeasurable]
  have hvar : ∀ l, Var[fun ω ↦ b (Xs l ω) - ∫ x, b x ∂q; P] = Var[b; q] := fun l ↦ by
    rw [variance_sub_const (hbl l).aestronglyMeasurable, ← hlaw l,
      variance_map hm.aemeasurable (hX l).aemeasurable]
    rfl
  have hindZ : iIndepFun (fun l ω ↦ b (Xs l ω) - ∫ x, b x ∂q) P :=
    hind.comp (fun _ x ↦ b x - ∫ x, b x ∂q) (fun _ ↦ hm.sub measurable_const)
  have hsum : Var[fun ω ↦ ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q); P]
      = n * Var[b; q] := by
    have : (fun ω ↦ ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q))
        = ∑ l ∈ Finset.range n, fun ω ↦ b (Xs l ω) - ∫ x, b x ∂q := by
      ext ω; simp [Finset.sum_apply]
    rw [this, IndepFun.variance_sum (fun l _ ↦ hZ l) (fun i _ j _ hij ↦ hindZ.indepFun hij)]
    simp [hvar]
  have hY : MemLp (fun ω ↦ (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q)) 2 P :=
    (memLp_finsetSum _ (fun l _ ↦ hZ l)).const_mul _
  have hEY : ∫ ω, (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q) ∂P = 0 := by
    rw [integral_const_mul, integral_finsetSum _ (fun l _ ↦ (hZ l).integrable one_le_two)]
    rw [Finset.sum_eq_zero fun l _ ↦ ?_, mul_zero]
    rw [integral_sub ((hbl l).integrable one_le_two) (integrable_const _), hmean,
      integral_const, probReal_univ, one_smul, sub_self]
  have hVY : Var[fun ω ↦ (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q); P]
      ≤ Var[b; q] := by
    rw [variance_const_mul, hsum]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn, variance_nonneg]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [inv_pow, Real.sq_sqrt hn'.le, ← mul_assoc, inv_mul_cancel₀ hn'.ne', one_mul]
  have h1 : ∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q)‖ₑ ^ 2 ∂P
      = ENNReal.ofReal
        (Var[fun ω ↦ (√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q); P]) := by
    rw [ofReal_variance hY, evariance, hEY]
    simp
  have h2 : ENNReal.ofReal (Var[b; q]) ≤ ∫⁻ x, ‖b x‖ₑ ^ 2 ∂q := by
    rw [ofReal_variance hb, evariance_def' hb.aestronglyMeasurable]
    exact tsub_le_self
  rw [h1]
  exact (ENNReal.ofReal_le_ofReal hVY).trans h2

/-- The `L²(P)`-norm of the centred normalised sum is at most `‖b‖_{L²(q)}`. -/
theorem _root_.ProbabilityTheory.rpow_lintegral_enorm_sq_empiricalSum_le
    (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {b : X → ℝ} (hm : Measurable b)
    (hb : MemLp b 2 q) (n : ℕ) :
    (∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q)‖ₑ ^ 2 ∂P) ^ (1 / 2 : ℝ)
      ≤ eLpNorm b 2 q := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
    hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
  exact ENNReal.rpow_le_rpow (lintegral_enorm_sq_empiricalSum_le hX hlaw hind hm hb n)
    (by norm_num)

/-- No thesis counterpart; used by `integral_add_pow_of_indepFun`. On a finite measure, an `L⁴`
function has integrable powers `f ^ a` for `a ≤ 4`, via `|f|^a ≤ 1 + f⁴`. -/
private theorem integrable_pow_of_memLp_four {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ}
    (hf : MemLp f 4 μ) {a : ℕ} (ha : a ≤ 4) : Integrable (fun ω ↦ f ω ^ a) μ := by
  have h4 : Integrable (fun ω ↦ f ω ^ 4) μ := by
    refine (hf.integrable_norm_rpow (by norm_num) (by norm_num)).congr
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    simp [Real.norm_eq_abs, (by decide : Even 4).pow_abs]
  refine Integrable.mono' ((integrable_const 1).add h4)
    ((continuous_pow a).comp_aestronglyMeasurable hf.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun ω ↦ ?_)
  rw [Real.norm_eq_abs, abs_pow]
  rcases le_or_gt |f ω| 1 with h | h
  · exact (pow_le_one₀ (abs_nonneg _) h).trans (le_add_of_nonneg_right (by positivity))
  · calc |f ω| ^ a ≤ |f ω| ^ 4 := pow_le_pow_right₀ h.le ha
      _ = f ω ^ 4 := (by decide : Even 4).pow_abs _
      _ ≤ 1 + f ω ^ 4 := le_add_of_nonneg_left zero_le_one

/-- No thesis counterpart; used by `rpow_lintegral_enorm_pow_four_empiricalSum_le`. Jensen for the
square on a probability space: `(∫ g)² ≤ ∫ g²`. -/
private theorem sq_integral_le_integral_sq {g : Ω → ℝ} (hg : Integrable g P)
    (hg2 : Integrable (fun ω ↦ g ω ^ 2) P) : (∫ ω, g ω ∂P) ^ 2 ≤ ∫ ω, g ω ^ 2 ∂P := by
  have h0 : 0 ≤ ∫ ω, (g ω - ∫ ω, g ω ∂P) ^ 2 ∂P := integral_nonneg fun ω ↦ sq_nonneg _
  have he : ∀ ω, (g ω - ∫ ω, g ω ∂P) ^ 2
      = g ω ^ 2 - 2 * g ω * ∫ ω, g ω ∂P + (∫ ω, g ω ∂P) ^ 2 := fun ω ↦ by ring
  simp only [he] at h0
  have hi : Integrable (fun ω ↦ g ω ^ 2 - 2 * g ω * ∫ ω, g ω ∂P) P :=
    hg2.sub ((hg.const_mul 2).mul_const _)
  rw [integral_add hi (integrable_const _), integral_sub hg2 ((hg.const_mul 2).mul_const _),
    integral_mul_const, integral_const_mul, integral_const, probReal_univ, one_smul] at h0
  nlinarith

/-- No thesis counterpart; used by `integral_pow_sum_range_of_iIndepFun`. Second and fourth
moments of the sum of two independent centred `L⁴` variables: the odd cross terms vanish. -/
private theorem integral_add_pow_of_indepFun {S Z : Ω → ℝ} (hS : MemLp S 4 P) (hZ : MemLp Z 4 P)
    (hind : IndepFun S Z P) (hES : ∫ ω, S ω ∂P = 0) (hEZ : ∫ ω, Z ω ∂P = 0) :
    ∫ ω, (S ω + Z ω) ^ 2 ∂P = ∫ ω, S ω ^ 2 ∂P + ∫ ω, Z ω ^ 2 ∂P ∧
    ∫ ω, (S ω + Z ω) ^ 4 ∂P
      = ∫ ω, S ω ^ 4 ∂P + 6 * ((∫ ω, S ω ^ 2 ∂P) * ∫ ω, Z ω ^ 2 ∂P) + ∫ ω, Z ω ^ 4 ∂P := by
  have hSa : ∀ a, a ≤ 4 → Integrable (fun ω ↦ S ω ^ a) P := fun a ha ↦
    integrable_pow_of_memLp_four hS ha
  have hZb : ∀ b, b ≤ 4 → Integrable (fun ω ↦ Z ω ^ b) P := fun b hb ↦
    integrable_pow_of_memLp_four hZ hb
  have hindab : ∀ a b : ℕ, IndepFun (fun ω ↦ S ω ^ a) (fun ω ↦ Z ω ^ b) P := fun a b ↦
    hind.comp (measurable_id.pow_const a) (measurable_id.pow_const b)
  have hmul : ∀ a, a ≤ 4 → ∀ b, b ≤ 4 → Integrable (fun ω ↦ S ω ^ a * Z ω ^ b) P :=
    fun a ha b hb ↦ (hindab a b).integrable_mul (hSa a ha) (hZb b hb)
  have hint : ∀ a, a ≤ 4 → ∀ b, b ≤ 4 →
      ∫ ω, S ω ^ a * Z ω ^ b ∂P = (∫ ω, S ω ^ a ∂P) * ∫ ω, Z ω ^ b ∂P := fun a ha b hb ↦
    (hindab a b).integral_fun_mul_eq_mul_integral (hSa a ha).aestronglyMeasurable
      (hZb b hb).aestronglyMeasurable
  have e2 : ∀ ω, (S ω + Z ω) ^ 2 = S ω ^ 2 + 2 * (S ω ^ 1 * Z ω ^ 1) + Z ω ^ 2 := fun ω ↦ by ring
  have e4 : ∀ ω, (S ω + Z ω) ^ 4 = S ω ^ 4 + 4 * (S ω ^ 3 * Z ω ^ 1) + 6 * (S ω ^ 2 * Z ω ^ 2)
      + 4 * (S ω ^ 1 * Z ω ^ 3) + Z ω ^ 4 := fun ω ↦ by ring
  simp only [e2, e4]
  have hA2 : Integrable (fun ω ↦ S ω ^ 2 + 2 * (S ω ^ 1 * Z ω ^ 1)) P :=
    (hSa 2 (by norm_num)).add ((hmul 1 (by norm_num) 1 (by norm_num)).const_mul 2)
  have hB1 : Integrable (fun ω ↦ S ω ^ 4 + 4 * (S ω ^ 3 * Z ω ^ 1)) P :=
    (hSa 4 (by norm_num)).add ((hmul 3 (by norm_num) 1 (by norm_num)).const_mul 4)
  have hB2 : Integrable (fun ω ↦ S ω ^ 4 + 4 * (S ω ^ 3 * Z ω ^ 1) + 6 * (S ω ^ 2 * Z ω ^ 2)) P :=
    hB1.add ((hmul 2 (by norm_num) 2 (by norm_num)).const_mul 6)
  have hB3 : Integrable (fun ω ↦ S ω ^ 4 + 4 * (S ω ^ 3 * Z ω ^ 1) + 6 * (S ω ^ 2 * Z ω ^ 2)
      + 4 * (S ω ^ 1 * Z ω ^ 3)) P :=
    hB2.add ((hmul 1 (by norm_num) 3 (by norm_num)).const_mul 4)
  constructor
  · rw [integral_add hA2 (hZb 2 (by norm_num)),
      integral_add (hSa 2 (by norm_num)) ((hmul 1 (by norm_num) 1 (by norm_num)).const_mul 2),
      integral_const_mul, hint 1 (by norm_num) 1 (by norm_num)]
    simp only [pow_one, hES, zero_mul, mul_zero, add_zero]
  · rw [integral_add hB3 (hZb 4 (by norm_num)),
      integral_add hB2 ((hmul 1 (by norm_num) 3 (by norm_num)).const_mul 4),
      integral_add hB1 ((hmul 2 (by norm_num) 2 (by norm_num)).const_mul 6),
      integral_add (hSa 4 (by norm_num)) ((hmul 3 (by norm_num) 1 (by norm_num)).const_mul 4),
      integral_const_mul, integral_const_mul, integral_const_mul,
      hint 3 (by norm_num) 1 (by norm_num), hint 2 (by norm_num) 2 (by norm_num),
      hint 1 (by norm_num) 3 (by norm_num)]
    simp only [pow_one, hES, hEZ, zero_mul, mul_zero, add_zero]

/-- No thesis counterpart; the moment computation behind
`rpow_lintegral_enorm_pow_four_empiricalSum_le`. For independent centred `Z l` with common second
and fourth moments `σ²`, `μ₄`, the partial sums have `E S_n² = n σ²` and
`E S_n⁴ = n μ₄ + 3 n (n − 1) σ⁴`. -/
private theorem integral_pow_sum_range_of_iIndepFun {Z : ℕ → Ω → ℝ} (hZm : ∀ l, Measurable (Z l))
    (hZ : ∀ l, MemLp (Z l) 4 P) (hind : iIndepFun Z P) (hE : ∀ l, ∫ ω, Z l ω ∂P = 0)
    {σ2 μ4 : ℝ} (hE2 : ∀ l, ∫ ω, Z l ω ^ 2 ∂P = σ2) (hE4 : ∀ l, ∫ ω, Z l ω ^ 4 ∂P = μ4) (n : ℕ) :
    ∫ ω, (∑ l ∈ Finset.range n, Z l ω) ^ 2 ∂P = n * σ2 ∧
    ∫ ω, (∑ l ∈ Finset.range n, Z l ω) ^ 4 ∂P = n * μ4 + 3 * n * (n - 1) * σ2 ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hS : MemLp (fun ω ↦ ∑ l ∈ Finset.range n, Z l ω) 4 P :=
      memLp_finsetSum _ fun l _ ↦ hZ l
    have hES : ∫ ω, ∑ l ∈ Finset.range n, Z l ω ∂P = 0 := by
      rw [integral_finsetSum _ fun l _ ↦ (hZ l).integrable (by norm_num)]
      exact Finset.sum_eq_zero fun l _ ↦ hE l
    have hSZ : IndepFun (fun ω ↦ ∑ l ∈ Finset.range n, Z l ω) (Z n) P := by
      convert hind.indepFun_sum_range_succ hZm n using 1
      ext ω
      simp [Finset.sum_apply]
    obtain ⟨h2, h4⟩ := integral_add_pow_of_indepFun hS (hZ n) hSZ hES (hE n)
    simp only [Finset.sum_range_succ]
    rw [h2, h4, ih.1, ih.2, hE2 n, hE4 n]
    constructor <;> push_cast <;> ring

/-- [Hit26, Lemma 4.2.3] (2) for `s = 4`: the `L⁴(P)`-norm of the centred
normalised sum is at most `4 ‖b‖_{L⁴(q)}` (the sharp constant is `2 · 3^{1/4}`), for every `n`. -/
private theorem rpow_lintegral_enorm_pow_four_empiricalSum_le (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) {b : X → ℝ} (hm : Measurable b)
    (hb : MemLp b 4 q) (n : ℕ) :
    (∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, (b (Xs l ω) - ∫ x, b x ∂q)‖ₑ ^ 4 ∂P) ^ (1 / 4 : ℝ)
      ≤ 4 * eLpNorm b 4 q := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ x, b x ∂q := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℕ → Ω → ℝ, Z = fun l ω ↦ b (Xs l ω) - c := ⟨_, rfl⟩
  have hZapp : ∀ l ω, b (Xs l ω) - ∫ x, b x ∂q = Z l ω := fun l ω ↦ by rw [hZdef, hc]
  simp only [hZapp]
  -- the centred variables
  have hbc : MemLp (fun x ↦ b x - c) 4 q := hb.sub (memLp_const c)
  have hbcm : Measurable (fun x ↦ b x - c) := hm.sub measurable_const
  have hZm : ∀ l, Measurable (Z l) := fun l ↦ by rw [hZdef]; exact hbcm.comp (hX l)
  have hZ : ∀ l, MemLp (Z l) 4 P := fun l ↦ by
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
    rw [this, integral_sub (hb.integrable (by norm_num)) (integrable_const _), integral_const,
      probReal_univ, one_smul, hc, sub_self]
  obtain ⟨h2, h4⟩ := integral_pow_sum_range_of_iIndepFun hZm hZ hindZ hE (fun l ↦ hmom l 2)
    (fun l ↦ hmom l 4) n
  -- σ⁴ ≤ μ₄ and μ₄ ≤ 16 ∫ b⁴
  have hσμ : (∫ x, (b x - c) ^ 2 ∂q) ^ 2 ≤ ∫ x, (b x - c) ^ 4 ∂q := by
    have := sq_integral_le_integral_sq (integrable_pow_of_memLp_four hbc (by norm_num : 2 ≤ 4))
      ((integrable_pow_of_memLp_four hbc le_rfl).congr
        (Filter.Eventually.of_forall fun x ↦ by ring))
    simpa only [← pow_mul] using this
  have hb4 : Integrable (fun x ↦ b x ^ 4) q := integrable_pow_of_memLp_four hb le_rfl
  have hc4 : c ^ 4 ≤ ∫ x, b x ^ 4 ∂q := by
    have h1 := sq_integral_le_integral_sq (hb.integrable (by norm_num))
      (integrable_pow_of_memLp_four hb (by norm_num : 2 ≤ 4))
    have h2 := sq_integral_le_integral_sq (integrable_pow_of_memLp_four hb (by norm_num : 2 ≤ 4))
      (hb4.congr (Filter.Eventually.of_forall fun x ↦ by ring))
    rw [← hc] at h1
    calc c ^ 4 = (c ^ 2) ^ 2 := by ring
      _ ≤ (∫ x, b x ^ 2 ∂q) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) h1 2
      _ ≤ ∫ x, (b x ^ 2) ^ 2 ∂q := h2
      _ = ∫ x, b x ^ 4 ∂q := integral_congr_ae (Filter.Eventually.of_forall fun x ↦ by ring)
  have hμ4 : ∫ x, (b x - c) ^ 4 ∂q ≤ 16 * ∫ x, b x ^ 4 ∂q := by
    calc ∫ x, (b x - c) ^ 4 ∂q ≤ ∫ x, 8 * (b x ^ 4 + c ^ 4) ∂q := by
          refine integral_mono (integrable_pow_of_memLp_four hbc le_rfl)
            ((hb4.add (integrable_const _)).const_mul 8) fun x ↦ ?_
          nlinarith [sq_nonneg ((b x + c) ^ 2), sq_nonneg (b x ^ 2 - c ^ 2)]
      _ = 8 * (∫ x, b x ^ 4 ∂q + c ^ 4) := by
          rw [integral_const_mul, integral_add hb4 (integrable_const _), integral_const,
            probReal_univ, one_smul]
      _ ≤ 16 * ∫ x, b x ^ 4 ∂q := by linarith
  -- the real fourth moment of the normalised sum
  have hS4 : Integrable (fun ω ↦ ((√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω) ^ 4) P :=
    integrable_pow_of_memLp_four ((memLp_finsetSum _ fun l _ ↦ hZ l).const_mul _) le_rfl
  have hreal : ∫ ω, ((√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω) ^ 4 ∂P
      ≤ 48 * ∫ x, b x ^ 4 ∂q := by
    simp only [mul_pow]
    rw [integral_const_mul, h4]
    have hμ0 : 0 ≤ ∫ x, (b x - c) ^ 4 ∂q := integral_nonneg fun x ↦ by positivity
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp only [hn, Nat.cast_zero, Real.sqrt_zero, inv_zero, zero_mul, zero_sub, mul_zero,
        mul_neg, mul_one, zero_add, neg_zero]
      linarith
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      have hsq : ((√(n : ℝ))⁻¹) ^ 4 = ((n : ℝ) ^ 2)⁻¹ := by
        rw [inv_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hn'.le]
      rw [hsq]
      have hσ : 3 * (n : ℝ) * (n - 1) * (∫ x, (b x - c) ^ 2 ∂q) ^ 2
          ≤ 3 * n * (n - 1) * ∫ x, (b x - c) ^ 4 ∂q := by
        have : (0 : ℝ) ≤ 3 * n * (n - 1) := by
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          nlinarith
        exact mul_le_mul_of_nonneg_left hσμ this
      calc ((n : ℝ) ^ 2)⁻¹ * (n * ∫ x, (b x - c) ^ 4 ∂q
            + 3 * n * (n - 1) * (∫ x, (b x - c) ^ 2 ∂q) ^ 2)
          ≤ ((n : ℝ) ^ 2)⁻¹ * (n * ∫ x, (b x - c) ^ 4 ∂q
            + 3 * n * (n - 1) * ∫ x, (b x - c) ^ 4 ∂q) := by gcongr
        _ = (3 - 2 / n) * ∫ x, (b x - c) ^ 4 ∂q := by field_simp; ring
        _ ≤ 3 * ∫ x, (b x - c) ^ 4 ∂q := by
          apply mul_le_mul_of_nonneg_right _ hμ0
          have : 0 ≤ 2 / (n : ℝ) := by positivity
          linarith
        _ ≤ 48 * ∫ x, b x ^ 4 ∂q := by linarith
  -- pass to `ℝ≥0∞`
  have hpt : ∀ y : ℝ, ‖y‖ₑ ^ 4 = ENNReal.ofReal (y ^ 4) := fun y ↦ by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), (by decide : Even 4).pow_abs]
  have hL : ∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω‖ₑ ^ 4 ∂P
      ≤ 4 ^ 4 * ∫⁻ x, ‖b x‖ₑ ^ 4 ∂q := by
    simp only [hpt]
    rw [← ofReal_integral_eq_lintegral_ofReal hS4
        (Filter.Eventually.of_forall fun ω ↦ by positivity),
      ← ofReal_integral_eq_lintegral_ofReal hb4
        (Filter.Eventually.of_forall fun x ↦ by positivity),
      show (4 : ℝ≥0∞) ^ 4 = ENNReal.ofReal (4 ^ 4) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (hreal.trans (by
      have := integral_nonneg (μ := q) (f := fun x ↦ b x ^ 4) fun x ↦ by positivity
      linarith))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofNat_ne_top
    hm.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat]
  calc (∫⁻ ω, ‖(√(n : ℝ))⁻¹ * ∑ l ∈ Finset.range n, Z l ω‖ₑ ^ 4 ∂P) ^ (1 / 4 : ℝ)
      ≤ (4 ^ 4 * ∫⁻ x, ‖b x‖ₑ ^ 4 ∂q) ^ (1 / 4 : ℝ) := ENNReal.rpow_le_rpow hL (by norm_num)
    _ = 4 * (∫⁻ x, ‖b x‖ₑ ^ 4 ∂q) ^ (1 / 4 : ℝ) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_natCast,
        ← ENNReal.rpow_mul]
      norm_num

end SingularLearningTheory
