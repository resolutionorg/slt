/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Finite Sample Moments
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {μ : Measure E} {X : ℕ → Ω → E}

section Scalar

/-- `(∑ zⱼ)^{3/2} ≤ √5 ∑ zⱼ^{3/2}` for five nonnegative terms (convexity of `x^{3/2}`). -/
private theorem sum_five_rpow_le {z : Fin 5 → ℝ} (hz : ∀ j, 0 ≤ z j) :
    (∑ j, z j) ^ (3 / 2 : ℝ) ≤ Real.sqrt 5 * ∑ j, z j ^ (3 / 2 : ℝ) := by
  have h := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.univ : Finset (Fin 5))
    (fun _ ↦ (1 / 5 : ℝ)) (fun j ↦ 5 * z j) (fun _ _ ↦ by norm_num)
    (by simp) (fun j _ ↦ by have := hz j; positivity) (p := 3 / 2) (by norm_num)
  have e1 : ∑ j : Fin 5, (1 / 5 : ℝ) * (5 * z j) = ∑ j, z j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    ring
  have e2 : ∀ j, (1 / 5 : ℝ) * (5 * z j) ^ (3 / 2 : ℝ) = Real.sqrt 5 * z j ^ (3 / 2 : ℝ) := by
    intro j
    rw [Real.mul_rpow (by norm_num) (hz j)]
    have h5 : (5 : ℝ) ^ (3 / 2 : ℝ) = 5 * Real.sqrt 5 := by
      rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by norm_num), Real.rpow_one,
        Real.sqrt_eq_rpow]
    rw [h5]
    ring
  rw [e1] at h
  refine h.trans (le_of_eq ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ ↦ e2 j

/-- `(x²)^{3/2} = x³` for `x ≥ 0`. -/
theorem _root_.Real.sq_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : (x ^ 2) ^ (3 / 2 : ℝ) = x ^ 3 := by
  rw [← Real.rpow_natCast x 2, ← Real.rpow_mul hx, ← Real.rpow_natCast x 3]
  norm_num

/-- `(x⁴)^{3/2} = x⁶` for `x ≥ 0`. -/
private theorem pow_four_rpow_three_halves {x : ℝ} (hx : 0 ≤ x) : (x ^ 4) ^
    (3 / 2 : ℝ) = x ^ 6 := by
  rw [← Real.rpow_natCast x 4, ← Real.rpow_mul hx, ← Real.rpow_natCast x 6]
  norm_num

private theorem pow_three_le_one_add_pow_six {x : ℝ} (hx : 0 ≤ x) : x ^ 3 ≤ 1 + x ^ 6 := by
  nlinarith [sq_nonneg (x ^ 3 - 1), pow_nonneg hx 3]

/-- Jensen for finite averages: `((1/n) ∑ zᵢ)^{3/2} ≤ (1/n) ∑ zᵢ^{3/2}`. -/
private theorem average_rpow_three_halves_le {n : ℕ} (hn : 0 < n) {z : ℕ → ℝ}
    (hz : ∀ i, 0 ≤ z i) :
    ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, z i) ^ (3 / 2 : ℝ)
      ≤ (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, z i ^ (3 / 2 : ℝ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have h := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.range n) (fun _ ↦ (1 / (n : ℝ))) z
    (fun _ _ ↦ by positivity) (by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp) (fun i _ ↦ hz i) (p := 3 / 2) (by norm_num)
  rw [← Finset.mul_sum, ← Finset.mul_sum] at h
  exact h

end Scalar

/-- The quartet dominator `S = 1 + L² + L⁴ + ā₂ + ā₄`. -/
@[expose] noncomputable def quartetDom (L : ℝ) (a : E → ℝ) (X : ℕ → Ω → E) (n : ℕ) (ω : Ω) : ℝ :=
  1 + L ^ 2 + L ^ 4 + (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 2
    + (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 4

omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem quartetDom_nonneg {L : ℝ} {a : E → ℝ} (n : ℕ) (ω : Ω) :
    0 ≤ quartetDom L a X n ω := by
  unfold quartetDom
  have h1 : 0 ≤ (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 2 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)
  have h2 : 0 ≤ (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 4 :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)
  positivity

/-- Scalar bound for the tilted second-order term: for `q = a/(β s)` with `s ≥ 1`,
`a² (c + 4 (L + q)²) ≤ c a² + 8 L² a² + (8/β²) a⁴`. -/
theorem tilt_pointwise_le {c L a β s : ℝ} (hβ : 0 < β) (hs : 1 ≤ s) :
    a ^ 2 * (c + 4 * (L + a / (β * s)) ^ 2)
      ≤ c * a ^ 2 + 8 * L ^ 2 * a ^ 2 + 8 / β ^ 2 * a ^ 4 := by
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = a / (β * s) := ⟨_, rfl⟩
  rw [← hq]
  have h1 : (L + q) ^ 2 ≤ 2 * L ^ 2 + 2 * q ^ 2 := by
    have := two_mul_le_add_sq L q
    nlinarith [this]
  have h2 : q ^ 2 ≤ a ^ 2 / β ^ 2 := by
    rw [hq, div_pow, mul_pow]
    refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hs)
  have h3 : c + 4 * (L + q) ^ 2 ≤ c + 8 * L ^ 2 + 8 * (a ^ 2 / β ^ 2) := by linarith
  calc a ^ 2 * (c + 4 * (L + q) ^ 2) ≤ a ^ 2 * (c + 8 * L ^ 2 + 8 * (a ^ 2 / β ^ 2)) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
    _ = c * a ^ 2 + 8 * L ^ 2 * a ^ 2 + 8 / β ^ 2 * a ^ 4 := by ring

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The averaged tilted bound:
`∑ᵢ a(Xᵢ)² (c + 4 (L + a(Xᵢ)/(β√n))²)/n ≤ c ā₂ + 8 L² ā₂ + (8/β²) ā₄`. -/
private theorem tilt_sum_le {c L β : ℝ} (hβ : 0 < β) {a : E → ℝ}
    {n : ℕ} (hn : 0 < n) (ω : Ω) :
    ∑ i ∈ Finset.range n, a (X i ω) ^ 2 * (c + 4 * (L + a (X i ω) / (β * Real.sqrt n)) ^ 2) / n
      ≤ c * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 2)
        + 8 * L ^ 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 2)
        + 8 / β ^ 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 4) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hs : (1 : ℝ) ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact Nat.one_le_cast.mpr hn
  calc ∑ i ∈ Finset.range n, a (X i ω) ^ 2 * (c + 4 * (L + a (X i ω) / (β * Real.sqrt n)) ^ 2) / n
      ≤ ∑ i ∈ Finset.range n,
          (c * a (X i ω) ^ 2 + 8 * L ^ 2 * a (X i ω) ^ 2 + 8 / β ^ 2 * a (X i ω) ^ 4) / n :=
        Finset.sum_le_sum fun i _ ↦
          div_le_div_of_nonneg_right (tilt_pointwise_le hβ hs) hn'.le
    _ = _ := by
        rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, ← Finset.mul_sum]
        field_simp

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- Cauchy–Schwarz for the empirical moments: `ā₂² ≤ ā₄`. -/
theorem _root_.average_sq_le_average_pow_four {a : E → ℝ} {n : ℕ} (hn : 0 < n) (ω : Ω) :
    ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 2) ^ 2
      ≤ (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 4 := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range n) (fun i ↦ a (X i ω) ^ 2)
    (fun _ ↦ (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hcs
  have e4 : ∑ i ∈ Finset.range n, (a (X i ω) ^ 2) ^ 2 = ∑ i ∈ Finset.range n, a (X i ω) ^ 4 :=
    Finset.sum_congr rfl fun i _ ↦ by ring
  rw [e4] at hcs
  rw [mul_pow, div_pow, one_pow]
  calc 1 / (n : ℝ) ^ 2 * (∑ i ∈ Finset.range n, a (X i ω) ^ 2) ^ 2
      ≤ 1 / (n : ℝ) ^ 2 * ((∑ i ∈ Finset.range n, a (X i ω) ^ 4) * n) :=
        mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = 1 / (n : ℝ) * ∑ i ∈ Finset.range n, a (X i ω) ^ 4 := by
        field_simp


omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- `S^{3/2} ≤ √5 (3 + 2 L⁶ + 2 ā₆)`: the `3/2`-power of the dominator is controlled by a linear
dominator with sixth moments. -/
theorem quartetDom_rpow_le {L : ℝ} (hL : 0 ≤ L) {a : E → ℝ} (ha0 : ∀ x, 0 ≤ a x) {n : ℕ}
    (hn : 0 < n) (ω : Ω) :
    quartetDom L a X n ω ^ (3 / 2 : ℝ)
      ≤ Real.sqrt 5
        * (3 + 2 * L ^ 6 + 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6)) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨A2, hA2⟩ : ∃ A2 : ℝ, A2 = (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨A4, hA4⟩ : ∃ A4 : ℝ, A4 = (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 4 :=
    ⟨_, rfl⟩
  obtain ⟨A6, hA6⟩ : ∃ A6 : ℝ, A6 = (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6 :=
    ⟨_, rfl⟩
  have hA20 : 0 ≤ A2 := by
    rw [hA2]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)
  have hA40 : 0 ≤ A4 := by
    rw [hA4]; exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ ↦ by positivity)
  have hq : quartetDom L a X n ω = 1 + L ^ 2 + L ^ 4 + A2 + A4 := by rw [hA2, hA4]; rfl
  rw [hq, ← hA6]
  -- the five-term convexity bound
  have hzn : ∀ j, 0 ≤ ![(1 : ℝ), L ^ 2, L ^ 4, A2, A4] j := by
    intro j
    fin_cases j
    · simp
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.mk_one, Fin.isValue, Matrix.cons_val_one,
        Matrix.cons_val_zero]; positivity
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val]; positivity
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val]; positivity
    · simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.reduceFinMk, Matrix.cons_val]; positivity
  have h := sum_five_rpow_le hzn
  simp only [Fin.sum_univ_five, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val] at h
  rw [Real.one_rpow, Real.sq_rpow_three_halves hL, pow_four_rpow_three_halves hL] at h
  -- the averaged terms
  have hA2b : A2 ^ (3 / 2 : ℝ) ≤ 1 + A6 := by
    rw [hA2, hA6]
    refine (average_rpow_three_halves_le hn (z := fun i ↦ a (X i ω) ^ 2)
      fun i ↦ by positivity).trans ?_
    have e : ∑ i ∈ Finset.range n, (a (X i ω) ^ 2) ^ (3 / 2 : ℝ)
        = ∑ i ∈ Finset.range n, a (X i ω) ^ 3 :=
      Finset.sum_congr rfl fun i _ ↦ Real.sq_rpow_three_halves (ha0 _)
    rw [e]
    have hle : ∑ i ∈ Finset.range n, a (X i ω) ^ 3
        ≤ ∑ i ∈ Finset.range n, (1 + a (X i ω) ^ 6) :=
      Finset.sum_le_sum fun i _ ↦ pow_three_le_one_add_pow_six (ha0 _)
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hle
    calc 1 / (n : ℝ) * ∑ i ∈ Finset.range n, a (X i ω) ^ 3
        ≤ 1 / (n : ℝ) * ((n : ℝ) + ∑ i ∈ Finset.range n, a (X i ω) ^ 6) :=
          mul_le_mul_of_nonneg_left hle (by positivity)
      _ = 1 + 1 / (n : ℝ) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6 := by field_simp
  have hA4b : A4 ^ (3 / 2 : ℝ) ≤ A6 := by
    rw [hA4, hA6]
    refine (average_rpow_three_halves_le hn (z := fun i ↦ a (X i ω) ^ 4)
      fun i ↦ by positivity).trans (le_of_eq ?_)
    congr 1
    exact Finset.sum_congr rfl fun i _ ↦ pow_four_rpow_three_halves (ha0 _)
  have hL3 : L ^ 3 ≤ 1 + L ^ 6 := pow_three_le_one_add_pow_six hL
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg 5))
  linarith

omit [MeasurableSpace E] in
/-- Uniform `3/2`-moments of a sequence dominated by `Cq · S` with `S^{3/2} ≤ G`, `∫ G ≤ CG`. -/
theorem moment_of_dominated {Y : ℕ → Ω → ℝ} (hYm : ∀ n, Measurable (Y n)) (hY0 : ∀ ω, Y 0 ω = 0)
    {Cq : ℝ} (hCq : 0 ≤ Cq) {S G : ℕ → Ω → ℝ} (hS0 : ∀ n ω, 0 ≤ S n ω)
    (hY : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P, |Y n ω| ≤ Cq * S n ω)
    (hGi : ∀ n : ℕ, 0 < n → Integrable (G n) P) {CG : ℝ} (hCG : 0 ≤ CG)
    (hGC : ∀ n : ℕ, 0 < n → ∫ ω, G n ω ∂P ≤ CG)
    (hSG : ∀ (n : ℕ) ω, 0 < n → S n ω ^ (3 / 2 : ℝ) ≤ G n ω) :
    (∀ n, Integrable (fun ω ↦ |Y n ω| ^ (3 / 2 : ℝ)) P) ∧
      ∀ n, ∫ ω, |Y n ω| ^ (3 / 2 : ℝ) ∂P ≤ Cq ^ (3 / 2 : ℝ) * CG := by
  have hzero : (fun ω ↦ |Y 0 ω| ^ (3 / 2 : ℝ)) = fun _ ↦ (0 : ℝ) := by
    funext ω; rw [hY0, abs_zero, Real.zero_rpow (by norm_num)]
  have hbd : ∀ n : ℕ, 0 < n → ∀ᵐ ω ∂P, ‖|Y n ω| ^ (3 / 2 : ℝ)‖ ≤ Cq ^ (3 / 2 : ℝ) * G n ω := by
    intro n hn
    filter_upwards [hY n hn] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
    calc |Y n ω| ^ (3 / 2 : ℝ) ≤ (Cq * S n ω) ^ (3 / 2 : ℝ) :=
          Real.rpow_le_rpow (abs_nonneg _) hω (by norm_num)
      _ = Cq ^ (3 / 2 : ℝ) * S n ω ^ (3 / 2 : ℝ) := Real.mul_rpow hCq (hS0 n ω)
      _ ≤ Cq ^ (3 / 2 : ℝ) * G n ω :=
          mul_le_mul_of_nonneg_left (hSG n ω hn) (Real.rpow_nonneg hCq _)
  have hint : ∀ n, Integrable (fun ω ↦ |Y n ω| ^ (3 / 2 : ℝ)) P := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hzero]; exact integrable_const _
    · exact Integrable.mono' ((hGi n hn).const_mul _)
        ((continuous_abs.measurable.comp (hYm n)).pow_const _).aestronglyMeasurable (hbd n hn)
  refine ⟨hint, fun n ↦ ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [hzero, integral_zero]; exact mul_nonneg (Real.rpow_nonneg hCq _) hCG
  · calc ∫ ω, |Y n ω| ^ (3 / 2 : ℝ) ∂P ≤ ∫ ω, Cq ^ (3 / 2 : ℝ) * G n ω ∂P :=
          integral_mono_of_nonneg (Eventually.of_forall fun ω ↦ Real.rpow_nonneg (abs_nonneg _) _)
            ((hGi n hn).const_mul _) ((hbd n hn).mono fun ω h ↦ by
              rwa [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] at h)
      _ = Cq ^ (3 / 2 : ℝ) * ∫ ω, G n ω ∂P := integral_const_mul _ _
      _ ≤ Cq ^ (3 / 2 : ℝ) * CG := mul_le_mul_of_nonneg_left (hGC n hn) (Real.rpow_nonneg hCq _)

/-- The linear dominator `√5 (3 + 2 L⁶ + 2 ā₆)` is integrable with `∫ ≤ √5 (3 + 2 C_L + 2 ∫ a⁶ dμ)`
uniformly in `n`, for an i.i.d. sample with law `μ`. -/
theorem linear_dominator_moment {L : ℕ → Ω → ℝ} {CL : ℝ}
    (hL6 : ∀ n, Integrable (fun ω ↦ L n ω ^ 6) P) (hL6C : ∀ n, ∫ ω, L n ω ^ 6 ∂P ≤ CL)
    {a : E → ℝ} (ham : Measurable a) (ha6 : Integrable (fun x ↦ a x ^ 6) μ)
    (hXm : ∀ j, Measurable (X j)) (hmap : ∀ j, P.map (X j) = μ) {n : ℕ} (hn : 0 < n) :
    Integrable (fun ω ↦ Real.sqrt 5 *
      (3 + 2 * L n ω ^ 6 + 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6))) P ∧
    ∫ ω, Real.sqrt 5 *
      (3 + 2 * L n ω ^ 6 + 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6)) ∂P
      ≤ Real.sqrt 5 * (3 + 2 * CL + 2 * ∫ x, a x ^ 6 ∂μ) := by
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hint6 : ∀ i, Integrable (fun ω ↦ a (X i ω) ^ 6) P := fun i ↦ by
    have h := (integrable_map_measure (ham.pow_const 6).aestronglyMeasurable
      (hXm i).aemeasurable).mp (by rw [hmap i]; exact ha6)
    exact h
  have hmap6 : ∀ i, ∫ ω, a (X i ω) ^ 6 ∂P = ∫ x, a x ^ 6 ∂μ := fun i ↦ by
    rw [← hmap i, integral_map (hXm i).aemeasurable (ham.pow_const 6).aestronglyMeasurable]
  have hA6i : Integrable (fun ω ↦ (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6) P :=
    (integrable_finsetSum _ fun i _ ↦ hint6 i).const_mul _
  have hA6 : ∫ ω, (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6 ∂P = ∫ x, a x ^ 6 ∂μ := by
    rw [integral_const_mul, integral_finsetSum _ fun i _ ↦ hint6 i,
      Finset.sum_congr rfl fun i _ ↦ hmap6 i, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have h1 : Integrable (fun ω ↦ 3 + 2 * L n ω ^ 6) P :=
    (integrable_const _).add ((hL6 n).const_mul 2)
  have h2 : Integrable (fun ω ↦ 3 + 2 * L n ω ^ 6
      + 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6)) P := h1.add (hA6i.const_mul 2)
  refine ⟨h2.const_mul _, ?_⟩
  have e1 : ∫ ω, (3 + 2 * L n ω ^ 6) ∂P = 3 + 2 * ∫ ω, L n ω ^ 6 ∂P := by
    rw [integral_add (integrable_const _) ((hL6 n).const_mul 2), integral_const_mul]
    simp
  have e2 : ∫ ω, (3 + 2 * L n ω ^ 6
      + 2 * ((1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6)) ∂P
      = ∫ ω, (3 + 2 * L n ω ^ 6) ∂P
        + 2 * ∫ ω, (1 / (n : ℝ)) * ∑ i ∈ Finset.range n, a (X i ω) ^ 6 ∂P := by
    rw [integral_add h1 (hA6i.const_mul 2), integral_const_mul]
  rw [integral_const_mul, e2, e1, hA6]
  exact mul_le_mul_of_nonneg_left (by linarith [hL6C n]) (Real.sqrt_nonneg 5)

end SingularLearningTheory.BayesGibbs
