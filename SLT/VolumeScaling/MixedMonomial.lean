/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.WeightedMonomial
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Ring.Star
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
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
# The ordered two-variable mixed kernel

The min/attaining read-off `λ = min_i (h_i+1)/(2k_i)`, `θ = #argmin`
reduces, by sorting coordinates and peeling from the largest `λ` down, to a
single two-variable *kernel*: on `[-1,1]²` with the product of weighted
measures `|x|^{h₁}·|y|^{h₂}` and `f = x^{2k₁} y^{2k₂}`, ordered
`λ₁ ≤ λ₂` (`λᵢ = (hᵢ+1)/(2kᵢ)`),

* strict `λ₁ < λ₂`:  `(λ, θ) = (λ₁, 1)`;
* equal  `λ₁ = λ₂`:  `(λ, θ) = (λ₁, 2)`.

The analysis peels the second (larger-`λ`) coordinate: at `|y| ≤ ε^{1/(2k₂)}`
the inner slice is the whole interval (full weighted mass), beyond it the
slice is the weighted sublevel at threshold `ε/y^{2k₂} < 1`.  The slice
is stated *piecewise* — never as `min 1 (ε/y^{2k₂})^…`, whose `y = 0` value
is division garbage.  The crossover integral `∫_{t*}^1 t^β dt`
(`β = h₂ − 2k₂λ₁ = 2k₂(λ₂−λ₁) − 1`) is kept abstract in the exact volume
lemma; the strict read-off evaluates it by the power rule (`β > −1`), the
equal read-off by `∫ dt/t = −log t*` (`β = −1`), which is where `θ = 2`'s
log factor is born.
-/

public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory

/-- The weighted measure of a symmetric interval:
`μ_h(Icc (-δ) δ) = 2δ^{h+1}/(h+1)`. -/
private theorem withDensity_abs_rpow_Icc {h δ : ℝ} (hh : 0 ≤ h) (hδ : 0 ≤ δ) :
    (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h)) (Icc (-δ) δ)
      = ENNReal.ofReal (2 * δ ^ (h + 1) / (h + 1)) := by
  have hcont : Continuous fun x : ℝ => |x| ^ h :=
    continuous_abs.rpow_const fun x => Or.inr hh
  have hnn : ∀ x : ℝ, 0 ≤ |x| ^ h := fun x => Real.rpow_nonneg (abs_nonneg x) h
  rw [withDensity_apply _ measurableSet_Icc,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
      (Filter.Eventually.of_forall hnn),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -δ ≤ δ),
    integral_abs_rpow_symm hh hδ]

/-- The mixed sublevel slice at fixed second coordinate `y`, below the
crossover (`y^{2k₂} ≤ ε`): the whole interval. -/
private theorem mixed_slice_full {k₁ k₂ : ℕ} {ε y : ℝ}
    (hbelow : (y ^ (2 * k₂) : ℝ) ≤ ε) :
    {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
      = Icc (-1 : ℝ) 1 := by
  ext x
  simp only [mem_ofPred_eq, mem_Icc, and_iff_left_iff_imp]
  rintro ⟨hx1, hx2⟩
  have hxabs : |x| ≤ 1 := abs_le.mpr ⟨hx1, hx2⟩
  have hx2k : x ^ (2 * k₁) ≤ 1 := by
    have := pow_le_one₀ (abs_nonneg x) hxabs (n := 2 * k₁)
    rwa [← abs_pow, abs_of_nonneg ((even_two_mul k₁).pow_nonneg x)] at this
  have hy2k : (0 : ℝ) ≤ y ^ (2 * k₂) := (even_two_mul k₂).pow_nonneg y
  calc x ^ (2 * k₁) * y ^ (2 * k₂) ≤ 1 * y ^ (2 * k₂) :=
        mul_le_mul_of_nonneg_right hx2k hy2k
    _ = y ^ (2 * k₂) := one_mul _
    _ ≤ ε := hbelow

/-- The mixed sublevel slice at fixed second coordinate `y`, beyond the
crossover (`ε < y^{2k₂}`): the symmetric interval at the radius. -/
private theorem mixed_slice_tail {k₁ k₂ : ℕ} {ε y : ℝ} (hk₁ : 0 < k₁)
    (hε0 : 0 < ε) (habove : ε < (y ^ (2 * k₂) : ℝ)) :
    {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
      = Icc (-((ε / y ^ (2 * k₂)) ^ (((2 * k₁ : ℕ) : ℝ))⁻¹))
          ((ε / y ^ (2 * k₂)) ^ (((2 * k₁ : ℕ) : ℝ))⁻¹) := by
  have hy0 : (0 : ℝ) < y ^ (2 * k₂) := lt_trans hε0 habove
  have hr0 : (0 : ℝ) < ε / y ^ (2 * k₂) := div_pos hε0 hy0
  have hr1 : ε / y ^ (2 * k₂) < 1 := (div_lt_one hy0).mpr habove
  have hradius : (ε / y ^ (2 * k₂)) ^ (((2 * k₁ : ℕ) : ℝ))⁻¹ ≤ 1 :=
    (Real.rpow_le_one hr0.le hr1.le (by positivity)).trans le_rfl
  ext x
  simp only [mem_ofPred_eq, mem_Icc, ← abs_le]
  constructor
  · rintro ⟨_, hf⟩
    have hx : x ^ (2 * k₁) ≤ ε / y ^ (2 * k₂) := (le_div_iff₀ hy0).mpr hf
    have habs : |x| ^ ((2 * k₁ : ℕ) : ℝ) ≤ ε / y ^ (2 * k₂) := by
      rw [Real.rpow_natCast, ← abs_pow,
        abs_of_nonneg ((even_two_mul k₁).pow_nonneg x)]
      exact hx
    exact (Real.le_rpow_inv_iff_of_pos (abs_nonneg x) hr0.le
      (by positivity : (0:ℝ) < ((2 * k₁ : ℕ) : ℝ))).mpr habs
  · intro habs
    have hx : |x| ^ ((2 * k₁ : ℕ) : ℝ) ≤ ε / y ^ (2 * k₂) :=
      (Real.le_rpow_inv_iff_of_pos (abs_nonneg x) hr0.le
        (by positivity : (0:ℝ) < ((2 * k₁ : ℕ) : ℝ))).mp habs
    rw [Real.rpow_natCast, ← abs_pow,
      abs_of_nonneg ((even_two_mul k₁).pow_nonneg x)] at hx
    refine ⟨le_trans habs hradius, ?_⟩
    exact (le_div_iff₀ hy0).mp hx

/-- The slice measure at fixed `y`, as a piecewise formula: full weighted
mass below the crossover, the power beyond it. -/
private theorem mixed_slice_measure {k₁ k₂ : ℕ} {h₁ ε : ℝ} (hk₁ : 0 < k₁)
    (hh₁ : 0 ≤ h₁) (hε0 : 0 < ε) (y : ℝ) :
    (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁))
      {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
      = if (y ^ (2 * k₂) : ℝ) ≤ ε
        then ENNReal.ofReal (2 / (h₁ + 1))
        else ENNReal.ofReal (2 / (h₁ + 1)
          * (ε / y ^ (2 * k₂)) ^ ((h₁ + 1) / (2 * k₁ : ℝ))) := by
  split_ifs with hcase
  · rw [mixed_slice_full hcase,
      withDensity_abs_rpow_Icc hh₁ zero_le_one, Real.one_rpow]
    norm_num
  · have hcase' : ε < y ^ (2 * k₂) := lt_of_not_ge hcase
    rw [mixed_slice_tail hk₁ hε0 hcase',
      withDensity_abs_rpow_Icc hh₁ (Real.rpow_nonneg
        (div_pos hε0 (lt_trans hε0 hcase')).le _)]
    congr 1
    have hr0 : (0 : ℝ) < ε / y ^ (2 * k₂) := div_pos hε0 (lt_trans hε0 hcase')
    rw [← Real.rpow_mul hr0.le]
    rw [show ((2 * k₁ : ℕ) : ℝ)⁻¹ * (h₁ + 1) = (h₁ + 1) / (2 * k₁ : ℝ) by
      push_cast
      field_simp]
    ring

section TwoVarKernel

variable {k₁ k₂ : ℕ} {h₁ h₂ : ℝ}

/-- The tail-region weighted lintegral: over `{t* < |y| ≤ 1}` the slice has
the power form, and the `μ₂`-integral evaluates to the crossover
integral `∫_{t*}^1 t^β dt` with `β = h₂ − 2k₂λ₁`. -/
private theorem mixed_tail_lintegral (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∫⁻ y in {y : ℝ | ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹ < |y| ∧ |y| ≤ 1},
      ENNReal.ofReal (2 / (h₁ + 1)
        * (ε / y ^ (2 * k₂)) ^ ((h₁ + 1) / (2 * k₁ : ℝ)))
      ∂(volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)))
      = ENNReal.ofReal ((4 / (h₁ + 1)) * ε ^ ((h₁ + 1) / (2 * k₁ : ℝ))
          * ∫ t in (ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹)..1,
              t ^ (h₂ - 2 * k₂ * ((h₁ + 1) / (2 * k₁ : ℝ)))) := by
  set lam₁ : ℝ := (h₁ + 1) / (2 * k₁ : ℝ) with hlam₁
  set tstar : ℝ := ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹ with htstar
  have hts0 : 0 < tstar := Real.rpow_pos_of_pos hε0 _
  have hts1 : tstar < 1 :=
    Real.rpow_lt_one hε0.le hε1 (by positivity)
  -- the only use of `hk₁`
  have hlam₁0 : 0 < lam₁ := by
    rw [hlam₁]; positivity
  set R : Set ℝ := {y : ℝ | tstar < |y| ∧ |y| ≤ 1} with hR
  have hRset : R = Ico (-1 : ℝ) (-tstar) ∪ Ioc tstar 1 := by
    ext y
    simp only [hR, mem_ofPred_eq, mem_union, mem_Ico, mem_Ioc]
    rcases le_or_gt 0 y with hy | hy
    · rw [abs_of_nonneg hy]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨h1, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
    · rw [abs_of_neg hy]
      constructor
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨by linarith, by linarith⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩) <;> constructor <;> linarith
  have hRmeas : MeasurableSet R := by
    rw [hRset]
    exact measurableSet_Ico.union measurableSet_Ioc
  -- the real integrand, and its key pointwise form on R
  set g : ℝ → ℝ := fun y =>
    2 / (h₁ + 1) * (ε / y ^ (2 * k₂)) ^ lam₁ * |y| ^ h₂ with hg
  set beta : ℝ := h₂ - 2 * (k₂ : ℝ) * lam₁ with hbeta
  have hpoint : ∀ y ∈ R, g y = 2 / (h₁ + 1) * ε ^ lam₁ * |y| ^ beta := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    have hyabs : 0 < |y| := lt_trans hts0 hy1
    have habs : y ^ (2 * k₂) = |y| ^ ((2 * k₂ : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, ← abs_pow,
        abs_of_nonneg ((even_two_mul k₂).pow_nonneg y)]
    have h1 : (ε / y ^ (2 * k₂)) ^ lam₁
        = ε ^ lam₁ / |y| ^ (2 * (k₂ : ℝ) * lam₁) := by
      rw [habs, Real.div_rpow hε0.le (Real.rpow_nonneg hyabs.le _),
        ← Real.rpow_mul hyabs.le]
      congr 1
      push_cast
      ring
    simp only [hg]
    rw [h1, hbeta, Real.rpow_sub hyabs]
    ring
  -- continuity of g away from 0, hence integrability on R
  have hRsub : R ⊆ Icc (-1 : ℝ) (-tstar) ∪ Icc tstar 1 := by
    rw [hRset]
    exact union_subset_union Ico_subset_Icc_self Ioc_subset_Icc_self
  have hgcont : ContinuousOn g (Icc (-1 : ℝ) (-tstar) ∪ Icc tstar 1) := by
    have hne : ∀ y ∈ Icc (-1 : ℝ) (-tstar) ∪ Icc tstar 1,
        (y : ℝ) ^ (2 * k₂) ≠ 0 := by
      rintro y (hy | hy)
      · exact pow_ne_zero _ (by rcases hy with ⟨_, h2⟩; intro h0; rw [h0] at h2; linarith)
      · exact pow_ne_zero _ (by rcases hy with ⟨h1, _⟩; intro h0; rw [h0] at h1; linarith)
    refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
    · refine ContinuousOn.rpow_const ?_ fun y hy => Or.inl ?_
      · exact (continuousOn_const.div (continuousOn_pow _) hne)
      · exact div_ne_zero hε0.ne' (hne y hy)
    · exact (continuous_abs.continuousOn).rpow_const fun y _ => Or.inr hh₂
  have hgint : IntegrableOn g R volume := by
    refine IntegrableOn.mono_set ?_ hRsub
    refine ContinuousOn.integrableOn_compact ?_ hgcont
    exact (isCompact_Icc).union isCompact_Icc
  have hgnn : ∀ y, 0 ≤ g y := by
    intro y
    rw [hg]
    have h2k : (0 : ℝ) ≤ y ^ (2 * k₂) := (even_two_mul k₂).pow_nonneg y
    have : (0:ℝ) ≤ (ε / y ^ (2 * k₂)) ^ lam₁ := by
      rcases eq_or_lt_of_le h2k with h0 | hpos
      · rw [← h0, div_zero]
        exact Real.rpow_nonneg le_rfl _
      · exact Real.rpow_nonneg (div_pos hε0 hpos).le _
    positivity
  -- withDensity → volume, then to a Bochner integral of g
  have hmeasg : Measurable fun y : ℝ =>
      ENNReal.ofReal (2 / (h₁ + 1) * (ε / y ^ (2 * k₂)) ^ lam₁) := by
    fun_prop
  rw [restrict_withDensity hRmeas,
    lintegral_withDensity_eq_lintegral_mul _
      (by fun_prop : Measurable fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)) hmeasg]
  have hconv : ∀ y ∈ R, ENNReal.ofReal (|y| ^ h₂)
        * ENNReal.ofReal (2 / (h₁ + 1) * (ε / y ^ (2 * k₂)) ^ lam₁)
      = ENNReal.ofReal (g y) := by
    intro y _
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg y) h₂), hg]
    dsimp only
    congr 1
    ring
  simp only [Pi.mul_apply]
  rw [setLIntegral_congr_fun hRmeas hconv,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hgint
      (Filter.Eventually.of_forall hgnn)]
  congr 1
  -- evaluate the real integral over R
  have hdisj : Disjoint (Ico (-1 : ℝ) (-tstar)) (Ioc tstar 1) := by
    refine Set.disjoint_left.mpr ?_
    rintro y ⟨_, h2⟩ ⟨h3, _⟩
    linarith
  have hint1 : IntegrableOn g (Ico (-1 : ℝ) (-tstar)) volume :=
    hgint.mono_set (by rw [hRset]; exact subset_union_left)
  have hint2 : IntegrableOn g (Ioc tstar 1) volume :=
    hgint.mono_set (by rw [hRset]; exact subset_union_right)
  rw [hRset, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2]
  -- both pieces equal the positive-side interval integral of the β-power form
  have hposside : ∫ y in Ioc tstar 1, g y
      = ∫ t in tstar..1, 2 / (h₁ + 1) * ε ^ lam₁ * t ^ beta := by
    rw [intervalIntegral.integral_of_le hts1.le]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro y hy
    have hyR : y ∈ R := by rw [hRset]; exact Or.inr hy
    rw [hpoint y hyR, abs_of_pos (lt_trans hts0 hy.1)]
  have hnegside : ∫ y in Ico (-1 : ℝ) (-tstar), g y
      = ∫ t in tstar..1, 2 / (h₁ + 1) * ε ^ lam₁ * t ^ beta := by
    rw [MeasureTheory.integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ -tstar),
      ← intervalIntegral.integral_comp_neg g,
      intervalIntegral.integral_of_le hts1.le,
      intervalIntegral.integral_of_le hts1.le]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc ?_
    intro y hy
    have hy0 : 0 < y := lt_trans hts0 hy.1
    have hyR : y ∈ R := by rw [hRset]; exact Or.inr hy
    have hgneg : g (-y) = g y := by
      rw [hg]
      dsimp only
      rw [abs_neg, show (-y) ^ (2 * k₂) = y ^ (2 * k₂) by
        rw [neg_pow, Even.neg_one_pow (even_two_mul k₂), one_mul]]
    dsimp only
    rw [hgneg, hpoint y hyR, abs_of_pos hy0]
  rw [hposside, hnegside, intervalIntegral.integral_const_mul]
  ring

/-- **The exact mixed two-variable volume**: for `ε ∈ (0,1)`,
`V(ε) = (4/((h₁+1)(h₂+1))) ε^{λ₂} + (4/(h₁+1)) ε^{λ₁} ∫_{t*}^1 t^β dt`. -/
private theorem sublevelVol_mixed_two (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    sublevelVol
      ((volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁)).prod
        (volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      (fun p : ℝ × ℝ => p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂)) ε
      = 2 / (h₁ + 1) * (2 / (h₂ + 1)) * ε ^ ((h₂ + 1) / (2 * k₂ : ℝ))
        + 4 / (h₁ + 1) * ε ^ ((h₁ + 1) / (2 * k₁ : ℝ))
          * ∫ t in (ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹)..1,
              t ^ (h₂ - 2 * k₂ * ((h₁ + 1) / (2 * k₁ : ℝ))) := by
  haveI : SigmaFinite (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁)) :=
    SigmaFinite.withDensity_of_ne_top' fun _ => ENNReal.ofReal_ne_top
  haveI : SigmaFinite (volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)) :=
    SigmaFinite.withDensity_of_ne_top' fun _ => ENNReal.ofReal_ne_top
  set lam₁ : ℝ := (h₁ + 1) / (2 * k₁ : ℝ) with hlam₁
  set lam₂ : ℝ := (h₂ + 1) / (2 * k₂ : ℝ) with hlam₂
  set tstar : ℝ := ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹ with htstar
  have hts0 : 0 < tstar := Real.rpow_pos_of_pos hε0 _
  have hts1 : tstar ≤ 1 := (Real.rpow_le_one hε0.le hε1.le (by positivity))
  have htspow : tstar ^ ((2 * k₂ : ℕ) : ℝ) = ε := by
    rw [htstar, ← Real.rpow_mul hε0.le, inv_mul_cancel₀ (by positivity), Real.rpow_one]
  -- crossover characterization
  have hcross : ∀ y : ℝ, |y| ≤ tstar ↔ (y ^ (2 * k₂) : ℝ) ≤ ε := by
    intro y
    have habs : y ^ (2 * k₂) = |y| ^ ((2 * k₂ : ℕ) : ℝ) := by
      rw [Real.rpow_natCast, ← abs_pow,
        abs_of_nonneg ((even_two_mul k₂).pow_nonneg y)]
    rw [habs, ← htspow]
    constructor
    · intro h
      exact Real.rpow_le_rpow (abs_nonneg y) h (by positivity)
    · intro h
      by_contra hcon
      have := Real.rpow_lt_rpow hts0.le (not_le.mp hcon)
        (by positivity : (0:ℝ) < ((2*k₂ : ℕ) : ℝ))
      linarith
  -- measurability of the sublevel set
  have hS : MeasurableSet ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      ∩ {p : ℝ × ℝ | p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂) ≤ ε}) := by
    refine (measurableSet_Icc.prod measurableSet_Icc).inter ?_
    exact measurableSet_le (by fun_prop) measurable_const
  unfold sublevelVol
  rw [Measure.prod_apply_symm hS]
  -- the slice function
  have hslice : ∀ y : ℝ,
      (fun x => (x, y)) ⁻¹' ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
        ∩ {p : ℝ × ℝ | p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂) ≤ ε})
      = if y ∈ Icc (-1 : ℝ) 1
        then {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
        else ∅ := by
    intro y
    by_cases hy : y ∈ Icc (-1 : ℝ) 1
    · rw [ite_eq_left hy]
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq]
      tauto
    · rw [ite_eq_right hy]
      ext x
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq,
        mem_empty_iff_false, iff_false]
      tauto
  -- reduce to a set lintegral over Icc(-1,1)
  have hlin : (∫⁻ y, (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁))
        ((fun x => (x, y)) ⁻¹' ((Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
          ∩ {p : ℝ × ℝ | p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂) ≤ ε}))
        ∂(volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)))
      = ∫⁻ y in Icc (-1 : ℝ) 1,
          (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁))
            {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
          ∂(volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)) := by
    rw [← lintegral_indicator measurableSet_Icc]
    refine lintegral_congr fun y => ?_
    rw [hslice y, apply_ite (volume.withDensity fun x : ℝ =>
      ENNReal.ofReal (|x| ^ h₁)), measure_empty, Set.indicator_apply]
  rw [hlin]
  -- split the domain at the crossover
  have hsplit : Icc (-1 : ℝ) 1
      = Icc (-tstar) tstar ∪ {y : ℝ | tstar < |y| ∧ |y| ≤ 1} := by
    ext y
    simp only [mem_Icc, mem_union, mem_ofPred_eq, ← abs_le]
    constructor
    · intro h
      rcases le_or_gt |y| tstar with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨h2, h⟩
    · rintro (h | ⟨_, h⟩)
      · exact le_trans h hts1
      · exact h
  have hdisj2 : Disjoint (Icc (-tstar) tstar) {y : ℝ | tstar < |y| ∧ |y| ≤ 1} := by
    refine Set.disjoint_left.mpr ?_
    intro y hy hy2
    rw [mem_Icc, ← abs_le] at hy
    exact absurd hy (not_le.mpr hy2.1)
  have hmeas2 : MeasurableSet {y : ℝ | tstar < |y| ∧ |y| ≤ 1} :=
    ((measurableSet_lt measurable_const continuous_abs.measurable).inter
      (measurableSet_le continuous_abs.measurable measurable_const))
  rw [show (volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)).restrict
        (Icc (-1 : ℝ) 1)
      = (volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)).restrict
        (Icc (-tstar) tstar ∪ {y : ℝ | tstar < |y| ∧ |y| ≤ 1}) from by
        rw [← hsplit],
    lintegral_union hmeas2 hdisj2]
  -- region 1: constant full mass
  have hreg1 : (∫⁻ y in Icc (-tstar) tstar,
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁))
          {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
        ∂(volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)))
      = ENNReal.ofReal (2 / (h₁ + 1) * (2 / (h₂ + 1) * ε ^ lam₂)) := by
    have hcongr : ∀ y ∈ Icc (-tstar) tstar,
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁))
          {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
        = ENNReal.ofReal (2 / (h₁ + 1)) := by
      intro y hy
      rw [mem_Icc, ← abs_le] at hy
      have hbelow := (hcross y).mp hy
      rw [mixed_slice_measure hk₁ hh₁ hε0 y, ite_eq_left hbelow]
    rw [setLIntegral_congr_fun measurableSet_Icc hcongr, setLIntegral_const,
      withDensity_abs_rpow_Icc hh₂ hts0.le,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h2 : tstar ^ (h₂ + 1) = ε ^ lam₂ := by
      rw [htstar, ← Real.rpow_mul hε0.le, hlam₂]
      congr 1
      push_cast
      field_simp
    rw [h2]
    ring
  -- region 2: the tail lintegral
  have hreg2 : (∫⁻ y in {y : ℝ | tstar < |y| ∧ |y| ≤ 1},
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁))
          {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
        ∂(volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)))
      = ENNReal.ofReal ((4 / (h₁ + 1)) * ε ^ lam₁
          * ∫ t in tstar..1, t ^ (h₂ - 2 * k₂ * lam₁)) := by
    have hcongr : ∀ y ∈ {y : ℝ | tstar < |y| ∧ |y| ≤ 1},
        (volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁))
          {x : ℝ | x ∈ Icc (-1 : ℝ) 1 ∧ x ^ (2 * k₁) * y ^ (2 * k₂) ≤ ε}
        = ENNReal.ofReal (2 / (h₁ + 1)
            * (ε / y ^ (2 * k₂)) ^ lam₁) := by
      intro y hy
      have habove : ε < y ^ (2 * k₂) := by
        by_contra hcon
        exact absurd ((hcross y).mpr (not_lt.mp hcon)) (not_le.mpr hy.1)
      rw [mixed_slice_measure hk₁ hh₁ hε0 y, ite_eq_right (not_le.mpr habove)]
    rw [setLIntegral_congr_fun hmeas2 hcongr]
    exact mixed_tail_lintegral hk₁ hk₂ hh₁ hh₂ hε0 hε1
  have hint_nn : 0 ≤ ∫ t in tstar..1, t ^ (h₂ - 2 * k₂ * lam₁) :=
    intervalIntegral.integral_nonneg hts1 fun t ht =>
      Real.rpow_nonneg (le_trans hts0.le ht.1) _
  have htail_nn : 0 ≤ (4 / (h₁ + 1)) * ε ^ lam₁
      * ∫ t in tstar..1, t ^ (h₂ - 2 * k₂ * lam₁) := by
    refine mul_nonneg (mul_nonneg (by positivity) ?_) hint_nn
    exact Real.rpow_nonneg hε0.le _
  rw [hreg1, hreg2, ← ENNReal.ofReal_add (by positivity) htail_nn,
    ENNReal.toReal_ofReal (by positivity)]
  ring

/-- **Strict branch**: `λ₁ < λ₂` gives `(λ, θ, c) = (λ₁, 1, ·)` —
the nonattaining coordinate contributes only a constant factor. -/
theorem hasLLCOn_mixed_two_strict (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂)
    (hlt : (h₁ + 1) / (2 * k₁ : ℝ) < (h₂ + 1) / (2 * k₂ : ℝ)) :
    HasLLCOn
      ((volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁)).prod
        (volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      (fun p : ℝ × ℝ => p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂))
      ((h₁ + 1) / (2 * k₁ : ℝ)) 1
      (4 / ((h₁ + 1) * (2 * k₂ * ((h₂ + 1) / (2 * k₂ : ℝ)
        - (h₁ + 1) / (2 * k₁ : ℝ))))) := by
  set lam₁ : ℝ := (h₁ + 1) / (2 * k₁ : ℝ) with hlam₁
  set lam₂ : ℝ := (h₂ + 1) / (2 * k₂ : ℝ) with hlam₂
  set d : ℝ := lam₂ - lam₁ with hd
  have hd0 : 0 < d := sub_pos.mpr hlt
  have hb1 : h₂ - 2 * k₂ * lam₁ + 1 = 2 * k₂ * d := by
    rw [hd, hlam₂]
    field_simp
    ring
  -- the limit function
  have hlim : Tendsto (fun ε : ℝ =>
      2 / (h₁ + 1) * (2 / (h₂ + 1)) * ε ^ d
        + 4 / (h₁ + 1) * ((1 - ε ^ d) / (2 * k₂ * d)))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 / ((h₁ + 1) * (2 * k₂ * d)))) := by
    have hεd : Tendsto (fun ε : ℝ => ε ^ d) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have hc : ContinuousAt (fun ε : ℝ => ε ^ d) 0 :=
        Real.continuousAt_rpow_const 0 d (Or.inr hd0.le)
      have h0 : (0 : ℝ) ^ d = 0 := Real.zero_rpow hd0.ne'
      have := hc.tendsto
      rw [h0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun ε : ℝ =>
        2 / (h₁ + 1) * (2 / (h₂ + 1)) * ε ^ d) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hεd.const_mul (2 / (h₁ + 1) * (2 / (h₂ + 1)))
    have h2 : Tendsto (fun ε : ℝ =>
        4 / (h₁ + 1) * ((1 - ε ^ d) / (2 * k₂ * d))) (𝓝[>] (0 : ℝ))
        (𝓝 (4 / (h₁ + 1) * ((1 - 0) / (2 * k₂ * d)))) := by
      exact (((tendsto_const_nhds.sub hεd).div_const _).const_mul _)
    have := h1.add h2
    rw [zero_add] at this
    convert this using 2
    rw [sub_zero, div_mul_div_comm, mul_one]
  refine Tendsto.congr' ?_ hlim
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  have hts0 : (0:ℝ) < ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹ := Real.rpow_pos_of_pos hε.1 _
  have hts1 : ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹ ≤ 1 :=
    Real.rpow_le_one hε.1.le hε.2.le (by positivity)
  have hTval : (∫ t in (ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹)..1,
      t ^ (h₂ - 2 * k₂ * lam₁)) = (1 - ε ^ d) / (2 * k₂ * d) := by
    have hk₂R : (0:ℝ) < (k₂ : ℝ) := Nat.cast_pos.mpr hk₂
    rw [integral_rpow (Or.inl (by nlinarith [mul_pos (mul_pos two_pos hk₂R) hd0]
      : (-1:ℝ) < h₂ - 2 * k₂ * lam₁))]
    rw [Real.one_rpow]
    have hpow : (ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹) ^ (h₂ - 2 * k₂ * lam₁ + 1)
        = ε ^ d := by
      rw [← Real.rpow_mul hε.1.le, hb1]
      congr 1
      push_cast
      field_simp
    rw [hpow, hb1]
  rw [sublevelVol_mixed_two hk₁ hk₂ hh₁ hh₂ hε.1 hε.2, hTval]
  simp only [llcScale, sub_self, Real.rpow_zero, mul_one]
  have hpos : (0:ℝ) < ε ^ lam₁ := Real.rpow_pos_of_pos hε.1 _
  have hsplit : ε ^ lam₂ = ε ^ lam₁ * ε ^ d := by
    rw [hd, ← Real.rpow_add hε.1]
    congr 1
    ring
  rw [hsplit]
  field_simp
  ring

/-- **Equal branch**: `λ₁ = λ₂ = λ` gives `(λ, θ, c) = (λ, 2, ·)` —
both coordinates attain, and the crossover integral contributes the log. -/
theorem hasLLCOn_mixed_two_equal (hk₁ : 0 < k₁) (hk₂ : 0 < k₂)
    (hh₁ : 0 ≤ h₁) (hh₂ : 0 ≤ h₂)
    (heq : (h₁ + 1) / (2 * k₁ : ℝ) = (h₂ + 1) / (2 * k₂ : ℝ)) :
    HasLLCOn
      ((volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h₁)).prod
        (volume.withDensity fun y : ℝ => ENNReal.ofReal (|y| ^ h₂)))
      (Icc (-1 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1)
      (fun p : ℝ × ℝ => p.1 ^ (2 * k₁) * p.2 ^ (2 * k₂))
      ((h₁ + 1) / (2 * k₁ : ℝ)) 2
      (4 / ((h₁ + 1) * (2 * k₂))) := by
  set lam₁ : ℝ := (h₁ + 1) / (2 * k₁ : ℝ) with hlam₁
  have hk₂R : (0:ℝ) < (k₂ : ℝ) := Nat.cast_pos.mpr hk₂
  have hbeta : h₂ - 2 * k₂ * lam₁ = -1 := by
    have h2 : (2:ℝ) * k₂ * lam₁ = h₂ + 1 := by
      rw [show lam₁ = (h₂ + 1) / (2 * k₂ : ℝ) from heq]
      field_simp
    linarith
  have hlim : Tendsto (fun ε : ℝ =>
      2 / (h₁ + 1) * (2 / (h₂ + 1)) * (-Real.log ε)⁻¹
        + 4 / (h₁ + 1) * (1 / (2 * k₂)))
      (𝓝[>] (0 : ℝ)) (𝓝 (4 / ((h₁ + 1) * (2 * k₂)))) := by
    have h0 : Tendsto (fun ε : ℝ =>
        2 / (h₁ + 1) * (2 / (h₂ + 1)) * (-Real.log ε)⁻¹)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using (tendsto_neg_log_nhdsGT_zero.inv_tendsto_atTop).const_mul
        (2 / (h₁ + 1) * (2 / (h₂ + 1)))
    have := h0.add (tendsto_const_nhds
      (x := 4 / (h₁ + 1) * (1 / (2 * (k₂:ℝ)))))
    rw [zero_add] at this
    convert this using 2
    rw [div_mul_div_comm, mul_one]
  refine Tendsto.congr' ?_ hlim
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  have hts0 : (0:ℝ) < ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹ := Real.rpow_pos_of_pos hε.1 _
  have hts1 : ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹ ≤ 1 :=
    Real.rpow_le_one hε.1.le hε.2.le (by positivity)
  have hlog : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε.1 hε.2)
  have hTval : (∫ t in (ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹)..1,
      t ^ (h₂ - 2 * k₂ * lam₁)) = (-Real.log ε) / (2 * k₂) := by
    have hcongr : ∀ t ∈ uIcc (ε ^ (((2 * k₂ : ℕ) : ℝ))⁻¹) 1,
        t ^ (h₂ - 2 * k₂ * lam₁) = t⁻¹ := by
      intro t ht
      rw [uIcc_of_le hts1] at ht
      rw [hbeta, Real.rpow_neg_one]
    rw [intervalIntegral.integral_congr hcongr,
      integral_inv (by
        rw [uIcc_of_le hts1]
        exact fun hmem => absurd hmem.1 (not_le.mpr hts0)),
      one_div, Real.log_inv, Real.log_rpow hε.1]
    push_cast
    field_simp
  rw [sublevelVol_mixed_two hk₁ hk₂ hh₁ hh₂ hε.1 hε.2, hTval]
  have heqlam : (h₂ + 1) / (2 * k₂ : ℝ) = lam₁ := heq.symm
  rw [heqlam]
  simp only [llcScale]
  rw [show (2:ℝ) - 1 = 1 by norm_num, Real.rpow_one]
  have hpos : (0:ℝ) < ε ^ lam₁ := Real.rpow_pos_of_pos hε.1 _
  have hlogne : Real.log ε ≠ 0 := (neg_pos.mp hlog).ne
  field_simp
  ring

end TwoVarKernel

end SingularLearningTheory
