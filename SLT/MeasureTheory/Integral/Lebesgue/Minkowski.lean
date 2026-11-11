/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import Mathlib.Order.CompletePartialOrder
import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
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
# Minkowski's inequality for countable sums, and limits in `L²` versus almost everywhere

No thesis counterpart; used by `EmpiricalProcess/LimitOfAnalytic.lean` (the moment bounds of
[Hit26, Lemma 4.2.4] and [Hit26, Lemma 4.2.8]
for series of coefficient processes) and `EmpiricalProcess/LocalExpansion.lean` (identifying
the `L²(q)`-sum of a power series with its pointwise sum).
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Minkowski's inequality in `L²` for a finite sum of `ℝ≥0∞`-valued functions, in the
`rpow` form Mathlib's `ENNReal.lintegral_Lp_add_le` produces. -/
private theorem lintegral_sum_rpow_le {g : ι → Ω → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (s : Finset ι) :
    (∫⁻ ω, (∑ i ∈ s, g i ω) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤
      ∑ i ∈ s, (∫⁻ ω, g i ω ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h := ENNReal.lintegral_Lp_add_le (μ := P) (hg a).aemeasurable
      (Finset.measurable_sum s fun i _ ↦ hg i).aemeasurable (one_le_two : (1 : ℝ) ≤ 2)
    simp only [Pi.add_apply] at h
    simp only [Finset.sum_insert ha]
    exact h.trans (add_le_add le_rfl ih)

/-- Minkowski's inequality in `L²` for a finite sum of `ℝ≥0∞`-valued functions. -/
theorem _root_.MeasureTheory.lintegral_sum_sq_le {g : ι → Ω → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (s : Finset ι) :
    ∫⁻ ω, (∑ i ∈ s, g i ω) ^ 2 ∂P ≤ (∑ i ∈ s, (∫⁻ ω, g i ω ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 := by
  have h := lintegral_sum_rpow_le (P := P) hg s
  simp only [ENNReal.rpow_two] at h
  calc ∫⁻ ω, (∑ i ∈ s, g i ω) ^ 2 ∂P
      = ((∫⁻ ω, (∑ i ∈ s, g i ω) ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num
    _ ≤ _ := pow_le_pow_left' h 2

/-- Minkowski's inequality in `L²` for a countable sum of `ℝ≥0∞`-valued functions. -/
theorem _root_.MeasureTheory.lintegral_tsum_sq_le [Countable ι] {g : ι → Ω → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i)) :
    ∫⁻ ω, (∑' i, g i ω) ^ 2 ∂P ≤ (∑' i, (∫⁻ ω, g i ω ^ 2 ∂P) ^ (1 / 2 : ℝ)) ^ 2 := by
  classical
  have hsq : ∀ ω, (∑' i, g i ω) ^ 2 = ⨆ s : Finset ι, (∑ i ∈ s, g i ω) ^ 2 := fun ω ↦ by
    rw [ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_pow_of_ne_zero two_ne_zero]
  simp_rw [hsq]
  rw [lintegral_iSup_directed]
  · exact iSup_le fun s ↦
      (lintegral_sum_sq_le hg s).trans (pow_le_pow_left' (ENNReal.sum_le_tsum s) 2)
  · exact fun s ↦ ((Finset.measurable_sum s fun i _ ↦ hg i).pow_const 2).aemeasurable
  · intro s t
    refine ⟨s ∪ t, fun ω ↦ ?_, fun ω ↦ ?_⟩
    · exact pow_le_pow_left' (Finset.sum_le_sum_of_subset Finset.subset_union_left) 2
    · exact pow_le_pow_left' (Finset.sum_le_sum_of_subset Finset.subset_union_right) 2

/-- If `s N → G` in `L²` and `s N → t` almost everywhere, then `G = t` almost everywhere. -/
private theorem ae_eq_of_tendsto_eLpNorm_of_tendsto_ae {s : ℕ → Ω → ℝ} {G t : Ω → ℝ}
    (_hs : ∀ N, AEStronglyMeasurable (s N) P) (_hG : AEStronglyMeasurable G P)
    (hL : Tendsto (fun N ↦ eLpNorm (s N - G) 2 P) atTop (𝓝 0))
    (hpt : ∀ᵐ ω ∂P, Tendsto (fun N ↦ s N ω) atTop (𝓝 (t ω))) : G =ᵐ[P] t := by
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero hL).exists_seq_tendsto_ae
  filter_upwards [hae, hpt] with ω hGω htω
  exact tendsto_nhds_unique hGω (htω.comp hns.tendsto_atTop)

/-- Minkowski's inequality in `L^p`, `p ≥ 1` real, for a finite sum of `ℝ≥0∞`-valued
functions, in the `rpow` form Mathlib's `ENNReal.lintegral_Lp_add_le` produces. -/
private theorem lintegral_sum_rpow_le' {g : ι → Ω → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (s : Finset ι)
    {p : ℝ} (hp : 1 ≤ p) :
    (∫⁻ ω, (∑ i ∈ s, g i ω) ^ p ∂P) ^ (1 / p) ≤ ∑ i ∈ s, (∫⁻ ω, g i ω ^ p ∂P) ^ (1 / p) := by
  classical
  have hp0 : 0 < p := zero_lt_one.trans_le hp
  induction s using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos, hp0]
  | insert a s ha ih =>
    have h := ENNReal.lintegral_Lp_add_le (μ := P) (hg a).aemeasurable
      (Finset.measurable_sum s fun i _ ↦ hg i).aemeasurable hp
    simp only [Pi.add_apply] at h
    simp only [Finset.sum_insert ha]
    exact h.trans (add_le_add le_rfl ih)

/-- Minkowski's inequality in `L^p`, `p ≥ 1` a natural number, for a finite sum of
`ℝ≥0∞`-valued functions. -/
theorem _root_.MeasureTheory.lintegral_sum_pow_le {g : ι → Ω → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (s : Finset ι)
    {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ ω, (∑ i ∈ s, g i ω) ^ p ∂P ≤ (∑ i ∈ s, (∫⁻ ω, g i ω ^ p ∂P) ^ (1 / p : ℝ)) ^ p := by
  have hp' : (1 : ℝ) ≤ p := Nat.one_le_cast.mpr hp
  have hp0 : (p : ℝ) ≠ 0 := (zero_lt_one.trans_le hp').ne'
  have h := lintegral_sum_rpow_le' (P := P) hg s hp'
  simp only [ENNReal.rpow_natCast] at h
  calc ∫⁻ ω, (∑ i ∈ s, g i ω) ^ p ∂P
      = ((∫⁻ ω, (∑ i ∈ s, g i ω) ^ p ∂P) ^ (1 / p : ℝ)) ^ p := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, one_div_mul_cancel hp0, ENNReal.rpow_one]
    _ ≤ _ := pow_le_pow_left' h p

/-- Minkowski's inequality in `L^p`, `p ≥ 1` a natural number, for a countable sum of
`ℝ≥0∞`-valued functions. -/
theorem _root_.MeasureTheory.lintegral_tsum_pow_le [Countable ι] {g : ι → Ω → ℝ≥0∞}
    (hg : ∀ i, Measurable (g i))
    {p : ℕ} (hp : 1 ≤ p) :
    ∫⁻ ω, (∑' i, g i ω) ^ p ∂P ≤ (∑' i, (∫⁻ ω, g i ω ^ p ∂P) ^ (1 / p : ℝ)) ^ p := by
  classical
  have hp0 : p ≠ 0 := by omega
  have hpow : ∀ ω, (∑' i, g i ω) ^ p = ⨆ s : Finset ι, (∑ i ∈ s, g i ω) ^ p := fun ω ↦ by
    rw [ENNReal.tsum_eq_iSup_sum, ENNReal.iSup_pow_of_ne_zero hp0]
  simp_rw [hpow]
  rw [lintegral_iSup_directed]
  · exact iSup_le fun s ↦
      (lintegral_sum_pow_le hg s hp).trans (pow_le_pow_left' (ENNReal.sum_le_tsum s) p)
  · exact fun s ↦ ((Finset.measurable_sum s fun i _ ↦ hg i).pow_const p).aemeasurable
  · intro s t
    refine ⟨s ∪ t, fun ω ↦ ?_, fun ω ↦ ?_⟩
    · exact pow_le_pow_left' (Finset.sum_le_sum_of_subset Finset.subset_union_left) p
    · exact pow_le_pow_left' (Finset.sum_le_sum_of_subset Finset.subset_union_right) p

/-- If `s N → G` in `L^p` for some `p ≠ 0` and `s N → t` almost everywhere, then `G = t` almost
everywhere. -/
theorem _root_.MeasureTheory.ae_eq_of_tendsto_eLpNorm_of_tendsto_ae' {s : ℕ → Ω → ℝ} {G t : Ω → ℝ}
    {p : ℝ≥0∞}
    (hp : p ≠ 0) (_hs : ∀ N, AEStronglyMeasurable (s N) P) (_hG : AEStronglyMeasurable G P)
    (hL : Tendsto (fun N ↦ eLpNorm (s N - G) p P) atTop (𝓝 0))
    (hpt : ∀ᵐ ω ∂P, Tendsto (fun N ↦ s N ω) atTop (𝓝 (t ω))) : G =ᵐ[P] t := by
  obtain ⟨ns, hns, hae⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm hp hL).exists_seq_tendsto_ae
  filter_upwards [hae, hpt] with ω hGω htω
  exact tendsto_nhds_unique hGω (htω.comp hns.tendsto_atTop)

end SingularLearningTheory
