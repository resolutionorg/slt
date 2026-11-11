/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.Probability.Moments.TiltedCumulant
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Log Partition Second Order
-/

public section

open MeasureTheory Set

namespace ProbabilityTheory

variable {W : Type*} [MeasurableSpace W] {ρ : Measure W} {f : W → ℝ}

private theorem tiltLogPartition_zero [IsProbabilityMeasure ρ] : tiltLogPartition ρ f 0 = 0 := by
  unfold tiltLogPartition tiltPartition
  simp

/-- `Var_s(f) ≤ E^s[f²]`. -/
theorem tiltVar_le_second_moment (t : ℝ) :
    tiltVar ρ f t ≤ tiltNum2 ρ f t / tiltPartition ρ f t := by
  unfold tiltVar
  linarith [sq_nonneg (tiltMean ρ f t)]

section SecondOrder

variable [IsProbabilityMeasure ρ] (hf : Measurable f) {I : Set ℝ} (hI : IsOpen I)
  (hIc : Convex ℝ I) {B : W → ℝ} (hB : Integrable B ρ)
  (hbound : ∀ t ∈ I, ∀ w, (1 + f w ^ 2) * Real.exp (-(t * f w)) ≤ B w)
  (h0 : (0 : ℝ) ∈ I) (h1 : (1 : ℝ) ∈ I)
include hf hI hIc hB hbound h0 h1

omit hf hI hB hbound in
private theorem Icc_subset_of_mem : Icc (0 : ℝ) 1 ⊆ I := by
  have := hIc.ordConnected.uIcc_subset h0 h1
  rwa [uIcc_of_le zero_le_one] at this

/-- The tilted mean is antitone on `[0,1]`: `M(s) ≤ M(0)`. -/
private theorem tiltMean_le_tiltMean_zero {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    tiltMean ρ f s ≤ tiltMean ρ f 0 := by
  have hsub := Icc_subset_of_mem hIc h0 h1
  have h := tiltMean_sub_eq hf hI hB hbound hIc h0 (hsub hs)
  have hnn : 0 ≤ ∫ t in (0 : ℝ)..s, tiltVar ρ f t :=
    intervalIntegral.integral_nonneg hs.1 fun t ht ↦
      tiltVar_nonneg hf hB hbound (hsub ⟨ht.1, ht.2.trans hs.2⟩)
  linarith

/-- `M(0) − M(s) ≤ s · sup_{[0,1]} V`. -/
private theorem tiltMean_zero_sub_le {Vmax : ℝ} (hV : ∀ s ∈ Icc (0 : ℝ) 1, tiltVar ρ f s ≤ Vmax)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : tiltMean ρ f 0 - tiltMean ρ f s ≤ s * Vmax := by
  have hsub := Icc_subset_of_mem hIc h0 h1
  have h := tiltMean_sub_eq hf hI hB hbound hIc h0 (hsub hs)
  have hVc : ContinuousOn (tiltVar ρ f) (Icc 0 s) :=
    (continuousOn_tiltVar hf hI hB hbound).mono fun t ht ↦ hsub ⟨ht.1, ht.2.trans hs.2⟩
  have hle : ∫ t in (0 : ℝ)..s, tiltVar ρ f t ≤ ∫ t in (0 : ℝ)..s, Vmax :=
    intervalIntegral.integral_mono_on hs.1 (hVc.intervalIntegrable_of_Icc hs.1)
      intervalIntegrable_const fun t ht ↦ hV t ⟨ht.1, ht.2.trans hs.2⟩
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hle
  linarith

/-- **The second-order Taylor step**: `|−L(1) − M(0)| ≤ ½ sup_{[0,1]} V`. -/
theorem abs_neg_tiltLogPartition_one_sub_tiltMean_zero_le {Vmax : ℝ}
    (hV : ∀ s ∈ Icc (0 : ℝ) 1, tiltVar ρ f s ≤ Vmax) :
    |-(tiltLogPartition ρ f 1) - tiltMean ρ f 0| ≤ Vmax / 2 := by
  have hsub := Icc_subset_of_mem hIc h0 h1
  have hL := tiltLogPartition_sub_eq hf hI hB hbound hIc h0 h1
  rw [tiltLogPartition_zero, sub_zero] at hL
  have hMc : ContinuousOn (tiltMean ρ f) (Icc 0 1) := fun t ht ↦
    (hasDerivAt_tiltMean hf hI hB hbound (hsub ht)).continuousAt.continuousWithinAt
  have hMint : IntervalIntegrable (tiltMean ρ f) volume 0 1 :=
    hMc.intervalIntegrable_of_Icc zero_le_one
  have hup : ∫ s in (0 : ℝ)..1, tiltMean ρ f s ≤ ∫ s in (0 : ℝ)..1, tiltMean ρ f 0 :=
    intervalIntegral.integral_mono_on zero_le_one hMint intervalIntegrable_const fun s hs ↦
      tiltMean_le_tiltMean_zero hf hI hIc hB hbound h0 h1 hs
  have hlow : ∫ s in (0 : ℝ)..1, (tiltMean ρ f 0 - s * Vmax) ≤ ∫ s in (0 : ℝ)..1, tiltMean ρ f s :=
    intervalIntegral.integral_mono_on zero_le_one
      (IntervalIntegrable.sub intervalIntegrable_const
        (intervalIntegral.intervalIntegrable_id.mul_const Vmax))
      hMint fun s hs ↦ by linarith [tiltMean_zero_sub_le hf hI hIc hB hbound h0 h1 hV hs]
  rw [intervalIntegral.integral_const, sub_zero, one_smul] at hup
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    (intervalIntegral.intervalIntegrable_id.mul_const Vmax), intervalIntegral.integral_const,
    intervalIntegral.integral_mul_const, integral_id] at hlow
  norm_num at hlow
  have hV0 : 0 ≤ Vmax := (tiltVar_nonneg hf hB hbound h0).trans (hV 0 ⟨le_rfl, zero_le_one⟩)
  rw [abs_le]
  constructor <;> nlinarith

end SecondOrder

/-- **Lemma 6.5 (3), the `B₂` bound.** For finitely many tilted families `(ρⱼ, fⱼ)`
(`ρⱼ` the `σ = 0` posterior, `fⱼ = a(Xⱼ, u) u^k`), with `nBₜ(ε) = ∑ⱼ −Lⱼ(1)` and
`nGₜ(ε) = ∑ⱼ Mⱼ(0)`,

`|nBₜ(ε) − nGₜ(ε)| ≤ ½ ∑ⱼ sup_{[0,1]} Varⱼ`. -/
private theorem abs_sum_neg_tiltLogPartition_sub_le {ι : Type*} (s : Finset ι)
    {ρ : ι → Measure W} [∀ j, IsProbabilityMeasure (ρ j)] {f : ι → W → ℝ}
    (hf : ∀ j, Measurable (f j)) {I : ι → Set ℝ} (hI : ∀ j, IsOpen (I j))
    (hIc : ∀ j, Convex ℝ (I j)) {B : ι → W → ℝ} (hB : ∀ j, Integrable (B j) (ρ j))
    (hbound : ∀ j, ∀ t ∈ I j, ∀ w, (1 + f j w ^ 2) * Real.exp (-(t * f j w)) ≤ B j w)
    (h0 : ∀ j, (0 : ℝ) ∈ I j) (h1 : ∀ j, (1 : ℝ) ∈ I j) {Vmax : ι → ℝ}
    (hV : ∀ j, ∀ t ∈ Icc (0 : ℝ) 1, tiltVar (ρ j) (f j) t ≤ Vmax j) :
    |(∑ j ∈ s, -(tiltLogPartition (ρ j) (f j) 1)) - ∑ j ∈ s, tiltMean (ρ j) (f j) 0|
      ≤ (∑ j ∈ s, Vmax j) / 2 := by
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ ↦ ?_)
  exact abs_neg_tiltLogPartition_one_sub_tiltMean_zero_le (hf j) (hI j) (hIc j) (hB j) (hbound j)
    (h0 j) (h1 j) (hV j)

end ProbabilityTheory
