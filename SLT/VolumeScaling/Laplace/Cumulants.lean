/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Laplace.Moments

/-!
# Leading loss cumulants under the deterministic Gibbs posterior

The Gibbs posterior at inverse temperature `s` localized to `K` weights the
loss `f` by `e^{−s f}`. Its raw moments `M_n(s) = ∫_K f^n e^{−s f} dμ`
obey the recursion `M_{n+1} = s·A_{n+1} − (n+1)·A_n` over the
weighted Laplace kernels `A_n` whose asymptotics are determined by `(λ, θ, c)`. This file reads
off the leading cumulants:

  `s · E_s[f] → λ`,   `E_s[f] = M_1/M_0`.

The first cumulant is `s·E_s[f] = s·A_1/A_0 − 1 → (λ+1) − 1 = λ`, using
`Γ(λ+2)/Γ(λ+1) = λ+1` and the scale shift `L_{n+1} = s^{−1} L_n`.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f : α → ℝ}

/-- **The zeroth moment.** `M_0(s) = ∫_K e^{−s f} dμ = s · A_0(s)` — the
`n = 0` analog of the recursion (its `−n·A_{n-1}` term would vanish). -/
private theorem setIntegral_exp_eq_smul_momentKernel (hfin : μ K ≠ ⊤)
    (hf_meas : Measurable f) (hf0 : 0 ≤ᵐ[μ.restrict K] f) {s : ℝ} (hs : 0 < s) :
    (∫ x in K, Real.exp (-(s * f x)) ∂μ)
      = s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * SingularLearningTheory.momentKernel μ K f 0
          ε := by
  have hpt : (fun x => Real.exp (-(s * f x)))
      =ᵐ[μ.restrict K] fun x =>
        s * ∫ ε in Ioi (f x), ε ^ 0 * Real.exp (-(s * ε)) := by
    filter_upwards [hf0] with x hx
    have hx0 : (0 : ℝ) ≤ f x := hx
    have hk := integral_momentRec_kernel hs hx0 0
    simp only [pow_zero, one_mul] at hk
    rw [← hk, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ε _ => ?_)
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    ring
  rw [integral_congr_ae hpt, integral_const_mul,
    SingularLearningTheory.setIntegral_tail_eq_momentKernel hfin hf_meas hf0 hs 0]

/-- **First cumulant.** Under `HasLLCOn μ K f λ θ c` with `c > 0`,
the posterior mean of the loss obeys `s · E_s[f] → λ`, where
`E_s[f] = (∫_K f e^{−sf})/(∫_K e^{−sf})`. -/
private theorem HasLLCOn.tendsto_smul_expectation {lam theta c : ℝ}
    (h : HasLLCOn μ K f lam theta c) (hc : 0 < c) (hfin : μ K ≠ ⊤)
    (hf_meas : Measurable f) (hf0 : 0 ≤ᵐ[μ.restrict K] f) (hlam : 0 ≤ lam) :
    Tendsto (fun s => s * ((∫ x in K, f x * Real.exp (-(s * f x)) ∂μ)
        / (∫ x in K, Real.exp (-(s * f x)) ∂μ))) atTop (𝓝 lam) := by
  have hΓpos : (0 : ℝ) < Real.Gamma (lam + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hLpos : (0 : ℝ) < c * Real.Gamma (lam + 1) := by positivity
  have hD1 := h.momentKernel_div_tendsto 1 hc hfin
  have hD0 := h.momentKernel_div_tendsto 0 hc hfin
  simp only [Nat.cast_one, Nat.cast_zero, add_zero] at hD1 hD0
  -- the ratio D₁/D₀ → c·Γ(λ+2) / c·Γ(λ+1) = λ+1
  have hratio := hD1.div hD0 hLpos.ne'
  have hval : c * Real.Gamma (lam + 1 + 1) / (c * Real.Gamma (lam + 1)) = lam + 1 := by
    rw [show lam + 1 + 1 = (lam + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : lam + 1 ≠ 0)]
    field_simp
  rw [hval] at hratio
  -- s·E_s[f] equals D₁/D₀ − 1 eventually, which tends to (λ+1) − 1 = λ
  have hfinal := hratio.sub_const 1
  have hgoal_eq : (lam + 1) - 1 = lam := by ring
  rw [hgoal_eq] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    hD0.eventually (eventually_gt_nhds hLpos)] with s hs1 hD0s
  have hs0 : (0 : ℝ) < s := by linarith
  have hL0pos : (0 : ℝ) < SingularLearningTheory.laplaceScale lam theta s :=
      SingularLearningTheory.laplaceScale_pos hs1
  have hL1pos : (0 : ℝ) < SingularLearningTheory.laplaceScale (lam + 1) theta s :=
      SingularLearningTheory.laplaceScale_pos hs1
  -- the scale shift: s·L₁ = L₀
  have hL : s * SingularLearningTheory.laplaceScale (lam + 1) theta s =
      SingularLearningTheory.laplaceScale lam theta s := by
    have hshift := SingularLearningTheory.laplaceScale_add_natCast (lam := lam) (theta := theta) 1
        hs0
    rw [Nat.cast_one] at hshift
    rw [hshift, show (-(1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    field_simp
  -- A₀ > 0 from the positive ratio limit (numerator of the positive quotient)
  have hsA0pos : 0 < s * ∫ ε in Ioi (0 : ℝ),
      Real.exp (-(s * ε)) * SingularLearningTheory.momentKernel μ K f 0 ε := by
    rcases div_pos_iff.mp hD0s with ⟨h1, _⟩ | ⟨_, h2⟩
    · exact h1
    · exact absurd h2 (not_lt.mpr hL0pos.le)
  have hA0pos : 0 < ∫ ε in Ioi (0 : ℝ),
      Real.exp (-(s * ε)) * SingularLearningTheory.momentKernel μ K f 0 ε :=
    (mul_pos_iff_of_pos_left hs0).mp hsA0pos
  -- moment identities at this s
  have hM0 := setIntegral_exp_eq_smul_momentKernel hfin hf_meas hf0 hs0
  have hM1 := SingularLearningTheory.setIntegral_pow_mul_exp_eq_momentRecursion hfin hf_meas hf0 hs0
      0
  simp only [zero_add, pow_one, Nat.cast_zero, one_mul] at hM1
  -- substitute and clear denominators
  simp only [Pi.div_apply]
  rw [hM0, hM1, ← hL]
  have hM0ne : s * (∫ ε in Ioi (0 : ℝ),
      Real.exp (-(s * ε)) * SingularLearningTheory.momentKernel μ K f 0 ε) ≠ 0 := hsA0pos.ne'
  field_simp

/-- **Second cumulant.** Under `HasLLCOn μ K f λ θ c` with `c > 0`,
the posterior variance of the loss obeys `s² · Var_s[f] → λ`, where
`Var_s[f] = M_2/M_0 − (M_1/M_0)²`. -/
theorem HasLLCOn.tendsto_sq_smul_variance {lam theta c : ℝ}
    (h : HasLLCOn μ K f lam theta c) (hc : 0 < c) (hfin : μ K ≠ ⊤)
    (hf_meas : Measurable f) (hf0 : 0 ≤ᵐ[μ.restrict K] f) (hlam : 0 ≤ lam) :
    Tendsto (fun s => s ^ 2 *
      ((∫ x in K, f x ^ 2 * Real.exp (-(s * f x)) ∂μ)
          / (∫ x in K, Real.exp (-(s * f x)) ∂μ)
        - ((∫ x in K, f x * Real.exp (-(s * f x)) ∂μ)
          / (∫ x in K, Real.exp (-(s * f x)) ∂μ)) ^ 2)) atTop (𝓝 lam) := by
  have hΓpos : (0 : ℝ) < Real.Gamma (lam + 1) := Real.Gamma_pos_of_pos (by linarith)
  have hLpos : (0 : ℝ) < c * Real.Gamma (lam + 1) := by positivity
  have hV1 : c * Real.Gamma (lam + 1 + 1) / (c * Real.Gamma (lam + 1)) = lam + 1 := by
    rw [show lam + 1 + 1 = (lam + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : lam + 1 ≠ 0)]
    field_simp
  have hV2 : c * Real.Gamma (lam + 2 + 1) / (c * Real.Gamma (lam + 1))
      = (lam + 2) * (lam + 1) := by
    rw [show lam + 2 + 1 = (lam + 1 + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : lam + 1 + 1 ≠ 0),
      show lam + 1 + 1 = (lam + 1) + 1 by ring,
      Real.Gamma_add_one (by linarith : lam + 1 ≠ 0)]
    field_simp
    ring
  -- the second moment: s²·M_2/M_0 → λ(λ+1)
  have hSecond : Tendsto (fun s => s ^ 2 *
      ((∫ x in K, f x ^ 2 * Real.exp (-(s * f x)) ∂μ)
        / (∫ x in K, Real.exp (-(s * f x)) ∂μ))) atTop (𝓝 (lam * (lam + 1))) := by
    have hD2 := h.momentKernel_div_tendsto 2 hc hfin
    have hD1 := h.momentKernel_div_tendsto 1 hc hfin
    have hD0 := h.momentKernel_div_tendsto 0 hc hfin
    simp only [Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, add_zero] at hD2 hD1 hD0
    have hcomb := (hD2.div hD0 hLpos.ne').sub ((hD1.div hD0 hLpos.ne').const_mul 2)
    rw [show c * Real.Gamma (lam + 2 + 1) / (c * Real.Gamma (lam + 1))
        - 2 * (c * Real.Gamma (lam + 1 + 1) / (c * Real.Gamma (lam + 1)))
        = lam * (lam + 1) from by rw [hV1, hV2]; ring] at hcomb
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      hD0.eventually (eventually_gt_nhds hLpos)] with s hs1 hD0s
    have hs0 : (0 : ℝ) < s := by linarith
    have hL0pos : (0 : ℝ) < SingularLearningTheory.laplaceScale lam theta s :=
        SingularLearningTheory.laplaceScale_pos hs1
    have hL1pos : (0 : ℝ) < SingularLearningTheory.laplaceScale (lam + 1) theta s :=
        SingularLearningTheory.laplaceScale_pos hs1
    have hL2pos : (0 : ℝ) < SingularLearningTheory.laplaceScale (lam + 2) theta s :=
        SingularLearningTheory.laplaceScale_pos hs1
    have hL1 : SingularLearningTheory.laplaceScale (lam + 1) theta s =
        SingularLearningTheory.laplaceScale lam theta s / s := by
      have hsh := SingularLearningTheory.laplaceScale_add_natCast (lam := lam) (theta := theta) 1
          hs0
      rw [Nat.cast_one, show (-(1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one] at hsh
      rw [hsh, inv_mul_eq_div]
    have hL2 : SingularLearningTheory.laplaceScale (lam + 2) theta s =
        SingularLearningTheory.laplaceScale lam theta s / s ^ 2 := by
      have hsh := SingularLearningTheory.laplaceScale_add_natCast (lam := lam) (theta := theta) 2
          hs0
      rw [show ((2 : ℕ) : ℝ) = 2 from by norm_num,
        Real.rpow_neg hs0.le, Real.rpow_two] at hsh
      rw [hsh]; field_simp
    have hsA0pos : 0 < s * ∫ ε in Ioi (0 : ℝ),
        Real.exp (-(s * ε)) * SingularLearningTheory.momentKernel μ K f 0 ε := by
      rcases div_pos_iff.mp hD0s with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact h1
      · exact absurd h2 (not_lt.mpr hL0pos.le)
    have hA0pos : 0 < ∫ ε in Ioi (0 : ℝ),
        Real.exp (-(s * ε)) * SingularLearningTheory.momentKernel μ K f 0 ε :=
      (mul_pos_iff_of_pos_left hs0).mp hsA0pos
    have hM0 := setIntegral_exp_eq_smul_momentKernel hfin hf_meas hf0 hs0
    have hM2 := SingularLearningTheory.setIntegral_pow_mul_exp_eq_momentRecursion hfin hf_meas hf0
        hs0 1
    norm_num at hM2
    simp only [Pi.div_apply]
    rw [hM0, hM2, hL1, hL2]
    field_simp
  have hFirst := h.tendsto_smul_expectation hc hfin hf_meas hf0 hlam
  have hcomb := hSecond.sub (hFirst.pow 2)
  rw [show lam * (lam + 1) - lam ^ 2 = lam from by ring] at hcomb
  refine hcomb.congr (fun s => ?_)
  ring

end SingularLearningTheory
