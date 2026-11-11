/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Monomial weights in the volume integrand: the one-dimensional base

The blow-up charts hand the volume integrals a monomial Jacobian weight `∏ u^{M−1}`; the read-off
formula `λ = min_i (h_i+1)/(2k_i)` ([Wat09, Theorem 4.6, Corollary 4.3 and Theorem 4.7; the
formula is Definition 6.4, eq. (6.16)]) needs a weighted volume calculus that the bounded-weight
invariance of `Invariance` cannot supply — monomial weights vanish at the center and genuinely
shift `λ`.

This file is the one-dimensional base: under the weighted measure `volume.withDensity (|x|^h)`
on `[-1,1]` (real `h ≥ 0`), the principal monomial `|x|^p` has the exact sublevel volume

  `W(ε) = (2/(h+1)) · ε^{(h+1)/p}`,   `ε ∈ (0,1)`,

hence `HasLLCOn` with `(λ, θ, c) = ((h+1)/p, 1, 2/(h+1))`. At `h = 0` this recovers the
unweighted instance `(1/p, 1, 2)` of `MonomialVolume`. The exponents that occur in the charts are
the naturals `M − 1`, so `h : ℝ, 0 ≤ h` is free generality.

The computation: the sublevel set is the symmetric interval `[−δ, δ]` with `δ = ε^{1/p}` (exactly
as in the unweighted case), and `∫_{−δ}^{δ} |x|^h dx = 2δ^{h+1}/(h+1)` by reflection symmetry
plus the power rule. `SignedPower` and `FiberIdentity` build on these formulas.
-/

public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory

/-- The symmetric weighted interval integral:
`∫ x in -δ..δ, |x|^h = 2δ^{h+1}/(h+1)` for `h ≥ 0 ≤ δ`. -/
theorem _root_.integral_abs_rpow_symm {h δ : ℝ} (hh : 0 ≤ h) (hδ : 0 ≤ δ) :
    ∫ x in (-δ : ℝ)..δ, |x| ^ h = 2 * δ ^ (h + 1) / (h + 1) := by
  have hcont : Continuous fun x : ℝ => |x| ^ h :=
    continuous_abs.rpow_const fun x => Or.inr hh
  have hhalf : ∫ x in (0 : ℝ)..δ, |x| ^ h = δ ^ (h + 1) / (h + 1) := by
    rw [intervalIntegral.integral_congr (g := fun x => x ^ h) ?_]
    · rw [integral_rpow (Or.inl (by linarith))]
      rw [Real.zero_rpow (by linarith : h + 1 ≠ 0), sub_zero]
    · intro x hx
      rw [uIcc_of_le hδ, mem_Icc] at hx
      dsimp only
      rw [abs_of_nonneg hx.1]
  have hneg : ∫ x in (-δ : ℝ)..0, |x| ^ h = δ ^ (h + 1) / (h + 1) := by
    have h2 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := δ)
      (fun x => |x| ^ h)
    simp only [abs_neg, neg_zero] at h2
    rw [← h2]
    exact hhalf
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := (-δ : ℝ)) (b := 0)
    (c := δ) (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    hneg, hhalf]
  ring

/-- **Exact weighted volume**: under the weight `|x|^h`, the sublevel
volume of `|x|^p` on `[-1,1]` at `ε ∈ (0,1)` is `(2/(h+1)) ε^{(h+1)/p}`. -/
theorem sublevelVol_abs_rpow_withDensity_Icc {p h ε : ℝ} (hp : 0 < p) (hh : 0 ≤ h)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    sublevelVol (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h))
      (Icc (-1 : ℝ) 1) (fun x => |x| ^ p) ε
      = 2 / (h + 1) * ε ^ ((h + 1) / p) := by
  have hδ0 : 0 ≤ ε ^ p⁻¹ := Real.rpow_nonneg hε0.le _
  have hδ1 : ε ^ p⁻¹ ≤ 1 := Real.rpow_le_one hε0.le hε1.le (by positivity)
  have hsub : {x : ℝ | |x| ^ p ≤ ε} = Icc (-(ε ^ p⁻¹)) (ε ^ p⁻¹) := by
    ext x
    rw [mem_ofPred_eq, mem_Icc, ← abs_le,
      Real.le_rpow_inv_iff_of_pos (abs_nonneg x) hε0.le hp]
  have hcont : Continuous fun x : ℝ => |x| ^ h :=
    continuous_abs.rpow_const fun x => Or.inr hh
  have hnn : ∀ x : ℝ, 0 ≤ |x| ^ h := fun x => Real.rpow_nonneg (abs_nonneg x) h
  unfold sublevelVol
  rw [hsub, inter_eq_self_of_subset_right (Icc_subset_Icc (neg_le_neg hδ1) hδ1),
    withDensity_apply _ measurableSet_Icc,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
      (Filter.Eventually.of_forall hnn),
    ENNReal.toReal_ofReal (by
      refine integral_nonneg fun x => hnn x),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(ε ^ p⁻¹) ≤ ε ^ p⁻¹),
    integral_abs_rpow_symm hh hδ0,
    ← Real.rpow_mul hε0.le]
  rw [show p⁻¹ * (h + 1) = (h + 1) / p by field_simp]
  ring

/-- **The weighted one-dimensional base case**: `|x|^p` under the weight `|x|^h`
on `[-1,1]` has `(λ, θ, c) = ((h+1)/p, 1, 2/(h+1))`.  The weight shifts
`λ` from `1/p` to `(h+1)/p` and keeps `θ = 1`. -/
theorem hasLLCOn_abs_rpow_withDensity {p h : ℝ} (hp : 0 < p) (hh : 0 ≤ h) :
    HasLLCOn (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h))
      (Icc (-1 : ℝ) 1) (fun x => |x| ^ p) ((h + 1) / p) 1 (2 / (h + 1)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  rw [sublevelVol_abs_rpow_withDensity_Icc hp hh hε.1 hε.2]
  simp only [llcScale, sub_self, Real.rpow_zero, mul_one]
  rw [mul_div_assoc, div_self (Real.rpow_pos_of_pos hε.1 _).ne', mul_one]

/-- Even-power, natural-weight form: `x^(2k)` under the weight `|x|^m`
(the chart Jacobian exponent `m = M − 1`) has
`(λ, θ, c) = ((m+1)/(2k), 1, 2/(m+1))`. -/
theorem hasLLCOn_pow_even_withDensity {k m : ℕ} (hk : 0 < k) :
    HasLLCOn (volume.withDensity fun x => ENNReal.ofReal (|x| ^ (m : ℝ)))
      (Icc (-1 : ℝ) 1) (fun x => x ^ (2 * k))
      (((m : ℝ) + 1) / ((2 * k : ℕ) : ℝ)) 1 (2 / ((m : ℝ) + 1)) := by
  have heq : (fun x : ℝ => x ^ (2 * k)) = fun x : ℝ => |x| ^ ((2 * k : ℕ) : ℝ) := by
    funext x
    rw [Real.rpow_natCast, pow_abs]
    exact (abs_of_nonneg ((even_two_mul k).pow_nonneg x)).symm
  rw [heq]
  exact hasLLCOn_abs_rpow_withDensity
    (by exact_mod_cast Nat.pos_of_ne_zero (by omega)) (Nat.cast_nonneg m)

end SingularLearningTheory
