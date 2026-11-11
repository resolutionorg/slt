/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import SLT.VolumeScaling.WeightedMonomial
import SLT.VolumeScaling.Invariance
public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
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
# Adjoining a strictly non-minimal direction: the analytic core (§2.1.5)

This file develops the analytic core of the single-monomial volume calculus:
adjoining one extra weighted coordinate, whose ratio `(h+1)/e` is strictly
larger than the current scaling exponent `λ`, leaves the sublevel-volume
exponents `(λ, θ)` unchanged. The argument is a Tonelli split (2.1.5.1), a
far-tail bound (2.1.5.2), a convergent dyadic-shell estimate (2.1.5.3–2.1.5.4),
and a final squeeze (2.1.5.5).

It opens with the auxiliary dilation control (plan atom **2.1.5.0**): replacing
the threshold `ε` by a fixed positive multiple `a·ε` does not change the order
of the model scale `llcScale λ θ ε = ε^λ (−log ε)^{θ−1}`. The shell estimate
2.1.5.3 invokes this at `a = 2^{k+1}` to see that the logarithmic factor is not
inflated when the threshold is scaled.

The general Θ-stability of `llcScale` under ε-dilation by an arbitrary positive
constant is already established in `Dln/VolumeScaling/Invariance.lean` as
`isTheta_llcScale_comp_div`, in the form
`(fun ε => llcScale λ θ (ε / c)) =Θ[𝓝[>] 0] llcScale λ θ` for `c > 0`. The
multiplicative form below is that lemma at `c = a⁻¹`, since `ε / a⁻¹ = a·ε`.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal

namespace SingularLearningTheory

/-- **Plan atom 2.1.5.0 — fixed-dilation control (multiplicative form).** For a
fixed positive `a`, the model scale evaluated at `a·ε` is Θ-equivalent to the
model scale at `ε` near `0⁺`:
`(fun ε => llcScale λ θ (a·ε)) =Θ[𝓝[>] 0] llcScale λ θ`.

This is `isTheta_llcScale_comp_div` (Θ-stability under ε-dilation by any
positive constant, proved in `Invariance.lean`) specialized to `c = a⁻¹`, using
`ε / a⁻¹ = a·ε`. The reusable multiplicative shape is what the dyadic-shell
estimate consumes. -/
theorem isTheta_llcScale_comp_mul {lam theta a : ℝ} (ha : 0 < a) :
    (fun ε => llcScale lam theta (a * ε)) =Θ[𝓝[>] (0 : ℝ)] llcScale lam theta := by
  have h := isTheta_llcScale_comp_div (lam := lam) (theta := theta) (inv_pos.mpr ha)
  have harg : ∀ ε : ℝ, a * ε = ε / a⁻¹ := by
    intro ε; rw [div_eq_mul_inv, inv_inv, mul_comm]
  have heq : (fun ε => llcScale lam theta (a * ε))
      = (fun ε => llcScale lam theta (ε / a⁻¹)) := by
    funext ε; rw [harg ε]
  rw [heq]; exact h

/-- **Plan atom 2.1.3 — one-variable slice.** For `p > 0`, `h ≥ 0`, `t > 0`,
`ε > 0`, the weighted mass of the slice `{u ∈ [−1,1] : t·|u|^p ≤ ε}` under the
density `|u|^h` is `(2/(h+1)) · min(1, (ε/t)^{(h+1)/p})`.

The slice is the symmetric interval `[−ρ, ρ]` with `ρ = min(1, (ε/t)^{1/p})`,
since `t·|u|^p ≤ ε ⟺ |u| ≤ (ε/t)^{1/p}` and `|u| ≤ 1` on the box. Its weighted
mass is `2ρ^{h+1}/(h+1)` (`integral_abs_rpow_symm`), and
`ρ^{h+1} = min(1, (ε/t)^{(h+1)/p})`. The Tonelli decomposition (2.1.5.1)
integrates this over the base space with `t = m(x)`. This generalizes the
`t = 1` case `sublevelVol_abs_rpow_withDensity_Icc`. -/
theorem sublevelVol_scaled_abs_rpow_withDensity_Icc {p h t ε : ℝ}
    (hp : 0 < p) (hh : 0 ≤ h) (ht : 0 < t) (hε : 0 < ε) :
    sublevelVol (volume.withDensity fun u => ENNReal.ofReal (|u| ^ h))
      (Icc (-1 : ℝ) 1) (fun u => t * |u| ^ p) ε
      = 2 / (h + 1) * min 1 ((ε / t) ^ ((h + 1) / p)) := by
  have hq0 : (0 : ℝ) ≤ ε / t := (div_pos hε ht).le
  set ρ : ℝ := min 1 ((ε / t) ^ p⁻¹) with hρdef
  have hρ0 : 0 ≤ ρ := le_min zero_le_one (Real.rpow_nonneg hq0 _)
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hcont : Continuous fun x : ℝ => |x| ^ h :=
    continuous_abs.rpow_const fun _ => Or.inr hh
  have hnn : ∀ x : ℝ, 0 ≤ |x| ^ h := fun x => Real.rpow_nonneg (abs_nonneg x) h
  -- The localized sublevel set is the symmetric interval [-ρ, ρ].
  have hset : Icc (-1 : ℝ) 1 ∩ {x | t * |x| ^ p ≤ ε} = Icc (-ρ) ρ := by
    ext u
    simp only [mem_inter_iff, mem_Icc, mem_ofPred_eq, ← abs_le]
    constructor
    · rintro ⟨hu1, hu2⟩
      have hpow : |u| ^ p ≤ ε / t := by rw [le_div_iff₀ ht, mul_comm]; exact hu2
      exact le_min hu1 ((Real.le_rpow_inv_iff_of_pos (abs_nonneg u) hq0 hp).mpr hpow)
    · intro hu
      refine ⟨le_trans hu hρ1, ?_⟩
      have hpow : |u| ^ p ≤ ε / t :=
        (Real.le_rpow_inv_iff_of_pos (abs_nonneg u) hq0 hp).mp (le_trans hu (min_le_right _ _))
      rw [le_div_iff₀ ht, mul_comm] at hpow; exact hpow
  -- ρ^(h+1) = min 1 ((ε/t)^((h+1)/p)).
  have hmul : ((ε / t) ^ p⁻¹) ^ (h + 1) = (ε / t) ^ ((h + 1) / p) := by
    rw [← Real.rpow_mul hq0]; congr 1; ring
  have hexp : ρ ^ (h + 1) = min 1 ((ε / t) ^ ((h + 1) / p)) := by
    rcases le_total ((ε / t) ^ p⁻¹) 1 with hle | hge
    · have hle2 : (ε / t) ^ ((h + 1) / p) ≤ 1 := by
        rw [← hmul]; exact Real.rpow_le_one (Real.rpow_nonneg hq0 _) hle (by linarith)
      rw [hρdef, min_eq_right hle, hmul, min_eq_right hle2]
    · have hge2 : (1 : ℝ) ≤ (ε / t) ^ ((h + 1) / p) := by
        rw [← hmul]
        calc (1 : ℝ) = (1 : ℝ) ^ (h + 1) := (Real.one_rpow _).symm
          _ ≤ ((ε / t) ^ p⁻¹) ^ (h + 1) := Real.rpow_le_rpow zero_le_one hge (by linarith)
      rw [hρdef, min_eq_left hge, Real.one_rpow, min_eq_left hge2]
  unfold sublevelVol
  rw [hset, withDensity_apply _ measurableSet_Icc,
    ← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
      (Filter.Eventually.of_forall hnn),
    ENNReal.toReal_ofReal (integral_nonneg fun x => hnn x),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -ρ ≤ ρ),
    integral_abs_rpow_symm hh hρ0, hexp]
  ring

end SingularLearningTheory
