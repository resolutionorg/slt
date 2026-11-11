/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Bounded-unit density congruence

Volume-scaling exponents are blind to bounded positive density factors: if `c * w ≤ jac ≤ C * w`
on `K` (`0 < c`), the `withDensity`-weighted sublevel volumes under `jac` and `w` are two-sidedly
comparable, so `HasLLCExponentsOn` holds for one weight iff it holds for the other — and an
eventually-vanishing sublevel volume transfers likewise. This is the bridge between a read-off
stated under a monomial weight and a transport stated under the full Jacobian density
(`jacAbs = |unit| * monomial`); the chart-local read-off (`ChartLocal`) uses it.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Filter Set Asymptotics ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}
variable {K : Set α} {f w jac : α → ℝ} {c C : ℝ}

/-- The one-sided density bound on subsets of `K`: a pointwise factor
bound transfers to the weighted measures. -/
theorem _root_.withDensity_le_mul_of_le_mul
    (hw : Measurable fun x => ENNReal.ofReal (w x))
    (hC : 0 ≤ C) (hle : ∀ x ∈ K, jac x ≤ C * w x)
    {S : Set α} (hS : MeasurableSet S) (hSK : S ⊆ K) :
    (μ.withDensity fun x => ENNReal.ofReal (jac x)) S
      ≤ ENNReal.ofReal C *
        (μ.withDensity fun x => ENNReal.ofReal (w x)) S := by
  rw [withDensity_apply _ hS, withDensity_apply _ hS,
    ← lintegral_const_mul _ hw]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem hS] with x hx
  calc ENNReal.ofReal (jac x)
      ≤ ENNReal.ofReal (C * w x) :=
        ENNReal.ofReal_le_ofReal (hle x (hSK hx))
    _ = ENNReal.ofReal C * ENNReal.ofReal (w x) :=
        ENNReal.ofReal_mul hC

section Congruence

variable (hK : MeasurableSet K) (hf : Measurable f)
  (hw : Measurable fun x => ENNReal.ofReal (w x))
  (hjac : Measurable fun x => ENNReal.ofReal (jac x))
  (hc : 0 < c) (hC : 0 ≤ C)
  (hge : ∀ x ∈ K, c * w x ≤ jac x)
  (hle : ∀ x ∈ K, jac x ≤ C * w x)
  (hfin : (μ.withDensity fun x => ENNReal.ofReal (w x)) K ≠ ∞)

include hK hf hw hC hle hfin in
/-- The sublevel-volume upper comparison at every threshold. -/
theorem sublevelVol_withDensity_le (ε : ℝ) :
    sublevelVol (μ.withDensity fun x => ENNReal.ofReal (jac x))
        K f ε
      ≤ C * sublevelVol (μ.withDensity fun x => ENNReal.ofReal (w x))
        K f ε := by
  set S := K ∩ {x | f x ≤ ε} with hSdef
  have hS : MeasurableSet S :=
    hK.inter (measurableSet_le hf measurable_const)
  have hSK : S ⊆ K := inter_subset_left
  have hbound := withDensity_le_mul_of_le_mul (μ := μ) hw hC hle hS hSK
  have hwfin : (μ.withDensity fun x => ENNReal.ofReal (w x)) S ≠ ∞ :=
    fun hcon => hfin (eq_top_mono (measure_mono hSK) hcon)
  have hjfin : (μ.withDensity fun x => ENNReal.ofReal (jac x)) S
      ≠ ∞ := by
    intro hcon
    rw [hcon] at hbound
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwfin)
      (top_le_iff.mp hbound)
  rw [sublevelVol, sublevelVol, ← hSdef]
  calc ((μ.withDensity fun x => ENNReal.ofReal (jac x)) S).toReal
      ≤ (ENNReal.ofReal C *
          (μ.withDensity fun x => ENNReal.ofReal (w x)) S).toReal :=
        ENNReal.toReal_mono
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwfin) hbound
    _ = C * ((μ.withDensity fun x =>
          ENNReal.ofReal (w x)) S).toReal := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]

include hK hf hw hjac hc hC hge hle hfin in
/-- The reverse comparison: the unit's lower bound caps the
monomial-weighted volume by the Jacobian-weighted one. -/
theorem sublevelVol_withDensity_ge (ε : ℝ) :
    sublevelVol (μ.withDensity fun x => ENNReal.ofReal (w x)) K f ε
      ≤ c⁻¹ *
        sublevelVol (μ.withDensity fun x => ENNReal.ofReal (jac x))
          K f ε := by
  -- the roles swap: `w ≤ c⁻¹ * jac` on `K`
  have hle' : ∀ x ∈ K, w x ≤ c⁻¹ * jac x := fun x hx => by
    have h := hge x hx
    rw [inv_mul_eq_div, le_div_iff₀ hc, mul_comm]
    exact h
  have hjacfin : (μ.withDensity fun x => ENNReal.ofReal (jac x)) K
      ≠ ∞ := by
    intro hcon
    have hbound := withDensity_le_mul_of_le_mul (μ := μ) hw hC hle
      hK subset_rfl
    rw [hcon] at hbound
    exact (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin)
      (top_le_iff.mp hbound)
  exact sublevelVol_withDensity_le hK hf hjac
    (inv_nonneg.mpr hc.le) hle' hjacfin ε

include hK hf hw hjac hc hC hge hle hfin in
/-- The two weighted sublevel volumes are `Θ`-equivalent. -/
theorem sublevelVol_withDensity_isTheta :
    (sublevelVol (μ.withDensity fun x => ENNReal.ofReal (jac x))
        K f)
      =Θ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (sublevelVol (μ.withDensity fun x => ENNReal.ofReal (w x))
        K f) := by
  constructor
  · refine IsBigO.of_bound C (Eventually.of_forall fun ε => ?_)
    rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
      Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
    exact sublevelVol_withDensity_le hK hf hw hC hle hfin ε
  · refine IsBigO.of_bound c⁻¹ (Eventually.of_forall fun ε => ?_)
    rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
      Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
    exact sublevelVol_withDensity_ge hK hf hw hjac hc hC hge hle
      hfin ε

include hK hf hw hjac hc hC hge hle hfin in
/-- **The bounded-unit congruence**: volume-scaling exponents do not
see bounded positive density factors. -/
theorem hasLLCExponentsOn_withDensity_congr {lam theta : ℝ} :
    HasLLCExponentsOn
        (μ.withDensity fun x => ENNReal.ofReal (jac x)) K f lam theta
      ↔ HasLLCExponentsOn
        (μ.withDensity fun x => ENNReal.ofReal (w x)) K f lam theta := by
  have hth := sublevelVol_withDensity_isTheta hK hf hw hjac hc hC
    hge hle hfin
  exact ⟨fun h => hth.symm.trans h, fun h => hth.trans h⟩

include hK hf hw hC hle hfin in
/-- The eventually-zero analogue: a vanishing monomial-weighted
sublevel volume vanishes under the Jacobian weight too. -/
theorem sublevelVol_withDensity_eq_zero {ε : ℝ}
    (h0 : sublevelVol (μ.withDensity fun x => ENNReal.ofReal (w x))
      K f ε = 0) :
    sublevelVol (μ.withDensity fun x => ENNReal.ofReal (jac x))
      K f ε = 0 := by
  have hle' := sublevelVol_withDensity_le hK hf hw hC hle hfin ε
  rw [h0, mul_zero] at hle'
  exact le_antisymm hle' (sublevelVol_nonneg _ _ _ _)

end Congruence

end SingularLearningTheory
