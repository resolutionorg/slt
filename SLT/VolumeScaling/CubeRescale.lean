/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
import SLT.VolumeScaling.BlowUpSubstitution
import SLT.VolumeScaling.FiberIdentity
import SLT.VolumeScaling.Invariance
import SLT.VolumeScaling.MonomialReadOff
import SLT.VolumeScaling.Transport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Positivity.Finset

/-!
# The cube rescaling

The weighted monomial read-off (`MonomialReadOff`) transfers from the unit cube to `[-R,R]^n`
with exponents unchanged: the weighted measure is scaling-covariant with the explicit constant
`R^{h+1}` per coordinate, and the monomial picks up the constant `R^{2Σk}`, which the
bounded-unit comparison absorbs. This completes the monomial-volume computations on cubes of
every radius.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

/-- The weighted line measure is scaling-covariant with explicit
constant: pushing forward along `x ↦ R·x` multiplies it by
`R^{-(h+1)}`. -/
theorem _root_.map_mul_left_weighted {R h : ℝ} (hR : 0 < R) (_hh : 0 ≤ h) :
    Measure.map (R * ·)
      (volume.withDensity fun u => ENNReal.ofReal (|u| ^ h))
    = ENNReal.ofReal (R ^ (-(h + 1)))
      • (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h)) := by
  have hgw : (fun u : ℝ => ENNReal.ofReal (|u| ^ h))
      = (fun x : ℝ => ENNReal.ofReal (R ^ (-h)) *
          ENNReal.ofReal (|x| ^ h)) ∘ (R * ·) := by
    funext u
    change ENNReal.ofReal (|u| ^ h)
      = ENNReal.ofReal (R ^ (-h)) * ENNReal.ofReal (|R * u| ^ h)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _), abs_mul,
      abs_of_pos hR, Real.mul_rpow hR.le (abs_nonneg u), ← mul_assoc,
      ← Real.rpow_add hR, neg_add_cancel, Real.rpow_zero, one_mul]
  have hmeas : Measurable fun x : ℝ =>
      ENNReal.ofReal (R ^ (-h)) * ENNReal.ofReal (|x| ^ h) := by
    fun_prop
  have hofm : Measurable fun x : ℝ => ENNReal.ofReal (|x| ^ h) := by
    fun_prop
  rw [hgw, SLT.MeasureTheory.Measure.map_withDensity_comp volume (measurable_const_mul R) hmeas,
    Real.map_volume_mul_left hR.ne',
    show (fun x : ℝ => ENNReal.ofReal (R ^ (-h)) *
        ENNReal.ofReal (|x| ^ h))
      = ENNReal.ofReal (R ^ (-h)) •
        fun x : ℝ => ENNReal.ofReal (|x| ^ h) from rfl,
    withDensity_smul_measure, withDensity_smul _ hofm, smul_smul]
  have hconst : ENNReal.ofReal |R⁻¹| * ENNReal.ofReal (R ^ (-h))
      = ENNReal.ofReal (R ^ (-(h + 1))) := by
    rw [abs_inv, abs_of_pos hR, ← Real.rpow_neg_one R,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hR.le _),
      ← Real.rpow_add hR, show (-1 : ℝ) + -h = -(h + 1) by ring]
  have hgw' : ((ENNReal.ofReal (R ^ (-h)) • fun x : ℝ =>
      ENNReal.ofReal (|x| ^ h)) ∘ fun x : ℝ => R * x)
      = fun u : ℝ => ENNReal.ofReal (|u| ^ h) := hgw.symm
  rw [hconst, hgw']

/-- A finite multiple of a σ-finite measure is σ-finite. -/
theorem _root_.MeasureTheory.Measure.sigmaFinite_smul {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SigmaFinite μ] {c : ℝ≥0∞} (hc : c ≠ ⊤) :
    SigmaFinite (c • μ) := by
  refine ⟨⟨⟨fun m => spanningSets μ m, fun _ => trivial, fun m => ?_,
    iUnion_spanningSets μ⟩⟩⟩
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc)
    (measure_spanningSets_lt_top μ m)

/-- **The rescaled weighted monomial read-off**: the weighted monomial on
`[-R,R]^n` has the same exponents as on the unit cube. -/
theorem hasLLCExponentsOn_weighted_monomial_rescaled {n : ℕ}
    (k : Fin n → ℕ) (h : Fin n → ℝ) (hk : ∀ i, 0 < k i)
    (hh : ∀ i, 0 ≤ h i) {lam : ℝ}
    (hmin : ∀ i, lam ≤ (h i + 1) / (2 * k i : ℝ))
    (hatt : ∃ i, (h i + 1) / (2 * k i : ℝ) = lam)
    {R : ℝ} (hR : 0 < R) :
    HasLLCExponentsOn
      (Measure.pi fun i => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i))
      (Set.univ.pi fun _ : Fin n => Icc (-R) R)
      (fun x => ∏ i, |x i| ^ (2 * k i : ℝ))
      lam ((Finset.univ.filter
        fun i => (h i + 1) / (2 * k i : ℝ) = lam).card) := by
  classical
  set cs : Fin n → ℝ≥0∞ := fun i => ENNReal.ofReal (R ^ (-(h i + 1)))
  have h1d : ∀ i : Fin n, MeasurePreserving (R * ·)
      (volume.withDensity fun u => ENNReal.ofReal (|u| ^ h i))
      (cs i • volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i)) :=
    fun i => ⟨measurable_const_mul R, map_mul_left_weighted hR (hh i)⟩
  have : ∀ i : Fin n, SigmaFinite (cs i • volume.withDensity
      fun x : ℝ => ENNReal.ofReal (|x| ^ h i)) := fun i =>
    MeasureTheory.Measure.sigmaFinite_smul _ ENNReal.ofReal_ne_top
  have hmp : MeasurePreserving (fun (x : Fin n → ℝ) i => R * x i)
      (Measure.pi fun i => volume.withDensity
        fun u => ENNReal.ofReal (|u| ^ h i))
      (Measure.pi fun i => cs i • volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i)) :=
    measurePreserving_pi _ _ h1d
  have hpismul : (Measure.pi fun i => cs i • volume.withDensity
      fun x : ℝ => ENNReal.ofReal (|x| ^ h i))
      = (∏ i, cs i) • Measure.pi fun i => volume.withDensity
        fun x : ℝ => ENNReal.ofReal (|x| ^ h i) := by
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul,
      ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => rfl
  set T : (Fin n → ℝ) ≃ᵐ (Fin n → ℝ) :=
    MeasurableEquiv.piCongrRight fun _ =>
      (Homeomorph.mulLeft₀ R hR.ne').toMeasurableEquiv
  have hmap : Measure.map (⇑T)
      (Measure.pi fun i => volume.withDensity
        fun u => ENNReal.ofReal (|u| ^ h i))
      = (∏ i, cs i) • Measure.pi fun i => volume.withDensity
        fun x : ℝ => ENNReal.ofReal (|x| ^ h i) := by
    rw [show ⇑T = fun (x : Fin n → ℝ) i => R * x i from rfl,
      hmp.map_eq, hpismul]
  have hc0 : (∏ i, cs i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ =>
      (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hR _)).ne'
  have hctop : (∏ i, cs i) ≠ ⊤ :=
    (ENNReal.prod_lt_top fun i _ => ENNReal.ofReal_lt_top).ne
  have htrans := hasLLCExponentsOn_comp_smul_measurableEquiv
    (K' := Set.univ.pi fun _ : Fin n => Icc (-R) R)
    (g := fun x => ∏ i, |x i| ^ (2 * k i : ℝ))
    (lam := lam) (theta := ((Finset.univ.filter
      fun i => (h i + 1) / (2 * k i : ℝ) = lam).card : ℝ))
    T hc0 hctop hmap
  have hset : ⇑T ⁻¹' (Set.univ.pi fun _ : Fin n => Icc (-R) R)
      = Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1 := by
    ext x
    have hTx : T x = fun i => R * x i := rfl
    simp only [mem_preimage, hTx, Set.mem_univ_pi, mem_Icc]
    refine forall_congr' fun i => ?_
    rw [show (-R : ℝ) = R * (-1) by ring,
      show (R * x i ≤ R) = (R * x i ≤ R * 1) by rw [mul_one],
      mul_le_mul_iff_of_pos_left hR, mul_le_mul_iff_of_pos_left hR]
  have hFT : (fun x : Fin n → ℝ =>
      (fun y : Fin n → ℝ => ∏ i, |y i| ^ (2 * k i : ℝ)) (T x))
      = fun x => (∏ i, R ^ (2 * k i : ℝ))
          * ∏ i, |x i| ^ (2 * k i : ℝ) := by
    funext x
    have hTx : T x = fun i => R * x i := rfl
    rw [hTx]
    change (∏ i, |R * x i| ^ (2 * k i : ℝ)) = _
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [abs_mul, abs_of_pos hR,
      Real.mul_rpow hR.le (abs_nonneg _)]
  have hbase := hasLLCExponentsOn_weighted_monomial k h hk hh
    hmin hatt
  have hCpos : 0 < ∏ i, R ^ (2 * k i : ℝ) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos hR _
  have hKfin : (Measure.pi fun i => volume.withDensity
      fun x : ℝ => ENNReal.ofReal (|x| ^ h i))
      (Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ≠ ⊤ := by
    rw [Measure.pi_pi]
    refine (ENNReal.prod_lt_top fun i _ => ?_).ne
    rw [weighted_Icc_mass (hh i)]
    exact ENNReal.ofReal_lt_top
  have habsorb := HasLLCExponentsOn.of_bounded_unit hKfin hbase
    hCpos hCpos
    (fun x _ => le_of_eq rfl)
    (fun x _ => le_of_eq rfl)
  rw [hset, hFT] at htrans
  exact htrans.mp habsorb

end SingularLearningTheory
