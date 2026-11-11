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
import SLT.VolumeScaling.StrictFamily
import SLT.VolumeScaling.Transport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# The weighted monomial read-off on `Fin n`

The public form of the weighted-monomial exponent computation: on the unit cube,
`∏ᵢ |xᵢ|^{2kᵢ}` under the weights `|xᵢ|^{hᵢ}` has `λ = minᵢ (hᵢ+1)/(2kᵢ)` and `θ = #argmin` — by
transporting the split theorem of `StrictFamily` along the subtype-split and enumeration
equivalences. The minimum is carried abstractly (`λ ≤ λᵢ` everywhere, attained somewhere), which
is the shape the chart read-offs use; `CubeRescale` extends it to cubes of any radius.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

/-- **The weighted monomial read-off**: the weighted monomial on the unit
cube has the minimal coordinate exponent as `λ` and the number of
attaining coordinates as `θ`. -/
theorem hasLLCExponentsOn_weighted_monomial {n : ℕ}
    (k : Fin n → ℕ) (h : Fin n → ℝ) (hk : ∀ i, 0 < k i)
    (hh : ∀ i, 0 ≤ h i) {lam : ℝ}
    (hmin : ∀ i, lam ≤ (h i + 1) / (2 * k i : ℝ))
    (hatt : ∃ i, (h i + 1) / (2 * k i : ℝ) = lam) :
    HasLLCExponentsOn
      (Measure.pi fun i => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i))
      (Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1)
      (fun x => ∏ i, |x i| ^ (2 * k i : ℝ))
      lam ((Finset.univ.filter
        fun i => (h i + 1) / (2 * k i : ℝ) = lam).card) := by
  classical
  set p : Fin n → Prop := fun i => (h i + 1) / (2 * k i : ℝ) ≠ lam
    with hpdef
  -- the attaining block is nonempty
  obtain ⟨i₀, hi₀⟩ := hatt
  have hlam : 0 < lam := by
    rw [← hi₀]
    exact div_pos (by linarith [hh i₀]) (by have := hk i₀; positivity)
  have hne : Nonempty {i // ¬ p i} := ⟨⟨i₀, not_not.mpr hi₀⟩⟩
  set na := Fintype.card {i // ¬ p i} with hnadef
  have hna : 1 ≤ na := Fintype.card_pos
  obtain ⟨m, hm⟩ : ∃ m, na = m + 1 :=
    ⟨na - 1, (Nat.succ_pred_eq_of_pos hna).symm⟩
  set ns := Fintype.card {i // p i}
  -- the enumerations
  set eS : Fin ns ≃ {i // p i} := (Fintype.equivFin _).symm
  set eA : Fin (m + 1) ≃ {i // ¬ p i} :=
    (finCongr hm.symm).trans (Fintype.equivFin _).symm
  -- the split theorem on the enumerated blocks
  have hsplit := hasLLCExponentsOn_split
    (m := m) (n := ns)
    (ke := fun i => k (eA i)) (he := fun i => h (eA i))
    (ps := fun j => (2 * k (eS j) : ℝ)) (hs := fun j => h (eS j))
    (fun i => hk _) (fun i => hh _)
    (fun i => not_not.mp (eA i).2)
    (fun j => by have := hk (eS j); positivity) (fun j => hh _)
    (fun j => lt_of_le_of_ne (hmin _) (Ne.symm ((eS j).2)))
  -- the transport chain
  have hT1 := measurePreserving_piEquivPiSubtypeProd
    (μ := fun i : Fin n => volume.withDensity
      fun x => ENNReal.ofReal (|x| ^ h i)) p
  have hT2 := (measurePreserving_piCongrLeft
    (fun i : {i // p i} => volume.withDensity
      fun x => ENNReal.ofReal (|x| ^ h i)) eS).symm
    (MeasurableEquiv.piCongrLeft _ eS)
  have hT3 := (measurePreserving_piCongrLeft
    (fun i : {i // ¬ p i} => volume.withDensity
      fun x => ENNReal.ofReal (|x| ^ h i)) eA).symm
    (MeasurableEquiv.piCongrLeft _ eA)
  set T : (Fin n → ℝ) ≃ᵐ ((Fin ns → ℝ) × (Fin (m + 1) → ℝ)) :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p).trans
      (((MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ)
        eS).symm).prodCongr
       ((MeasurableEquiv.piCongrLeft (fun _ : {i // ¬ p i} => ℝ)
        eA).symm))
  have hTmp : MeasurePreserving (⇑T)
      (Measure.pi fun i => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i))
      ((Measure.pi fun j : Fin ns => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h (eS j))).prod
       (Measure.pi fun i : Fin (m + 1) => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h (eA i)))) := by
    exact (hT2.prod hT3).comp hT1
  -- transport the split theorem back
  have htrans := MeasurePreserving.hasLLCExponentsOn_comp
    (K' := (Set.univ.pi fun _ : Fin ns => Icc (-1 : ℝ) 1) ×ˢ
      Set.univ.pi fun _ : Fin (m + 1) => Icc (-1 : ℝ) 1)
    (g := fun z => (∏ j, |z.1 j| ^ (2 * k (eS j) : ℝ))
      * ∏ i, |z.2 i| ^ (2 * k (eA i) : ℝ))
    (lam := lam) (theta := (m + 1 : ℝ)) T hTmp
  -- identify the set
  have hset : ⇑T ⁻¹' ((Set.univ.pi fun _ : Fin ns => Icc (-1 : ℝ) 1) ×ˢ
      Set.univ.pi fun _ : Fin (m + 1) => Icc (-1 : ℝ) 1)
      = Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1 := by
    ext x
    have hTx : T x = (fun j => x (eS j), fun i => x (eA i)) := rfl
    simp only [mem_preimage, hTx, mem_prod, Set.mem_univ_pi]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hpi : p i
      · have := h1 (eS.symm ⟨i, hpi⟩)
        rwa [Equiv.apply_symm_apply] at this
      · have := h2 (eA.symm ⟨i, hpi⟩)
        rwa [Equiv.apply_symm_apply] at this
    · intro hx
      exact ⟨fun j => hx _, fun i => hx _⟩
  -- identify the function
  have hfun : (fun x : Fin n → ℝ =>
      (∏ j, |(T x).1 j| ^ (2 * k (eS j) : ℝ))
        * ∏ i, |(T x).2 i| ^ (2 * k (eA i) : ℝ))
      = fun x => ∏ i, |x i| ^ (2 * k i : ℝ) := by
    funext x
    have hTx : T x = (fun j => x (eS j), fun i => x (eA i)) := rfl
    rw [hTx]
    change (∏ j, |x (eS j)| ^ (2 * k (eS j) : ℝ))
        * (∏ i, |x (eA i)| ^ (2 * k (eA i) : ℝ))
      = ∏ i, |x i| ^ (2 * k i : ℝ)
    rw [Equiv.prod_comp eS
        (fun i : {i // p i} => |x i| ^ (2 * k i : ℝ)),
      Equiv.prod_comp eA
        (fun i : {i // ¬ p i} => |x i| ^ (2 * k i : ℝ)),
      Fintype.prod_subtype_mul_prod_subtype p
        (fun i => |x i| ^ (2 * k i : ℝ))]
  -- the order is the attaining count
  have hcard : ((Finset.univ.filter
      fun i => (h i + 1) / (2 * k i : ℝ) = lam).card : ℝ)
      = (m + 1 : ℝ) := by
    have h1 : (Finset.univ.filter
        fun i => (h i + 1) / (2 * k i : ℝ) = lam)
        = Finset.univ.filter fun i => ¬ p i := by
      refine Finset.filter_congr fun i _ => ?_
      rw [hpdef]
      simp
    rw [h1, ← Fintype.card_subtype, ← hnadef, hm]
    push_cast
    ring
  rw [hcard]
  simpa only [hset, hfun] using htrans.mpr hsplit

end SingularLearningTheory
