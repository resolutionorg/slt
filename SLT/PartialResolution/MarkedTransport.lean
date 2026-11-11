/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# Marked scalings and marked shears

The chart-box forms of the blow-up primitives: a marked scalar coordinate scales a marked block
(`markedScale`, with the monomial density `markedDensity`), and a marked target block absorbs a
function of the other coordinates (`markedShear`). Each comes with a measure-preserving split of
the coordinate space built from the markings (`markScaleSplit`, `shearSplit`), with subtype
complements rather than `Fin`-arithmetic enumeration. The standard blow-up chart is a marked
scaling (`StandardCharts`, `blowUpChart_eq_markedScale`); the marked shear is used by
`PrimitiveInjective`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace Analytic

variable {d n : ℕ}

/-- The spectator coordinates of a marked scaling. -/
abbrev MarkCompl (u : Fin d) (b : Fin n ↪ Fin d) : Type :=
  {j : Fin d // j ≠ u ∧ ∀ i, b i ≠ j}

/-- The index split of a marked scaling: pivot, block, spectators. -/
noncomputable def markIndexEquiv (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) :
    Fin d ≃ (Unit ⊕ Fin n) ⊕ MarkCompl u b where
  toFun j :=
    if h : j = u then .inl (.inl ())
    else if h' : ∃ i, b i = j then .inl (.inr h'.choose)
    else .inr ⟨j, h, fun i hi => h' ⟨i, hi⟩⟩
  invFun
    | .inl (.inl _) => u
    | .inl (.inr i) => b i
    | .inr s => s.1
  left_inv j := by
    by_cases h : j = u
    · simp [h]
    · by_cases h' : ∃ i, b i = j
      · simp only [dite_eq_right h, dite_eq_left h']
        exact h'.choose_spec
      · simp [dite_eq_right h, dite_eq_right h']
  right_inv p := by
    rcases p with (_ | i) | s
    · simp
    · have hbi : ∃ i', b i' = b i := ⟨i, rfl⟩
      simp only [dite_eq_right (hbu i), dite_eq_left hbi]
      exact congrArg (Sum.inl ∘ Sum.inr) (b.injective hbi.choose_spec)
    · simp only [dite_eq_right s.2.1, dite_eq_right (fun h' : ∃ i, b i = s.1 =>
        s.2.2 h'.choose h'.choose_spec)]

/-- The split of the coordinate space induced by a marked scaling. -/
noncomputable def markScaleSplit (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) :
    (Fin d → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) × (MarkCompl u b → ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ => ℝ)
      (markIndexEquiv u b hbu).symm).symm).trans <|
    (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).trans <|
      MeasurableEquiv.prodCongr
        ((MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ).trans
          (MeasurableEquiv.prodCongr
            (MeasurableEquiv.funUnique Unit ℝ)
            (MeasurableEquiv.refl _)))
        (MeasurableEquiv.refl _)

theorem measurePreserving_markScaleSplit (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) :
    MeasurePreserving (markScaleSplit u b hbu) volume volume := by
  have h1 : MeasurePreserving
      (⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin d => ℝ)
        (markIndexEquiv u b hbu).symm).symm) volume volume :=
    (MeasureTheory.volume_measurePreserving_piCongrLeft _ _).symm _
  have h2 : MeasurePreserving
      (⇑(MeasurableEquiv.sumPiEquivProdPi
        (fun _ : (Unit ⊕ Fin n) ⊕ MarkCompl u b => ℝ)))
      volume volume :=
    MeasureTheory.volume_measurePreserving_sumPiEquivProdPi _
  have h3 : MeasurePreserving
      (⇑(MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Fin n => ℝ)))
      volume volume :=
    MeasureTheory.volume_measurePreserving_sumPiEquivProdPi _
  have h4 : MeasurePreserving (⇑(MeasurableEquiv.funUnique Unit ℝ))
      volume volume :=
    measurePreserving_funUnique volume Unit
  have h5 : MeasurePreserving
      (⇑(MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
        (MeasurableEquiv.refl (Fin n → ℝ)))) volume volume :=
    h4.prod (MeasurePreserving.id _)
  have h6 : MeasurePreserving
      (⇑(MeasurableEquiv.prodCongr
        ((MeasurableEquiv.sumPiEquivProdPi (fun _ : Unit ⊕ Fin n => ℝ)).trans
          (MeasurableEquiv.prodCongr (MeasurableEquiv.funUnique Unit ℝ)
            (MeasurableEquiv.refl _)))
        (MeasurableEquiv.refl (MarkCompl u b → ℝ)))) volume volume :=
    (h5.comp h3).prod (MeasurePreserving.id _)
  exact (h6.comp h2).comp h1

@[simp] theorem markIndexEquiv_pivot (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) :
    markIndexEquiv u b hbu u = .inl (.inl ()) := by
  simp [markIndexEquiv]

@[simp] theorem markIndexEquiv_block (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) (i : Fin n) :
    markIndexEquiv u b hbu (b i) = .inl (.inr i) := by
  have hbi : ∃ i', b i' = b i := ⟨i, rfl⟩
  simp only [markIndexEquiv, Equiv.coe_fn_mk, dite_eq_right (hbu i), dite_eq_left hbi]
  exact congrArg (Sum.inl ∘ Sum.inr) (b.injective hbi.choose_spec)

@[simp] theorem markIndexEquiv_spec (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) (s : MarkCompl u b) :
    markIndexEquiv u b hbu s.1 = .inr s := by
  simp only [markIndexEquiv, Equiv.coe_fn_mk, dite_eq_right s.2.1,
    dite_eq_right (fun h' : ∃ i, b i = s.1 => s.2.2 h'.choose h'.choose_spec)]

@[simp] theorem markScaleSplit_pivot (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) (x : Fin d → ℝ) :
    (markScaleSplit u b hbu x).1.1 = x u := rfl

@[simp] theorem markScaleSplit_block (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) (x : Fin d → ℝ) (i : Fin n) :
    (markScaleSplit u b hbu x).1.2 i = x (b i) := rfl

@[simp] theorem markScaleSplit_spec (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) (x : Fin d → ℝ) (s : MarkCompl u b) :
    (markScaleSplit u b hbu x).2 s = x s.1 := rfl

theorem markScaleSplit_symm_pivot (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u)
    (p : (ℝ × (Fin n → ℝ)) × (MarkCompl u b → ℝ)) :
    (markScaleSplit u b hbu).symm p u = p.1.1 := by
  conv_rhs => rw [← (markScaleSplit u b hbu).apply_symm_apply p]
  rfl

theorem markScaleSplit_symm_block (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u)
    (p : (ℝ × (Fin n → ℝ)) × (MarkCompl u b → ℝ)) (i : Fin n) :
    (markScaleSplit u b hbu).symm p (b i) = p.1.2 i := by
  conv_rhs => rw [← (markScaleSplit u b hbu).apply_symm_apply p]
  rfl

theorem markScaleSplit_symm_spec (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u)
    (p : (ℝ × (Fin n → ℝ)) × (MarkCompl u b → ℝ)) (s : MarkCompl u b) :
    (markScaleSplit u b hbu).symm p s.1 = p.2 s := by
  conv_rhs => rw [← (markScaleSplit u b hbu).apply_symm_apply p]
  rfl

/-- The marked scaling: the pivot coordinate scales the marked block,
all other coordinates unchanged. -/
noncomputable def markedScale (u : Fin d) (b : Fin n ↪ Fin d) :
    (Fin d → ℝ) → (Fin d → ℝ) := by
  classical
  exact fun x j => if ∃ i, b i = j then x u * x j else x j

/-- The marked density. -/
noncomputable def markedDensity (u : Fin d) (n : ℕ) :
    (Fin d → ℝ) → ℝ≥0∞ :=
  fun x => ENNReal.ofReal (|x u| ^ n)

@[simp] theorem markedScale_apply_mem (u : Fin d) (b : Fin n ↪ Fin d)
    (x : Fin d → ℝ) (i : Fin n) :
    markedScale u b x (b i) = x u * x (b i) := by
  rw [markedScale, ite_eq_left ⟨i, rfl⟩]

theorem markedScale_apply_not_mem (u : Fin d) (b : Fin n ↪ Fin d)
    (x : Fin d → ℝ) {j : Fin d} (hj : ∀ i, b i ≠ j) :
    markedScale u b x j = x j := by
  rw [markedScale, ite_eq_right fun h : ∃ i, b i = j => hj h.choose h.choose_spec]

/-! ## The marked shear -/

/-- The non-target coordinates of a marked shear. -/
abbrev TargetCompl (b : Fin n ↪ Fin d) : Type :=
  {j : Fin d // ∀ i, b i ≠ j}

/-- The index split of a marked shear: non-targets, then targets. -/
noncomputable def shearIndexEquiv (b : Fin n ↪ Fin d) :
    Fin d ≃ TargetCompl b ⊕ Fin n where
  toFun j :=
    if h' : ∃ i, b i = j then .inr h'.choose
    else .inl ⟨j, fun i hi => h' ⟨i, hi⟩⟩
  invFun
    | .inl s => s.1
    | .inr i => b i
  left_inv j := by
    by_cases h' : ∃ i, b i = j
    · simp only [dite_eq_left h']
      exact h'.choose_spec
    · simp [dite_eq_right h']
  right_inv p := by
    rcases p with s | i
    · simp only [dite_eq_right (fun h' : ∃ i, b i = s.1 =>
        s.2 h'.choose h'.choose_spec)]
    · have hbi : ∃ i', b i' = b i := ⟨i, rfl⟩
      simp only [dite_eq_left hbi]
      exact congrArg Sum.inr (b.injective hbi.choose_spec)

/-- The split of the coordinate space induced by a marked shear. -/
noncomputable def shearSplit (b : Fin n ↪ Fin d) :
    (Fin d → ℝ) ≃ᵐ (TargetCompl b → ℝ) × (Fin n → ℝ) :=
  ((MeasurableEquiv.piCongrLeft (fun _ => ℝ)
      (shearIndexEquiv b).symm).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ => ℝ)

theorem measurePreserving_shearSplit (b : Fin n ↪ Fin d) :
    MeasurePreserving (shearSplit b) volume volume :=
  (MeasureTheory.volume_measurePreserving_sumPiEquivProdPi _).comp
    ((MeasureTheory.volume_measurePreserving_piCongrLeft _ _).symm _)

@[simp] theorem shearSplit_compl (b : Fin n ↪ Fin d) (x : Fin d → ℝ)
    (s : TargetCompl b) : (shearSplit b x).1 s = x s.1 := rfl

@[simp] theorem shearSplit_target (b : Fin n ↪ Fin d) (x : Fin d → ℝ)
    (i : Fin n) : (shearSplit b x).2 i = x (b i) := rfl

theorem shearSplit_symm_compl (b : Fin n ↪ Fin d)
    (p : (TargetCompl b → ℝ) × (Fin n → ℝ)) (s : TargetCompl b) :
    (shearSplit b).symm p s.1 = p.1 s := by
  conv_rhs => rw [← (shearSplit b).apply_symm_apply p]
  rfl

theorem shearSplit_symm_target (b : Fin n ↪ Fin d)
    (p : (TargetCompl b → ℝ) × (Fin n → ℝ)) (i : Fin n) :
    (shearSplit b).symm p (b i) = p.2 i := by
  conv_rhs => rw [← (shearSplit b).apply_symm_apply p]
  rfl

/-- The marked shear: the targets absorb a function of the
non-targets. -/
noncomputable def markedShear (b : Fin n ↪ Fin d)
    (c : (TargetCompl b → ℝ) → Fin n → ℝ) :
    (Fin d → ℝ) → (Fin d → ℝ) := by
  classical
  exact fun x j =>
    if h' : ∃ i, b i = j then x j + c (fun s => x s.1) h'.choose else x j

@[simp] theorem markedShear_apply_mem (b : Fin n ↪ Fin d)
    (c : (TargetCompl b → ℝ) → Fin n → ℝ) (x : Fin d → ℝ) (i : Fin n) :
    markedShear b c x (b i) = x (b i) + c (fun s => x s.1) i := by
  have hbi : ∃ i', b i' = b i := ⟨i, rfl⟩
  rw [markedShear, dite_eq_left hbi, b.injective hbi.choose_spec]

theorem markedShear_apply_not_mem (b : Fin n ↪ Fin d)
    (c : (TargetCompl b → ℝ) → Fin n → ℝ) (x : Fin d → ℝ) {j : Fin d}
    (hj : ∀ i, b i ≠ j) :
    markedShear b c x j = x j := by
  rw [markedShear,
    dite_eq_right fun h : ∃ i, b i = j => hj h.choose h.choose_spec]

end Analytic
