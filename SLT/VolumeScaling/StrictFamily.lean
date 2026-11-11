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
import SLT.VolumeScaling.FiberIdentity
import SLT.VolumeScaling.SignedPower
import SLT.VolumeScaling.StrictPeel
import SLT.VolumeScaling.Transport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Positivity.Finset

/-!
# Folding strict peels: the family lemma

Multiplying an abstract `[0,1]`-valued factor of exponents `(λ, θ)` by a *finite family* of
strict weighted coordinates (each `(hⱼ+1)/pⱼ > λ`) preserves `(λ, θ)`: induction on the family,
peeling one coordinate per step through the `piFinSuccAbove` reshuffle and the single-coordinate
strict peel (`StrictPeel`). The split theorem `hasLLCExponentsOn_split` instantiates the abstract
factor with the equal-exponent block (`SignedPower`); `MonomialReadOff` transports it to the
general weighted monomial.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

variable {γ : Type*} [MeasurableSpace γ] {ν : Measure γ} {K : Set γ}

/-- **The strict family peel**: a finite family of strict weighted
coordinates (each `(hⱼ+1)/pⱼ > λ`) multiplies onto an abstract
`[0,1]`-valued factor of exponents `(λ, θ)` without changing them. -/
theorem hasLLCExponentsOn_mul_strict_family [SFinite ν]
    (hK : MeasurableSet K) {g : γ → ℝ} (hgm : Measurable g)
    (hg0 : ∀ y ∈ K, 0 ≤ g y) (hg1 : ∀ y ∈ K, g y ≤ 1)
    {lam theta : ℝ} (hlam : 0 < lam) (htheta : 1 ≤ theta)
    (hνK : ν K ≠ ⊤) (hg : HasLLCExponentsOn ν K g lam theta)
    {n : ℕ} (p h : Fin n → ℝ) (hp : ∀ j, 0 < p j)
    (hh : ∀ j, 0 ≤ h j) (hstrict : ∀ j, lam < (h j + 1) / p j) :
    HasLLCExponentsOn
      ((Measure.pi fun j => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h j)).prod ν)
      ((Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ×ˢ K)
      (fun z => (∏ j, |z.1 j| ^ p j) * g z.2) lam theta := by
  induction n with
  | zero =>
    have hfm : Measurable fun z : (Fin 0 → ℝ) × γ =>
        (∏ j, |z.1 j| ^ p j) * g z.2 := by
      have h1 : (fun z : (Fin 0 → ℝ) × γ =>
          (∏ j, |z.1 j| ^ p j) * g z.2)
          = fun z => g z.2 := by
        funext z
        rw [show (∏ j, |z.1 j| ^ p j) = 1 from Finset.prod_of_isEmpty _,
          one_mul]
      rw [h1]
      exact hgm.comp measurable_snd
    have hVeq : ∀ ε : ℝ, sublevelVol
        ((Measure.pi fun j : Fin 0 => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ h j)).prod ν)
        ((Set.univ.pi fun _ : Fin 0 => Icc (-1 : ℝ) 1) ×ˢ K)
        (fun z => (∏ j, |z.1 j| ^ p j) * g z.2) ε
        = sublevelVol ν K g ε := by
      intro ε
      unfold sublevelVol
      have hSm : MeasurableSet
          (((Set.univ.pi fun _ : Fin 0 => Icc (-1 : ℝ) 1) ×ˢ K) ∩
            {z : (Fin 0 → ℝ) × γ | (∏ j, |z.1 j| ^ p j) * g z.2 ≤ ε}) :=
        ((MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod
          hK).inter (hfm measurableSet_Iic)
      rw [Measure.pi_of_empty _, Measure.dirac_prod,
        Measure.map_apply measurable_prodMk_left hSm]
      congr 2
      ext y
      simp only [mem_preimage, mem_inter_iff, mem_prod, mem_ofPred_eq,
        Set.mem_univ_pi]
      constructor
      · rintro ⟨⟨_, hyK⟩, hle⟩
        refine ⟨hyK, ?_⟩
        rwa [show (∏ j : Fin 0, |(fun a : Fin 0 =>
          isEmptyElim a : Fin 0 → ℝ) j| ^ p j) = 1
          from Finset.prod_of_isEmpty _, one_mul] at hle
      · rintro ⟨hyK, hle⟩
        refine ⟨⟨fun i => isEmptyElim i, hyK⟩, ?_⟩
        rwa [show (∏ j : Fin 0, |(fun a : Fin 0 =>
          isEmptyElim a : Fin 0 → ℝ) j| ^ p j) = 1
          from Finset.prod_of_isEmpty _, one_mul]
    unfold HasLLCExponentsOn
    rw [funext hVeq]
    exact hg
  | succ n ih =>
    -- per-coordinate measures
    have hIH := ih (fun j => p j.succ) (fun j => h j.succ)
      (fun j => hp _) (fun j => hh _) (fun j => hstrict _)
    -- the abstract factor for the single peel
    set g' : (Fin n → ℝ) × γ → ℝ :=
      fun w => (∏ j, |w.1 j| ^ p j.succ) * g w.2 with hg'def
    have hg'm : Measurable g' := by
      rw [hg'def]
      fun_prop
    have hK' : MeasurableSet
        ((Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ×ˢ K) :=
      (MeasurableSet.univ_pi fun _ => measurableSet_Icc).prod hK
    have hg'0 : ∀ w ∈ (Set.univ.pi fun _ : Fin n =>
        Icc (-1 : ℝ) 1) ×ˢ K, 0 ≤ g' w := by
      rintro w ⟨_, hwK⟩
      have h1 : (0 : ℝ) ≤ ∏ j, |w.1 j| ^ p j.succ :=
        Finset.prod_nonneg fun j _ =>
          Real.rpow_nonneg (abs_nonneg _) _
      exact mul_nonneg h1 (hg0 _ hwK)
    have hg'1 : ∀ w ∈ (Set.univ.pi fun _ : Fin n =>
        Icc (-1 : ℝ) 1) ×ˢ K, g' w ≤ 1 := by
      rintro w ⟨hwc, hwK⟩
      have h1 : ∏ j, |w.1 j| ^ p j.succ ≤ 1 := by
        refine Finset.prod_le_one₀
          (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
          (fun j _ => ?_)
        refine Real.rpow_le_one (abs_nonneg _) ?_ (hp _).le
        have := hwc j (Set.mem_univ j)
        exact abs_le.mpr ⟨this.1, this.2⟩
      calc g' w ≤ 1 * 1 := by
            refine mul_le_mul h1 (hg1 _ hwK) (hg0 _ hwK) zero_le_one
        _ = 1 := one_mul 1
    have hν'K' : ((Measure.pi fun j : Fin n => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h j.succ)).prod ν)
        ((Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ×ˢ K) ≠ ⊤ := by
      rw [Measure.prod_prod, Measure.pi_pi]
      refine ENNReal.mul_ne_top ?_ hνK
      refine (ENNReal.prod_lt_top fun j _ => ?_).ne
      rw [weighted_Icc_mass (hh j.succ)]
      exact ENNReal.ofReal_lt_top
    -- the single peel on the reshuffled space
    have hpeel := hasLLCExponentsOn_mul_strict_coord
      (ν := (Measure.pi fun j : Fin n => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h j.succ)).prod ν)
      hK' hg'm hg'0 hg'1 (hp 0) (hh 0) hlam htheta (hstrict 0)
      hν'K' hIH
    -- the reshuffle: pi over Fin (n+1) times γ, to ℝ times (pi times γ)
    have hμrw : (Measure.pi fun j : Fin n => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h ((0 : Fin (n+1)).succAbove j)))
        = Measure.pi fun j : Fin n => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ h j.succ) := by
      refine congrArg Measure.pi (funext fun j => ?_)
      rw [Fin.succAbove_zero]
    have hT : MeasurePreserving
        (⇑MeasurableEquiv.prodAssoc ∘ Prod.map
          (⇑(MeasurableEquiv.piFinSuccAbove
            (fun _ : Fin (n + 1) => ℝ) 0)) id)
        ((Measure.pi fun j : Fin (n + 1) => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ h j)).prod ν)
        ((volume.withDensity fun x => ENNReal.ofReal (|x| ^ h 0)).prod
          ((Measure.pi fun j : Fin n => volume.withDensity
            fun x => ENNReal.ofReal (|x| ^ h j.succ)).prod ν)) := by
      have h1 := (measurePreserving_piFinSuccAbove
        (fun j : Fin (n + 1) => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ h j)) 0).prod
        (MeasurePreserving.id ν)
      rw [hμrw] at h1
      exact (measurePreserving_prodAssoc _ _ _).comp h1
    -- package as a measurable equivalence for the transport
    set T : ((Fin (n + 1) → ℝ) × γ) ≃ᵐ (ℝ × ((Fin n → ℝ) × γ)) :=
      ((MeasurableEquiv.piFinSuccAbove
        (fun _ : Fin (n + 1) => ℝ) 0).prodCongr
        (MeasurableEquiv.refl γ)).trans MeasurableEquiv.prodAssoc
    have hTcoe : ⇑T = ⇑MeasurableEquiv.prodAssoc ∘ Prod.map
        (⇑(MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0)) id := rfl
    have hTmp : MeasurePreserving (⇑T)
        ((Measure.pi fun j : Fin (n + 1) => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ h j)).prod ν)
        ((volume.withDensity fun x => ENNReal.ofReal (|x| ^ h 0)).prod
          ((Measure.pi fun j : Fin n => volume.withDensity
            fun x => ENNReal.ofReal (|x| ^ h j.succ)).prod ν)) := by
      rw [hTcoe]
      exact hT
    have htrans := MeasurePreserving.hasLLCExponentsOn_comp
      (K' := Icc (-1 : ℝ) 1 ×ˢ
        ((Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ×ˢ K))
      (g := fun z => |z.1| ^ p 0 * g' z.2)
      (lam := lam) (theta := theta) T hTmp
    -- identify the set and the function
    have hset : ⇑T ⁻¹' (Icc (-1 : ℝ) 1 ×ˢ
        ((Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ×ˢ K))
        = (Set.univ.pi fun _ : Fin (n + 1) => Icc (-1 : ℝ) 1) ×ˢ K := by
      ext z
      simp only [mem_preimage, mem_prod, Set.mem_univ_pi, hTcoe,
        Function.comp_apply, MeasurableEquiv.prodAssoc,
        MeasurableEquiv.coe_mk, Equiv.prodAssoc_apply]
      constructor
      · rintro ⟨h0, htail, hzK⟩
        refine ⟨fun i => ?_, hzK⟩
        induction i using Fin.cases with
        | zero => exact h0
        | succ j => exact htail j
      · rintro ⟨hall, hzK⟩
        exact ⟨hall 0, fun j => hall j.succ, hzK⟩
    have hfun : (fun z : (Fin (n + 1) → ℝ) × γ =>
        (fun w : ℝ × ((Fin n → ℝ) × γ) => |w.1| ^ p 0 * g' w.2) (T z))
        = fun z => (∏ j, |z.1 j| ^ p j) * g z.2 := by
      funext z
      change |z.1 0| ^ p 0
          * ((∏ j : Fin n, |z.1 j.succ| ^ p j.succ) * g z.2)
        = (∏ j, |z.1 j| ^ p j) * g z.2
      rw [Fin.prod_univ_succ]
      ring
    rw [hset, hfun] at htrans
    exact htrans.mpr hpeel

/-- **The split theorem**: a weighted monomial with an
attaining equal-`λ` block and a strict block has exponents
`(λ, #attainers)` on the unit cube — the strict block contributes
nothing to the order. -/
theorem hasLLCExponentsOn_split {m n : ℕ}
    {ke : Fin (m + 1) → ℕ} {he : Fin (m + 1) → ℝ}
    {ps hs : Fin n → ℝ}
    (hke : ∀ i, 0 < ke i) (hhe : ∀ i, 0 ≤ he i)
    {lam : ℝ} (heq : ∀ i, (he i + 1) / (2 * ke i : ℝ) = lam)
    (hps : ∀ j, 0 < ps j) (hhs : ∀ j, 0 ≤ hs j)
    (hstrict : ∀ j, lam < (hs j + 1) / ps j) :
    HasLLCExponentsOn
      ((Measure.pi fun j : Fin n => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ hs j)).prod
        (Measure.pi fun i : Fin (m + 1) => volume.withDensity
          fun x => ENNReal.ofReal (|x| ^ he i)))
      ((Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) ×ˢ
        Set.univ.pi fun _ : Fin (m + 1) => Icc (-1 : ℝ) 1)
      (fun z => (∏ j, |z.1 j| ^ ps j)
        * ∏ i, |z.2 i| ^ (2 * ke i : ℝ))
      lam (m + 1) := by
  have hlam : 0 < lam := by
    rw [← heq 0]
    exact div_pos (by linarith [hhe 0]) (by have := hke 0; positivity)
  refine hasLLCExponentsOn_mul_strict_family
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc)
    ?_ ?_ ?_ hlam (by
      have : (1 : ℝ) ≤ (m : ℝ) + 1 := by
        have := Nat.cast_nonneg (α := ℝ) m
        linarith
      exact this) ?_
    (hasLLCExponentsOn_equal_block hke hhe heq)
    ps hs hps hhs hstrict
  · -- measurability of the equal monomial
    fun_prop
  · -- nonnegativity
    intro y _
    exact Finset.prod_nonneg fun i _ =>
      Real.rpow_nonneg (abs_nonneg _) _
  · -- bounded by one on the cube
    intro y hy
    refine Finset.prod_le_one₀
      (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (fun i _ => ?_)
    refine Real.rpow_le_one (abs_nonneg _) ?_ (by positivity)
    have := hy i (Set.mem_univ i)
    exact abs_le.mpr ⟨this.1, this.2⟩
  · -- the equal block carries finite mass on the cube
    rw [Measure.pi_pi]
    refine (ENNReal.prod_lt_top fun i _ => ?_).ne
    rw [weighted_Icc_mass (hhe i)]
    exact ENNReal.ofReal_lt_top

end SingularLearningTheory
