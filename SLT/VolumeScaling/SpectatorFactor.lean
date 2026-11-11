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
import SLT.VolumeScaling.CubeRescale
import SLT.VolumeScaling.PeelFactors
import SLT.VolumeScaling.Transport
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Positivity.Finset

/-!
# Spectator factors

Extending the domain by coordinates the function never reads scales the sublevel volume by the
spectator block's measure — a nonzero finite constant — so the volume-scaling exponents are
unchanged (`HasLLCExponentsOn.prod_fst`).

The second half of the file is the support-version weighted-monomial read-off
(`hasLLCExponentsOn_weighted_monomial_support`): coordinates with exponent zero are spectators,
so the monomial over a nonempty support inside a larger cube has the support's minimal ratio as
`λ` and its attaining count as `θ`; it uses the cube rescaling (`CubeRescale`) and is the form
`ArbitraryExponent` extends to arbitrary exponents.
-/

public section

open Filter MeasureTheory Asymptotics Set

namespace SingularLearningTheory

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- **The spectator-factor extension**: the exponents survive a
product with a block of nonzero finite measure that the function
ignores. -/
theorem HasLLCExponentsOn.prod_fst {μ : Measure α} {ν : Measure β}
    [SFinite ν] {K : Set α} {B : Set β} {f : α → ℝ} {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta)
    (hB : ν B ≠ 0) (hB' : ν B ≠ ⊤) :
    HasLLCExponentsOn (μ.prod ν) (K ×ˢ B) (fun p => f p.1)
      lam theta := by
  unfold HasLLCExponentsOn at h ⊢
  have hfun : sublevelVol (μ.prod ν) (K ×ˢ B) (fun p => f p.1) =
      fun ε => (ν B).toReal * sublevelVol μ K f ε :=
    funext fun ε => sublevelVol_indep_factor ε
  rw [hfun]
  exact h.const_mul_left (ENNReal.toReal_ne_zero.mpr ⟨hB, hB'⟩)

/-! ## The support-version weighted-monomial read-off -/

/-- The 1-d weighted box has positive mass. -/
theorem weighted_Icc_ne_zero {h R : ℝ} (hh : 0 ≤ h) (hR : 0 < R) :
    (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h))
      (Icc (-R) R) ≠ 0 := by
  rw [withDensity_apply _ measurableSet_Icc]
  intro hcon
  have hsub : Icc (R / 2) R ⊆ Icc (-R) R :=
    Icc_subset_Icc (by linarith) le_rfl
  have hle : ENNReal.ofReal ((R / 2) ^ h) * volume (Icc (R / 2) R) ≤
      ∫⁻ x in Icc (-R) R, ENNReal.ofReal (|x| ^ h) :=
    calc ENNReal.ofReal ((R / 2) ^ h) * volume (Icc (R / 2) R)
        = ∫⁻ _ in Icc (R / 2) R,
            ENNReal.ofReal ((R / 2) ^ h) :=
          (MeasureTheory.setLIntegral_const _ _).symm
      _ ≤ ∫⁻ x in Icc (R / 2) R, ENNReal.ofReal (|x| ^ h) := by
          refine MeasureTheory.setLIntegral_mono
            (by fun_prop) fun x hx => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          have hx2 : R / 2 ≤ |x| := by
            rw [abs_of_nonneg
              (by linarith [hx.1] : (0 : ℝ) ≤ x)]
            exact hx.1
          exact Real.rpow_le_rpow (by linarith) hx2 hh
      _ ≤ ∫⁻ x in Icc (-R) R, ENNReal.ofReal (|x| ^ h) :=
          MeasureTheory.lintegral_mono_set hsub
  rw [hcon] at hle
  have h1 : ENNReal.ofReal ((R / 2) ^ h) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr
      (Real.rpow_pos_of_pos (by linarith) h)
  have h2 : volume (Icc (R / 2) R) ≠ 0 := by
    rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_zero_iff.mpr (by linarith)
  exact absurd (le_antisymm hle zero_le)
    (mul_ne_zero h1 h2)

/-- The 1-d weighted box has finite mass. -/
theorem weighted_Icc_ne_top {h R : ℝ} (hh : 0 ≤ h) (_hR : 0 < R) :
    (volume.withDensity fun x => ENNReal.ofReal (|x| ^ h))
      (Icc (-R) R) ≠ ⊤ := by
  rw [withDensity_apply _ measurableSet_Icc]
  refine ne_top_of_le_ne_top ?_
    (MeasureTheory.setLIntegral_mono (by fun_prop)
      (fun x hx => ?_) :
      _ ≤ ∫⁻ _ in Icc (-R) R,
        ENNReal.ofReal ((max 1 R) ^ h))
  · rw [MeasureTheory.setLIntegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  · refine ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow (abs_nonneg x) ?_ hh)
    refine le_trans (abs_le.mpr ⟨hx.1, hx.2⟩) (le_max_right 1 R)
/-- **The support-version weighted-monomial read-off**: zero exponents
are spectators — the monomial over a nonempty support inside a larger
cube has the support's minimal ratio as `λ` and its attaining count
as `θ`. -/
theorem hasLLCExponentsOn_weighted_monomial_support {n : ℕ}
    (k : Fin n → ℕ) (h : Fin n → ℝ) (hh : ∀ i, 0 ≤ h i) {lam : ℝ}
    (hmin : ∀ i, 0 < k i → lam ≤ (h i + 1) / (2 * k i : ℝ))
    (hatt : ∃ i, 0 < k i ∧ (h i + 1) / (2 * k i : ℝ) = lam)
    {R : ℝ} (hR : 0 < R) :
    HasLLCExponentsOn
      (Measure.pi fun i => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i))
      (Set.univ.pi fun _ : Fin n => Icc (-R) R)
      (fun x => ∏ i, |x i| ^ (2 * k i : ℝ))
      lam ((Finset.univ.filter
        fun i => 0 < k i ∧ (h i + 1) / (2 * k i : ℝ) = lam).card) := by
  classical
  set p : Fin n → Prop := fun i => 0 < k i with hpdef
  obtain ⟨i₀, hi₀, hr₀⟩ := hatt
  have : Nonempty {i // p i} := ⟨⟨i₀, hi₀⟩⟩
  set ns := Fintype.card {i // p i} with hnsdef
  set na := Fintype.card {i // ¬ p i} with hnadef
  set eS : Fin ns ≃ {i // p i} := (Fintype.equivFin _).symm with heSdef
  set eA : Fin na ≃ {i // ¬ p i} := (Fintype.equivFin _).symm with heAdef
  have hsupp := hasLLCExponentsOn_weighted_monomial_rescaled
    (n := ns) (fun j => k (eS j)) (fun j => h (eS j))
    (fun j => (eS j).2) (fun j => hh _)
    (fun j => hmin _ (eS j).2)
    ⟨eS.symm ⟨i₀, hi₀⟩, by
      rw [Equiv.apply_symm_apply]
      exact hr₀⟩ hR
  set νA : Measure (Fin na → ℝ) := Measure.pi fun i =>
    volume.withDensity fun x => ENNReal.ofReal (|x| ^ h (eA i))
    with hνAdef
  set BA : Set (Fin na → ℝ) :=
    Set.univ.pi fun _ : Fin na => Icc (-R) R with hBAdef
  have hνB : νA BA = ∏ i : Fin na,
      (volume.withDensity fun x =>
        ENNReal.ofReal (|x| ^ h (eA i))) (Icc (-R) R) := by
    rw [hνAdef, hBAdef, Measure.pi_pi]
  have hν0 : νA BA ≠ 0 := by
    rw [hνB]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      weighted_Icc_ne_zero (hh _) hR
  have hνtop : νA BA ≠ ⊤ := by
    rw [hνB]
    exact ENNReal.prod_ne_top fun i _ =>
      weighted_Icc_ne_top (hh _) hR
  have hprod := hsupp.prod_fst (ν := νA) (B := BA) hν0 hνtop
  set T : (Fin n → ℝ) ≃ᵐ ((Fin ns → ℝ) × (Fin na → ℝ)) :=
    (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => ℝ) p).trans
      (((MeasurableEquiv.piCongrLeft (fun _ : {i // p i} => ℝ)
        eS).symm).prodCongr
       ((MeasurableEquiv.piCongrLeft (fun _ : {i // ¬ p i} => ℝ)
        eA).symm)) with hTdef
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
  have hTmp : MeasurePreserving (⇑T)
      (Measure.pi fun i => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h i))
      ((Measure.pi fun j : Fin ns => volume.withDensity
        fun x => ENNReal.ofReal (|x| ^ h (eS j))).prod νA) :=
    (hT2.prod hT3).comp hT1
  have htrans := MeasurePreserving.hasLLCExponentsOn_comp
    (K' := (Set.univ.pi fun _ : Fin ns => Icc (-R) R) ×ˢ BA)
    (g := fun z : (Fin ns → ℝ) × (Fin na → ℝ) =>
      ∏ j, |z.1 j| ^ (2 * k (eS j) : ℝ))
    (lam := lam)
    (theta := ((Finset.univ.filter fun j : Fin ns =>
      (h (eS j) + 1) / (2 * k (eS j) : ℝ) = lam).card : ℝ))
    T hTmp
  have hset : ⇑T ⁻¹' ((Set.univ.pi fun _ : Fin ns =>
      Icc (-R) R) ×ˢ BA)
      = Set.univ.pi fun _ : Fin n => Icc (-R) R := by
    ext x
    have hTx : T x = (fun j => x (eS j), fun i => x (eA i)) := rfl
    simp only [mem_preimage, hTx, mem_prod, Set.mem_univ_pi,
      hBAdef]
    constructor
    · rintro ⟨h1, h2⟩ i
      by_cases hpi : p i
      · have := h1 (eS.symm ⟨i, hpi⟩)
        rwa [Equiv.apply_symm_apply] at this
      · have := h2 (eA.symm ⟨i, hpi⟩)
        rwa [Equiv.apply_symm_apply] at this
    · intro hx
      exact ⟨fun j => hx _, fun i => hx _⟩
  have hfun : (fun x : Fin n → ℝ =>
      ∏ j, |(T x).1 j| ^ (2 * k (eS j) : ℝ))
      = fun x => ∏ i, |x i| ^ (2 * k i : ℝ) := by
    funext x
    have hTx : T x = (fun j => x (eS j), fun i => x (eA i)) := rfl
    rw [hTx]
    change (∏ j, |x (eS j)| ^ (2 * k (eS j) : ℝ))
      = ∏ i, |x i| ^ (2 * k i : ℝ)
    rw [← Fintype.prod_subtype_mul_prod_subtype p
      (fun i => |x i| ^ (2 * k i : ℝ)),
      ← Equiv.prod_comp eS
        (fun i : {i // p i} => |x i| ^ (2 * k i : ℝ))]
    have hones : (∏ i : {i // ¬ p i}, |x i| ^ (2 * k i : ℝ)) = 1 :=
      Finset.prod_eq_one fun i _ => by
        have hki : k i = 0 := Nat.eq_zero_of_not_pos i.2
        rw [hki]
        norm_num
    rw [hones, mul_one]
  have hcard : (Finset.univ.filter fun i : Fin n =>
      0 < k i ∧ (h i + 1) / (2 * k i : ℝ) = lam).card
      = (Finset.univ.filter fun j : Fin ns =>
        (h (eS j) + 1) / (2 * k (eS j) : ℝ) = lam).card := by
    refine Finset.card_bij'
      (fun i hi => eS.symm ⟨i, (Finset.mem_filter.mp hi).2.1⟩)
      (fun j _ => (eS j : Fin n)) ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [Equiv.apply_symm_apply]
      exact hi.2.2
    · intro j hj
      rw [Finset.mem_filter] at hj ⊢
      exact ⟨Finset.mem_univ _, (eS j).2, hj.2⟩
    · intro i hi
      rw [Equiv.apply_symm_apply]
    · intro j hj
      exact (congrArg eS.symm (Subtype.ext rfl)).trans
        (eS.symm_apply_apply j)
  rw [hset] at htrans
  rw [show (fun x : Fin n → ℝ =>
      (fun z : (Fin ns → ℝ) × (Fin na → ℝ) =>
        ∏ j, |z.1 j| ^ (2 * k (eS j) : ℝ)) (T x))
      = fun x => ∏ i, |x i| ^ (2 * k i : ℝ) from hfun] at htrans
  rw [hcard]
  exact htrans.mpr hprod

end SingularLearningTheory
