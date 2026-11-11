/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.PartialResolution

/-!
# Disjoint union of partial resolutions

Bierstone and Milman compose Σ-coverings: "for each `j`, there is a finite subset `K(j)` … the
mappings `π_j ∘ π_{jk}`, for all `j` and all `k ∈ K(j)`, form a Σ-covering of `M`"
[BM88, Remark 4.5]. The chart-form counterpart is the disjoint union `PartialResolution.sigma`:
from `R i : PartialResolution n F (K i)` for `i` in a finite index type build a partial resolution
of `F` on `⋃ i, K i` with chart index `Σ i, (R i).ι`, the charts of the `R i` unchanged, the
multiplicity bound `∑ i, (R i).mult` and the multiplicity null set `⋃ i, (R i).multN`. The
covering clause holds because `(⋃ K i) \ ⋃ images ⊆ ⋃ i, (K i \ ⋃ images_i)`; the multiplicity
bound because the preimage set of a point `y` is the union over `i` of the preimage sets of the
`R i`, each of cardinality at most `(R i).mult` (and empty for `i` with `y ∉ K i`, by `mapsTo`);
`Set.encard_iUnion_le` bounds the cardinality of a finite union by the sum. The construction is
stated for any finite index type in `Type` (`Fin N` is an instance), which is what the gluing
lemma of `OfLocal.lean` needs after a finite subcover.
-/

@[expose] public section

open Set MeasureTheory

namespace Analytic

/-- The cardinality of a finite union is at most the sum of the cardinalities. -/
theorem _root_.Set.encard_biUnion_le {α ι : Type*} (s : Finset ι) (t : ι → Set α) :
    (⋃ i ∈ s, t i).encard ≤ ∑ i ∈ s, (t i).encard := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hi]
    exact (Set.encard_union_le _ _).trans (add_le_add le_rfl ih)

/-- The cardinality of a union over a finite type is at most the sum of the cardinalities. -/
theorem _root_.Set.encard_iUnion_le {α ι : Type*} [Fintype ι] (t : ι → Set α) :
    (⋃ i, t i).encard ≤ ∑ i, (t i).encard := by
  have := Set.encard_biUnion_le Finset.univ t
  simpa using this

namespace PartialResolution

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ}

/-- The disjoint union of finitely many partial resolutions of `F` is a partial resolution of `F`
on the union of the sets, with the charts unchanged, the multiplicity bounds added and the
multiplicity null sets united: the composition of finitely many Σ-coverings of
[BM88, Remark 4.5]. -/
def sigma {ι : Type} [Fintype ι] {K : ι → Set (Fin n → ℝ)}
    (R : ∀ i, PartialResolution n F (K i)) : PartialResolution n F (⋃ i, K i) where
  K_compact := isCompact_iUnion fun i => (R i).K_compact
  ι := Σ i, (R i).ι
  dom p := (R p.1).dom p.2
  dom_compact p := (R p.1).dom_compact p.2
  φ p := (R p.1).φ p.2
  smooth p := (R p.1).smooth p.2
  mapsTo p := fun x hx => mem_iUnion.mpr ⟨p.1, (R p.1).mapsTo p.2 hx⟩
  cover := by
    refine measure_mono_null (fun y hy => ?_) (measure_iUnion_null fun i => (R i).cover)
    obtain ⟨hyK, hyn⟩ := hy
    obtain ⟨i, hi⟩ := mem_iUnion.mp hyK
    refine mem_iUnion.mpr ⟨i, hi, fun h => hyn ?_⟩
    obtain ⟨j, x, hx, rfl⟩ := by simpa only [mem_iUnion, mem_image] using h
    exact mem_iUnion.mpr ⟨⟨i, j⟩, ⟨x, hx, rfl⟩⟩
  E p := (R p.1).E p.2
  E_subset p := (R p.1).E_subset p.2
  E_closed p := (R p.1).E_closed p.2
  E_null p := (R p.1).E_null p.2
  inj p := (R p.1).inj p.2
  jac_ne_zero p := (R p.1).jac_ne_zero p.2
  mult := ∑ i, (R i).mult
  multN := ⋃ i, (R i).multN
  multN_null := measure_iUnion_null fun i => (R i).multN_null
  mult_bound := by
    intro y hy
    obtain ⟨hyK, hyN⟩ := hy
    rw [Nat.cast_sum]
    calc {p : (Σ i, (R i).ι) × (Fin n → ℝ) |
            p.2 ∈ (R p.1.1).dom p.1.2 ∧ (R p.1.1).φ p.1.2 p.2 = y}.encard
        ≤ (⋃ i, (fun q : (R i).ι × (Fin n → ℝ) => ((⟨i, q.1⟩ : Σ i, (R i).ι), q.2)) ''
            {q : (R i).ι × (Fin n → ℝ) | q.2 ∈ (R i).dom q.1 ∧ (R i).φ q.1 q.2 = y}).encard := by
          refine Set.encard_le_encard fun p hp => ?_
          exact mem_iUnion.mpr ⟨p.1.1, ⟨(p.1.2, p.2), hp, rfl⟩⟩
      _ ≤ ∑ i, ((fun q : (R i).ι × (Fin n → ℝ) => ((⟨i, q.1⟩ : Σ i, (R i).ι), q.2)) ''
            {q : (R i).ι × (Fin n → ℝ) | q.2 ∈ (R i).dom q.1 ∧ (R i).φ q.1 q.2 = y}).encard :=
          Set.encard_iUnion_le _
      _ ≤ ∑ i, ((R i).mult : ℕ∞) := by
          refine Finset.sum_le_sum fun i _ => (Set.encard_image_le _ _).trans ?_
          by_cases hi : y ∈ K i
          · exact (R i).mult_bound y ⟨hi, fun h => hyN (mem_iUnion.mpr ⟨i, h⟩)⟩
          · have hempty : {q : (R i).ι × (Fin n → ℝ) |
                q.2 ∈ (R i).dom q.1 ∧ (R i).φ q.1 q.2 = y} = ∅ := by
              refine Set.eq_empty_of_forall_notMem fun q hq => hi ?_
              rw [← hq.2]
              exact (R i).mapsTo q.1 hq.1
            rw [hempty, Set.encard_empty]
            exact zero_le

variable {ι : Type} [Fintype ι] {K : ι → Set (Fin n → ℝ)} (R : ∀ i, PartialResolution n F (K i))

@[simp] theorem sigma_dom (p : (sigma R).ι) : (sigma R).dom p = (R p.1).dom p.2 := rfl

@[simp] theorem sigma_φ (p : (sigma R).ι) : (sigma R).φ p = (R p.1).φ p.2 := rfl

@[simp] theorem sigma_E (p : (sigma R).ι) : (sigma R).E p = (R p.1).E p.2 := rfl

@[simp] theorem sigma_mult : (sigma R).mult = ∑ i, (R i).mult := rfl

@[simp] theorem sigma_multN : (sigma R).multN = ⋃ i, (R i).multN := rfl

/-- Every chart of the disjoint union is a chart of one of the summands. -/
theorem sigma_charts (p : (sigma R).ι) :
    ∃ i j, (sigma R).dom p = (R i).dom j ∧ (sigma R).φ p = (R i).φ j ∧
      (sigma R).E p = (R i).E j :=
  ⟨p.1, p.2, rfl, rfl, rfl⟩

/-- Every chart of a summand is a chart of the disjoint union. -/
theorem exists_sigma_chart (i : ι) (j : (R i).ι) :
    ∃ p : (sigma R).ι, (sigma R).dom p = (R i).dom j ∧ (sigma R).φ p = (R i).φ j ∧
      (sigma R).E p = (R i).E j :=
  ⟨⟨i, j⟩, rfl, rfl, rfl⟩

end PartialResolution

end Analytic
