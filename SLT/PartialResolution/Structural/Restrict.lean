/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.PartialResolution

/-!
# Restriction of a partial resolution to a compact subset

"The mappings `π_j | π_j⁻¹(V_i)` … form a Σ-covering of `M`" [BM88, Remark 4.5]. In chart form,
`PartialResolution.restrict`: a partial resolution of `F` on `K'` restricts to one on a compact
`K ⊆ K'` by cutting every chart domain down to `dom i ∩ φ i ⁻¹' K` (compact: a closed subset of
the compact `dom i`, closed by `ContinuousOn.preimage_isClosed_of_isClosed`) and every
exceptional set to its intersection with the new domain; the maps, the smooth neighbourhoods, the
Jacobians, the multiplicity bound and its null set are unchanged. The covering clause: a point of
`K` not covered by the restricted charts is not covered by the original ones (its preimages would
lie in `φ i ⁻¹' K`).
-/

@[expose] public section

open Set MeasureTheory

namespace Analytic

namespace PartialResolution

variable {n : ℕ} {F : (Fin n → ℝ) → ℝ} {K' : Set (Fin n → ℝ)}

/-- The part of a chart domain mapped into a closed set is closed. -/
theorem isClosed_dom_inter_preimage (R : PartialResolution n F K') (i : R.ι)
    {K : Set (Fin n → ℝ)} (hK : IsClosed K) : IsClosed (R.dom i ∩ R.φ i ⁻¹' K) :=
  (R.continuousOn i).preimage_isClosed_of_isClosed (R.dom_compact i).isClosed hK

/-- Restriction of a partial resolution of `F` on `K'` to a compact `K ⊆ K'`: the chart domains
become `dom i ∩ φ i ⁻¹' K`, the exceptional sets are cut down accordingly, and everything else is
unchanged (the printed `π_j | π_j⁻¹(V_i)` of [BM88, Remark 4.5]). -/
def restrict (R : PartialResolution n F K') {K : Set (Fin n → ℝ)} (hK : K ⊆ K')
    (hKc : IsCompact K) : PartialResolution n F K where
  K_compact := hKc
  ι := R.ι
  dom i := R.dom i ∩ R.φ i ⁻¹' K
  dom_compact i :=
    (R.dom_compact i).of_isClosed_subset (R.isClosed_dom_inter_preimage i hKc.isClosed)
      inter_subset_left
  φ := R.φ
  smooth i := by
    obtain ⟨U, hU, hsub, hsm⟩ := R.smooth i
    exact ⟨U, hU, inter_subset_left.trans hsub, hsm⟩
  mapsTo i := fun _ hx => hx.2
  cover := by
    refine measure_mono_null (fun y hy => ?_) R.cover
    obtain ⟨hyK, hyn⟩ := hy
    refine ⟨hK hyK, fun h => hyn ?_⟩
    obtain ⟨i, x, hx, rfl⟩ := by simpa only [mem_iUnion, mem_image] using h
    exact mem_iUnion.mpr ⟨i, ⟨x, ⟨hx, hyK⟩, rfl⟩⟩
  E i := R.E i ∩ (R.dom i ∩ R.φ i ⁻¹' K)
  E_subset _ := inter_subset_right
  E_closed i := (R.E_closed i).inter (R.isClosed_dom_inter_preimage i hKc.isClosed)
  E_null i := measure_mono_null inter_subset_left (R.E_null i)
  inj i := (R.inj i).mono (by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx1.1, fun h => hx2 ⟨h, hx1⟩⟩)
  jac_ne_zero i := by
    rintro x ⟨hx1, hx2⟩
    exact R.jac_ne_zero i x ⟨hx1.1, fun h => hx2 ⟨h, hx1⟩⟩
  mult := R.mult
  multN := R.multN
  multN_null := R.multN_null
  mult_bound := fun y hy =>
    (Set.encard_le_encard (by
      rintro p ⟨hp1, hp2⟩
      exact ⟨hp1.1, hp2⟩)).trans (R.mult_bound y ⟨hK hy.1, hy.2⟩)

variable (R : PartialResolution n F K') {K : Set (Fin n → ℝ)} (hK : K ⊆ K') (hKc : IsCompact K)

@[simp] theorem restrict_dom (i : (R.restrict hK hKc).ι) :
    (R.restrict hK hKc).dom i = R.dom i ∩ R.φ i ⁻¹' K := rfl

@[simp] theorem restrict_φ (i : (R.restrict hK hKc).ι) : (R.restrict hK hKc).φ i = R.φ i := rfl

@[simp] theorem restrict_E (i : (R.restrict hK hKc).ι) :
    (R.restrict hK hKc).E i = R.E i ∩ (R.dom i ∩ R.φ i ⁻¹' K) := rfl

@[simp] theorem restrict_mult : (R.restrict hK hKc).mult = R.mult := rfl

@[simp] theorem restrict_multN : (R.restrict hK hKc).multN = R.multN := rfl

/-- Every chart of the restriction is a chart of the original cut down to the preimage of `K`. -/
theorem restrict_charts (i : (R.restrict hK hKc).ι) :
    ∃ j : R.ι, (R.restrict hK hKc).dom i = R.dom j ∩ R.φ j ⁻¹' K ∧
      (R.restrict hK hKc).φ i = R.φ j ∧
      (R.restrict hK hKc).E i = R.E j ∩ (R.dom j ∩ R.φ j ⁻¹' K) :=
  ⟨i, rfl, rfl, rfl⟩

/-- Every chart of the original appears, cut down, in the restriction. -/
theorem exists_restrict_chart (j : R.ι) :
    ∃ i : (R.restrict hK hKc).ι, (R.restrict hK hKc).dom i = R.dom j ∩ R.φ j ⁻¹' K ∧
      (R.restrict hK hKc).φ i = R.φ j ∧
      (R.restrict hK hKc).E i = R.E j ∩ (R.dom j ∩ R.φ j ⁻¹' K) :=
  ⟨j, rfl, rfl, rfl⟩

end PartialResolution

end Analytic
