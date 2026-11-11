/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Topology.Maps.Proper.CompactlyGenerated
public import SLT.Resolution.Hironaka

/-!
# A resolution is a closed map into `U`

A resolution is proper over the open set `U`, hence a closed map into `U`: the image of a closed
subset of `M` is relatively closed in `U` (`Resolution.isClosed_image`).
-/

public section

namespace SingularLearningTheory

open Set Filter Topology

variable {d : ℕ}

/-- A resolution is a closed map into the open `U ⊆ ℝ^d`: for closed `C ⊆ M`, the image `π '' C`
is relatively closed in `U`. No thesis counterpart. -/
theorem Resolution.isClosed_image {F : (Fin d → ℝ) → ℝ} (R : Resolution F) {C : Set R.M}
    (hC : IsClosed C) : R.U ∩ closure (R.π '' C) ⊆ R.π '' C := by
  have : LocallyCompactSpace R.U := R.isOpen_U.locallyCompactSpace
  let g' : R.M → R.U := fun x ↦ ⟨R.π x, R.mem_U x⟩
  have hg' : Continuous g' := R.continuous_π.subtype_mk _
  have hprop : IsProperMap g' := by
    refine isProperMap_iff_isCompact_preimage.mpr ⟨hg', fun K hK ↦ ?_⟩
    have hpre : g' ⁻¹' K = R.π ⁻¹' (Subtype.val '' K) := by
      ext x
      exact (Subtype.val_injective.mem_set_image (a := g' x)).symm
    rw [hpre]
    exact R.proper _ (by rintro _ ⟨y, -, rfl⟩; exact y.2) (hK.image continuous_subtype_val)
  rintro y ⟨hyV, hycl⟩
  have hcl : IsClosed (g' '' C) := hprop.isClosedMap _ hC
  have hmem : (⟨y, hyV⟩ : R.U) ∈ closure (g' '' C) := by
    rw [closure_subtype]
    have himg : Subtype.val '' (g' '' C) = R.π '' C := by rw [image_image]
    simpa [himg] using hycl
  rw [hcl.closure_eq] at hmem
  obtain ⟨x, hx, hxy⟩ := hmem
  exact ⟨x, hx, congrArg Subtype.val hxy⟩

end SingularLearningTheory
