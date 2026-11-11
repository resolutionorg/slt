/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Borel spaces on countable disjoint unions

Mathlib's measurable structure on a countable disjoint union of Borel spaces is the Borel
σ-algebra of its topology (`Sigma.borelSpace`).
-/

public section

open Set MeasureTheory Topology

namespace SingularLearningTheory

@[expose] instance _root_.Sigma.borelSpace {ι : Type*} {U : ι → Type*} [Countable ι]
    [∀ i, TopologicalSpace (U i)] [∀ i, MeasurableSpace (U i)]
    [∀ i, BorelSpace (U i)] : BorelSpace (Sigma U) := by
  constructor
  apply le_antisymm
  · intro s hs
    have hs' : ∀ i, MeasurableSet (Sigma.mk i ⁻¹' s) :=
      MeasurableSpace.measurableSet_iInf.mp hs
    -- Only this direction temporarily equips the codomain with its Borel space.
    -- The goal already explicitly asks for measurability in that Borel space.
    letI : MeasurableSpace (Sigma U) := borel (Sigma U)
    letI : BorelSpace (Sigma U) := ⟨rfl⟩
    change MeasurableSet s
    have heq : s = ⋃ i, Sigma.mk i '' (Sigma.mk i ⁻¹' s) := by
      ext x
      constructor
      · intro hx
        exact mem_iUnion.mpr ⟨x.1, x.2, hx, rfl⟩
      · intro hx
        rcases mem_iUnion.mp hx with ⟨i, y, hy, hxy⟩
        exact hxy ▸ hy
    rw [heq]
    apply MeasurableSet.iUnion
    intro i
    exact (Topology.IsOpenEmbedding.sigmaMk.measurableEmbedding).measurableSet_image' (hs' i)
  · apply MeasurableSpace.generateFrom_le
    intro s hs
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro i
    exact (isOpen_sigma_iff.mp hs i).measurableSet

end SingularLearningTheory
