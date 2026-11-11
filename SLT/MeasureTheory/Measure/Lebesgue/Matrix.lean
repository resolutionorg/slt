/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Measure structure on real matrix spaces (LA5.3c, infrastructure)

Mathlib's `Matrix m n α` is a type synonym for `m → n → α` whose
topology is inherited (`inferInstanceAs`) but whose *measure* structure
is not: no `MeasurableSpace`, no `MeasureSpace`, no Borel/Haar facts.
Volume-scaling statements on products of matrix spaces need these instances, so this file transfers
the pi instances across the synonym, in
the same `inferInstanceAs` style Mathlib uses for the topology (so all
structures are definitionally the pi ones).
-/

public section

open MeasureTheory

namespace Matrix

variable (m n : Type*) [Fintype m] [Fintype n]

@[expose] instance instSecondCountableTopologyMatrix :
    SecondCountableTopology (Matrix m n ℝ) :=
  inferInstanceAs (SecondCountableTopology (m → n → ℝ))

instance instMeasurableSpaceMatrix : MeasurableSpace (Matrix m n ℝ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℝ))

noncomputable instance instMeasureSpaceMatrix : MeasureSpace (Matrix m n ℝ) :=
  inferInstanceAs (MeasureSpace (m → n → ℝ))

@[expose] instance instBorelSpaceMatrix : BorelSpace (Matrix m n ℝ) :=
  inferInstanceAs (BorelSpace (m → n → ℝ))

@[expose] instance instSigmaFiniteVolumeMatrix :
    SigmaFinite (volume : Measure (Matrix m n ℝ)) :=
  inferInstanceAs (SigmaFinite (volume : Measure (m → n → ℝ)))

-- Synthesizing the Haar instance on the nested pi type `m → n → ℝ` exceeds the default size
-- limit of instance problems.
set_option synthInstance.maxSize 400 in
@[expose] instance instIsAddHaarMeasureVolumeMatrix :
    (volume : Measure (Matrix m n ℝ)).IsAddHaarMeasure :=
  inferInstanceAs ((volume : Measure (m → n → ℝ)).IsAddHaarMeasure)

end Matrix

namespace MeasureTheory

/-- Missing glue in Mathlib: `prod.instIsAddHaarMeasure` is keyed on
`μ.prod ν` and never fires on the product `MeasureSpace`'s `volume`
(which is `volume.prod volume` only definitionally). Restated on
`volume` so nested product spaces synthesize. -/
@[expose] instance Prod.instIsAddHaarMeasureVolume {α β : Type*}
    [MeasureSpace α] [AddGroup α] [TopologicalSpace α] [MeasurableAdd α]
    [SFinite (volume : Measure α)]
    [(volume : Measure α).IsAddHaarMeasure]
    [MeasureSpace β] [AddGroup β] [TopologicalSpace β] [MeasurableAdd β]
    [SFinite (volume : Measure β)]
    [(volume : Measure β).IsAddHaarMeasure] :
    (volume : Measure (α × β)).IsAddHaarMeasure :=
  inferInstanceAs (((volume : Measure α).prod volume).IsAddHaarMeasure)

open Set in
/-- Uncurrying `(m → n → ℝ) ≃ (m × n → ℝ)` is measure-preserving for the
pi volumes (missing from Mathlib's kit, which has the index-reindexing and
sum-splitting equivalences but not curry): both sides assign every
measurable box the product of its side volumes. -/
private theorem volume_measurePreserving_curry_symm (m n : Type*)
    [Fintype m] [Fintype n] :
    MeasurePreserving (MeasurableEquiv.curry m n ℝ).symm volume volume := by
  refine ⟨(MeasurableEquiv.curry m n ℝ).symm.measurable,
    (Measure.pi_eq fun s _ => ?_).symm⟩
  rw [MeasurableEquiv.map_apply,
    show (MeasurableEquiv.curry m n ℝ).symm ⁻¹' univ.pi s
        = univ.pi fun i => univ.pi fun j => s (i, j) by
      ext f
      simp only [MeasurableEquiv.coe_curry_symm, mem_preimage, mem_pi,
        mem_univ, forall_const, Function.uncurry]
      exact ⟨fun h i j => h (i, j), fun h p => h p.1 p.2⟩,
    volume_pi_pi, Fintype.prod_prod_type]
  exact Finset.prod_congr rfl fun i _ => volume_pi_pi _

end MeasureTheory
