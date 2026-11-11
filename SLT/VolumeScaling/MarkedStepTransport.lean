/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.MarkedAtoms
public import SLT.PartialResolution.MarkedTransport
import SLT.PartialResolution.ExactTransport
public import SLT.PartialResolution.Defs

/-!
# The per-step transport certificate (plan atom 3.2.9)

A single step of Aoyagi's resolution is a marked-scaling of one block (the pivot
coordinate `x_u` multiplies the marked block coordinates) followed by the shears on
that block (each marked coordinate absorbs a function of the non-target
coordinates). The marked-scaling transports the volume with density `|x_u|^n`,
where `n` is the block size, and a shear is volume-preserving (density `1`). This
file composes the two committed transports into the per-step certificate: the
composite transports the volume on the whole space with the single-coordinate
monomial density `|x_u|^n` — the scale's density, the shear contributing nothing.

The proof is one application of the committed composition lemma
`VolumeScaling.TransportsToOn.comp` (densities multiply along a composite, the inner
map sending the source set into the outer map's domain — here trivially, both are
the whole space) followed by simplifying the trailing factor `1`. It depends only on
Mathlib and the marked-scale and marked-shear transports (`SLT/VolumeScaling/MarkedAtoms.lean`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory
open Analytic

variable {d n : ℕ}

/-- **Plan atom 3.2.9.** A marked-scaling of a block (pivot `u`, block embedding `b`
of size `n`, the pivot not lying in the block) followed by a marked shear on the same
block transports the volume on the whole space with density `|x_u|^n`: the
marked-scaling contributes `|x_u|^n`, the shear contributes `1`. -/
theorem _root_.Analytic.transportsToOn_markedStep (u : Fin d) (b : Fin n ↪ Fin d)
    (hbu : ∀ i, b i ≠ u) (c : (TargetCompl b → ℝ) → Fin n → ℝ)
    (hc : Measurable c) :
    TransportsToOn volume volume Set.univ
      (fun x => markedShear b c (markedScale u b x)) (markedDensity u n) := by
  have h := (transportsToOn_markedScale u b hbu).comp
    (transportsToOn_markedShear b c hc) (mapsTo_univ _ _)
  simpa only [mul_one] using h

end SingularLearningTheory
