/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Defs
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Zeta functions: definitions

Meromorphic continuation of the zeta function and its largest pole
([Wat09, Theorem 6.6 and Definition 6.4]), and uniqueness of the continuation. The other
characterisations of `(λ, m)` ([Wat09, Theorem 7.1]) are in `SLT/SingularIntegrals.lean`.

The hypotheses are deterministic: `K` analytic and nonnegative, fundamental condition (II),
compactness of `W`, nonzero germs of `K` and `φ` at the zeros of `K`, and positive prior mass on
every sublevel set `{K < ε}`. Neither IID samples nor RFV is needed. The continuation is a
function separate from the defining integral, which need not converge outside `Re z > 0`.
C¹ atlas weights alone do not give continuation to all of `ℂ`, so the statements keep the
smooth and analytic prior assumptions instead of assuming only an atlas.

The definitions are those of `SLTChallenge/Zeta.lean`, word for word, and
`SLT/SingularIntegrals/Zeta.lean` proves its theorems.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory Set

variable {E : Type*} [MeasureSpace E]

/-- [Wat09, eq. (6.15)]: `ζ(z) = ∫_W K(w)^z φ(w) dw`. Restated verbatim from the library
under the library's name. -/
noncomputable def zetaFunction (K φ : E → ℝ) (W : Set E) (z : ℂ) : ℂ :=
  ∫ w in W, (K w : ℂ) ^ z * φ w

end SingularLearningTheory

