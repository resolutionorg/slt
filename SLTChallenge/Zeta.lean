/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLTChallenge.SingularIntegrals
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Zeta functions and the learning coefficient

Meromorphic continuation of the zeta function and its largest pole ([Wat09, Theorem 6.6 and
Definition 6.4]), and uniqueness of the continuation.
`SLT/SingularIntegrals/Zeta/Defs.lean` has `zetaFunction` word for word, and
`SLT/SingularIntegrals/Zeta.lean` proves the theorems. The other
characterisations of `(λ, m)` ([Wat09, Theorem 7.1]) are in `SLTChallenge/SingularIntegrals.lean`.

The hypotheses are deterministic: `K` analytic and nonnegative, fundamental condition (II),
compactness of `W`, nonzero germs of `K` and `φ` at the zeros of `K`, and positive prior mass on
every sublevel set `{K < ε}`. Neither IID samples nor RFV is needed. The continuation is a
function separate from the defining integral, which need not converge outside `Re z > 0`.
C¹ atlas weights alone do not give continuation to all of `ℂ`, so the statements keep the
smooth and analytic prior assumptions instead of assuming only an atlas.
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

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- **Meromorphic continuation of the zeta function.** The zeta function is holomorphic on
`Re z > 0` and continues to a meromorphic function on `ℂ` whose poles are negative rationals; its
largest pole is `−λ`, of order `m`, where `(λ, m)` is the singularity type.

Relation to the source.
* **Strengthening.** The theorem is about a pair $(K, \varphi)$ alone: the book's Fundamental
  Condition (I) for a model is replaced by the analyticity and nonnegativity of $K$, and the prior
  need not be a probability measure. It adds that the largest pole and its order are the singularity
  type.

Source statement: [Wat09, Theorem 6.6 and Definition 6.4] -/
theorem zetaFunction_meromorphic_continuation
    {d : ℕ} (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions K φ W)
    :
    let ζ := SingularLearningTheory.zetaFunction K φ W
    DifferentiableOn ℂ ζ {z : ℂ | 0 < z.re} ∧
    ∃ (ζext : ℂ → ℂ) (lam : ℝ) (m : ℕ),
      0 < lam ∧ 1 ≤ m ∧ (∃ r : ℚ, (r : ℝ) = lam) ∧
      IsSingularityType K φ W lam m ∧
      -- ζext is the meromorphic extension of ζ
      (∀ z : ℂ, 0 < z.re → ζext z = ζ z) ∧
      MeromorphicOn ζext univ ∧
      -- all poles are negative rational numbers
      (∀ z : ℂ, meromorphicOrderAt ζext z < 0 →
        z.im = 0 ∧ z.re < 0 ∧ ∃ r : ℚ, (r : ℝ) = z.re) ∧
      -- largest pole is -lam and it has order m
      DifferentiableOn ℂ ζext {z : ℂ | -lam < z.re} ∧
      meromorphicOrderAt ζext (-(lam : ℂ)) = -(m : ℤ) :=
  sorry

/-- **Uniqueness of meromorphic continuation**, the uniqueness clause of [Wat09, Theorem 6.6]. Two
continuations agree on a punctured neighbourhood of every point; their values at poles are
arbitrary. -/
theorem zetaFunction_continuation_unique
    {d : ℕ} (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) :
    let ζ := SingularLearningTheory.zetaFunction K φ W
    ∀ ζext₁ ζext₂ : ℂ → ℂ, MeromorphicOn ζext₁ univ → MeromorphicOn ζext₂ univ →
      (∀ z : ℂ, 0 < z.re → ζext₁ z = ζ z) → (∀ z : ℂ, 0 < z.re → ζext₂ z = ζ z) →
      -- equal on every sufficiently small punctured neighbourhood, to account for poles
      ∀ z : ℂ, ζext₁ =ᶠ[𝓝[≠] z] ζext₂ :=
  sorry

end SingularLearningTheory
