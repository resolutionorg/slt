/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals
public import SLT.SingularIntegrals.Transforms
public import SLT.Analysis.Meromorphic.Uniqueness
public import SLT.SingularIntegrals.Zeta.FromResolution
public import SLT.SingularIntegrals.Volume.Atlas
public import SLT.SingularIntegrals.Volume.Consequences

/-!
# Meromorphic continuation of the zeta function

The proved counterpart of `SLTChallenge/Zeta.lean`. A resolution atlas with smooth chart
weights gives the continuation with negative rational poles and identifies the largest pole
with the singularity type. Uniqueness follows from the identity principle for meromorphic
functions.
-/

public section

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
      (∀ z : ℂ, 0 < z.re → ζext z = ζ z) ∧
      MeromorphicOn ζext univ ∧
      (∀ z : ℂ, meromorphicOrderAt ζext z < 0 →
        z.im = 0 ∧ z.re < 0 ∧ ∃ r : ℚ, (r : ℝ) = z.re) ∧
      DifferentiableOn ℂ ζext {z : ℂ | -lam < z.re} ∧
      meromorphicOrderAt ζext (-(lam : ℂ)) = -(m : ℤ) := by
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  intro ζ
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun w hw ↦ II.nonneg hw
  have hφc := II.continuousOn
  have hφi : IntegrableOn φ W := hφc.integrableOn_compact hW
  refine ⟨zetaFunction_differentiableOn_of_continuousOn hW hKa.continuousOn hK hφi hφ, ?_⟩
  obtain ⟨A⟩ := exists_atlasData_of_sublevel_mass hW hKa hK II hKg hφg hvol
  have := A.nonempty_ι hvol
  let R := A.toResolutionAtlas
  obtain ⟨α, hα⟩ := R.exists_isEssential
  obtain ⟨Z, hZeq, hZm, hZp, hZd, hZo⟩ := R.exists_zetaContinuation_of_smooth_weights
    hW hKa.continuousOn hK hφi hφ A.exists_smooth_weight_extension
    ⟨α, hα, A.weight_pos α⟩
  exact ⟨Z, R.rlct, R.mult, R.rlct_pos, R.mult_pos, R.rlct_rational,
    A.toNondegenerateResolutionAtlas.isSingularityType_of_continuousOn hW hKa.continuousOn hφ hφc,
    hZeq, hZm, hZp, hZd, hZo⟩

/-- **Uniqueness of meromorphic continuation**, the uniqueness clause of [Wat09, Theorem 6.6]. Two
continuations agree on a punctured neighbourhood of every point; their values at poles are
arbitrary. -/
theorem zetaFunction_continuation_unique
    {d : ℕ} (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) :
    let ζ := SingularLearningTheory.zetaFunction K φ W
    ∀ ζext₁ ζext₂ : ℂ → ℂ, MeromorphicOn ζext₁ univ → MeromorphicOn ζext₂ univ →
      (∀ z : ℂ, 0 < z.re → ζext₁ z = ζ z) → (∀ z : ℂ, 0 < z.re → ζext₂ z = ζ z) →
      ∀ z : ℂ, ζext₁ =ᶠ[𝓝[≠] z] ζext₂ :=
  fun _ _ hZ₁ hZ₂ h₁ h₂ ↦
    hZ₁.eventuallyEq_nhdsNE_of_eqOn_re_gt hZ₂ 0 fun z hz ↦ (h₁ z hz).trans (h₂ z hz).symm

end SingularLearningTheory
