/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Probability.Independence.Basic
public import SLT.StandardForm.Defs
public import SLT.SingularIntegrals.Defs

/-!
# The free energy formula: definitions

[Wat09, §6.2]: the evidence (partition function) and stochastic complexity (free energy), the
limit functional `Y` of [Wat09, Theorem 6.7], and the free energy formula of [Wat09] Main
Theorem 6.2 in the form of [Wat09, Corollary 6.1]. The standard form of the log likelihood ratio
that these use is in `SLT/StandardForm.lean`.

The definitions are those of `SLTChallenge/FreeEnergy.lean`, word for word, and
`SLT/FreeEnergy.lean` proves its theorems.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open Real (exp log)
open scoped ENNReal Manifold

variable {d : ℕ} {X : Type*} [MeasurableSpace X]

section PartitionFunctions

variable {Ω : Type*} [MeasurableSpace Ω]

/-- [Wat09, Definition 6.2]: the evidence (partition function)
`Z_n = ∫_W ∏ p(X_i|w)^β φ(w) dw = ∫_W exp(−nβ L_n(w)) φ(w) dw`. -/
noncomputable def evidence (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ)
    (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w in W, exp (-(n * β * empiricalNegativeLogLikelihood p Xs n ω w)) * φ w

/-- [Wat09, Definition 6.2]: the stochastic complexity (free energy) `F_n = −log Z_n`. -/
noncomputable def freeEnergy (p : (Fin d → ℝ) → X → ℝ) (W : Set (Fin d → ℝ)) (φ : (Fin d → ℝ) → ℝ)
    (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
  -log (evidence p W φ β Xs n ω)

end PartitionFunctions

/-! ## The limit functional `Y` -/

section LimitFunctional

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- [Wat09, Theorem 6.7]: the limit functional on the right-hand side of the theorem, as a
function `Y(χ)` of a continuous function `χ` on the pieces of a chart family `F` in place of the
limit process `ξ`. The sum runs over the essential pieces; the weight of a piece is the
partition of unity `ρ` times the unit of the prior density, so that `ρ` plays the role of the
book's partition of unity in Theorem 6.5(4).

Relation to the source.
* **Translation.** `F.limitFunctional β ρ χ` is the right-hand side of [Wat09, Theorem 6.7] at the
  field $\chi$; the partition of unity `ρ` times the unit of the prior density is the book's
  $\varphi^*_0$. -/
noncomputable def SLTResolution.ChartFamily.limitFunctional (β : ℝ) {R : SLTResolution K φ W}
    (F : R.ChartFamily)
    (ρ : SmoothPartitionOfUnity F.ι 𝓘(ℝ, Fin d → ℝ) R.M F.sublevel)
    (χ : C((α : F.Piece) × cube d α.radius, ℝ)) : ℝ :=
  ∑ᶠ (α : F.Piece) (_ : α.IsEssential),
    let k := α.k
    let h := α.h
    let hk := (F.chart α.chart).active
    let I := criticalCoords k h hk
    let Face := Icc (0 : {j // j ∉ I} → ℝ) (fun _ ↦ α.radius)
    gammaConst k h hk *
      ∫ t in Ioi (0 : ℝ), ∫ v : Face,
        let u := toCriticalFace k h hk (F.chart α.chart).radius_pos.le v
        t ^ (R.rlct - 1) * (∏ j, v.val j ^ ((h j : ℝ) - 2 * k j * R.rlct)) *
          exp (-(β * t) + β * √t * χ ⟨α, u⟩) *
          (ρ α.chart (α.point (u : Fin d → ℝ)) * α.densityUnit (u : Fin d → ℝ))
        ∂(volume.comap Subtype.val)

end LimitFunctional

/-- [Wat09, eq. (6.12)]: the normalised evidence `Z_n^0 = ∫_W exp(−nβ K_n(w)) φ(w) dw`.

Relation to the source.
* **Translation.** `normalizedEvidence p w₀ W φ β Xs n ω` is the $Z_n^0$ of [Wat09, eq. (6.12)] with
  $K_n$ measured from $w_0$; when $q = p(\cdot \mid w_0)$ it is the book's. -/
noncomputable def normalizedEvidence {Ω : Type*} (p : (Fin d → ℝ) → X → ℝ) (w₀ : Fin d → ℝ)
    (W : Set (Fin d → ℝ))
    (φ : (Fin d → ℝ) → ℝ) (β : ℝ) (Xs : ℕ → Ω → X) (n : ℕ) (ω : Ω) : ℝ :=
    let Kn := empiricalExcessLoss p w₀ Xs n ω
  ∫ w in W, exp (-(n * β * Kn w)) * φ w

end SingularLearningTheory
