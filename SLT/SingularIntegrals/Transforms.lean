/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.StateDensity
import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Analysis.MellinTransform
public import Mathlib.Analysis.CStarAlgebra.Classes
public import SLT.Analysis.Mellin.Defs
public import SLT.SingularIntegrals.Zeta.Defs

/-!
# Integral transforms and the zeta function

Formalises [Hit26, Section 3.1.1]. The state density
function `ν(t; φ)` sits between the zeta function and the normalised partition
function, one Mellin transform to the left and one Laplace transform to the
right:

    ζ(z; φ)  ←—𝓜—  ν(t; φ)  —𝓛→  Z₀(n; φ)

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 3.1.6] | `mellinTransform` |
| [Hit26, Definition 3.1.7] | `laplaceTransform` |
| [Hit26, Equation (3.1.2)] | `zetaFunction` |
| [Hit26, Equation (3.0.3)] | `normalizedPartitionFunction` |
| [Hit26, Theorem 3.1.8] | |
| | `mellinTransform_isStateDensity`, |
| | `laplaceTransform_isStateDensity` |

## Conventions

Two places where [Hit26]'s conventions differ from Mathlib's, or from the
thesis's own definitions elsewhere:

* **Mellin exponent.** [Hit26]'s `(𝓜ν)(z) = ∫₀^∞ ν(t) t^z dt` uses the
  exponent `t^z`, whereas Mathlib's `mellin` uses the standard `t^(s-1)`. So the
  thesis's transform at `z` is Mathlib's at `z + 1`; `mellinTransform_eq_mellin`
  records this.

* **The `β` in the Laplace transform.** [Hit26] defines
  `Z₀(n; φ) = ∫_W exp(-nβK(w)) φ(w) dw` with an inverse temperature `β`, but
  states part 2 of
  [Hit26, Theorem 3.1.8] as
  `(𝓛ν)(n) = Z₀(n; φ)`. That holds only for `β = 1`; in general it is
  `(𝓛ν)(nβ) = Z₀(n; φ)`, which is what `laplaceTransform_isStateDensity` proves.

Both transforms are stated here as honest integrals. [Hit26] extends them "by
meromorphic continuation elsewhere"; that continuation is not formalised, and
nothing in the free energy formula's proof needs it — the proof reaches `ν`
through the explicit normal-crossing computations of `NormalCrossing.lean`, where
the transforms are evaluated on their strip of convergence.
-/

public section

open MeasureTheory Set Complex

namespace SingularLearningTheory

variable {E : Type*} [MeasureSpace E] {K φ : E → ℝ} {W : Set E} {ν : ℝ → ℝ}

/-- [Hit26, Definition 3.1.7]: `(𝓛ν)(s) = ∫₀^∞ ν(t) e^{-st} dt`. -/
@[expose] noncomputable def laplaceTransform (ν : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ t in Ioi (0 : ℝ), Complex.exp (-(s * t)) * ν t

/-- [Hit26, Equation (3.0.3)]:
`Z₀(n; φ) = ∫_W exp(-nβK(w)) φ(w) dw`. -/
@[expose] noncomputable def normalizedPartitionFunction (K φ : E → ℝ) (W : Set E)
    (β n : ℝ) : ℝ :=
  ∫ w in W, Real.exp (-(n * β * K w)) * φ w

/-- [Hit26]'s Mellin transform is Mathlib's, shifted by one: [Hit26]
integrates `ν(t) t^z` where Mathlib's `mellin` integrates `t^(s-1) • ν t`. -/
theorem mellinTransform_eq_mellin (ν : ℝ → ℝ) (z : ℂ) :
    mellinTransform ν z = mellin (fun t ↦ (ν t : ℂ)) (z + 1) := by
  rw [mellinTransform, mellin]
  exact setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ by
    rw [add_sub_cancel_right, smul_eq_mul]

/-- `t ↦ t^z` is measurable as a map `ℝ → ℂ`. It is not continuous at `0` unless
`0 < z.re`, so this goes through the definition of `cpow` rather than continuity.
No thesis counterpart; used by `mellinTransform_isStateDensity`. -/
theorem _root_.measurable_ofReal_cpow (z : ℂ) : Measurable (fun t : ℝ ↦ ((t : ℂ) ^ z)) := by
  have hrw : (fun t : ℝ ↦ ((t : ℂ) ^ z))
      = fun t : ℝ ↦ if (t : ℂ) = 0 then (if z = 0 then 1 else 0)
                    else Complex.exp (Complex.log t * z) :=
    funext fun t ↦ Complex.cpow_def _ _
  rw [hrw]
  refine Measurable.ite ?_ measurable_const
    (Complex.measurable_exp.comp
      ((Complex.measurable_log.comp Complex.measurable_ofReal).mul_const z))
  simp [Complex.ofReal_eq_zero]

section Transforms

variable (h : IsStateDensity K φ W ν)
include h

/-- [Hit26, Theorem 3.1.8],
part 1: the Mellin transform of the state density function is the zeta function.

This is [Wat09, Theorem 4.4] (`IsStateDensity.integral_mul`) applied to `f t = t^z`. -/
theorem mellinTransform_isStateDensity (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (z : ℂ)
    (hint : Integrable fun t : ℝ ↦ ν t • ((t : ℂ) ^ z)) :
    mellinTransform ν z = zetaFunction K φ W z := by
  have key := IsStateDensity.setIntegral_smul h hK hφ hφ0 hK0
    (measurable_ofReal_cpow z).aestronglyMeasurable hint
  rw [mellinTransform, zetaFunction,
    show (fun t : ℝ ↦ ((t : ℂ) ^ z) * ν t) = fun t : ℝ ↦ ν t • ((t : ℂ) ^ z) from
      funext fun t ↦ by rw [Complex.real_smul]; ring]
  refine key.trans (integral_congr_ae (.of_forall fun w ↦ ?_))
  change φ w • ((K w : ℂ) ^ z) = (K w : ℂ) ^ z * (φ w : ℂ)
  rw [Complex.real_smul]
  ring

/-- [Hit26, Theorem 3.1.8],
part 2: the Laplace transform of the state density function is the normalised
partition function.

This is [Wat09, Theorem 4.4] applied to `f t = e^{-st}`. [Hit26] writes the conclusion as
`(𝓛ν)(n) = Z₀(n; φ)`, which needs `β = 1`; in general the transform is evaluated
at `nβ`. -/
theorem laplaceTransform_isStateDensity (hK : Measurable K)
    (hφ : AEMeasurable φ (volume.restrict W)) (hφ0 : 0 ≤ᵐ[volume.restrict W] φ)
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (β n : ℝ)
    (hint : Integrable fun t : ℝ ↦ ν t • Complex.exp (-(((n * β : ℝ) : ℂ) * t))) :
    laplaceTransform ν ((n * β : ℝ) : ℂ)
      = ((normalizedPartitionFunction K φ W β n : ℝ) : ℂ) := by
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ ↦ Complex.exp (-(((n * β : ℝ) : ℂ) * t))) volume := by fun_prop
  have key := IsStateDensity.setIntegral_smul h hK hφ hφ0 hK0 hmeas hint
  rw [laplaceTransform, normalizedPartitionFunction,
    show (fun t : ℝ ↦ Complex.exp (-(((n * β : ℝ) : ℂ) * t)) * ν t)
        = fun t : ℝ ↦ ν t • Complex.exp (-(((n * β : ℝ) : ℂ) * t)) from
      funext fun t ↦ by rw [Complex.real_smul]; ring,
    ]
  refine key.trans (Eq.trans (integral_congr_ae (.of_forall fun w ↦ ?_)) integral_ofReal)
  change φ w • Complex.exp (-(((n * β : ℝ) : ℂ) * (K w : ℂ)))
      = ((Real.exp (-(n * β * K w)) * φ w : ℝ) : ℂ)
  rw [Complex.real_smul]
  push_cast
  ring

end Transforms

end SingularLearningTheory
