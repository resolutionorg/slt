/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# The single-piece squeeze read-off

The per-piece chain of the volume computation sandwiches one piece's sublevel volume between a
child chart's sublevel volumes at two box radii. When both bounds carry the *same* exponents —
a radius-uniform child read-off guarantees this — the squeezed piece carries them too; and when
the upper bound vanishes eventually, so does the piece. This file provides the two read-offs as
generic asymptotics on `𝓝[>] 0`, with no content beyond the `HasLLCExponentsOn` wrapper, and
the box sandwich `HasLLCExponentsOn.of_sandwich` between two concentric regions used by the
chart-local read-off (`ChartLocal`, `CompactLocalize`).
-/

public section

open MeasureTheory Set Asymptotics _root_.Filter
open scoped ENNReal Topology

namespace SingularLearningTheory

/-- **The nonnegative squeeze for `IsTheta`**: a nonnegative function
sandwiched between two functions each `Θ`-equivalent to `φ` is itself
`Θ`-equivalent to `φ`.  Both arms ride the bound through the
nonnegativity (norms drop to the values). -/
theorem _root_.isTheta_of_nonneg_squeeze {v l h φ : ℝ → ℝ}
    (hv : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ v ε)
    (hl : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ l ε)
    (hle₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), l ε ≤ v ε)
    (hle₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), v ε ≤ h ε)
    (hlθ : l =Θ[𝓝[>] (0 : ℝ)] φ) (hhθ : h =Θ[𝓝[>] (0 : ℝ)] φ) :
    v =Θ[𝓝[>] (0 : ℝ)] φ := by
  constructor
  · refine IsBigO.trans ?_ hhθ.1
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hv, hle₂] with ε hvε hleε
    rw [Real.norm_of_nonneg hvε, Real.norm_of_nonneg (le_trans hvε hleε),
      one_mul]
    exact hleε
  · refine hlθ.2.trans ?_
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hl, hle₁] with ε hlε hleε
    rw [Real.norm_of_nonneg hlε, Real.norm_of_nonneg (le_trans hlε hleε),
      one_mul]
    exact hleε

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α}
  {f : α → ℝ}

/-- **The single-piece squeeze read-off**: a sublevel volume
sandwiched between two functions carrying the LLC exponents
`(lam, theta)` carries them too. -/
theorem HasLLCExponentsOn.of_squeeze {Vlo Vhi : ℝ → ℝ} {lam theta : ℝ}
    (hlo : Vlo =Θ[𝓝[>] (0 : ℝ)] llcScale lam theta)
    (hhi : Vhi =Θ[𝓝[>] (0 : ℝ)] llcScale lam theta)
    (hlo_nonneg : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ Vlo ε)
    (hle₁ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Vlo ε ≤ sublevelVol μ K f ε)
    (hle₂ : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVol μ K f ε ≤ Vhi ε) :
    HasLLCExponentsOn μ K f lam theta :=
  isTheta_of_nonneg_squeeze
    (Eventually.of_forall (sublevelVol_nonneg μ K f)) hlo_nonneg hle₁ hle₂
    hlo hhi

/-- **The eventual-zero squeeze**: a nonnegative function dominated by
an eventually-vanishing one vanishes eventually. -/
theorem _root_.eventually_eq_zero_of_le {v h : ℝ → ℝ}
    (hv : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ v ε)
    (hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), v ε ≤ h ε)
    (h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), h ε = 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), v ε = 0 := by
  filter_upwards [hv, hle, h0] with ε hvε hleε h0ε
  rw [h0ε] at hleε
  exact le_antisymm hleε hvε

/-- The eventual-zero squeeze for a sublevel volume under an
eventually-vanishing bound. -/
theorem eventually_sublevelVol_eq_zero_of_le {Vhi : ℝ → ℝ}
    (hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVol μ K f ε ≤ Vhi ε)
    (h0 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Vhi ε = 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVol μ K f ε = 0 :=
  eventually_eq_zero_of_le
    (Eventually.of_forall (sublevelVol_nonneg μ K f)) hle h0

/-- **Box-sandwich.** A set `S` with `K₁ ⊆ S ⊆ K₂`, where both bounding sets
carry the sublevel-volume exponents `(λ, θ)` of `f` and the outer set has finite
measure, inherits those exponents. The intended use takes `K₁`, `K₂` to be two
concentric centered cubes and `S` a region trapped between them. -/
theorem HasLLCExponentsOn.of_sandwich {lam theta : ℝ} {K₁ K₂ S : Set α}
    (h₁ : HasLLCExponentsOn μ K₁ f lam theta)
    (h₂ : HasLLCExponentsOn μ K₂ f lam theta)
    (hsub₁ : K₁ ⊆ S) (hsub₂ : S ⊆ K₂) (hfin : μ K₂ ≠ ∞) :
    HasLLCExponentsOn μ S f lam theta := by
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hfin (measure_mono hsub₂)
  exact HasLLCExponentsOn.of_squeeze h₁ h₂
    (Eventually.of_forall (sublevelVol_nonneg μ K₁ f))
    (Eventually.of_forall fun ε => sublevelVol_mono_set hsub₁ hSfin f ε)
    (Eventually.of_forall fun ε => sublevelVol_mono_set hsub₂ hfin f ε)

end SingularLearningTheory
