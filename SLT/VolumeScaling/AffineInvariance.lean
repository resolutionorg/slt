/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

/-!
# Affine invariance of the learning coefficient (K0(ii), affine slice)

Along an affine substitution `x ↦ L x + b` with `det L ≠ 0`, sublevel sets
transform by exact preimage and additive Haar measure scales by
`|det L|⁻¹` — on *arbitrary* sets. Hence the localized sublevel-volume
function transfers by an exact constant multiple, and both predicates
transfer: `HasLLCOn` with `c ↦ |det L|⁻¹·c`, and `HasLLCExponentsOn`
unchanged. This serves the linear coordinate changes of the DLN reduction
(LA0's reindexings have `|det| = 1`; LA2's unitriangular factors likewise);
the full `C¹`-diffeomorphism case with two-sided Jacobian bounds (K4's
blow-up charts) remains open.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]
  (μ : Measure E) [μ.IsAddHaarMeasure]

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Additive Haar measure is translation-invariant on preimages of
arbitrary sets. -/
private theorem measure_preimage_add_right (b : E) (A : Set E) :
    μ ((fun y => y + b) ⁻¹' A) = μ A := by
  have hmb : MeasurableEmbedding (fun y : E => y + b) :=
    (MeasurableEquiv.addRight b).measurableEmbedding
  rw [← hmb.map_apply]
  congr 1
  exact map_add_right_eq_self μ b

/-- Exact sublevel-volume transfer under an affine substitution. -/
private theorem sublevelVol_affine (L : E →ₗ[ℝ] E) (hL : LinearMap.det L ≠ 0) (b : E)
    (K : Set E) (f : E → ℝ) (ε : ℝ) :
    sublevelVol μ ((fun x => L x + b) ⁻¹' K) (fun x => f (L x + b)) ε
      = |(LinearMap.det L)⁻¹| * sublevelVol μ K f ε := by
  unfold sublevelVol
  have hset : ((fun x => L x + b) ⁻¹' K) ∩ {x | f (L x + b) ≤ ε}
      = L ⁻¹' ((fun y => y + b) ⁻¹' (K ∩ {x | f x ≤ ε})) := rfl
  rw [hset, Measure.addHaar_preimage_linearMap μ hL,
    measure_preimage_add_right μ b, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

variable {μ} {K : Set E} {f : E → ℝ}

/-- **K0(ii), affine slice — constant-carrying form**: the full `(λ, θ, c)`
data transfers along affine substitutions, with the constant rescaled by
`|det L|⁻¹`. -/
theorem HasLLCOn.affine {lam theta c : ℝ} (h : HasLLCOn μ K f lam theta c)
    (L : E →ₗ[ℝ] E) (hL : LinearMap.det L ≠ 0) (b : E) :
    HasLLCOn μ ((fun x => L x + b) ⁻¹' K) (fun x => f (L x + b)) lam theta
      (|(LinearMap.det L)⁻¹| * c) := by
  unfold HasLLCOn at h ⊢
  refine Tendsto.congr (fun ε => ?_) (h.const_mul (|(LinearMap.det L)⁻¹|))
  rw [sublevelVol_affine μ L hL b]
  ring

/-- **K0(ii), affine slice — exponent form**: `(λ, θ)` are unchanged by
affine substitutions. -/
theorem HasLLCExponentsOn.affine {lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta)
    (L : E →ₗ[ℝ] E) (hL : LinearMap.det L ≠ 0) (b : E) :
    HasLLCExponentsOn μ ((fun x => L x + b) ⁻¹' K)
      (fun x => f (L x + b)) lam theta := by
  unfold HasLLCExponentsOn at h ⊢
  have hk : |(LinearMap.det L)⁻¹| ≠ 0 := by
    simp [abs_eq_zero, inv_eq_zero, hL]
  have heq : sublevelVol μ ((fun x => L x + b) ⁻¹' K) (fun x => f (L x + b))
      = fun ε => |(LinearMap.det L)⁻¹| * sublevelVol μ K f ε :=
    funext fun ε => sublevelVol_affine μ L hL b K f ε
  rw [heq]
  exact (Asymptotics.isTheta_const_mul_left hk).mpr h

end SingularLearningTheory
