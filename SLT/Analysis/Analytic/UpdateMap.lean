/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Analysis.Calculus.ContDiff.Defs
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
# Maps of `ℝ^d` that change one coordinate

The coordinate change of [Wat09, Remark 2.7] ([Hit26,
Theorem 3.3.1], absorbing the unit of `K ∘ g` into
one coordinate) has the form `u ↦ update u j (f u)`: every coordinate but the `j`-th is kept. Its
Jacobian matrix is the identity except for row `j`, so its determinant is the `(j, j)` entry, `∂_j
f`. No thesis counterpart for the individual lemmas.
-/

public section

namespace SingularLearningTheory

open Set Filter Topology

variable {d : ℕ}

/-- The determinant of the identity matrix with row `j` replaced by `r` is `r j`. -/
private theorem _root_.Matrix.det_one_updateRow {ι : Type*} [Fintype ι] [DecidableEq ι] {R : Type*}
    [CommRing R]
    (j : ι) (r : ι → R) : ((1 : Matrix ι ι R).updateRow j r).det = r j := by
  have hr : r = ∑ k, r k • (1 : Matrix ι ι R) k := by
    funext i
    simp [Matrix.one_apply]
  rw [hr, Matrix.det_updateRow_sum, Matrix.det_one, smul_eq_mul, mul_one]
  simp [Matrix.one_apply]

/-- The map that replaces the `j`-th coordinate of `u` by `f u`. -/
@[expose] def _root_.updateMap (j : Fin d) (f : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) : Fin d → ℝ :=
  Function.update u j (f u)

/-- The derivative of `updateMap j f` at a point where `f` has derivative `f'`: the identity on
the coordinates `i ≠ j`, and `f'` in the `j`-th coordinate. -/
@[expose] noncomputable def _root_.updateMapDeriv (j : Fin d) (f' : (Fin d → ℝ) →L[ℝ] ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ if i = j then f' else ContinuousLinearMap.proj i

theorem _root_.updateMap_apply (j : Fin d) (f : (Fin d → ℝ) → ℝ) (u : Fin d → ℝ) (i : Fin d) :
    updateMap j f u i = if i = j then f u else u i := by
  simp only [updateMap, Function.update_apply]

theorem _root_.hasFDerivAt_updateMap {j : Fin d} {f : (Fin d → ℝ) → ℝ}
    {f' : (Fin d → ℝ) →L[ℝ] ℝ} {u : Fin d → ℝ} (hf : HasFDerivAt f f' u) :
    HasFDerivAt (updateMap j f) (updateMapDeriv j f') u := by
  have h : updateMap j f = fun u i ↦ if i = j then f u else u i := by
    funext u i
    exact updateMap_apply j f u i
  rw [h, updateMapDeriv]
  refine hasFDerivAt_pi.2 fun i ↦ ?_
  by_cases hi : i = j
  · simp only [hi, ite_true]
    exact hf
  · simp only [hi, ite_false]
    exact hasFDerivAt_apply i u

/-- The Jacobian determinant of `updateMap j f` is the partial derivative `∂_j f`. -/
theorem _root_.det_updateMapDeriv (j : Fin d) (f' : (Fin d → ℝ) →L[ℝ] ℝ) :
    (updateMapDeriv j f').det = f' (Pi.single j 1) := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix',
    ← Matrix.det_one_updateRow j fun i ↦ f' (Pi.single i 1)]
  congr 1
  ext i k
  simp only [LinearMap.toMatrix'_apply, updateMapDeriv, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.pi_apply, Matrix.updateRow_apply, Matrix.one_apply]
  split_ifs with h h' <;> simp_all [eq_comm]

theorem _root_.analyticAt_updateMap {j : Fin d} {f : (Fin d → ℝ) → ℝ} {u : Fin d → ℝ}
    (hf : AnalyticAt ℝ f u) : AnalyticAt ℝ (updateMap j f) u := by
  refine analyticAt_pi_iff.2 fun i ↦ ?_
  by_cases hi : i = j
  · simp only [updateMap_apply, hi, ite_true]
    exact hf
  · simp only [updateMap_apply, hi, ite_false]
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i).analyticAt _

theorem _root_.contDiff_updateMap {j : Fin d} {f : (Fin d → ℝ) → ℝ} {n : WithTop ℕ∞}
    (hf : ContDiff ℝ n f) : ContDiff ℝ n (updateMap j f) := by
  refine contDiff_pi.2 fun i ↦ ?_
  by_cases hi : i = j
  · simp only [updateMap_apply, hi, ite_true]
    exact hf
  · simp only [updateMap_apply, hi, ite_false]
    exact contDiff_apply ℝ (fun _ ↦ ℝ) i

end SingularLearningTheory
