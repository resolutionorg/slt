/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import SLT.VolumeScaling.LFoldProduct
import SLT.VolumeScaling.PowerComp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# The equal-exponent block

The scalar product chain (`hasLLCOn_prod_sq`, `LFoldProduct`) composed with the power
reparametrization (`PowerComp`): on the unit cube in `L+1` variables, `(∏ᵢ |zᵢ|)^{1/λ}` has
volume-scaling exponents `(λ, L+1)`. This is the model case of a block of coordinates all
attaining the same exponent `λ`: the multiplicity `θ = L+1` is the block size. `SignedPower`
uses it.
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

/-- **The equal-exponent block**: on the unit cube, `(∏ᵢ |zᵢ|)^{1/λ}` has volume-scaling
exponents `(λ, L+1)`. -/
theorem hasLLCExponentsOn_prod_abs_rpow (L : ℕ) {lam : ℝ}
    (hlam : 0 < lam) :
    HasLLCExponentsOn volume
      (Set.univ.pi fun _ : Fin (L + 1) => Icc (-1 : ℝ) 1)
      (fun z => (∏ i, |z i|) ^ (1 / lam)) lam (L + 1) := by
  have h0 : HasLLCExponentsOn volume
      (Set.univ.pi fun _ : Fin (L + 1) => Icc (-1 : ℝ) 1)
      (fun z => (∏ i, z i) ^ 2) (1 / 2) (L + 1) :=
    (hasLLCOn_prod_sq L).hasLLCExponentsOn (by positivity)
  have happ := h0.rpow_comp
    (c := 1 / (2 * lam)) (by positivity)
    (fun z _ => sq_nonneg _)
  have hfun : (fun z : Fin (L + 1) → ℝ =>
      (((∏ i, z i) ^ 2 : ℝ)) ^ (1 / (2 * lam)))
      = fun z => (∏ i, |z i|) ^ (1 / lam) := by
    funext z
    rw [show ((∏ i, z i) ^ 2 : ℝ) = (∏ i, |z i|) ^ (2 : ℕ) by
        rw [← Finset.abs_prod, sq_abs],
      ← Real.rpow_natCast (∏ i, |z i|) 2,
      ← Real.rpow_mul (Finset.prod_nonneg fun i _ => abs_nonneg _),
      show ((2 : ℕ) : ℝ) * (1 / (2 * lam)) = 1 / lam by
        push_cast
        field_simp]
  have hexp : (1 : ℝ) / 2 / (1 / (2 * lam)) = lam := by
    field_simp
  rw [hfun, hexp] at happ
  exact happ

end SingularLearningTheory
