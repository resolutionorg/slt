/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import SLT.VolumeScaling.SqueezeReadOff
import SLT.VolumeScaling.Basic
public import SLT.VolumeScaling.Defs
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
# The cover-piece intersection dichotomy at every radius (generic)

A radius-uniform sandwich assembler (`nodeMixedUniform_of_uniform_cover`) asks,
per cover piece, for a dichotomy on the box-radius intersection
`(box-image R) ∩ (piece R)` at every radius `R > 0`: either it carries fixed
sublevel-volume exponents `(lam, theta)` at every radius, or its sublevel volumes
vanish eventually at every radius.

A per-piece scaling typically delivers the dichotomy on the *piece itself*
`P R` at every radius, and the cover is geometrically clean only for `R ≥ 1`
(the small box `box R`, `R < 1`, must be covered by the *unit* pieces).  This
file bridges the two with a generic squeeze: choosing the cover piece
`A R = P R` for `R ≥ 1` and `A R = P 1` for `R < 1`, the intersection
`(box R) ∩ A R` inherits the dichotomy because, for `R < 1`,
`P R ⊆ (box R) ∩ P 1 ⊆ P 1` with the *same* exponents on both endpoints
(`HasLLCExponentsOn.of_squeeze`), and in the vanishing branch the intersection is
dominated by the vanishing unit piece.  For `R ≥ 1` the intersection equals the
piece (`P R ⊆ box R`).

Generic in the measure, the box family `S`, and the piece families `P`, `A`; no
Aoyagi-specific content, so it factors with the rest of `Dln/VolumeScaling/`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set
open scoped Topology ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- **The cover-piece intersection dichotomy at every radius.**  Let `S R` be the
box-image at radius `R`, `P R` a cover piece at radius `R`, and `A R` the
"max-radius" choice (`A R = P R` for `R ≥ 1`, `A R = P 1` for `R < 1`).  If each
piece sits in its box (`P R ⊆ S R`) and shrinks into the unit piece for small
radii (`P R ⊆ P 1` for `R ≤ 1`), and the unit piece's sublevel sets are finite,
then the per-piece dichotomy on `P` transfers to the box-intersection
`(S R) ∩ (A R)` at every positive radius.  The radius-`< 1` carrier case is a
squeeze `P R ⊆ (S R) ∩ P 1 ⊆ P 1`; the vanishing case is monotonicity. -/
theorem coverPiece_inter_dichotomy {μ : Measure α} {f : α → ℝ} {lam theta : ℝ}
    (S P A : ℝ → Set α)
    (hA1 : ∀ R, 1 ≤ R → A R = P R) (hA0 : ∀ R, R < 1 → A R = P 1)
    (hsub : ∀ R, 0 < R → P R ⊆ S R) (hmono : ∀ R, 0 < R → R ≤ 1 → P R ⊆ P 1)
    (hfin : ∀ ε, μ (P 1 ∩ {x | f x ≤ ε}) ≠ ⊤)
    (hdich : (∀ R, 0 < R → HasLLCExponentsOn μ (P R) f lam theta)
        ∨ (∀ R, 0 < R → ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVol μ (P R) f ε = 0)) :
    (∀ R, 0 < R → HasLLCExponentsOn μ ((S R) ∩ A R) f lam theta)
      ∨ (∀ R, 0 < R → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          sublevelVol μ ((S R) ∩ A R) f ε = 0) := by
  rcases hdich with hcar | hvan
  · refine Or.inl (fun R hR => ?_)
    by_cases h1 : 1 ≤ R
    · rw [hA1 R h1, Set.inter_eq_self_of_subset_right (hsub R hR)]
      exact hcar R hR
    · have hRlt : R < 1 := not_le.mp h1
      rw [hA0 R hRlt]
      have hPRsub : P R ⊆ (S R) ∩ P 1 :=
        Set.subset_inter (hsub R hR) (hmono R hR hRlt.le)
      have hmidsub : (S R) ∩ P 1 ⊆ P 1 := Set.inter_subset_right
      refine HasLLCExponentsOn.of_squeeze (hcar R hR) (hcar 1 one_pos)
        (Filter.Eventually.of_forall (sublevelVol_nonneg _ _ _))
        (Filter.Eventually.of_forall (fun ε => ?_))
        (Filter.Eventually.of_forall (fun ε => ?_))
      · simp only [sublevelVol]
        exact ENNReal.toReal_mono
          (ne_top_of_le_ne_top (hfin ε)
            (measure_mono (Set.inter_subset_inter_left _ hmidsub)))
          (measure_mono (Set.inter_subset_inter_left _ hPRsub))
      · simp only [sublevelVol]
        exact ENNReal.toReal_mono (hfin ε)
          (measure_mono (Set.inter_subset_inter_left _ hmidsub))
  · refine Or.inr (fun R hR => ?_)
    by_cases h1 : 1 ≤ R
    · rw [hA1 R h1, Set.inter_eq_self_of_subset_right (hsub R hR)]
      exact hvan R hR
    · have hRlt : R < 1 := not_le.mp h1
      rw [hA0 R hRlt]
      have hmidsub : (S R) ∩ P 1 ⊆ P 1 := Set.inter_subset_right
      exact eventually_sublevelVol_eq_zero_of_le
        (Filter.Eventually.of_forall (fun ε => by
          simp only [sublevelVol]
          exact ENNReal.toReal_mono (hfin ε)
            (measure_mono (Set.inter_subset_inter_left _ hmidsub))))
        (hvan 1 one_pos)

/-- **The lower-squeeze cover-piece intersection dichotomy.**  A generalization of
`coverPiece_inter_dichotomy` for cover families that *overshoot* their box: an orbit
piece under marked scaling lies in `S (R·R)`, not `S R`, for `R > 1`, so the
`hsub : P R ⊆ S R` hypothesis there fails.  Given instead a *lower family*
`L R ⊆ (S R) ∩ A R` carrying the exponents alongside the upper family `A R`, and
finiteness of `A R`'s sublevel sets, the dichotomy transfers to `(S R) ∩ A R` at
every positive radius.  The carrier case is the squeeze
`L R ⊆ (S R) ∩ A R ⊆ A R` (`HasLLCExponentsOn.of_squeeze`); the vanishing case is
monotonicity into `A R`.  Uniform in `R` — the `1 ≤ R` split lives in the caller's
choice of the `A`/`L` families. -/
theorem coverPiece_inter_dichotomy_of_lower_squeeze {μ : Measure α} {f : α → ℝ}
    {lam theta : ℝ} (S A L : ℝ → Set α)
    (hL : ∀ R, 0 < R → L R ⊆ (S R) ∩ A R)
    (hfinA : ∀ R, 0 < R → ∀ ε, μ (A R ∩ {x | f x ≤ ε}) ≠ ⊤)
    (hdich : (∀ R, 0 < R → HasLLCExponentsOn μ (L R) f lam theta
                            ∧ HasLLCExponentsOn μ (A R) f lam theta)
        ∨ (∀ R, 0 < R → ∀ᶠ ε in 𝓝[>] (0 : ℝ), sublevelVol μ (A R) f ε = 0)) :
    (∀ R, 0 < R → HasLLCExponentsOn μ ((S R) ∩ A R) f lam theta)
      ∨ (∀ R, 0 < R → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          sublevelVol μ ((S R) ∩ A R) f ε = 0) := by
  rcases hdich with hcar | hvan
  · refine Or.inl (fun R hR => ?_)
    obtain ⟨hLexp, hAexp⟩ := hcar R hR
    have hlowsub : L R ⊆ (S R) ∩ A R := hL R hR
    have hupsub : (S R) ∩ A R ⊆ A R := Set.inter_subset_right
    refine HasLLCExponentsOn.of_squeeze hLexp hAexp
      (Filter.Eventually.of_forall (sublevelVol_nonneg _ _ _))
      (Filter.Eventually.of_forall (fun ε => ?_))
      (Filter.Eventually.of_forall (fun ε => ?_))
    · simp only [sublevelVol]
      exact ENNReal.toReal_mono
        (ne_top_of_le_ne_top (hfinA R hR ε)
          (measure_mono (Set.inter_subset_inter_left _ hupsub)))
        (measure_mono (Set.inter_subset_inter_left _ hlowsub))
    · simp only [sublevelVol]
      exact ENNReal.toReal_mono (hfinA R hR ε)
        (measure_mono (Set.inter_subset_inter_left _ hupsub))
  · refine Or.inr (fun R hR => ?_)
    have hupsub : (S R) ∩ A R ⊆ A R := Set.inter_subset_right
    exact eventually_sublevelVol_eq_zero_of_le
      (Filter.Eventually.of_forall (fun ε => by
        simp only [sublevelVol]
        exact ENNReal.toReal_mono (hfinA R hR ε)
          (measure_mono (Set.inter_subset_inter_left _ hupsub))))
      (hvan R hR)

end SingularLearningTheory
