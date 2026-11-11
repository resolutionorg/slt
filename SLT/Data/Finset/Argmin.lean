/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.BooleanAlgebra
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
# Aggregate lift under a surjection with section (route (a), D4 kernel)

A generic order-theoretic fact, with no chart / cover / resolution dependency: it lifts a
per-element comparison between two finite families to an equality of their two combinatorial
aggregates — the least value (`Finset.inf'`), and the greatest of a second statistic over the
elements attaining that least value (`Finset.sup'` over the argmin-filtered set).

This is the kernel route (a)'s step D4 instantiates.  The "full" family is indexed by `ι`, the
"compressed" family by `κ`; they are related by a surjection `f : ι → κ` with a section
`s : κ → ι`.  Writing `glam`/`gth` for the full family's least-exponent / multiplicity and
`hlam`/`hth` for the compressed family's, the hypotheses are exactly the per-pivot exponent
comparison of `Dln/Network/PerPivotExponents.lean` together with the structural identities the
cover bundle supplies at the representative leaves:

* `H1`        — `hlam (f a) ≤ glam a`            (representative `λ` ≤ full `λ`; the D2a lift),
* `H2`        — at equal `λ`, `gth a ≤ hth (f a)` (full `θ` ≤ representative `θ`; the D3a lift),
* `Hlam_sec`  — `glam (s b) = hlam b`            (the representative leaf's `λ` is the
                                                  compressed `λ`; a reflexive identity, not a
                                                  cross-chart comparison),
* `Hth_sec`   — `gth (s b) = hth b`              (likewise for `θ`).

The conclusion identifies the two `inf'` aggregates (`combLam_full = combLam_comp`) and the two
`sup'`-over-argmin aggregates (`combTheta_full = combTheta_comp`), matching the definitions of
`combLam`/`combTheta` in `Dln/VolumeScaling/Interface.lean`.  Surjectivity of `f` is implied by
the section and is not needed separately.
-/

public section

namespace Finset

open Finset

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [Nonempty ι] [Nonempty κ]
variable {α : Type*} [LinearOrder α] {β : Type*} [LinearOrder β]

/-- The argmin set — the elements attaining the family's least value — is nonempty, because the
infimum over a nonempty finite family is attained. -/
theorem argmin_univ_nonempty (g : ι → α) :
    (univ.filter (fun a => g a = univ.inf' univ_nonempty g)).Nonempty := by
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := ι)) g
  exact ⟨a, mem_filter.mpr ⟨mem_univ a, ha.symm⟩⟩

/-- **The least-value half (route-(a) D2b kernel).** The two infima coincide. This needs only
the full-side domination `H1` and the section's `λ`-identity `Hlam_sec` — not the multiplicity
hypotheses — so route (a)'s global-`λ` step can consume it on its own. -/
theorem inf'_univ_eq_of_le_of_section
    (f : ι → κ) (s : κ → ι) (glam : ι → α) (hlam : κ → α)
    (H1 : ∀ a, hlam (f a) ≤ glam a)
    (Hlam_sec : ∀ b, glam (s b) = hlam b) :
    univ.inf' univ_nonempty glam = univ.inf' univ_nonempty hlam := by
  apply le_antisymm
  · rw [Finset.le_inf'_iff]
    intro b _
    calc univ.inf' univ_nonempty glam
        ≤ glam (s b) := Finset.inf'_le glam (mem_univ (s b))
      _ = hlam b := Hlam_sec b
  · rw [Finset.le_inf'_iff]
    intro a _
    calc univ.inf' univ_nonempty hlam
        ≤ hlam (f a) := Finset.inf'_le hlam (mem_univ (f a))
      _ ≤ glam a := H1 a

/-- **The multiplicity half (route-(a) D3b kernel).** The greatest second-statistics over the
two argmin sets coincide. Uses `inf'_univ_eq_of_le_of_section` to align the minima, then the
full-side domination
(`H1`, `H2`) for `≤` and the section identities (`Hlam_sec`, `Hth_sec`) for `≥`. -/
theorem sup'_argmin_eq_of_le_of_section
    (f : ι → κ) (s : κ → ι)
    (glam : ι → α) (hlam : κ → α) (gth : ι → β) (hth : κ → β)
    (H1 : ∀ a, hlam (f a) ≤ glam a)
    (Hlam_sec : ∀ b, glam (s b) = hlam b)
    (H2 : ∀ a, glam a = hlam (f a) → gth a ≤ hth (f a))
    (Hth_sec : ∀ b, gth (s b) = hth b) :
    (univ.filter (fun a => glam a = univ.inf' univ_nonempty glam)).sup'
        (argmin_univ_nonempty glam) gth
      = (univ.filter (fun b => hlam b = univ.inf' univ_nonempty hlam)).sup'
        (argmin_univ_nonempty hlam) hth := by
  have hlam_eq := inf'_univ_eq_of_le_of_section f s glam hlam H1 Hlam_sec
  apply le_antisymm
  · -- full multiplicity ≤ compressed multiplicity
    rw [Finset.sup'_le_iff]
    intro a ha
    rw [mem_filter] at ha
    have hga : glam a = univ.inf' univ_nonempty glam := ha.2
    -- f a attains the compressed least value (squeeze)
    have hfa : hlam (f a) = univ.inf' univ_nonempty hlam := by
      apply le_antisymm
      · calc hlam (f a) ≤ glam a := H1 a
          _ = univ.inf' univ_nonempty glam := hga
          _ = univ.inf' univ_nonempty hlam := hlam_eq
      · exact Finset.inf'_le hlam (mem_univ (f a))
    have hgla : glam a = hlam (f a) := by rw [hga, hlam_eq, hfa]
    refine le_trans (H2 a hgla) ?_
    exact Finset.le_sup' hth (mem_filter.mpr ⟨mem_univ (f a), hfa⟩)
  · -- compressed multiplicity ≤ full multiplicity
    rw [Finset.sup'_le_iff]
    intro b hb
    rw [mem_filter] at hb
    have hhb : hlam b = univ.inf' univ_nonempty hlam := hb.2
    have hsb : glam (s b) = univ.inf' univ_nonempty glam := by
      rw [Hlam_sec b, hhb, ← hlam_eq]
    rw [← Hth_sec b]
    exact Finset.le_sup' gth (mem_filter.mpr ⟨mem_univ (s b), hsb⟩)

/-- **Route-(a) D4 aggregate-lift kernel** (the conjunction of `inf'_univ_eq_of_le_of_section` and
`sup'_argmin_eq_of_le_of_section`).
Under a surjection-with-section `f`/`s` and the per-element comparison (`H1`, `H2`) plus the
section identities (`Hlam_sec`, `Hth_sec`), the least values agree and the greatest
second-statistics over the argmin sets agree. -/
private theorem aggLift
    (f : ι → κ) (s : κ → ι)
    (glam : ι → α) (hlam : κ → α) (gth : ι → β) (hth : κ → β)
    (H1 : ∀ a, hlam (f a) ≤ glam a)
    (Hlam_sec : ∀ b, glam (s b) = hlam b)
    (H2 : ∀ a, glam a = hlam (f a) → gth a ≤ hth (f a))
    (Hth_sec : ∀ b, gth (s b) = hth b) :
    univ.inf' univ_nonempty glam = univ.inf' univ_nonempty hlam ∧
    (univ.filter (fun a => glam a = univ.inf' univ_nonempty glam)).sup'
        (argmin_univ_nonempty glam) gth
      = (univ.filter (fun b => hlam b = univ.inf' univ_nonempty hlam)).sup'
        (argmin_univ_nonempty hlam) hth :=
  ⟨inf'_univ_eq_of_le_of_section f s glam hlam H1 Hlam_sec,
   sup'_argmin_eq_of_le_of_section f s glam hlam gth hth H1 Hlam_sec H2 Hth_sec⟩

end Finset
