/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
public import Mathlib.Geometry.Manifold.IsManifold.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
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
# Composing an analytic chart with an analytic diffeomorphism of the model space

The chart of [Hit26, Theorem 3.3.1] (3) is composed
with the coordinate change of [Wat09, Remark 2.7] (`Analysis/Analytic/UnitAbsorption.lean`); the
composite is again a chart of the maximal analytic atlas. No thesis counterpart.
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]

/-- An analytic partial diffeomorphism of `ℝ^d` (analytic with analytic inverse on its source and
target) belongs to the analytic groupoid. -/
theorem _root_.mem_contDiffGroupoid_of_analytic (Φ : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ))
    (h₁ : AnalyticOnNhd ℝ Φ Φ.source) (h₂ : AnalyticOnNhd ℝ Φ.symm Φ.target) :
    Φ ∈ contDiffGroupoid ω 𝓘(ℝ, Fin d → ℝ) := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ]
  exact ⟨(contDiffOn_omega_iff_analyticOn Φ.open_source.uniqueDiffOn).mpr
      (Φ.open_source.analyticOn_iff_analyticOnNhd.mpr h₁),
    (contDiffOn_omega_iff_analyticOn Φ.open_target.uniqueDiffOn).mpr
      (Φ.open_target.analyticOn_iff_analyticOnNhd.mpr h₂)⟩

/-- Composing a chart of the maximal analytic atlas with an element of the analytic groupoid
stays in the maximal atlas. -/
theorem _root_.mem_maximalAtlas_trans {e : OpenPartialHomeomorph M (Fin d → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M)
    {Φ : OpenPartialHomeomorph (Fin d → ℝ) (Fin d → ℝ)}
    (hΦ : Φ ∈ contDiffGroupoid ω 𝓘(ℝ, Fin d → ℝ)) :
    e.trans Φ ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M := by
  rw [IsManifold.mem_maximalAtlas_iff, mem_maximalAtlas_iff] at he ⊢
  intro e' he'
  obtain ⟨h1, h2⟩ := he e' he'
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm, OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℝ, Fin d → ℝ)).trans ((contDiffGroupoid ω _).symm hΦ) h1
  · rw [← OpenPartialHomeomorph.trans_assoc]
    exact (contDiffGroupoid ω 𝓘(ℝ, Fin d → ℝ)).trans h2 hΦ

/-- The transition map between two charts of the maximal analytic atlas is analytic on its
domain `e'.target ∩ e'.symm ⁻¹' e.source`. -/
theorem _root_.analyticOnNhd_trans_of_mem_maximalAtlas [IsManifold 𝓘(ℝ, Fin d → ℝ) ω M]
    {e e' : OpenPartialHomeomorph M (Fin d → ℝ)}
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M)
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M) :
    AnalyticOnNhd ℝ (e ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' e.source) := by
  have h := IsManifold.compatible_of_mem_maximalAtlas he' he
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at h
  simp only [contDiffPregroupoid, modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ,
    OpenPartialHomeomorph.coe_trans, OpenPartialHomeomorph.trans_source,
    OpenPartialHomeomorph.symm_source] at h
  have hopen : IsOpen (e'.target ∩ e'.symm ⁻¹' e.source) := by
    have := e'.symm.isOpen_inter_preimage e.open_source
    rwa [OpenPartialHomeomorph.symm_source] at this
  exact hopen.analyticOn_iff_analyticOnNhd.mp
    ((contDiffOn_omega_iff_analyticOn hopen.uniqueDiffOn).mp h.1)

end SingularLearningTheory
