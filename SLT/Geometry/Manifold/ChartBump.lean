/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

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
# Bumps on a manifold through a chart

The inner partition of unity of [Hit26,
Section 3.3.1] lives on the resolution manifold
`M`. It is built from bumps `f` on the model space `ℝ^d` transported through a chart `e` of the
maximal analytic atlas (`OpenPartialHomeomorph.chartBump e f = f ∘ e` on `e.source`, `0` elsewhere).
When `tsupport f` is
a compact subset of `e.target`, the transported bump is continuous and smooth in every chart of the
maximal atlas: near a point of `e.source` it is `f` composed with an analytic transition map, and
near a point outside the compact set `e.symm '' tsupport f` it vanishes. No thesis counterpart for
the individual lemmas.
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d : ℕ} {M : Type} [TopologicalSpace M]

/-- The bump `f` on the model space transported to `M` through the chart `e`: `f (e P)` for
`P ∈ e.source`, `0` elsewhere. -/
@[expose] noncomputable def _root_.OpenPartialHomeomorph.chartBump
    (e : OpenPartialHomeomorph M (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ) :
    M → ℝ :=
  e.source.indicator fun P ↦ f (e P)

variable (e : OpenPartialHomeomorph M (Fin d → ℝ)) (f : (Fin d → ℝ) → ℝ)

theorem _root_.OpenPartialHomeomorph.chartBump_symm_apply {u : Fin d → ℝ} (hu : u ∈ e.target) :
    OpenPartialHomeomorph.chartBump e f (e.symm u) = f u := by
  simp only [OpenPartialHomeomorph.chartBump, indicator_of_mem (e.map_target hu), e.right_inv hu]

theorem _root_.OpenPartialHomeomorph.chartBump_eq_zero_of_notMem {P : M}
    (hP : P ∉ e.symm '' tsupport f) :
    OpenPartialHomeomorph.chartBump e f P = 0 := by
  by_cases hPs : P ∈ e.source
  · have hnot : e P ∉ tsupport f := fun h ↦ hP ⟨e P, h, e.left_inv hPs⟩
    simp only [OpenPartialHomeomorph.chartBump, indicator_of_mem hPs,
        image_eq_zero_of_notMem_tsupport hnot]
  · exact indicator_of_notMem hPs _

theorem _root_.OpenPartialHomeomorph.chartBump_nonneg (hf : ∀ u, 0 ≤ f u)
    (P : M) : 0 ≤ OpenPartialHomeomorph.chartBump e f P :=
  indicator_nonneg (fun Q _ ↦ hf (e Q)) P

theorem _root_.OpenPartialHomeomorph.chartBump_le_one (hf : ∀ u, f u ≤ 1)
    (P : M) : OpenPartialHomeomorph.chartBump e f P ≤ 1 :=
  indicator_le' (fun Q _ ↦ hf (e Q)) (fun _ _ ↦ zero_le_one) P

theorem _root_.OpenPartialHomeomorph.mem_source_of_chartBump_ne_zero {P : M}
    (h : OpenPartialHomeomorph.chartBump e f P ≠ 0) :
    P ∈ e.source ∧ e P ∈ Function.support f :=
  indicator_apply_ne_zero.mp h

/-- The transported bump vanishes off the compact set `e.symm '' tsupport f`, which is closed. -/
theorem _root_.OpenPartialHomeomorph.isCompact_image_tsupport [T2Space M]
    (hsupp : tsupport f ⊆ e.target)
    (hcpt : HasCompactSupport f) : IsCompact (e.symm '' tsupport f) :=
  hcpt.image_of_continuousOn (e.continuousOn_symm.mono hsupp)

theorem _root_.OpenPartialHomeomorph.continuous_chartBump [T2Space M] (hf : Continuous f)
    (hsupp : tsupport f ⊆ e.target)
    (hcpt : HasCompactSupport f) : Continuous (OpenPartialHomeomorph.chartBump e f) := by
  rw [continuous_iff_continuousAt]
  intro P
  by_cases hP : P ∈ e.source
  · refine ((hf.continuousAt).comp (e.continuousAt hP)).congr ?_
    filter_upwards [e.open_source.mem_nhds hP] with Q hQ
    simp only [OpenPartialHomeomorph.chartBump, Function.comp_apply, indicator_of_mem hQ]
  · have hS : P ∉ e.symm '' tsupport f := fun ⟨u, hu, huP⟩ ↦
      hP (huP ▸ e.map_target (hsupp hu))
    refine (continuousAt_const : ContinuousAt (fun _ : M ↦ (0 : ℝ)) P).congr ?_
    filter_upwards [(OpenPartialHomeomorph.isCompact_image_tsupport e f hsupp
        hcpt).isClosed.isOpen_compl.mem_nhds hS]
      with Q hQ
    exact (OpenPartialHomeomorph.chartBump_eq_zero_of_notMem e f hQ).symm

variable [ChartedSpace (Fin d → ℝ) M]

/-- In any chart `e'` of the maximal analytic atlas the transported bump is smooth. -/
theorem _root_.OpenPartialHomeomorph.contDiffOn_chartBump_comp_symm [T2Space M]
    [IsManifold 𝓘(ℝ, Fin d → ℝ) ω M]
    (he : e ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M)
    {e' : OpenPartialHomeomorph M (Fin d → ℝ)}
    (he' : e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M) (hf : ContDiff ℝ ∞ f)
    (hsupp : tsupport f ⊆ e.target) (hcpt : HasCompactSupport f) :
    ContDiffOn ℝ ∞ (OpenPartialHomeomorph.chartBump e f ∘ e'.symm) e'.target := by
  apply contDiffOn_of_locally_contDiffOn
  intro v hv
  by_cases hP : e'.symm v ∈ e.source
  · have htrans := IsManifold.compatible_of_mem_maximalAtlas he' he
    rw [contDiffGroupoid, mem_groupoid_of_pregroupoid] at htrans
    have hcd : ContDiffOn ℝ ω (e ∘ e'.symm) (e'.target ∩ e'.symm ⁻¹' e.source) := by
      have h1 := htrans.1
      simp only [contDiffPregroupoid, OpenPartialHomeomorph.trans_source,
        OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.coe_trans,
        modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
        inter_univ, Function.comp_id, Function.id_comp] at h1
      exact h1
    refine ⟨e'.target ∩ e'.symm ⁻¹' e.source, ?_, ⟨hv, hP⟩, ?_⟩
    · have := e'.symm.isOpen_inter_preimage e.open_source
      rwa [OpenPartialHomeomorph.symm_source] at this
    · refine (hf.comp_contDiffOn (hcd.of_le le_top)).congr ?_ |>.mono inter_subset_right
      intro w hw
      have hw' : e'.symm w ∈ e.source := hw.2
      simp only [OpenPartialHomeomorph.chartBump, Function.comp_apply, indicator_of_mem hw']
  · have hS : e'.symm v ∉ e.symm '' tsupport f := fun ⟨u, hu, huP⟩ ↦
      hP (huP ▸ e.map_target (hsupp hu))
    have hclosed := (OpenPartialHomeomorph.isCompact_image_tsupport e f hsupp hcpt).isClosed
    refine ⟨e'.target ∩ e'.symm ⁻¹' (e.symm '' tsupport f)ᶜ, ?_, ⟨hv, hS⟩, ?_⟩
    · have := e'.symm.isOpen_inter_preimage hclosed.isOpen_compl
      rwa [OpenPartialHomeomorph.symm_source] at this
    · refine (contDiffOn_const (c := (0 : ℝ))).congr ?_ |>.mono inter_subset_right
      intro w hw
      exact OpenPartialHomeomorph.chartBump_eq_zero_of_notMem e f hw.2

end SingularLearningTheory
