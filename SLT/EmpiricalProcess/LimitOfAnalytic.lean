/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.FiniteDimensional
public import SLT.EmpiricalProcess.MajorantsOfExpansion
public import SLT.EmpiricalProcess.TightnessFromPatches
public import SLT.FreeEnergy.FundamentalConditions
import SLT.EmpiricalProcess.Convergence
import SLT.EmpiricalProcess.Modification
public import SLT.EmpiricalProcess.LocalExpansion
public import SLT.EmpiricalProcess.Defs

/-!
# [Wat09, Theorem 5.9]: convergence of the empirical process

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 4.2.9] ([Wat09, Theorem 5.9]), on a compact metric space | |
| | `exists_empiricalProcessLimit_of_l2Expansion` |
| [Hit26, Theorem 4.2.9], for `f` `L^s(q)`-valued analytic on `W ⊆ ℝ^d` | |
| | `SingularLearningTheory.LsValuedAnalytic.exists_empiricalProcessLimit` |

The assembly. On a compact metric space `U`, for `f` measurable in `x`, continuous in `u` for
almost every `x`, square integrable at every `u`, with continuous mean and an `L²(q)`-expansion
around every point: the continuous modification `Ψ_n` of `ψ_n` is tight
(`SingularLearningTheory.EmpiricalProcess.isTightMeasureSet_of_patchMajorants`), its linear
finite-dimensional images converge to the
Gaussian laws of the CLT
(`SingularLearningTheory.EmpiricalProcess.tendstoInDistribution_clm_finiteEval`), so
`MeasureTheory.exists_tendstoInDistribution_of_tight` yields the limit law `μ` on `C(U, ℝ)`, whose
finite-dimensional distributions are then read off. For [Hit26]'s setting, `f` `L^s(q)`-valued
real analytic on a neighbourhood of the compact `W ⊆ ℝ^d` with `s ≥ 2`, the inclusion
`L^s(q) → L²(q)` supplies the expansions (`HasFPowerSeriesOnBall.exists_l2Expansion`), the square
integrability and the
continuity of the mean.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] {q : Measure X}
  [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P] {Xs : ℕ → Ω → X}

section Abstract

variable {U : Type*} [MetricSpace U] [CompactSpace U] {f : X → U → ℝ}

/-- [Hit26, Theorem 4.2.9] ([Wat09, Theorem 5.9]) on a compact metric
parameter space `U`, from local `L²(q)`-expansions of the integrand: the empirical process of `f`
along an i.i.d. sample `X_i ∼ q` is tight in `C(U, ℝ)` and converges in distribution to a random
continuous function with centred Gaussian finite-dimensional distributions of covariance
`cov(f(X, u), f(X, u'))`, realised as the identity on `(C(U, ℝ), μ)`. -/
theorem exists_empiricalProcessLimit_of_l2Expansion (hf_meas : ∀ u, Measurable fun x ↦ f x u)
    (hf_cont : ∀ᵐ x ∂q, Continuous (f x)) (hL2 : ∀ u, MemLp (fun x ↦ f x u) 2 q)
    (hmean : Continuous fun u ↦ ∫ x, f x u ∂q)
    (hloc : ∀ u : U, ∃ B : Set U, IsOpen B ∧ u ∈ B ∧ Nonempty (L2Expansion q f B))
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) :
    ∃ (P' : Measure C(U, ℝ)) (_ : IsProbabilityMeasure P'),
      Nonempty (EmpiricalProcessLimit q f Xs P P') := by
  obtain ⟨G, hGm, hGq, hG⟩ := exists_measurable_continuity_set q f hf_cont
  have hΨm : ∀ n, Measurable (EmpiricalProcess.continuousModification q f Xs hG hmean n) :=
    EmpiricalProcess.measurable_continuousModification hGm hG hmean hf_meas hX
  have hΨ : ∀ n, ∀ᵐ ω ∂P, ∀ u,
      EmpiricalProcess.continuousModification q f Xs hG hmean n ω u = empiricalProcess q f Xs n ω
          u :=
    EmpiricalProcess.ae_continuousModification_apply hX hlaw hGq hG hmean
  choose B hBo hBu hBE using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover B hBo fun u _ ↦ mem_iUnion.mpr ⟨u, hBu u⟩
  have hBc : ⋃ i : t, B i = univ := by
    refine eq_univ_of_univ_subset (ht.trans fun u hu ↦ ?_)
    simp only [mem_iUnion, exists_prop] at hu
    obtain ⟨i, hi, hui⟩ := hu
    exact mem_iUnion.mpr ⟨⟨i, hi⟩, hui⟩
  have tight := EmpiricalProcess.isTightMeasureSet_of_patchMajorants (fun i : t ↦ hBo i) hBc hΨm
      fun i ↦
    (hBE i).some.patchMajorants Xs hX hlaw hind (TopologicalSpace.IsSeparable.of_separableSpace _)
      (hf_cont.mono fun x hx ↦ hx.continuousOn) hΨ
  obtain ⟨μ, hconv, hfdd⟩ := exists_tendstoInDistribution_of_tight hΨm tight
    (fun M u L ↦ ⟨gaussianReal 0 (Var[EmpiricalProcess.linearCombination f u L; q]).toNNReal,
        inferInstance⟩)
    fun M u L ↦ EmpiricalProcess.tendstoInDistribution_clm_finiteEval hX hlaw hind hf_meas hL2 hΨ u
        L
  have hfdd' : ∀ (M : ℕ) (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ),
      (μ : Measure C(U, ℝ)).map (fun h ↦ L (ContinuousMap.finiteEval u h))
        = gaussianReal 0 (Var[EmpiricalProcess.linearCombination f u L; q]).toNNReal := hfdd
  refine ⟨μ, inferInstance, ⟨⟨EmpiricalProcess.continuousModification q f Xs hG hmean, hΨm, hΨ,
      tight, id, hconv,
    fun M u ↦ isGaussian_map_finiteEval_of_fdd hfdd' M u,
    fun u ↦ integral_eval_eq_zero_of_fdd hfdd' u, fun u u' ↦ ?_⟩⟩⟩
  change cov[fun h : C(U, ℝ) ↦ h u, fun h ↦ h u'; (μ : Measure C(U, ℝ))] = _
  rw [covariance_eval_of_fdd hfdd' u u', covariance_eq_of_variances hL2 u u',
    EmpiricalProcess.linearCombination_proj_zero, EmpiricalProcess.linearCombination_proj_one,
        EmpiricalProcess.linearCombination_proj_add,
    Real.coe_toNNReal _ (variance_nonneg _ _), Real.coe_toNNReal _ (variance_nonneg _ _),
    Real.coe_toNNReal _ (variance_nonneg _ _)]

end Abstract

section SLT

variable {d : ℕ}

/-- Local `L²(q)`-expansions of `f` on `W` from `L^s(q)`-valued analyticity on a neighbourhood
([Hit26, Definition 4.2.2]), with coefficients in `L^s(q)`. -/
theorem LsValuedAnalytic.loc {s : ℝ≥0∞} [Fact (1 ≤ s)] (hs : 2 ≤ s) {W : Set (Fin d → ℝ)}
    {f : X → (Fin d → ℝ) → ℝ} (hf : LsValuedAnalytic s q f W) (w₀ : W) :
    ∃ B : Set W, IsOpen B ∧ w₀ ∈ B ∧
      ∃ E : L2Expansion q (fun x (w : W) ↦ f x w) B, E.HigherMoment s := by
  obtain ⟨V, hVo, hWV, F, hFa, hFf⟩ := hf
  obtain ⟨p, r, hpr⟩ := hFa w₀ (hWV w₀.2)
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hVo w₀ (hWV w₀.2)
  have hpr' : HasFPowerSeriesOnBall F p w₀ (min r (ENNReal.ofReal ε)) :=
    hpr.mono (lt_min hpr.r_pos (ENNReal.ofReal_pos.mpr hε)) (min_le_left _ _)
  have hf' : ∀ u : W, edist (u : Fin d → ℝ) w₀ < min r (ENNReal.ofReal ε) →
      (F u : X → ℝ) =ᵐ[q] fun x ↦ f x u := by
    intro u hu
    refine hFf u (hball ?_)
    rw [Metric.mem_ball, ← ENNReal.ofReal_lt_ofReal_iff hε, ← edist_dist]
    exact hu.trans_le (min_le_right _ _)
  obtain ⟨ρ, hρ, hB⟩ := HasFPowerSeriesOnBall.exists_l2Expansion hs hpr'
    (fun u : W ↦ (u : Fin d → ℝ)) (fun x (u : W) ↦ f x u) hf'
  refine ⟨{u : W | dist (u : Fin d → ℝ) w₀ < ρ}, ?_, ?_, ?_⟩
  · exact isOpen_lt (continuous_subtype_val.dist continuous_const) continuous_const
  · simpa using hρ
  · exact hB _ (fun u hu ↦ le_of_lt hu) fun u _ v _ ↦ le_of_eq (Subtype.dist_eq u v).symm

/-- [Hit26, Theorem 4.2.9] ([Wat09, Theorem 5.9]) as [Hit26] states it: for
`W` compact and `f` `L^s(q)`-valued real analytic on `W` with `s ≥ 2` (represented by an analytic
map into `L^s(q)` on an open neighbourhood of `W`), measurable in `x` and continuous in `w` for
almost every `x`, the empirical process of an i.i.d. sample converges in distribution in `C(W, ℝ)`
to a centred Gaussian random continuous function with covariance `cov(f(X, w), f(X, w'))`. Only
`s ≥ 2` is used (through the inclusion `L^s(q) → L²(q)`), not [Hit26]'s evenness of `s`. -/
protected theorem LsValuedAnalytic.exists_empiricalProcessLimit {s : ℝ≥0∞} [Fact (1 ≤ s)]
    (hs : 2 ≤ s)
    {W : Set (Fin d → ℝ)} (hW : IsCompact W) {f : X → (Fin d → ℝ) → ℝ}
    (hf_meas : ∀ w, Measurable fun x ↦ f x w) (hf_cont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    (hf : LsValuedAnalytic s q f W) (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P) :
    ∃ (P' : Measure C(W, ℝ)) (_ : IsProbabilityMeasure P'),
      Nonempty (EmpiricalProcessLimit q (fun x (w : W) ↦ f x w) Xs P P') := by
  haveI : CompactSpace W := isCompact_iff_compactSpace.mp hW
  obtain ⟨V, hVo, hWV, F, hFa, hFf⟩ := id hf
  refine exists_empiricalProcessLimit_of_l2Expansion (f := fun x (w : W) ↦ f x w)
    (fun w ↦ hf_meas w) ?_ ?_ ?_ ?_ hX hlaw hind
  · filter_upwards [hf_cont] with x hx
    exact continuousOn_iff_continuous_domRestrict.mp hx
  · exact fun w ↦ ((Lp.memLp (F w)).mono_exponent hs).ae_eq (hFf w (hWV w.2))
  · have : (fun w : W ↦ ∫ x, f x w ∂q) = fun w : W ↦ lpIntegral q (F w) := by
      funext w
      rw [lpIntegral_apply]
      exact (integral_congr_ae (hFf w (hWV w.2))).symm
    rw [this]
    exact ((lpIntegral q).continuous.comp_continuousOn hFa.continuousOn).comp_continuous
      continuous_subtype_val fun w ↦ hWV w.2
  · intro w₀
    obtain ⟨B, hBo, hw₀, E, -⟩ := LsValuedAnalytic.loc hs hf w₀
    exact ⟨B, hBo, hw₀, ⟨E⟩⟩

end SLT

end SingularLearningTheory
