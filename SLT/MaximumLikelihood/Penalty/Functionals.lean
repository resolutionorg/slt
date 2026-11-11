/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Geometry
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Penalized rewards on the zeros of $K$

Read a penalty $\sigma$ on the chart cubes of a resolution atlas, as $\sigma \circ g$. For a
penalty weight $a$ and a field $\Psi$ on the cubes, the penalized reward is the maximum, over the
resolved zeros $v$ of $K$, of $\max(0, -\Psi(v))^2/4 - a\sigma(g(v))$. At the limit $\Psi$ of the
empirical process, it is the limit of the shifted error $nK(\hat w) - a\sigma(\hat w)$ of an
estimator with a finite penalty in [Wat09, Main Theorem 6.4(2)]. This module proves that the
maximum is attained, bounds it, and shows that it is continuous in the field and Lipschitz in the
weight. For a diverging penalty, as in [Wat09, Main Theorem 6.4(3)], the reward is taken over the
resolved zeros at which $\sigma$ is smallest, which form a nonempty compact set.

## Main definitions

* `SingularLearningTheory.ResolutionAtlas.chartPenalty`: the penalty read on the chart cubes.
* `SingularLearningTheory.ResolutionAtlas.penalizedMax` and
  `SingularLearningTheory.ResolutionAtlas.penalizedLikelihoodRewardSup`: the penalized reward, for a
  function on the cubes and for a penalty on the parameter space.
* `SingularLearningTheory.ResolutionAtlas.resolvedPenaltyMinimizers`: the resolved zeros at which
  the penalty is smallest. `SingularLearningTheory.ResolutionAtlas.penaltyMinimum` is that smallest
  value, and `SingularLearningTheory.MaximumLikelihood.penaltySelectSlice` the resolved zeros within
  $\delta$ of it.

## Main results

* `SingularLearningTheory.ResolutionAtlas.chartPenalty_continuous_lipschitz`: a $C^1$ penalty on a
  neighborhood of $W$ is continuous on the cubes, with one Lipschitz constant for all charts.
* `SingularLearningTheory.ResolutionAtlas.exists_penalizedMax_eq` and
  `SingularLearningTheory.ResolutionAtlas.le_penalizedMax`: the maximum is attained, and bounds the
  objective at every resolved zero.
* `SingularLearningTheory.ResolutionAtlas.abs_penalizedMax_sub_le`: changing the weight from $a$ to
  $a'$ changes the reward by at most $|a - a'|\sup|\sigma|$.
* `SingularLearningTheory.MaximumLikelihood.continuous_penalizedMax`: the reward is continuous in the
  field.
* `SingularLearningTheory.MaximumLikelihood.abs_penalizedMax_le`: the reward is at most
  $\|\Psi\|^2/4 + |a|\sup|\sigma|$ in absolute value.
* `SingularLearningTheory.MaximumLikelihood.continuous_selectedLikelihoodReward`: the reward over the
  penalty minimizers is continuous in the field.
* `IsCompact.near_minimum_subset_open`: near-minimizers of a continuous
  function on a compact set lie in any open set that contains its exact minimizers.
* `SingularLearningTheory.MaximumLikelihood.aestronglyMeasurable_penalty_comp`: $\sigma(\hat w)$ is
  almost everywhere strongly measurable when $\sigma$ is continuous on $W$ and $\hat w$ is a
  measurable estimator in $W$ almost surely.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.ResolutionAtlas

open SingularLearningTheory.MaximumLikelihood

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The ambient penalty read on the resolution cubes. -/
@[expose] def chartPenalty (σ : (Fin d → ℝ) → ℝ) (v : Domain R) : ℝ := σ (R.g v.1 v.2)

private theorem continuous_chartPenalty {σ : (Fin d → ℝ) → ℝ} (hσ : ContinuousOn σ W) :
    Continuous (chartPenalty R σ) := by
  refine continuous_sigma fun α ↦ ?_
  exact continuousOn_iff_continuous_domRestrict.mp
    (hσ.comp (R.g_analytic α).continuousOn (R.g_mapsTo α))

/-- The stated C¹ assumption supplies one Lipschitz constant for every chart. -/
theorem chartPenalty_continuous_lipschitz {σ : (Fin d → ℝ) → ℝ}
    {U : Set (Fin d → ℝ)} (hWU : W ⊆ U) (hσ : ContDiffOn ℝ 1 σ U) :
    Continuous (chartPenalty R σ) ∧
      ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ α (u v : cube d (R.b α)),
        |σ (R.g α u) - σ (R.g α v)| ≤ Λ * dist u v := by
  classical
  have hg : ∀ α, ContDiffOn ℝ 1 (fun u ↦ σ (R.g α u)) (cube d (R.b α)) := fun α ↦
    hσ.comp ((R.g_analytic α).contDiffOn_of_completeSpace.of_le le_top)
      (fun u hu ↦ hWU (R.g_mapsTo α hu))
  have hLip : ∀ α, ∃ C : NNReal,
      LipschitzOnWith C (fun u ↦ σ (R.g α u)) (cube d (R.b α)) := fun α ↦
    (hg α).exists_lipschitzOnWith (by simp)
      (convex_Icc _ _) isCompact_Icc
  choose C hC using hLip
  refine ⟨continuous_chartPenalty R (hσ.continuousOn.mono hWU),
    ∑ α, (C α : ℝ), Finset.sum_nonneg (fun α _ ↦ NNReal.coe_nonneg _), ?_⟩
  intro α u v
  have h := (hC α).dist_le_mul u u.property v v.property
  rw [Real.dist_eq] at h
  refine h.trans (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
  exact Finset.single_le_sum (f := fun α ↦ (C α : ℝ))
    (fun α _ ↦ NNReal.coe_nonneg _) (Finset.mem_univ α)

/-- Generic zero-set penalized maximum. No positivity of the penalty is required. -/
@[expose] noncomputable def penalizedMax (σg : Domain R → ℝ) (a : ℝ) (Ψ : C(Domain R, ℝ)) : ℝ :=
  sSup ((fun v ↦ (max 0 (-Ψ v)) ^ 2 / 4 - a * σg v) '' resolvedZeroSet R)

/-- The penalized reward: the supremum over the chart cubes of the reward minus `a` times the
penalty, with the penalty read through `chartPenalty`. -/
@[expose] noncomputable def penalizedLikelihoodRewardSup (σ : (Fin d → ℝ) → ℝ)
    (a : ℝ) (Ψ : C(Domain R, ℝ)) : ℝ :=
  penalizedMax R (chartPenalty R σ) a Ψ

section Maxima

variable (σg : Domain R → ℝ) (hσ : Continuous σg)

include hσ

private theorem continuousOn_penalizedObjective (a : ℝ) (Ψ : C(Domain R, ℝ)) :
    ContinuousOn (fun v ↦ (max 0 (-Ψ v)) ^ 2 / 4 - a * σg v) (resolvedZeroSet R) :=
  ((((continuous_const.max Ψ.continuous.neg).pow 2).div_const 4).sub
    (hσ.const_mul a)).continuousOn

theorem exists_penalizedMax_eq (a : ℝ) (Ψ : C(Domain R, ℝ)) :
    ∃ v ∈ resolvedZeroSet R,
      penalizedMax R σg a Ψ = (max 0 (-Ψ v)) ^ 2 / 4 - a * σg v :=
  (isCompact_resolvedZeroSet R).exists_sSup_image_eq (resolvedZeroSet_nonempty R)
    (continuousOn_penalizedObjective R σg hσ a Ψ)

theorem le_penalizedMax (a : ℝ) (Ψ : C(Domain R, ℝ)) {v : Domain R}
    (hv : v ∈ resolvedZeroSet R) :
    (max 0 (-Ψ v)) ^ 2 / 4 - a * σg v ≤ penalizedMax R σg a Ψ :=
  le_csSup ((isCompact_resolvedZeroSet R).image_of_continuousOn
    (continuousOn_penalizedObjective R σg hσ a Ψ)).bddAbove (mem_image_of_mem _ hv)

/-- Changing the penalty weight costs at most |a-a'| sup_Z |σg|. -/
theorem abs_penalizedMax_sub_le {Sg : ℝ}
    (hσb : ∀ v ∈ resolvedZeroSet R, |σg v| ≤ Sg)
    (a a' : ℝ) (Ψ : C(Domain R, ℝ)) :
    |penalizedMax R σg a Ψ - penalizedMax R σg a' Ψ| ≤ |a - a'| * Sg := by
  have key : ∀ a a' : ℝ,
      penalizedMax R σg a Ψ ≤ penalizedMax R σg a' Ψ + |a - a'| * Sg := by
    intro a a'
    obtain ⟨v, hv, heq⟩ := exists_penalizedMax_eq R σg hσ a Ψ
    rw [heq]
    have h1 := le_penalizedMax R σg hσ a' Ψ hv
    have h2 : |(a' - a) * σg v| ≤ |a - a'| * Sg := by
      rw [abs_mul, abs_sub_comm a' a]
      exact mul_le_mul_of_nonneg_left (hσb v hv) (abs_nonneg _)
    have h3 := (abs_le.mp h2).2
    linarith
  rw [abs_sub_le_iff]
  constructor
  · linarith [key a a']
  · have := key a' a
    rw [abs_sub_comm a' a] at this
    linarith

private theorem continuous_penalizedMax (a : ℝ) : Continuous (penalizedMax R σg a) := by
  refine (isCompact_resolvedZeroSet R).continuous_sSup
    (f := fun (Ψ : C(Domain R, ℝ)) (v : Domain R) ↦
      (max 0 (-Ψ v)) ^ 2 / 4 - a * σg v) ?_
  have hev : Continuous fun p : C(Domain R, ℝ) × Domain R ↦ p.1 p.2 := continuous_eval
  have hσ' : Continuous fun p : C(Domain R, ℝ) × Domain R ↦ σg p.2 := hσ.comp continuous_snd
  exact (((continuous_const.max hev.neg).pow 2).div_const 4).sub (hσ'.const_mul a)

theorem continuous_jointPenalizedReward (a : ℝ) :
    Continuous fun Ψ : C(Domain R, ℝ) ↦
      (penalizedMax R σg a Ψ, -penalizedMax R σg a Ψ) :=
  (continuous_penalizedMax R σg hσ a).prodMk (continuous_penalizedMax R σg hσ a).neg

/-- The penalized reward is signed; this absolute bound replaces any positivity argument. -/
theorem abs_penalizedMax_le {Sg : ℝ}
    (hσb : ∀ v ∈ resolvedZeroSet R, |σg v| ≤ Sg)
    (a : ℝ) (Ψ : C(Domain R, ℝ)) :
    |penalizedMax R σg a Ψ| ≤ ‖Ψ‖ ^ 2 / 4 + |a| * Sg := by
  obtain ⟨v, hv, heq⟩ := exists_penalizedMax_eq R σg hσ a Ψ
  rw [heq]
  have hm0 : 0 ≤ max 0 (-Ψ v) := le_max_left _ _
  have hm : max 0 (-Ψ v) ≤ ‖Ψ‖ := by
    refine max_le (norm_nonneg _) ?_
    have h := Ψ.norm_coe_le_norm v
    rw [Real.norm_eq_abs] at h
    linarith [neg_abs_le (Ψ v)]
  calc |(max 0 (-Ψ v)) ^ 2 / 4 - a * σg v|
      ≤ |(max 0 (-Ψ v)) ^ 2 / 4| + |a * σg v| := by
          simpa only [sub_eq_add_neg, abs_neg] using
            abs_add_le ((max 0 (-Ψ v)) ^ 2 / 4) (-(a * σg v))
    _ ≤ ‖Ψ‖ ^ 2 / 4 + |a| * Sg := by
        rw [abs_of_nonneg (by positivity : 0 ≤ (max 0 (-Ψ v)) ^ 2 / 4), abs_mul]
        exact add_le_add
          (div_le_div_of_nonneg_right (pow_le_pow_left₀ hm0 hm 2) (by norm_num))
          (mul_le_mul_of_nonneg_left (hσb v hv) (abs_nonneg _))

end Maxima

/-- The minimizers of the penalty over the resolved zero set. -/
@[expose] def resolvedPenaltyMinimizers (σ : (Fin d → ℝ) → ℝ) : Set (Domain R) :=
  {u | u ∈ resolvedZeroSet R ∧ ∀ v ∈ resolvedZeroSet R, chartPenalty R σ u ≤ chartPenalty R σ v}

/-- The smallest value of the penalty `SingularLearningTheory.ResolutionAtlas.chartPenalty`
over the resolved zeros `SingularLearningTheory.ResolutionAtlas.resolvedZeroSet` of $K$, as an
infimum. For a continuous penalty it is attained
(`SingularLearningTheory.ResolutionAtlas.exists_penaltyMinimum_eq`). -/
noncomputable def penaltyMinimum (σ : (Fin d → ℝ) → ℝ) : ℝ :=
  sInf (chartPenalty R σ '' resolvedZeroSet R)

/-- The resolved zeros of $K$ at which the penalty
`SingularLearningTheory.ResolutionAtlas.chartPenalty` is within $\delta$ of its smallest value
`SingularLearningTheory.ResolutionAtlas.penaltyMinimum`. For a continuous penalty, the slice at
$\delta = 0$ is `SingularLearningTheory.ResolutionAtlas.resolvedPenaltyMinimizers`. -/
private def penaltySelectSlice (σ : (Fin d → ℝ) → ℝ) (δ : ℝ) : Set (Domain R) :=
  {u | u ∈ resolvedZeroSet R ∧ chartPenalty R σ u ≤ penaltyMinimum R σ + δ}

section Minima

variable {σ : (Fin d → ℝ) → ℝ} (hσ : Continuous (chartPenalty R σ))

include hσ

theorem exists_penaltyMinimum_eq :
    ∃ v ∈ resolvedZeroSet R, chartPenalty R σ v = penaltyMinimum R σ := by
  obtain ⟨v, hv, heq⟩ := (isCompact_resolvedZeroSet R).exists_sInf_image_eq
    (resolvedZeroSet_nonempty R) hσ.continuousOn
  exact ⟨v, hv, heq.symm⟩

theorem penaltyMinimum_le {v : Domain R} (hv : v ∈ resolvedZeroSet R) :
    penaltyMinimum R σ ≤ chartPenalty R σ v :=
  csInf_le ((isCompact_resolvedZeroSet R).image_of_continuousOn hσ.continuousOn).bddBelow
    (mem_image_of_mem _ hv)

private theorem isCompact_penaltySelectSlice (δ : ℝ) : IsCompact (penaltySelectSlice R σ δ) :=
  (isCompact_resolvedZeroSet R).inter_right (isClosed_le hσ continuous_const)

private theorem penaltySelectSlice_nonempty {δ : ℝ} (hδ : 0 ≤ δ) :
    (penaltySelectSlice R σ δ).Nonempty := by
  obtain ⟨v, hv, heq⟩ := exists_penaltyMinimum_eq R hσ
  exact ⟨v, hv, by rw [heq]; linarith⟩

private theorem resolvedPenaltyMinimizers_eq_selectSlice :
    resolvedPenaltyMinimizers R σ = penaltySelectSlice R σ 0 := by
  ext u
  constructor
  · rintro ⟨hu, hmin⟩
    obtain ⟨v, hv, heq⟩ := exists_penaltyMinimum_eq R hσ
    exact ⟨hu, by simpa only [add_zero, ← heq] using hmin v hv⟩
  · rintro ⟨hu, hmin⟩
    refine ⟨hu, fun v hv ↦ ?_⟩
    have hle : chartPenalty R σ u ≤ penaltyMinimum R σ := by simpa only [add_zero] using hmin
    exact hle.trans (penaltyMinimum_le R hσ hv)

theorem isCompact_resolvedPenaltyMinimizers : IsCompact (resolvedPenaltyMinimizers R σ) := by
  rw [resolvedPenaltyMinimizers_eq_selectSlice R hσ]
  exact isCompact_penaltySelectSlice R hσ 0

theorem resolvedPenaltyMinimizers_nonempty : (resolvedPenaltyMinimizers R σ).Nonempty := by
  rw [resolvedPenaltyMinimizers_eq_selectSlice R hσ]
  exact penaltySelectSlice_nonempty R hσ le_rfl

/-- Reuse the compact-subset reward theorem for the exact diverging-penalty limit. -/
theorem continuous_selectedLikelihoodReward :
    Continuous (likelihoodRewardSup R (resolvedPenaltyMinimizers R σ)) :=
  continuous_likelihoodRewardSup R _
    (isCompact_resolvedPenaltyMinimizers R hσ) (resolvedPenaltyMinimizers_nonempty R hσ)

end Minima

/-- Compactness alone forces near-minimizers into every open neighbourhood of
all exact minimizers. With O a metric thickening, this controls the selection defect
uniformly over Lipschitz-bounded paths and avoids a new weak-convergence wrapper. -/
theorem _root_.IsCompact.near_minimum_subset_open {A : Type*} [TopologicalSpace A]
    {Z : Set A} (hZ : IsCompact Z) {τ : A → ℝ} (hτ : ContinuousOn τ Z)
    {m : ℝ} (hm : ∀ z ∈ Z, m ≤ τ z)
    {O : Set A} (hO : IsOpen O) (hminO : ∀ z ∈ Z, τ z = m → z ∈ O) :
    ∃ δ > 0, ∀ z ∈ Z, τ z ≤ m + δ → z ∈ O := by
  classical
  let B := Z ∩ Oᶜ
  have hB : IsCompact B := hZ.inter_right hO.isClosed_compl
  by_cases hBne : B.Nonempty
  · obtain ⟨b, hb, hbm⟩ := hB.exists_isMinOn hBne
      (hτ.mono (show B ⊆ Z from inter_subset_left))
    have hgap : m < τ b := by
      by_contra h
      have heq : τ b = m := le_antisymm (le_of_not_gt h) (hm b hb.1)
      exact hb.2 (hminO b hb.1 heq)
    refine ⟨(τ b - m) / 2, half_pos (sub_pos.mpr hgap), ?_⟩
    intro z hz hnear
    by_contra hzO
    have hle : τ b ≤ τ z := hbm (show z ∈ B from ⟨hz, hzO⟩)
    linarith
  · refine ⟨1, one_pos, fun z hz _ ↦ ?_⟩
    by_contra hzO
    exact hBne ⟨z, hz, hzO⟩

section AEMeasurability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {σ : (Fin d → ℝ) → ℝ} {ŵ : Ω → Fin d → ℝ}

/-- The assumptions do not imply global measurability of σ. A measurable extension
from W suffices for a.e. feasible estimators, without strengthening the statement. -/
theorem _root_.SingularLearningTheory.MaximumLikelihood.aestronglyMeasurable_penalty_comp
    (hW : IsCompact W) (hσ : ContinuousOn σ W)
    (hŵ : Measurable ŵ) (hŵW : ∀ᵐ ω ∂P, ŵ ω ∈ W) :
    AEStronglyMeasurable (fun ω ↦ σ (ŵ ω)) P := by
  classical
  have hm : Measurable (W.piecewise σ (fun _ ↦ 0)) :=
    hσ.measurable_piecewise continuousOn_const hW.isClosed.measurableSet
  refine (hm.comp hŵ).aestronglyMeasurable.congr ?_
  filter_upwards [hŵW] with ω hω
  simp [Set.piecewise, hω]

end AEMeasurability
end SingularLearningTheory.ResolutionAtlas
