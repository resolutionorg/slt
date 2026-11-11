/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.SingularityType
public import SLT.SingularIntegrals.PositiveCube
public import SLT.SingularIntegrals.DeterministicFreeEnergy
public import SLT.Resolution.FromHironaka
public import SLT.VolumeScaling.ScaleDominance
import SLT.VolumeScaling.Transport
import SLT.VolumeScaling.Invariance
import SLT.VolumeScaling.Basic
public import SLT.StandardForm.FundamentalConditionI
import SLT.SingularIntegrals.Resolution
public import SLT.Resolution.Atlas
import Mathlib.Order.CompletePartialOrder
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Every nondegenerate resolution atlas computes the singularity type

[Hit26] defines the learning coefficient `λ` and its multiplicity `m` chart-wise from a
resolution ([Hit26, Equation (5.2.1)]) and remarks that the
local learning coefficient does not depend on the choice of resolution (the remark after
[Hit26, Definition 6.2.1]). Here: for every nondegenerate atlas `R` of
`(K, φ, W)`, the pair `(R.rlct, R.mult)` is the intrinsic singularity type by volume scaling
(`NondegenerateResolutionAtlas.isSingularityType`), so any two nondegenerate atlases have the same
exponents (`NondegenerateResolutionAtlas.rlct_eq_rlct`, `mult_eq_mult`), and under Hironaka's
theorem the type exists (`exists_isSingularityType`).

| Thesis | Lean |
| --- | --- |
| [Hit26, Equation (5.2.1)], `(λ, m)` of the atlas | |
| is the type by volume scaling | `NondegenerateResolutionAtlas.isSingularityType` |
| remark after [Hit26, Definition 6.2.1] (independence of the resolution) | |
| | `NondegenerateResolutionAtlas.rlct_eq_rlct`, `mult_eq_mult` |
| [Hit26, Equation (3.3.5)] for the indicator of `{K ≤ ε}` | |
| | `ResolutionAtlas.sublevelVol_priorMeasure_eq_sum` |

## The proof

On the volume side, parallel to `DeterministicFreeEnergy.lean` on the Laplace side. For
`ε < δ` the transport identity gives `V(ε) = Σ_α V_α(ε)` with
`V_α(ε) = ∫_{[0,b_α]^d ∩ {u^{2k_α} ≤ ε}} u^{h_α} φ̃_α(u) du` (`chartVolume`). Each `V_α` is
`O(ε^{λ_α} (−log ε)^{m_α − 1})`, the weight being bounded on the cube and the monomial
sublevel volumes on the positive cube being known (`PositiveCube.lean`,
`chartVolume_isBigO`). An essential chart with positive trace mass has a box near its
essential face on which the weight is bounded below, and on that box the chart density and the
monomial are comparable to their primary-coordinate parts, so `V_α` is also `Ω` of its scale
(`llcScale_isBigO_chartVolume`). A finite sum of nonnegative functions, all `O(S)` and one
`Ω(S)`, is `Θ(S)` (`Asymptotics.isTheta_sum_of_isBigO`), and the scale of every chart is `O` of the
scale
`ε^λ (−log ε)^{m−1}` of the essential charts (`λ = min λ_α`, `m = max m_α` at the minimum).
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology Asymptotics SingularLearningTheory
open scoped ENNReal

variable {d : ℕ}

/-! ## A sum of nonnegative functions, all `O(S)` and one `Ω(S)` -/

/-- No thesis counterpart. A finite sum of eventually nonnegative functions, each `O(S)` and
one of them `Ω(S)`, is `Θ(S)`. -/
theorem _root_.Asymptotics.isTheta_sum_of_isBigO {ι E : Type*} [Fintype ι] {l : Filter E}
    {F : ι → E → ℝ}
    {S : E → ℝ} (i₀ : ι) (hupper : ∀ i, F i =O[l] S) (hlower : S =O[l] F i₀)
    (hnonneg : ∀ i, ∀ᶠ x in l, 0 ≤ F i x) :
    (fun x ↦ ∑ i, F i x) =Θ[l] S := by
  refine ⟨(IsBigO.sum fun i _ ↦ hupper i).congr_left fun x ↦ Finset.sum_apply x Finset.univ F,
    hlower.trans (IsBigO.of_bound 1 ?_)⟩
  filter_upwards [Filter.eventually_all.mpr hnonneg] with x hx
  rw [one_mul, Real.norm_of_nonneg (hx i₀), Real.norm_of_nonneg (Finset.sum_nonneg fun i _ ↦ hx i)]
  exact Finset.single_le_sum (fun i _ ↦ hx i) (Finset.mem_univ i₀)

namespace ResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The chart density `u^{h_α} φ̃_α(u)`. -/
@[expose] noncomputable def chartDensity (α : R.ι) (u : Fin d → ℝ) : ℝ :=
  (∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u

/-- The chart monomial `u^{2k_α} = K(g_α u)`. -/
@[expose] def cubeMonomial (α : R.ι) (u : Fin d → ℝ) : ℝ := ∏ j, u j ^ (2 * R.k α j)

/-- The chart measure `u^{h_α} φ̃_α(u) du`. -/
@[expose] noncomputable def chartMeasure (α : R.ι) : Measure (Fin d → ℝ) :=
  volume.withDensity fun u ↦ ENNReal.ofReal (R.chartDensity α u)

/-- The chart sublevel volume `V_α(ε) = ∫_{[0,b_α]^d ∩ {u^{2k_α} ≤ ε}} u^{h_α} φ̃_α(u) du`. -/
@[expose] noncomputable def chartVolume (α : R.ι) (ε : ℝ) : ℝ :=
  sublevelVol (R.chartMeasure α) (cube d (R.b α)) (R.cubeMonomial α) ε

/-- The scale `ε^{λ_α} (−log ε)^{m_α − 1}` of a chart. -/
@[expose] noncomputable def chartScale (α : R.ι) : ℝ → ℝ := llcScale (R.chartRlct α) (R.chartMult α)

theorem measurableSet_cube (α : R.ι) : MeasurableSet (cube d (R.b α)) :=
  measurableSet_Icc

theorem measurable_cubeMonomial (α : R.ι) : Measurable (R.cubeMonomial α) :=
  Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _

theorem cubeMonomial_nonneg (α : R.ι) (u : Fin d → ℝ) : 0 ≤ R.cubeMonomial α u :=
  Finset.prod_nonneg fun _ _ ↦ (even_two_mul _).pow_nonneg _

theorem chartVolume_nonneg (α : R.ι) (ε : ℝ) : 0 ≤ R.chartVolume α ε := sublevelVol_nonneg _ _ _ _

/-- The weight is bounded on the compact cube by a positive constant. -/
theorem exists_weight_le (α : R.ι) : ∃ M, 0 < M ∧ ∀ u ∈ cube d (R.b α), R.weight α u ≤ M := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (R.weight_continuousOn α)
  exact ⟨max C 1, by positivity, fun u hu ↦
    (le_abs_self _).trans ((hC u hu).trans (le_max_left _ _))⟩

/-- The monomial weight `u^{h_α}` is bounded on the cube by `∏ b_α^{h_j}`. -/
theorem prod_rpow_le (α : R.ι) {u : Fin d → ℝ} (hu : u ∈ cube d (R.b α)) :
    ∏ j, u j ^ (R.h α j : ℝ) ≤ ∏ j, R.b α ^ (R.h α j : ℝ) :=
  Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (hu.1 j) _) fun j _ ↦
    Real.rpow_le_rpow (hu.1 j) (hu.2 j) (Nat.cast_nonneg _)

/-- A density bounded on a set of finite volume has finite mass there. No thesis counterpart. -/
theorem _root_.MeasureTheory.withDensity_ofReal_ne_top {E : Type*} [MeasureSpace E] {S : Set E}
    (hS : MeasurableSet S)
    (hSfin : volume S ≠ ⊤) {ρ : E → ℝ} {C : ℝ} (hρ : ∀ x ∈ S, ρ x ≤ C) :
    (volume.withDensity fun x ↦ ENNReal.ofReal (ρ x)) S ≠ ⊤ := by
  rw [withDensity_apply _ hS]
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C * volume S) (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top hSfin) ?_
  rw [← setLIntegral_const]
  exact setLIntegral_mono' hS fun x hx ↦ ENNReal.ofReal_le_ofReal (hρ x hx)

theorem volume_cube_ne_top (α : R.ι) : volume (cube d (R.b α)) ≠ ⊤ :=
  isCompact_Icc.measure_lt_top.ne

theorem chartMeasure_cube_ne_top (α : R.ι) : R.chartMeasure α (cube d (R.b α)) ≠ ⊤ := by
  obtain ⟨M, -, hM⟩ := R.exists_weight_le α
  refine withDensity_ofReal_ne_top (R.measurableSet_cube α) (R.volume_cube_ne_top α)
    (C := (∏ j, R.b α ^ (R.h α j : ℝ)) * M) fun u hu ↦ ?_
  exact mul_le_mul (R.prod_rpow_le α hu) (hM u hu) (R.weight_nonneg α u hu)
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (R.b_pos α).le _)

/-! ## The transport identity for sublevel volumes -/

/-- [Hit26, Equation (3.3.5)] applied to the indicator of
`{K ≤ ε}`, `ε < δ`: the prior mass of `W ∩ {K ≤ ε}` is the sum over the charts of the chart
measures of `{u^{2k_α} ≤ ε}`. -/
theorem priorMeasure_sublevel_eq_sum (hW : MeasurableSet W) (hKm : Measurable K)
    {ε : ℝ} (hε : ε < R.δ) :
    priorMeasure φ Set.univ (W ∩ {w | K w ≤ ε})
      = ∑ α, R.chartMeasure α (cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε}) := by
  have hS : MeasurableSet {w | K w ≤ ε} := measurableSet_le hKm measurable_const
  have h1 : priorMeasure φ Set.univ (W ∩ {w | K w ≤ ε})
      = ((volume.restrict W).withDensity fun w ↦ ENNReal.ofReal (R.χ w * φ w)) {w | K w ≤ ε} := by
    rw [priorMeasure, Measure.restrict_univ, withDensity_apply _ hS, Measure.restrict_restrict hS,
      inter_comm W, withDensity_apply _ (hS.inter hW)]
    refine setLIntegral_congr_fun (hS.inter hW) fun w hw ↦ ?_
    rw [R.χ_eq_one w hw.2 (lt_of_le_of_lt hw.1 hε), one_mul]
  rw [h1, R.transport, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  have hpre : R.g α ⁻¹' {w | K w ≤ ε} ∩ cube d (R.b α)
      = cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, cubeMonomial]
    constructor
    · rintro ⟨h, hu⟩
      exact ⟨hu, (R.monomial α u hu).symm.trans_le h⟩
    · rintro ⟨hu, h⟩
      exact ⟨(R.monomial α u hu).trans_le h, hu⟩
  rw [Measure.map_apply (R.g_measurable α) hS, withDensity_apply _ ((R.g_measurable α) hS),
    Measure.restrict_restrict ((R.g_measurable α) hS), hpre, chartMeasure,
    withDensity_apply _ ((R.measurableSet_cube α).inter (measurableSet_le
      (R.measurable_cubeMonomial α) measurable_const))]
  rfl

/-- The transport identity for a measurable part `A ⊆ W`: the prior mass of `A ∩ {K ≤ ε}`,
`ε < δ`, is the sum over the charts of the chart measures of `g_α⁻¹(A) ∩ {u^{2k_α} ≤ ε}`. -/
theorem priorMeasure_inter_sublevel_eq_sum (hW : MeasurableSet W) (hKm : Measurable K)
    {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) (hAW : A ⊆ W) {ε : ℝ} (hε : ε < R.δ) :
    priorMeasure φ Set.univ (A ∩ {w | K w ≤ ε})
      = ∑ α, R.chartMeasure α (cube d (R.b α) ∩ R.g α ⁻¹' A ∩ {u | R.cubeMonomial α u ≤ ε}) := by
  have hS : MeasurableSet (A ∩ {w | K w ≤ ε}) := hA.inter (measurableSet_le hKm measurable_const)
  have h1 : priorMeasure φ Set.univ (A ∩ {w | K w ≤ ε})
      = ((volume.restrict W).withDensity fun w ↦ ENNReal.ofReal (R.χ w * φ w))
          (A ∩ {w | K w ≤ ε}) := by
    rw [priorMeasure, Measure.restrict_univ, withDensity_apply _ hS, withDensity_apply _ hS,
      Measure.restrict_restrict hS, inter_eq_left.mpr (inter_subset_left.trans hAW)]
    refine setLIntegral_congr_fun hS fun w hw ↦ ?_
    rw [R.χ_eq_one w (hAW hw.1) (lt_of_le_of_lt hw.2 hε), one_mul]
  rw [h1, R.transport, Measure.finsetSum_apply]
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  have hpre : R.g α ⁻¹' (A ∩ {w | K w ≤ ε}) ∩ cube d (R.b α)
      = cube d (R.b α) ∩ R.g α ⁻¹' A ∩ {u | R.cubeMonomial α u ≤ ε} := by
    ext u
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq, cubeMonomial]
    constructor
    · rintro ⟨⟨hA', h⟩, hu⟩
      exact ⟨⟨hu, hA'⟩, (R.monomial α u hu).symm.trans_le h⟩
    · rintro ⟨⟨hu, hA'⟩, h⟩
      exact ⟨⟨hA', (R.monomial α u hu).trans_le h⟩, hu⟩
  rw [Measure.map_apply (R.g_measurable α) hS, withDensity_apply _ ((R.g_measurable α) hS),
    Measure.restrict_restrict ((R.g_measurable α) hS), hpre, chartMeasure,
    withDensity_apply _ (((R.measurableSet_cube α).inter ((R.g_measurable α) hA)).inter
      (measurableSet_le (R.measurable_cubeMonomial α) measurable_const))]
  rfl

/-- `V(ε) = Σ_α V_α(ε)` for `ε < δ`. -/
theorem sublevelVol_priorMeasure_eq_sum (hW : MeasurableSet W) (hKm : Measurable K)
    {ε : ℝ} (hε : ε < R.δ) :
    sublevelVol (priorMeasure φ Set.univ) W K ε = ∑ α, R.chartVolume α ε := by
  rw [sublevelVol, R.priorMeasure_sublevel_eq_sum hW hKm hε, ENNReal.toReal_sum fun α _ ↦
    ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α) (measure_mono inter_subset_left)]
  rfl

/-! ## The upper bound: every chart is `O` of its scale -/

/-- The primary coordinates are the coordinates attaining the least ratio: `m_α` as a count
over `Fin d`. -/
theorem chartMult_eq_card_filter (α : R.ι) :
    R.chartMult α = (Finset.univ.filter fun j ↦ 0 < R.k α j ∧
      ((R.h α j : ℝ) + 1) / (2 * R.k α j) = R.chartRlct α).card := by
  rw [chartMult_eq_card, primary_eq_filter, activeSet, Finset.filter_filter]
  rfl

/-- The monomial read-off on the chart cube: `u^{2k_α}` against `u^{h_α}` has exponents
`(λ_α, m_α)`. -/
theorem hasLLCExponentsOn_cubeMonomial (α : R.ι) :
    HasLLCExponentsOn (volume.withDensity fun u ↦ ENNReal.ofReal (∏ j, u j ^ (R.h α j : ℝ)))
      (cube d (R.b α)) (R.cubeMonomial α) (R.chartRlct α) (R.chartMult α) := by
  rw [R.chartMult_eq_card_filter α]
  refine hasLLCExponentsOn_monomial_cube (R.k α) (R.h α) (R.chartRlct_pos α) (fun j hj ↦ ?_) ?_
    (R.b_pos α)
  · exact Finset.inf'_le _ (by simp [activeSet, hj])
  · obtain ⟨j, hj⟩ := R.primary_nonempty α
    exact ⟨j, R.k_pos_of_mem_primary hj, R.ratio_eq_of_mem_primary hj⟩

/-- `V_α(ε) ≤ M · ∫_{[0,b_α]^d ∩ {u^{2k_α} ≤ ε}} u^{h_α} du` for a bound `M` of the weight. -/
theorem chartVolume_le (α : R.ι) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ u ∈ cube d (R.b α), R.weight α u ≤ M) (ε : ℝ) :
    R.chartVolume α ε ≤ M * sublevelVol
      (volume.withDensity fun u ↦ ENNReal.ofReal (∏ j, u j ^ (R.h α j : ℝ)))
      (cube d (R.b α)) (R.cubeMonomial α) ε := by
  have hS : MeasurableSet (cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε}) :=
    (R.measurableSet_cube α).inter (measurableSet_le (R.measurable_cubeMonomial α)
      measurable_const)
  have hfin : (volume.withDensity fun u ↦ ENNReal.ofReal (∏ j, u j ^ (R.h α j : ℝ)))
      (cube d (R.b α)) ≠ ⊤ :=
    withDensity_ofReal_ne_top (R.measurableSet_cube α) (R.volume_cube_ne_top α)
      fun u hu ↦ R.prod_rpow_le α hu
  rw [chartVolume, sublevelVol, sublevelVol, ← ENNReal.toReal_ofReal hM0, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ne_top_of_le_ne_top hfin (measure_mono inter_subset_left))) ?_
  rw [chartMeasure, withDensity_apply _ hS, withDensity_apply _ hS, ← lintegral_const_mul' _ _
    ENNReal.ofReal_ne_top]
  refine setLIntegral_mono' hS fun u hu ↦ ?_
  rw [← ENNReal.ofReal_mul hM0, chartDensity, mul_comm M]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hM u hu.1)
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1.1 j) _))

/-- Every chart volume is `O(ε^{λ_α} (−log ε)^{m_α − 1})`. -/
theorem chartVolume_isBigO (α : R.ι) : R.chartVolume α =O[𝓝[>] (0 : ℝ)] R.chartScale α := by
  obtain ⟨M, hM0, hM⟩ := R.exists_weight_le α
  refine (IsBigO.of_bound M ?_).trans (R.hasLLCExponentsOn_cubeMonomial α).1
  refine Eventually.of_forall fun ε ↦ ?_
  rw [Real.norm_of_nonneg (R.chartVolume_nonneg α ε),
    Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
  exact R.chartVolume_le α hM0.le hM ε

/-! ## The lower bound: an essential chart with positive trace mass is `Ω` of its scale -/

/-- No thesis counterpart. Positive essential trace mass gives a box `∏_j [t_j, t_j + η]` inside
the cube, with `t_j = 0` on the primary coordinates and `t_j > 0` on the others, on which the
weight is at least `c₀ > 0` (the box of `le_chartIntegral_of_traceMass_pos`). -/
theorem exists_box_of_traceMass_pos {α : R.ι} (hT : 0 < R.essentialTraceMass α) :
    ∃ (t : Fin d → ℝ) (η c₀ : ℝ), 0 < η ∧ 0 < c₀ ∧ (∀ j ∈ R.primary α, t j = 0) ∧
      (∀ j ∉ R.primary α, 0 < t j) ∧
      (pi univ fun j ↦ Icc (t j) (t j + η)) ⊆ cube d (R.b α) ∧
      ∀ u ∈ pi univ fun j ↦ Icc (t j) (t j + η), c₀ ≤ R.weight α u := by
  obtain ⟨w₀, hw₀, hw₀P, hw₀S, hw₀pos⟩ := R.exists_weight_pos_of_traceMass_pos hT
  have hb := R.b_pos α
  set c₀ : ℝ := R.weight α w₀ / 2 with hc₀_def
  have hc₀ : 0 < c₀ := by positivity
  obtain ⟨δ₀, hδ₀, hδ⟩ := Metric.continuousWithinAt_iff.mp (R.weight_continuousOn α w₀ hw₀) c₀ hc₀
  have hev : ∀ᶠ η in nhdsWithin (0 : ℝ) (Ioi 0),
      η < δ₀ ∧ η ≤ R.b α ∧ ∀ j ∈ (R.primary α)ᶜ, η < w₀ j := by
    refine (eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hδ₀)).and
      ((eventually_nhdsWithin_of_eventually_nhds (eventually_le_nhds hb)).and ?_)
    rw [Filter.eventually_all_finset]
    intro j hj
    exact eventually_nhdsWithin_of_eventually_nhds
      (eventually_lt_nhds (hw₀S j (Finset.mem_compl.mp hj)).1)
  obtain ⟨η, ⟨hηδ, hηb, hηS⟩, hη⟩ := (hev.and eventually_mem_nhdsWithin).exists
  rw [mem_Ioi] at hη
  set t : Fin d → ℝ := fun j ↦ if j ∈ R.primary α then 0 else w₀ j - η with ht_def
  have hBox_P : ∀ u ∈ pi univ fun j ↦ Icc (t j) (t j + η), ∀ j ∈ R.primary α, u j ∈ Icc 0 η :=
    fun u hu j hj ↦ by
      have := hu j (mem_univ j)
      simpa [ht_def, hj] using this
  have hBox_S : ∀ u ∈ pi univ fun j ↦ Icc (t j) (t j + η), ∀ j ∉ R.primary α,
      u j ∈ Icc (w₀ j - η) (w₀ j) := fun u hu j hj ↦ by
    have := hu j (mem_univ j)
    simpa [ht_def, hj] using this
  have hBox_sub : (pi univ fun j ↦ Icc (t j) (t j + η)) ⊆ cube d (R.b α) := fun u hu ↦ mem_cube.2
      fun j ↦ by
    by_cases hj : j ∈ R.primary α
    · obtain ⟨h1, h2⟩ := hBox_P u hu j hj
      exact ⟨h1, h2.trans hηb⟩
    · obtain ⟨h1, h2⟩ := hBox_S u hu j hj
      have := hηS j (Finset.mem_compl.mpr hj)
      have := (hw₀S j hj).2
      constructor <;> linarith
  refine ⟨t, η, c₀, hη, hc₀, fun j hj ↦ by simp [ht_def, hj], fun j hj ↦ ?_, hBox_sub,
    fun u hu ↦ ?_⟩
  · simp only [ht_def, hj, ite_false]
    linarith [hηS j (Finset.mem_compl.mpr hj)]
  · have hdist : dist u w₀ < δ₀ := by
      rw [dist_pi_lt_iff hδ₀]
      intro j
      rw [Real.dist_eq, abs_sub_lt_iff]
      by_cases hj : j ∈ R.primary α
      · obtain ⟨h1, h2⟩ := hBox_P u hu j hj
        rw [hw₀P j hj]
        constructor <;> linarith
      · obtain ⟨h1, h2⟩ := hBox_S u hu j hj
        constructor <;> linarith
    have := hδ (hBox_sub hu) hdist
    rw [Real.dist_eq, abs_sub_lt_iff] at this
    linarith

/-- The exponents `k_α` restricted to the primary coordinates (`0` elsewhere). -/
@[expose] noncomputable def primaryK (α : R.ι)
    (j : Fin d) : ℕ := if j ∈ R.primary α then R.k α j else 0

/-- The exponents `h_α` restricted to the primary coordinates (`0` elsewhere). -/
@[expose] noncomputable def primaryH (α : R.ι)
    (j : Fin d) : ℕ := if j ∈ R.primary α then R.h α j else 0

/-- The primary part `∏_{j primary} u_j^{2k_j}` of the chart monomial. -/
@[expose] noncomputable def primaryMonomial (α : R.ι) (u : Fin d → ℝ) : ℝ := ∏ j, u j ^
    (2 * R.primaryK α j)

/-- The primary part `∏_{j primary} u_j^{h_j}` of the monomial weight. -/
@[expose] noncomputable def primaryDensity (α : R.ι) (u : Fin d → ℝ) : ℝ :=
  ∏ j, u j ^ (R.primaryH α j : ℝ)

/-- The measure `∏_{j primary} u_j^{h_j} du`. -/
@[expose] noncomputable def primaryMeasure (α : R.ι) : Measure (Fin d → ℝ) :=
  volume.withDensity fun u ↦ ENNReal.ofReal (R.primaryDensity α u)

theorem primaryMonomial_eq (α : R.ι) (u : Fin d → ℝ) :
    R.primaryMonomial α u = ∏ j ∈ R.primary α, u j ^ (2 * R.k α j) := by
  rw [primaryMonomial, ← Finset.prod_mul_prod_compl (R.primary α)]
  have h1 : ∏ j ∈ R.primary α, u j ^ (2 * R.primaryK α j)
      = ∏ j ∈ R.primary α, u j ^ (2 * R.k α j) :=
    Finset.prod_congr rfl fun j hj ↦ by simp [primaryK, hj]
  have h2 : ∏ j ∈ (R.primary α)ᶜ, u j ^ (2 * R.primaryK α j) = 1 :=
    Finset.prod_eq_one fun j hj ↦ by simp [primaryK, Finset.mem_compl.mp hj]
  rw [h1, h2, mul_one]

theorem primaryDensity_eq (α : R.ι) (u : Fin d → ℝ) :
    R.primaryDensity α u = ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ) := by
  rw [primaryDensity, ← Finset.prod_mul_prod_compl (R.primary α)]
  have h1 : ∏ j ∈ R.primary α, u j ^ (R.primaryH α j : ℝ)
      = ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ) :=
    Finset.prod_congr rfl fun j hj ↦ by simp [primaryH, hj]
  have h2 : ∏ j ∈ (R.primary α)ᶜ, u j ^ (R.primaryH α j : ℝ) = 1 :=
    Finset.prod_eq_one fun j hj ↦ by simp [primaryH, Finset.mem_compl.mp hj]
  rw [h1, h2, mul_one]

theorem measurable_primaryMonomial (α : R.ι) : Measurable (R.primaryMonomial α) :=
  Finset.measurable_prod _ fun j _ ↦ (measurable_pi_apply j).pow_const _

/-- The primary monomial against the primary density has exponents `(λ_α, m_α)` on every cube
`[0, η]^d`: the coordinates outside the primary set are spectators. -/
theorem hasLLCExponentsOn_primaryMonomial (α : R.ι) {η : ℝ} (hη : 0 < η) :
    HasLLCExponentsOn (R.primaryMeasure α) (cube d η) (R.primaryMonomial α) (R.chartRlct α)
      (R.chartMult α) := by
  have hfilter : (Finset.univ.filter fun j ↦ 0 < R.primaryK α j ∧
      ((R.primaryH α j : ℝ) + 1) / (2 * R.primaryK α j) = R.chartRlct α) = R.primary α := by
    ext j
    rw [Finset.mem_filter]
    simp only [Finset.mem_univ, true_and, primaryK, primaryH]
    by_cases hj : j ∈ R.primary α
    · simp only [hj, ite_true, iff_true]
      exact ⟨R.k_pos_of_mem_primary hj, R.ratio_eq_of_mem_primary hj⟩
    · simp [hj]
  have hmin : ∀ j, 0 < R.primaryK α j →
      R.chartRlct α ≤ ((R.primaryH α j : ℝ) + 1) / (2 * R.primaryK α j) := by
    intro j hj
    have hjP : j ∈ R.primary α := by
      by_contra h
      simp [primaryK, h] at hj
    simp only [primaryK, primaryH, hjP, ite_true]
    exact (R.ratio_eq_of_mem_primary hjP).ge
  have hatt : ∃ j, 0 < R.primaryK α j ∧
      ((R.primaryH α j : ℝ) + 1) / (2 * R.primaryK α j) = R.chartRlct α := by
    obtain ⟨j, hj⟩ := R.primary_nonempty α
    refine ⟨j, ?_, ?_⟩
    · simpa [primaryK, hj] using R.k_pos_of_mem_primary hj
    · simp only [primaryK, primaryH, hj, ite_true]
      exact R.ratio_eq_of_mem_primary hj
  have h := hasLLCExponentsOn_monomial_cube (R.primaryK α) (R.primaryH α) (R.chartRlct_pos α)
    hmin hatt hη
  rw [hfilter] at h
  exact h

/-- Translating the box `∏_j [t_j, t_j + η]` back to `[0, η]^d`: the primary monomial and
density do not see a translation of the non-primary coordinates. -/
theorem sublevelVol_primaryMeasure_box (α : R.ι) {t : Fin d → ℝ}
    (htP : ∀ j ∈ R.primary α, t j = 0) (η ε : ℝ) :
    sublevelVol (R.primaryMeasure α) (pi univ fun j ↦ Icc (t j) (t j + η)) (R.primaryMonomial α) ε
      = sublevelVol (R.primaryMeasure α) (cube d η) (R.primaryMonomial α) ε := by
  have hBox : MeasurableSet (pi univ fun j ↦ Icc (t j) (t j + η)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  have hT := sublevelVol_withDensity_comp_measurePreserving (MeasurableEquiv.addRight t)
    (measurePreserving_add_right volume t)
    (w := fun u ↦ ENNReal.ofReal (R.primaryDensity α u)) hBox (R.measurable_primaryMonomial α) ε
  have h1 : ∀ x : Fin d → ℝ, R.primaryDensity α (x + t) = R.primaryDensity α x := fun x ↦
    Finset.prod_congr rfl fun j _ ↦ by
      by_cases hj : j ∈ R.primary α
      · simp [htP j hj]
      · simp [primaryH, hj]
  have h2 : ∀ x : Fin d → ℝ, R.primaryMonomial α (x + t) = R.primaryMonomial α x := fun x ↦
    Finset.prod_congr rfl fun j _ ↦ by
      by_cases hj : j ∈ R.primary α
      · simp [htP j hj]
      · simp [primaryK, hj]
  have h3 : (MeasurableEquiv.addRight t) ⁻¹' (pi univ fun j ↦ Icc (t j) (t j + η)) = cube d η := by
    ext u
    rw [mem_cube]
    simp only [mem_preimage, MeasurableEquiv.coe_addRight, mem_univ_pi, Pi.add_apply, mem_Icc]
    constructor <;> intro H j <;> have := H j <;> constructor <;> linarith
  rw [primaryMeasure, ← hT, h3]
  simp only [MeasurableEquiv.coe_addRight, h1, h2]

/-- An essential chart with positive trace mass is `Ω` of its scale:
`ε^{λ_α} (−log ε)^{m_α − 1} = O(V_α(ε))`. -/
theorem chartScale_isBigO_chartVolume {α : R.ι} (hT : 0 < R.essentialTraceMass α) :
    R.chartScale α =O[𝓝[>] (0 : ℝ)] R.chartVolume α := by
  obtain ⟨t, η, c₀, hη, hc₀, htP, htS, hBox_sub, hBox_weight⟩ := R.exists_box_of_traceMass_pos hT
  have hBox : MeasurableSet (pi univ fun j ↦ Icc (t j) (t j + η)) :=
    MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc
  set A₂ : ℝ := ∏ j ∈ (R.primary α)ᶜ, R.b α ^ (2 * R.k α j) with hA₂_def
  have hA₂ : 0 < A₂ := Finset.prod_pos fun j _ ↦ pow_pos (R.b_pos α) _
  set c₂ : ℝ := ∏ j ∈ (R.primary α)ᶜ, t j ^ (R.h α j : ℝ) with hc₂_def
  have hc₂ : 0 < c₂ := Finset.prod_pos fun j hj ↦
    Real.rpow_pos_of_pos (htS j (Finset.mem_compl.mp hj)) _
  -- pointwise on the box: the monomial is at most `A₂` times its primary part, the density at
  -- least `c₂ c₀` times its primary part
  have hmono : ∀ u ∈ pi univ fun j ↦ Icc (t j) (t j + η),
      R.cubeMonomial α u ≤ A₂ * R.primaryMonomial α u := by
    intro u hu
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ ((hBox_sub hu).1 j)
    have hub : ∀ j, u j ≤ R.b α := fun j ↦ ((hBox_sub hu).2 j)
    rw [cubeMonomial, primaryMonomial_eq, ← Finset.prod_mul_prod_compl (R.primary α), mul_comm]
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu0 j) _)
    exact Finset.prod_le_prod₀ (fun j _ ↦ pow_nonneg (hu0 j) _) fun j _ ↦
      pow_le_pow_left₀ (hu0 j) (hub j) _
  have hdens : ∀ u ∈ pi univ fun j ↦ Icc (t j) (t j + η),
      c₂ * c₀ * R.primaryDensity α u ≤ R.chartDensity α u := by
    intro u hu
    have hu0 : ∀ j, 0 ≤ u j := fun j ↦ ((hBox_sub hu).1 j)
    have hS : ∀ j ∈ (R.primary α)ᶜ, t j ≤ u j := fun j _ ↦ (hu j (mem_univ j)).1
    have hY : c₂ ≤ ∏ j ∈ (R.primary α)ᶜ, u j ^ (R.h α j : ℝ) :=
      Finset.prod_le_prod₀ (fun j hj ↦ Real.rpow_nonneg (htS j (Finset.mem_compl.mp hj)).le _)
        fun j hj ↦ Real.rpow_le_rpow (htS j (Finset.mem_compl.mp hj)).le (hS j hj)
          (Nat.cast_nonneg _)
    have hX : 0 ≤ ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ) :=
      Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu0 j) _
    rw [chartDensity, primaryDensity_eq, ← Finset.prod_mul_prod_compl (R.primary α)]
    calc c₂ * c₀ * ∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ)
        = (∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ)) * c₂ * c₀ := by ring
      _ ≤ (∏ j ∈ R.primary α, u j ^ (R.h α j : ℝ)) *
            (∏ j ∈ (R.primary α)ᶜ, u j ^ (R.h α j : ℝ)) * R.weight α u :=
          mul_le_mul (mul_le_mul_of_nonneg_left hY hX) (hBox_weight u hu) hc₀.le
            (mul_nonneg hX (hc₂.le.trans hY))
  -- the key inequality `c₂ c₀ V_P(ε / A₂) ≤ V_α(ε)`
  have hkey : ∀ ε, c₂ * c₀ *
      sublevelVol (R.primaryMeasure α) (cube d η) (R.primaryMonomial α) (ε / A₂)
        ≤ R.chartVolume α ε := by
    intro ε
    rw [← R.sublevelVol_primaryMeasure_box α htP η]
    have hS₁ : MeasurableSet ((pi univ fun j ↦ Icc (t j) (t j + η)) ∩
        {u | R.primaryMonomial α u ≤ ε / A₂}) :=
      hBox.inter (measurableSet_le (R.measurable_primaryMonomial α) measurable_const)
    have hsub : (pi univ fun j ↦ Icc (t j) (t j + η)) ∩ {u | R.primaryMonomial α u ≤ ε / A₂}
        ⊆ cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε} := by
      rintro u ⟨hu, hf⟩
      refine ⟨hBox_sub hu, ?_⟩
      simp only [mem_ofPred_eq] at hf ⊢
      calc R.cubeMonomial α u ≤ A₂ * R.primaryMonomial α u := hmono u hu
        _ ≤ A₂ * (ε / A₂) := by gcongr
        _ = ε := mul_div_cancel₀ _ hA₂.ne'
    rw [chartVolume, sublevelVol, sublevelVol, ← ENNReal.toReal_ofReal (mul_pos hc₂ hc₀).le,
      ← ENNReal.toReal_mul]
    refine ENNReal.toReal_mono (ne_top_of_le_ne_top (R.chartMeasure_cube_ne_top α)
      (measure_mono inter_subset_left)) ?_
    calc ENNReal.ofReal (c₂ * c₀) * R.primaryMeasure α ((pi univ fun j ↦ Icc (t j) (t j + η)) ∩
          {u | R.primaryMonomial α u ≤ ε / A₂})
        = ∫⁻ u in (pi univ fun j ↦ Icc (t j) (t j + η)) ∩ {u | R.primaryMonomial α u ≤ ε / A₂},
            ENNReal.ofReal (c₂ * c₀ * R.primaryDensity α u) := by
          rw [primaryMeasure, withDensity_apply _ hS₁, ← lintegral_const_mul' _ _
            ENNReal.ofReal_ne_top]
          exact lintegral_congr fun u ↦ (ENNReal.ofReal_mul (mul_pos hc₂ hc₀).le).symm
      _ ≤ ∫⁻ u in (pi univ fun j ↦ Icc (t j) (t j + η)) ∩ {u | R.primaryMonomial α u ≤ ε / A₂},
            ENNReal.ofReal (R.chartDensity α u) :=
          setLIntegral_mono' hS₁ fun u hu ↦ ENNReal.ofReal_le_ofReal (hdens u hu.1)
      _ = R.chartMeasure α ((pi univ fun j ↦ Icc (t j) (t j + η)) ∩
            {u | R.primaryMonomial α u ≤ ε / A₂}) := (withDensity_apply _ hS₁).symm
      _ ≤ R.chartMeasure α (cube d (R.b α) ∩ {u | R.cubeMonomial α u ≤ ε}) := measure_mono hsub
  have hP := R.hasLLCExponentsOn_primaryMonomial α hη
  have hcomp : (fun ε ↦ R.chartScale α (ε / A₂)) =O[𝓝[>] (0 : ℝ)]
      fun ε ↦ sublevelVol (R.primaryMeasure α) (cube d η) (R.primaryMonomial α) (ε / A₂) :=
    hP.2.comp_tendsto (tendsto_div_const_nhdsGT_zero hA₂)
  refine ((isTheta_llcScale_comp_div hA₂).symm.1).trans (hcomp.trans (IsBigO.of_bound
    (c₂ * c₀)⁻¹ (Eventually.of_forall fun ε ↦ ?_)))
  rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
    Real.norm_of_nonneg (R.chartVolume_nonneg α ε), ← div_eq_inv_mul, le_div_iff₀ (mul_pos hc₂ hc₀)]
  linarith [hkey ε]

/-! ## The sum: the atlas computes the type -/

/-- Every chart scale is `O` of the atlas scale `ε^λ (−log ε)^{m−1}`: `λ ≤ λ_α`, and `m_α ≤ m`
when `λ_α = λ`. -/
theorem chartScale_isBigO (α : R.ι) :
    R.chartScale α =O[𝓝[>] (0 : ℝ)] llcScale R.rlct R.mult := by
  refine isBigO_llcScale_of_lex ?_
  rcases eq_or_lt_of_le (R.rlct_le_chartRlct α) with h | h
  · exact Or.inr ⟨h, by exact_mod_cast R.chartMult_le_mult h.symm⟩
  · exact Or.inl h

end ResolutionAtlas

/-- The sublevel sets of `K` and of a `K'` agreeing with `K` on `W` coincide on `W`. -/
protected theorem IsSingularityType.congr {K K' φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {lam : ℝ}
    {m : ℕ}
    (h : ∀ w ∈ W, K w = K' w) (hK : IsSingularityType K φ W lam m) :
    IsSingularityType K' φ W lam m := by
  have hset : ∀ ε, W ∩ {w | K w ≤ ε} = W ∩ {w | K' w ≤ ε} := fun ε ↦ by
    ext w
    simp only [mem_inter_iff, mem_ofPred_eq]
    exact and_congr_right fun hw ↦ by rw [h w hw]
  simpa only [IsSingularityType, hset] using hK

namespace NondegenerateResolutionAtlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : NondegenerateResolutionAtlas K φ W)

/-- **Every nondegenerate resolution atlas computes the singularity type.** [Hit26,
Equation (5.2.1)]: the chart-wise `(λ, m)` of a
nondegenerate atlas of `(K, φ, W)` is the intrinsic singularity type by volume scaling, `V(ε) = ∫_{W
∩ {K ≤ ε}} φ =Θ ε^λ (−log ε)^{m−1}`. Hypotheses beyond the atlas: `W` measurable, `K` measurable, `φ
≥ 0` and a.e.-measurable on `W` (no integrability of `φ` is needed: the transport identity confines
`V(ε)`, `ε < δ`, to the chart cubes). -/
theorem isSingularityType (hW : MeasurableSet W) (hKm : Measurable K) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφm : AEMeasurable φ (volume.restrict W)) : IsSingularityType K φ W R.rlct R.mult := by
  rw [isSingularityType_iff hW hφ hφm, HasLLCExponentsOn]
  have hV : sublevelVol (priorMeasure φ Set.univ) W K =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε ↦ ∑ α, R.toResolutionAtlas.chartVolume α ε := by
    filter_upwards [Ioo_mem_nhdsGT R.δ_pos] with ε hε
    exact R.toResolutionAtlas.sublevelVol_priorMeasure_eq_sum hW hKm hε.2
  rw [Filter.EventuallyEq.isTheta_congr_left hV]
  obtain ⟨α₀, hα₀, hT⟩ := R.traceMass_pos
  refine isTheta_sum_of_isBigO α₀ (fun α ↦ (R.toResolutionAtlas.chartVolume_isBigO α).trans
    (R.toResolutionAtlas.chartScale_isBigO α)) ?_
    fun α ↦ Eventually.of_forall (R.toResolutionAtlas.chartVolume_nonneg α)
  have : llcScale R.rlct R.mult = R.toResolutionAtlas.chartScale α₀ := by
    rw [ResolutionAtlas.chartScale, hα₀.1, hα₀.2]
  rw [this]
  exact R.toResolutionAtlas.chartScale_isBigO_chartVolume hT

/-- Thesis, remark after [Hit26, Definition 6.2.1] ("the local learning
coefficient does not depend on the choice of resolution"), for the global pair: two
nondegenerate atlases of `(K, φ, W)` have the same `λ`. -/
theorem rlct_eq_rlct (R' : NondegenerateResolutionAtlas K φ W) (hW : MeasurableSet W)
    (hKm : Measurable K) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφm : AEMeasurable φ (volume.restrict W)) :
    R.rlct = R'.rlct :=
  ((R.isSingularityType hW hKm hφ hφm).unique (R'.isSingularityType hW hKm hφ hφm)).1

/-- Two nondegenerate atlases of `(K, φ, W)` have the same multiplicity `m`. -/
theorem mult_eq_mult (R' : NondegenerateResolutionAtlas K φ W) (hW : MeasurableSet W)
    (hKm : Measurable K) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφm : AEMeasurable φ (volume.restrict W)) :
    R.mult = R'.mult :=
  ((R.isSingularityType hW hKm hφ hφm).unique (R'.isSingularityType hW hKm hφ hφm)).2

end NondegenerateResolutionAtlas

/-- **Existence of the singularity type** (from Hironaka's theorem), in the setting of [Hit26,
Theorem 3.3.9]: `W` compact semianalytic, `K ≥ 0` and `φ ≥ 0` real
analytic on an open neighbourhood of `W`, the conditions at `W₀` of
`exists_nondegenerateResolutionAtlas`. The type is read off the nondegenerate atlas of
`Resolution/FromHironaka.lean`; `λ > 0` and `m ≥ 1` come with it. -/
theorem exists_isSingularityType {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hWs : Semianalytic W)
    {U : Set (Fin d → ℝ)} (hU : IsOpen U) (hWU : W ⊆ U) (hKa : AnalyticOnNhd ℝ K U)
    (hK : ∀ w ∈ W, 0 ≤ K w) (hφa : AnalyticOnNhd ℝ φ U) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hK₀ : K w₀ = 0)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0)) (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w)) :
    ∃ (lam : ℝ) (m : ℕ), 0 < lam ∧ 0 < m ∧ IsSingularityType K φ W lam m := by
  classical
  obtain ⟨R⟩ := exists_nondegenerateResolutionAtlas_of_analytic hW hWs hU hWU hKa hK hφa hφ
    hw₀ hK₀ hKg hφg hvol
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  have hagree : ∀ w ∈ W, K w = W.piecewise K 0 w := fun w hw ↦
    (Set.piecewise_eq_of_mem W _ _ hw).symm
  have hKm : Measurable (W.piecewise K 0) :=
    ContinuousOn.measurable_piecewise (hKa.continuousOn.mono hWU) continuousOn_const hWm
  have hφm : AEMeasurable φ (volume.restrict W) := (hφa.continuousOn.mono hWU).aemeasurable hWm
  refine ⟨R.rlct, R.mult, R.toResolutionAtlas.rlct_pos, R.toResolutionAtlas.mult_pos, ?_⟩
  exact ((R.congr hagree).isSingularityType hWm hKm hφ hφm).congr fun w hw ↦ (hagree w hw).symm

end SingularLearningTheory
