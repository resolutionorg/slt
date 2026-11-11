/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.HalfRadial.Measure
public import SLT.BayesGibbs.Pair.MeasureConvergence
public import SLT.BayesGibbs.Weighted.ContinuousChartProbability
import SLT.BayesGibbs.Weighted.ContinuousChart
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# Convergence of pair insertions

Pair insertion convergence, obtained from single marks, without kernel differentiability or a
further empirical process theorem.
-/

public section

namespace SingularLearningTheory.ResolutionAtlas

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The metric on `SingularLearningTheory.ResolutionAtlas.FaceDomain` given by
`Metric.Sigma.metricSpace`: each chart cube keeps its own metric, and points of different cubes
are at distance at least $1$. Mathlib does not make this metric on a sigma type an instance, so
it is a local instance here. -/
noncomputable local instance pairRadialConvergenceMetric1 : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace

/-- The bounded-field/primary-modulus classes used in the chart limit. -/
@[expose] def halfRadialGoodSet (j : ℕ) : Set R.ChartFunctions :=
  {ζ | ∀ α, ‖ζ α‖ ≤ j ∧ ∀ u : cube d (R.b α),
    |ζ α u - ζ α (R.primaryZero α u)| ≤
      j * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i}

/-- Single marks converge uniformly over the common good class, including
nonessential charts with their zero limiting mass. -/
theorem halfRadialMeasure_uniform_test {β : ℝ} (hβ : 0 < β) (j : ℕ)
    (mark : C(R.FaceDomain, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ ζ ∈ R.halfRadialGoodSet j,
      |(∫ u, mark u ∂R.halfRadialMeasure β n ζ) -
        ∫ u, mark u ∂R.halfRadialLimitMeasure β hβ ζ| ≤ ε := by
  have hc : 0 < (Fintype.card R.ι : ℝ) := by exact_mod_cast Fintype.card_pos
  have heps : 0 < ε / (Fintype.card R.ι : ℝ) := div_pos hε hc
  have hα : ∀ α : R.ι, ∀ᶠ n : ℕ in atTop, ∀ ζ ∈ R.halfRadialGoodSet j,
      |R.halfRadialScale n *
        R.chartRadialInsertion α β (1 / 2) n (ζ α) (R.markedChartWeight α mark) -
        (if R.IsEssential α then
          R.chartRadialLimit β (1 / 2) α (ζ α) (R.markedChartWeight α mark) else 0)|
        ≤ ε / (Fintype.card R.ι : ℝ) := by
    intro α
    by_cases hα : R.IsEssential α
    · obtain ⟨N, hN⟩ := R.essential_continuous_radial_insertion_uniform hα hβ
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (R.markedChartWeight α mark) j j heps
      filter_upwards [eventually_ge_atTop N] with n hn ζ hζ
      simpa only [halfRadialScale, if_pos hα] using hN n hn (ζ α) (hζ α).1 (hζ α).2
    · obtain ⟨N, hN⟩ := R.nonessential_radial_insertion_uniform hα hβ
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (norm_nonneg (R.markedChartWeight α mark)) j heps
      filter_upwards [eventually_ge_atTop N] with n hn ζ hζ
      simpa only [halfRadialScale, if_neg hα, sub_zero] using
        hN n hn (ζ α) (R.markedChartWeight α mark) (hζ α).1 le_rfl
  filter_upwards [Filter.eventually_all.mpr hα] with n hn ζ hζ
  rw [R.integral_halfRadialMeasure, R.integral_halfRadialLimitMeasure_eq_chart,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ α, |R.halfRadialScale n *
        R.chartRadialInsertion α β (1 / 2) n (ζ α) (R.markedChartWeight α mark) -
        (if R.IsEssential α then
          R.chartRadialLimit β (1 / 2) α (ζ α) (R.markedChartWeight α mark) else 0)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _α : R.ι, ε / (Fintype.card R.ι : ℝ) :=
      Finset.sum_le_sum fun α _ ↦ hn α ζ hζ
    _ = ε := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp [hc.ne']

/-- The limiting half-radial masses are bounded on bounded fields, by compact
continuity of the one-dimensional frozen kernel. -/
theorem halfRadialLimitMeasure_mass_bound {β : ℝ} (hβ : 0 < β) (j : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ ζ ∈ R.halfRadialGoodSet j,
      (R.halfRadialLimitMeasure β hβ ζ).real univ ≤ D := by
  let g : C(Icc (-(j : ℝ)) (j : ℝ), ℝ) :=
    ⟨fun x ↦ frozenInner (R.rlct + 1 / 2) β x,
      (continuous_frozenInner (by linarith [R.rlct_pos]) hβ).comp continuous_subtype_val⟩
  refine ⟨‖g‖ * R.essentialFaceMeasure.real univ, by positivity, fun ζ hζ ↦ ?_⟩
  have heval (u : R.FaceDomain) : frozenInner (R.rlct + 1 / 2) β (ζ u.1 u.2) ≤ ‖g‖ := by
    have hb : |ζ u.1 u.2| ≤ j :=
      (show |ζ u.1 u.2| ≤ ‖ζ u.1‖ from by
        simpa only [Real.norm_eq_abs] using (ζ u.1).norm_coe_le_norm u.2).trans (hζ u.1).1
    let x : Icc (-(j : ℝ)) (j : ℝ) := ⟨ζ u.1 u.2, abs_le.mp hb⟩
    exact (le_abs_self (g x)).trans (by simpa only [Real.norm_eq_abs] using g.norm_coe_le_norm x)
  have hmass := R.integral_halfRadialLimitMeasure β hβ ζ (1 : C(R.FaceDomain, ℝ))
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one, one_mul] at hmass
  rw [hmass]
  calc
    _ ≤ ∫ _u, ‖g‖ ∂R.essentialFaceMeasure := integral_mono
      (Continuous.integrable_of_compactSpace _
        (R.halfRadialLimitDensity β hβ ζ).continuous) (integrable_const _) heval
    _ = _ := by rw [integral_const, smul_eq_mul]; ring

/-- The n-dependent masses inherit a uniform eventual bound from the scalar
single-mark limit with mark one. -/
theorem halfRadialMeasure_combined_mass_bound {β : ℝ} (hβ : 0 < β) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop, ∀ ζ ∈ R.halfRadialGoodSet j,
      (R.halfRadialMeasure β n ζ).real univ +
        (R.halfRadialLimitMeasure β hβ ζ).real univ ≤ C := by
  obtain ⟨D, hD, hDb⟩ := R.halfRadialLimitMeasure_mass_bound hβ j
  refine ⟨2 * D + 2, by positivity, ?_⟩
  filter_upwards [R.halfRadialMeasure_uniform_test hβ j (1 : C(R.FaceDomain, ℝ)) zero_lt_one]
    with n hn ζ hζ
  have hdiff := hn ζ hζ
  simp only [ContinuousMap.one_apply, integral_const, smul_eq_mul, mul_one] at hdiff
  have hup := (le_abs_self _).trans hdiff
  have hν := hDb ζ hζ
  linarith

/-- Uniform continuous-kernel pair insertion convergence on each good class. -/
theorem pair_halfRadial_uniform {β : ℝ} (hβ : 0 < β) (j : ℕ)
    (F : C(R.FaceDomain × R.FaceDomain, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ ζ ∈ R.halfRadialGoodSet j,
      |(∫ z, F z ∂(R.halfRadialMeasure β n ζ).prod (R.halfRadialMeasure β n ζ)) -
        ∫ z, F z ∂(R.halfRadialLimitMeasure β hβ ζ).prod
          (R.halfRadialLimitMeasure β hβ ζ)| ≤ ε := by
  obtain ⟨C, hC, hmass⟩ := R.halfRadialMeasure_combined_mass_bound hβ j
  exact pair_integral_uniform_of_tests_uniform
    (R.halfRadialMeasure β) (R.halfRadialLimitMeasure β hβ)
    (R.halfRadialGoodSet j) hC hmass
    (fun mark ε hε ↦ R.halfRadialMeasure_uniform_test hβ j mark hε) F hε

namespace EmpiricalProcessInput

variable {R} {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

/-- Finite-chart simultaneous control, deduced from the already proved
single-chart probability estimate rather than redoing the norm-tightness proof. -/
theorem halfRadialGoodSet_tight :
    ∀ η > 0, ∃ j N : ℕ, ∀ n ≥ N,
      P {ω | I.Ξ n ω ∉ R.halfRadialGoodSet j} ≤ ENNReal.ofReal η := by
  intro η hη
  have hc : 0 < (Fintype.card R.ι : ℝ) := by exact_mod_cast Fintype.card_pos
  choose J N hJN using fun α : R.ι ↦
    I.chart_field_control_tight α (η / (Fintype.card R.ι : ℝ)) (div_pos hη hc)
  refine ⟨Finset.univ.sup J, Finset.univ.sup N, fun n hn ↦ ?_⟩
  let bad (α : R.ι) : Set Ω := {ω | I.Ξ n ω α ∉
    {ζ : C(cube d (R.b α), ℝ) | ‖ζ‖ ≤ J α ∧
      ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
        J α * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i}}
  have hcover : {ω | I.Ξ n ω ∉ R.halfRadialGoodSet (Finset.univ.sup J)} ⊆ ⋃ α, bad α := by
    intro ω hω
    by_contra hnot
    have hall : ∀ α, I.Ξ n ω α ∈
        {ζ : C(cube d (R.b α), ℝ) | ‖ζ‖ ≤ J α ∧
          ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
            J α * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i} := by
      simpa only [bad, mem_iUnion, mem_ofPred_eq, not_exists, not_not] using hnot
    apply hω
    intro α
    have hj : (J α : ℝ) ≤ Finset.univ.sup J := by
      exact_mod_cast (Finset.le_sup (Finset.mem_univ α) : J α ≤ Finset.univ.sup J)
    refine ⟨(hall α).1.trans hj, fun u ↦ ((hall α).2 u).trans ?_⟩
    exact mul_le_mul_of_nonneg_right hj
      (Finset.sum_nonneg fun i _ ↦ u.2.1 i)
  calc
    _ ≤ P (⋃ α, bad α) := measure_mono hcover
    _ ≤ ∑ α, P (bad α) := measure_iUnion_fintype_le P bad
    _ ≤ ∑ _α : R.ι, ENNReal.ofReal (η / (Fintype.card R.ι : ℝ)) :=
      Finset.sum_le_sum fun α _ ↦ hJN α n
        ((Finset.le_sup (Finset.mem_univ α) : N α ≤ Finset.univ.sup N).trans hn)
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ (div_pos hη hc).le)]
      congr 1
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hc.ne']

/-- The pair radial numerator is approximated in probability by the same
kernel evaluated against the current-field essential-face radial measure. -/
theorem pair_halfRadial_sub_limit_tendstoInMeasure (hβ : 0 < β)
    (F : C(R.FaceDomain × R.FaceDomain, ℝ)) :
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦
        (∫ z, F z ∂(R.halfRadialMeasure β n (I.Ξ n ω)).prod
          (R.halfRadialMeasure β n (I.Ξ n ω))) -
        ∫ z, F z ∂(R.halfRadialLimitMeasure β hβ (I.Ξ n ω)).prod
          (R.halfRadialLimitMeasure β hβ (I.Ξ n ω))) atTop 0 := by
  apply tendstoInMeasure_of_uniform_on
    (B := R.halfRadialGoodSet) (X := I.Ξ)
    (F := fun n ζ ↦ ∫ z, F z ∂(R.halfRadialMeasure β n ζ).prod (R.halfRadialMeasure β n ζ))
    (G := fun ζ ↦ ∫ z, F z ∂(R.halfRadialLimitMeasure β hβ ζ).prod
      (R.halfRadialLimitMeasure β hβ ζ))
  · intro j ε hε
    exact eventually_atTop.1 (R.pair_halfRadial_uniform hβ j F hε)
  · exact I.halfRadialGoodSet_tight

end EmpiricalProcessInput
end SingularLearningTheory.ResolutionAtlas
