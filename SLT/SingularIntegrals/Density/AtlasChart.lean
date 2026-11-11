/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Density.Asymptotic
import SLT.SingularIntegrals.Density.Continuity
public import SLT.SingularIntegrals.Density.Chart
import SLT.SingularIntegrals.TypeOfAtlas
public import SLT.SingularIntegrals.Resolution
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Density and derivative of a resolution chart

Extend the chart weight continuously by clamping to its compact cube. The slice
formula then supplies both the derivative of its sublevel mass and its asymptotic.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.ResolutionAtlas
open SliceDensity

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The chart weight extended continuously to the ambient space by clamping to its cube. -/
@[expose] noncomputable def densityWeight (α : R.ι) (u : Fin d → ℝ) : ℝ :=
  R.weight α (R.clamp α u)

theorem continuous_densityWeight (α : R.ι) : Continuous (R.densityWeight α) :=
  (R.weight_continuousOn α).comp_continuous
    (continuous_subtype_val.comp (R.continuous_clamp α)) fun u ↦ (R.clamp α u).2

theorem densityWeight_eq {α : R.ι} {u : Fin d → ℝ} (hu : u ∈ cube d (R.b α)) :
    R.densityWeight α u = R.weight α u := by
  unfold densityWeight
  rw [R.clamp_of_mem hu]

theorem densityWeight_nonneg (α : R.ι) (u : Fin d → ℝ) : 0 ≤ R.densityWeight α u :=
  R.weight_nonneg α _ (R.clamp α u).2

theorem contDiffOn_densityWeight (α : R.ι) :
    ContDiffOn ℝ 1 (R.densityWeight α) (cube d (R.b α)) :=
  (R.weight_contDiffOn α).congr fun _u hu ↦ R.densityWeight_eq hu

/-- A single chart, with its extended weight, regarded as a monomial resolution atlas. -/
@[expose] noncomputable def densityAtlas (α : R.ι) :=
  monomialAtlas (R.k α) (R.h α) (R.b α) (R.densityWeight α) (R.b_pos α)
    (R.active α) (R.contDiffOn_densityWeight α) (fun u _ ↦ R.densityWeight_nonneg α u)

@[simp] theorem densityAtlas_rlct (α : R.ι) : (R.densityAtlas α).rlct = R.chartRlct α :=
  monomialAtlas.rlct_eq ..

@[simp] theorem densityAtlas_mult (α : R.ι) : (R.densityAtlas α).mult = R.chartMult α :=
  monomialAtlas.mult_eq ..

theorem densityAtlas_coefficient {α : R.ι} (hα : R.chartRlct α = R.rlct) :
    (R.densityAtlas α).sublevelCoefficient = R.sublevelChartCoefficient α := by
  rw [densityAtlas, monomialAtlas.coefficient_eq]
  change (R.densityAtlas α).sublevelChartCoefficient () = _
  unfold sublevelChartCoefficient
  have hrlct : (R.densityAtlas α).rlct = R.rlct := (R.densityAtlas_rlct α).trans hα
  rw [hrlct]
  congr 1
  unfold essentialTraceMass
  apply setIntegral_congr_fun (R.measurableSet_cube α)
  intro v hv
  have hz : ((R.primary α)ᶜ.piecewise v (0 : Fin d → ℝ)) ∈ cube d (R.b α) := by
    refine mem_cube.2 fun j ↦ ?_
    by_cases hmem : j ∈ (R.primary α)ᶜ
    · simpa only [Finset.piecewise, hmem, ite_true] using mem_cube.1 hv j
    · simp only [Finset.piecewise, hmem, ite_false, Pi.zero_apply, mem_Icc, le_refl,
        true_and]
      exact (R.b_pos α).le
  have hexp : (R.densityAtlas α).secondaryExponent () = R.secondaryExponent α := by
    unfold secondaryExponent
    rw [hrlct]
    rfl
  change (∏ j ∈ (R.primary α)ᶜ, v j ^ (R.densityAtlas α).secondaryExponent () j) *
    R.densityWeight α ((R.primary α)ᶜ.piecewise v 0) = _
  rw [hexp, R.densityWeight_eq hz]

/-- A chosen primary coordinate, used to solve the monomial level equation. -/
noncomputable def densityCoordinate (α : R.ι) : Fin d := (R.primary_nonempty α).choose

theorem densityCoordinate_mem (α : R.ι) : R.densityCoordinate α ∈ R.primary α :=
  (R.primary_nonempty α).choose_spec

theorem densityCoordinate_pos (α : R.ι) : 0 < R.k α (R.densityCoordinate α) :=
  R.k_pos_of_mem_primary (R.densityCoordinate_mem α)

section PositiveDimension
variable {n : ℕ} {K φ : (Fin (n + 1) → ℝ) → ℝ} {W : Set (Fin (n + 1) → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The real-valued slice density of one chart, integrating out its chosen primary coordinate. -/
@[expose] noncomputable def chartStateDensity (α : R.ι) (t : ℝ) : ℝ :=
  (sliceDens (R.k α) (R.h α) (R.b α) (R.densityWeight α) (R.densityCoordinate α) t).toReal

theorem chartStateDensity_nonneg (α : R.ι) (t : ℝ) : 0 ≤ R.chartStateDensity α t :=
  ENNReal.toReal_nonneg

theorem tendsto_chartStateDensity (α : R.ι) :
    Tendsto (fun t ↦ t * R.chartStateDensity α t /
      (t ^ R.chartRlct α * (-Real.log t) ^ (R.chartMult α - 1))) (𝓝[>] 0)
      (𝓝 (R.chartRlct α * (R.densityAtlas α).sublevelCoefficient)) := by
  obtain ⟨L, hL⟩ := R.exists_lipschitzOnWith_weight α
  have hsum : ∀ u ∈ cube (n + 1) (R.b α), ∀ v ∈ cube (n + 1) (R.b α),
      |R.densityWeight α u - R.densityWeight α v| ≤ (L : ℝ) * ∑ j, |u j - v j| := by
    intro u hu v hv
    rw [R.densityWeight_eq hu, R.densityWeight_eq hv, ← Real.dist_eq]
    apply (hL.dist_le_mul u hu v hv).trans
    apply mul_le_mul_of_nonneg_left _ L.2
    apply (dist_pi_le_iff (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)).mpr
    intro j
    rw [Real.dist_eq]
    exact Finset.single_le_sum (f := fun j ↦ |u j - v j|)
      (fun _ _ ↦ abs_nonneg _) (Finset.mem_univ j)
  have h := tendsto_chart_density (R.b_pos α) (R.densityCoordinate_pos α)
    (R.continuous_densityWeight α) (R.contDiffOn_densityWeight α)
    (R.densityWeight_nonneg α) (R.densityCoordinate_mem α) L.2 hsum
  change Tendsto (fun t ↦ t * R.chartStateDensity α t /
    (t ^ (R.densityAtlas α).rlct * (-Real.log t) ^ ((R.densityAtlas α).mult - 1)))
    (𝓝[>] 0) (𝓝 ((R.densityAtlas α).rlct * (R.densityAtlas α).sublevelCoefficient)) at h
  simpa only [R.densityAtlas_rlct, R.densityAtlas_mult] using h

/-- The sublevel volume of a monomial chart differentiates to its slice density. -/
theorem hasDerivAt_chartVolume (α : R.ι) {t : ℝ} (ht : 0 < t)
    (htb : t < R.b α ^ aExp (R.k α) (R.densityCoordinate α)) :
    HasDerivAt (sublevelVolume (fun u ↦ ∏ j, u j ^ (2 * R.k α j))
      (fun u ↦ (∏ j, u j ^ (R.h α j : ℝ)) * R.densityWeight α u)
      (cube (n + 1) (R.b α))) (R.chartStateDensity α t) t := by
  have hfc := R.continuous_densityWeight α
  have hν := isStateDensity_slice (h := R.h α) (R.b_pos α) (R.densityCoordinate_pos α)
    hfc.measurable hfc.continuousOn
  have hc := continuousAt_sliceDens (h := R.h α) (R.b_pos α)
    (R.densityCoordinate_pos α) hfc ht htb
  apply hν.hasDerivAt_sublevelVolume SliceDensity.measurable_monomial (by fun_prop)
    (ae_restrict_of_forall_mem (R.measurableSet_cube α) fun u hu ↦
      mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
        (R.densityWeight_nonneg α u))
    (fun _ ↦ (integrable_slice (R.b_pos α) (R.densityCoordinate_pos α)
      hfc.measurable hfc.continuousOn).integrableOn)
  exact (ENNReal.continuousAt_toReal hc.2).comp hc.1

end PositiveDimension
end SingularLearningTheory.ResolutionAtlas
