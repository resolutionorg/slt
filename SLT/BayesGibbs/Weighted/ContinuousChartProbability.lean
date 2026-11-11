/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.ContinuousChart
public import SLT.BayesGibbs.Weighted.ChartLimit

/-!
# Marked radial chart integrals in probability

On a chart of a resolution atlas, the posterior integral with a continuous mark $A$ and an extra
factor $(u^{2k})^p$, scaled by $n^{\lambda + p}/(\log n)^{m-1}$, approaches its marked radial limit
uniformly over chart fields with bounded norm and a bounded Lipschitz constant in the primary
coordinates. This module evaluates these integrals at the chart processes $\xi_n$ of an empirical
process input and proves that the error tends to zero in probability, for one chart and for the
sum over all charts. The limit vanishes on the charts that are not essential.

## Main results

* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.chart_field_control_tight`: with
  probability close to one, uniformly in $n$, the chart process has bounded norm and bounded
  Lipschitz constant in the primary coordinates.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.continuous_radial_insertion_sub_limit_tendstoInMeasure`:
  the marked radial integral on one chart minus its limit tends to zero in probability.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.continuous_radial_sum_sub_limit_tendstoInMeasure`:
  the same for the sum over all charts, whose limit is a sum over the essential charts.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {R : ResolutionAtlas K φ W} {β : ℝ}
  {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

/-- Joint norm and primary-modulus control already supplied by I. -/
theorem chart_field_control_tight (α : R.ι) :
    ∀ η > 0, ∃ j N : ℕ, ∀ n ≥ N,
      P {ω | I.Ξ n ω α ∉ {ζ : C(cube d (R.b α), ℝ) |
        ‖ζ‖ ≤ j ∧ ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
          j * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i}} ≤ ENNReal.ofReal η := by
  have hnorm : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < ‖I.Ξ n ω α‖} ≤ ENNReal.ofReal η := fun η hη ↦
    (I.tendsto.continuous_comp (continuous_apply α)).eventually_measure_norm_gt_le hη
  intro η hη
  obtain ⟨M, N₁, hN₁⟩ := hnorm (η / 2) (half_pos hη)
  obtain ⟨L, N₂, hN₂⟩ := I.lipschitz_tight (η / 2) (half_pos hη)
  refine ⟨⌈max M L⌉₊, max N₁ N₂, fun n hn ↦ ?_⟩
  have hM : M ≤ ⌈max M L⌉₊ := (le_max_left M L).trans (Nat.le_ceil _)
  have hL : L ≤ ⌈max M L⌉₊ := (le_max_right M L).trans (Nat.le_ceil _)
  calc P {ω | I.Ξ n ω α ∉ {ζ : C(cube d (R.b α), ℝ) |
        ‖ζ‖ ≤ ⌈max M L⌉₊ ∧ ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
          ⌈max M L⌉₊ * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i}}
      ≤ P ({ω | M < ‖I.Ξ n ω α‖} ∪ {ω | ¬ ∀ α, ∀ u : cube d (R.b α),
          |I.Ξ n ω α u - I.Ξ n ω α (R.primaryZero α u)| ≤
            L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j}) := by
        refine measure_mono fun ω hω ↦ ?_
        by_contra hcon
        simp only [mem_union, mem_ofPred_eq, not_or, not_lt, not_not] at hcon
        obtain ⟨hMω, hLω⟩ := hcon
        refine hω ⟨hMω.trans hM, fun u ↦ (hLω α u).trans
          (mul_le_mul_of_nonneg_right hL ?_)⟩
        exact Finset.sum_nonneg fun i _ ↦ u.2.1 i
    _ ≤ P {ω | M < ‖I.Ξ n ω α‖} + P {ω | ¬ ∀ α, ∀ u : cube d (R.b α),
          |I.Ξ n ω α u - I.Ξ n ω α (R.primaryZero α u)| ≤
            L * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
        add_le_add (hN₁ n (le_of_max_le_left hn)) (hN₂ n (le_of_max_le_right hn))
    _ = ENNReal.ofReal η := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity), add_halves]

/-- Continuous fixed marked radial insertion limit in probability. -/
theorem continuous_radial_insertion_sub_limit_tendstoInMeasure (α : R.ι) {p : ℝ}
    (hβ : 0 < β) (hp : 0 ≤ p) (A : C(cube d (R.b α), ℝ)) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n (I.Ξ n ω α) A -
        (if R.IsEssential α then R.chartRadialLimit β p α (I.Ξ n ω α) A else 0)) atTop 0 := by
  refine tendstoInMeasure_of_uniform_on (X := fun n ω ↦ I.Ξ n ω α)
    (G := fun ζ ↦ if R.IsEssential α then R.chartRadialLimit β p α ζ A else 0)
    (F := fun (n : ℕ) ζ ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
      R.chartRadialInsertion α β p n ζ A)
    (B := fun j : ℕ ↦ {ζ : C(cube d (R.b α), ℝ) |
      ‖ζ‖ ≤ j ∧ ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
        j * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i})
    (fun j ε hε ↦ ?_) (I.chart_field_control_tight α)
  by_cases hα : R.IsEssential α
  · obtain ⟨N, hN⟩ := R.essential_continuous_radial_insertion_uniform hα hβ hp A j j hε
    refine ⟨N, fun n hn ζ hζ ↦ ?_⟩
    simp only [ite_eq_left hα]
    exact hN n hn ζ hζ.1 hζ.2
  · obtain ⟨N, hN⟩ := R.nonessential_radial_insertion_uniform hα hβ hp (norm_nonneg A) j hε
    refine ⟨N, fun n hn ζ hζ ↦ ?_⟩
    simp only [ite_eq_right hα, sub_zero]
    exact hN n hn ζ A hζ.1 le_rfl

/-- Summing all charts retains the essential-face marked functional. -/
theorem continuous_radial_sum_sub_limit_tendstoInMeasure {p : ℝ}
    (hβ : 0 < β) (hp : 0 ≤ p) (A : R.ChartFunctions) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        (∑ α, R.chartRadialInsertion α β p n (I.Ξ n ω α) (A α)) -
        ∑ α, if R.IsEssential α then R.chartRadialLimit β p α (I.Ξ n ω α) (A α) else 0)
      atTop 0 := by
  have h := tendstoInMeasure_finset_sum_zero Finset.univ
    (fun α _ ↦ I.continuous_radial_insertion_sub_limit_tendstoInMeasure α hβ hp (A α))
  simpa only [Finset.sum_sub_distrib, Finset.mul_sum] using h

end SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput
