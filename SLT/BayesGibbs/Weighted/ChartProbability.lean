/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.ChartLimit
import SLT.BayesGibbs.Weighted.BlockLimit

/-!
# Marked radial integrals of the chart process in probability

On a chart $\alpha$ of a resolution atlas, evaluate the marked radial integral
`SingularLearningTheory.ResolutionAtlas.chartRadialInsertion` at the chart process $\xi_n$ of an
empirical process input, scaled by $n^{\lambda + p}/(\log n)^{m-1}$. Its difference from the
limit at the same field, `SingularLearningTheory.ResolutionAtlas.chartRadialLimit` on essential
charts and zero on the others, tends to zero in probability. The mark $A(\xi_n)$ may depend on
the field, as long as fields of bounded norm and bounded Lipschitz constant in the primary
coordinates give marks of the same kind. The proof combines the uniform convergence of the
scaled integral on such sets of fields with the tightness of $\|\xi_n\|$ and of the primary
Lipschitz constants of $\xi_n$. These convergences give the limits of the posterior integrals
with a feature inserted.

## Main results

* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.radial_insertion_sub_limit_tendstoInMeasure`:
  the convergence for a mark that depends on the field.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.fixed_radial_insertion_sub_limit_tendstoInMeasure`:
  the convergence for a fixed mark with a primary Lipschitz bound.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.self_mark_radial_insertion_sub_limit_tendstoInMeasure`:
  the convergence for the self mark $a\xi_n$, which the limit of the training Gibbs error needs.
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

/-- Marked chart insertions converge in probability to their frozen value
at the current field. The amplitude may depend on that field; its only input
is a deterministic bounded-set estimate. In particular this handles a fixed
mark and the self mark A(ζ)=a*ζ, without another process convergence theorem. -/
theorem radial_insertion_sub_limit_tendstoInMeasure (α : R.ι) {p : ℝ}
    (hβ : 0 < β) (hp : 0 ≤ p)
    (A : C(cube d (R.b α), ℝ) → C(cube d (R.b α), ℝ))
    (hA : ∀ j : ℕ, ∃ P₀ LA : ℝ, ∀ ζ : C(cube d (R.b α), ℝ),
      ‖ζ‖ ≤ j →
      (∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
        j * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i) →
      ‖A ζ‖ ≤ P₀ ∧
      ∀ u : cube d (R.b α), |A ζ u - A ζ (R.primaryZero α u)| ≤
        LA * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n (I.Ξ n ω α) (A (I.Ξ n ω α)) -
        (if R.IsEssential α then
          R.chartRadialLimit β p α (I.Ξ n ω α) (A (I.Ξ n ω α)) else 0)) atTop 0 := by
  classical
  have hnorm : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < ‖I.Ξ n ω α‖} ≤ ENNReal.ofReal η := fun η hη ↦
    (I.tendsto.continuous_comp (continuous_apply α)).eventually_measure_norm_gt_le hη
  refine tendstoInMeasure_of_uniform_on (X := fun n ω ↦ I.Ξ n ω α)
    (G := fun ζ ↦ if R.IsEssential α then R.chartRadialLimit β p α ζ (A ζ) else 0)
    (F := fun (n : ℕ) ζ ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
      R.chartRadialInsertion α β p n ζ (A ζ))
    (B := fun j : ℕ ↦ {ζ : C(cube d (R.b α), ℝ) |
      ‖ζ‖ ≤ j ∧ ∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
        j * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i})
    (fun j ε hε ↦ ?_) (fun η hη ↦ ?_)
  · obtain ⟨P₀, LA, hAj⟩ := hA j
    by_cases hα : R.IsEssential α
    · obtain ⟨N, hN⟩ := R.essential_radial_insertion_uniform hα hβ hp j P₀ j LA hε
      refine ⟨N, fun n hn ζ hζ ↦ ?_⟩
      simp only [ite_eq_left hα]
      exact hN n hn ζ (A ζ) hζ.1 (hAj ζ hζ.1 hζ.2).1 hζ.2 (hAj ζ hζ.1 hζ.2).2
    · obtain ⟨N, hN⟩ := R.nonessential_radial_insertion_uniform hα hβ hp
        (le_max_left 0 P₀) j hε
      refine ⟨N, fun n hn ζ hζ ↦ ?_⟩
      simp only [ite_eq_right hα, sub_zero]
      exact hN n hn ζ (A ζ) hζ.1 ((hAj ζ hζ.1 hζ.2).1.trans (le_max_right 0 P₀))
  · obtain ⟨M, N₁, hN₁⟩ := hnorm (η / 2) (half_pos hη)
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

/-- Fixed total amplitudes require only their primary Lipschitz bound. -/
theorem fixed_radial_insertion_sub_limit_tendstoInMeasure (α : R.ι) {p : ℝ}
    (hβ : 0 < β) (hp : 0 ≤ p) (a : C(cube d (R.b α), ℝ)) {La : ℝ}
    (ha : ∀ u : cube d (R.b α), |a u - a (R.primaryZero α u)| ≤
      La * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n (I.Ξ n ω α) a -
        (if R.IsEssential α then R.chartRadialLimit β p α (I.Ξ n ω α) a else 0)) atTop 0 :=
  I.radial_insertion_sub_limit_tendstoInMeasure α hβ hp (fun _ ↦ a)
    (fun _ ↦ ⟨‖a‖, La, fun _ _ _ ↦ ⟨le_rfl, ha⟩⟩)

/-- The self mark needed for the training Gibbs limit: a fixed total
amplitude times the current empirical field. -/
theorem self_mark_radial_insertion_sub_limit_tendstoInMeasure (α : R.ι) {p : ℝ}
    (hβ : 0 < β) (hp : 0 ≤ p) (a : C(cube d (R.b α), ℝ)) {La : ℝ}
    (ha : ∀ u : cube d (R.b α), |a u - a (R.primaryZero α u)| ≤
      La * ∑ i ∈ R.primary α, (u : Fin d → ℝ) i) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n (I.Ξ n ω α) (a * I.Ξ n ω α) -
        (if R.IsEssential α then
          R.chartRadialLimit β p α (I.Ξ n ω α) (a * I.Ξ n ω α) else 0)) atTop 0 := by
  apply I.radial_insertion_sub_limit_tendstoInMeasure α hβ hp (fun ζ ↦ a * ζ)
  intro j
  refine ⟨‖a‖ * j, j * La + ‖a‖ * j, fun ζ hζ hζL ↦ ⟨?_, ?_⟩⟩
  · exact (norm_mul_le a ζ).trans (mul_le_mul_of_nonneg_left hζ (norm_nonneg a))
  · have hprod := NormalCrossing.marked_amplitude_primary_bound
      (w := fun u ↦ a u) (a := fun u ↦ ζ u) (π := fun u ↦ R.primaryZero α u)
      (s := fun u ↦ ∑ i ∈ R.primary α, (u : Fin d → ℝ) i)
      (fun u ↦ by simpa only [Real.norm_eq_abs] using a.norm_coe_le_norm u)
      (fun u ↦ (Real.norm_eq_abs _).symm.le.trans ((ζ.norm_coe_le_norm u).trans hζ))
      ha hζL (norm_nonneg a) (Nat.cast_nonneg j)
    simpa only [ContinuousMap.mul_apply] using hprod

end SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput
