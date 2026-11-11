/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.ChartLimit
public import SLT.BayesGibbs.PrimaryAmplitudeApprox
import SLT.BayesGibbs.Weighted.BlockLimit
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# Marked radial integrals with continuous marks

On an essential chart of a resolution atlas, the marked radial integral
`SingularLearningTheory.ResolutionAtlas.chartRadialInsertion` with $p \ge 0$, scaled by
$n^{\lambda + p}/(\log n)^{m-1}$, converges to its limit
`SingularLearningTheory.ResolutionAtlas.chartRadialLimit` uniformly over chart fields $\zeta$ with
$\|\zeta\| \le M$ and a fixed Lipschitz bound in the primary coordinates. This module extends that
limit from marks with a Lipschitz bound in the primary coordinates to every continuous mark $A$.
The scaled integral is linear in $A$ and at most a multiple of $\|A\|$, uniformly in $n \ge 2$,
and $A$ is approximated uniformly by a mark with a Lipschitz bound in the primary coordinates and
the same values on the face where the primary coordinates vanish.

## Main results

* `SingularLearningTheory.ResolutionAtlas.integrable_chartRadialInsertion`: the integrand is
  integrable on the chart cube for continuous fields and marks.
* `SingularLearningTheory.ResolutionAtlas.essential_radial_insertion_norm_bound`: on an essential
  chart, the scaled integral is at most $C\|A\|$ for every $n \ge 2$ and every field with
  $\|\zeta\| \le M$.
* `SingularLearningTheory.ResolutionAtlas.essential_continuous_radial_insertion_uniform`: on an
  essential chart, the scaled integral of a fixed continuous mark converges to its limit,
  uniformly over fields with $\|\zeta\| \le M$ and a fixed Lipschitz bound in the primary
  coordinates.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.ResolutionAtlas

open SingularLearningTheory.NormalCrossing

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- Continuous chart integrands are integrable for every nonnegative radial power. -/
theorem integrable_chartRadialInsertion (α : R.ι) (β n : ℝ) {p : ℝ} (hp : 0 ≤ p)
    (ζ A : C(cube d (R.b α), ℝ)) :
    IntegrableOn (fun u ↦ (∏ j, u j ^ (2 * R.k α j)) ^ p *
      Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j)) +
        Real.sqrt n * β * (∏ j, u j ^ R.k α j) * ζ (R.clamp α u)) *
      (∏ j, u j ^ (R.h α j : ℝ)) * A (R.clamp α u)) (cube d (R.b α)) := by
  have hK : Continuous (fun u : Fin d → ℝ ↦ ∏ j, u j ^ (2 * R.k α j)) :=
    continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _
  have hU : Continuous (fun u : Fin d → ℝ ↦ ∏ j, u j ^ R.k α j) :=
    continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _
  have hmon : Continuous (fun u : Fin d → ℝ ↦ ∏ j, u j ^ (R.h α j : ℝ)) :=
    continuous_finsetProd _ fun j _ ↦
      (Real.continuous_rpow_const (Nat.cast_nonneg _)).comp (continuous_apply j)
  have he : Continuous (fun u : Fin d → ℝ ↦ Real.exp
      (-(n * β * ∏ j, u j ^ (2 * R.k α j)) +
        Real.sqrt n * β * (∏ j, u j ^ R.k α j) * ζ (R.clamp α u))) :=
    Real.continuous_exp.comp (((hK.const_mul _).neg).add
      ((hU.const_mul _).mul (ζ.continuous.comp (R.continuous_clamp α))))
  exact (((((Real.continuous_rpow_const hp).comp hK).mul he).mul hmon).mul
    (A.continuous.comp (R.continuous_clamp α))).continuousOn.integrableOn_compact
      isCompact_Icc

theorem chartRadialInsertion_sub (α : R.ι) (β n : ℝ) {p : ℝ} (hp : 0 ≤ p)
    (ζ A B : C(cube d (R.b α), ℝ)) :
    R.chartRadialInsertion α β p n ζ (A - B) =
      R.chartRadialInsertion α β p n ζ A - R.chartRadialInsertion α β p n ζ B := by
  rw [chartRadialInsertion, chartRadialInsertion, chartRadialInsertion,
    ← integral_sub (R.integrable_chartRadialInsertion α β n hp ζ A)
      (R.integrable_chartRadialInsertion α β n hp ζ B)]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [ContinuousMap.sub_apply]
  ring

/-- Uniform operator bound on essential radial insertions. This is the
boundedness needed to pass from primary-Lipschitz to continuous amplitudes. -/
theorem essential_radial_insertion_norm_bound {α : R.ι} (hα : R.IsEssential α)
    {β p : ℝ} (hβ : 0 < β) (hp : 0 ≤ p) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → ∀ ζ A : C(cube d (R.b α), ℝ), ‖ζ‖ ≤ M →
      |(n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n ζ A| ≤ C * ‖A‖ := by
  obtain ⟨r, eP, eS, hr⟩ := R.exists_blockData α
  have hb := R.b_pos α
  have hk : ∀ i, 0 < R.k α (eP i) := fun i ↦ R.k_pos_of_mem_primary (eP i).2
  have hlam : ∀ i, ((R.h α (eP i) : ℝ) + 1) / (2 * R.k α (eP i)) = R.rlct := fun i ↦
    (R.ratio_eq_of_mem_primary (eP i).2).trans hα.1
  have hsec : ∀ i, 2 * R.k α (eS i) * R.rlct < (R.h α (eS i) : ℝ) + 1 := fun i ↦ by
    have := R.two_mul_k_mul_chartRlct_lt_of_notMem_primary (eS i).2
    rwa [hα.1] at this
  obtain ⟨a₁, -, a₂, ha₂, hZ⟩ := blockIntegral_bounds hk hlam R.rlct_pos hsec hb hβ hp
  refine ⟨a₂ * Real.exp (β * M ^ 2 / 2), mul_pos ha₂ (Real.exp_pos _), ?_⟩
  intro n hn ζ A hζ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : Real.log (n : ℝ) ≠ 0 := (Real.log_pos (by linarith)).ne'
  have hpow : (n : ℝ) ^ (R.rlct + p) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
  have hmult : R.mult - 1 = r := by rw [← hα.2, ← hr, Nat.add_sub_cancel]
  have hln : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hscale : 0 ≤ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) :=
    div_nonneg (Real.rpow_nonneg hn0.le _) (pow_nonneg hln _)
  have hξm := (R.measurable_clamp_comp ζ).comp (MeasurableEquiv.blockEquiv eP eS).measurable
  have hξ : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      |ζ (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))| ≤ M := fun z _ ↦
    (Real.norm_eq_abs _).symm.le.trans ((ContinuousMap.norm_coe_le_norm ζ _).trans hζ)
  have hAb : ∀ z ∈ cube (r + 1) (R.b α) ×ˢ cube (d - (r + 1)) (R.b α),
      |A (R.clamp α (MeasurableEquiv.blockEquiv eP eS z))| ≤ ‖A‖ := fun z _ ↦
    (Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm A _)
  have habs := NormalCrossing.abs_blockIntegral_le_const_amplitude (fun i ↦ R.k α (eP i))
    (fun i ↦ R.k α (eS i))
    (show ∀ i, (-1 : ℝ) < (R.h α (eP i) : ℝ) from fun i ↦ by linarith [Nat.cast_nonneg (α := ℝ) (R.h α (eP i))])
    (show ∀ i, (-1 : ℝ) < (R.h α (eS i) : ℝ) from fun i ↦ by linarith [Nat.cast_nonneg (α := ℝ) (R.h α (eS i))])
    hb hβ.le hp hn0.le (norm_nonneg A) hξm hξ hAb
  have hZn := (hZ _ (fun _ ↦ ‖A‖) M 0 ‖A‖ hξm measurable_const le_rfl hξ
    (fun _ _ ↦ norm_nonneg A) (fun _ _ ↦ le_rfl) n hn2).2
  rw [R.chartRadialInsertion_eq_blockIntegral eP eS, abs_mul, abs_of_nonneg hscale]
  calc
    _ ≤ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        (a₂ * Real.log n ^ r / n ^ (R.rlct + p) * Real.exp (β * M ^ 2 / 2) * ‖A‖) :=
      mul_le_mul_of_nonneg_left (habs.trans hZn) hscale
    _ = _ := by rw [hmult]; field_simp [hpow, pow_ne_zero r hlog]

/-- Fixed continuous amplitudes have the uniform essential-chart
limit. No Lipschitz regularity of the covariance mark is required. -/
theorem essential_continuous_radial_insertion_uniform {α : R.ι} (hα : R.IsEssential α)
    {β p : ℝ} (hβ : 0 < β) (hp : 0 ≤ p) (A : C(cube d (R.b α), ℝ))
    (M Lξ : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ ζ : C(cube d (R.b α), ℝ), ‖ζ‖ ≤ M →
      (∀ u : cube d (R.b α), |ζ u - ζ (R.primaryZero α u)| ≤
        Lξ * ∑ j ∈ R.primary α, (u : Fin d → ℝ) j) →
      |(n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        R.chartRadialInsertion α β p n ζ A - R.chartRadialLimit β p α ζ A| ≤ ε := by
  obtain ⟨C, hC, hbound⟩ := R.essential_radial_insertion_norm_bound hα hβ hp M
  obtain ⟨B, LB, hBA, htrace, hBL⟩ := R.exists_chart_amplitude_approx α A
    (div_pos hε (mul_pos two_pos hC))
  obtain ⟨N, hN⟩ := R.essential_radial_insertion_uniform hα hβ hp M ‖B‖ Lξ LB (half_pos hε)
  refine ⟨max N 2, fun n hn ζ hζ hζL ↦ ?_⟩
  have hlim : R.chartRadialLimit β p α ζ B = R.chartRadialLimit β p α ζ A := by
    unfold chartRadialLimit
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun v hv ↦ ?_
    rw [htrace ⟨v, hv⟩]
  have hfirst : |(n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
      R.chartRadialInsertion α β p n ζ A -
      (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
      R.chartRadialInsertion α β p n ζ B| ≤ ε / 2 := by
    rw [← mul_sub, ← R.chartRadialInsertion_sub α β n hp ζ A B]
    calc
      _ ≤ C * ‖A - B‖ := hbound n (le_of_max_le_right hn) ζ (A - B) hζ
      _ ≤ C * (ε / (2 * C)) := by
        rw [norm_sub_rev]
        exact mul_le_mul_of_nonneg_left hBA hC.le
      _ = ε / 2 := by field_simp
  have hsecond := hN n (le_of_max_le_left hn) ζ B hζ le_rfl hζL hBL
  rw [hlim] at hsecond
  exact (abs_sub_le _ _ _).trans ((add_le_add hfirst hsecond).trans (by linarith))

end SingularLearningTheory.ResolutionAtlas
