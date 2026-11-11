/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Weighted.ContinuousChartProbability
public import SLT.BayesGibbs.CompactPosterior.RatioProbability
public import SLT.BayesGibbs.Weighted.ChartLimit
import SLT.SingularIntegrals.DeterministicFreeEnergy

/-!
# Weighted partition functions and their limits

For an empirical process input on a resolution atlas, the weighted partition function of a
function $a$ is $\int_W a(w)e^{-n\beta K_n(w)}\varphi(w)\,dw$, the numerator of the posterior
expectation of $a$. Splitting the prior with the localization $\chi$, it is the sum over the
charts of the marked radial integrals of the chart processes, plus a tail with weight
$(1 - \chi)\varphi$. Let $a$ be bounded and measurable, with
$a(g_\alpha(u)) = (u^{2k_\alpha})^p A_\alpha(u)$ on every chart and $A_\alpha$ continuous. Then
the partition function scaled by $n^{\lambda + p}/(\log n)^{m-1}$ approaches in probability the
sum over the essential charts of the marked radial limits, with mark $A_\alpha$ times the chart
weight. This applies to $a = K$
and to $a = E_q[f(x, \cdot)^2]$.

## Main definitions

* `SingularLearningTheory.ResolutionAtlas.chartWeightCM`: the chart weight as a continuous function on
  the chart cube.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.weightedPartition` and
  `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.weightedTail`: the weighted partition
  function and its tail off the localization.

## Main results

* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.bounded_mark_tail_tendsto`: for a
  bounded $a$, the tail times any power of $n$ over a power of $\log n$ tends to zero in
  probability.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.ae_weightedPartition_eq_radial`: the
  decomposition into the marked radial integrals of the chart processes and the tail.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.weightedPartition_sub_limit_tendstoInMeasure`:
  the limit in probability.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- The chart weight `SingularLearningTheory.ResolutionAtlas.weight` of chart $\alpha$ as a
continuous function on the chart cube $[0, b_\alpha]^d$. It multiplies the mark in the chart
radial integrals of
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.ae_weightedPartition_eq_radial`. -/
@[expose] noncomputable def chartWeightCM (α : R.ι) : C(cube d (R.b α), ℝ) :=
  ⟨fun u ↦ R.weight α u, continuousOn_iff_continuous_domRestrict.mp (R.weight_continuousOn α)⟩

@[simp] theorem chartWeightCM_apply (α : R.ι) (u : cube d (R.b α)) :
    R.chartWeightCM α u = R.weight α u := rfl

namespace EmpiricalProcessInput

variable {R} {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

/-- The weighted partition function $\int_W a(w)e^{-n\beta K_n(w)}\varphi(w)\,dw$ of a function
$a$ at sample size $n$ and outcome $\omega$, with $K_n$ the empirical loss
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.Kn`. It is the numerator of the
expectation of $a$ under the tempered posterior
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.temperedPosterior`. -/
@[expose] noncomputable def weightedPartition (a : (Fin d → ℝ) → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w in W, a w * Real.exp (-(n * β * I.Kn n ω w)) * φ w

/-- The tail $\int_W a(w)e^{-n\beta K_n(w)}(1 - \chi(w))\varphi(w)\,dw$ of
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.weightedPartition` off the
localization $\chi$ (`SingularLearningTheory.ResolutionAtlas.χ`). For bounded measurable $a$ it
tends to zero in probability even after multiplication by $n^\lambda/(\log n)^{m-1}$, for any
$\lambda$ and $m$
(`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.bounded_mark_tail_tendsto`). -/
@[expose] noncomputable def weightedTail (a : (Fin d → ℝ) → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ w in W, a w * Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)

theorem ae_weightedTail_integrable_and_bound
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : (Fin d → ℝ) → ℝ} (ham : Measurable a)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ w ∈ W, |a w| ≤ M) (n : ℕ) :
    ∀ᵐ ω ∂P,
      IntegrableOn (fun w ↦ a w * Real.exp (-(n * β * I.Kn n ω w)) *
        ((1 - R.χ w) * φ w)) W ∧ |I.weightedTail a n ω| ≤ M * I.tail n ω := by
  filter_upwards [I.tail_bound n] with ω hτ
  let e : (Fin d → ℝ) → ℝ := fun w ↦
    Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w)
  have hem : AEStronglyMeasurable e (volume.restrict W) :=
    ((I.Kn_measurable n).of_uncurry_left.const_mul _).neg.exp.aestronglyMeasurable.mul
      ((measurable_const.sub R.χ_measurable).aestronglyMeasurable.mul hφi.aestronglyMeasurable)
  have he0 : ∀ᵐ w ∂(volume.restrict W), 0 ≤ e w := by
    filter_upwards [ae_restrict_mem hW] with w hw
    exact mul_nonneg (Real.exp_pos _).le
      (mul_nonneg (sub_nonneg.mpr (R.χ_le_one w)) (hφ w hw))
  have hei : Integrable e (volume.restrict W) :=
    Integrable.mono' (hφi.const_mul (Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2))) hem (by
      filter_upwards [ae_restrict_mem hW, he0] with w hw hew
      rw [Real.norm_eq_abs, abs_of_nonneg hew]
      exact I.exp_mul_tail_weight_le hτ hβ.le hw (hφ w hw))
  have hpt : ∀ᵐ w ∂(volume.restrict W), ‖a w * e w‖ ≤ M * e w := by
    filter_upwards [ae_restrict_mem hW, he0] with w hw hew
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hew]
    exact mul_le_mul_of_nonneg_right (ha w hw) hew
  have hai : Integrable (fun w ↦ a w * e w) (volume.restrict W) :=
    (hei.const_mul M).mono' (ham.aestronglyMeasurable.mul hem) hpt
  refine ⟨hai.congr (Eventually.of_forall fun w ↦ by dsimp [e]; ring), ?_⟩
  have hb := norm_integral_le_of_norm_le (hei.const_mul M) hpt
  rw [integral_const_mul, Real.norm_eq_abs] at hb
  simpa only [weightedTail, tail, e, mul_assoc] using hb

theorem bounded_mark_tail_tendsto
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : (Fin d → ℝ) → ℝ} (ham : Measurable a)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ w ∈ W, |a w| ≤ M) (lam : ℝ) (m : ℕ) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ (n : ℝ) ^ lam / Real.log n ^ (m - 1) *
      I.weightedTail a n ω) atTop 0 := by
  have hsmall := tendstoInMeasure_const_mul_zero M (I.tail_tendsto hW hφ hφi hβ lam m)
  apply tendstoInMeasure_zero_of_abs_le (Z := fun n ω ↦ M *
    ((n : ℝ) ^ lam / Real.log n ^ (m - 1) * I.tail n ω)) (fun n ↦ ?_) hsmall
  filter_upwards [I.ae_weightedTail_integrable_and_bound hW hφ hφi hβ ham hM ha n] with ω hω
  have hs : 0 ≤ (n : ℝ) ^ lam / Real.log n ^ (m - 1) :=
    div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      (pow_nonneg (Real.log_natCast_nonneg n) _)
  rw [abs_mul, abs_of_nonneg hs]
  calc _ ≤ (n : ℝ) ^ lam / Real.log n ^ (m - 1) * (M * I.tail n ω) :=
      mul_le_mul_of_nonneg_left hω.2 hs
    _ = _ := by ring

/-- Exact transport of a bounded mark that factors as K^p times a continuous
chart mark. Applied to a=K and to a=∫f²dq, this gives the T and D
numerators, including their original parameter-space tail. -/
theorem ae_weightedPartition_eq_radial
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : (Fin d → ℝ) → ℝ} (ham : Measurable a)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ w ∈ W, |a w| ≤ M)
    (p : ℝ) (A : R.ChartFunctions)
    (hfactor : ∀ α (u : cube d (R.b α)), a (R.g α u) =
      (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ p * A α u)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, I.weightedPartition a n ω =
      (∑ α, R.chartRadialInsertion α β p n (I.Ξ n ω α) (R.chartWeightCM α * A α)) +
        I.weightedTail a n ω := by
  have hci : ∀ᵐ ω ∂P, ∀ α, ∀ u : cube d (R.b α),
      I.Kn n ω (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * I.Ξ n ω α u :=
    ae_all_iff.mpr fun α ↦ I.chart_identity n hn α
  filter_upwards [hci, I.ae_weightedTail_integrable_and_bound hW hφ hφi hβ ham hM ha n]
    with ω hω htail
  have hFm : Measurable fun w ↦ a w * Real.exp (-(n * β * I.Kn n ω w)) :=
    ham.mul (((I.Kn_measurable n).of_uncurry_left.const_mul _).neg.exp)
  have hFb : ∀ α, ∃ C, ∀ u ∈ cube d (R.b α),
      |a (R.g α u) * Real.exp (-(n * β * I.Kn n ω (R.g α u)))| ≤ C := by
    intro α
    refine ⟨M * Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2), fun u hu ↦ ?_⟩
    rw [abs_mul, abs_of_pos (Real.exp_pos _), I.exp_Kn_comp_g n ω α (hω α) hu]
    exact mul_le_mul (ha _ (R.g_mapsTo α hu)) (I.exp_chart_le n ω α hβ.le u)
      (Real.exp_pos _).le hM
  obtain ⟨hint, heq⟩ := R.integral_localized_eq_sum_of_bounded hW hφ hφi hFm hFb
  have hsplit : ∀ w, a w * Real.exp (-(n * β * I.Kn n ω w)) * φ w =
      (a w * Real.exp (-(n * β * I.Kn n ω w))) * (R.χ w * φ w) +
      a w * Real.exp (-(n * β * I.Kn n ω w)) * ((1 - R.χ w) * φ w) := fun w ↦ by ring
  simp only [weightedPartition, weightedTail]
  simp_rw [hsplit]
  rw [integral_add hint htail.1, heq]
  congr 1
  refine Finset.sum_congr rfl fun α _ ↦ ?_
  rw [chartRadialInsertion]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu ↦ ?_
  rw [hfactor α ⟨u, hu⟩, I.exp_Kn_comp_g n ω α (hω α) hu, R.clamp_of_mem hu]
  simp only [ContinuousMap.mul_apply, chartWeightCM_apply]
  ring

/-- Marked global numerator limit. Its premises are ordinary measurability,
boundedness and chart factorization, all discharged for K and ∫f²dq. -/
theorem weightedPartition_sub_limit_tendstoInMeasure
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {a : (Fin d → ℝ) → ℝ} (ham : Measurable a)
    {M : ℝ} (hM : 0 ≤ M) (ha : ∀ w ∈ W, |a w| ≤ M)
    {p : ℝ} (hp : 0 ≤ p) (A : R.ChartFunctions)
    (hfactor : ∀ α (u : cube d (R.b α)), a (R.g α u) =
      (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) ^ p * A α u) :
    TendstoInMeasure P
      (fun (n : ℕ) ω ↦ (n : ℝ) ^ (R.rlct + p) / Real.log n ^ (R.mult - 1) *
        I.weightedPartition a n ω -
        ∑ α, if R.IsEssential α then
          R.chartRadialLimit β p α (I.Ξ n ω α) (R.chartWeightCM α * A α) else 0)
      atTop 0 := by
  have hlocal := I.continuous_radial_sum_sub_limit_tendstoInMeasure hβ hp
    (fun α ↦ R.chartWeightCM α * A α)
  have htail := I.bounded_mark_tail_tendsto hW hφ hφi hβ ham hM ha (R.rlct + p) R.mult
  refine (tendstoInMeasure_add_zero hlocal htail).congr' ?_ (EventuallyEq.rfl)
  filter_upwards [eventually_ge_atTop 1] with n hn
  filter_upwards [I.ae_weightedPartition_eq_radial hW hφ hφi hβ ham hM ha p A hfactor hn] with ω hω
  rw [hω]
  ring

end EmpiricalProcessInput
end SingularLearningTheory.ResolutionAtlas
