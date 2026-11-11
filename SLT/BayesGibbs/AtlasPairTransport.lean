/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.HalfRadial.Measure
public import SLT.BayesGibbs.Pair.PosteriorLocalization

/-!
# Transport of pair integrals to the resolution charts

The product of the localized prior $\chi\varphi\,dw$ with itself is the sum, over pairs of charts
of a resolution atlas, of the products of the chart prior measures pushed forward along the chart
maps. Weighting both coordinates by the tempered posterior density $e^{-n\beta K_n}$ and using
the chart identity of the empirical process, a localized pair integral of a test function that
factors as $u^{k_\alpha} v^{k_\gamma} C(u, v)$ on each pair of charts becomes, after scaling by
the square of `SingularLearningTheory.ResolutionAtlas.halfRadialScale`, the integral of $C$ against
the product of the half-radial measure with itself. This puts the two-replica term of the
posterior observables of [Wat09, Theorem 6.8] in chart coordinates, where its convergence in law
is proved.

## Main definitions

* `SingularLearningTheory.ResolutionAtlas.chartPriorDensity` and
  `SingularLearningTheory.ResolutionAtlas.chartPriorMeasure`: the prior on chart $\alpha$, with density
  $u^{h_\alpha}\tilde\varphi_\alpha(u)$ on the cube $[0, b_\alpha]^d$.

## Main results

* `SingularLearningTheory.BayesGibbs.integral_prod_finset_sum_map`: an integral against the product of
  two finite sums of pushforward measures is the double sum of the integrals over pairs.
* `MeasureTheory.integral_prod_withDensity_ofReal`: an integral against a product
  of measures with densities is the integral of the product of the densities with the integrand.
* `SingularLearningTheory.ResolutionAtlas.integral_pair_localized_eq_sum`: the integral against the
  square of the localized prior is the sum of chart-pair integrals.
* `SingularLearningTheory.ResolutionAtlas.integral_halfRadialMeasure_prod`: the integral against the
  square of the half-radial measure as a sum of chart-pair integrals.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.ae_localized_pair_eq_halfRadial`:
  almost surely, the scaled localized pair integral under the tempered posterior weight equals the
  integral against the square of the half-radial measure.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.BayesGibbs

/-- Tensorizing a finite sum of pushforward measures. Only integrability on
individual chart pairs is needed. -/
private theorem integral_prod_finset_sum_map
    {A U ι : Type*} [MeasurableSpace A] [MeasurableSpace U] [Fintype ι]
    (μ : ι → Measure A) [∀ i, IsFiniteMeasure (μ i)]
    (g : ι → A → U) (hg : ∀ i, Measurable (g i))
    {F : U × U → ℝ} (hF : Measurable F)
    (hI : ∀ i j, Integrable (fun z ↦ F (g i z.1, g j z.2)) ((μ i).prod (μ j))) :
    (∫ z, F z ∂((∑ i, (μ i).map (g i)).prod (∑ j, (μ j).map (g j)))) =
      ∑ i, ∑ j, ∫ z, F (g i z.1, g j z.2) ∂((μ i).prod (μ j)) := by
  have hIm : ∀ i j, Integrable F (((μ i).map (g i)).prod ((μ j).map (g j))) := by
    intro i j
    rw [Measure.map_prod_map _ _ (hg i) (hg j),
      integrable_map_measure hF.aestronglyMeasurable ((hg i).prodMap (hg j)).aemeasurable]
    exact hI i j
  have hp : ((∑ i, (μ i).map (g i)).prod (∑ j, (μ j).map (g j))) =
      ∑ i, ∑ j, (((μ i).map (g i)).prod ((μ j).map (g j))) := by
    simp only [← Measure.sum_fintype, Measure.prod_sum_left, Measure.prod_sum_right]
    exact Measure.sum_comm _
  rw [hp, integral_finsetSum_measure
    (fun i _ ↦ integrable_finsetSum_measure.mpr (fun j _ ↦ hIm i j))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum_measure (fun j _ ↦ hIm i j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [Measure.map_prod_map _ _ (hg i) (hg j),
    integral_map ((hg i).prodMap (hg j)).aemeasurable hF.aestronglyMeasurable]
  rfl

/-- Integration against a product of densities, for signed test functions. No integrability of
the test function is required for this identity of Bochner integrals. -/
theorem _root_.MeasureTheory.integral_prod_withDensity_ofReal
    {A : Type*} [MeasurableSpace A] (μ ν : Measure A) [SFinite μ] [SFinite ν]
    {a b : A → ℝ} (ha : AEMeasurable a μ) (hb : AEMeasurable b ν)
    (ha0 : ∀ᵐ u ∂μ, 0 ≤ a u) (hb0 : ∀ᵐ v ∂ν, 0 ≤ b v) (F : A × A → ℝ) :
    (∫ z, F z ∂((μ.withDensity (fun u ↦ ENNReal.ofReal (a u))).prod
      (ν.withDensity (fun v ↦ ENNReal.ofReal (b v))))) =
      ∫ z, a z.1 * b z.2 * F z ∂μ.prod ν := by
  rw [prod_withDensity₀ ha.ennreal_ofReal hb.ennreal_ofReal]
  have hprod : AEMeasurable (fun z : A × A ↦
      ENNReal.ofReal (a z.1) * ENNReal.ofReal (b z.2)) (μ.prod ν) :=
    ha.ennreal_ofReal.comp_fst.mul hb.ennreal_ofReal.comp_snd
  rw [integral_withDensity_eq_integral_toReal_smul₀
      hprod
      (.of_forall fun _ ↦ ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha0,
    Measure.quasiMeasurePreserving_snd.ae hb0] with z hz₁ hz₂
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hz₁, ENNReal.toReal_ofReal hz₂,
    smul_eq_mul]

end SingularLearningTheory.BayesGibbs

namespace SingularLearningTheory.ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
/-- The metric on `SingularLearningTheory.ResolutionAtlas.FaceDomain` given by
`Metric.Sigma.metricSpace`: each chart cube keeps its own metric, and points of different cubes
are at distance at least $1$. Mathlib does not make this metric on a sigma type an instance, so
it is a local instance here. -/
noncomputable local instance atlasPairTransportMetric1 : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace

/-- The density $u^{h_\alpha}\tilde\varphi_\alpha(u)$ of the prior on chart $\alpha$: the monomial
with the exponents `SingularLearningTheory.ResolutionAtlas.h` times the chart weight
`SingularLearningTheory.ResolutionAtlas.weight`. -/
@[expose] noncomputable def chartPriorDensity (α : R.ι) (u : Fin d → ℝ) : ℝ :=
  (∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u

/-- The prior on chart $\alpha$: the measure with density
`SingularLearningTheory.ResolutionAtlas.chartPriorDensity` on the cube $[0, b_\alpha]^d$. By
`SingularLearningTheory.ResolutionAtlas.transport`, the localized prior $\chi\varphi\,dw$ is the
sum over the charts of its pushforwards along the chart maps. -/
@[expose] noncomputable def chartPriorMeasure (α : R.ι) : Measure (Fin d → ℝ) :=
  (volume.restrict (cube d (R.b α))).withDensity
    (fun u ↦ ENNReal.ofReal (R.chartPriorDensity α u))

theorem integrable_chartPriorDensity (α : R.ι) :
    IntegrableOn (R.chartPriorDensity α) (cube d (R.b α)) := by
  have hc : ContinuousOn (R.chartPriorDensity α) (cube d (R.b α)) :=
    (continuousOn_finsetProd _ fun j _ ↦
      ((Real.continuous_rpow_const (Nat.cast_nonneg _)).comp (continuous_apply j)).continuousOn).mul
        (R.weight_continuousOn α)
  exact hc.integrableOn_compact isCompact_Icc

theorem ae_chartPriorDensity_nonneg (α : R.ι) :
    ∀ᵐ u ∂volume.restrict (cube d (R.b α)), 0 ≤ R.chartPriorDensity α u := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  exact mul_nonneg
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
    (R.weight_nonneg α u hu)

@[expose] instance chartPriorMeasure_finite (α : R.ι) : IsFiniteMeasure
    (R.chartPriorMeasure α) := by
  apply isFiniteMeasure_withDensity
  exact (lintegral_ofReal_ne_top_iff_integrable
    (R.integrable_chartPriorDensity α).aestronglyMeasurable
    (R.ae_chartPriorDensity_nonneg α)).mpr (R.integrable_chartPriorDensity α)

theorem ae_mem_cube_chartPriorMeasure (α : R.ι) :
    ∀ᵐ u ∂R.chartPriorMeasure α, u ∈ cube d (R.b α) :=
  (withDensity_absolutelyContinuous _ _).ae_le
    (ae_restrict_mem measurableSet_Icc)

/-- Exact product-prior transport. This is the tensor square of `R.transport`,
with no assertion that charts cover individual feasible parameter points. -/
theorem integral_pair_localized_eq_sum
    {F : (Fin d → ℝ) × (Fin d → ℝ) → ℝ} (hF : Measurable F)
    (hb : ∀ α β, ∃ C : ℝ, ∀ u ∈ cube d (R.b α), ∀ v ∈ cube d (R.b β),
      |F (R.g α u, R.g β v)| ≤ C) :
    (∫ z, F z ∂(((volume.restrict W).withDensity
      (fun w ↦ ENNReal.ofReal (R.χ w * φ w))).prod
      ((volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (R.χ w * φ w))))) =
      ∑ α, ∑ β, ∫ z,
        R.chartPriorDensity α z.1 * R.chartPriorDensity β z.2 *
          F (R.g α z.1, R.g β z.2)
        ∂(volume.restrict (cube d (R.b α))).prod
          (volume.restrict (cube d (R.b β))) := by
  have hI : ∀ α β, Integrable (fun z ↦ F (R.g α z.1, R.g β z.2))
      ((R.chartPriorMeasure α).prod (R.chartPriorMeasure β)) := by
    intro α β
    obtain ⟨C, hC⟩ := hb α β
    refine (integrable_const C).mono'
      (hF.comp ((R.g_measurable α).prodMap (R.g_measurable β))).aestronglyMeasurable ?_
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (R.ae_mem_cube_chartPriorMeasure α),
      Measure.quasiMeasurePreserving_snd.ae (R.ae_mem_cube_chartPriorMeasure β)] with z hz₁ hz₂
    simpa only [Real.norm_eq_abs] using hC z.1 hz₁ z.2 hz₂
  rw [R.transport]
  change (∫ z, F z ∂((∑ α, (R.chartPriorMeasure α).map (R.g α)).prod
    (∑ α, (R.chartPriorMeasure α).map (R.g α)))) = _
  rw [BayesGibbs.integral_prod_finset_sum_map _ _ R.g_measurable hF hI]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro β _
  exact integral_prod_withDensity_ofReal _ _
    (R.integrable_chartPriorDensity α).aemeasurable
    (R.integrable_chartPriorDensity β).aemeasurable
    (R.ae_chartPriorDensity_nonneg α) (R.ae_chartPriorDensity_nonneg β) _

/-- Product integral on the half-radial source measures, before replacing the
source densities by their formulas. -/
theorem integral_halfRadialMeasure_prod (β : ℝ) (n : ℕ) (ζ : R.ChartFunctions)
    (C : C(R.FaceDomain × R.FaceDomain, ℝ)) :
    (∫ z, C z ∂((R.halfRadialMeasure β n ζ).prod (R.halfRadialMeasure β n ζ))) =
      ∑ α, ∑ γ, ∫ z,
        R.halfRadialSourceDensity α β n (ζ α) z.1 *
        R.halfRadialSourceDensity γ β n (ζ γ) z.2 *
        C (R.fullChartEmbedding α z.1, R.fullChartEmbedding γ z.2)
        ∂(volume.restrict (cube d (R.b α))).prod
          (volume.restrict (cube d (R.b γ))) := by
  have hI : ∀ α γ, Integrable
      (fun z ↦ C (R.fullChartEmbedding α z.1, R.fullChartEmbedding γ z.2))
      ((R.halfRadialSourceMeasure α β n (ζ α)).prod
        (R.halfRadialSourceMeasure γ β n (ζ γ))) := by
    intro α γ
    exact (integrable_const ‖C‖).mono'
      (C.continuous.comp ((R.continuous_fullChartEmbedding α).prodMap
        (R.continuous_fullChartEmbedding γ))).aestronglyMeasurable
      (.of_forall fun z ↦ C.norm_coe_le_norm _)
  unfold halfRadialMeasure halfRadialComponent
  rw [BayesGibbs.integral_prod_finset_sum_map _ _
    (fun α ↦ (R.continuous_fullChartEmbedding α).measurable) C.continuous.measurable hI]
  apply Finset.sum_congr rfl
  intro α _
  apply Finset.sum_congr rfl
  intro γ _
  apply integral_prod_withDensity_ofReal _ _
    (R.integrable_halfRadialSourceDensity α β n (ζ α)).aemeasurable
    (R.integrable_halfRadialSourceDensity γ β n (ζ γ)).aemeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact R.halfRadialSourceDensity_nonneg α β n (ζ α) hu
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact R.halfRadialSourceDensity_nonneg γ β n (ζ γ) hu

namespace EmpiricalProcessInput
variable {R} {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

/-- Exact same-sample tensor transport of the global population kernel.
The probability-one chart identity is quantified over all charts before it is
used; no uncountable diagonal intersection is taken. -/
theorem ae_localized_pair_eq_halfRadial
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ}
    (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w ∈ W, ∀ v ∈ W, |B (w, v)| ≤ M)
    (C : C(R.FaceDomain × R.FaceDomain, ℝ))
    (hfactor : ∀ α γ (u : cube d (R.b α)) (v : cube d (R.b γ)),
      B (R.g α u, R.g γ v) =
        ((∏ j, (u : Fin d → ℝ) j ^ R.k α j) *
          (∏ j, (v : Fin d → ℝ) j ^ R.k γ j)) * C (⟨α, u⟩, ⟨γ, v⟩))
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P,
      R.halfRadialScale n ^ 2 *
        (∫ z, B z * (R.χ z.1 * (Real.exp (-(n * β * I.Kn n ω z.1)) * φ z.1)) *
          (R.χ z.2 * (Real.exp (-(n * β * I.Kn n ω z.2)) * φ z.2))
          ∂(volume.restrict W).prod (volume.restrict W)) =
        ∫ z, C z ∂((R.halfRadialMeasure β n (I.Ξ n ω)).prod
          (R.halfRadialMeasure β n (I.Ξ n ω))) := by
  have hci := ae_all_iff.mpr fun α ↦ I.chart_identity n hn α
  filter_upwards [hci] with ω hω
  let e : (Fin d → ℝ) → ℝ := fun w ↦ Real.exp (-(n * β * I.Kn n ω w))
  have hem : Measurable e :=
    (((I.Kn_measurable n).of_uncurry_left.const_mul _).neg.exp)
  let F : (Fin d → ℝ) × (Fin d → ℝ) → ℝ := fun z ↦ B z * e z.1 * e z.2
  have hFm : Measurable F := (hB.mul (hem.comp measurable_fst)).mul (hem.comp measurable_snd)
  have hFb : ∀ α γ, ∃ D : ℝ, ∀ u ∈ cube d (R.b α), ∀ v ∈ cube d (R.b γ),
      |F (R.g α u, R.g γ v)| ≤ D := by
    intro α γ
    refine ⟨M * Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2) *
      Real.exp (β * ‖I.Ξ n ω γ‖ ^ 2 / 2), fun u hu v hv ↦ ?_⟩
    dsimp [F, e]
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _),
      I.exp_Kn_comp_g n ω α (hω α) hu, I.exp_Kn_comp_g n ω γ (hω γ) hv]
    gcongr
    · exact hb _ (R.g_mapsTo α hu) _ (R.g_mapsTo γ hv)
    · exact Real.exp_le_exp.mp (I.exp_chart_le n ω α hβ.le u)
    · exact Real.exp_le_exp.mp (I.exp_chart_le n ω γ hβ.le v)
  have hχφ : AEMeasurable (fun w ↦ R.χ w * φ w) (volume.restrict W) :=
    R.χ_measurable.aemeasurable.mul hφi.aemeasurable
  have hχφ0 : ∀ᵐ w ∂volume.restrict W, 0 ≤ R.χ w * φ w := by
    filter_upwards [ae_restrict_mem hW] with w hw
    exact mul_nonneg (R.χ_nonneg w) (hφ w hw)
  have ht := R.integral_pair_localized_eq_sum hFm hFb
  rw [integral_prod_withDensity_ofReal _ _ hχφ hχφ hχφ0 hχφ0 F] at ht
  have hleft : (∫ z, B z * (R.χ z.1 * (e z.1 * φ z.1)) *
      (R.χ z.2 * (e z.2 * φ z.2)) ∂(volume.restrict W).prod (volume.restrict W)) =
      ∑ α, ∑ γ, ∫ z, R.chartPriorDensity α z.1 * R.chartPriorDensity γ z.2 *
        F (R.g α z.1, R.g γ z.2)
        ∂(volume.restrict (cube d (R.b α))).prod
          (volume.restrict (cube d (R.b γ))) := by
    convert ht using 1
    apply integral_congr_ae
    exact .of_forall fun z ↦ by dsimp [F]; ring
  rw [R.integral_halfRadialMeasure_prod, hleft, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ _
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae
      (ae_restrict_mem measurableSet_Icc),
    Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem measurableSet_Icc)] with z hu hv
  have hhalf (a : R.ι) (u : Fin d → ℝ) (hu : u ∈ cube d (R.b a)) :
      (∏ j, u j ^ (2 * R.k a j)) ^ (1 / 2 : ℝ) = ∏ j, u j ^ R.k a j := by
    rw [← Real.sqrt_eq_rpow, Finset.prod_pow_two_mul, Real.sqrt_sq]
    exact Finset.prod_nonneg fun j _ ↦ pow_nonneg (hu.1 j) _
  dsimp [F, e]
  rw [hfactor α γ ⟨z.1, hu⟩ ⟨z.2, hv⟩,
    I.exp_Kn_comp_g n ω α (hω α) hu, I.exp_Kn_comp_g n ω γ (hω γ) hv]
  simp only [halfRadialSourceDensity, chartPriorDensity, markedChartWeight_apply,
    ContinuousMap.one_apply, mul_one, fullChartEmbedding, R.clamp_of_mem hu,
    R.clamp_of_mem hv, hhalf α z.1 hu, hhalf γ z.2 hv]
  ring

end EmpiricalProcessInput
end SingularLearningTheory.ResolutionAtlas
