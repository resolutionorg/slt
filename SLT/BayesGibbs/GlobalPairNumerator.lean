/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.AtlasPairTransport
public import SLT.BayesGibbs.Pair.RadialConvergence
public import SLT.BayesGibbs.PopulationDiagonalLimit
public import SLT.BayesGibbs.HalfRadial.CompactQ
public import SLT.BayesGibbs.EssentialFace.Product
public import SLT.BayesGibbs.TightProducts
import SLT.BayesGibbs.Pair.PosteriorLocalization
import SLT.BayesGibbs.CompactPosterior.RatioProbability
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# The pair numerator of the functional variance

The functional variance involves the pair numerator, the integral of $B(w, w')$ against
$e^{-n\beta K_n(w)}\varphi(w)\,e^{-n\beta K_n(w')}\varphi(w')$ over $W \times W$. For a bounded
$B$ that factors through the charts, this module shows that the pair numerator, scaled by the
square of $n^{\lambda + 1/2}/(\log n)^{m-1}$, approaches the integral of a continuous kernel
against the product of the half-radial limit measures at the chart processes. The part of the
pair numerator outside the localization is negligible at this scale. For the population product
$E_q[f(x, w) f(x, w')]$ under relatively finite variance, the limit is the compact numerator
`SingularLearningTheory.GaussianPosterior.compactQnum` of the covariance kernel of the limiting
empirical process. This is the $Q$ coordinate of the five raw posterior integrals.

## Main definitions

* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.pairWeightedPartition`: the pair
  numerator over $W \times W$.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.pairLocalizedPartition`: the pair
  numerator with both factors localized.
* `SingularLearningTheory.BayesGibbs.populationProduct`: the population product
  $E_q[f(x, w) f(x, w')]$.

## Main results

* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.pair_localization_remainder_tendstoInMeasure`:
  the scaled difference of the pair numerator and its localized form tends to zero in
  probability.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.pairWeightedPartition_sub_limit_tendstoInMeasure`:
  the scaled pair numerator minus its half-radial limit tends to zero in probability.
* `SingularLearningTheory.BayesGibbs.populationProduct_bounded_of_squares`: a bound on the population
  second moment bounds the population product.
* `EmpiricalProcessInput.normalized_populationProduct_sub_compactQnum`: under relatively
  finite variance, the scaled pair numerator of the population product minus
  `SingularLearningTheory.GaussianPosterior.compactQnum` tends to zero in probability.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory

/-- Eventual-a.e. form of the existing domination lemma. -/
theorem _root_.MeasureTheory.tendstoInMeasure_zero_of_eventually_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y Z : ℕ → Ω → ℝ}
    (hle : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P, |Y n ω| ≤ Z n ω)
    (hZ : TendstoInMeasure P Z atTop 0) : TendstoInMeasure P Y atTop 0 := by
  rw [tendstoInMeasure_iff_norm] at hZ ⊢
  intro ε hε
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hZ ε hε)
    (.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [hle] with n hn
  apply measure_mono_ae
  filter_upwards [hn] with ω hω hε'
  simp only [Pi.zero_apply, sub_zero, Real.norm_eq_abs] at hε' ⊢
  exact hε'.trans (hω.trans (le_abs_self _))

namespace ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
/-- The metric `Metric.Sigma.metricSpace` on the disjoint union
`SingularLearningTheory.ResolutionAtlas.FaceDomain` of the chart cubes, local to this module. Its
topology is the disjoint-union topology. -/
noncomputable local instance globalPairNumeratorMetric1 : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace

theorem halfRadialScale_sq {n : ℕ} (hn : 1 ≤ n) :
    R.halfRadialScale n ^ 2 =
      ((n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1)) *
      ((n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1)) := by
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hp : (n : ℝ) ^ (R.rlct + 1 / 2) * (n : ℝ) ^ (R.rlct + 1 / 2) =
      (n : ℝ) ^ R.rlct * (n : ℝ) ^ (R.rlct + 1) := by
    rw [← Real.rpow_add hn0, ← Real.rpow_add hn0]
    congr 1
    ring
  dsimp [halfRadialScale]
  calc _ = ((n : ℝ) ^ (R.rlct + 1 / 2) * (n : ℝ) ^ (R.rlct + 1 / 2)) /
      (Real.log n ^ (R.mult - 1) * Real.log n ^ (R.mult - 1)) := by ring
    _ = _ := by rw [hp]; ring

/-- A continuous kernel supported on the essential faces only depends on its
values on pairs of face embeddings. -/
theorem integral_essentialFaceMeasure_prod_congr_faces
    (F G : C(R.FaceDomain × R.FaceDomain, ℝ))
    (h : ∀ α β v w,
      F (R.faceEmbedding α v, R.faceEmbedding β w) =
      G (R.faceEmbedding α v, R.faceEmbedding β w)) :
    (∫ z, F z ∂R.essentialFaceMeasure.prod R.essentialFaceMeasure) =
      ∫ z, G z ∂R.essentialFaceMeasure.prod R.essentialFaceMeasure := by
  rw [R.integral_essentialFaceMeasure_prod, R.integral_essentialFaceMeasure_prod]
  apply Finset.sum_congr rfl
  intro α _
  split_ifs
  · congr 1
    apply Finset.sum_congr rfl
    intro β _
    split_ifs
    · congr 1
      apply integral_congr_ae
      filter_upwards with v
      congr 1
      apply integral_congr_ae
      exact .of_forall fun w ↦ by
        dsimp only
        rw [h α β v w]
    · rfl
  · rfl

/-- The corresponding support principle after the half-radial density tilt. -/
theorem integral_halfRadialLimitMeasure_prod_congr_faces
    {β : ℝ} (hβ : 0 < β) (ζ : R.ChartFunctions)
    (F G : C(R.FaceDomain × R.FaceDomain, ℝ))
    (h : ∀ α γ v w,
      F (R.faceEmbedding α v, R.faceEmbedding γ w) =
      G (R.faceEmbedding α v, R.faceEmbedding γ w)) :
    (∫ z, F z ∂(R.halfRadialLimitMeasure β hβ ζ).prod
      (R.halfRadialLimitMeasure β hβ ζ)) =
      ∫ z, G z ∂(R.halfRadialLimitMeasure β hβ ζ).prod
        (R.halfRadialLimitMeasure β hβ ζ) := by
  let D := R.halfRadialLimitDensity β hβ ζ
  let H : C(R.FaceDomain × R.FaceDomain, ℝ) :=
    ⟨fun z ↦ D z.1 * D z.2,
      (D.continuous.comp continuous_fst).mul (D.continuous.comp continuous_snd)⟩
  unfold halfRadialLimitMeasure
  rw [integral_prod_withDensity_ofReal _ _ D.continuous.aemeasurable
      D.continuous.aemeasurable
      (.of_forall fun u ↦ (R.halfRadialLimitDensity_pos β hβ ζ u).le)
      (.of_forall fun u ↦ (R.halfRadialLimitDensity_pos β hβ ζ u).le),
    integral_prod_withDensity_ofReal _ _ D.continuous.aemeasurable
      D.continuous.aemeasurable
      (.of_forall fun u ↦ (R.halfRadialLimitDensity_pos β hβ ζ u).le)
      (.of_forall fun u ↦ (R.halfRadialLimitDensity_pos β hβ ζ u).le)]
  exact R.integral_essentialFaceMeasure_prod_congr_faces (H * F) (H * G)
    (fun α γ v w ↦ by simp only [ContinuousMap.mul_apply, h α γ v w])

namespace EmpiricalProcessInput
variable {R} {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

/-- The pair numerator
$\int_{W \times W} B(w, w')\,e^{-n\beta K_n(w)}\varphi(w)\,e^{-n\beta K_n(w')}\varphi(w')\,dw\,dw'$
at sample size $n$ and sample point $\omega$, where $K_n$ is
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.Kn`. With the population product
`SingularLearningTheory.BayesGibbs.populationProduct` as $B$, it is the $Q$ numerator of the
functional variance. -/
@[expose] noncomputable def pairWeightedPartition (B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∫ z, B z * (Real.exp (-(n * β * I.Kn n ω z.1)) * φ z.1) *
    (Real.exp (-(n * β * I.Kn n ω z.2)) * φ z.2)
    ∂(volume.restrict W).prod (volume.restrict W)

/-- The pair numerator
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.pairWeightedPartition` with each
factor $e^{-n\beta K_n(w)}\varphi(w)$ multiplied by the localization $\chi(w)$ of the atlas. The
two differ by a term that vanishes in probability after scaling by the square of
`SingularLearningTheory.ResolutionAtlas.halfRadialScale`. -/
@[expose] noncomputable def pairLocalizedPartition (B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ)
    (n : ℕ) (ω : Ω) : ℝ :=
  ∫ z, B z * (R.χ z.1 * (Real.exp (-(n * β * I.Kn n ω z.1)) * φ z.1)) *
    (R.χ z.2 * (Real.exp (-(n * β * I.Kn n ω z.2)) * φ z.2))
    ∂(volume.restrict W).prod (volume.restrict W)

/-- The pair-weighted partition function is the integral against the product of the restricted
prior with itself. -/
theorem pairWeightedPartition_eq_prior_product
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ) (n : ℕ) (ω : Ω) :
    I.pairWeightedPartition B n ω =
      ∫ z, B z * Real.exp (-(n * β * I.Kn n ω z.1)) *
        Real.exp (-(n * β * I.Kn n ω z.2))
        ∂((volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))).prod
          ((volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))) := by
  have hφ0 : ∀ᵐ w ∂volume.restrict W, 0 ≤ φ w :=
    (ae_restrict_mem hW).mono fun w hw ↦ hφ w hw
  rw [integral_prod_withDensity_ofReal _ _ hφi.aemeasurable hφi.aemeasurable hφ0 hφ0]
  apply integral_congr_ae
  exact .of_forall fun z ↦ by dsimp [pairWeightedPartition]; ring

/-- Unlocalized-minus-localized pair remainder is negligible at the
Q-numerator normalization, using the already established scalar tail bound. -/
theorem pair_localization_remainder_tendstoInMeasure
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ}
    (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w ∈ W, ∀ v ∈ W, |B (w, v)| ≤ M) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦ R.halfRadialScale n ^ 2 *
      (I.pairWeightedPartition B n ω - I.pairLocalizedPartition B n ω)) atTop 0 := by
  let Z : ℕ → Ω → ℝ := fun n ω ↦
    (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω
  let T : ℕ → Ω → ℝ := fun n ω ↦
    (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) * I.tail n ω
  have hZ := I.tendstoInDistribution_normalizedEvidence hW hφ hφi hβ
    (fun α _ ↦ R.exists_lipschitzOnWith_weight α)
  have hZT : TendstoInMeasure P (fun n ω ↦ Z n ω * T n ω) atTop 0 :=
    tendstoInMeasure_mul_zero_of_tight
      (fun η hη ↦ by simpa only [Z, Real.norm_eq_abs] using
        hZ.eventually_measure_norm_gt_le hη)
      (I.tail_tendsto hW hφ hφi hβ (R.rlct + 1) R.mult)
  apply tendstoInMeasure_zero_of_eventually_abs_le
    (Z := fun n ω ↦ 2 * M * (Z n ω * T n ω)) ?_
    (tendstoInMeasure_const_mul_zero (2 * M) hZT)
  filter_upwards [eventually_ge_atTop 1] with n hn
  filter_upwards [I.ae_integrableOn hW hφ hφi hβ hn] with ω he
  let e : (Fin d → ℝ) → ℝ := fun w ↦ Real.exp (-(n * β * I.Kn n ω w)) * φ w
  have he0 : ∀ᵐ w ∂volume.restrict W, 0 ≤ e w := by
    filter_upwards [ae_restrict_mem hW] with w hw
    exact mul_nonneg (Real.exp_pos _).le (hφ w hw)
  have hbb : ∀ᵐ z ∂(volume.restrict W).prod (volume.restrict W), |B z| ≤ M := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem hW),
      Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem hW)] with z hz₁ hz₂
    exact hb z.1 hz₁ z.2 hz₂
  have h := BayesGibbs.abs_pair_localization_error_le hB hM hbb he he0
    R.χ_measurable R.χ_nonneg R.χ_le_one
  have htail : (∫ w in W, (1 - R.χ w) * e w) = I.tail n ω := by
    apply integral_congr_ae
    exact .of_forall fun w ↦ by dsimp [e, tail]; ring
  rw [htail] at h
  change |R.halfRadialScale n ^ 2 *
    (I.pairWeightedPartition B n ω - I.pairLocalizedPartition B n ω)| ≤ _
  rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
  calc _ ≤ R.halfRadialScale n ^ 2 * (2 * M * I.tail n ω * I.normalizedEvidence n ω) :=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _ = _ := by rw [R.halfRadialScale_sq hn]; dsimp [Z, T]; ring

/-- Full parameter-space pair numerator, including every cross/tail term,
is approximated by the current-field compact radial integral. -/
theorem pairWeightedPartition_sub_limit_tendstoInMeasure
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ}
    (hB : Measurable B) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w ∈ W, ∀ v ∈ W, |B (w, v)| ≤ M)
    (C : C(R.FaceDomain × R.FaceDomain, ℝ))
    (hfactor : ∀ α γ (u : cube d (R.b α)) (v : cube d (R.b γ)),
      B (R.g α u, R.g γ v) =
        ((∏ j, (u : Fin d → ℝ) j ^ R.k α j) *
          (∏ j, (v : Fin d → ℝ) j ^ R.k γ j)) * C (⟨α, u⟩, ⟨γ, v⟩)) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      R.halfRadialScale n ^ 2 * I.pairWeightedPartition B n ω -
      ∫ z, C z ∂(R.halfRadialLimitMeasure β hβ (I.Ξ n ω)).prod
        (R.halfRadialLimitMeasure β hβ (I.Ξ n ω))) atTop 0 := by
  have ht := I.pair_localization_remainder_tendstoInMeasure hW hφ hφi hβ hB hM hb
  have hl := I.pair_halfRadial_sub_limit_tendstoInMeasure hβ C
  refine (tendstoInMeasure_add_zero ht hl).congr' ?_ EventuallyEq.rfl
  filter_upwards [eventually_ge_atTop 1] with n hn
  filter_upwards [I.ae_localized_pair_eq_halfRadial hW hφ hφi hβ hB hM hb C hfactor hn]
    with ω hω
  change R.halfRadialScale n ^ 2 * (I.pairWeightedPartition B n ω -
    I.pairLocalizedPartition B n ω) + _ = _
  change R.halfRadialScale n ^ 2 * I.pairLocalizedPartition B n ω = _ at hω
  rw [← hω]
  ring

end EmpiricalProcessInput
end ResolutionAtlas

namespace BayesGibbs
variable {X : Type*} [MeasurableSpace X] {q : Measure X} [SFinite q]
  {d : ℕ} {f : X → (Fin d → ℝ) → ℝ}

/-- The population product $E_q[f(x, w) f(x, w')] = \int f(x, w)\,f(x, w')\,dq(x)$ at a pair
$(w, w')$ of parameters. On the diagonal it equals
`SingularLearningTheory.BayesGibbs.populationSecondMoment`. -/
@[expose] noncomputable def populationProduct (q : Measure X) (f : X → (Fin d → ℝ) → ℝ)
    (z : (Fin d → ℝ) × (Fin d → ℝ)) : ℝ := ∫ x, f x z.1 * f x z.2 ∂q

theorem measurable_populationProduct (hf : Measurable (Function.uncurry f)) :
    Measurable (populationProduct q f) := by
  have h : Measurable (fun p : X × ((Fin d → ℝ) × (Fin d → ℝ)) ↦
      f p.1 p.2.1 * f p.1 p.2.2) :=
    (hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  exact h.stronglyMeasurable.integral_prod_left.measurable

private theorem populationProduct_bounded_of_squares
    {W : Set (Fin d → ℝ)} (hf : Measurable (Function.uncurry f))
    (h2 : ∀ w ∈ W, Integrable (fun x ↦ f x w ^ 2) q)
    {M : ℝ} (hM : ∀ w ∈ W, |populationSecondMoment q f w| ≤ M) :
    ∀ w ∈ W, ∀ v ∈ W, |populationProduct q f (w, v)| ≤ M := by
  intro w hw v hv
  have h := abs_integral_product_le_half_squares
    hf.of_uncurry_right.aestronglyMeasurable hf.of_uncurry_right.aestronglyMeasurable
    (h2 w hw) (h2 v hv)
  have hw' := (le_abs_self (populationSecondMoment q f w)).trans (hM w hw)
  have hv' := (le_abs_self (populationSecondMoment q f v)).trans (hM v hv)
  change |populationProduct q f (w, v)| ≤
    (populationSecondMoment q f w + populationSecondMoment q f v) / 2 at h
  linarith

end BayesGibbs

namespace ResolutionAtlas
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
/-- The metric `Metric.Sigma.metricSpace` on the disjoint union
`SingularLearningTheory.ResolutionAtlas.FaceDomain` of the chart cubes, local to this module. Its
topology is the disjoint-union topology. -/
noncomputable local instance globalPairNumeratorMetric2 : MetricSpace R.FaceDomain := Metric.Sigma.metricSpace
variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {Xs : ℕ → Ω → X}
  {f : X → (Fin d → ℝ) → ℝ} {s : ℝ≥0∞}
  (L : R.AnalyticResolvedLikelihood s q f)
  (E : EmpiricalProcessLimit q (fun x (u : R.FaceDomain) ↦ L.a u.1 x u.2) Xs P P')
  (hE4 : E.MomentBound 4)

variable {R} in
theorem AnalyticResolvedLikelihood.integral_halfRadialLimit_rawCovariance_eq_compactQnum
    {β : ℝ} (hβ : 0 < β) (ζ : R.ChartFunctions) :
    (∫ z, L.rawCovarianceCM E hE4 z
      ∂(R.halfRadialLimitMeasure β hβ ζ).prod (R.halfRadialLimitMeasure β hβ ζ)) =
      GaussianPosterior.compactQnum R.essentialFaceMeasure β R.rlct
        (E.covarianceKernel hE4) (R.chartFieldCM ζ) := by
  let C : C(R.FaceDomain × R.FaceDomain, ℝ) :=
    ⟨fun z ↦ (E.covarianceKernel hE4).C z.1 z.2, (E.covarianceKernel hE4).continuous⟩
  rw [R.integral_halfRadialLimitMeasure_prod_congr_faces hβ ζ
    (L.rawCovarianceCM E hE4) C (L.rawCovarianceCM_faces E hE4)]
  exact R.integral_halfRadialLimitMeasure_prod_eq_compactQnum β hβ ζ (E.covarianceKernel hE4)

variable {R} in
/-- Raw Q-coordinate convergence, under the original RFV bound. The
L² premise is automatic from FundamentalConditionI at s≥2, including s=6. -/
theorem EmpiricalProcessInput.normalized_populationProduct_sub_compactQnum
    {β : ℝ} (hβ : 0 < β) (J : R.EmpiricalProcessInput β P P')
    (hW : IsCompact W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f)) (hK : ContinuousOn K W)
    (h2 : ∀ w ∈ W, Integrable (fun x ↦ f x w ^ 2) q)
    {c : ℝ} (hc : 0 ≤ c)
    (hrfv : ∀ w ∈ W, BayesGibbs.populationSecondMoment q f w ≤ c * K w) :
    TendstoInMeasure P (fun (n : ℕ) ω ↦
      R.halfRadialScale n ^ 2 * J.pairWeightedPartition (BayesGibbs.populationProduct q f) n ω -
      GaussianPosterior.compactQnum R.essentialFaceMeasure β R.rlct
        (E.covarianceKernel hE4) (R.chartFieldCM (J.Ξ n ω))) atTop 0 := by
  obtain ⟨M, hM0, hM⟩ := BayesGibbs.populationSecondMoment_bounded_of_rfv hW hK hc hrfv
  have hbound := BayesGibbs.populationProduct_bounded_of_squares hf h2 hM
  have h := J.pairWeightedPartition_sub_limit_tendstoInMeasure hW.measurableSet hφ hφi hβ
    (BayesGibbs.measurable_populationProduct hf) hM0 hbound (L.rawCovarianceCM E hE4)
    (L.populationProduct_chart E hE4)
  exact h.congr (fun n ↦ .of_forall fun ω ↦ by
    rw [L.integral_halfRadialLimit_rawCovariance_eq_compactQnum E hE4 hβ]) EventuallyEq.rfl

end ResolutionAtlas
end SingularLearningTheory
