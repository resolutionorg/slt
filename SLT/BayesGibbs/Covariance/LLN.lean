/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CombinedFeatureCovariance
import SLT.BayesGibbs.Prior.AEPairTransport
import SLT.BayesGibbs.Prior.AETransport
import SLT.BayesGibbs.FeatureEnvelopeSix
import SLT.BayesGibbs.SixthMoments
import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.StandardForm.FundamentalConditionI
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Uniform law of large numbers for the covariance of the log density ratio

Under fundamental condition (I) at $s = 6$, an analytic resolution of the log density ratio $f$,
and weak limits of its empirical processes on the charts and on the tail $\{K \ge \delta\}$, there
are measurable random errors $\delta_n \ge 0$ with $\delta_n \to 0$ almost surely such that,
almost surely, for every $n$ and almost every pair $w, v$ under the prior,
$$\Bigl|\frac{1}{n}\sum_{i<n} f(X_i, w)f(X_i, v) - E_q[f(x, w)f(x, v)]\Bigr|
  \le \delta_n\sqrt{K(w)}\sqrt{K(v)}.$$
The proof writes $f(x, w) = \sqrt{K(w)}F(x, u)$ with one continuous feature $F$ on the disjoint
union of the chart cubes and the tail, and applies the strong law for its product feature. The
bound lets the empirical covariance in the functional variance be replaced by the population one.

## Main definitions

* `SingularLearningTheory.BayesGibbs.rawProductError`: the error of the empirical covariance of $f$ at
  a pair of parameters, without centering.

## Main results

* `SingularLearningTheory.BayesGibbs.exists_covariance_error`: the errors $\delta_n$ exist, with
  the bound above on the diagonal and for pairs.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

/-- The raw empirical product error, without centering the data feature. -/
@[expose] noncomputable def rawProductError {X Ω V : Type*} [MeasurableSpace X]
    (q : Measure X) (f : X → V → ℝ) (Xs : ℕ → Ω → X)
    (n : ℕ) (ω : Ω) (w v : V) : ℝ :=
  (n : ℝ)⁻¹ * (∑ i ∈ Finset.range n, f (Xs i ω) w * f (Xs i ω) v) -
    ∫ x, f x w * f x v ∂q

theorem measurable_rawProductError {X Ω V : Type*} [MeasurableSpace X] [MeasurableSpace V]
    {q : Measure X} [SFinite q] {f : X → V → ℝ} {Xs : ℕ → Ω → X}
    (hf : Measurable (Function.uncurry f)) (n : ℕ) (ω : Ω) :
    Measurable (fun z : V × V ↦ rawProductError q f Xs n ω z.1 z.2) := by
  have hpop : Measurable (fun z : V × V ↦ ∫ x, f x z.1 * f x z.2 ∂q) :=
    ((hf.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).mul
      (hf.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))).stronglyMeasurable.integral_prod_left.measurable
  exact ((Finset.measurable_sum _ fun i _ ↦
    (hf.of_uncurry_left.comp measurable_fst).mul
      (hf.of_uncurry_left.comp measurable_snd)).const_mul _).sub hpop

/-- The uniform error of the law of large numbers for the covariances. The diagonal and pair
bounds hold for every n on one common sample event. -/
theorem exists_covariance_error
    {d : ℕ} {X Ω Ω' ΩT : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace ΩT]
    {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {PT : Measure ΩT} [IsProbabilityMeasure PT]
    {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (R : ResolutionAtlas K φ W) (I : FundamentalConditionI 6 q f K W)
    (L : R.AnalyticResolvedLikelihood 6 q f)
    (hW : IsCompact W) (hφ : IntegrableOn φ W)
    (hf : Measurable (Function.uncurry f))
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    (E : EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P PT) :
    ∃ δ : ℕ → Ω → ℝ,
      (∀ n, Measurable (δ n)) ∧ (∀ n ω, 0 ≤ δ n ω) ∧
      (∀ᵐ ω ∂P, Tendsto (fun n ↦ δ n ω) atTop (𝓝 0)) ∧
      ∀ᵐ ω ∂P, ∀ n,
        (∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
          |rawProductError q f Xs n ω w w| ≤ δ n ω * K w) ∧
        (∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
          ∀ᵐ v ∂(volume.restrict W).withDensity (fun v ↦ ENNReal.ofReal (φ v)),
            |rawProductError q f Xs n ω w v| ≤
              δ n ω * (Real.sqrt (K w) * Real.sqrt (K v))) := by
  let U := (α : R.ι) × cube d (R.b α)
  let V := {w // w ∈ W ∧ R.δ ≤ K w}
  letI : MetricSpace U := Metric.Sigma.metricSpace
  haveI : CompactSpace V := isCompact_iff_compactSpace.mp (I.isCompact_tail hW R.δ)
  letI : MetricSpace (CombinedFeatureDomain U V) := Metric.Sigma.metricSpace
  have hmeanE : Continuous fun u : U ↦ ∫ x, L.a u.1 x u.2 ∂q := by
    have heq : (fun u : U ↦ ∫ x, L.a u.1 x u.2 ∂q) =
        fun u ↦ ∏ j, (u.2 : Fin d → ℝ) j ^ R.k u.1 j := funext fun u ↦ L.mean u.1 u.2
    rw [heq]
    refine continuous_sigma fun α ↦ ?_
    change Continuous (fun u : cube d (R.b α) ↦ ∏ j, (u : Fin d → ℝ) j ^ R.k α j)
    exact continuous_finsetProd _ fun j _ ↦
      ((continuous_apply j).comp continuous_subtype_val).pow _
  obtain ⟨F₀, hF₀m, hF₀Lp, hF₀⟩ := EmpiricalProcessLimit.exists_continuous_feature_rep_six E
    (L.momentBound_chart_six hX hlaw hind E) (hX 0) (hlaw 0)
    (fun u ↦ (continuous_eval_const u.2).measurable.comp (L.a_measurable u.1))
    (Eventually.of_forall fun x ↦ continuous_sigma fun α ↦ (L.a α x).continuous) hmeanE
  have hKT : Continuous fun w : V ↦ K w :=
    I.continuousOn_K.comp_continuous continuous_subtype_val fun w ↦ w.2.1
  have hmeanT : Continuous fun w : V ↦ ∫ x, f x w / Real.sqrt (K w) ∂q := by
    have heq : (fun w : V ↦ ∫ x, f x w / Real.sqrt (K w) ∂q) =
        fun w : V ↦ K w / Real.sqrt (K w) := by
      funext w
      rw [integral_div, ← I.K_eq w]
    rw [heq]
    exact hKT.div (Real.continuous_sqrt.comp hKT)
      (fun w ↦ (Real.sqrt_pos.mpr (R.δ_pos.trans_le w.2.2)).ne')
  have hcontT : ∀ᵐ x ∂q, Continuous fun w : V ↦ f x w / Real.sqrt (K w) := by
    filter_upwards [I.ae_continuousOn_tail hcont R.δ_pos] with x hx
    exact continuousOn_iff_continuous_domRestrict.mp hx
  obtain ⟨F₁, hF₁m, hF₁Lp, hF₁⟩ := EmpiricalProcessLimit.exists_continuous_feature_rep_six T
    (I.momentBound_tail_six hW hcont R.δ_pos hX hlaw hind T) (hX 0) (hlaw 0)
    (fun w ↦ hf.of_uncurry_right.div_const _) hcontT hmeanT
  let F : X → C(CombinedFeatureDomain U V, ℝ) := combinedFeature F₀ F₁
  have hFm : Measurable F := measurable_combinedFeature hF₀m hF₁m
  have hF2 : MemLp F 2 q :=
    (memLp_combinedFeature hF₀m hF₁m hF₀Lp hF₁Lp).mono_exponent (by norm_num)
  let param : CombinedFeatureDomain U V → (Fin d → ℝ) := fun u ↦ match u with
    | ⟨false, ⟨α, v⟩⟩ => R.g α v
    | ⟨true, w⟩ => (show V from w).val
  have hfactor : ∀ᵐ x ∂q, ∀ α, ∀ u : cube d (R.b α),
      f x (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * L.a α x u :=
    ae_all_iff.mpr L.factor
  have heq : ∀ᵐ x ∂q, ∀ u : CombinedFeatureDomain U V,
      f x (param u) = Real.sqrt (K (param u)) * F x u := by
    filter_upwards [hF₀, hF₁, hfactor] with x h₀ h₁ hx
    rintro ⟨b, u⟩
    cases b
    · rcases u with ⟨α, v⟩
      have hmon : 0 ≤ ∏ j, (v : Fin d → ℝ) j ^ R.k α j :=
        Finset.prod_nonneg fun j _ ↦ pow_nonneg (v.2.1 j) _
      have hsq : K (R.g α v) = (∏ j, (v : Fin d → ℝ) j ^ R.k α j) ^ 2 := by
        rw [R.monomial α v v.2, Finset.prod_pow_two_mul]
      change f x (R.g α v) = Real.sqrt (K (R.g α v)) * F₀ x ⟨α, v⟩
      rw [hx α v, hsq, Real.sqrt_sq hmon, h₀ ⟨α, v⟩]
    · let v : V := u
      change f x (v : Fin d → ℝ) = Real.sqrt (K (v : Fin d → ℝ)) * F₁ x v
      rw [h₁ v]
      have hs : Real.sqrt (K (v : Fin d → ℝ)) ≠ 0 :=
        (Real.sqrt_pos.mpr (R.δ_pos.trans_le v.2.2)).ne'
      field_simp [hs]
  have heqXs : ∀ᵐ ω ∂P, ∀ i, ∀ u : CombinedFeatureDomain U V,
      f (Xs i ω) (param u) = Real.sqrt (K (param u)) * F (Xs i ω) u := by
    apply ae_all_iff.mpr
    intro i
    have hi := heq
    rw [← hlaw i] at hi
    exact ae_of_ae_map (hX i).aemeasurable hi
  let δ : ℕ → Ω → ℝ := fun n ω ↦
    ‖(n : ℝ)⁻¹ • (∑ i ∈ Finset.range n, productFeature (F (Xs i ω))) -
      ∫ x, productFeature (F x) ∂q‖
  refine ⟨δ, ?_, ?_, ?_, ?_⟩
  · intro n
    exact measurable_productFeature_error
      (U := CombinedFeatureDomain U V) (q := q) (Xs := Xs) (F := F) hFm hX n
  · intro n ω
    exact norm_nonneg _
  · exact productFeature_strongLaw
      (U := CombinedFeatureDomain U V) (P := P) (q := q) (Xs := Xs) (F := F)
      hFm hF2 hX hlaw hind
  · have hKm : Measurable K := by
      rw [funext I.K_eq]
      exact hf.stronglyMeasurable.integral_prod_left.measurable
    filter_upwards [heqXs] with ω hω n
    have hall : ∀ u v : CombinedFeatureDomain U V,
        |rawProductError q f Xs n ω (param u) (param v)| ≤
          δ n ω * (Real.sqrt (K (param u)) * Real.sqrt (K (param v))) := by
      intro u v
      exact factored_product_kernel_error_le (f := f) (Xs := Xs)
        (r := fun w ↦ Real.sqrt (K w)) hFm hF2 n ω (param u) (param v) u v
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        (heq.mono fun x hx ↦ hx u) (heq.mono fun x hx ↦ hx v)
        (fun i _ ↦ hω i u) (fun i _ ↦ hω i v)
    have hpm := measurable_rawProductError (q := q) (Xs := Xs) hf n ω
    constructor
    · apply R.ae_prior_of_chart_and_tail hW.measurableSet hφ
        (p := fun w ↦ |rawProductError q f Xs n ω w w| ≤ δ n ω * K w)
        (measurableSet_le ((hpm.comp (measurable_id.prodMk measurable_id)).abs)
          (hKm.const_mul _))
      · intro α u hu
        let z : CombinedFeatureDomain U V := ⟨false, ⟨α, ⟨u, hu⟩⟩⟩
        have h := hall z z
        have hK : 0 ≤ K (R.g α u) := by
          rw [R.monomial α u hu, Finset.prod_pow_two_mul]
          positivity
        simpa only [param, z, ← pow_two, Real.sq_sqrt hK] using h
      · intro w hw hwK
        let z : CombinedFeatureDomain U V := ⟨true, ⟨w, hw, hwK⟩⟩
        have h := hall z z
        simpa only [param, z, ← pow_two, Real.sq_sqrt (R.δ_pos.le.trans hwK)] using h
    · apply R.ae_prior_pair_of_chart_and_tail hW.measurableSet hφ
        (p := fun w v ↦ |rawProductError q f Xs n ω w v| ≤
          δ n ω * (Real.sqrt (K w) * Real.sqrt (K v)))
        (measurableSet_le hpm.abs
          (((hKm.sqrt.comp measurable_fst).mul (hKm.sqrt.comp measurable_snd)).const_mul _))
      · intro α u hu γ v hv
        exact hall ⟨false, ⟨α, ⟨u, hu⟩⟩⟩ ⟨false, ⟨γ, ⟨v, hv⟩⟩⟩
      · intro α u hu v hv hvK
        exact hall ⟨false, ⟨α, ⟨u, hu⟩⟩⟩ ⟨true, ⟨v, hv, hvK⟩⟩
      · intro w hw hwK γ v hv
        exact hall ⟨true, ⟨w, hw, hwK⟩⟩ ⟨false, ⟨γ, ⟨v, hv⟩⟩⟩
      · intro w hw hwK v hv hvK
        exact hall ⟨true, ⟨w, hw, hwK⟩⟩ ⟨true, ⟨v, hv, hvK⟩⟩

end SingularLearningTheory.BayesGibbs
