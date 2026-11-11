/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.Covariance.PosteriorReplacement
public import SLT.BayesGibbs.FiniteSample.PosteriorAUI
public import SLT.BayesGibbs.FiniteSample.PosteriorRatios
import SLT.BayesGibbs.TightProducts
import SLT.BayesGibbs.CompactPosterior.RatioProbability
public import SLT.BayesGibbs.FiniteSample.PosteriorFive
import SLT.BayesGibbs.Posterior.FirstMoment
import SLT.BayesGibbs.ExpMeasure
import SLT.BayesGibbs.Posterior.RadialMoment
public import SLT.BayesGibbs.Covariance.LLN
import SLT.Probability.Moments.EmpiricalSumEven

/-!
# Replacing the empirical covariance in probability

As $n \to \infty$, the functional variance $V$ of the tempered posterior minus its population
form, in which the empirical covariance of the log density ratio $f$ is replaced by its
expectation under $q$, tends to zero in probability. This is the last coordinate of the gap
between `SingularLearningTheory.BayesGibbs.posteriorFive` and
`SingularLearningTheory.BayesGibbs.populationPosteriorFive`. At each sample the gap is at most
$2\delta_n \cdot nE_w[K(w)]$, with errors $\delta_n \to 0$ almost surely, and $nE_w[K(w)]$ is
bounded in probability through the bound $\sqrt n|K_n - K| \le \Lambda_n\sqrt K$, with
$\Lambda_n$ bounded in probability, and the Laplace doubling bound.

## Main results

* `SingularLearningTheory.BayesGibbs.finiteSample_covariance_replacement_of_error`: the gap tends to zero in
  probability when the error of the empirical covariance is at most $\delta_n K(w)$ on the
  diagonal and $\delta_n\sqrt{K(w)}\sqrt{K(v)}$ for pairs, with $\delta_n \to 0$ almost surely.
* `SingularLearningTheory.BayesGibbs.finiteSample_covariance_replacement_tendstoInMeasure`: the same under
  fundamental condition (I) at $s = 6$, an analytic resolution of $f$ and weak limits of its
  empirical processes on the charts and on the tail $\{K \ge \delta\}$, which supply the errors
  $\delta_n$.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.BayesGibbs

private theorem tight_quadratic_envelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Λ : ℕ → Ω → ℝ}
    (hΛ : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < |Λ n ω|} ≤ ENNReal.ofReal η) {c : ℝ} (hc : 0 ≤ c) :
    ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < |c + 4 * Λ n ω ^ 2|} ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨M, N, hN⟩ := hΛ η hη
  refine ⟨c + 4 * (|M| + 1) ^ 2, N, fun n hn ↦ (measure_mono ?_).trans (hN n hn)⟩
  intro ω hω
  change c + 4 * (|M| + 1) ^ 2 < |c + 4 * Λ n ω ^ 2| at hω
  change M < |Λ n ω|
  rw [abs_of_nonneg (show 0 ≤ c + 4 * Λ n ω ^ 2 by positivity)] at hω
  by_contra hh
  have hL : |Λ n ω| ≤ |M| + 1 := (le_of_not_gt hh).trans (by linarith [le_abs_self M])
  have hs := pow_le_pow_left₀ (abs_nonneg _) hL 2
  rw [sq_abs] at hs
  nlinarith

/-- Probability endpoint from the raw-kernel error. This auxiliary lemma
is used only internally by the theorem below. -/
private theorem finiteSample_covariance_replacement_of_error
    {d : ℕ} {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
    {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ} {Xs : ℕ → Ω → X}
    (hν : ν ≠ 0) (hKm : Measurable K) (hf : Measurable (Function.uncurry f))
    (hK0 : ∀ᵐ w ∂ν, 0 ≤ K w) {B : ℝ} (hKB : ∀ᵐ w ∂ν, K w ≤ B)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    {A : X → ℝ} (hAm : Measurable A) (hA0 : ∀ x, 0 ≤ A x) (hA6 : MemLp A 6 q)
    (hAf : ∀ᵐ x ∂q, ∀ᵐ w ∂ν, |f x w| ≤ A x * Real.sqrt (K w))
    {Λ : ℕ → Ω → ℝ} (hΛ0 : ∀ n ω, 0 ≤ Λ n ω)
    (hΛtight : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < |Λ n ω|} ≤ ENNReal.ofReal η)
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ᵐ w ∂ν,
      Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ Λ n ω * Real.sqrt (K w))
    {β D : ℝ} (hβ : 0 < β) (hD : 1 ≤ D)
    (hLD : ∀ᶠ n : ℕ in atTop, ∫ w, Real.exp (-((n : ℝ) * β / 4 * K w)) ∂ν ≤
      D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w)) ∂ν)
    {δ : ℕ → Ω → ℝ} (hδm : ∀ n, Measurable (δ n)) (hδ0 : ∀ n ω, 0 ≤ δ n ω)
    (hδlim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ δ n ω) atTop (𝓝 0))
    (hδbound : ∀ᵐ ω ∂P, ∀ n,
      (∀ᵐ w ∂ν, |rawProductError q f Xs n ω w w| ≤ δ n ω * K w) ∧
      (∀ᵐ w ∂ν, ∀ᵐ v ∂ν, |rawProductError q f Xs n ω w v| ≤
        δ n ω * (Real.sqrt (K w) * Real.sqrt (K v)))) :
    TendstoInMeasure P (fun n ω ↦ posteriorFive ν q K f Xs β n ω 4 -
      populationPosteriorFive (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω
          w))
        q K (empiricalLoss f Xs n ω) f n 4) atTop 0 := by
  let c := 4 / β * Real.log D
  have hc : 0 ≤ c := mul_nonneg (by positivity) (Real.log_nonneg hD)
  have hδprob : TendstoInMeasure P δ atTop 0 :=
    tendstoInMeasure_of_tendsto_ae (fun n ↦ (hδm n).aestronglyMeasurable) hδlim
  have hmajor : TendstoInMeasure P
      (fun n ω ↦ 2 * ((c + 4 * Λ n ω ^ 2) * δ n ω)) atTop 0 :=
    tendstoInMeasure_const_mul_zero 2
      (tendstoInMeasure_mul_zero_of_tight (tight_quadratic_envelope hΛtight hc) hδprob)
  apply tendstoInMeasure_zero_of_eventually_abs_le (Z := fun n ω ↦ 2 * ((c + 4 * Λ n ω ^ 2) * δ n ω)) _ hmajor
  have hA2 : Integrable (fun x ↦ A x ^ 2) q :=
    integrable_pow_of_memLp (s := 6) (by norm_num) hA6 (by norm_num)
  have hsample : ∀ᵐ ω ∂P, ∀ i, ∀ᵐ w ∂ν,
      |f (Xs i ω) w| ≤ A (Xs i ω) * Real.sqrt (K w) := by
    apply ae_all_iff.mpr
    intro i
    have h := hAf
    rw [← hlaw i] at h
    exact ae_of_ae_map (hX i).aemeasurable h
  filter_upwards [hLD, eventually_ge_atTop 1] with n hLDn hn
  filter_upwards [he n hn, hsample, hδbound] with ω heω hsω hδω
  let Kn := empiricalLoss f Xs n ω
  let Q := Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * Kn w)
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hKnm : Measurable Kn := by
    unfold Kn empiricalLoss
    exact (Finset.measurable_sum _ fun i _ ↦ hf.of_uncurry_left).div_const _
  have hsand : ∀ᵐ w ∂ν,
      (n : ℝ) * β * (K w / 2) - β / 2 * Λ n ω ^ 2 ≤ (n : ℝ) * β * Kn w ∧
      (n : ℝ) * β * Kn w ≤ (n : ℝ) * β * (3 / 2 * K w) + β / 2 * Λ n ω ^ 2 := by
    filter_upwards [hK0, heω] with w hw0 hwe
    simpa only [zero_div, add_zero, zero_mul] using
      tilted_exponent_bounds (f := 0) (A := 0) (σ := 0) hw0 hn' hβ
        ⟨le_rfl, zero_le_one⟩ hwe (by simp)
  obtain ⟨hQprob, hKi, hKb⟩ := posterior_first_moment_le_ae (G := fun w ↦ (n : ℝ) * β * Kn w) hν hKm (hKnm.const_mul _)
    hK0 hKB hn' hβ (by positivity : 0 ≤ β / 2 * Λ n ω ^ 2) hD
    (hsand.mono fun _ h ↦ h.1) (hsand.mono fun _ h ↦ h.2) hLDn
  letI : IsProbabilityMeasure Q := hQprob
  have hgg : (n : ℝ) * ∫ w, K w ∂Q ≤ c + 4 * Λ n ω ^ 2 := by
    have heq : 8 / β * (β / 2 * Λ n ω ^ 2) = 4 * Λ n ω ^ 2 := by field_simp [hβ.ne'] <;> ring
    simpa only [heq] using hKb
  have hb := empirical_population_variance_error_le hn ω hf hKm hKi
    (ae_expMeasure_of_ae hK0) hAm hA2 hA0 (ae_expMeasure_of_ae hKB)
    (hAf.mono fun x hx ↦ ae_expMeasure_of_ae hx)
    (fun i _ ↦ ae_expMeasure_of_ae (hsω i)) (hδ0 n ω)
    (ae_expMeasure_of_ae (hδω n).1)
    (ae_expMeasure_of_ae ((hδω n).2.mono fun w hw ↦ ae_expMeasure_of_ae hw))
  change |(∑ i ∈ Finset.range n, posteriorFeatureVariance Q f (Xs i ω)) -
      (n : ℝ) * ((∫ w, ∫ x, f x w ^ 2 ∂q ∂Q) -
        ∫ z, ∫ x, f x z.1 * f x z.2 ∂q ∂Q.prod Q)| ≤ _
  exact hb.trans (by nlinarith [mul_le_mul_of_nonneg_left hgg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (hδ0 n ω))])

/-- Covariance replacement on the finite-sample and population five-vectors. The law of large
numbers for the raw covariances is proved from the sixth-moment conditions and the chart and tail
processes. -/
theorem finiteSample_covariance_replacement_tendstoInMeasure
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
    [CompactSpace {w // w ∈ W ∧ R.δ ≤ K w}]
    (E : EmpiricalProcessLimit q
      (fun x (u : (α : R.ι) × cube d (R.b α)) ↦ L.a u.1 x u.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P PT)
    (hν : (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)) ≠ 0)
    (hKm : Measurable K)
    (hK0 : ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)), 0 ≤ K w)
    {B : ℝ} (hKB : ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)), K w ≤ B)
    {A : X → ℝ} (hAm : Measurable A) (hA0 : ∀ x, 0 ≤ A x) (hA6 : MemLp A 6 q)
    (hAf : ∀ᵐ x ∂q, ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
      |f x w| ≤ A x * Real.sqrt (K w))
    {Λ : ℕ → Ω → ℝ} (hΛ0 : ∀ n ω, 0 ≤ Λ n ω)
    (hΛtight : ∀ η > 0, ∃ M : ℝ, ∃ N : ℕ, ∀ n ≥ N,
      P {ω | M < |Λ n ω|} ≤ ENNReal.ofReal η)
    (he : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P,
      ∀ᵐ w ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)),
        Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ Λ n ω * Real.sqrt (K w))
    {β D : ℝ} (hβ : 0 < β) (hD : 1 ≤ D)
    (hLD : ∀ᶠ n : ℕ in atTop,
      ∫ w, Real.exp (-((n : ℝ) * β / 4 * K w))
        ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)) ≤
      D * ∫ w, Real.exp (-(3 * (n : ℝ) * β / 2 * K w))
        ∂(volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))) :
    let ν := (volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))
    TendstoInMeasure P (fun n ω ↦ posteriorFive ν q K f Xs β n ω 4 -
      populationPosteriorFive (Measure.expMeasure ν (fun w ↦ (n : ℝ) * β * empiricalLoss f Xs n ω
          w))
        q K (empiricalLoss f Xs n ω) f n 4) atTop 0 := by
  haveI : IsFiniteMeasure ((volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w))) :=
    isFiniteMeasure_withDensity_ofReal hφ.hasFiniteIntegral
  obtain ⟨δ, hδm, hδ0, hδlim, hδbound⟩ :=
    exists_covariance_error R I L hW hφ hf hcont hX hlaw hind E T
  exact finiteSample_covariance_replacement_of_error hν hKm hf hK0 hKB hX hlaw hAm hA0 hA6 hAf
    hΛ0 hΛtight he hβ hD hLD hδm hδ0 hδlim hδbound

end SingularLearningTheory.BayesGibbs
