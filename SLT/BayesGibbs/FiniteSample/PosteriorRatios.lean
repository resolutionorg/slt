/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.FiniteSample.RawFive
public import SLT.BayesGibbs.Posterior.Measurability
import SLT.BayesGibbs.AtlasPairTransport
import SLT.BayesGibbs.ExpMeasure
public import SLT.BayesGibbs.LaplaceDoubling.Basic
import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Posterior expectations as ratios of weighted partition functions

Expectations under the tempered posterior, and under its product with itself, are ratios of
weighted partition functions to the evidence and to its square. Applied to the five finite-sample
raw integrals of an empirical process input, the evidence $Z$ and the integrals $T$, $H$, $D$, $Q$,
the algebraic normalization `SingularLearningTheory.GaussianPosterior.normalizeRaw` therefore gives
exactly the posterior vector `SingularLearningTheory.BayesGibbs.populationPosteriorFive`. This is the
identity through which the convergence in law of the raw integrals passes to the posterior
observables of [Wat09, Theorem 6.8].

## Main definitions

* `SingularLearningTheory.BayesGibbs.populationPosteriorFive`: the vector
  $(T - V/2,\ U - V/2,\ T,\ U,\ V)$ with $T = nG_g$, $U = nG_t$ and $V$ the functional variance
  with the population covariance of the log density ratio in place of the empirical one. It is
  the vector of the five observables before the Taylor remainders of the Bayes errors and the
  replacement of the empirical covariance are added.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.temperedPosterior`: the tempered
  posterior $e^{-n\beta K_n(w)}\varphi(w)\,dw / Z_n$ on $W$ built from the empirical loss of the
  input.

## Main results

* `SingularLearningTheory.BayesGibbs.integral_prod_expMeasure_eq_ratio`: an integral against the
  product of a tilted measure with itself is a ratio over the squared normalizer.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.integral_temperedPosterior_eq_ratio` and
  `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.integral_temperedPosterior_prod_eq_ratio`:
  posterior expectations of one and of two coordinates as ratios of weighted partition functions.
* `SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.normalize_finiteSampleRawFive_eq_populationPosteriorFive`:
  the normalized raw integrals equal `populationPosteriorFive` for every $n \ge 2$.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Topology
open scoped ENNReal Classical

namespace SingularLearningTheory.BayesGibbs

/-- Exact product-posterior ratio, including the totalized zero-evidence case. -/
private theorem integral_prod_expMeasure_eq_ratio {U : Type*} [MeasurableSpace U]
    (ν : Measure U) [SFinite ν] {G : U → ℝ} (hG : Measurable G) (F : U × U → ℝ) :
    (∫ z, F z ∂(expMeasure ν G).prod (expMeasure ν G)) =
      (∫ z, F z * Real.exp (-G z.1) * Real.exp (-G z.2) ∂ν.prod ν) /
        (∫ w, Real.exp (-G w) ∂ν) ^ 2 := by
  have hZ : 0 ≤ ∫ w, Real.exp (-G w) ∂ν := integral_nonneg fun _ ↦ (Real.exp_pos _).le
  have he : Measurable (fun w ↦ Real.exp (-G w)) := hG.neg.exp
  unfold expMeasure
  rw [prod_smul_left, prod_smul_right, smul_smul, integral_smul_measure,
    ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_ofReal hZ]
  rw [integral_prod_withDensity_ofReal _ _ he.aemeasurable he.aemeasurable
    (.of_forall fun _ ↦ (Real.exp_pos _).le) (.of_forall fun _ ↦ (Real.exp_pos _).le)]
  have hi : (∫ z, Real.exp (-G z.1) * Real.exp (-G z.2) * F z ∂ν.prod ν) =
      ∫ z, F z * Real.exp (-G z.1) * Real.exp (-G z.2) ∂ν.prod ν := by
    apply integral_congr_ae
    exact .of_forall fun z ↦ by ring
  rw [hi, smul_eq_mul]
  simp only [div_eq_mul_inv, pow_two, mul_inv_rev]
  ring

/-- The exact posterior vector before the predictive Taylor remainders and
empirical-to-population covariance replacement are added. -/
@[expose] noncomputable def populationPosteriorFive
    {X U : Type*} [MeasurableSpace X] [MeasurableSpace U]
    (Q : Measure U) (q : Measure X) (K Kn : U → ℝ) (f : X → U → ℝ) (n : ℕ) : Fin 5 → ℝ :=
  let T := (n : ℝ) * ∫ w, K w ∂Q
  let U := (n : ℝ) * ∫ w, Kn w ∂Q
  let V := (n : ℝ) * ((∫ w, (∫ x, f x w ^ 2 ∂q) ∂Q) -
    ∫ z, (∫ x, f x z.1 * f x z.2 ∂q) ∂Q.prod Q)
  ![T - V / 2, U - V / 2, T, U, V]

end SingularLearningTheory.BayesGibbs

namespace SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput
variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {R : ResolutionAtlas K φ W} {β : ℝ} {Ω Ω' : Type*}
  [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (J : R.EmpiricalProcessInput β P P')

/-- The tempered posterior $e^{-n\beta K_n(w)}\varphi(w)\,dw / Z_n$ on `W` at sample size $n$
and outcome $\omega$, with $K_n$ the empirical loss
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.Kn` of `J`. It is the Gibbs measure
`MeasureTheory.Measure.expMeasure` of the exponent $n\beta K_n$ over the prior
$\varphi\,dw$ on `W`. -/
@[expose] noncomputable def temperedPosterior (n : ℕ) (ω : Ω) : Measure (Fin d → ℝ) :=
  expMeasure ((volume.restrict W).withDensity (fun w ↦ ENNReal.ofReal (φ w)))
    (fun w ↦ (n : ℝ) * β * J.Kn n ω w)

/-- Exact one-coordinate posterior ratio on the original restricted prior. -/
theorem integral_temperedPosterior_eq_ratio
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (a : (Fin d → ℝ) → ℝ) (n : ℕ) (ω : Ω) :
    (∫ w, a w ∂J.temperedPosterior n ω) = J.weightedPartition a n ω / J.normalizedEvidence n ω := by
  unfold temperedPosterior
  rw [integral_expMeasure_eq_ratio _ ((J.Kn_measurable n).of_uncurry_left.const_mul _),
    BayesGibbs.integral_exp_restricted_prior hW hφ hφi]
  congr 1
  rw [integral_withDensity_eq_integral_toReal_smul₀ hφi.aemeasurable.ennreal_ofReal
    (.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hW] with w hw
  rw [ENNReal.toReal_ofReal (hφ w hw), smul_eq_mul]
  ring

/-- Exact two-coordinate posterior ratio. -/
theorem integral_temperedPosterior_prod_eq_ratio
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (B : (Fin d → ℝ) × (Fin d → ℝ) → ℝ) (n : ℕ) (ω : Ω) :
    (∫ z, B z ∂(J.temperedPosterior n ω).prod (J.temperedPosterior n ω)) =
      J.pairWeightedPartition B n ω / J.normalizedEvidence n ω ^ 2 := by
  unfold temperedPosterior
  rw [BayesGibbs.integral_prod_expMeasure_eq_ratio _
    ((J.Kn_measurable n).of_uncurry_left.const_mul _),
    BayesGibbs.integral_exp_restricted_prior hW hφ hφi,
    ← J.pairWeightedPartition_eq_prior_product hW hφ hφi]
  rfl

/-- The normalized raw vector is exactly the population-posterior five-vector.
Only the two ordinary Gibbs integrability facts are needed for the H identity;
no positive evidence premise or statistical normalization is inserted. -/
theorem normalize_finiteSampleRawFive_eq_populationPosteriorFive
    {X : Type*} [MeasurableSpace X] (q : Measure X) (f : X → (Fin d → ℝ) → ℝ)
    (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    {n : ℕ} (hn : 2 ≤ n) (ω : Ω)
    (hKi : Integrable K (J.temperedPosterior n ω))
    (hKni : Integrable (J.Kn n ω) (J.temperedPosterior n ω)) :
    GaussianPosterior.normalizeRaw (J.finiteSampleRawFive q f n ω) =
      BayesGibbs.populationPosteriorFive (J.temperedPosterior n ω) q K (J.Kn n ω) f n := by
  let S := (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1)
  have hn0 : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hn1 : 1 < (n : ℝ) := by exact_mod_cast (show 1 < n by omega)
  have hS : S ≠ 0 := (div_pos (Real.rpow_pos_of_pos hn0 _) (pow_pos (Real.log_pos hn1) _)).ne'
  have hTscale : (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) = S * n := by
    rw [Real.rpow_add hn0, Real.rpow_one]
    dsimp [S]
    ring
  have hHscale : R.halfRadialScale n * Real.sqrt n = S * n := by
    rw [ResolutionAtlas.halfRadialScale, Real.sqrt_eq_rpow]
    calc _ = ((n : ℝ) ^ (R.rlct + 1 / 2) * (n : ℝ) ^ (1 / 2 : ℝ)) /
        Real.log n ^ (R.mult - 1) := by ring
      _ = (n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) := by
        rw [← Real.rpow_add hn0]
        congr 2
        ring
      _ = _ := hTscale
  have hQscale : R.halfRadialScale n ^ 2 = S ^ 2 * n := by
    rw [R.halfRadialScale_sq (by omega), hTscale]
    change S * (S * n) = S ^ 2 * n
    ring
  have hcancel (a : ℝ) : S * n * a / (S * J.normalizedEvidence n ω) = (n : ℝ) *
      (a / J.normalizedEvidence n ω) := by
    rw [mul_assoc, mul_div_mul_left _ _ hS]
    ring
  have hcancel₂ (a : ℝ) : S ^ 2 * n * a / (S * J.normalizedEvidence n ω) ^ 2 =
      (n : ℝ) * (a / J.normalizedEvidence n ω ^ 2) := by
    rw [mul_pow, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero 2 hS)]
    ring
  have hT : J.finiteSampleRawFive q f n ω 1 / J.finiteSampleRawFive q f n ω 0 =
      (n : ℝ) * ∫ w, K w ∂J.temperedPosterior n ω := by
    change ((n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) *
      J.weightedPartition K n ω) / (S * J.normalizedEvidence n ω) = _
    rw [hTscale, hcancel, J.integral_temperedPosterior_eq_ratio hW hφ hφi]
  have hD : J.finiteSampleRawFive q f n ω 3 / J.finiteSampleRawFive q f n ω 0 =
      (n : ℝ) * ∫ w, BayesGibbs.populationSecondMoment q f w ∂J.temperedPosterior n ω := by
    change ((n : ℝ) ^ (R.rlct + 1) / Real.log n ^ (R.mult - 1) *
      J.weightedPartition (BayesGibbs.populationSecondMoment q f) n ω) /
          (S * J.normalizedEvidence n ω) = _
    rw [hTscale, hcancel, J.integral_temperedPosterior_eq_ratio hW hφ hφi]
  have hQ : J.finiteSampleRawFive q f n ω 4 / J.finiteSampleRawFive q f n ω 0 ^ 2 =
      (n : ℝ) * ∫ z, BayesGibbs.populationProduct q f z
        ∂(J.temperedPosterior n ω).prod (J.temperedPosterior n ω) := by
    change (R.halfRadialScale n ^ 2 *
      J.pairWeightedPartition (BayesGibbs.populationProduct q f) n ω) /
          (S * J.normalizedEvidence n ω) ^ 2 = _
    rw [hQscale, hcancel₂, J.integral_temperedPosterior_prod_eq_ratio hW hφ hφi]
  have hcent : J.weightedPartition (fun w ↦ Real.sqrt n * (K w - J.Kn n ω w)) n ω =
      Real.sqrt n * J.weightedPartition (fun w ↦ K w - J.Kn n ω w) n ω := by
    unfold weightedPartition
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall fun w ↦ by ring
  have hH : J.finiteSampleRawFive q f n ω 2 / J.finiteSampleRawFive q f n ω 0 =
      (n : ℝ) * (∫ w, K w ∂J.temperedPosterior n ω) -
        (n : ℝ) * ∫ w, J.Kn n ω w ∂J.temperedPosterior n ω := by
    change (R.halfRadialScale n *
      J.weightedPartition (fun w ↦ Real.sqrt n * (K w - J.Kn n ω w)) n ω) /
        (S * J.normalizedEvidence n ω) = _
    rw [hcent, ← mul_assoc, hHscale, hcancel,
      ← J.integral_temperedPosterior_eq_ratio hW hφ hφi, integral_sub hKi hKni]
    ring
  ext j
  fin_cases j <;>
    simp only [GaussianPosterior.normalizeRaw, hT, hH, hD, hQ,
      BayesGibbs.populationPosteriorFive, BayesGibbs.populationSecondMoment,
      BayesGibbs.populationProduct, Matrix.cons_val_zero, Matrix.cons_val_succ] <;> ring

end SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput
