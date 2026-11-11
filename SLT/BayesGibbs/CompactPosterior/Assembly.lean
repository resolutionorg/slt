/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CompactPosterior.Ratios
public import SLT.BayesGibbs.CompactPosterior.Expectations
public import SLT.MeasureTheory.Function.AsympUnifIntegrable
public import SLT.BayesGibbs.Covariance.Kernel
import SLT.BayesGibbs.CompactPosterior.RatioProbability

/-!
# Assembly of the posterior observables

The limiting laws, expectations and identities of the observable vector
`Y_n = (n BG_n, n BT_n, n GG_n, n GT_n, V_n)`, from approximation and asymptotic uniform
integrability hypotheses on it, which the transport, Taylor and moment arguments establish.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.GaussianPosterior

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K] (ρ : Measure K) [IsFiniteMeasure ρ]
  {β lam : ℝ}

private theorem compactFive_telescoping (C : PSDKernel K) (g : C(K, ℝ)) :
    compactFive ρ β lam C g 0 - compactFive ρ β lam C g 1 -
      compactFive ρ β lam C g 2 + compactFive ρ β lam C g 3 = 0 := by
  let T := compactM2 β lam ρ g
  let H := compactH β lam ρ g
  let V := compactV ρ β lam C g
  change (T - V / 2) - (T - H - V / 2) - T + (T - H) = 0
  ring

private theorem compactFive_gibbs_sum (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (C : PSDKernel K) (g : C(K, ℝ)) :
    compactFive ρ β lam C g 2 + compactFive ρ β lam C g 3 = 2 * lam / β := by
  have h := two_mul_compactM2_sub_compactH ρ hβ hlam hρ g
  change compactM2 β lam ρ g + (compactM2 β lam ρ g - compactH β lam ρ g) = _
  linarith

private theorem compactFive_variance_generalization (C : PSDKernel K) (g : C(K, ℝ)) :
    compactFive ρ β lam C g 4 -
      2 * (compactFive ρ β lam C g 2 - compactFive ρ β lam C g 0) = 0 := by
  let T := compactM2 β lam ρ g
  let V := compactV ρ β lam C g
  change V - 2 * (T - (T - V / 2)) = 0
  ring

private theorem compactFive_variance_training (C : PSDKernel K) (g : C(K, ℝ)) :
    compactFive ρ β lam C g 4 -
      2 * (compactFive ρ β lam C g 3 - compactFive ρ β lam C g 1) = 0 := by
  let T := compactM2 β lam ρ g
  let H := compactH β lam ρ g
  let V := compactV ρ β lam C g
  change V - 2 * ((T - H) - (T - H - V / 2)) = 0
  ring

section Probability
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {g : ℕ → Ω → C(K, ℝ)} {g' : Ω' → C(K, ℝ)}

/-- The exact common-field residuals imply every in-probability equation in the
Bayes/Gibbs statements of `SLTChallenge`. No Gaussian assumption is needed here. -/
private theorem compactFive_probability_identities
    (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (C : PSDKernel K)
    (Y : ℕ → Ω → Fin 5 → ℝ)
    (ha : ∀ j, TendstoInMeasure P
      (fun n ω ↦ Y n ω j - compactFive ρ β lam C (g n ω) j) atTop 0) :
    TendstoInMeasure P (fun n ω ↦ Y n ω 0 - Y n ω 1 - Y n ω 2 + Y n ω 3) atTop 0 ∧
    TendstoInMeasure P (fun n ω ↦ Y n ω 2 + Y n ω 3 - 2 * lam / β) atTop 0 ∧
    TendstoInMeasure P (fun n ω ↦ Y n ω 4 - 2 * (Y n ω 2 - Y n ω 0)) atTop 0 ∧
    TendstoInMeasure P (fun n ω ↦ Y n ω 4 - 2 * (Y n ω 3 - Y n ω 1)) atTop 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert tendstoInMeasure_add_zero
      (tendstoInMeasure_sub_zero (tendstoInMeasure_sub_zero (ha 0) (ha 1)) (ha 2)) (ha 3) using 1
    funext n ω
    have h := compactFive_telescoping ρ (β := β) (lam := lam) C (g n ω)
    linarith
  · convert tendstoInMeasure_add_zero (ha 2) (ha 3) using 1
    funext n ω
    have h := compactFive_gibbs_sum ρ hβ hlam hρ C (g n ω)
    linarith
  · convert tendstoInMeasure_sub_zero (ha 4)
      (tendstoInMeasure_const_mul_zero 2 (tendstoInMeasure_sub_zero (ha 2) (ha 0))) using 1
    funext n ω
    have h := compactFive_variance_generalization ρ (β := β) (lam := lam) C (g n ω)
    linarith
  · convert tendstoInMeasure_sub_zero (ha 4)
      (tendstoInMeasure_const_mul_zero 2 (tendstoInMeasure_sub_zero (ha 3) (ha 1))) using 1
    funext n ω
    have h := compactFive_variance_training ρ (β := β) (lam := lam) C (g n ω)
    linarith

/-- Joint law, eventual integrability, and expectation convergence from the
finite-sample approximation and its AUI bound. -/
private theorem compactFive_convergence
    (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (C : PSDKernel K)
    (hg : TendstoInDistribution g atTop g' (fun _ ↦ P) P')
    (Y : ℕ → Ω → Fin 5 → ℝ) (hYm : ∀ n, AEMeasurable (Y n) P)
    (ha : ∀ j, TendstoInMeasure P
      (fun n ω ↦ Y n ω j - compactFive ρ β lam C (g n ω) j) atTop 0)
    (hAUI : ∀ j, AsympUnifIntegrable P (fun n ω ↦ Y n ω j)) :
    TendstoInDistribution Y atTop (fun ω ↦ compactFive ρ β lam C (g' ω)) (fun _ ↦ P) P' ∧
    (∀ j, Integrable (fun ω ↦ compactFive ρ β lam C (g' ω) j) P') ∧
    (∀ j, ∀ᶠ n in atTop, Integrable (fun ω ↦ Y n ω j) P) ∧
    (∀ j, Tendsto (fun n ↦ ∫ ω, Y n ω j ∂P) atTop
      (𝓝 (∫ ω, compactFive ρ β lam C (g' ω) j ∂P'))) := by
  have hbase := hg.continuous_comp (continuous_compactFive ρ hβ hlam hρ C)
  have herror : TendstoInMeasure P
      (Y - (fun n ω ↦ compactFive ρ β lam C (g n ω))) atTop 0 :=
    tendstoInMeasure_finite_pi_zero ha
  have hjoint := tendstoInDistribution_of_tendstoInMeasure_sub Y
    (fun ω ↦ compactFive ρ β lam C (g' ω)) hbase herror hYm
  have hc j := hjoint.continuous_comp (continuous_apply j)
  refine ⟨hjoint, fun j ↦ (hAUI j).integrable_limit (hc j), ?_, ?_⟩
  · intro j
    exact (hAUI j).eventually_integrable
      (fun n ↦ ((continuous_apply j).measurable.comp_aemeasurable (hYm n)).aestronglyMeasurable)
  · intro j
    exact (hAUI j).tendsto_integral (hc j)

end Probability
end SingularLearningTheory.GaussianPosterior

namespace SingularLearningTheory
open GaussianPosterior

/-- Expected limits, in the order BG, BT, GG, GT, V. -/
@[expose] noncomputable def bayesGibbsCoefficients (β lam ν : ℝ) : Fin 5 → ℝ :=
  ![lam / β + (1 - 1 / β) * ν, lam / β - (1 + 1 / β) * ν,
    lam / β + ν, lam / β - ν, 2 * ν / β]

variable {X Ω Ω' U : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace U] [CompactSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
  {q : Measure X} {f : X → U → ℝ} {Xs : ℕ → Ω → X}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- Final statistical assembly before specializing actual posterior observables.
All samplewise transport, Taylor, covariance LLN and AUI obligations remain visible.
The same supplied process determines every coordinate of the limit. -/
theorem EmpiricalProcessLimit.compactPosterior_assembly
    (E : EmpiricalProcessLimit q f Xs P P') (hE4 : E.MomentBound 4)
    (ρ : Measure U) [IsFiniteMeasure ρ] (hρ : ρ ≠ 0)
    {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam)
    (Y : ℕ → Ω → Fin 5 → ℝ) (hYm : ∀ n, AEMeasurable (Y n) P)
    (ha : ∀ j, TendstoInMeasure P (fun n ω ↦
      Y n ω j - compactFive ρ β lam (E.covarianceKernel hE4) (-E.Ψ n ω) j) atTop 0)
    (hAUI : ∀ j, AsympUnifIntegrable P (fun n ω ↦ Y n ω j)) :
    ∃ ν : ℝ, 0 ≤ ν ∧
      TendstoInDistribution Y atTop
        (fun ω ↦ compactFive ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω)) (fun _ ↦ P) P' ∧
      (∀ j, Integrable
        (fun ω ↦ compactFive ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω) j) P') ∧
      (∀ j, ∀ᶠ n in atTop, Integrable (fun ω ↦ Y n ω j) P) ∧
      (∀ j, Tendsto (fun n ↦ ∫ ω, Y n ω j ∂P) atTop
        (𝓝 (bayesGibbsCoefficients β lam ν j))) ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 0 - Y n ω 1 - Y n ω 2 + Y n ω 3) atTop 0 ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 2 + Y n ω 3 - 2 * lam / β) atTop 0 ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 4 - 2 * (Y n ω 2 - Y n ω 0)) atTop 0 ∧
      TendstoInMeasure P (fun n ω ↦ Y n ω 4 - 2 * (Y n ω 3 - Y n ω 1)) atTop 0 := by
  have hg : TendstoInDistribution (fun n ω ↦ -E.Ψ n ω) atTop
      (fun ω ↦ -E.Ψlim ω) (fun _ ↦ P) P' := E.tendsto.continuous_comp continuous_neg
  obtain ⟨hd, hi, hei, hm⟩ := compactFive_convergence ρ hβ hlam hρ
    (E.covarianceKernel hE4) hg Y hYm ha hAUI
  obtain ⟨ν, hν, hiV, hiQ, hEV, hEQ⟩ := E.expected_compactQuartet hE4 ρ hρ hβ hlam
  have hcoef : ∀ j : Fin 5,
      (∫ ω, compactFive ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω) j ∂P') =
        bayesGibbsCoefficients β lam ν j := by
    intro j
    fin_cases j
    · exact hEQ 0
    · exact hEQ 1
    · exact hEQ 2
    · exact hEQ 3
    · exact hEV
  refine ⟨ν, hν, hd, hi, hei, ?_, ?_⟩
  · intro j
    simpa only [hcoef j] using hm j
  · exact compactFive_probability_identities ρ hβ hlam hρ (E.covarianceKernel hE4) Y ha

/-- The two equations of state follow algebraically from the quartet coefficient
limits. Integrals of n times the error are rewritten exactly as n times integrals. -/
theorem BayesGibbs.equations_of_state_of_coefficient_limits
    {e : ℕ → Ω → Fin 4 → ℝ} {β lam ν : ℝ} (hβ : β ≠ 0)
    (hlim : ∀ j : Fin 4, Tendsto (fun n : ℕ ↦ ∫ ω, (n : ℝ) * e n ω j ∂P)
      atTop (𝓝 (![lam / β + (1 - 1 / β) * ν,
        lam / β - (1 + 1 / β) * ν, lam / β + ν, lam / β - ν] j))) :
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ((∫ ω, e n ω 0 ∂P) - (∫ ω, e n ω 1 ∂P) -
      2 * β * ((∫ ω, e n ω 3 ∂P) - (∫ ω, e n ω 1 ∂P)))) atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ ↦ (n : ℝ) * ((∫ ω, e n ω 2 ∂P) - (∫ ω, e n ω 3 ∂P) -
      2 * β * ((∫ ω, e n ω 3 ∂P) - (∫ ω, e n ω 1 ∂P)))) atTop (𝓝 0) := by
  have hcorr := ((hlim 3).sub (hlim 1)).const_mul (2 * β)
  constructor
  · convert ((hlim 0).sub (hlim 1)).sub hcorr using 1
    · funext n
      simp only [integral_const_mul]
      ring
    · congr 1
      change 0 = (lam / β + (1 - 1 / β) * ν) - (lam / β - (1 + 1 / β) * ν) -
        2 * β * ((lam / β - ν) - (lam / β - (1 + 1 / β) * ν))
      field_simp [hβ]
      ring
  · convert ((hlim 2).sub (hlim 3)).sub hcorr using 1
    · funext n
      simp only [integral_const_mul]
      ring
    · congr 1
      change 0 = (lam / β + ν) - (lam / β - ν) -
        2 * β * ((lam / β - ν) - (lam / β - (1 + 1 / β) * ν))
      field_simp [hβ]
      ring

end SingularLearningTheory
