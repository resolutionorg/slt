/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CompactPosterior.Identities
public import SLT.BayesGibbs.CompactPosterior.RatioProbability

/-!
# Ratios of the compact posterior numerators

Raw input order: Z, T numerator, H numerator, covariance diagonal numerator, covariance pair
numerator. Output order: BG, BT, GG, GT, functional variance.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.GaussianPosterior

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
  [MeasurableSpace K] [BorelSpace K] (ρ : Measure K) [IsFiniteMeasure ρ]
  {β lam : ℝ}

/-- The five raw integrals of the limiting posterior on the compact space $K$ against $\rho$, at the
field $g$ and the kernel $C$: the evidence $\int S_\lambda(g)\,d\rho$, then the numerators
$\int S_{\lambda+1}(g)\,d\rho$, $\int g\,S_{\lambda+1/2}(g)\,d\rho$ and
$\int C(u, u)\,S_{\lambda+1}(g(u))\,d\rho(u)$, then the pair numerator
`SingularLearningTheory.GaussianPosterior.compactQnum`. Here $S_\lambda$ is
`SingularLearningTheory.frozenInner` at $\lambda$ and $\beta$. The three middle
entries are stored as ratios times the evidence, which equal these integrals when $\beta$ and
$\lambda$ are positive and $\rho \neq 0$
(`SingularLearningTheory.GaussianPosterior.compactRaw_first_numerator`). They are the compact
counterparts of the finite-sample integrals
`SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.finiteSampleRawFive`, in the same
order. -/
@[expose] noncomputable def compactRaw (β lam : ℝ) (C : PSDKernel K) (g : C(K, ℝ)) : Fin 5 → ℝ :=
  ![compactD β lam ρ g,
    compactM2 β lam ρ g * compactD β lam ρ g,
    compactH β lam ρ g * compactD β lam ρ g,
    compactDiag ρ β lam C g * compactD β lam ρ g,
    compactQnum ρ β lam C g]

/-- The five posterior observables of the limiting posterior on the compact space $K$, at the field
$g$ and the kernel $C$: the Bayes generalization, Bayes training, Gibbs generalization and Gibbs
training terms (the entries of `SingularLearningTheory.GaussianPosterior.compactQuartet`), then
the functional variance `SingularLearningTheory.GaussianPosterior.compactV`. When the evidence is
positive they are the ratios that `SingularLearningTheory.GaussianPosterior.normalizeRaw` forms
from `SingularLearningTheory.GaussianPosterior.compactRaw`. -/
@[expose] noncomputable def compactFive (β lam : ℝ) (C : PSDKernel K) (g : C(K, ℝ)) : Fin 5 → ℝ :=
  ![compactQuartet ρ β lam C g 0, compactQuartet ρ β lam C g 1,
    compactQuartet ρ β lam C g 2, compactQuartet ρ β lam C g 3,
    compactV ρ β lam C g]

/-- Algebraic posterior normalization, total even when the finite evidence vanishes. -/
@[expose] noncomputable def normalizeRaw (z : Fin 5 → ℝ) : Fin 5 → ℝ :=
  let T := z 1 / z 0
  let H := z 2 / z 0
  let V := z 3 / z 0 - z 4 / z 0 ^ 2
  ![T - V / 2, T - H - V / 2, T, T - H, V]

private theorem continuous_compactRaw (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (C : PSDKernel K) : Continuous (compactRaw ρ β lam C) := by
  have hD := continuous_compactD ρ hβ hlam
  have hT := (continuous_compactM2 ρ hβ hlam hρ).mul hD
  have hH := (continuous_compactH ρ hβ hlam hρ).mul hD
  have hC := (continuous_compactDiag ρ hβ hlam hρ C).mul hD
  have hQ := continuous_compactQnum ρ hβ hlam C
  apply continuous_pi
  intro j
  fin_cases j <;> simp only [compactRaw, Matrix.cons_val_zero, Matrix.cons_val_succ]
  all_goals assumption

theorem continuous_compactFive (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (C : PSDKernel K) : Continuous (compactFive ρ β lam C) := by
  have hF := continuous_compactQuartet ρ hβ hlam hρ C
  have hV := continuous_compactV ρ hβ hlam hρ C
  apply continuous_pi
  intro j
  fin_cases j
  · exact (continuous_apply (0 : Fin 4)).comp hF
  · exact (continuous_apply (1 : Fin 4)).comp hF
  · exact (continuous_apply (2 : Fin 4)).comp hF
  · exact (continuous_apply (3 : Fin 4)).comp hF
  · exact hV

/-- These three identities expose the raw weighted-integral interface. -/
theorem compactRaw_first_numerator (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (C : PSDKernel K) (g : C(K, ℝ)) : compactRaw ρ β lam C g 1 =
      ∫ u, frozenInner (lam + 1) β (g u) ∂ρ := by
  simp [compactRaw, compactM2, (compactD_pos ρ hβ hlam hρ g).ne']

theorem compactRaw_self_numerator (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (C : PSDKernel K) (g : C(K, ℝ)) : compactRaw ρ β lam C g 2 =
      ∫ u, g u * frozenInner (lam + 1 / 2) β (g u) ∂ρ := by
  simp [compactRaw, compactH, (compactD_pos ρ hβ hlam hρ g).ne']

theorem compactRaw_diag_numerator (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0)
    (C : PSDKernel K) (g : C(K, ℝ)) : compactRaw ρ β lam C g 3 =
      ∫ u, C.C u u * frozenInner (lam + 1) β (g u) ∂ρ := by
  simp [compactRaw, compactDiag, (compactD_pos ρ hβ hlam hρ g).ne']

section Probability
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  {g : ℕ → Ω → C(K, ℝ)} {g' : Ω' → C(K, ℝ)}

/-- The chart probability limits give these five scalar hypotheses; the divisions and the
connected covariance subtraction are carried out here. -/
theorem normalizedRaw_sub_compactFive_tendstoInMeasure
    (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (C : PSDKernel K)
    (hg : TendstoInDistribution g atTop g' (fun _ ↦ P) P')
    (v : ℕ → Ω → Fin 5 → ℝ) (hvm : ∀ n, AEMeasurable (v n) P)
    (hv : ∀ j, TendstoInMeasure P
      (fun n ω ↦ v n ω j - compactRaw ρ β lam C (g n ω) j) atTop 0) :
    ∀ j, TendstoInMeasure P
      (fun n ω ↦ normalizeRaw (v n ω) j - compactFive ρ β lam C (g n ω) j) atTop 0 := by
  have hL := continuous_compactRaw ρ hβ hlam hρ C
  have hpos : ∀ x, 0 < compactRaw ρ β lam C x 0 :=
    fun x ↦ compactD_pos ρ hβ hlam hρ x
  have hr i k := tendstoInMeasure_ratio_pow_sub hg hvm hL hv i 0 k hpos
  have hT : TendstoInMeasure P
      (fun n ω ↦ v n ω 1 / v n ω 0 - compactM2 β lam ρ (g n ω)) atTop 0 := by
    simpa [compactRaw, (compactD_pos ρ hβ hlam hρ _).ne'] using hr 1 1
  have hH : TendstoInMeasure P
      (fun n ω ↦ v n ω 2 / v n ω 0 - compactH β lam ρ (g n ω)) atTop 0 := by
    simpa [compactRaw, (compactD_pos ρ hβ hlam hρ _).ne'] using hr 2 1
  have hD : TendstoInMeasure P
      (fun n ω ↦ v n ω 3 / v n ω 0 - compactDiag ρ β lam C (g n ω)) atTop 0 := by
    simpa [compactRaw, (compactD_pos ρ hβ hlam hρ _).ne'] using hr 3 1
  have hQ : TendstoInMeasure P
      (fun n ω ↦ v n ω 4 / v n ω 0 ^ 2 - compactQ ρ β lam C (g n ω)) atTop 0 := by
    simpa [compactRaw, compactQ] using hr 4 2
  have hV := tendstoInMeasure_sub_zero hD hQ
  have hVhalf := tendstoInMeasure_const_mul_zero (1 / 2) hV
  intro j
  fin_cases j
  · convert tendstoInMeasure_sub_zero hT hVhalf using 1
    funext n ω
    simp [normalizeRaw, compactFive, compactQuartet, compactV]
    ring
  · convert tendstoInMeasure_sub_zero (tendstoInMeasure_sub_zero hT hH) hVhalf using 1
    funext n ω
    simp [normalizeRaw, compactFive, compactQuartet, compactV]
    ring
  · simpa [normalizeRaw, compactFive, compactQuartet] using hT
  · convert tendstoInMeasure_sub_zero hT hH using 1
    funext n ω
    simp [normalizeRaw, compactFive, compactQuartet]
    ring
  · convert hV using 1
    funext n ω
    simp [normalizeRaw, compactFive, compactV]
    ring

end Probability
end SingularLearningTheory.GaussianPosterior
