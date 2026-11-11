/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CompactPosterior.Identities
public import SLT.BayesGibbs.Covariance.Kernel

/-!
# Expected compact quartet at the limiting empirical process

`SingularLearningTheory.EmpiricalProcessLimit.expected_compactQuartet` computes the expectations of the
compact quartet and the compact functional variance at the limit $-\Psi$ of an empirical process
with bounded fourth moments, for a nonzero finite base measure $\rho$ and $\beta, \lambda > 0$.
There is a $\nu \ge 0$ with $E[V] = 2\nu/\beta$, and the expected Bayes generalization, Bayes
training, Gibbs generalization and Gibbs training limits are $\lambda/\beta + (1 - 1/\beta)\nu$,
$\lambda/\beta - (1 + 1/\beta)\nu$, $\lambda/\beta + \nu$ and $\lambda/\beta - \nu$. In
particular $E[B_g] - E[B_t] = \beta\,E[V]$ for the limits. The proof works with a Gaussian field
with the same covariance kernel that agrees with $-\Psi$ almost surely.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology

namespace SingularLearningTheory
open GaussianPosterior

variable {X Ω Ω' U : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  [MetricSpace U] [CompactSpace U] [Nonempty U] [MeasurableSpace U] [BorelSpace U]
  {q : Measure X} {f : X → U → ℝ} {Xs : ℕ → Ω → X}
  {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']

/-- The supplied limit has exactly the general-covariance compact quartet
coefficients. The Gaussian modification is only an internal a.e. representative. -/
theorem EmpiricalProcessLimit.expected_compactQuartet
    (E : EmpiricalProcessLimit q f Xs P P') (hE4 : E.MomentBound 4)
    (ρ : Measure U) [IsFiniteMeasure ρ] (hρ : ρ ≠ 0)
    {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) :
    ∃ ν : ℝ, 0 ≤ ν ∧
      Integrable (fun ω ↦ compactV ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω)) P' ∧
      (∀ j : Fin 4, Integrable (fun ω ↦ compactQuartet ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω) j) P') ∧
      (∫ ω, compactV ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω) ∂P') = 2 * ν / β ∧
      ∀ j : Fin 4, (∫ ω, compactQuartet ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω) j ∂P') =
        ![lam / β + (1 - 1 / β) * ν, lam / β - (1 + 1 / β) * ν,
          lam / β + ν, lam / β - ν] j := by
  obtain ⟨Γ, hΓ⟩ := E.exists_canonicalGaussianField hE4
  obtain ⟨ν, hν, hi, hEV, hEQ⟩ := Γ.expected_compactQuartet ρ hβ hlam hρ
  have hVeq : (fun ω ↦ compactV ρ β lam (E.covarianceKernel hE4) (Γ.G ω)) =ᵐ[P']
      fun ω ↦ compactV ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω) :=
    hΓ.mono fun ω hω ↦ congrArg (fun g : C(U, ℝ) ↦ compactV ρ β lam (E.covarianceKernel hE4) g) hω
  have hQeq : ∀ j : Fin 4,
      (fun ω ↦ compactQuartet ρ β lam (E.covarianceKernel hE4) (Γ.G ω) j) =ᵐ[P']
        fun ω ↦ compactQuartet ρ β lam (E.covarianceKernel hE4) (-E.Ψlim ω) j :=
    fun j ↦ hΓ.mono fun ω hω ↦ congrArg (fun g ↦ compactQuartet ρ β lam (E.covarianceKernel hE4) g j) hω
  refine ⟨ν, hν, (Γ.integrable_compactV ρ hβ hlam hρ).congr hVeq,
    fun j ↦ (hi j).congr (hQeq j), ?_, ?_⟩
  · exact (integral_congr_ae hVeq.symm).trans hEV
  · intro j
    exact (integral_congr_ae (hQeq j).symm).trans (hEQ j)

end SingularLearningTheory
