/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Probability.CentralLimit
public import SLT.EmpiricalProcess.Convergence
public import SLT.EmpiricalProcess.Defs
import SLT.Probability.Distributions.Gaussian.Map
public import SLT.EmpiricalProcess.Borel

/-!
# The finite-dimensional distributions of the empirical process

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 4.2.9] (3), the CLT for `(ψ_n(w₁), …, ψ_n(w_M))` | |
| | `SingularLearningTheory.EmpiricalProcess.tendstoInDistribution_clm_finiteEval` |
| [Hit26, Theorem 4.2.9] (3), the limit's law from its marginals | |
| | `ProbabilityTheory.isGaussian_map_finiteEval_of_fdd`,
`ProbabilityTheory.integral_eval_eq_zero_of_fdd`, `ProbabilityTheory.covariance_eval_of_fdd` |

For a linear functional `L` on `ℝ^M`, `L(Ψ_n(u₁), …, Ψ_n(u_M))` is almost surely the centred
normalised sum of `h_L(x) = L(f(x, u₁), …, f(x, u_M))` along the sample, so the scalar CLT gives
its limit `N(0, Var_q h_L)`. A probability measure `μ` on `C(U, ℝ)` whose linear images
`(L ∘ π_u)_* μ` are all such Gaussians has Gaussian finite-dimensional distributions with mean
zero, and covariance given by polarisation of the variances.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

/-- A linear functional on `ℝ^M` in coordinates: `L(v) = Σ_j L(e_j) v_j`. -/
theorem _root_.ContinuousLinearMap.apply_eq_sum_mul {M : ℕ} (L : (Fin M → ℝ) →L[ℝ] ℝ)
    (v : Fin M → ℝ) : L v = ∑ j, L (Pi.single j 1) * v j := by
  conv_lhs => rw [← Finset.univ_sum_single v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  have : Pi.single j (v j) = v j • (Pi.single j (1 : ℝ) : Fin M → ℝ) := by
    ext k
    by_cases h : k = j <;> simp [Pi.single_apply, h]
  rw [this, map_smul, smul_eq_mul, mul_comm]

variable {X U : Type*} (f : X → U → ℝ)

/-- `h_L(x) = L(f(x, u₁), …, f(x, u_M))`, the scalar integrand whose centred normalised sums are
`L(ψ_n(u₁), …, ψ_n(u_M))`. -/
@[expose] noncomputable def EmpiricalProcess.linearCombination {M : ℕ} (u : Fin M → U)
    (L : (Fin M → ℝ) →L[ℝ] ℝ) (x : X) :
    ℝ :=
  L fun j ↦ f x (u j)

variable {f}

private theorem linearCombination_eq_sum {M : ℕ} (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ) :
    EmpiricalProcess.linearCombination f u L = fun x ↦ ∑ j, L (Pi.single j 1) * f x (u j) :=
  funext fun x ↦ L.apply_eq_sum_mul fun j ↦ f x (u j)

theorem EmpiricalProcess.linearCombination_proj_zero (u u' : U) :
    EmpiricalProcess.linearCombination f ![u, u'] (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 ↦ ℝ) 0)
      = fun x ↦ f x u := rfl

theorem EmpiricalProcess.linearCombination_proj_one (u u' : U) :
    EmpiricalProcess.linearCombination f ![u, u'] (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 ↦ ℝ) 1)
      = fun x ↦ f x u' := rfl

theorem EmpiricalProcess.linearCombination_proj_add (u u' : U) :
    EmpiricalProcess.linearCombination f ![u, u'] (ContinuousLinearMap.proj (R := ℝ)
        (φ := fun _ : Fin 2 ↦ ℝ) 0
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) = fun x ↦ f x u + f x u' :=
  rfl

private theorem linearCombination_const_proj (u : U) :
    EmpiricalProcess.linearCombination f (fun _ : Fin 1 ↦ u)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0) = fun x ↦ f x u := rfl

section Integrals

variable [MeasurableSpace X] {q : Measure X} [IsProbabilityMeasure q]

omit [IsProbabilityMeasure q] in
private theorem measurable_linearCombination (hf_meas : ∀ u, Measurable fun x ↦ f x u) {M : ℕ}
    (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ) : Measurable (EmpiricalProcess.linearCombination f u
        L) :=
  L.continuous.measurable.comp (Measurable.of_eval fun j ↦ hf_meas (u j))

omit [IsProbabilityMeasure q] in
private theorem memLp_linearCombination (hL2 : ∀ u, MemLp (fun x ↦ f x u) 2 q) {M : ℕ}
    (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ) : MemLp (EmpiricalProcess.linearCombination f u L) 2
        q := by
  rw [linearCombination_eq_sum]
  exact memLp_finsetSum _ fun j _ ↦ (hL2 (u j)).const_mul _

private theorem integral_linearCombination (hL2 : ∀ u, MemLp (fun x ↦ f x u) 2 q) {M : ℕ}
    (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ) :
    ∫ x, EmpiricalProcess.linearCombination f u L x ∂q = L fun j ↦ ∫ x, f x (u j) ∂q := by
  rw [linearCombination_eq_sum, L.apply_eq_sum_mul,
    integral_finsetSum _ fun j _ ↦ ((hL2 (u j)).integrable one_le_two).const_mul _]
  simp_rw [integral_const_mul]

/-- `cov(f(·, u), f(·, u')) = (Var(f_u + f_{u'}) − Var f_u − Var f_{u'}) / 2`. -/
theorem _root_.ProbabilityTheory.covariance_eq_of_variances (hL2 : ∀ u, MemLp (fun x ↦ f x u) 2 q)
    (u u' : U) :
    cov[fun x ↦ f x u, fun x ↦ f x u'; q]
      = (Var[fun x ↦ f x u + f x u'; q] - Var[fun x ↦ f x u; q] - Var[fun x ↦ f x u'; q]) / 2 := by
  have := variance_add (hL2 u) (hL2 u')
  rw [show (fun x ↦ f x u + f x u') = (fun x ↦ f x u) + fun x ↦ f x u' from rfl, this]
  ring

end Integrals

variable {Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [TopologicalSpace U]
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]

/-- [Hit26, Theorem 4.2.9] (3), the CLT step: for `L` a linear functional
on `ℝ^M`, `L(Ψ_n(u₁), …, Ψ_n(u_M))` converges in distribution to `N(0, Var_q h_L)`. -/
theorem EmpiricalProcess.tendstoInDistribution_clm_finiteEval {Xs : ℕ → Ω → X}
    (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hind : iIndepFun Xs P)
    (hf_meas : ∀ u, Measurable fun x ↦ f x u) (hL2 : ∀ u, MemLp (fun x ↦ f x u) 2 q)
    {Ψ : ℕ → Ω → C(U, ℝ)} (hΨ : ∀ n, ∀ᵐ ω ∂P, ∀ u, Ψ n ω u = empiricalProcess q f Xs n ω u)
    {M : ℕ} (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ) :
    TendstoInDistribution (fun n ω ↦ L (ContinuousMap.finiteEval u (Ψ n ω))) atTop id (fun _ ↦ P)
      (gaussianReal 0 (Var[EmpiricalProcess.linearCombination f u L; q]).toNNReal) := by
  have key := tendstoInDistribution_empiricalSum hX hlaw hind
    (measurable_linearCombination hf_meas u L) (memLp_linearCombination hL2 u L)
  refine key.congr (fun n ↦ ?_) Filter.EventuallyEq.rfl
  filter_upwards [hΨ n] with ω hω
  have h1 : ContinuousMap.finiteEval u (Ψ n ω) = (√(n : ℝ))⁻¹ • ∑ l ∈ Finset.range n,
      ((fun j ↦ f (Xs l ω) (u j)) - fun j ↦ ∫ x, f x (u j) ∂q) := by
    ext j
    simp only [ContinuousMap.finiteEval, hω, empiricalProcess, Pi.smul_apply, Finset.sum_apply,
        Pi.sub_apply,
      smul_eq_mul]
  rw [h1, map_smul, map_sum, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl fun l _ ↦ ?_
  rw [map_sub, integral_linearCombination hL2]
  rfl

/-! ### The law of the limit from its one-dimensional marginals -/

section Fdd

variable {μ : Measure C(U, ℝ)} [IsProbabilityMeasure μ]
  {v : (M : ℕ) → (Fin M → U) → ((Fin M → ℝ) →L[ℝ] ℝ) → NNReal}

omit [IsProbabilityMeasure μ] in
/-- [Hit26, Theorem 4.2.9] (3): the finite-dimensional distributions of `μ`
are Gaussian when all their linear images are. -/
theorem _root_.ProbabilityTheory.isGaussian_map_finiteEval_of_fdd
    (hfdd : ∀ M u L, μ.map (fun h ↦ L (ContinuousMap.finiteEval u h)) = gaussianReal 0 (v M u L))
        (M : ℕ)
    (u : Fin M → U) : IsGaussian (μ.map fun h j ↦ h (u j)) :=
  isGaussian_of_map_eq_gaussianReal fun L ↦ ⟨0, v M u L, by
    change (μ.map (ContinuousMap.finiteEval u)).map L = _
    rw [Measure.map_map L.continuous.measurable (ContinuousMap.measurable_finiteEval u)]
    exact hfdd M u L⟩

omit [IsProbabilityMeasure μ] in
/-- The one-point marginal `h ↦ h(u)` of `μ`. -/
private theorem map_eval_eq_of_fdd
    (hfdd : ∀ M u L, μ.map (fun h ↦ L (ContinuousMap.finiteEval u h)) = gaussianReal 0 (v M u L))
        (u : U) :
    μ.map (fun h : C(U, ℝ) ↦ h u) = gaussianReal 0 (v 1 (fun _ ↦ u) (ContinuousLinearMap.proj 0)) :=
  hfdd 1 (fun _ ↦ u) (ContinuousLinearMap.proj 0)

omit [IsProbabilityMeasure μ] in
/-- Mean zero. -/
theorem _root_.ProbabilityTheory.integral_eval_eq_zero_of_fdd
    (hfdd : ∀ M u L, μ.map (fun h ↦ L (ContinuousMap.finiteEval u h)) = gaussianReal 0 (v M u L))
        (u : U) :
    ∫ h, h u ∂μ = 0 :=
  (memLp_two_and_integral_eq_zero_of_map_eq_gaussianReal (continuous_eval_const u).measurable
    (map_eval_eq_of_fdd hfdd u)).2.1

/-- The covariance of two evaluations, by polarisation of the three variances. -/
theorem _root_.ProbabilityTheory.covariance_eval_of_fdd
    (hfdd : ∀ M u L, μ.map (fun h ↦ L (ContinuousMap.finiteEval u h)) = gaussianReal 0 (v M u L))
        (u u' : U) :
    cov[fun h ↦ h u, fun h ↦ h u'; μ]
      = ((v 2 ![u, u'] (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0
            + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1) : ℝ)
          - v 2 ![u, u'] (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0)
          - v 2 ![u, u'] (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1)) / 2 :=
  by
  have hAB := hfdd 2 ![u, u'] (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0
    + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1)
  rw [show (fun h : C(U, ℝ) ↦ (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 0
      + ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 ↦ ℝ) 1)
          (ContinuousMap.finiteEval ![u, u'] h))
      = (fun h ↦ h u) + fun h ↦ h u' from funext fun h ↦ by simp [ContinuousMap.finiteEval]] at hAB
  exact covariance_eq_of_map_eq_gaussianReal (continuous_eval_const u).measurable
    (continuous_eval_const u').measurable (hfdd 2 ![u, u'] (ContinuousLinearMap.proj 0))
    (hfdd 2 ![u, u'] (ContinuousLinearMap.proj 1)) hAB

end Fdd

end SingularLearningTheory
