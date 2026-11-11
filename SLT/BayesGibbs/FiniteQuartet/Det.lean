/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import SLT.BayesGibbs.RadialMoments
public import SLT.BayesGibbs.Gaussian.SteinVector
import SLT.FreeEnergy.Main
public import SLT.FreeEnergy.StochasticAsymptotics

/-!
# The finite quartet: denominators, ratios and derivatives

The denominator and posterior ratios of the finite quartet, their polynomial bounds and derivatives,
and the continuity of `quartetH`.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

theorem _root_.Real.sqrt_le_sqrt_add (a x : ℝ) (ha : 0 ≤ a) :
    Real.sqrt (a + x ^ 2 / 4) ≤ Real.sqrt a + |x| / 2 := by
  rw [Real.sqrt_le_left (by positivity)]
  have := Real.sq_sqrt ha
  nlinarith [Real.sqrt_nonneg a, abs_nonneg x, sq_abs x]

/-- The coordinate projection as a continuous linear map on `Fin m → ℝ`. -/
@[expose] def coordProj {m : ℕ} (i : Fin m) : (Fin m → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

@[simp] theorem coordProj_apply {m : ℕ} (i : Fin m) (v : Fin m → ℝ) : coordProj i v = v i := rfl

theorem hasFDerivAt_coord {m : ℕ} (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (fun v : Fin m → ℝ ↦ v i) (coordProj i) g := hasFDerivAt_apply i g

section Det

variable {m : ℕ} (β lam : ℝ) (ρ : Fin m → ℝ)

/-- The denominator `D(g) = ∑ ρ_i S_λ(g_i)`. -/
@[expose] noncomputable def quartetD (g : Fin m → ℝ) : ℝ := ∑ i, ρ i * frozenInner lam β (g i)

/-- The unnormalised first moments `N_i(g) = ρ_i S_{λ+1/2}(g_i)`. -/
@[expose] noncomputable def quartetN (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  ρ i * frozenInner (lam + 1 / 2) β (g i)

/-- The posterior weights `W_i(g) = ρ_i S_{λ+1/2}(g_i)/D(g)`. -/
@[expose] noncomputable def quartetW (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  quartetN β lam ρ i g / quartetD β lam ρ g

/-- The normalised second moments `R_i(g) = ρ_i S_{λ+1}(g_i)/D(g)`. -/
@[expose] noncomputable def quartetR (i : Fin m) (g : Fin m → ℝ) : ℝ :=
  ρ i * frozenInner (lam + 1) β (g i) / quartetD β lam ρ g

/-- The posterior second moment `M₂(g) = ∑ R_i(g)`. -/
@[expose] noncomputable def quartetM2 (g : Fin m → ℝ) : ℝ := ∑ i, quartetR β lam ρ i g

/-- The field–moment pairing `H(g) = ∑ g_i W_i(g)`. -/
@[expose] noncomputable def quartetH (g : Fin m → ℝ) : ℝ := ∑ i, g i * quartetW β lam ρ i g

/-- The bilocal quadratic form `∑_{ij} b_{ij} W_i W_j`. -/
@[expose] noncomputable def quartetQ (b : Matrix (Fin m) (Fin m) ℝ) (g : Fin m → ℝ) : ℝ :=
  ∑ i, ∑ j, b i j * quartetW β lam ρ i g * quartetW β lam ρ j g


/-- The partial derivative `∂_j W_i = β δ_{ij} R_i − β W_i W_j`. -/
@[expose] noncomputable def quartetW' (i j : Fin m) (g : Fin m → ℝ) : ℝ :=
  β * (if i = j then quartetR β lam ρ i g else 0) - β * quartetW β lam ρ i g * quartetW β lam ρ j g

variable {β lam} (hβ : 0 < β) (hlam : 0 < lam) {ρ} (hρ : ∀ i, 0 < ρ i) [Nonempty (Fin m)]
include hβ hlam hρ

theorem quartetD_pos (g : Fin m → ℝ) : 0 < quartetD β lam ρ g :=
  Finset.sum_pos (fun i _ ↦ mul_pos (hρ i) (frozenInner_pos hlam hβ (g i)))
    Finset.univ_nonempty

omit [Nonempty (Fin m)] in
private theorem single_le_quartetD (i : Fin m) (g : Fin m → ℝ) :
    ρ i * frozenInner lam β (g i) ≤ quartetD β lam ρ g :=
  Finset.single_le_sum (fun j _ ↦ (mul_pos (hρ j) (frozenInner_pos hlam hβ (g j))).le)
    (Finset.mem_univ i)

private theorem quartetW_nonneg (i : Fin m) (g : Fin m → ℝ) : 0 ≤ quartetW β lam ρ i g :=
  div_nonneg (mul_pos (hρ i) (frozenInner_pos (by linarith) hβ (g i))).le
    (quartetD_pos hβ hlam hρ g).le

private theorem quartetR_nonneg (i : Fin m) (g : Fin m → ℝ) : 0 ≤ quartetR β lam ρ i g :=
  div_nonneg (mul_pos (hρ i) (frozenInner_pos (by linarith) hβ (g i))).le
    (quartetD_pos hβ hlam hρ g).le

/-- **The Schwinger–Dyson identity**: `M₂(g) = λ/β + H(g)/2`. -/
private theorem quartetM2_eq (g : Fin m → ℝ) :
    quartetM2 β lam ρ g = lam / β + quartetH β lam ρ g / 2 := by
  have hD := quartetD_pos hβ hlam hρ g
  have hsum : ∑ i, ρ i * frozenInner (lam + 1) β (g i) =
      (∑ i, g i * (ρ i * frozenInner (lam + 1 / 2) β (g i))) / 2 +
        lam / β * quartetD β lam ρ g := by
    unfold quartetD
    rw [Finset.sum_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [fluctuation_recurrence β lam hβ hlam]; ring
  unfold quartetM2 quartetR quartetH quartetW quartetN
  rw [← Finset.sum_div, hsum]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp
  ring

/-! ### Polynomial bounds -/

private theorem quartetW_le (i : Fin m) (g : Fin m → ℝ) :
    quartetW β lam ρ i g ≤ Real.sqrt (2 * lam / β) + |g i| / 2 := by
  have hD := quartetD_pos hβ hlam hρ g
  have h0 := frozenInner_pos hlam hβ (g i)
  have hle := single_le_quartetD hβ hlam hρ i g
  have hhalf := fluctuation_half_le hβ hlam (g i)
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  unfold quartetW quartetN
  rw [div_le_iff₀ hD]
  calc ρ i * frozenInner (lam + 1 / 2) β (g i)
      ≤ ρ i * (Real.sqrt (2 * lam / β + max (g i) 0 ^ 2 / 4) * frozenInner lam β (g i)) :=
        mul_le_mul_of_nonneg_left hhalf (hρ i).le
    _ ≤ (Real.sqrt (2 * lam / β) + |g i| / 2) * (ρ i * frozenInner lam β (g i)) := by
        have h1 : Real.sqrt (2 * lam / β + max (g i) 0 ^ 2 / 4) ≤
            Real.sqrt (2 * lam / β) + |g i| / 2 := by
          refine (Real.sqrt_le_sqrt ?_).trans (sqrt_le_sqrt_add (2 * lam / β) (g i) hB)
          have : max (g i) 0 ^ 2 ≤ g i ^ 2 := by
            rcases le_total (g i) 0 with h | h
            · rw [max_eq_right h, zero_pow two_ne_zero]; positivity
            · rw [max_eq_left h]
          linarith
        nlinarith [mul_pos (hρ i) h0, Real.sqrt_nonneg (2 * lam / β), abs_nonneg (g i)]
    _ ≤ (Real.sqrt (2 * lam / β) + |g i| / 2) * quartetD β lam ρ g :=
        mul_le_mul_of_nonneg_left hle (add_nonneg (Real.sqrt_nonneg _) (by positivity))

private theorem quartetR_le (i : Fin m) (g : Fin m → ℝ) :
    quartetR β lam ρ i g ≤ 2 * lam / β + g i ^ 2 / 4 := by
  have hD := quartetD_pos hβ hlam hρ g
  have h0 := frozenInner_pos hlam hβ (g i)
  have hle := single_le_quartetD hβ hlam hρ i g
  have hsucc := fluctuation_succ_le hβ hlam (g i)
  have hmax : max (g i) 0 ^ 2 ≤ g i ^ 2 := by
    rcases le_total (g i) 0 with h | h
    · rw [max_eq_right h, zero_pow two_ne_zero]; positivity
    · rw [max_eq_left h]
  unfold quartetR
  rw [div_le_iff₀ hD]
  calc ρ i * frozenInner (lam + 1) β (g i)
      ≤ ρ i * ((2 * lam / β + max (g i) 0 ^ 2 / 4) * frozenInner lam β (g i)) :=
        mul_le_mul_of_nonneg_left hsucc (hρ i).le
    _ ≤ (2 * lam / β + g i ^ 2 / 4) * (ρ i * frozenInner lam β (g i)) := by
        nlinarith [mul_pos (hρ i) h0]
    _ ≤ (2 * lam / β + g i ^ 2 / 4) * quartetD β lam ρ g :=
        mul_le_mul_of_nonneg_left hle (add_nonneg (div_nonneg (by linarith) hβ.le) (by positivity))

theorem polyBoundedPi_quartetW (i : Fin m) : PolyBoundedPi (quartetW β lam ρ i) := by
  refine ⟨Real.sqrt (2 * lam / β) + 1 / 2, 1, fun g ↦ ?_⟩
  rw [abs_of_nonneg (quartetW_nonneg hβ hlam hρ i g), pow_one]
  have h1 := quartetW_le hβ hlam hρ i g
  have h2 : |g i| ≤ ‖g‖ := by
    have := norm_le_pi_norm g i; rwa [Real.norm_eq_abs] at this
  nlinarith [Real.sqrt_nonneg (2 * lam / β), norm_nonneg g]

theorem polyBoundedPi_quartetR (i : Fin m) : PolyBoundedPi (quartetR β lam ρ i) := by
  refine ⟨2 * lam / β + 1 / 4, 2, fun g ↦ ?_⟩
  rw [abs_of_nonneg (quartetR_nonneg hβ hlam hρ i g)]
  have h1 := quartetR_le hβ hlam hρ i g
  have h2 : |g i| ≤ ‖g‖ := by
    have := norm_le_pi_norm g i; rwa [Real.norm_eq_abs] at this
  have h3 : g i ^ 2 ≤ ‖g‖ ^ 2 := by rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  have hB : 0 ≤ 2 * lam / β := div_nonneg (by linarith) hβ.le
  nlinarith [norm_nonneg g]

private theorem polyBoundedPi_quartetM2 : PolyBoundedPi (quartetM2 β lam ρ) :=
  PolyBoundedPi.finset_sum _ fun i ↦ polyBoundedPi_quartetR hβ hlam hρ i

theorem polyBoundedPi_quartetW' (i j : Fin m) : PolyBoundedPi (quartetW' β lam ρ i j) := by
  unfold quartetW'
  refine PolyBoundedPi.sub ?_ ?_
  · by_cases h : i = j
    · simp only [h, ite_true]
      exact (polyBoundedPi_quartetR hβ hlam hρ j).const_mul β
    · simp only [h, ite_false, mul_zero]
      exact PolyBoundedPi.const 0
  · exact ((polyBoundedPi_quartetW hβ hlam hρ i).const_mul β).mul
      (polyBoundedPi_quartetW hβ hlam hρ j)

/-! ### Continuity and measurability -/

omit hρ [Nonempty (Fin m)] in
private theorem continuous_quartetD : Continuous (quartetD β lam ρ) := by
  unfold quartetD
  exact continuous_finsetSum _ fun i _ ↦
    continuous_const.mul ((continuous_frozenInner hlam hβ).comp (continuous_apply i))

theorem continuous_quartetW (i : Fin m) : Continuous (quartetW β lam ρ i) := by
  unfold quartetW quartetN
  exact (continuous_const.mul ((continuous_frozenInner (by linarith) hβ).comp
    (continuous_apply i))).div (continuous_quartetD hβ hlam)
    fun g ↦ (quartetD_pos hβ hlam hρ g).ne'

theorem continuous_quartetR (i : Fin m) : Continuous (quartetR β lam ρ i) := by
  unfold quartetR
  exact (continuous_const.mul ((continuous_frozenInner (by linarith) hβ).comp
    (continuous_apply i))).div (continuous_quartetD hβ hlam)
    fun g ↦ (quartetD_pos hβ hlam hρ g).ne'

theorem continuous_quartetW' (i j : Fin m) : Continuous (quartetW' β lam ρ i j) := by
  unfold quartetW'
  refine Continuous.sub (continuous_const.mul ?_)
    ((continuous_const.mul (continuous_quartetW hβ hlam hρ i)).mul
      (continuous_quartetW hβ hlam hρ j))
  by_cases h : i = j
  · simp only [h, ite_true]; exact continuous_quartetR hβ hlam hρ j
  · simp only [h, ite_false]; exact continuous_const

/-! ### Derivatives -/

omit hρ [Nonempty (Fin m)] in
/-- The derivative of the denominator. -/
private theorem hasFDerivAt_quartetD (g : Fin m → ℝ) :
    HasFDerivAt (quartetD β lam ρ)
      (∑ i, (ρ i * (β * frozenInner (lam + 1 / 2) β (g i))) • coordProj i :
        (Fin m → ℝ) →L[ℝ] ℝ) g := by
  unfold quartetD
  have hsum := HasFDerivAt.sum (u := Finset.univ)
    (A := fun i (y : Fin m → ℝ) ↦ ρ i * frozenInner lam β (y i))
    (A' := fun i ↦ (ρ i * (β * frozenInner (lam + 1 / 2) β (g i))) • coordProj i) (x := g)
    fun i _ ↦ by
      have h := ((hasDerivAt_fluctuation β lam hβ hlam (g i)).comp_hasFDerivAt g
        (hasFDerivAt_coord i g)).const_mul (ρ i)
      refine h.congr_fderiv ?_
      ext v; simp [mul_assoc]
  rw [Finset.sum_fn] at hsum
  exact hsum

omit hρ [Nonempty (Fin m)] in
private theorem hasFDerivAt_quartetN (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (quartetN β lam ρ i)
      ((ρ i * (β * frozenInner (lam + 1) β (g i))) • coordProj i : (Fin m → ℝ) →L[ℝ] ℝ) g := by
  unfold quartetN
  have h := ((hasDerivAt_fluctuation β (lam + 1 / 2) hβ (by linarith) (g i)).comp_hasFDerivAt g
    (hasFDerivAt_coord i g)).const_mul (ρ i)
  rw [show lam + 1 / 2 + 1 / 2 = lam + 1 by ring] at h
  refine h.congr_fderiv ?_
  ext v; simp [mul_assoc]

/-- **The derivative of the posterior weights**: `∂_j W_i = β δ_{ij} R_i − β W_i W_j`. -/
theorem hasFDerivAt_quartetW (i : Fin m) (g : Fin m → ℝ) :
    HasFDerivAt (quartetW β lam ρ i)
      (∑ j, quartetW' β lam ρ i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) g := by
  have hD := quartetD_pos hβ hlam hρ g
  have hN := hasFDerivAt_quartetN (ρ := ρ) hβ hlam i g
  have hDd := hasFDerivAt_quartetD (ρ := ρ) hβ hlam g
  have hinv := (hasDerivAt_inv hD.ne').comp_hasFDerivAt g hDd
  have h := hN.mul hinv
  have hfun : quartetW β lam ρ i =
      quartetN β lam ρ i * ((fun y : ℝ ↦ y⁻¹) ∘ quartetD β lam ρ) := by
    funext x; simp [quartetW, div_eq_mul_inv]
  rw [hfun]
  refine h.congr_fderiv ?_
  have hDne : quartetD β lam ρ g ≠ 0 := hD.ne'
  have hRHS : ∀ v : Fin m → ℝ,
      (∑ j, quartetW' β lam ρ i j g • coordProj j : (Fin m → ℝ) →L[ℝ] ℝ) v =
        β * quartetR β lam ρ i g * v i -
          β * quartetW β lam ρ i g * ∑ j, quartetW β lam ρ j g * v j := by
    intro v
    simp only [sum_apply, smul_apply, coordProj_apply, smul_eq_mul, quartetW', sub_mul,
      Finset.sum_sub_distrib, mul_ite, mul_zero, ite_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  ext v
  rw [hRHS]
  simp only [add_apply, smul_apply, sum_apply, coordProj_apply, smul_eq_mul, Function.comp_apply]
  have hDsum : ∑ j, ρ j * (β * frozenInner (lam + 1 / 2) β (g j)) * v j =
      β * ∑ j, quartetN β lam ρ j g * v j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ ↦ by unfold quartetN; ring
  have hWsum : ∑ j, quartetW β lam ρ j g * v j =
      (∑ j, quartetN β lam ρ j g * v j) / quartetD β lam ρ g := by
    unfold quartetW
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  rw [hDsum, hWsum]
  set T := ∑ j, quartetN β lam ρ j g * v j
  unfold quartetR quartetW quartetN
  field_simp
  ring

/-! ### `0 ≤ Q ≤ c M₂` -/

end Det

variable {m : ℕ} {β lam : ℝ} {ρ : Fin m → ℝ}

theorem continuous_quartetH (hβ : 0 < β) (hlam : 0 < lam) (hρ : ∀ i, 0 < ρ i)
    [Nonempty (Fin m)] : Continuous (quartetH β lam ρ) :=
  continuous_finsetSum _ fun i _ ↦ (continuous_apply i).mul (continuous_quartetW hβ hlam hρ i)


end SingularLearningTheory.GaussianPosterior
