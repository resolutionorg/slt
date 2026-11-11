/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import SLT.Probability.Distributions.Gaussian.Stein

/-!
# Stein's identity for Gaussian vectors

Stein's identity for a finite product of Gaussians and its linear images.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

/-- The law of `m` independent standard Gaussians. -/
@[expose] noncomputable def _root_.ProbabilityTheory.stdGaussianPi (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi fun _ : Fin m ↦ gaussianReal 0 1

@[expose] instance (m : ℕ) : IsProbabilityMeasure (stdGaussianPi m) := by
  unfold stdGaussianPi; infer_instance

/-- Polynomial growth on `Fin m → ℝ`: `|H z| ≤ C (1 + ‖z‖)^k`. -/
@[expose] def _root_.PolyBoundedPi {m : ℕ} (H : (Fin m → ℝ) → ℝ) : Prop :=
  ∃ (C : ℝ) (k : ℕ), ∀ z, |H z| ≤ C * (1 + ‖z‖) ^ k

end SingularLearningTheory.GaussianPosterior

namespace PolyBoundedPi

open SingularLearningTheory SingularLearningTheory.GaussianPosterior

variable {m : ℕ}

theorem const (c : ℝ) : PolyBoundedPi fun _ : Fin m → ℝ ↦ c := ⟨|c|, 0, fun z ↦ by simp⟩

theorem coord (i : Fin m) : PolyBoundedPi fun z : Fin m → ℝ ↦ z i :=
  ⟨1, 1, fun z ↦ by
    rw [one_mul, pow_one]
    have := norm_le_pi_norm z i
    rw [Real.norm_eq_abs] at this
    linarith⟩

theorem mul {F G : (Fin m → ℝ) → ℝ} (hF : PolyBoundedPi F) (hG : PolyBoundedPi G) :
    PolyBoundedPi fun z ↦ F z * G z := by
  obtain ⟨C, k, hC⟩ := hF
  obtain ⟨D, l, hD⟩ := hG
  refine ⟨C * D, k + l, fun z ↦ ?_⟩
  have hC0 : 0 ≤ C * (1 + ‖z‖) ^ k := (abs_nonneg _).trans (hC z)
  rw [abs_mul, pow_add]
  calc |F z| * |G z| ≤ (C * (1 + ‖z‖) ^ k) * (D * (1 + ‖z‖) ^ l) :=
        mul_le_mul (hC z) (hD z) (abs_nonneg _) hC0
    _ = C * D * ((1 + ‖z‖) ^ k * (1 + ‖z‖) ^ l) := by ring

private theorem add {F G : (Fin m → ℝ) → ℝ} (hF : PolyBoundedPi F) (hG : PolyBoundedPi G) :
    PolyBoundedPi fun z ↦ F z + G z := by
  obtain ⟨C, k, hC⟩ := hF
  obtain ⟨D, l, hD⟩ := hG
  refine ⟨C + D, k + l, fun z ↦ ?_⟩
  have h1 : 1 ≤ 1 + ‖z‖ := by linarith [norm_nonneg z]
  have hk : (1 + ‖z‖) ^ k ≤ (1 + ‖z‖) ^ (k + l) := pow_le_pow_right₀ h1 (by omega)
  have hl : (1 + ‖z‖) ^ l ≤ (1 + ‖z‖) ^ (k + l) := pow_le_pow_right₀ h1 (by omega)
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg (F 0)).trans (hC 0); simpa using this
  have hD0 : 0 ≤ D := by
    have := (abs_nonneg (G 0)).trans (hD 0); simpa using this
  calc |F z + G z| ≤ |F z| + |G z| := abs_add_le _ _
    _ ≤ C * (1 + ‖z‖) ^ k + D * (1 + ‖z‖) ^ l := add_le_add (hC z) (hD z)
    _ ≤ C * (1 + ‖z‖) ^ (k + l) + D * (1 + ‖z‖) ^ (k + l) :=
        add_le_add (mul_le_mul_of_nonneg_left hk hC0) (mul_le_mul_of_nonneg_left hl hD0)
    _ = (C + D) * (1 + ‖z‖) ^ (k + l) := by ring

theorem const_mul {F : (Fin m → ℝ) → ℝ} (hF : PolyBoundedPi F) (c : ℝ) :
    PolyBoundedPi fun z ↦ c * F z := (const c).mul hF

private theorem neg {F : (Fin m → ℝ) → ℝ} (hF : PolyBoundedPi F) : PolyBoundedPi fun z ↦ -F z := by
  obtain ⟨C, k, hC⟩ := hF
  exact ⟨C, k, fun z ↦ by rw [abs_neg]; exact hC z⟩

theorem sub {F G : (Fin m → ℝ) → ℝ} (hF : PolyBoundedPi F) (hG : PolyBoundedPi G) :
    PolyBoundedPi fun z ↦ F z - G z := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

theorem finset_sum {ι : Type*} (s : Finset ι) {F : ι → (Fin m → ℝ) → ℝ}
    (hF : ∀ i, PolyBoundedPi (F i)) : PolyBoundedPi fun z ↦ ∑ i ∈ s, F i z := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (0 : ℝ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hF a).add ih

/-- A polynomially bounded function of one coordinate, the others frozen, is polynomially
bounded in that coordinate. -/
private theorem slice {n : ℕ} {H : (Fin (n + 1) → ℝ) → ℝ} (hH : PolyBoundedPi H) (k : Fin (n + 1))
    (y : Fin n → ℝ) : PolyBounded fun t ↦ H (Fin.insertNth (α := fun _ ↦ ℝ) k t y) := by
  obtain ⟨C, l, hC⟩ := hH
  refine ⟨C * (1 + ‖y‖) ^ l, l, fun t ↦ ?_⟩
  have hnorm : ‖Fin.insertNth (α := fun _ ↦ ℝ) k t y‖ ≤ |t| + ‖y‖ := by
    rw [pi_norm_le_iff_of_nonneg (by positivity)]
    intro i
    refine Fin.succAboveCases k ?_ (fun j ↦ ?_) i
    · rw [Fin.insertNth_apply_same, Real.norm_eq_abs]; linarith [norm_nonneg y]
    · rw [Fin.insertNth_apply_succAbove]
      have := norm_le_pi_norm y j
      linarith [abs_nonneg t]
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg (H 0)).trans (hC 0); simpa using this
  calc |H (Fin.insertNth (α := fun _ ↦ ℝ) k t y)| ≤
        C * (1 + ‖Fin.insertNth (α := fun _ ↦ ℝ) k t y‖) ^ l := hC _
    _ ≤ C * ((1 + ‖y‖) * (1 + |t|)) ^ l := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ l) hC0
        nlinarith [norm_nonneg y, abs_nonneg t]
    _ = C * (1 + ‖y‖) ^ l * (1 + |t|) ^ l := by rw [mul_pow]; ring

end PolyBoundedPi

namespace ProbabilityTheory

/-! ### Polynomially bounded functions are integrable against the product Gaussian -/

section Integrable

variable {m : ℕ}

private theorem one_add_norm_le_prod (z : Fin m → ℝ) : 1 + ‖z‖ ≤ ∏ i, (1 + |z i|) := by
  rcases isEmpty_or_nonempty (Fin m) with h | h
  · simp [Subsingleton.elim z 0]
  · obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun i ↦ |z i|) Finset.univ_nonempty
    have hz : ‖z‖ ≤ |z i₀| := by
      rw [pi_norm_le_iff_of_nonneg (abs_nonneg _)]
      intro i; rw [Real.norm_eq_abs]; exact hi₀ i (Finset.mem_univ i)
    calc 1 + ‖z‖ ≤ 1 + |z i₀| := by linarith
      _ = ∏ i, (if i = i₀ then 1 + |z i₀| else 1) := by
          rw [Finset.prod_ite_eq' Finset.univ i₀ (fun _ ↦ 1 + |z i₀|)]
          simp
      _ ≤ ∏ i, (1 + |z i|) := by
          refine Finset.prod_le_prod₀ (fun i _ ↦ ?_) fun i _ ↦ ?_
          · split_ifs <;> positivity
          · split_ifs with h
            · subst h; exact le_rfl
            · linarith [abs_nonneg (z i)]

private theorem integrable_one_add_norm_pow (k : ℕ) :
    Integrable (fun z : Fin m → ℝ ↦ (1 + ‖z‖) ^ k) (stdGaussianPi m) := by
  have hprod : Integrable (fun z : Fin m → ℝ ↦ ∏ i, (1 + |z i|) ^ k) (stdGaussianPi m) :=
    Integrable.fintype_prod (f := fun _ t ↦ (1 + |t|) ^ k) fun i ↦ integrable_one_add_abs_pow 1 k
  refine hprod.mono' (by fun_prop) (Filter.Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), Finset.prod_pow]
  exact pow_le_pow_left₀ (by positivity) (one_add_norm_le_prod z) k

theorem integrable_of_polyBoundedPi {H : (Fin m → ℝ) → ℝ} (hHm : Measurable H)
    (hH : PolyBoundedPi H) : Integrable H (stdGaussianPi m) := by
  obtain ⟨C, k, hC⟩ := hH
  refine ((integrable_one_add_norm_pow k).const_mul C).mono' hHm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z ↦ ?_)
  rw [Real.norm_eq_abs]
  exact hC z

end Integrable

/-! ### The coordinate Stein identity -/

section Coordinate

variable {n : ℕ}

private theorem hasDerivAt_insertNth (k : Fin (n + 1)) (y : Fin n → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ Fin.insertNth (α := fun _ ↦ ℝ) k s y)
      (Pi.single k (1 : ℝ) : Fin (n + 1) → ℝ) t := by
  rw [hasDerivAt_pi]
  intro i
  refine Fin.succAboveCases k ?_ (fun j ↦ ?_) i
  · simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
    exact hasDerivAt_id t
  · simp only [Fin.insertNth_apply_succAbove, Pi.single_eq_of_ne (Fin.succAbove_ne k j)]
    exact hasDerivAt_const t _

/-- **The coordinate Stein identity** for independent standard Gaussians:
`E[Z_k H(Z)] = E[∂_k H(Z)]` for `C¹` `H` with `H` and `∂_k H` of polynomial growth. -/
private theorem stdGaussianPi_stein (k : Fin (n + 1)) {H : (Fin (n + 1) → ℝ) → ℝ}
    {H' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ} (hH : ∀ z, HasFDerivAt H (H' z) z)
    (hH'm : Measurable fun z ↦ H' z (Pi.single k 1)) (hHb : PolyBoundedPi H)
    (hH'b : PolyBoundedPi fun z ↦ H' z (Pi.single k 1)) :
    ∫ z, z k * H z ∂stdGaussianPi (n + 1) = ∫ z, H' z (Pi.single k 1) ∂stdGaussianPi (n + 1) := by
  have hHm : Measurable H :=
    (continuous_iff_continuousAt.2 fun z ↦ (hH z).continuousAt).measurable
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) k with he
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ gaussianReal 0 1) k
  have hsymm : ∀ p : ℝ × (Fin n → ℝ), e.symm p = Fin.insertNth (α := fun _ ↦ ℝ) k p.1 p.2 :=
    fun p ↦ rfl
  -- integrability of both integrands on the product
  have hint1 : Integrable (fun z ↦ z k * H z) (stdGaussianPi (n + 1)) :=
    integrable_of_polyBoundedPi ((measurable_pi_apply k).mul hHm) ((PolyBoundedPi.coord k).mul hHb)
  have hint2 : Integrable (fun z ↦ H' z (Pi.single k 1)) (stdGaussianPi (n + 1)) :=
    integrable_of_polyBoundedPi hH'm hH'b
  unfold stdGaussianPi at hint1 hint2 ⊢
  set ν := (gaussianReal 0 1).prod (Measure.pi fun _ : Fin n ↦ gaussianReal 0 1) with hν
  -- transport along `e`
  have htrans : ∀ G : (Fin (n + 1) → ℝ) → ℝ,
      ∫ z, G z ∂(Measure.pi fun _ : Fin (n + 1) ↦ gaussianReal 0 1) = ∫ p, G (e.symm p) ∂ν := by
    intro G
    rw [← hmp.integral_comp' (fun p ↦ G (e.symm p))]
    congr 1
    funext x
    exact (congrArg G (e.symm_apply_apply x)).symm
  have hintp : ∀ G : (Fin (n + 1) → ℝ) → ℝ,
      Integrable G (Measure.pi fun _ : Fin (n + 1) ↦ gaussianReal 0 1) →
      Integrable (fun p ↦ G (e.symm p)) ν := by
    intro G hG
    refine (hmp.integrable_comp_emb e.measurableEmbedding (g := fun p ↦ G (e.symm p))).1 ?_
    refine hG.congr (Filter.Eventually.of_forall fun x ↦ ?_)
    exact (congrArg G (e.symm_apply_apply x)).symm
  rw [htrans, htrans, integral_prod_symm _ (hintp _ hint1), integral_prod_symm _ (hintp _ hint2)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [hsymm]
  -- the scalar Stein identity in the `k`-th coordinate, `y` frozen
  have hderiv : ∀ t, HasDerivAt (fun s ↦ H (Fin.insertNth (α := fun _ ↦ ℝ) k s y))
      (H' (Fin.insertNth (α := fun _ ↦ ℝ) k t y) (Pi.single k 1)) t :=
    fun t ↦ (hH _).comp_hasDerivAt t (hasDerivAt_insertNth k y t)
  have hstein := gaussianReal_stein 1 one_ne_zero
    (F := fun s ↦ H (Fin.insertNth (α := fun _ ↦ ℝ) k s y))
    (F' := fun s ↦ H' (Fin.insertNth (α := fun _ ↦ ℝ) k s y) (Pi.single k 1)) hderiv
    (hH'm.comp (Measurable.of_eval fun i ↦ by
      refine Fin.succAboveCases k ?_ (fun j ↦ ?_) i
      · simp only [Fin.insertNth_apply_same]; exact measurable_id
      · simp only [Fin.insertNth_apply_succAbove]; exact measurable_const))
    (hHb.slice k y) (hH'b.slice k y)
  simp only [NNReal.coe_one, one_mul] at hstein
  simp only [Fin.insertNth_apply_same]
  exact hstein

end Coordinate

/-! ### Gaussian vectors `G = A Z` -/

section Vector

variable {n m : ℕ}

/-- The Gaussian vector `A Z` and its law. -/
@[expose] noncomputable def gaussianVector (A : Matrix (Fin m) (Fin (n + 1)) ℝ) : Measure
    (Fin m → ℝ) :=
  (stdGaussianPi (n + 1)).map A.mulVec

theorem _root_.Matrix.measurable_mulVec (A : Matrix (Fin m) (Fin (n + 1))
    ℝ) : Measurable A.mulVec :=
  (Matrix.mulVecLin A).continuous_of_finiteDimensional.measurable

@[expose] instance (A : Matrix (Fin m) (Fin (n + 1)) ℝ) : IsProbabilityMeasure (gaussianVector A) :=
  ⟨by rw [gaussianVector, Measure.map_apply (Matrix.measurable_mulVec A) MeasurableSet.univ,
    preimage_univ, measure_univ]⟩

theorem integral_gaussianVector (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (F : (Fin m → ℝ) → ℝ)
    (hF : Measurable F) :
    ∫ g, F g ∂gaussianVector A = ∫ z, F (A.mulVec z) ∂stdGaussianPi (n + 1) :=
  integral_map (Matrix.measurable_mulVec A).aemeasurable hF.aestronglyMeasurable

theorem _root_.PolyBoundedPi.comp_mulVec (A : Matrix (Fin m) (Fin (n + 1)) ℝ) {F : (Fin m → ℝ) → ℝ}
    (hF : PolyBoundedPi F) : PolyBoundedPi fun z ↦ F (A.mulVec z) := by
  obtain ⟨C, k, hC⟩ := hF
  set T := (Matrix.mulVecLin A).toContinuousLinearMap with hT
  set L := ‖T‖ with hLdef
  have hL : ∀ z, ‖A.mulVec z‖ ≤ L * ‖z‖ := fun z ↦ T.le_opNorm z
  have hL0 : 0 ≤ L := norm_nonneg _
  refine ⟨C * (1 + L) ^ k, k, fun z ↦ ?_⟩
  have hC0 : 0 ≤ C := by
    have := (abs_nonneg (F 0)).trans (hC 0); simpa using this
  calc |F (A.mulVec z)| ≤ C * (1 + ‖A.mulVec z‖) ^ k := hC _
    _ ≤ C * ((1 + L) * (1 + ‖z‖)) ^ k := by
        refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ k) hC0
        nlinarith [hL z, norm_nonneg z]
    _ = C * (1 + L) ^ k * (1 + ‖z‖) ^ k := by rw [mul_pow]; ring

/-- **The Gaussian-vector Stein identity**: for `G = A Z` with covariance `b = A Aᵀ`,
`E[G_i F(G)] = ∑_j b_{ij} E[∂_j F(G)]`. -/
theorem gaussianVector_stein (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (i : Fin m)
    {F : (Fin m → ℝ) → ℝ} {F' : (Fin m → ℝ) → (Fin m → ℝ) →L[ℝ] ℝ}
    (hF : ∀ g, HasFDerivAt F (F' g) g) (hF'm : ∀ j, Measurable fun g ↦ F' g (Pi.single j 1))
    (hFb : PolyBoundedPi F) (hF'b : ∀ j, PolyBoundedPi fun g ↦ F' g (Pi.single j 1)) :
    ∫ g, g i * F g ∂gaussianVector A =
      ∑ j, (A * A.transpose : Matrix (Fin m) (Fin m) ℝ) i j *
        ∫ g, F' g (Pi.single j 1) ∂gaussianVector A := by
  have hFm : Measurable F :=
    (continuous_iff_continuousAt.2 fun g ↦ (hF g).continuousAt).measurable
  rw [integral_gaussianVector A (fun g ↦ g i * F g) ((measurable_pi_apply i).mul hFm)]
  rw [Finset.sum_congr rfl fun j _ ↦ by
    rw [integral_gaussianVector A (fun g ↦ F' g (Pi.single j 1)) (hF'm j)]]
  -- `(A z)_i F(A z) = ∑_k A_{ik} z_k H(z)` with `H = F ∘ A`
  set H : (Fin (n + 1) → ℝ) → ℝ := fun z ↦ F (A.mulVec z) with hH
  have hHd : ∀ z,
      HasFDerivAt H ((F' (A.mulVec z)).comp (Matrix.mulVecLin A).toContinuousLinearMap) z :=
    fun z ↦ (hF _).comp z (Matrix.mulVecLin A).toContinuousLinearMap.hasFDerivAt
  have hHpoly : PolyBoundedPi H := PolyBoundedPi.comp_mulVec A hFb
  have hcoord : ∀ k : Fin (n + 1), (Matrix.mulVecLin A).toContinuousLinearMap (Pi.single k 1) =
      fun j ↦ A j k := by
    intro k; funext j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq']
  have hsingle : ∀ k : Fin (n + 1),
      (fun j : Fin m ↦ A j k) = ∑ j, A j k • Pi.single j (1 : ℝ) := by
    intro k; funext j'
    simp [Finset.sum_apply, Pi.single_apply]
  have hstein : ∀ k, ∫ z, z k * H z ∂stdGaussianPi (n + 1) =
      ∑ j, A j k * ∫ z, F' (A.mulVec z) (Pi.single j 1) ∂stdGaussianPi (n + 1) := by
    intro k
    have hH'k : ∀ z, ((F' (A.mulVec z)).comp (Matrix.mulVecLin A).toContinuousLinearMap)
        (Pi.single k 1) = ∑ j, A j k * F' (A.mulVec z) (Pi.single j 1) := by
      intro z
      rw [ContinuousLinearMap.comp_apply, hcoord k, hsingle k, map_sum]
      simp [map_smul, smul_eq_mul]
    have hm : Measurable fun z ↦ ∑ j, A j k * F' (A.mulVec z) (Pi.single j 1) :=
      Finset.measurable_sum _ fun j _ ↦ ((hF'm j).comp (Matrix.measurable_mulVec A)).const_mul _
    have hb : PolyBoundedPi fun z ↦ ∑ j, A j k * F' (A.mulVec z) (Pi.single j 1) :=
      PolyBoundedPi.finset_sum _ fun j ↦ (PolyBoundedPi.comp_mulVec A (hF'b j)).const_mul _
    have h := stdGaussianPi_stein k hHd (by simpa only [hH'k] using hm) hHpoly
      (by simpa only [hH'k] using hb)
    rw [h]
    simp_rw [hH'k]
    rw [integral_finsetSum _ fun j _ ↦ ?_]
    · simp_rw [integral_const_mul]
    · exact (integrable_of_polyBoundedPi ((hF'm j).comp (Matrix.measurable_mulVec A))
        (PolyBoundedPi.comp_mulVec A (hF'b j))).const_mul _
  have hexp : ∀ z, A.mulVec z i * F (A.mulVec z) = ∑ k, A i k * (z k * H z) := by
    intro z
    simp only [hH, Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  simp_rw [hexp]
  rw [integral_finsetSum _ fun k _ ↦ ?_]
  · simp_rw [integral_const_mul, hstein, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    ring
  · exact (integrable_of_polyBoundedPi ((measurable_pi_apply k).mul
      (hFm.comp (Matrix.measurable_mulVec A))) ((PolyBoundedPi.coord k).mul hHpoly)).const_mul _

end Vector

end ProbabilityTheory
