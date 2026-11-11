/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.VolumeScaling.Laplace.Asymptotic
public import SLT.VolumeScaling.LFoldProduct
public import SLT.VolumeScaling.Laplace.Scale
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Algebra.Order.Ring.Star
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The multiplicity correction for the product germ

For `K(x) = (∏ᵢ xᵢ)²` on the cube `[-1,1]^(L+1)` (learning coefficient `1/2`,
multiplicity `L+1`), the Gibbs mean `E_t[K]` obeys

  `t · E_t[K] = 1/2 − L / log t + o(1 / log t)`.

Integrating `∂ₐ (a · e^{−t a² c}) = e^{−t a² c} − 2 t a² c e^{−t a² c}` over the first
coordinate gives the exact identity `t · E_t[K] − 1/2 = −Z_L(t) / Z_{L+1}(t)`, where
`Z_n(t) = ∫_{[-1,1]^n} e^{−t (∏ xᵢ)²}`. The leading Laplace asymptotic
`Z_{m+1}(t) ~ (2/m!) Γ(3/2) t^{−1/2} (log t)^m` (from `hasLLCOn_prod_sq`) then gives
`log t · Z_L / Z_{L+1} → L`; for `L = 0`, `Z_0(t) = e^{−t}` is exponentially small.
-/

public section

open MeasureTheory Filter Topology Real Set SingularLearningTheory

namespace ProductGerm

/-- The partition function `Z_n(t) = ∫_{[-1,1]^n} e^{−t (∏ xᵢ)²}`. -/
private noncomputable def partition (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in Set.univ.pi (fun _ : Fin n ↦ Set.Icc (-1 : ℝ) 1), Real.exp (-t * (∏ i, x i) ^ 2)

/-- The unnormalized first moment `N_n(t) = ∫_{[-1,1]^n} (∏ xᵢ)² e^{−t (∏ xᵢ)²}`. -/
private noncomputable def moment (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x in Set.univ.pi (fun _ : Fin n ↦ Set.Icc (-1 : ℝ) 1),
    (∏ i, x i) ^ 2 * Real.exp (-t * (∏ i, x i) ^ 2)

/-- The Gibbs mean of `K(x) = (∏ i, x i)^2` at inverse temperature `t` under the uniform
measure on `[-1, 1]^(L+1)`. -/
@[expose] noncomputable def gibbsMean (L : ℕ) (t : ℝ) : ℝ :=
  (∫ x in Set.univ.pi (fun _ : Fin (L + 1) ↦ Set.Icc (-1 : ℝ) 1),
      (∏ i, x i) ^ 2 * Real.exp (-t * (∏ i, x i) ^ 2)) /
    (∫ x in Set.univ.pi (fun _ : Fin (L + 1) ↦ Set.Icc (-1 : ℝ) 1),
      Real.exp (-t * (∏ i, x i) ^ 2))

private theorem isCompact_cube (n : ℕ) : IsCompact (Set.univ.pi fun _ : Fin n ↦ Icc (-1 : ℝ) 1) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

/-- Peeling the first coordinate off the cube. -/
private theorem setIntegral_cube_succ (n : ℕ) {G : (Fin (n + 1) → ℝ) → ℝ} (hG : Continuous G) :
    ∫ x in Set.univ.pi (fun _ : Fin (n + 1) ↦ Icc (-1 : ℝ) 1), G x
      = ∫ y in Set.univ.pi (fun _ : Fin n ↦ Icc (-1 : ℝ) 1),
          ∫ a in Icc (-1 : ℝ) 1, G (Fin.cons a y) := by
  set μ : Fin (n + 1) → Measure ℝ := fun _ ↦ volume.restrict (Icc (-1) 1)
  have h1 : volume.restrict (Set.univ.pi fun _ : Fin (n + 1) ↦ Icc (-1 : ℝ) 1)
      = Measure.pi μ := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have h2 : volume.restrict (Set.univ.pi fun _ : Fin n ↦ Icc (-1 : ℝ) 1)
      = Measure.pi fun _ : Fin n ↦ volume.restrict (Icc (-1 : ℝ) 1) := by
    rw [volume_pi, Measure.restrict_pi_pi]
  have hInt : Integrable G (Measure.pi μ) := by
    rw [← h1]
    exact hG.continuousOn.integrableOn_compact (isCompact_cube _)
  have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
  rw [h1, h2, ← hmp.integral_comp' G, integral_prod_symm]
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply]
    rfl
  · exact (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).mpr hInt

/-- The one-dimensional integration by parts:
`∫_{-1}^{1} (2t (aP)² − 1) e^{−t (aP)²} da = −2 e^{−t P²}`. -/
private theorem integral_Icc_ibp (t P : ℝ) :
    ∫ a in Icc (-1 : ℝ) 1,
        (2 * t * ((a * P) ^ 2 * Real.exp (-t * (a * P) ^ 2)) - Real.exp (-t * (a * P) ^ 2))
      = -2 * Real.exp (-t * P ^ 2) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hderiv : ∀ a : ℝ, HasDerivAt (fun a ↦ -(a * Real.exp (-t * (a * P) ^ 2)))
      (2 * t * ((a * P) ^ 2 * Real.exp (-t * (a * P) ^ 2)) - Real.exp (-t * (a * P) ^ 2))
      a := by
    intro a
    have h := ((hasDerivAt_id' a).fun_mul
      ((((hasDerivAt_id' a).mul_const P).fun_pow 2).const_mul (-t)).exp).fun_neg
    refine h.congr_deriv ?_
    norm_num
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun a _ ↦ hderiv a)
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring_nf

/-- The exact identity `2t · N_{L+1}(t) = Z_{L+1}(t) − 2 Z_L(t)`, where `N` is the
unnormalized first moment of `K`. -/
private theorem two_mul_moment (L : ℕ) (t : ℝ) :
    2 * t * (∫ x in Set.univ.pi (fun _ : Fin (L + 1) ↦ Set.Icc (-1 : ℝ) 1),
        (∏ i, x i) ^ 2 * Real.exp (-t * (∏ i, x i) ^ 2))
      = partition (L + 1) t - 2 * partition L t := by
  set G : (Fin (L + 1) → ℝ) → ℝ := fun x ↦
    2 * t * ((∏ i, x i) ^ 2 * Real.exp (-t * (∏ i, x i) ^ 2))
      - Real.exp (-t * (∏ i, x i) ^ 2) with hG
  have hGc : Continuous G := by rw [hG]; fun_prop
  have hint : ∀ {F : (Fin (L + 1) → ℝ) → ℝ}, Continuous F →
      IntegrableOn F (Set.univ.pi fun _ : Fin (L + 1) ↦ Icc (-1 : ℝ) 1) :=
    fun hF ↦ hF.continuousOn.integrableOn_compact (isCompact_cube _)
  have hsplit : ∫ x in Set.univ.pi (fun _ : Fin (L + 1) ↦ Icc (-1 : ℝ) 1), G x
      = 2 * t * (∫ x in Set.univ.pi (fun _ : Fin (L + 1) ↦ Set.Icc (-1 : ℝ) 1),
          (∏ i, x i) ^ 2 * Real.exp (-t * (∏ i, x i) ^ 2)) - partition (L + 1) t := by
    rw [hG, integral_sub (hint (by fun_prop)) (hint (by fun_prop)), integral_const_mul]
    rfl
  have hpeel : ∫ x in Set.univ.pi (fun _ : Fin (L + 1) ↦ Icc (-1 : ℝ) 1), G x
      = -2 * partition L t := by
    rw [setIntegral_cube_succ L hGc, partition, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y ↦ ?_)
    simp only [hG, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    exact integral_Icc_ibp t _
  linarith

/-- The exact form of the correction: `t · E_t[K] − 1/2 = −Z_L(t) / Z_{L+1}(t)`. -/
private theorem mul_gibbsMean_sub_half (L : ℕ) {t : ℝ} (hZ : partition (L + 1) t ≠ 0) :
    t * gibbsMean L t - 1 / 2 = -(partition L t / partition (L + 1) t) := by
  have h := two_mul_moment L t
  rw [show gibbsMean L t = moment (L + 1) t / partition (L + 1) t from rfl]
  rw [show (∫ x in Set.univ.pi (fun _ : Fin (L + 1) ↦ Set.Icc (-1 : ℝ) 1),
      (∏ i, x i) ^ 2 * Real.exp (-t * (∏ i, x i) ^ 2)) = moment (L + 1) t from rfl] at h
  generalize moment (L + 1) t = N at h ⊢
  field_simp
  linarith

private theorem partition_zero (t : ℝ) : partition 0 t = Real.exp (-t) := by
  simp [partition, Measure.real]

/-- The leading Laplace asymptotic of `Z_{m+1}`, from the exact volume scaling. -/
private theorem partition_div_tendsto (m : ℕ) :
    Tendsto (fun s ↦ partition (m + 1) s / SingularLearningTheory.laplaceScale (1 / 2) ((m : ℝ) + 1)
        s) atTop
      (𝓝 (2 / m.factorial * Real.Gamma (1 / 2 + 1))) := by
  have hfin : volume (Set.univ.pi fun _ : Fin (m + 1) ↦ Icc (-1 : ℝ) 1) ≠ ⊤ :=
    (isCompact_cube _).measure_lt_top.ne
  have h := (hasLLCOn_prod_sq m).laplace_div_tendsto (by positivity)
    (Continuous.aemeasurable (by fun_prop)) (Eventually.of_forall fun _ ↦ sq_nonneg _) hfin
  refine h.congr fun s ↦ ?_
  simp only [partition, neg_mul]

private theorem log_mul_laplaceScale {lam theta s : ℝ} (hs : 1 < s) :
    Real.log s * SingularLearningTheory.laplaceScale lam theta s =
        SingularLearningTheory.laplaceScale lam (theta + 1) s := by
  unfold SingularLearningTheory.laplaceScale
  rw [show theta + 1 - 1 = (theta - 1) + 1 by ring, Real.rpow_add (Real.log_pos hs),
    Real.rpow_one]
  ring

/-- `Z_L / (t^{−1/2} (log t)^{L−1})` converges, to `0` for `L = 0`. -/
private theorem partition_div_tendsto' (L : ℕ) :
    Tendsto (fun s ↦ partition L s / SingularLearningTheory.laplaceScale (1 / 2) (L : ℝ) s) atTop
      (𝓝 (if L = 0 then 0 else 2 / (L - 1).factorial * Real.Gamma (1 / 2 + 1))) := by
  cases L with
  | zero =>
    simp only [partition_zero, ite_true]
    exact (SingularLearningTheory.tendsto_exp_neg_mul_div_laplaceScale (lam := 1 / 2) (theta := 0)
        one_pos).congr
      fun s ↦ by simp
  | succ m =>
    simpa using partition_div_tendsto m

/-- `log t · Z_L(t) / Z_{L+1}(t) → L`. -/
private theorem log_mul_partition_div_tendsto (L : ℕ) :
    Tendsto (fun s ↦ Real.log s * (partition L s / partition (L + 1) s)) atTop
      (𝓝 (L : ℝ)) := by
  have hc : (0 : ℝ) < 2 / L.factorial * Real.Gamma (1 / 2 + 1) := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2 + 1)
    positivity
  have h := (partition_div_tendsto' L).div (partition_div_tendsto L) hc.ne'
  have hval : (if L = 0 then 0 else 2 / (L - 1).factorial * Real.Gamma (1 / 2 + 1))
      / (2 / L.factorial * Real.Gamma (1 / 2 + 1)) = L := by
    rcases L with _ | k
    · simp
    · have hΓ := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2 + 1)
      simp only [Nat.add_one_ne_zero, ite_false, Nat.add_sub_cancel, Nat.factorial_succ,
        Nat.cast_mul]
      field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have h1 := SingularLearningTheory.laplaceScale_pos (lam := 1 / 2) (theta := (L : ℝ)) hs
  have h2 := log_mul_laplaceScale (lam := 1 / 2) (theta := (L : ℝ)) hs
  simp only [Pi.div_apply]
  rw [← h2]
  field_simp

private theorem eventually_partition_pos (L : ℕ) : ∀ᶠ s in atTop, 0 < partition (L + 1) s := by
  have hc : (0 : ℝ) < 2 / L.factorial * Real.Gamma (1 / 2 + 1) := by
    have := Real.Gamma_pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2 + 1)
    positivity
  filter_upwards [(partition_div_tendsto L).eventually (eventually_gt_nhds hc),
    eventually_gt_atTop (1 : ℝ)] with s hs hs1
  have := SingularLearningTheory.laplaceScale_pos (lam := 1 / 2) (theta := (L : ℝ) + 1) hs1
  exact (div_pos_iff_of_pos_right this).mp hs

/-- **The multiplicity correction**: `t · E_t[K] = 1/2 − L / log t + o(1 / log t)` for
`K = (∏ᵢ xᵢ)²` on `[-1,1]^(L+1)`. -/
private theorem gibbsMean_log_correction (L : ℕ) :
    Tendsto (fun t : ℝ ↦ Real.log t * (t * gibbsMean L t - 1 / 2)) atTop
      (𝓝 (-(L : ℝ))) := by
  refine (log_mul_partition_div_tendsto L).neg.congr' ?_
  filter_upwards [eventually_partition_pos L] with s hs
  rw [mul_gibbsMean_sub_half L hs.ne']
  ring

/-- **The learning coefficient**: `t · E_t[K] → 1/2` for `K = (∏ᵢ xᵢ)²` on `[-1,1]^(L+1)`. -/
theorem gibbsMean_tendsto_half (L : ℕ) :
    Tendsto (fun t : ℝ ↦ t * gibbsMean L t) atTop (𝓝 (1 / 2)) := by
  have h := ((gibbsMean_log_correction L).div_atTop Real.tendsto_log_atTop).const_add (1 / 2)
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with s hs
  have := (Real.log_pos hs).ne'
  field_simp
  ring

end ProductGerm
