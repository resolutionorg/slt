/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Atlas
public import SLT.SingularIntegrals.NormalCrossing

/-!
# Orthants, the signed square map, and the change of variables on one ramified chart

[Hit26, Section 3.3.1], the step "each
orthant is analytically isomorphic to `[0, b)^d`", combined with the substitution `v_j = w_j²`
that makes every exponent even ([Hit26]'s remark after
[Hit26, Theorem 3.3.1]). A chart cube of the atlas is
`w ↦ Γ (ε ⊙ w²)` on `[0, √b]^d`, for a monomialising coordinate map `Γ` on the box `[-b, b]^d`
and a sign vector `ε ∈ {±1}^d`; this file provides the signed square map, its derivative and
Jacobian, its injectivity on the open positive cube, and the change-of-variables formula for
one such chart (`lintegral_image_orthantSq`).

| Thesis | Lean |
| --- | --- |
| [Hit26, Section 3.3.1], orthants | `orthantSq` |
| [Hit26, Equation (3.3.5)], one chart | `lintegral_image_orthantSq` |
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {d : ℕ}

/-- The sign vector `ε ∈ {±1}^d` of an orthant, indexed by `Fin d → Bool`. -/
@[expose] def orthantSign (b : Fin d → Bool) (j : Fin d) : ℝ := if b j then 1 else -1

theorem orthantSign_sq (b : Fin d → Bool) (j : Fin d) : orthantSign b j ^ 2 = 1 := by
  unfold orthantSign; split_ifs <;> norm_num

theorem abs_orthantSign (b : Fin d → Bool) (j : Fin d) : |orthantSign b j| = 1 := by
  unfold orthantSign; split_ifs <;> simp

theorem orthantSign_ne_zero (b : Fin d → Bool) (j : Fin d) : orthantSign b j ≠ 0 := by
  unfold orthantSign; split_ifs <;> norm_num

/-- The signed square map `w ↦ (ε_j w_j²)_j` of the orthant `ε`. -/
@[expose] def orthantSq (b : Fin d → Bool)
    (w : Fin d → ℝ) : Fin d → ℝ := fun j ↦ orthantSign b j * w j ^ 2

/-- The derivative of `orthantSq b` at `w`: the diagonal map `v ↦ (2 ε_j w_j v_j)_j`. -/
@[expose] noncomputable def orthantSqDeriv (b : Fin d → Bool) (w : Fin d → ℝ) :
    (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.pi fun j ↦ (2 * orthantSign b j * w j) • ContinuousLinearMap.proj j

theorem hasFDerivAt_orthantSq (b : Fin d → Bool) (w : Fin d → ℝ) :
    HasFDerivAt (orthantSq b) (orthantSqDeriv b w) w := by
  refine hasFDerivAt_pi.mpr fun j ↦ ?_
  have h : HasFDerivAt (fun w : Fin d → ℝ ↦ w j ^ 2)
      ((2 * w j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j) w := by
    have := (hasFDerivAt_apply (𝕜 := ℝ) j w).pow 2
    simpa [Nat.cast_ofNat] using this
  have h2 := h.const_mul (orthantSign b j)
  have hd : orthantSign b j • (2 * w j) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j
      = (2 * orthantSign b j * w j) • ContinuousLinearMap.proj j := by
    rw [smul_smul]
    congr 1
    ring
  exact h2.congr_fderiv hd

theorem analyticOnNhd_orthantSq (b : Fin d → Bool) : AnalyticOnNhd ℝ (orthantSq b) univ := by
  intro w _
  refine analyticAt_pi_iff.mpr fun j ↦ ?_
  exact analyticAt_const.mul
    (((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).analyticAt _).pow 2)

/-- The Jacobian determinant of the signed square map is `∏ 2 ε_j w_j`. -/
private theorem det_orthantSqDeriv (b : Fin d → Bool) (w : Fin d → ℝ) :
    (orthantSqDeriv b w).det = ∏ j, 2 * orthantSign b j * w j := by
  classical
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix', ← Matrix.det_diagonal]
  congr 1
  ext i j
  simp only [LinearMap.toMatrix'_apply, orthantSqDeriv, ContinuousLinearMap.coe_coe,
    ContinuousLinearMap.pi_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply, Matrix.diagonal_apply, Pi.single_apply]
  split_ifs with h <;> simp [h]

theorem abs_det_orthantSqDeriv (b : Fin d → Bool) {w : Fin d → ℝ} (hw : ∀ j, 0 ≤ w j) :
    |(orthantSqDeriv b w).det| = ∏ j, 2 * w j := by
  rw [det_orthantSqDeriv, Finset.abs_prod]
  refine Finset.prod_congr rfl fun j _ ↦ ?_
  rw [abs_mul, abs_mul, abs_orthantSign, abs_of_nonneg (hw j)]
  norm_num

/-- The signed square map is injective on the open positive cube. -/
theorem orthantSq_injOn (b : Fin d → Bool) (c : ℝ) : InjOn (orthantSq b) (ocube d c) := by
  intro w hw w' hw' h
  funext j
  have hj := congrFun h j
  simp only [orthantSq] at hj
  have h0 : 0 < w j := (hw j (mem_univ j)).1
  have h0' : 0 < w' j := (hw' j (mem_univ j)).1
  have := mul_left_cancel₀ (orthantSign_ne_zero b j) hj
  exact (pow_left_inj₀ h0.le h0'.le two_ne_zero).mp this

/-- **Change of variables on one ramified chart.** For `Γ` differentiable and injective on the
image of the open positive cube `(0, c)^d` under the signed square map, and any
`F : ℝ^d → ℝ≥0∞`,
`∫_{Γ(ε ⊙ (0,c)²)} F = ∫_{(0,c)^d} |det Γ'(ε ⊙ w²)| (∏ 2 w_j) F(Γ(ε ⊙ w²)) dw`. -/
theorem lintegral_image_orthantSq {b : Fin d → Bool} {c : ℝ}
    {Γ : (Fin d → ℝ) → (Fin d → ℝ)} {Γ' : (Fin d → ℝ) → (Fin d → ℝ) →L[ℝ] (Fin d → ℝ)}
    (hΓ : ∀ v ∈ orthantSq b '' ocube d c, HasFDerivAt Γ (Γ' v) v)
    (hinj : InjOn Γ (orthantSq b '' ocube d c)) (F : (Fin d → ℝ) → ℝ≥0∞) :
    ∫⁻ x in (Γ ∘ orthantSq b) '' ocube d c, F x
      = ∫⁻ w in ocube d c,
          ENNReal.ofReal (|(Γ' (orthantSq b w)).det| * ∏ j, 2 * w j) * F (Γ (orthantSq b w)) := by
  have hs : MeasurableSet (ocube d c) := MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioo
  have hderiv : ∀ w ∈ ocube d c, HasFDerivWithinAt (Γ ∘ orthantSq b)
      ((Γ' (orthantSq b w)).comp (orthantSqDeriv b w)) (ocube d c) w := fun w hw ↦
    ((hΓ _ (mem_image_of_mem _ hw)).comp w (hasFDerivAt_orthantSq b w)).hasFDerivWithinAt
  have hinj' : InjOn (Γ ∘ orthantSq b) (ocube d c) :=
    hinj.comp (orthantSq_injOn b c) (mapsTo_image _ _)
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hderiv hinj' F]
  refine setLIntegral_congr_fun hs fun w hw ↦ ?_
  have hw0 : ∀ j, 0 ≤ w j := fun j ↦ (hw j (mem_univ j)).1.le
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp, LinearMap.det_comp, abs_mul,
    ← ContinuousLinearMap.det, ← ContinuousLinearMap.det, abs_det_orthantSqDeriv b hw0]
  rfl

end SingularLearningTheory
