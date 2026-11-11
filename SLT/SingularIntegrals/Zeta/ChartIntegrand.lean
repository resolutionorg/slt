/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.Mellin.Remainder
public import SLT.SingularIntegrals.DeterministicFreeEnergy
public import SLT.Resolution.Atlas
public import SLT.SingularIntegrals.Transforms

/-!
# Complex powers in resolution charts

These lemmas put the atlas transport identity in the monomial Mellin form
used by the smooth continuation. The chart boundary is negligible, so the algebra
is performed where every coordinate is positive.
-/

public section

open MeasureTheory Set Finset Complex

namespace SingularLearningTheory

namespace MellinAnalysis

/-- Multiplication of positive monomials converts the zeta integrand to `u^(2kz+h)`. -/
private theorem monomial_cpow_mul {d : ℕ} (k h : Fin d → ℕ) {u : Fin d → ℝ}
    (hu : ∀ j, 0 < u j) (z : ℂ) :
    (((∏ j, u j ^ (2 * k j) : ℝ) : ℂ) ^ z) * ((∏ j, u j ^ (h j : ℝ) : ℝ) : ℂ)
      = ∏ j, (u j : ℂ) ^ chartExp k h z j := by
  have hprod : 0 < ∏ j, u j ^ (2 * k j) :=
    Finset.prod_pos fun j _ ↦ pow_pos (hu j) _
  have heq : (((∏ j, u j ^ (2 * k j) : ℝ) : ℂ) ^ z) =
      ∏ j, (u j : ℂ) ^ (2 * (k j : ℂ) * z) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hprod.ne'),
      ← Complex.ofReal_log hprod.le,
      Real.log_prod (fun j _ ↦ (pow_pos (hu j) _).ne')]
    simp_rw [Real.log_pow]
    push_cast
    rw [Finset.sum_mul, Complex.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (hu j).ne'),
      ← Complex.ofReal_log (hu j).le]
    congr 1
    ring
  rw [heq, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  rw [Complex.ofReal_cpow (hu j).le, ← Complex.cpow_add _ _
    (Complex.ofReal_ne_zero.mpr (hu j).ne')]
  rfl

end MellinAnalysis

/-- Positive real parts make the defining zeta integrand integrable against any
integrable prior on the compact domain. -/
theorem _root_.integrableOn_cpow_mul
    {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w)
    (hφi : IntegrableOn φ W) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun w ↦ (K w : ℂ) ^ z * (φ w : ℂ)) W := by
  classical
  let K' := W.piecewise K (fun _ ↦ 0)
  have hK'm : Measurable K' :=
    hKc.measurable_piecewise continuousOn_const hW.measurableSet
  obtain ⟨M, hM⟩ := hW.bddAbove_image hKc
  have hi : IntegrableOn (fun w ↦ (K' w : ℂ) ^ z * (φ w : ℂ)) W := by
    refine hφi.ofReal.bdd_mul (c := (max M 1) ^ z.re)
      (((Complex.measurable_ofReal.comp hK'm).pow_const z).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hW.measurableSet] with w hw
    dsimp only [K']
    rw [piecewise_eq_of_mem W K _ hw,
      Complex.norm_cpow_eq_rpow_re_of_nonneg (hK w hw) hz.ne']
    exact Real.rpow_le_rpow (hK w hw) ((hM ⟨w, hw, rfl⟩).trans (le_max_left _ _)) hz.le
  refine hi.congr ?_
  filter_upwards [ae_restrict_mem hW.measurableSet] with w hw
  simp only [K', piecewise_eq_of_mem W K _ hw]

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : ResolutionAtlas K φ W)

/-- The localized zeta integral is the finite sum of the chart Mellin integrals. -/
theorem zeta_localized_eq_sum (hW : IsCompact W) (hKc : ContinuousOn K W)
    (hφi : IntegrableOn φ W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    {z : ℂ} (hz : 0 < z.re) :
    zetaFunction K (fun w ↦ R.χ w * φ w) W z =
      ∑ α, MellinAnalysis.remainderZeta (R.k α) (R.h α) (fun _ ↦ R.b α)
        (fun u ↦ (R.weight α u : ℂ)) z := by
  classical
  let K' := W.piecewise K (fun _ ↦ 0)
  have hK'm : Measurable K' :=
    hKc.measurable_piecewise continuousOn_const hW.measurableSet
  have hKm (α : R.ι) (u : Fin d → ℝ) (hu : u ∈ cube d (R.b α)) :
      K' (R.g α u) = ∏ j, u j ^ (2 * R.k α j) := by
    dsimp only [K']
    rw [piecewise_eq_of_mem W K _ (R.g_mapsTo α hu), R.monomial α u hu]
  have hFb : ∀ α, ∃ C : ℝ, ∀ u ∈ cube d (R.b α), ‖(K' (R.g α u) : ℂ) ^ z‖ ≤ C := by
    intro α
    refine ⟨(R.b α ^ (2 * ∑ j, R.k α j)) ^ z.re, fun u hu ↦ ?_⟩
    rw [hKm α u hu, Complex.norm_cpow_eq_rpow_re_of_nonneg
      (Finset.prod_nonneg fun j _ ↦ Even.pow_nonneg (even_two_mul _) _) hz.ne']
    exact Real.rpow_le_rpow
      (Finset.prod_nonneg fun j _ ↦ Even.pow_nonneg (even_two_mul _) _)
      (prod_pow_le_of_mem_Icc (R.k α) fun j ↦ ⟨hu.1 j, hu.2 j⟩) hz.le
  have ht := (R.integral_smul_localized_eq_sum_of_bounded hW.measurableSet hφ hφi
    ((Complex.measurable_ofReal.comp hK'm).pow_const z).stronglyMeasurable hFb).2
  calc zetaFunction K (fun w ↦ R.χ w * φ w) W z
      = ∫ w in W, (R.χ w * φ w) • (K' w : ℂ) ^ z := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hW.measurableSet] with w hw
        simp only [K', piecewise_eq_of_mem W K _ hw, Complex.real_smul, mul_comm]
    _ = _ := ht.trans (Finset.sum_congr rfl fun α _ ↦ by
      apply integral_congr_ae
      filter_upwards [MellinAnalysis.ae_box_pos (fun _ ↦ R.b α)] with u hu
      have hum : u ∈ cube d (R.b α) := ⟨fun j ↦ (hu j).1.le, fun j ↦ (hu j).2⟩
      simp only [Function.comp_apply]
      rw [hKm α u hum, Complex.real_smul, Complex.ofReal_mul]
      rw [mul_comm, ← mul_assoc, MellinAnalysis.monomial_cpow_mul (R.k α) (R.h α)
        (fun j ↦ (hu j).1)] )

end ResolutionAtlas

end SingularLearningTheory
