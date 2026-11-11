/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Zeta.ChartIntegrand
public import SLT.SingularIntegrals.Zeta.Tail
public import SLT.SingularIntegrals.Zeta.Pole
import SLT.SingularIntegrals.DeterministicFreeEnergy
import SLT.SingularIntegrals.Resolution
import SLT.Analysis.Meromorphic.NormSandwich
public import SLT.Resolution.Atlas
public import SLT.SingularIntegrals.Transforms
public import Mathlib.Analysis.Meromorphic.Order

/-!
# Meromorphic continuation from a smooth resolution atlas

The local chart continuation is glued on the complex plane and the entire tail is
added back. Positivity in one essential chart fixes the leading pole and its order.
-/

public section

open MeasureTheory Set Finset Filter Topology
open scoped ContDiff

namespace SingularLearningTheory.ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (R : ResolutionAtlas K φ W)

/-- Smooth extensions of the chart weights give global continuation with the
learning coefficient and multiplicity as its first pole data. -/
theorem exists_zetaContinuation_of_smooth_weights
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hK : ∀ w ∈ W, 0 ≤ K w)
    (hφi : IntegrableOn φ W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hsm : ∀ α, ∃ g : (Fin d → ℝ) → ℝ, ContDiff ℝ ∞ g ∧
      EqOn g (R.weight α) (cube d (R.b α)))
    (hpos : ∃ α, R.IsEssential α ∧ 0 < R.weight α 0) :
    ∃ Z : ℂ → ℂ,
      (∀ z : ℂ, 0 < z.re → Z z = zetaFunction K φ W z) ∧
      MeromorphicOn Z univ ∧
      (∀ z : ℂ, meromorphicOrderAt Z z < 0 →
        z.im = 0 ∧ z.re < 0 ∧ ∃ q : ℚ, (q : ℝ) = z.re) ∧
      DifferentiableOn ℂ Z {z : ℂ | -R.rlct < z.re} ∧
      meromorphicOrderAt Z (-(R.rlct : ℂ)) = -(R.mult : ℤ) := by
  classical
  choose g hg hgw using hsm
  let gc : R.ι → (Fin d → ℝ) → ℂ := fun α u ↦ (g α u : ℂ)
  have hgc : ∀ α, ContDiff ℝ ∞ (gc α) := fun α ↦
    Complex.ofRealCLM.contDiff.comp (hg α)
  obtain ⟨F, hFm, hFd, hFeq⟩ := MellinAnalysis.exists_continuation_chartSum R.k R.h
    (fun α _ ↦ R.b α) (fun α _ ↦ R.b_pos α) gc hgc
  have hconv {z : ℂ} (hz : -R.rlct < z.re) :
      ∀ α j, -1 < (MellinAnalysis.chartExp (R.k α) (R.h α) z j).re := by
    intro α j
    rw [MellinAnalysis.chartExp_re]
    exact R.mellinExponent_gt_of_gt_rlct hz α j
  have hFlocal {z : ℂ} (hz : 0 < z.re) :
      F z = zetaFunction K (fun w ↦ R.χ w * φ w) W z := by
    rw [hFeq z (hconv ((neg_lt_zero.mpr R.rlct_pos).trans hz)),
      R.zeta_localized_eq_sum hW hKc hφi hφ hz]
    apply Finset.sum_congr rfl
    intro α _
    apply setIntegral_congr_fun measurableSet_Icc
    intro u hu
    dsimp only
    rw [show gc α u = (R.weight α u : ℂ) from congrArg Complex.ofReal (hgw α hu)]
  have hFreal {x : ℝ} (hx : -R.rlct < x) :
      F (x : ℂ) = ((∑ α, R.realChartMellin α x : ℝ) : ℂ) := by
    rw [hFeq (x : ℂ) (hconv hx), Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun α _ ↦
      R.remainderZeta_eq_ofReal_realChartMellin α
        (fun u hu ↦ congrArg Complex.ofReal (hgw α hu)) x
  have hForder := R.meromorphicOrderAt_chartSum_eq_neg_mult (hFm _ (mem_univ _))
    (fun x hx ↦ hFreal hx) hpos
  let T := zetaFunction K (fun w ↦ (1 - R.χ w) * φ w) W
  have hT : Differentiable ℂ T := R.zeta_tail_differentiable hW hKc hφi hφ
  have hZdiff : ∀ z ∉ MellinAnalysis.polesSet R.k R.h,
      DifferentiableAt ℂ (F + T) z := fun z hz ↦ (hFd z hz).add (hT z)
  have hZm : MeromorphicOn (F + T) univ := fun z hz ↦
    (hFm z hz).add (hT.analyticAt z).meromorphicAt
  refine ⟨F + T, ?_, hZm, fun z hz ↦
    R.pole_negative_rational_of_off_polesSet hZm hZdiff hz,
    R.differentiableOn_of_off_polesSet hZdiff,
    meromorphicOrderAt_add_analytic_of_eq_neg R.mult_pos
      (hT.analyticAt _) hForder⟩
  intro z hz
  change F z + T z = _
  rw [hFlocal hz]
  have hχφi : IntegrableOn (fun w ↦ R.χ w * φ w) W := by
    refine hφi.bdd_mul (c := 1) R.χ_measurable.aestronglyMeasurable ?_
    exact .of_forall fun w ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (R.χ_nonneg w)]
      exact R.χ_le_one w
  have hψi : IntegrableOn (fun w ↦ (1 - R.χ w) * φ w) W := by
    refine (hφi.sub hχφi).congr (.of_forall fun w ↦ ?_)
    change φ w - R.χ w * φ w = (1 - R.χ w) * φ w
    ring
  dsimp only [T, zetaFunction]
  rw [← integral_add (integrableOn_cpow_mul hW hKc hK hχφi hz)
    (integrableOn_cpow_mul hW hKc hK hψi hz)]
  apply integral_congr_ae
  exact .of_forall fun w ↦ by push_cast; ring

end SingularLearningTheory.ResolutionAtlas
