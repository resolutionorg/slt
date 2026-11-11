/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.Meromorphic.NormSandwich
public import SLT.SingularIntegrals.Zeta.RealBounds
import SLT.SingularIntegrals.Resolution
public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.Analysis.CStarAlgebra.Classes
public import SLT.Analysis.Mellin.ChartSum

/-!
# The leading pole of a chart continuation

Real chart bounds identify the pole order, while the monomial candidate set gives
rationality, negativity and holomorphy to the right of the leading pole.
-/

public section

open MeasureTheory Set Finset Filter Topology

namespace SingularLearningTheory
namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
variable (R : ResolutionAtlas K φ W)

/-- On the real axis, a complex chart amplitude agreeing with the weight
has the real chart integral. No ambient measurability of the weight
is needed here: integral_complex_ofReal is an unconditional Bochner identity. -/
theorem remainderZeta_eq_ofReal_realChartMellin (α : R.ι)
    {g : (Fin d → ℝ) → ℂ}
    (hg : ∀ u ∈ cube d (R.b α), g u = (R.weight α u : ℂ)) (x : ℝ) :
    MellinAnalysis.remainderZeta (R.k α) (R.h α) (fun _ ↦ R.b α) g (x : ℂ) =
      (R.realChartMellin α x : ℂ) := by
  change (∫ u in cube d (R.b α),
    (∏ j, (u j : ℂ) ^ MellinAnalysis.chartExp (R.k α) (R.h α) (x : ℂ) j) * g u) = _
  calc _ = ∫ u in cube d (R.b α),
      (((∏ j, u j ^ R.mellinExponent α x j) * R.weight α u : ℝ) : ℂ) := by
        refine setIntegral_congr_fun measurableSet_Icc fun u hu ↦ ?_
        rw [hg u hu, Complex.ofReal_mul, Complex.ofReal_prod]
        congr 1
        refine Finset.prod_congr rfl fun j _ ↦ ?_
        have he : MellinAnalysis.chartExp (R.k α) (R.h α) (x : ℂ) j =
            (R.mellinExponent α x j : ℂ) := by
          simp only [MellinAnalysis.chartExp, mellinExponent]
          push_cast
          ring
        rw [he, ← Complex.ofReal_cpow (hu.1 j)]
    _ = (R.realChartMellin α x : ℂ) := integral_complex_ofReal

/-- Exact order for the localized continuation. It only needs one essential
chart whose weight is positive at the origin, as supplied by AtlasData. -/
theorem meromorphicOrderAt_chartSum_eq_neg_mult
    {F : ℂ → ℂ} (hF : MeromorphicAt F (-(R.rlct : ℂ)))
    (heq : ∀ x : ℝ, -R.rlct < x →
      F (x : ℂ) = ((∑ α, R.realChartMellin α x : ℝ) : ℂ))
    (hpos : ∃ α, R.IsEssential α ∧ 0 < R.weight α 0) :
    meromorphicOrderAt F (-(R.rlct : ℂ)) = -(R.mult : ℤ) := by
  obtain ⟨c, C, hc, hbound⟩ := R.exists_scaled_realChartMellin_sum_bounds hpos
  have hcast : ((-R.rlct : ℝ) : ℂ) = -(R.rlct : ℂ) := by simp
  rw [← hcast]
  apply meromorphicOrderAt_eq_neg_of_scaled_norm_sandwich
    (by simpa using hF) hc (C := C)
  filter_upwards [hbound, self_mem_nhdsWithin] with x hb hx
  change -R.rlct < x at hx
  have hs : 0 ≤ ∑ α, R.realChartMellin α x :=
    Finset.sum_nonneg fun α _ ↦ R.realChartMellin_nonneg α x
  have hp : 0 ≤ (x + R.rlct) ^ R.mult :=
    pow_nonneg (by linarith : 0 ≤ x + R.rlct) _
  have hn : ‖((x : ℂ) - ((-R.rlct : ℝ) : ℂ)) ^ R.mult * F (x : ℂ)‖ =
      (x + R.rlct) ^ R.mult * (∑ α, R.realChartMellin α x) := by
    rw [heq x hx]
    have he : ((x : ℂ) - ((-R.rlct : ℝ) : ℂ)) ^ R.mult *
        ((∑ α, R.realChartMellin α x : ℝ) : ℂ) =
        (((x + R.rlct) ^ R.mult * (∑ α, R.realChartMellin α x) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp hs)]
  simpa only [hn] using hb

/-- Every finite active atlas has an essential chart. -/
theorem exists_isEssential : ∃ α, R.IsEssential α := by
  classical
  obtain ⟨α, hα, hαeq⟩ := Finset.exists_mem_eq_sup'
    (ResolutionAtlas.minimalCharts_nonempty R) R.chartMult
  refine ⟨α, ⟨(Finset.mem_filter.mp hα).2, ?_⟩⟩
  rw [ResolutionAtlas.mult, hαeq]

/-- Rationality follows from the two attained finite minima. -/
theorem rlct_rational : ∃ q : ℚ, (q : ℝ) = R.rlct := by
  classical
  obtain ⟨α, -, hα⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty R.chartRlct
  obtain ⟨j, hj, hjEq⟩ := Finset.exists_mem_eq_inf'
    (ResolutionAtlas.activeSet_nonempty R α) (R.ratio α)
  refine ⟨((R.h α j : ℚ) + 1) / (2 * R.k α j), ?_⟩
  rw [ResolutionAtlas.rlct, hα, ResolutionAtlas.chartRlct_eq_inf', hjEq, ResolutionAtlas.ratio]
  push_cast
  rfl

/-- The pole lattice lies to the left of the RLCT. -/
theorem polesSet_re_le_neg_rlct :
    ∀ z ∈ MellinAnalysis.polesSet R.k R.h, z.re ≤ -R.rlct := by
  classical
  rintro z ⟨α, j, n, hk, rfl⟩
  rw [MellinAnalysis.chartPole_re]
  have hj : j ∈ R.activeSet α := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hk⟩
  have hr : R.chartRlct α ≤ R.ratio α j := Finset.inf'_le _ hj
  have hlam : R.rlct ≤ ((R.h α j : ℝ) + 1) / (2 * R.k α j) :=
    (R.rlct_le_chartRlct α).trans hr
  apply neg_le_neg
  refine hlam.trans (div_le_div_of_nonneg_right ?_ (by positivity))
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

/-- Holomorphy in the required first-pole half-plane comes from the candidate set. -/
theorem differentiableOn_of_off_polesSet {Z : ℂ → ℂ}
    (hd : ∀ z ∉ MellinAnalysis.polesSet R.k R.h, DifferentiableAt ℂ Z z) :
    DifferentiableOn ℂ Z {z : ℂ | -R.rlct < z.re} := by
  intro z hz
  apply (hd z ?_).differentiableWithinAt
  intro hP
  exact not_lt_of_ge (R.polesSet_re_le_neg_rlct z hP) hz

/-- Poles belong to the candidate set, hence are strictly negative real rationals.
Apply to the final continuation after adding the entire tail. -/
theorem pole_negative_rational_of_off_polesSet {Z : ℂ → ℂ}
    (hm : MeromorphicOn Z univ)
    (hd : ∀ z ∉ MellinAnalysis.polesSet R.k R.h, DifferentiableAt ℂ Z z)
    {z : ℂ} (hz : meromorphicOrderAt Z z < 0) :
    z.im = 0 ∧ z.re < 0 ∧ ∃ q : ℚ, (q : ℝ) = z.re := by
  have hP : z ∈ MellinAnalysis.polesSet R.k R.h := by
    by_contra hP
    have hnonneg :=
      ((hm z (mem_univ z)).analyticAt (hd z hP).continuousAt).meromorphicOrderAt_nonneg
    exact not_lt_of_ge hnonneg hz
  exact MellinAnalysis.polesSet_subset_negRat R.k R.h hP

end ResolutionAtlas
end SingularLearningTheory
