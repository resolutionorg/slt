/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.MeasureTheory.Constructions.Pi
import SLT.MeasureTheory.Integral.Lebesgue.Pi
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The product-density bridge

A finite product of measures, each reweighted by a density, equals the product measure
reweighted by the product of the densities:
`Measure.pi (fun i => (μ i).withDensity (g i))
  = (Measure.pi μ).withDensity (fun u => ∏ i, g i (u i))`.
Proved by pinning both measures on coordinate boxes (`Measure.pi_eq`); the box equation
reduces, through `withDensity_apply` and the indicator-product identity, to the Tonelli
factorization `lintegral_fin_nat_prod`.

Instantiated at Lebesgue measure and the power densities `|x|^{h i}`, this identifies the
product of one-dimensional power-weighted Lebesgue measures with the joint Lebesgue measure
weighted by the product monomial density — the form the chart-local source read-off
(`ChartLocal`) uses.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

/-- **Product-density bridge (general form).** A finite product of measures, each
reweighted by a measurable density, equals the product measure reweighted by the
product of the densities. -/
theorem _root_.MeasureTheory.Measure.pi_withDensity {n : ℕ} {E : Fin n → Type*}
    [∀ i, MeasurableSpace (E i)] (μ : (i : Fin n) → Measure (E i))
    [∀ i, SigmaFinite (μ i)] (g : (i : Fin n) → E i → ℝ≥0∞)
    (hg : ∀ i, Measurable (g i))
    [∀ i, SigmaFinite ((μ i).withDensity (g i))] :
    (Measure.pi fun i => (μ i).withDensity (g i))
      = (Measure.pi μ).withDensity (fun u => ∏ i, g i (u i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs),
    ← lintegral_indicator (MeasurableSet.univ_pi hs)]
  have hind : ∀ u : (i : Fin n) → E i,
      (Set.univ.pi s).indicator (fun u => ∏ i, g i (u i)) u
        = ∏ i, (s i).indicator (g i) (u i) := by
    intro u
    by_cases hu : u ∈ Set.univ.pi s
    · rw [Set.indicator_of_mem hu]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [Set.indicator_of_mem (Set.mem_univ_pi.mp hu i)]
    · rw [Set.indicator_of_notMem hu]
      simp only [Set.mem_univ_pi, not_forall] at hu
      obtain ⟨j, hj⟩ := hu
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj (g j))).symm
  simp_rw [hind]
  rw [lintegral_fin_nat_prod (fun i => (hg i).indicator (hs i))]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [lintegral_indicator (hs i)]
  exact (withDensity_apply (g i) (hs i)).symm

/-- **Product-density bridge for power densities.** The product over coordinates
of one-dimensional Lebesgue measures, each reweighted by `|x|^{h i}`, equals the
joint Lebesgue measure on `Fin n → ℝ` reweighted by the product monomial density
`∏ i, |x_i|^{h i}`. -/
theorem _root_.MeasureTheory.Measure.pi_withDensity_abs_rpow {n : ℕ} (h : Fin n → ℝ) :
    (Measure.pi fun _i : Fin n => volume.withDensity fun x : ℝ => ENNReal.ofReal (|x| ^ h _i))
      = (volume : Measure (Fin n → ℝ)).withDensity
          fun u => ENNReal.ofReal (∏ i, |u i| ^ h i) := by
  have hg : ∀ i : Fin n, Measurable fun x : ℝ => ENNReal.ofReal (|x| ^ h i) := by
    intro i; fun_prop
  rw [Measure.pi_withDensity _ _ hg, volume_pi]
  refine withDensity_congr_ae (Filter.Eventually.of_forall fun u => ?_)
  change ∏ i, ENNReal.ofReal (|u i| ^ h i) = ENNReal.ofReal (∏ i, |u i| ^ h i)
  rw [ENNReal.ofReal_prod_of_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _]

end SingularLearningTheory
