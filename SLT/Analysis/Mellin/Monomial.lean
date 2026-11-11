/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Monomial Mellin integrals on rectangular boxes

The elementary inputs for smooth chart continuation.
-/

public section

open MeasureTheory Set Finset Complex
open scoped ENNReal

namespace SingularLearningTheory.MellinAnalysis

variable {d : ℕ}

/-- Exponent of one coordinate in a monomial Mellin integral. -/
@[expose] def chartExp (k h : Fin d → ℕ) (z : ℂ) (p : Fin d) : ℂ := 2 * (k p : ℂ) * z + (h p : ℂ)

theorem chartExp_re (k h : Fin d → ℕ) (z : ℂ) (p : Fin d) :
    (chartExp k h z p).re = 2 * k p * z.re + h p := by
  simp [chartExp]

/-- Candidate pole after `j` integrations by parts in coordinate `p`. -/
@[expose] noncomputable def chartPole (k h : Fin d → ℕ) (p : Fin d) (j : ℕ) : ℂ :=
  -((((h p : ℝ) + j + 1) / (2 * k p) : ℝ) : ℂ)

/-- `u ↦ ∏ₚ uₚ^{eₚ}` is integrable on the box when `Re eₚ > −1` for all `p`. -/
theorem _root_.integrableOn_box_cpow (b : Fin d → ℝ) (e : Fin d → ℂ) (he : ∀ p, -1 < (e p).re) :
    IntegrableOn (fun u : Fin d → ℝ ↦ ∏ p, (u p : ℂ) ^ e p) (Icc 0 b) := by
  have h1 : ∀ p, IntegrableOn (fun x : ℝ ↦ (x : ℂ) ^ e p) (Icc (0 : ℝ) (b p)) := fun p ↦ by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegral.intervalIntegrable_cpow' (he p)).1.mono_set fun x hx ↦ by
      simpa using hx
  unfold IntegrableOn
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (E := ℝ) (μ := fun p ↦ volume.restrict (Icc (0 : ℝ) (b p)))
    (f := fun p (x : ℝ) ↦ (x : ℂ) ^ e p) h1

end SingularLearningTheory.MellinAnalysis
