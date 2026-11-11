/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import SLT.StandardForm.Defs
public import SLT.Setting.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Tactic.NormNum

/-!
# Fundamental condition I

Facts about `FundamentalConditionI` (`SLT/StandardForm/Defs.lean`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace SingularLearningTheory

variable {d : ℕ}

variable {X : Type*} [MeasurableSpace X]

/-- Under fundamental condition I, `f(·, w)` lies in `L^s(q)` for every `w ∈ W`. -/
theorem FundamentalConditionI.memLp {s : ℝ≥0∞} [Fact (1 ≤ s)] {q : Measure X}
    {f : X → (Fin d → ℝ) → ℝ} {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
    (I : FundamentalConditionI s q f K W) {w : Fin d → ℝ} (hw : w ∈ W) :
    MemLp (fun x ↦ f x w) s q := by
  obtain ⟨U, -, hWU, F, -, hFf⟩ := I.ls_analytic
  exact (Lp.memLp (F w)).ae_eq (hFf w (hWU hw))

end SingularLearningTheory
