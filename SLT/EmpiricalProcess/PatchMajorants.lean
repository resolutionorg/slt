/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.Tightness

/-!
# Majorants of a random continuous function on a patch

No thesis counterpart as a named statement; this is the output of the proofs of
[Hit26, Lemma 4.2.4] and [Hit26, Lemma 4.2.8]
on one ball `B` of the finite cover: measurable random variables `S_n`, `R_n` with
`sup_B |Ψ_n| ≤ S_n`, `|Ψ_n(u) − Ψ_n(v)| ≤ R_n dist(u, v)` on `B`, and second moments bounded
uniformly in `n`. `SingularLearningTheory.EmpiricalProcess.isTightMeasureSet_of_patchMajorants`
(Tightness from a finite open cover)
consumes it.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {Ω U : Type*} [MeasurableSpace Ω] [PseudoMetricSpace U]

/-- Measurable majorants of `sup_B |Ψ_n|` and of the Lipschitz constant of `Ψ_n` on `B`, with
second moments bounded uniformly in `n` (the conclusions of [Wat09, Theorem 5.8] and of
[Hit26, Lemma 4.2.8] on one ball, for `s = 2`). -/
structure EmpiricalProcess.PatchMajorants (Ψ : ℕ → Ω → C(U, ℝ)) (P : Measure Ω) (B : Set U) where
  /-- The majorant $S_n$ of $\sup_B |\Psi_n|$. -/
  S : ℕ → Ω → ℝ≥0∞
  /-- The majorant $R_n$ of the Lipschitz constant of $\Psi_n$ on $B$. -/
  R : ℕ → Ω → ℝ≥0∞
  S_measurable : ∀ n, Measurable (S n)
  R_measurable : ∀ n, Measurable (R n)
  /-- The bound on the second moments $\int S_n^2\,dP$, uniform in $n$. -/
  CS : ℝ≥0∞
  /-- The bound on the second moments $\int R_n^2\,dP$, uniform in $n$. -/
  CR : ℝ≥0∞
  CS_ne_top : CS ≠ ⊤
  CR_ne_top : CR ≠ ⊤
  lintegral_S_sq_le : ∀ n, ∫⁻ ω, S n ω ^ 2 ∂P ≤ CS
  lintegral_R_sq_le : ∀ n, ∫⁻ ω, R n ω ^ 2 ∂P ≤ CR
  enorm_le : ∀ n, ∀ᵐ ω ∂P, ∀ u ∈ B, ‖Ψ n ω u‖ₑ ≤ S n ω
  protected enorm_sub_le : ∀ n, ∀ᵐ ω ∂P, ∀ u ∈ B, ∀ v ∈ B, ‖Ψ n ω u - Ψ n ω v‖ₑ ≤ R n ω * edist u v

end SingularLearningTheory
