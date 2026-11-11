/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# Tonelli factorization of a coordinate product over a finite product measure

`∫⁻ x, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i)` for σ-finite factor measures and
measurable `ℝ≥0∞`-valued integrands. This is the lower (Tonelli) counterpart of Mathlib's Bochner
`integral_fin_nat_prod_eq_prod`; unlike the Bochner version it needs no integrability and
tolerates infinite integrals, which is what the product-density bridge (`ProductDensity`)
requires (a coordinate sublevel mass may be infinite on an unbounded box).

The proof mirrors the Bochner one: induct on `n`, peel coordinate `0` with the measure-preserving
equivalence `MeasurableEquiv.piFinSuccAbove`, and split the two factors with the binary Tonelli
identity `lintegral_prod_mul`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace SingularLearningTheory

/-- **Tonelli factorization over a finite product measure.** For σ-finite factor
measures `μ i` and measurable integrands `f i : E i → ℝ≥0∞`, the lower integral
of the coordinate product factorizes. -/
theorem _root_.lintegral_fin_nat_prod {n : ℕ} {E : Fin n → Type*}
    {mE : ∀ i, MeasurableSpace (E i)} {μ : (i : Fin n) → Measure (E i)}
    [∀ i, SigmaFinite (μ i)] {f : (i : Fin n) → E i → ℝ≥0∞}
    (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : (i : Fin n) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
      = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        ∫⁻ x : (i : Fin (n + 1)) → E i, ∏ i, f i (x i) ∂(Measure.pi μ)
            = ∫⁻ z : E 0 × ((i : Fin n) → E (Fin.succAbove 0 i)),
                f 0 z.1 * ∏ i : Fin n, f (Fin.succAbove 0 i) (z.2 i)
                ∂((μ 0).prod (Measure.pi (fun i => μ (Fin.succAbove 0 i)))) := by
              rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
                (MeasurableEquiv.measurableEmbedding _)]
              refine lintegral_congr fun a => ?_
              rw [Fin.prod_univ_succ]
              rfl
        _ = (∫⁻ x, f 0 x ∂μ 0)
              * ∏ i : Fin n, ∫⁻ x, f (Fin.succAbove 0 i) x ∂(μ (Fin.succAbove 0 i)) := by
            rw [← n_ih (fun i => hf (Fin.succAbove 0 i)),
              ← lintegral_prod_mul (f := f 0)
                (g := fun y : (i : Fin n) → E (Fin.succAbove 0 i) =>
                  ∏ i, f (Fin.succAbove 0 i) (y i)) (hf 0).aemeasurable
                (Finset.measurable_prod Finset.univ
                  (fun i _ => (hf (Fin.succAbove 0 i)).comp (measurable_pi_apply i))).aemeasurable]
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
            rw [Fin.prod_univ_succ]
            rfl

end SingularLearningTheory
