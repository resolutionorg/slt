/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.SosIdeal
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen

/-!
# Entry ideals under invertible multiplication (LA3)

Aoyagi's Lemma 3 in the K2 layer: the entries of `Q·A·Q'` generate the
same local ideal on a compact `K` as the entries of `A`, when `Q, Q'`
are continuous and pointwise invertible on `K` — hence (K2) the same
family exponents. Containment is witnessed by the bilinear coefficient
matrices `Qᵤᵢ·Q'ⱼᵥ`; the reverse direction writes
`A = Q⁻¹·(QAQ')·Q'⁻¹` with inverse entries continuous via
determinant-and-adjugate.
-/

public section

open MeasureTheory Set

namespace SingularLearningTheory

variable {X : Type*}

/-- The entries of a matrix-valued function, as a finite family. -/
@[expose] def entryFamily {I J : Type*} (A : X → Matrix I J ℝ) :
    I × J → X → ℝ :=
  fun p x => A x p.1 p.2

section Forward

variable {I J I' J' : Type*} [Fintype I] [Fintype J]
  [Fintype I'] [Fintype J'] [TopologicalSpace X] {K : Set X}

omit [Fintype I'] [Fintype J'] in
/-- One-sided containment: the entries of `Q·A·Q'` lie in the entry
ideal of `A`, with the bilinear coefficients. -/
private theorem idealLEOn_entryFamily_mul (hK : IsCompact K)
    {A : X → Matrix I J ℝ} {Q : X → Matrix I' I ℝ}
    {Q' : X → Matrix J J' ℝ}
    (hQ : ContinuousOn Q K) (hQ' : ContinuousOn Q' K) :
    SingularLearningTheory.IdealLEOn K (entryFamily fun x => Q x * A x * Q' x)
      (entryFamily A) := by
  classical
  refine SingularLearningTheory.IdealLEOn.of_continuousCoeffs hK
    (a := fun p q x => Q x p.1 q.1 * Q' x q.2 p.2)
    (fun p q => ?_) (fun p x hx => ?_)
  · have hQe : Continuous fun M : Matrix I' I ℝ => M p.1 q.1 := by
      fun_prop
    have hQ'e : Continuous fun M : Matrix J J' ℝ => M q.2 p.2 := by
      fun_prop
    exact (hQe.comp_continuousOn hQ).mul (hQ'e.comp_continuousOn hQ')
  · show (Q x * A x * Q' x) p.1 p.2
      = ∑ q : I × J, Q x p.1 q.1 * Q' x q.2 p.2 * A x q.1 q.2
    calc (Q x * A x * Q' x) p.1 p.2
        = ∑ j, (∑ i, Q x p.1 i * A x i j) * Q' x j p.2 := by
          rw [Matrix.mul_apply]
          exact Finset.sum_congr rfl fun j _ => by
            rw [Matrix.mul_apply]
      _ = ∑ j, ∑ i, Q x p.1 i * Q' x j p.2 * A x i j := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, ∑ j, Q x p.1 i * Q' x j p.2 * A x i j :=
          Finset.sum_comm
      _ = ∑ q : I × J, Q x p.1 q.1 * Q' x q.2 p.2 * A x q.1 q.2 :=
          (Fintype.sum_prod_type
            (fun q : I × J =>
              Q x p.1 q.1 * Q' x q.2 p.2 * A x q.1 q.2)).symm

end Forward

section Equal

variable {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [TopologicalSpace X] {K : Set X}

/-- Inverse entries are continuous where the matrix is invertible. -/
private theorem continuousOn_matrix_inv {Q : X → Matrix I I ℝ}
    (hQ : ContinuousOn Q K) (hQu : ∀ x ∈ K, IsUnit (Q x)) :
    ContinuousOn (fun x => (Q x)⁻¹) K := by
  have hdet : ∀ x ∈ K, (Q x).det ≠ 0 := fun x hx =>
    ((Matrix.isUnit_iff_isUnit_det _).mp (hQu x hx)).ne_zero
  have h1 : ContinuousOn (fun x => Ring.inverse (Q x).det) K := by
    have h2 : ContinuousOn (fun x => (Q x).det) K :=
      (continuous_id.matrix_det).comp_continuousOn hQ
    refine ContinuousOn.congr (f := fun x => ((Q x).det)⁻¹)
      (h2.inv₀ hdet) fun x _ => ?_
    rw [Ring.inverse_eq_inv']
  have h3 : ContinuousOn (fun x => (Q x).adjugate) K :=
    (continuous_id.matrix_adjugate).comp_continuousOn hQ
  exact (h1.smul h3).congr fun x _ => by simp [Matrix.inv_def]

/-- **LA3 (Aoyagi Lemma 3)**: the entries of `Q·A·Q'` generate the same
local ideal on a compact `K` as the entries of `A`, for continuous
pointwise-invertible `Q, Q'`. -/
private theorem idealEqOn_entryFamily_mul (hK : IsCompact K)
    {A : X → Matrix I J ℝ} {Q : X → Matrix I I ℝ}
    {Q' : X → Matrix J J ℝ}
    (hQ : ContinuousOn Q K) (hQ' : ContinuousOn Q' K)
    (hQu : ∀ x ∈ K, IsUnit (Q x)) (hQ'u : ∀ x ∈ K, IsUnit (Q' x)) :
    SingularLearningTheory.IdealEqOn K (entryFamily fun x => Q x * A x * Q' x)
      (entryFamily A) := by
  constructor
  · exact idealLEOn_entryFamily_mul hK hQ hQ'
  · -- A = Q⁻¹ · (Q·A·Q') · Q'⁻¹ on K
    have hrep : ∀ x ∈ K, A x
        = (Q x)⁻¹ * (Q x * A x * Q' x) * (Q' x)⁻¹ := by
      intro x hx
      have h1 := (Matrix.isUnit_iff_isUnit_det _).mp (hQu x hx)
      have h2 := (Matrix.isUnit_iff_isUnit_det _).mp (hQ'u x hx)
      rw [Matrix.mul_assoc (Q x) (A x) (Q' x),
        ← Matrix.mul_assoc ((Q x)⁻¹) (Q x) (A x * Q' x),
        Matrix.nonsing_inv_mul _ h1, Matrix.one_mul,
        Matrix.mul_assoc (A x) (Q' x) ((Q' x)⁻¹),
        Matrix.mul_nonsing_inv _ h2, Matrix.mul_one]
    have hfwd := idealLEOn_entryFamily_mul hK
      (A := fun x => Q x * A x * Q' x)
      (Q := fun x => (Q x)⁻¹) (Q' := fun x => (Q' x)⁻¹)
      (continuousOn_matrix_inv hQ hQu)
      (continuousOn_matrix_inv hQ' hQ'u)
    -- transport the containment along the pointwise identity on K
    obtain ⟨a, hbdd, hrepr⟩ := hfwd
    refine ⟨a, hbdd, fun p x hx => ?_⟩
    have h := hrepr p x hx
    change A x p.1 p.2 = _
    rw [hrep x hx]
    exact h

end Equal

section Exponents

variable {I J : Type*} [Fintype I] [Fintype J]
  [DecidableEq I] [DecidableEq J] [TopologicalSpace X]
  [MeasurableSpace X] {μ : Measure X} {K : Set X}

/-- **LA3, exponent form**: invertible multiplication does not change
the family exponents of the entries. -/
theorem _root_.SingularLearningTheory.hasLLCExponentsFamilyOn_entry_mul_iff (hK : IsCompact K)
    {A : X → Matrix I J ℝ} {Q : X → Matrix I I ℝ}
    {Q' : X → Matrix J J ℝ}
    (hQ : ContinuousOn Q K) (hQ' : ContinuousOn Q' K)
    (hQu : ∀ x ∈ K, IsUnit (Q x)) (hQ'u : ∀ x ∈ K, IsUnit (Q' x))
    {lam theta : ℝ} :
    SingularLearningTheory.HasLLCExponentsFamilyOn μ K
      (entryFamily fun x => Q x * A x * Q' x) lam theta ↔
    SingularLearningTheory.HasLLCExponentsFamilyOn μ K (entryFamily A) lam theta :=
  SingularLearningTheory.IdealEqOn.hasLLCExponentsFamilyOn_iff
    (idealEqOn_entryFamily_mul hK hQ hQ' hQu hQ'u)

end Exponents

/-- Unipotent (unit-determinant) matrices are pointwise invertible —
the convenience feeding LA3's hypotheses when a genuine row/column
multiplication arises in the replay (most of Aoyagi's "analytic
row/column operations" are coordinate redefinitions and need no
ideal-level lemma at all; see the R5.4 analysis). -/
private theorem isUnit_of_det_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (h : M.det = 1) : IsUnit M := by
  simp [Matrix.isUnit_iff_isUnit_det, h]

end SingularLearningTheory
