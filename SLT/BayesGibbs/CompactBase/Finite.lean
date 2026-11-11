/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.BayesGibbs.CompactBase.Kernel
public import SLT.BayesGibbs.FiniteQuartet.Basic
import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Gaussian fields and finite quantisations

`ProbabilityTheory.GaussianField` is a centred Gaussian random field with a given continuous
positive-semidefinite covariance kernel. A finite-range quantisation of a compact base reduces
sums against its law to sums over finitely many atoms of positive mass, and the finite-base
Stein identity holds for the field's values at these atoms.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`: the finite atom reduction, the Gaussian field
structure and the finite-base Stein identity.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

section Atoms

variable {K : Type*} [MeasurableSpace K] [MeasurableSingletonClass K] (ρ : Measure K)
  [IsFiniteMeasure ρ] {q : K → K}

/-- The atoms of positive mass of a finite-range quantisation. -/
@[expose] noncomputable def posAtoms (hfin : (Set.range q).Finite) : Finset K :=
  hfin.toFinset.filter fun a ↦ 0 < ρ.real (q ⁻¹' {a})

/-- Enumeration of the positive atoms. -/
@[expose] noncomputable def atomPt (hfin : (Set.range q).Finite)
    (i : Fin (posAtoms ρ hfin).card) : K :=
  ((posAtoms ρ hfin).equivFin.symm i : K)

/-- The weights of the positive atoms. -/
@[expose] noncomputable def atomWt (hfin : (Set.range q).Finite)
    (i : Fin (posAtoms ρ hfin).card) : ℝ :=
  ρ.real (q ⁻¹' {atomPt ρ hfin i})

omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
private theorem atomPt_mem (hfin : (Set.range q).Finite) (i : Fin (posAtoms ρ hfin).card) :
    atomPt ρ hfin i ∈ posAtoms ρ hfin := ((posAtoms ρ hfin).equivFin.symm i).2

omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
theorem atomWt_pos (hfin : (Set.range q).Finite) (i : Fin (posAtoms ρ hfin).card) :
    0 < atomWt ρ hfin i :=
  (Finset.mem_filter.1 (atomPt_mem ρ hfin i)).2

omit [MeasurableSingletonClass K] [IsFiniteMeasure ρ] in
/-- Sums over the range weighted by the atom masses reduce to sums over the positive atoms. -/
private theorem sum_range_eq_sum_atoms (hfin : (Set.range q).Finite) (F : K → ℝ) :
    ∑ a ∈ hfin.toFinset, ρ.real (q ⁻¹' {a}) * F a = ∑ i, atomWt ρ hfin i * F (atomPt ρ hfin i) := by
  rw [← Finset.sum_filter_of_ne (p := fun a ↦ 0 < ρ.real (q ⁻¹' {a})) (fun a _ h ↦ ?_)]
  · change ∑ a ∈ posAtoms ρ hfin, _ = _
    rw [← Finset.sum_coe_sort (posAtoms ρ hfin)]
    exact ((posAtoms ρ hfin).equivFin.symm.sum_comp
      (fun a : posAtoms ρ hfin ↦ ρ.real (q ⁻¹' {(a : K)}) * F a)).symm
  · rcases (measureReal_nonneg (μ := ρ) (s := q ⁻¹' {a})).lt_or_eq with h' | h'
    · exact h'
    · exact absurd (by rw [← h', zero_mul]) h

private theorem integral_comp_finiteRange_atoms (hq : Measurable q) (hfin : (Set.range q).Finite)
    (f : K → ℝ) : ∫ x, f (q x) ∂ρ = ∑ i, atomWt ρ hfin i * f (atomPt ρ hfin i) := by
  rw [integral_comp_finiteRange ρ hq hfin f, sum_range_eq_sum_atoms]

private theorem sum_atomWt (hq : Measurable q) (hfin : (Set.range q).Finite) :
    ∑ i, atomWt ρ hfin i = ρ.real univ := by
  have := integral_comp_finiteRange_atoms ρ hq hfin (fun _ ↦ (1 : ℝ))
  simp only [integral_const, smul_eq_mul, mul_one] at this
  exact this.symm

theorem nonempty_atoms (hq : Measurable q) (hfin : (Set.range q).Finite) (hρ : ρ ≠ 0) :
    Nonempty (Fin (posAtoms ρ hfin).card) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hsum := sum_atomWt ρ hq hfin
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  have : 0 < ρ.real univ := by
    rw [measureReal_def]
    exact ENNReal.toReal_pos (Measure.measure_univ_ne_zero.2 hρ) (measure_ne_top _ _)
  linarith

end Atoms

/-- The kernel matrix `C(xᵢ, xⱼ)` of a finite family of points. -/
@[expose] def _root_.PSDKernel.kernelMatrix {K : Type*} [TopologicalSpace K] (𝒞 : PSDKernel K)
    {m : ℕ}
    (x : Fin m → K) : Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j ↦ 𝒞.C (x i) (x j)

section Reduce

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (𝒞 : PSDKernel K) (g : C(K, ℝ)) {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hβ hlam hq

omit 𝒞 in
private theorem compactD_map_eq :
    compactD β lam (ρ.map q) g = quartetD β lam (atomWt ρ hfin) (fun i ↦ g (atomPt ρ hfin i)) := by
  rw [compactD_map ρ hβ hlam g hq,
    integral_comp_finiteRange_atoms ρ hq hfin (fun x ↦ frozenInner lam β (g x))]
  rfl

omit 𝒞 in
private theorem compactM2_map_eq :
    compactM2 β lam (ρ.map q) g =
      quartetM2 β lam (atomWt ρ hfin) (fun i ↦ g (atomPt ρ hfin i)) := by
  rw [compactM2_map ρ hβ hlam g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x ↦ frozenInner (lam + 1) β (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetM2 quartetR
  rw [Finset.sum_div]

omit 𝒞 in
theorem compactH_map_eq :
    compactH β lam (ρ.map q) g =
      quartetH β lam (atomWt ρ hfin) (fun i ↦ g (atomPt ρ hfin i)) := by
  rw [compactH_map ρ hβ hlam g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x ↦ g x * frozenInner (lam + 1 / 2) β (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetH quartetW quartetN
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

private theorem compactDiag_map_eq :
    compactDiag (ρ.map q) β lam 𝒞 g =
      quartetDiag β lam (atomWt ρ hfin) (𝒞.kernelMatrix (atomPt ρ hfin))
        (fun i ↦ g (atomPt ρ hfin i)) := by
  rw [compactDiag_map ρ hβ hlam 𝒞 g hq, integral_comp_finiteRange_atoms ρ hq hfin
    (fun x ↦ 𝒞.C x x * frozenInner (lam + 1) β (g x)), compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetDiag quartetR PSDKernel.kernelMatrix
  rw [Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ ↦ by simp only [Matrix.of_apply]; ring

private theorem compactQnum_map_eq :
    compactQnum (ρ.map q) β lam 𝒞 g =
      ∑ i, ∑ j, 𝒞.C (atomPt ρ hfin i) (atomPt ρ hfin j) *
        (atomWt ρ hfin i * frozenInner (lam + 1 / 2) β (g (atomPt ρ hfin i))) *
        (atomWt ρ hfin j * frozenInner (lam + 1 / 2) β (g (atomPt ρ hfin j))) := by
  set F : C(K × K, ℝ) := ⟨bilocalC β lam 𝒞 g, continuous_bilocalC hβ hlam 𝒞 g⟩ with hF
  have hint : Integrable (fun z : K × K ↦ bilocalC β lam 𝒞 g (q z.1, q z.2)) (ρ.prod ρ) :=
    Integrable.of_bound ((continuous_bilocalC hβ hlam 𝒞 g).measurable.comp
      (((hq.comp measurable_fst).prodMk (hq.comp measurable_snd)))).aestronglyMeasurable ‖F‖
      (Filter.Eventually.of_forall fun z ↦ F.norm_coe_le_norm (q z.1, q z.2))
  rw [compactQnum_map ρ hβ hlam 𝒞 g hq, integral_prod _ hint]
  have hin : ∀ x, ∫ y, bilocalC β lam 𝒞 g (q x, q y) ∂ρ =
      ∑ j, atomWt ρ hfin j * bilocalC β lam 𝒞 g (q x, atomPt ρ hfin j) := fun x ↦
    integral_comp_finiteRange_atoms ρ hq hfin (fun b ↦ bilocalC β lam 𝒞 g (q x, b))
  simp_rw [hin]
  have hout := integral_comp_finiteRange_atoms ρ hq hfin
    (fun a ↦ ∑ j, atomWt ρ hfin j * bilocalC β lam 𝒞 g (a, atomPt ρ hfin j))
  beta_reduce at hout
  rw [hout]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [bilocalC]
  ring

private theorem compactQ_map_eq (hρ : ρ ≠ 0) :
    compactQ (ρ.map q) β lam 𝒞 g =
      quartetQ β lam (atomWt ρ hfin) (𝒞.kernelMatrix (atomPt ρ hfin))
        (fun i ↦ g (atomPt ρ hfin i)) := by
  have := nonempty_atoms ρ hq hfin hρ
  have hD := quartetD_pos hβ hlam (atomWt_pos ρ hfin) (fun i ↦ g (atomPt ρ hfin i))
  unfold compactQ
  rw [compactQnum_map_eq ρ hβ hlam 𝒞 g hq hfin, compactD_map_eq ρ hβ hlam g hq hfin]
  unfold quartetQ quartetW quartetN PSDKernel.kernelMatrix
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Matrix.of_apply]
  field_simp

theorem compactV_map_eq (hρ : ρ ≠ 0) :
    compactV (ρ.map q) β lam 𝒞 g =
      quartetVgen β lam (atomWt ρ hfin) (𝒞.kernelMatrix (atomPt ρ hfin))
        (fun i ↦ g (atomPt ρ hfin i)) := by
  unfold compactV quartetVgen
  rw [compactDiag_map_eq ρ hβ hlam 𝒞 g hq hfin, compactQ_map_eq ρ hβ hlam 𝒞 g hq hfin hρ]


end Reduce

/-! ### The Gaussian field record -/

/-- A **Gaussian field** on the compact base with covariance kernel `𝒞`: a random continuous
function with measurable evaluations, a finite second sup-norm moment, and finite-dimensional
laws given by the axiom-clean `ProbabilityTheory.gaussianVector` construction with covariance
`kernelMatrix 𝒞 x`. -/
structure _root_.ProbabilityTheory.GaussianField {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (𝒞 : PSDKernel K)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) where
  /-- The random continuous function. -/
  G : Ω → C(K, ℝ)
  measurable_eval : ∀ x, Measurable fun ω ↦ G ω x
  integrable_sq_norm : Integrable (fun ω ↦ ‖G ω‖ ^ 2) P
  law : ∀ (m : ℕ) (x : Fin m → K), ∃ (n : ℕ) (A : Matrix (Fin m) (Fin (n + 1)) ℝ),
    A * A.transpose = 𝒞.kernelMatrix x ∧
      P.map (fun ω ↦ fun i ↦ G ω (x i)) = gaussianVector A

end SingularLearningTheory.GaussianPosterior

namespace ProbabilityTheory.GaussianField

open SingularLearningTheory SingularLearningTheory.GaussianPosterior

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {𝒞 : PSDKernel K} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (Γ : GaussianField 𝒞 P)

omit [MeasurableSpace K] [BorelSpace K] in
theorem measurable_evalVec {m : ℕ} (x : Fin m → K) :
    Measurable fun ω ↦ fun i ↦ Γ.G ω (x i) :=
  Measurable.of_eval fun i ↦ Γ.measurable_eval (x i)

omit [MeasurableSpace K] [BorelSpace K] in
/-- Finite-dimensional integrals transfer to the Gaussian vector. -/
theorem integral_eval {m n : ℕ} (x : Fin m → K) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (hA : P.map (fun ω ↦ fun i ↦ Γ.G ω (x i)) = gaussianVector A) {F : (Fin m → ℝ) → ℝ}
    (hF : Measurable F) :
    ∫ ω, F (fun i ↦ Γ.G ω (x i)) ∂P = ∫ v, F v ∂gaussianVector A := by
  rw [← hA, integral_map (Γ.measurable_evalVec x).aemeasurable hF.aestronglyMeasurable]

omit [MeasurableSpace K] [BorelSpace K] in
theorem integrable_eval {m n : ℕ} (x : Fin m → K) (A : Matrix (Fin m) (Fin (n + 1)) ℝ)
    (hA : P.map (fun ω ↦ fun i ↦ Γ.G ω (x i)) = gaussianVector A) {F : (Fin m → ℝ) → ℝ}
    (hF : Measurable F) (hint : Integrable F (gaussianVector A)) :
    Integrable (fun ω ↦ F (fun i ↦ Γ.G ω (x i))) P := by
  rw [← hA] at hint
  exact (integrable_map_measure hF.aestronglyMeasurable
    (Γ.measurable_evalVec x).aemeasurable).1 hint

variable {β lam : ℝ} (ρ : Measure K) [IsFiniteMeasure ρ] (hβ : 0 < β) (hlam : 0 < lam)
  (hρ : ρ ≠ 0) {q : K → K} (hq : Measurable q) (hfin : (Set.range q).Finite)
include hβ hlam hρ hq hfin

/-- **`E H = β E V` on a quantised base.** -/
theorem integral_compactH_map_eq :
    ∫ ω, compactH β lam (ρ.map q) (Γ.G ω) ∂P =
      β * ∫ ω, compactV (ρ.map q) β lam 𝒞 (Γ.G ω) ∂P := by
  have := nonempty_atoms ρ hq hfin hρ
  obtain ⟨n, A, hAB, hA⟩ := Γ.law _ (atomPt ρ hfin)
  have hw := atomWt_pos ρ hfin
  simp_rw [compactH_map_eq ρ hβ hlam (Γ.G _) hq hfin,
    compactV_map_eq ρ hβ hlam 𝒞 (Γ.G _) hq hfin hρ]
  rw [Γ.integral_eval _ A hA (continuous_quartetH hβ hlam hw).measurable,
    Γ.integral_eval _ A hA (continuous_quartetVgen hβ hlam hw _).measurable, ← hAB]
  exact integral_quartetH_eq_gen hβ hlam hw A


end ProbabilityTheory.GaussianField

namespace SingularLearningTheory.GaussianPosterior
end SingularLearningTheory.GaussianPosterior
