/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.Defs

/-!
# Two empirical-process limits on one probability space

No thesis counterpart. The free energy theorems place the limit `ξ` of the chart process and the
limit of `ψ_n` on `{K ≥ δ}` on a single probability space `(Ω', P')` ("always possible, by a
product"); here the two `EmpiricalProcessLimit`s, each realised on its own space, are transported
to the product space along the two projections.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

section Projections

variable {Ω₁ Ω₂ E : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] [MeasurableSpace E]
  {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodFst`. -/
private lemma map_prod_fst [IsProbabilityMeasure P₂] : (P₁.prod P₂).map Prod.fst = P₁ := by
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodSnd`. -/
private lemma map_prod_snd [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂] :
    (P₁.prod P₂).map Prod.snd = P₂ := by
  rw [Measure.map_snd_prod, measure_univ, one_smul]

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodFst`. -/
lemma _root_.MeasureTheory.Measure.map_comp_fst [IsProbabilityMeasure P₂] {g : Ω₁ → E}
    (hg : AEMeasurable g P₁) :
    (P₁.prod P₂).map (fun ω ↦ g ω.1) = P₁.map g := by
  have hg' : AEMeasurable g ((P₁.prod P₂).map Prod.fst) := by rwa [map_prod_fst]
  rw [show (fun ω : Ω₁ × Ω₂ ↦ g ω.1) = g ∘ Prod.fst from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hg' measurable_fst.aemeasurable, map_prod_fst]

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodSnd`. -/
lemma _root_.MeasureTheory.Measure.map_comp_snd [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {g : Ω₂ → E}
    (hg : AEMeasurable g P₂) : (P₁.prod P₂).map (fun ω ↦ g ω.2) = P₂.map g := by
  have hg' : AEMeasurable g ((P₁.prod P₂).map Prod.snd) := by rwa [map_prod_snd]
  rw [show (fun ω : Ω₁ × Ω₂ ↦ g ω.2) = g ∘ Prod.snd from rfl,
    ← AEMeasurable.map_map_of_aemeasurable hg' measurable_snd.aemeasurable, map_prod_snd]

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodFst`. -/
lemma _root_.MeasureTheory.integral_comp_fst [IsProbabilityMeasure P₂] {g : Ω₁ → ℝ}
    (hg : AEStronglyMeasurable g P₁) : ∫ ω, g ω.1 ∂(P₁.prod P₂) = ∫ ω, g ω ∂P₁ := by
  have hg' : AEStronglyMeasurable g ((P₁.prod P₂).map Prod.fst) := by rwa [map_prod_fst]
  have h := integral_map (μ := P₁.prod P₂) measurable_fst.aemeasurable hg'
  rwa [map_prod_fst, eq_comm] at h

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodSnd`. -/
lemma _root_.MeasureTheory.integral_comp_snd [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
    {g : Ω₂ → ℝ}
    (hg : AEStronglyMeasurable g P₂) : ∫ ω, g ω.2 ∂(P₁.prod P₂) = ∫ ω, g ω ∂P₂ := by
  have hg' : AEStronglyMeasurable g ((P₁.prod P₂).map Prod.snd) := by rwa [map_prod_snd]
  have h := integral_map (μ := P₁.prod P₂) measurable_snd.aemeasurable hg'
  rwa [map_prod_snd, eq_comm] at h

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodFst`. -/
lemma _root_.ProbabilityTheory.covariance_comp_fst [IsProbabilityMeasure P₂] {g g' : Ω₁ → ℝ}
    (hg : AEStronglyMeasurable g P₁) (hg' : AEStronglyMeasurable g' P₁) :
    cov[fun ω ↦ g ω.1, fun ω ↦ g' ω.1; P₁.prod P₂] = cov[g, g'; P₁] := by
  have h₁ : AEStronglyMeasurable g ((P₁.prod P₂).map Prod.fst) := by rwa [map_prod_fst]
  have h₂ : AEStronglyMeasurable g' ((P₁.prod P₂).map Prod.fst) := by rwa [map_prod_fst]
  have h := covariance_map_fun h₁ h₂ measurable_fst.aemeasurable
  rwa [map_prod_fst, eq_comm] at h

/-- No thesis counterpart; used by `EmpiricalProcessLimit.prodSnd`. -/
lemma _root_.ProbabilityTheory.covariance_comp_snd [IsProbabilityMeasure P₁]
    [IsProbabilityMeasure P₂] {g g' : Ω₂ → ℝ}
    (hg : AEStronglyMeasurable g P₂) (hg' : AEStronglyMeasurable g' P₂) :
    cov[fun ω ↦ g ω.2, fun ω ↦ g' ω.2; P₁.prod P₂] = cov[g, g'; P₂] := by
  have h₁ : AEStronglyMeasurable g ((P₁.prod P₂).map Prod.snd) := by rwa [map_prod_snd]
  have h₂ : AEStronglyMeasurable g' ((P₁.prod P₂).map Prod.snd) := by rwa [map_prod_snd]
  have h := covariance_map_fun h₁ h₂ measurable_snd.aemeasurable
  rwa [map_prod_snd, eq_comm] at h

end Projections

variable {X Ω Ω₁ Ω₂ : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω₁]
  [MeasurableSpace Ω₂] {U : Type*} [TopologicalSpace U] {q : Measure X} {f : X → U → ℝ}
  {Xs : ℕ → Ω → X} {P : Measure Ω} {P₁ : Measure Ω₁} {P₂ : Measure Ω₂} [IsProbabilityMeasure P]
  [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]

namespace EmpiricalProcessLimit

variable {Ω' : Type*} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

/-- No thesis counterpart; the limit evaluated at a point is a.e.-measurable. -/
lemma aemeasurable_Ψlim_eval (E : EmpiricalProcessLimit q f Xs P P') (u : U) :
    AEMeasurable (fun ω' ↦ E.Ψlim ω' u) P' :=
  (continuous_eval_const u).measurable.comp_aemeasurable E.tendsto.aemeasurable_limit

/-- No thesis counterpart; the limit evaluated at finitely many points is a.e.-measurable. -/
lemma aemeasurable_Ψlim_pi (E : EmpiricalProcessLimit q f Xs P P') {M : ℕ} (u : Fin M → U) :
    AEMeasurable (fun ω' j ↦ E.Ψlim ω' (u j)) P' :=
  AEMeasurable.of_eval fun j ↦ E.aemeasurable_Ψlim_eval (u j)

/-- An empirical-process limit realised on `Ω₁`, viewed on the product `Ω₁ × Ω₂` through the
first projection. -/
@[expose] noncomputable def prodFst (E : EmpiricalProcessLimit q f Xs P P₁) :
    EmpiricalProcessLimit q f Xs P (P₁.prod P₂) where
  Ψ := E.Ψ
  Ψ_measurable := E.Ψ_measurable
  Ψ_ae_eq := E.Ψ_ae_eq
  tight := E.tight
  Ψlim := fun ω ↦ E.Ψlim ω.1
  tendsto :=
    { forall_aemeasurable := E.tendsto.forall_aemeasurable
      aemeasurable_limit := E.tendsto.aemeasurable_limit.comp_fst
      tendsto := by
        convert E.tendsto.tendsto using 3
        congr 1
        refine ProbabilityMeasure.toMeasure_injective ?_
        exact Measure.map_comp_fst E.tendsto.aemeasurable_limit }
  gaussian := fun M u ↦ by
    rw [Measure.map_comp_fst (E.aemeasurable_Ψlim_pi u)]
    exact E.gaussian M u
  mean_zero := fun u ↦
    (integral_comp_fst (E.aemeasurable_Ψlim_eval u).aestronglyMeasurable).trans
      (E.mean_zero u)
  cov := fun u u' ↦
    (covariance_comp_fst (E.aemeasurable_Ψlim_eval u).aestronglyMeasurable
      (E.aemeasurable_Ψlim_eval u').aestronglyMeasurable).trans (E.cov u u')

/-- An empirical-process limit realised on `Ω₂`, viewed on the product `Ω₁ × Ω₂` through the
second projection. -/
@[expose] noncomputable def prodSnd (E : EmpiricalProcessLimit q f Xs P P₂) :
    EmpiricalProcessLimit q f Xs P (P₁.prod P₂) where
  Ψ := E.Ψ
  Ψ_measurable := E.Ψ_measurable
  Ψ_ae_eq := E.Ψ_ae_eq
  tight := E.tight
  Ψlim := fun ω ↦ E.Ψlim ω.2
  tendsto :=
    { forall_aemeasurable := E.tendsto.forall_aemeasurable
      aemeasurable_limit := E.tendsto.aemeasurable_limit.comp_snd
      tendsto := by
        convert E.tendsto.tendsto using 3
        congr 1
        refine ProbabilityMeasure.toMeasure_injective ?_
        exact Measure.map_comp_snd E.tendsto.aemeasurable_limit }
  gaussian := fun M u ↦ by
    rw [Measure.map_comp_snd (E.aemeasurable_Ψlim_pi u)]
    exact E.gaussian M u
  mean_zero := fun u ↦
    (integral_comp_snd (E.aemeasurable_Ψlim_eval u).aestronglyMeasurable).trans
      (E.mean_zero u)
  cov := fun u u' ↦
    (covariance_comp_snd (E.aemeasurable_Ψlim_eval u).aestronglyMeasurable
      (E.aemeasurable_Ψlim_eval u').aestronglyMeasurable).trans (E.cov u u')

end EmpiricalProcessLimit

end SingularLearningTheory
