/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.OptimizerFaces
public import SLT.FreeEnergy.Discharge
public import SLT.FreeEnergy.SamplewiseResolution

/-!
# A common empirical process for prior and optimizer charts

Restriction preserves the finite-sample field and limit, including the joint law
of prior charts and optimizer-only coordinate faces.
-/

public section

namespace SingularLearningTheory

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace EmpiricalProcessLimit

variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {U V : Type*} [TopologicalSpace U] [TopologicalSpace V] [CompactSpace U] [CompactSpace V]
  {q : Measure X} {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P']
  {f : X → U → ℝ} {Xs : ℕ → Ω → X}

/-- Restrict a continuous empirical field to any continuously parametrized
compact subdomain, preserving its joint Gaussian realization. -/
@[expose] noncomputable def precomp (E : EmpiricalProcessLimit q f Xs P P') (j : C(V, U)) :
    EmpiricalProcessLimit q (fun x v ↦ f x (j v)) Xs P P' where
  Ψ := fun n ω ↦ (E.Ψ n ω).comp j
  Ψ_measurable := fun n ↦
    (ContinuousMap.continuous_precomp j).measurable.comp (E.Ψ_measurable n)
  Ψ_ae_eq := fun n ↦ by
    filter_upwards [E.Ψ_ae_eq n] with ω hω v
    exact hω (j v)
  tight := by
    have ht := E.tight.map (ContinuousMap.continuous_precomp j)
    apply ht.subset
    rintro _ ⟨n, rfl⟩
    refine ⟨P.map (E.Ψ n), ⟨n, rfl⟩, ?_⟩
    exact Measure.map_map (ContinuousMap.continuous_precomp j).measurable (E.Ψ_measurable n)
  Ψlim := fun ω' ↦ (E.Ψlim ω').comp j
  tendsto := E.tendsto.continuous_comp (ContinuousMap.continuous_precomp j)
  gaussian := fun m u ↦ E.gaussian m (fun i ↦ j (u i))
  mean_zero := fun v ↦ E.mean_zero (j v)
  cov := fun v v' ↦ E.cov (j v) (j v')

end EmpiricalProcessLimit

namespace AtlasData

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (A : AtlasData K φ W) [Nonempty A.ι]

/-- Inclusion of the genuine prior charts into the common optimizer chart domain. -/
@[expose] noncomputable def optimizerPriorInclusion :
    C((α : A.toResolutionAtlas.ι) × cube d (A.toResolutionAtlas.b α),
      (α : A.optimizerAtlas.ι) × cube d (A.optimizerAtlas.b α)) where
  toFun := fun v ↦ ⟨Sum.inl v.1, v.2⟩
  continuous_toFun := continuous_sigma fun α ↦ by
    change Continuous (fun u : cube d (A.toResolutionAtlas.b α) ↦
      (⟨Sum.inl α, u⟩ : (α : A.optimizerAtlas.ι) × cube d (A.optimizerAtlas.b α)))
    exact continuous_sigmaMk (σ := fun α : A.optimizerAtlas.ι ↦
      cube d (A.optimizerAtlas.b α)) (i := Sum.inl α)

variable {X : Type*} [MeasurableSpace X] {q : Measure X}
  {f : X → (Fin d → ℝ) → ℝ} {s : ℝ≥0∞}

/-- The prior likelihood coefficients are literal restrictions of the single
resolved likelihood on all optimizer charts. -/
@[expose] noncomputable def priorLikelihoodOfOptimizer
    (L : A.optimizerAtlas.AnalyticResolvedLikelihood s q f) :
    A.toResolutionAtlas.AnalyticResolvedLikelihood s q f where
  a := fun α ↦ L.a (Sum.inl α)
  a_measurable := fun α ↦ L.a_measurable (Sum.inl α)
  factor := fun α ↦ L.factor (Sum.inl α)
  mean := fun α u ↦ L.mean (Sum.inl α) u
  memLp := fun α u ↦ L.memLp (Sum.inl α) u
  loc := fun α u ↦ L.loc (Sum.inl α) u

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {Xs : ℕ → Ω → X}

/-- The empirical-process input of the prior free-energy theorem, on the very
same limit space and same realization as the optimizer process. -/
@[expose] noncomputable def priorProcessOfOptimizer
    (L : A.optimizerAtlas.AnalyticResolvedLikelihood s q f)
    (E : EmpiricalProcessLimit q
      (fun x (u : (α : A.optimizerAtlas.ι) × cube d (A.optimizerAtlas.b α)) ↦ L.a u.1 x u.2)
      Xs P P') :
    EmpiricalProcessLimit q
      (fun x (u : (α : A.toResolutionAtlas.ι) × cube d (A.toResolutionAtlas.b α)) ↦
        (A.priorLikelihoodOfOptimizer L).a u.1 x u.2) Xs P P' where
  Ψ := fun n ω ↦ (E.Ψ n ω).comp A.optimizerPriorInclusion
  Ψ_measurable := (E.precomp A.optimizerPriorInclusion).Ψ_measurable
  Ψ_ae_eq := fun n ↦ by
    filter_upwards [E.Ψ_ae_eq n] with ω hω u
    exact hω (A.optimizerPriorInclusion u)
  tight := (E.precomp A.optimizerPriorInclusion).tight
  Ψlim := fun ω' ↦ (E.Ψlim ω').comp A.optimizerPriorInclusion
  tendsto := (E.precomp A.optimizerPriorInclusion).tendsto
  gaussian := fun m u ↦ E.gaussian m (fun i ↦ A.optimizerPriorInclusion (u i))
  mean_zero := fun u ↦ E.mean_zero (A.optimizerPriorInclusion u)
  cov := fun u v ↦ E.cov (A.optimizerPriorInclusion u) (A.optimizerPriorInclusion v)

variable (L : A.optimizerAtlas.AnalyticResolvedLikelihood s q f)
  (E : EmpiricalProcessLimit q
    (fun x (u : (α : A.optimizerAtlas.ι) × cube d (A.optimizerAtlas.b α)) ↦ L.a u.1 x u.2)
    Xs P P')

@[simp] theorem priorProcessOfOptimizer_Ψ (n : ℕ) (ω : Ω) :
    (A.priorProcessOfOptimizer L E).Ψ n ω = (E.Ψ n ω).comp A.optimizerPriorInclusion := rfl

@[simp] theorem priorProcessOfOptimizer_Ψlim (ω' : Ω') :
    (A.priorProcessOfOptimizer L E).Ψlim ω' = (E.Ψlim ω').comp A.optimizerPriorInclusion := rfl

end AtlasData
end SingularLearningTheory
