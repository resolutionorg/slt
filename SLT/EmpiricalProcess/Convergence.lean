/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.Borel
public import SLT.Probability.Distributions.Gaussian.Map
import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Convergence in distribution in `C(U, ℝ)` from tightness and finite-dimensional limits

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 4.1.8] | Mathlib `isCompact_closure_of_isTightMeasureSet` |
| [Hit26, Lemma 4.1.4] | |
| | Mathlib `tendsto_of_subseq_tendsto` |
| [Hit26, Theorem 4.1.6], | |
| [Hit26, Corollary 4.1.10] | |
| | `MeasureTheory.exists_tendstoInDistribution_of_tight` |

`U` is a compact metric space. A tight sequence of random continuous functions `Ψ_n` whose
finite-dimensional distributions converge — in the form that every linear image
`L(Ψ_n(u₁), …, Ψ_n(u_M))` converges in distribution to a prescribed law `ν(u, L)` — converges in
distribution in `C(U, ℝ)`. Every subsequential limit `μ` of the laws (Prokhorov) satisfies
`(L ∘ π_u)_* μ = ν(u, L)` (continuous mapping), so any two agree on every finite-dimensional
distribution (Cramér–Wold, `Measure.ext_of_map_continuousLinearMap`) and hence everywhere
(`MeasureTheory.Measure.ext_of_fdd`); the whole sequence then converges by the sub-subsequence
criterion. The limit is
realised as the identity on `(C(U, ℝ), μ)`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

variable {U : Type*} [MetricSpace U]

private theorem continuous_clm_comp_finiteEval {M : ℕ} (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ) :
    Continuous fun h : C(U, ℝ) ↦ L (ContinuousMap.finiteEval u h) :=
  L.continuous.comp (ContinuousMap.continuous_finiteEval u)

variable [CompactSpace U] {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Laws

variable {Ψ : ℕ → Ω → C(U, ℝ)}

/-- The laws `P ∘ Ψ_n⁻¹` of the random continuous functions, as probability measures. -/
private noncomputable def laws (P : Measure Ω) [IsProbabilityMeasure P]
    (_hΨ : ∀ n, Measurable (Ψ n))
    (n : ℕ) : ProbabilityMeasure C(U, ℝ) :=
  ProbabilityMeasure.map (⟨P, ‹IsProbabilityMeasure P›⟩ : ProbabilityMeasure Ω) (Ψ n)

variable (hΨ : ∀ n, Measurable (Ψ n))

omit [CompactSpace U] in
private theorem coe_laws (n : ℕ) : (laws P hΨ n : Measure C(U, ℝ)) = P.map (Ψ n) := rfl

omit [CompactSpace U] in
/-- A subsequential limit `μ` of the laws inherits the finite-dimensional limits: if
`L(Ψ_n(u₁), …, Ψ_n(u_M)) → ν` in distribution along the whole sequence, then
`(L ∘ π_u)_* μ = ν`. -/
private theorem map_eq_of_tendsto_laws {μ : ProbabilityMeasure C(U, ℝ)} {φ : ℕ → ℕ}
    (hφ : Tendsto φ atTop atTop) (hlim : Tendsto (laws P hΨ ∘ φ) atTop (𝓝 μ))
    {M : ℕ} {u : Fin M → U} {L : (Fin M → ℝ) →L[ℝ] ℝ} {ν : ProbabilityMeasure ℝ}
    (hν : TendstoInDistribution (fun n ω ↦ L (ContinuousMap.finiteEval u (Ψ n ω))) atTop id
        (fun _ ↦ P)
      (ν : Measure ℝ)) :
    (μ : Measure C(U, ℝ)).map (fun h ↦ L (ContinuousMap.finiteEval u h)) = ν := by
  have hcont := continuous_clm_comp_finiteEval u L
  have h1 := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim hcont
  have h2 := hν.tendsto.comp hφ
  have h1' : Tendsto (β := ProbabilityMeasure ℝ)
      (fun i ↦ ⟨P.map (fun ω ↦ L (ContinuousMap.finiteEval u (Ψ (φ i) ω))),
        inferInstance⟩)
      atTop (𝓝 (μ.map fun h ↦ L (ContinuousMap.finiteEval u h))) := by
    refine h1.congr fun i ↦ ?_
    apply Subtype.ext
    change (P.map (Ψ (φ i))).map (fun h ↦ L (ContinuousMap.finiteEval u h)) = _
    rw [Measure.map_map hcont.measurable (hΨ _)]
    rfl
  have := tendsto_nhds_unique h1' h2
  have := congrArg ProbabilityMeasure.toMeasure this
  simpa [Measure.map_id] using this

end Laws

/-- Two subsequential limits of the laws with the same finite-dimensional limits are equal
(Cramér–Wold, then `MeasureTheory.Measure.ext_of_fdd`). -/
private theorem _root_.MeasureTheory.ProbabilityMeasure.ext_of_map_clm_finiteEval
    {μ μ' : ProbabilityMeasure C(U, ℝ)}
    (h : ∀ (M : ℕ) (u : Fin M → U) (L : (Fin M → ℝ) →L[ℝ] ℝ),
      (μ : Measure C(U, ℝ)).map (fun h ↦ L (ContinuousMap.finiteEval u h))
        = (μ' : Measure C(U, ℝ)).map (fun h ↦ L (ContinuousMap.finiteEval u h))) : μ = μ' := by
  apply ProbabilityMeasure.toMeasure_injective
  refine Measure.ext_of_fdd fun M u ↦ ?_
  refine Measure.ext_of_map_continuousLinearMap fun L ↦ ?_
  rw [Measure.map_map L.continuous.measurable (ContinuousMap.measurable_finiteEval u),
    Measure.map_map L.continuous.measurable (ContinuousMap.measurable_finiteEval u)]
  exact h M u L

/-- [Hit26, Corollary 4.1.10]
([Hit26, Theorem 4.1.6] with Prokhorov's theorem):
a tight sequence of random continuous functions whose finite-dimensional distributions
converge — every linear image `L(Ψ_n(u₁), …, Ψ_n(u_M))` converges in distribution to `ν(u, L)` —
converges in distribution in `C(U, ℝ)`, to the identity on `(C(U, ℝ), μ)` for a probability
measure `μ` whose finite-dimensional distributions are the prescribed ones. -/
theorem _root_.MeasureTheory.exists_tendstoInDistribution_of_tight {Ψ : ℕ → Ω → C(U, ℝ)}
    (hΨ : ∀ n, Measurable (Ψ n))
    (ht : IsTightMeasureSet (Set.range fun n ↦ P.map (Ψ n)))
    (ν : (M : ℕ) → (Fin M → U) → ((Fin M → ℝ) →L[ℝ] ℝ) → ProbabilityMeasure ℝ)
    (hν : ∀ M u L, TendstoInDistribution (fun n ω ↦ L (ContinuousMap.finiteEval u (Ψ n ω))) atTop id
      (fun _ ↦ P) (ν M u L : Measure ℝ)) :
    ∃ μ : ProbabilityMeasure C(U, ℝ),
      TendstoInDistribution Ψ atTop id (fun _ ↦ P) (μ : Measure C(U, ℝ)) ∧
      ∀ M u L, (μ : Measure C(U, ℝ)).map (fun h ↦ L (ContinuousMap.finiteEval u h)) = ν M u L := by
  have hS : IsTightMeasureSet
      {((μ : ProbabilityMeasure C(U, ℝ)) : Measure C(U, ℝ)) | μ ∈ Set.range (laws P hΨ)} := by
    convert ht using 1
    ext m
    constructor
    · rintro ⟨μ, ⟨n, rfl⟩, rfl⟩
      exact ⟨n, rfl⟩
    · rintro ⟨n, rfl⟩
      exact ⟨laws P hΨ n, ⟨n, rfl⟩, rfl⟩
  have hK := isCompact_closure_of_isTightMeasureSet hS
  obtain ⟨μ, -, φ, hφ, hlim⟩ := hK.tendsto_subseq fun n ↦ subset_closure (mem_range_self n)
  have hfdd : ∀ M u L, (μ : Measure C(U, ℝ)).map (fun h ↦ L (ContinuousMap.finiteEval u h)) = ν M u
      L :=
    fun M u L ↦ map_eq_of_tendsto_laws hΨ hφ.tendsto_atTop hlim (hν M u L)
  have hlaws : Tendsto (laws P hΨ) atTop (𝓝 μ) := by
    refine tendsto_of_subseq_tendsto fun ns hns ↦ ?_
    obtain ⟨μ', -, ms, hms, hlim'⟩ :=
      hK.tendsto_subseq (x := laws P hΨ ∘ ns) fun n ↦ subset_closure (mem_range_self _)
    have hμ' : μ' = μ := by
      refine ProbabilityMeasure.ext_of_map_clm_finiteEval fun M u L ↦ ?_
      rw [hfdd M u L]
      exact map_eq_of_tendsto_laws hΨ (hns.comp hms.tendsto_atTop) hlim' (hν M u L)
    exact ⟨ms, hμ' ▸ hlim'⟩
  refine ⟨μ, ⟨fun n ↦ (hΨ n).aemeasurable, aemeasurable_id, ?_⟩, hfdd⟩
  have e : (⟨Measure.map id (μ : Measure C(U, ℝ)), by simpa using μ.2⟩ : ProbabilityMeasure C(U, ℝ))
      = μ := ProbabilityMeasure.toMeasure_injective Measure.map_id
  rw [e]
  exact hlaws

end SingularLearningTheory
