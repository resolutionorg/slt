/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.EmpiricalProcess.Defs
public import SLT.EmpiricalProcess.Borel

/-!
# The empirical process as a random continuous function

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 4.2.1], "`ψ_n` is a random variable on `C`" | |
| | `SingularLearningTheory.EmpiricalProcess.continuousModification`,
`SingularLearningTheory.EmpiricalProcess.measurable_continuousModification`, |
| | `SingularLearningTheory.EmpiricalProcess.ae_continuousModification_apply` |

[Hit26]'s `ψ_n(w) = n^{-1/2} Σ_{i<n} (f(X_i, w) − E f(X, w))` is continuous in `w` only when
every `X_i` lies in the set `G` of `x` with `f(x, ·)` continuous. The random continuous function
`Ψ_n` is `ψ_n` on the event `{∀ i < n, X_i ∈ G}` and `0` elsewhere; it is measurable into
`C(U, ℝ)` (evaluations are measurable, `ContinuousMap.measurable_of_eval`) and agrees with `ψ_n`
almost
surely when `q(Gᶜ) = 0`. The mean `w ↦ E f(X, w)` must be continuous as well; in [Hit26] this
follows from `L^s(q)`-valued analyticity.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {X Ω U : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MetricSpace U] [CompactSpace U]
  (q : Measure X) (f : X → U → ℝ) (Xs : ℕ → Ω → X) {G : Set X}

omit [CompactSpace U] in
/-- A measurable set of full measure on which `f(x, ·)` is continuous. -/
theorem _root_.MeasureTheory.exists_measurable_continuity_set
    (hf_cont : ∀ᵐ x ∂q, Continuous (f x)) :
    ∃ G : Set X, MeasurableSet G ∧ q Gᶜ = 0 ∧ ∀ x ∈ G, Continuous (f x) := by
  rw [ae_iff] at hf_cont
  obtain ⟨t, hst, htm, htq⟩ := exists_measurable_superset_of_null hf_cont
  refine ⟨tᶜ, htm.compl, by rwa [compl_compl], fun x hx ↦ ?_⟩
  by_contra hc
  exact hx (hst hc)

/-- The empirical process `ψ_n` as a continuous function of the parameter, on the event that
every `X_i`, `i < n`, lies in the continuity set `G`; `0` elsewhere. -/
@[expose] noncomputable def EmpiricalProcess.continuousModification (hG : ∀ x ∈ G, Continuous (f x))
    (hmean : Continuous fun u ↦ ∫ x, f x u ∂q) (n : ℕ) (ω : Ω) : C(U, ℝ) := by
  classical
  exact if h : ∀ l ∈ Finset.range n, Xs l ω ∈ G then
    ⟨fun u ↦ empiricalProcess q f Xs n ω u,
      continuous_const.mul (continuous_finsetSum _ fun l hl ↦ (hG _ (h l hl)).sub hmean)⟩
  else 0

variable {q f Xs}

omit [MeasurableSpace Ω] [CompactSpace U] in
private theorem continuousModification_apply (hG : ∀ x ∈ G, Continuous (f x))
    (hmean : Continuous fun u ↦ ∫ x, f x u ∂q) {n : ℕ} {ω : Ω}
    (h : ∀ l ∈ Finset.range n, Xs l ω ∈ G) (u : U) :
    EmpiricalProcess.continuousModification q f Xs hG hmean n ω u = empiricalProcess q f Xs n ω u :=
        by
  rw [EmpiricalProcess.continuousModification, dite_eq_left h]
  rfl

theorem EmpiricalProcess.measurable_continuousModification (hGm : MeasurableSet G)
    (hG : ∀ x ∈ G, Continuous (f x))
    (hmean : Continuous fun u ↦ ∫ x, f x u ∂q) (hf_meas : ∀ u, Measurable fun x ↦ f x u)
    (hX : ∀ i, Measurable (Xs i)) (n : ℕ) :
    Measurable (EmpiricalProcess.continuousModification q f Xs hG hmean n) := by
  refine ContinuousMap.measurable_of_eval fun u ↦ ?_
  have heq : (fun ω ↦ EmpiricalProcess.continuousModification q f Xs hG hmean n ω u)
      = indicator {ω | ∀ l ∈ Finset.range n, Xs l ω ∈ G}
        (fun ω ↦ empiricalProcess q f Xs n ω u) := by
    funext ω
    by_cases h : ∀ l ∈ Finset.range n, Xs l ω ∈ G
    · rw [continuousModification_apply hG hmean h, indicator_of_mem (mem_ofPred.mpr h)]
    · rw [indicator_of_notMem (show ω ∉ {ω | ∀ l ∈ Finset.range n, Xs l ω ∈ G} from h),
        EmpiricalProcess.continuousModification, dite_eq_right h, ContinuousMap.zero_apply]
  have hset : {ω | ∀ l ∈ Finset.range n, Xs l ω ∈ G} = ⋂ l ∈ Finset.range n, Xs l ⁻¹' G := by
    ext ω
    simp
  rw [heq]
  refine Measurable.indicator ?_ ?_
  · exact measurable_const.mul
      (Finset.measurable_sum _ fun l _ ↦ ((hf_meas u).comp (hX l)).sub measurable_const)
  · rw [hset]
    exact Finset.measurableSet_biInter _ fun l _ ↦ hX l hGm

/-- A property holding for `q`-almost every `x` holds, `P`-almost surely, at every `X_i`,
`i < n`. -/
theorem _root_.MeasureTheory.ae_forall_range_comp {P : Measure Ω} (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) {p : X → Prop} (hp : ∀ᵐ x ∂q, p x) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ l ∈ Finset.range n, p (Xs l ω) := by
  rw [Finset.eventually_all]
  intro l _
  rw [← hlaw l] at hp
  exact ae_of_ae_map (hX l).aemeasurable hp

omit [CompactSpace U] in
theorem EmpiricalProcess.ae_continuousModification_apply {P : Measure Ω}
    (hX : ∀ i, Measurable (Xs i))
    (hlaw : ∀ i, P.map (Xs i) = q) (hGq : q Gᶜ = 0) (hG : ∀ x ∈ G, Continuous (f x))
    (hmean : Continuous fun u ↦ ∫ x, f x u ∂q) (n : ℕ) :
    ∀ᵐ ω ∂P, ∀ u, EmpiricalProcess.continuousModification q f Xs hG hmean n ω u = empiricalProcess q
        f Xs n ω u := by
  have hp : ∀ᵐ x ∂q, x ∈ G := mem_ae_iff.mpr hGq
  filter_upwards [ae_forall_range_comp hX hlaw hp n] with ω hω u
  exact continuousModification_apply hG hmean hω u

end SingularLearningTheory
