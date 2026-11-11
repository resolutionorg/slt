/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Topology.UniformSpace.Ascoli
public import SLT.EmpiricalProcess.Borel

/-!
# Tightness of random continuous functions via Arzelà–Ascoli

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 4.1.11], in the form used | `isCompact_arzelaAscoliSet` |
| [Hit26, Equation (4.2.3)], | |
| [Hit26, Equation (4.2.4)] ⇒ tightness | |
| (the "standard argument" in the proof of [Hit26, Theorem 4.2.9]) | |
| | `MeasureTheory.isTightMeasureSet_of_bounded_of_equicontinuous` |

`U` is a compact metric space. The compact set is
`K = {h | ‖h‖ ≤ M ∧ ∀ k, ∀ u v, dist u v ≤ δ_k → |h u − h v| ≤ a_k}` with `a_k → 0`; a
sequence of random continuous functions whose sup norms are bounded in probability and whose
moduli of continuity are small in probability, uniformly in `n`, is tight.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {U : Type*} [MetricSpace U] [CompactSpace U]

/-- The closed, bounded, equicontinuous set of [Hit26, Theorem 4.1.11] as used
in the proof of [Hit26, Theorem 4.2.9]: `‖h‖ ≤ M` and
`|h u − h v| ≤ a_k` whenever `dist u v ≤ δ_k`. -/
private def arzelaAscoliSet (M : ℝ) (δ a : ℕ → ℝ) : Set C(U, ℝ) :=
  {h | ‖h‖ ≤ M ∧ ∀ k, ∀ u v : U, dist u v ≤ δ k → |h u - h v| ≤ a k}

omit [CompactSpace U] in
/-- A function on `U` satisfying the modulus-of-continuity conditions of `arzelaAscoliSet`
is continuous. No thesis counterpart; used by `isCompact_arzelaAscoliSet`. -/
private theorem continuous_of_modulus {δ a : ℕ → ℝ} (hδ : ∀ k, 0 < δ k) (ha : Tendsto a atTop (𝓝 0))
    {g : U → ℝ} (hg : ∀ k, ∀ u v : U, dist u v ≤ δ k → |g u - g v| ≤ a k) : Continuous g := by
  rw [Metric.continuous_iff]
  intro v ε hε
  obtain ⟨k, hk⟩ := (ha.eventually (gt_mem_nhds hε)).exists
  refine ⟨δ k, hδ k, fun u hu ↦ ?_⟩
  rw [Real.dist_eq]
  exact (hg k u v hu.le).trans_lt hk

/-- [Hit26, Theorem 4.1.11]: the set `arzelaAscoliSet M δ a` is compact when
`δ_k > 0` and `a_k → 0`. -/
private theorem isCompact_arzelaAscoliSet (M : ℝ) {δ a : ℕ → ℝ} (hδ : ∀ k, 0 < δ k)
    (ha : Tendsto a atTop (𝓝 0)) : IsCompact (arzelaAscoliSet (U := U) M δ a) := by
  rcases lt_or_ge M 0 with hM | hM
  · have : arzelaAscoliSet (U := U) M δ a = ∅ := by
      ext h
      simp only [arzelaAscoliSet, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
      exact fun hn ↦ absurd (hn.trans_lt hM) (not_lt.mpr (norm_nonneg h))
    rw [this]
    exact isCompact_empty
  refine ArzelaAscoli.isCompact_of_equicontinuous _ ?_ ?_
  · have himage : ContinuousMap.toFun '' arzelaAscoliSet (U := U) M δ a =
        {g : U → ℝ | (∀ u, |g u| ≤ M) ∧ ∀ k, ∀ u v : U, dist u v ≤ δ k → |g u - g v| ≤ a k} := by
      ext g
      constructor
      · rintro ⟨h, ⟨hM', hmod⟩, rfl⟩
        exact ⟨fun u ↦ (ContinuousMap.norm_le _ hM).mp hM' u, hmod⟩
      · rintro ⟨hM', hmod⟩
        exact ⟨⟨g, continuous_of_modulus hδ ha hmod⟩, ⟨(ContinuousMap.norm_le _ hM).mpr hM', hmod⟩,
          rfl⟩
    rw [himage]
    refine IsCompact.of_isClosed_subset
      (isCompact_univ_pi fun _ : U ↦ isCompact_Icc (a := -M) (b := M)) ?_ ?_
    · simp only [ofPred_and, ofPred_forall]
      exact (isClosed_iInter fun u ↦ isClosed_le (continuous_apply u).abs continuous_const).inter
        (isClosed_iInter fun k ↦ isClosed_iInter fun u ↦ isClosed_iInter fun v ↦
          isClosed_iInter fun _ ↦
            isClosed_le ((continuous_apply u).sub (continuous_apply v)).abs continuous_const)
    · intro g hg u _
      exact abs_le.mp (hg.1 u)
  · intro v
    rw [Metric.equicontinuousAt_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := (ha.eventually (gt_mem_nhds hε)).exists
    refine ⟨δ k, hδ k, fun u hu h ↦ ?_⟩
    rw [Real.dist_eq]
    exact (h.2.2 k v u (by rw [dist_comm]; exact hu.le)).trans_lt hk

omit [CompactSpace U] in
/-- The event "some pair at distance `≤ δ` has increment `> a`" is open in `C(U, ℝ)`. -/
private theorem isOpen_setOf_exists_dist_le_lt (δ a : ℝ) :
    IsOpen {h : C(U, ℝ) | ∃ u v : U, dist u v ≤ δ ∧ a < |h u - h v|} := by
  simp only [ofPred_exists]
  refine isOpen_iUnion fun u ↦ isOpen_iUnion fun v ↦ ?_
  by_cases huv : dist u v ≤ δ
  · simp only [huv, true_and]
    exact isOpen_lt continuous_const ((continuous_eval_const u).sub (continuous_eval_const v)).abs
  · simp only [huv, false_and, ofPred_false]
    exact isOpen_empty

/-- The tightness argument in the proof of [Hit26, Theorem 4.2.9]:
random continuous functions `Ψ_n` whose sup norms are bounded in probability
([Hit26, Equation (4.2.3)]) and whose moduli of continuity are small in
probability ([Hit26, Equation (4.2.4)]), both uniformly in `n`, form
a tight sequence in `C(U, ℝ)`. -/
theorem _root_.MeasureTheory.isTightMeasureSet_of_bounded_of_equicontinuous {Ω : Type*}
    [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Ψ : ℕ → Ω → C(U, ℝ)} (hΨ : ∀ n, Measurable (Ψ n))
    (hb : ∀ ε > 0, ∃ M : ℝ, ∀ n, P {ω | M < ‖Ψ n ω‖} ≤ ENNReal.ofReal ε)
    (he : ∀ ε > 0, ∀ a > 0, ∃ δ > 0, ∀ n,
      P {ω | ∃ u v : U, dist u v ≤ δ ∧ a < |Ψ n ω u - Ψ n ω v|} ≤ ENNReal.ofReal ε) :
    IsTightMeasureSet (Set.range fun n ↦ P.map (Ψ n)) := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  rcases eq_or_ne ε ⊤ with rfl | hεtop
  · exact ⟨∅, isCompact_empty, fun _ _ ↦ le_top⟩
  have hε' : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεtop
  obtain ⟨M, hM⟩ := hb (ε.toReal / 2) (by positivity)
  choose δ hδpos hδP using fun k : ℕ ↦
    he (ε.toReal / 2 / 2 / 2 ^ k) (by positivity) (1 / ((k : ℝ) + 1)) (by positivity)
  have hK := isCompact_arzelaAscoliSet (U := U) M hδpos
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  refine ⟨_, hK, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [Measure.map_apply (hΨ n) hK.isClosed.isOpen_compl.measurableSet]
  have hsub : Ψ n ⁻¹' (arzelaAscoliSet M δ fun k ↦ 1 / ((k : ℝ) + 1))ᶜ ⊆ {ω | M < ‖Ψ n ω‖} ∪
      ⋃ k, {ω | ∃ u v : U, dist u v ≤ δ k ∧ 1 / ((k : ℝ) + 1) < |Ψ n ω u - Ψ n ω v|} := by
    intro ω hω
    simp only [mem_preimage, mem_compl_iff, arzelaAscoliSet, mem_ofPred_eq, not_and, not_forall,
      not_le] at hω
    by_cases hn : ‖Ψ n ω‖ ≤ M
    · obtain ⟨k, u, v, huv, hlt⟩ := hω hn
      exact Or.inr (mem_iUnion.mpr ⟨k, u, v, huv, hlt⟩)
    · exact Or.inl (not_le.mp hn)
  calc P _ ≤ P ({ω | M < ‖Ψ n ω‖} ∪
        ⋃ k, {ω | ∃ u v : U, dist u v ≤ δ k ∧ 1 / ((k : ℝ) + 1) < |Ψ n ω u - Ψ n ω v|}) :=
        measure_mono hsub
    _ ≤ P {ω | M < ‖Ψ n ω‖} +
        ∑' k, P {ω | ∃ u v : U, dist u v ≤ δ k ∧ 1 / ((k : ℝ) + 1) < |Ψ n ω u - Ψ n ω v|} :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_iUnion_le _))
    _ ≤ ENNReal.ofReal (ε.toReal / 2) + ∑' k, ENNReal.ofReal (ε.toReal / 2 / 2 / 2 ^ k) :=
        add_le_add (hM n) (ENNReal.tsum_le_tsum fun k ↦ hδP k n)
    _ = ε := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ by positivity) (summable_geometric_two' _),
          tsum_geometric_two', ← ENNReal.ofReal_add (by positivity) (by positivity), add_halves,
          ENNReal.ofReal_toReal hεtop]

end SingularLearningTheory
