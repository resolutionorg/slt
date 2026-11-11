/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import SLT.BayesGibbs.FiniteQuartet.Det
import SLT.FreeEnergy.Main
public import SLT.FreeEnergy.StochasticAsymptotics
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# Quantisation of a compact base

Finite quantisations of a compact base, with the denominators controlled by compact continuity and
pointwise positivity.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`, with its Gaussian bounds on the denominators replaced
by compact continuity and pointwise positivity.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

/-- A continuous function on a compact space is integrable for every finite measure. -/
theorem _root_.Continuous.integrable_of_compactSpace {X : Type*} [TopologicalSpace X]
    [CompactSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Continuous f) : Integrable f μ :=
  Integrable.of_bound hf.measurable.aestronglyMeasurable ‖(⟨f, hf⟩ : C(X, ℝ))‖
    (Filter.Eventually.of_forall fun x ↦ (⟨f, hf⟩ : C(X, ℝ)).norm_coe_le_norm x)

section Quantise

variable {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K] [MeasurableSpace K]
  [BorelSpace K]

/-- **Finite quantisation of a compact metric space**: for every `ε > 0` there is a measurable map
with finite range moving every point by less than `ε`. -/
private theorem exists_measurable_finiteRange_approx {ε : ℝ} (hε : 0 < ε) :
    ∃ q : K → K, Measurable q ∧ (Set.range q).Finite ∧ ∀ x, dist x (q x) < ε := by
  obtain ⟨e, he⟩ := TopologicalSpace.exists_dense_seq K
  have hcover : (Set.univ : Set K) ⊆ ⋃ k : ℕ, Metric.ball (e k) ε := fun x _ ↦ by
    obtain ⟨k, hk⟩ := he.exists_dist_lt x hε
    exact Set.mem_iUnion.2 ⟨k, Metric.mem_ball.2 hk⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun k ↦ Metric.ball (e k) ε)
    (fun k ↦ Metric.isOpen_ball) hcover
  refine ⟨SimpleFunc.nearestPt e (t.sup id), (SimpleFunc.nearestPt e (t.sup id)).measurable,
    (SimpleFunc.nearestPt e (t.sup id)).finite_range, fun x ↦ ?_⟩
  obtain ⟨k, hkt, hxk⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  have hkN : k ≤ t.sup id := Finset.le_sup (f := id) hkt
  have h := SimpleFunc.edist_nearestPt_le e x hkN
  rw [dist_comm, ← edist_lt_ofReal]
  refine lt_of_le_of_lt h (edist_lt_ofReal.2 ?_)
  rw [dist_comm]
  exact Metric.mem_ball.1 hxk

/-- A sequence of quantisations with mesh `1/(n+1)`. -/
theorem _root_.CompactSpace.exists_quantization_seq :
    ∃ q : ℕ → K → K, (∀ n, Measurable (q n)) ∧ (∀ n, (Set.range (q n)).Finite) ∧
      ∀ n x, dist x (q n x) < 1 / ((n : ℝ) + 1) := by
  choose q hq using fun n : ℕ ↦
    exists_measurable_finiteRange_approx (K := K) (ε := 1 / ((n : ℝ) + 1)) (by positivity)
  exact ⟨q, fun n ↦ (hq n).1, fun n ↦ (hq n).2.1, fun n ↦ (hq n).2.2⟩

omit [CompactSpace K] [Nonempty K] [MeasurableSpace K] [BorelSpace K] in
/-- Convergence of the quantised points. -/
theorem _root_.tendsto_quantize {q : ℕ → K → K} {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) (x : K) : Tendsto (fun n ↦ q n x) atTop (𝓝 x) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ ?_) hε
  rw [dist_comm]
  exact (hqε n x).le

omit [Nonempty K] in
/-- **Pathwise convergence under quantisation**: for a continuous `f` on the compact base,
`∫ f∘q_n dρ → ∫ f dρ` when the mesh tends to zero. -/
theorem _root_.MeasureTheory.tendsto_integral_comp_quantize (ρ : Measure K) [IsFiniteMeasure ρ]
    (f : C(K, ℝ))
    {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ ∫ x, f (q n x) ∂ρ) atTop (𝓝 (∫ x, f x ∂ρ)) := by
  refine tendsto_integral_of_dominated_convergence (fun _ ↦ ‖f‖)
    (fun n ↦ (f.continuous.measurable.comp (hq n)).aestronglyMeasurable) (integrable_const _)
    (fun n ↦ Filter.Eventually.of_forall fun x ↦ f.norm_coe_le_norm _)
    (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (f.continuous.tendsto x).comp (tendsto_quantize hε hqε x)

omit [MetricSpace K] [CompactSpace K] [Nonempty K] [BorelSpace K] in
/-- The pushforward `ρ.map q` has the same total mass. -/
theorem map_quantize_univ (ρ : Measure K) {q : K → K} (hq : Measurable q) :
    ρ.map q univ = ρ univ := by
  rw [Measure.map_apply hq MeasurableSet.univ, Set.preimage_univ]

end Quantise

/-! ### The compact-base denominator and its bounds -/

section CompactD

variable {K : Type*} [MetricSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {β lam : ℝ}

/-- `D_ρ(g) = ∫_K S_λ(g(x)) dρ(x)`. -/
@[expose] noncomputable def compactD (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) : ℝ :=
  ∫ x, frozenInner lam β (g x) ∂ρ

/-- `M₂,ρ(g) = ∫ S_{λ+1}(g) dρ / D_ρ(g)`. -/
@[expose] noncomputable def compactM2 (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) : ℝ :=
  (∫ x, frozenInner (lam + 1) β (g x) ∂ρ) / compactD β lam ρ g

/-- `H_ρ(g) = ∫ g S_{λ+1/2}(g) dρ / D_ρ(g)`. -/
@[expose] noncomputable def compactH (β lam : ℝ) (ρ : Measure K) (g : K → ℝ) : ℝ :=
  (∫ x, g x * frozenInner (lam + 1 / 2) β (g x) ∂ρ) / compactD β lam ρ g

variable (ρ : Measure K) [IsFiniteMeasure ρ]

theorem integrable_fluctuation_comp (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) :
    Integrable (fun x ↦ frozenInner lam β (g x)) ρ :=
  Continuous.integrable_of_compactSpace ρ
    ((continuous_frozenInner hlam hβ).comp g.continuous)

theorem compactD_pos (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ)) :
    0 < compactD β lam ρ g := by
  unfold compactD
  rw [integral_pos_iff_support_of_nonneg
    (fun x ↦ (frozenInner_pos hlam hβ (g x)).le)
    (integrable_fluctuation_comp ρ hβ hlam g)]
  have hs : Function.support (fun x ↦ frozenInner lam β (g x)) = univ := by
    ext x
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (frozenInner_pos hlam hβ (g x)).ne'
  rw [hs]
  exact pos_iff_ne_zero.mpr (Measure.measure_univ_ne_zero.mpr hρ)


omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactD_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : K → K}
    (hq : Measurable q) :
    compactD β lam (ρ.map q) g = ∫ x, frozenInner lam β (g (q x)) ∂ρ := by
  unfold compactD
  exact integral_map hq.aemeasurable
    ((continuous_frozenInner hlam hβ).comp g.continuous).measurable.aestronglyMeasurable

/-- The continuous map `x ↦ S_λ(g x)`. -/
private noncomputable def fluctuationC (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) :
    C(K, ℝ) :=
  ⟨fun x ↦ frozenInner lam β (g x), (continuous_frozenInner hlam hβ).comp g.continuous⟩

/-- The continuous map `x ↦ g x * S_λ(g x)`. -/
private noncomputable def fluctuationMulC (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) :
    C(K, ℝ) :=
  ⟨fun x ↦ g x * frozenInner lam β (g x),
    g.continuous.mul ((continuous_frozenInner hlam hβ).comp g.continuous)⟩

/-- **`D` converges under quantisation**: `D_{ρ∘q_n⁻¹}(g) → D_ρ(g)` for each continuous `g`. -/
theorem tendsto_compactD_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : ℕ → K → K}
    (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ compactD β lam (ρ.map (q n)) g) atTop (𝓝 (compactD β lam ρ g)) := by
  simp_rw [compactD_map ρ hβ hlam g (hq _)]
  exact tendsto_integral_comp_quantize ρ (fluctuationC β lam hβ hlam g) hq hε hqε


omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactM2_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : K → K}
    (hq : Measurable q) :
    compactM2 β lam (ρ.map q) g =
      (∫ x, frozenInner (lam + 1) β (g (q x)) ∂ρ) / compactD β lam (ρ.map q) g := by
  unfold compactM2
  rw [integral_map (f := fun x ↦ frozenInner (lam + 1) β (g x)) hq.aemeasurable
    ((continuous_frozenInner (by linarith) hβ).comp
      g.continuous).measurable.aestronglyMeasurable]

omit [CompactSpace K] [IsFiniteMeasure ρ] in
theorem compactH_map (hβ : 0 < β) (hlam : 0 < lam) (g : C(K, ℝ)) {q : K → K}
    (hq : Measurable q) :
    compactH β lam (ρ.map q) g =
      (∫ x, g (q x) * frozenInner (lam + 1 / 2) β (g (q x)) ∂ρ) / compactD β lam (ρ.map q) g := by
  unfold compactH
  rw [integral_map (f := fun x ↦ g x * frozenInner (lam + 1 / 2) β (g x)) hq.aemeasurable
    (g.continuous.mul ((continuous_frozenInner (by linarith) hβ).comp
        g.continuous)).measurable.aestronglyMeasurable]

/-- **`M₂` converges under quantisation.** -/
private theorem tendsto_compactM2_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ))
    {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ compactM2 β lam (ρ.map (q n)) g) atTop (𝓝 (compactM2 β lam ρ g)) := by
  simp_rw [compactM2_map ρ hβ hlam g (hq _)]
  exact (tendsto_integral_comp_quantize ρ (fluctuationC β (lam + 1) hβ (by linarith) g) hq hε
    hqε).div (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

/-- **`H` converges under quantisation.** -/
theorem tendsto_compactH_map (hβ : 0 < β) (hlam : 0 < lam) (hρ : ρ ≠ 0) (g : C(K, ℝ))
    {q : ℕ → K → K} (hq : ∀ n, Measurable (q n)) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hqε : ∀ n x, dist x (q n x) < ε n) :
    Tendsto (fun n ↦ compactH β lam (ρ.map (q n)) g) atTop (𝓝 (compactH β lam ρ g)) := by
  simp_rw [compactH_map ρ hβ hlam g (hq _)]
  exact (tendsto_integral_comp_quantize ρ (fluctuationMulC β (lam + 1 / 2) hβ (by linarith) g)
    hq hε hqε).div (tendsto_compactD_map ρ hβ hlam g hq hε hqε) (compactD_pos ρ hβ hlam hρ g).ne'

omit [CompactSpace K] [IsFiniteMeasure ρ] in
/-- The quantised measure is finitely supported: `ρ.map q` is carried by the finite set
`range q`. -/
private theorem map_quantize_compl_range {q : K → K} (hq : Measurable q)
    (hfin : (Set.range q).Finite) : ρ.map q (Set.range q)ᶜ = 0 := by
  rw [Measure.map_apply hq hfin.measurableSet.compl]
  have : q ⁻¹' (Set.range q)ᶜ = ∅ := by
    ext x
    simp
  rw [this, measure_empty]

end CompactD

end SingularLearningTheory.GaussianPosterior
