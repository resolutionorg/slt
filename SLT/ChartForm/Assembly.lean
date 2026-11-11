/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.PartialResolution.Structural.Terminal
public import SLT.VolumeScaling.ChartFamily.Defs
import SLT.ChartForm.Chart
import SLT.Topology.MetricSpace.FiberCover
import SLT.ChartForm.Fibre
import Mathlib.MeasureTheory.Covering.Besicovitch

/-!
# The chart family of a monomial resolution

From a monomial resolution `R : PartialResolution n K N` of `K` on a compact neighbourhood `N` of
a zero `w` (every chart terminal, `IsMonomialChart`) to the chart family `MonomialChartCover` for
`|K|` at `w` that the volume computations of `Hironaka/VolumeScaling` take as input: at every
point `b` of the fibre of a chart over `w` the recentred chart on a small closed cube is a
`ResolutionChartData` with the exact transport of Lebesgue measure (`Chart.lean`); finitely many
of these cubes cover the compact fibre (`Cover.lean`), the leftovers `C_i` of the boxes have
compact images missing `w`, so `U = interior N \ ⋃ φ_i '' C_i` is an open neighbourhood of `w`,
the uncovered part `N₀ = N \ ⋃ φ_i '' dom i` is measurable and null (`R.cover`), and `U \ N₀` is
covered by the images of the chosen cubes. The index type is `Σ i, T_i` (the chosen cube centres);
it is nonempty because `U` is a nonempty open set and an empty family would make `U ⊆ N₀` null.
Every chart of the family is pinned to the recentred terminal chart it comes from (image,
dimension, both exponent vectors), and if `K ≥ 0` near `w` every loss exponent is even
(`Fibre.lean`).

This is the passage from [BM88, Theorem 4.4(3), p. 23] (compact subsets `L_j ⊆ W_j` with
`K = ⋃ π_j(L_j)`) to a finite family of charts centred over the base point.
-/

public section

open Set MeasureTheory Filter SingularLearningTheory
open scoped Topology ENNReal

namespace SingularLearningTheory
open Analytic

variable {n : ℕ}

/-- From a monomial resolution `R` of `K` on a compact neighbourhood `N` of a zero `w`, a finite
nonempty family of charts for `|K|` at `w`, each chart a terminal chart of `R` recentred at a
point of its fibre over `w` (image, dimension, loss and Jacobian exponents); if `K ≥ 0` near `w`
every loss exponent of every chart is even ([BM88, Theorem 4.4(3), p. 23] in chart form). -/
theorem exists_monomialChartCover_of_isMonomial {K : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ}
    {N : Set (Fin n → ℝ)} (hN : N ∈ 𝓝 w) (R : PartialResolution n K N) (hR : R.IsMonomial)
    (hKw : K w = 0) :
    ∃ (ι : Type) (_ : Fintype ι) (_ : Nonempty ι)
      (D : MonomialChartCover (Fin n → ℝ) volume (fun x => |K x|) w ι),
      ∀ α : ι, ∃ (i : R.ι) (b : Fin n → ℝ) (ϱ : ℝ) (e h : Fin n →₀ ℕ) (W : Set (Fin n → ℝ)),
        IsMonomialChart K (R.φ i) (R.dom i) e h W ∧ b ∈ R.dom i ∧ R.φ i b = w ∧ 0 < ϱ ∧
        Metric.closedBall b ϱ ⊆ W ∧
        (D.chart α).φ '' (D.chart α).K = R.φ i '' Metric.closedBall b ϱ ∧
        (∃ hd : (D.chart α).d = n,
          (∀ k : Fin n, (D.chart α).e (Fin.cast hd.symm k) = if b k = 0 then e k else 0) ∧
          ∀ k : Fin n, (D.chart α).h (Fin.cast hd.symm k) = if b k = 0 then h k else 0) ∧
        ((∀ᶠ x in 𝓝 w, 0 ≤ K x) → ∀ k, Even ((D.chart α).e k)) := by
  classical
  -- the terminal data of every chart of `R`
  choose e h W hc using hR
  -- the recentred chart at every fibre point
  have hchart : ∀ i, ∀ b ∈ R.dom i ∩ R.φ i ⁻¹' {w}, ∃ ϱ : ℝ, 0 < ϱ ∧
      Metric.closedBall b ϱ ⊆ W i ∧
      ∃ χ : ResolutionChartData (Fin n → ℝ) (fun x => |K x|) w,
        χ.φ '' χ.K = R.φ i '' Metric.closedBall b ϱ ∧
        TransportsToOn volume volume χ.K χ.φ (fun u => ENNReal.ofReal (χ.jacAbs u)) ∧
        ∃ hd : χ.d = n,
          (∀ k : Fin n, χ.e (Fin.cast hd.symm k) = if b k = 0 then e i k else 0) ∧
          ∀ k : Fin n, χ.h (Fin.cast hd.symm k) = if b k = 0 then h i k else 0 :=
    fun i b hb => (hc i).exists_resolutionChartData ((hc i).subset hb.1) hb.2 hKw
  choose ϱ hϱ hϱW χ hχimg hχT hχd using hchart
  -- total radii, positive on the fibre
  let ϱ' : R.ι → (Fin n → ℝ) → ℝ := fun i b =>
    if hb : b ∈ R.dom i ∩ R.φ i ⁻¹' {w} then ϱ i b hb else 1
  have hϱ' : ∀ i b (hb : b ∈ R.dom i ∩ R.φ i ⁻¹' {w}), ϱ' i b = ϱ i b hb := fun i b hb => by
    simp only [ϱ', dite_eq_left hb]
  have hφcont : ∀ i, ContinuousOn (R.φ i) (R.dom i) := fun i =>
    (hc i).analyticOnNhd.continuousOn.mono (hc i).subset
  -- the finite subcovers of the fibres
  have hcov : ∀ i, ∃ T : Finset (Fin n → ℝ), ↑T ⊆ R.dom i ∩ R.φ i ⁻¹' {w} ∧
      IsCompact (R.dom i \ ⋃ b ∈ T, Metric.ball b (ϱ' i b)) ∧
      IsCompact (R.φ i '' (R.dom i \ ⋃ b ∈ T, Metric.ball b (ϱ' i b))) ∧
      w ∉ R.φ i '' (R.dom i \ ⋃ b ∈ T, Metric.ball b (ϱ' i b)) := fun i =>
    IsCompact.exists_finset_fiber_cover (R.dom_compact i) (hφcont i) w (ϱ' i) fun b hb => by
      rw [hϱ' i b hb]; exact hϱ i b hb
  choose T hT hTC hTimg hTw using hcov
  -- the index type and the charts
  let ι : Type := Σ i : R.ι, {b : Fin n → ℝ // b ∈ T i}
  have hmem : ∀ α : ι, (α.2 : Fin n → ℝ) ∈ R.dom α.1 ∩ R.φ α.1 ⁻¹' {w} := fun α =>
    hT α.1 (Finset.mem_coe.mpr α.2.2)
  let chart : ι → ResolutionChartData (Fin n → ℝ) (fun x => |K x|) w := fun α =>
    χ α.1 α.2 (hmem α)
  -- the open set and the null set
  set U : Set (Fin n → ℝ) :=
    interior N \ ⋃ i, R.φ i '' (R.dom i \ ⋃ b ∈ T i, Metric.ball b (ϱ' i b)) with hUdef
  set N₀ : Set (Fin n → ℝ) := N \ ⋃ i, R.φ i '' R.dom i with hN₀def
  have hUopen : IsOpen U := isOpen_interior_sdiff_iUnion_image hTimg
  have hwU : w ∈ U := mem_interior_sdiff_iUnion_image hN hTw
  have hN₀m : MeasurableSet N₀ :=
    IsCompact.measurableSet_sdiff_iUnion_image R.K_compact fun i => R.image_compact i
  have hN₀null : volume N₀ = 0 := R.cover
  have hcover : U \ N₀ ⊆ ⋃ α : ι, (chart α).φ '' (chart α).K := by
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (interior_sdiff_subset_iUnion_image_closedBall T ϱ' hx)
    obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp hi
    refine mem_iUnion.mpr ⟨⟨i, b, hb⟩, ?_⟩
    have hbF : b ∈ R.dom i ∩ R.φ i ⁻¹' {w} := hT i (Finset.mem_coe.mpr hb)
    change x ∈ (χ i b _).φ '' (χ i b _).K
    rw [hχimg i b hbF]
    rwa [hϱ' i b hbF] at hxb
  -- the family is nonempty: an empty family would make the nonempty open `U` null
  have hne : Nonempty ι := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    have hsub : U ⊆ N₀ := fun x hx => by
      by_contra hxN₀
      have := hcover ⟨hx, hxN₀⟩
      rw [iUnion_of_empty] at this
      exact this
    exact (hUopen.measure_pos volume ⟨w, hwU⟩).ne'
      (measure_mono_null hsub hN₀null)
  refine ⟨ι, inferInstance, hne, ?_, ?_⟩
  · exact
      { chart := chart
        transport := fun α => hχT α.1 α.2 (hmem α)
        U := U
        U_open := hUopen
        w_mem_U := hwU
        N := N₀
        N_measurable := hN₀m
        N_null := hN₀null
        cover := hcover }
  · rintro ⟨i, b, hb⟩
    have hbF : b ∈ R.dom i ∩ R.φ i ⁻¹' {w} := hT i (Finset.mem_coe.mpr hb)
    obtain ⟨hd, hpin, hpinh⟩ := hχd i b hbF
    refine ⟨i, b, ϱ i b hbF, e i, h i, W i, hc i, hbF.1, hbF.2, hϱ i b hbF, hϱW i b hbF,
      hχimg i b hbF, ⟨hd, hpin, hpinh⟩, fun hpos k => ?_⟩
    -- evenness: transport the coordinate along `hd` and use the chart-level lemma
    have hk : k = Fin.cast hd.symm (Fin.cast hd k) := by simp
    rw [hk, hpin]
    split_ifs with hbk
    · have hcont : ContinuousAt (R.φ i) b :=
        ((hc i).analyticOnNhd b ((hc i).subset hbF.1)).continuousAt
      have hpos' : ∀ᶠ y in 𝓝 b, 0 ≤ K (R.φ i y) := by
        have := hcont.tendsto
        rw [hbF.2] at this
        exact this.eventually hpos
      exact (hc i).exponents_even_of_nonneg ((hc i).subset hbF.1) hpos' _ hbk
    · exact ⟨0, rfl⟩

end SingularLearningTheory
