/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
public import SLT.PartialResolution.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
import SLT.PartialResolution.ExactTransport

/-!
# The chart sandwich

Two facts about a family of charts, neither of which needs injectivity:

* **The bridge** (`TransportsToOn.hasLLCExponentsOn_image_inter`): a chart's source-side
  exponents against the Jacobian-weighted measure become target-side exponents on the
  `U₀`-clipped image piece — the sublevel volumes are *pointwise equal* by exact transport.
* **The sandwich** (`sublevelVol_le_sum_of_cover_ae`, `sublevelVol_inter_le`): a finite
  null-cover bounds the sublevel volume by the sum over the clipped pieces, and each piece
  bounds it below. Subadditivity and monotonicity; overlap is harmless.

These are the two ingredients of the squeeze in the general theorem (`ChartFamilyExponents`).
The file ends with two null-set lemmas: removing a set of measure zero from the region changes
neither the sublevel volumes (`sublevelVol_diff_null`) nor the exponents
(`hasLLCExponentsOn_diff_null_iff`).
-/

public section

open MeasureTheory Set Asymptotics
open scoped ENNReal Topology

namespace SingularLearningTheory
open Analytic

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- **The transport bridge**: exact transport carries the exponents from
the weighted source to the clipped image piece, with *equal* sublevel
volumes. -/
theorem _root_.Analytic.TransportsToOn.hasLLCExponentsOn_image_inter
    {μX : Measure X} {μY : Measure Y} [SFinite μX] {K : Set X}
    {φ : X → Y} {J : X → ℝ≥0∞}
    (htr : TransportsToOn μX μY K φ J) {s : Set X}
    (hs : s ⊆ K) {U₀ : Set Y} {f : Y → ℝ} (hf : Measurable f)
    {lam theta : ℝ}
    (hsrc : HasLLCExponentsOn (μX.withDensity J) (s ∩ φ ⁻¹' U₀)
      (fun x => f (φ x)) lam theta) :
    HasLLCExponentsOn μY (U₀ ∩ φ '' s) f lam theta := by
  have hkey : sublevelVol μY (U₀ ∩ φ '' s) f =
      sublevelVol (μX.withDensity J) (s ∩ φ ⁻¹' U₀) fun x => f (φ x) := by
    funext ε
    rw [sublevelVol, sublevelVol]
    congr 1
    have himg : φ '' (s ∩ φ ⁻¹' U₀) = U₀ ∩ φ '' s := by
      rw [inter_comm, Set.image_preimage_inter]
    calc μY (U₀ ∩ φ '' s ∩ {y | f y ≤ ε})
        = μY ({y | f y ≤ ε} ∩ φ '' (s ∩ φ ⁻¹' U₀)) := by
          rw [himg, inter_comm]
      _ = ∫⁻ x in {x | f (φ x) ≤ ε} ∩ (s ∩ φ ⁻¹' U₀), J x ∂μX :=
          htr.sublevel_eq (inter_subset_left.trans hs) hf ε
      _ = (μX.withDensity J) (s ∩ φ ⁻¹' U₀ ∩ {x | f (φ x) ≤ ε}) := by
          rw [withDensity_apply' _ _, inter_comm]
  rw [HasLLCExponentsOn, hkey]
  exact hsrc

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **The cover bound**: a finite null-cover of `U₀` bounds its
sublevel volume by the sum over the clipped pieces.  Overlap is
harmless — this is subadditivity. -/
theorem sublevelVol_le_sum_of_cover_ae {ι : Type*} [Fintype ι]
    {U₀ N : Set α} {A : ι → Set α} {f : α → ℝ} (hU : μ U₀ ≠ ∞)
    (hN : μ N = 0) (hcover : U₀ \ N ⊆ ⋃ i, A i) (ε : ℝ) :
    sublevelVol μ U₀ f ε ≤ ∑ i, sublevelVol μ (U₀ ∩ A i) f ε := by
  have hfin : ∀ i, μ (U₀ ∩ A i ∩ {x | f x ≤ ε}) ≠ ∞ := fun i =>
    (measure_mono (inter_subset_left.trans inter_subset_left)).trans_lt
      hU.lt_top |>.ne
  have hsub : U₀ ∩ {x | f x ≤ ε} ⊆
      N ∪ ⋃ i, (U₀ ∩ A i ∩ {x | f x ≤ ε}) := by
    rintro x ⟨hxU, hxf⟩
    by_cases hxN : x ∈ N
    · exact Or.inl hxN
    · obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover ⟨hxU, hxN⟩)
      exact Or.inr (mem_iUnion.mpr ⟨i, ⟨hxU, hi⟩, hxf⟩)
  have hraw : μ (U₀ ∩ {x | f x ≤ ε}) ≤
      ∑ i, μ (U₀ ∩ A i ∩ {x | f x ≤ ε}) :=
    (measure_mono hsub).trans <| (measure_union_le _ _).trans <| by
      rw [hN, zero_add]
      exact measure_iUnion_fintype_le _ _
  rw [sublevelVol, show (∑ i, sublevelVol μ (U₀ ∩ A i) f ε) =
      (∑ i, μ (U₀ ∩ A i ∩ {x | f x ≤ ε})).toReal from
      (ENNReal.toReal_sum fun i _ => hfin i).symm]
  exact ENNReal.toReal_mono (ENNReal.sum_ne_top.mpr fun i _ => hfin i) hraw

/-- **The piece bound**: each clipped piece bounds the sublevel volume
below. -/
theorem sublevelVol_inter_le {U₀ A : Set α} {f : α → ℝ} (hU : μ U₀ ≠ ∞)
    (ε : ℝ) :
    sublevelVol μ (U₀ ∩ A) f ε ≤ sublevelVol μ U₀ f ε :=
  ENNReal.toReal_mono
    ((measure_mono inter_subset_left).trans_lt hU.lt_top).ne
    (measure_mono (inter_subset_inter_left _ inter_subset_left))

/-- **Null-set invariance.** Removing a set `N` of measure zero (no measurability
of `N` is assumed) from the localization region keeps the sublevel volume unchanged
at every threshold: the two localized sublevel sets differ by a subset of `N`,
which carries no measure. -/
theorem sublevelVol_diff_null {N : Set α} (hN : μ N = 0) (K : Set α)
    (f : α → ℝ) (ε : ℝ) :
    sublevelVol μ (K \ N) f ε = sublevelVol μ K f ε := by
  unfold sublevelVol
  congr 1
  have hset : (K \ N) ∩ {x | f x ≤ ε} = (K ∩ {x | f x ≤ ε}) \ N := by
    ext x; simp only [mem_inter_iff, mem_sdiff, mem_ofPred_eq]; tauto
  rw [hset, measure_sdiff_null hN]

/-- Consequently the sublevel-volume scaling exponents on a region and on the
region with a set of measure zero removed coincide. -/
theorem hasLLCExponentsOn_diff_null_iff {N : Set α} (hN : μ N = 0)
    {K : Set α} {f : α → ℝ} {lam theta : ℝ} :
    HasLLCExponentsOn μ (K \ N) f lam theta ↔ HasLLCExponentsOn μ K f lam theta := by
  unfold HasLLCExponentsOn
  rw [show sublevelVol μ (K \ N) f = sublevelVol μ K f from
    funext (sublevelVol_diff_null hN K f)]

end SingularLearningTheory
