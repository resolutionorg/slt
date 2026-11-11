/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.ChartFamily.Basic
public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.Chart.Local
import SLT.VolumeScaling.Chart.Sandwich
import SLT.VolumeScaling.SqueezeReadOff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Localizing the volume-scaling exponents to a compact set between two Θ-regions

The general theorem (`ChartFamilyExponents`) produces the loss's volume-scaling exponents on
the open working neighborhood; the applications need them on a compact neighborhood. This file
bridges them without any tail estimate, by squeezing between two regions that *already* carry
the exponents: the image of a small centered box under a leading chart, which lies inside the
neighborhood and carries the family exponents by the chart-local read-off
(`hasLLCExponentsOn_leading_subbox_image_subset`), and the open neighborhood itself (the
general theorem). Any set sandwiched between an inner and an outer Θ-region inherits the
exponents by monotonicity of the sublevel volume.
-/

public section

open MeasureTheory Set Filter
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}

/-- **Squeeze between two Θ-regions.** If the loss has volume-scaling exponents `(λ, θ)` on both
an inner region `L` and an outer region `U` of finite measure, then any `K` with `L ⊆ K ⊆ U` has
them too: its sublevel volume is squeezed between the two by monotonicity. -/
theorem hasLLCExponentsOn_of_between {L K U : Set α} {lam theta : ℝ}
    (hL : HasLLCExponentsOn μ L f lam theta) (hU : HasLLCExponentsOn μ U f lam theta)
    (hLK : L ⊆ K) (hKU : K ⊆ U) (hUfin : μ U ≠ ∞) :
    HasLLCExponentsOn μ K f lam theta := by
  have hKfin : μ K ≠ ∞ := ne_top_of_le_ne_top hUfin (measure_mono hKU)
  exact HasLLCExponentsOn.of_squeeze hL hU
    (Eventually.of_forall (sublevelVol_nonneg _ _ _))
    (Eventually.of_forall fun ε => sublevelVol_mono_set hLK hKfin f ε)
    (Eventually.of_forall fun ε => sublevelVol_mono_set hKU hUfin f ε)

namespace MonomialChartCover

variable {Ambient : Type*} [MeasurableSpace Ambient] [TopologicalSpace Ambient]
  {μ : Measure Ambient} {f : Ambient → ℝ} {w : Ambient}
  {ι : Type*} [Fintype ι] [Nonempty ι]

/-- Strengthening of `hasLLCExponentsOn_leading_subbox_image`: the leading chart's centered-subbox
image — on which the loss carries the family coefficient `(combLam, combTheta)` — additionally
lies inside the working neighborhood `D.U`. Same proof, exposing the subbox-image inclusion. -/
theorem hasLLCExponentsOn_leading_subbox_image_subset
    (D : MonomialChartCover Ambient μ f w ι) (hf : Measurable f) :
    ∃ β : ι, ∃ r > 0,
      (D.chart β).φ '' (Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r) ⊆ D.U ∧
      HasLLCExponentsOn μ
        ((D.chart β).φ '' Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r)
        f D.combLam (D.combTheta : ℝ) := by
  obtain ⟨β, hlam, htheta⟩ := D.exists_leading
  obtain ⟨r, hrpos, hrK, hrU⟩ := (D.chart β).exists_subbox D.U_open D.w_mem_U
  refine ⟨β, r, hrpos, hrU, ?_⟩
  have hsub : (Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r) ⊆ (D.chart β).φ ⁻¹' D.U :=
    Set.image_subset_iff.mp hrU
  have hsrc : HasLLCExponentsOn
      (volume.withDensity fun u => ENNReal.ofReal ((D.chart β).jacAbs u))
      ((Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r) ∩ (D.chart β).φ ⁻¹' D.U)
      (fun u => f ((D.chart β).φ u)) (D.chart β).lam ((D.chart β).theta : ℝ) := by
    rw [Set.inter_eq_left.mpr hsub]
    exact (D.chart β).cube_source_readoff hrpos hrK
  have htr := (D.transport β).hasLLCExponentsOn_image_inter hrK hf hsrc
  rw [Set.inter_eq_right.mpr hrU, hlam, htheta] at htr
  exact htr

end MonomialChartCover

end SingularLearningTheory
