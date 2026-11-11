/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.ChartFamily.Basic
public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Measure.WithDensity
import SLT.VolumeScaling.ArbitraryExponent
import SLT.VolumeScaling.Chart.Sandwich
import SLT.VolumeScaling.Comparison
import SLT.VolumeScaling.DensityCongr
import SLT.MeasureTheory.Measure.WithDensityPi
import SLT.VolumeScaling.SqueezeReadOff
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.Tactic.Positivity.Finset

/-!
# Chart-local read-off: the cube form

On a centered cube, the chart's loss-exponent monomial `mon e`, taken against the joint
Lebesgue measure reweighted by the chart's Jacobian-exponent product density `mon h`, has the
chart's sublevel-volume exponents `(lam, theta)` (`cube_readoff`).

This restates the arbitrary-exponent monomial read-off (`ArbitraryExponent`, which is phrased
over the product of one-dimensional power-weighted Lebesgue measures and proves its own
explicit least-ratio exponent) in the form the chart-local assembly uses: against the joint
weighted measure (via the product-density bridge) and in the chart's own `lam`/`theta` (least
active ratio and its multiplicity). The chart's natural exponent vectors are read as real
exponents. Around it: `lam_pos` (the least ratio is positive), `cube_finite` (the weighted
measure of a cube is finite), `source_readoff` and `cube_source_readoff` (the read-off for the
loss itself, with its bounded factor absorbed, on the part of the chart box sent into an open
neighborhood and on a centered box inside the chart box). The file then transports the
read-off onto the chart image clipped to the neighborhood (`chart_piece_scaling`), the
per-chart input of the general theorem (`ChartFamilyExponents`), and places the family
exponents on a leading chart's box image (`hasLLCExponentsOn_leading_subbox_image`).
-/

public section

open MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory

namespace ResolutionChartData

variable {Ambient : Type*} [TopologicalSpace Ambient] {f : Ambient → ℝ} {w : Ambient}

/-- The least active ratio is positive. -/
theorem lam_pos (χ : ResolutionChartData Ambient f w) : 0 < χ.lam := by
  refine (Finset.lt_inf'_iff _).mpr fun i hi => ?_
  have hei : χ.e i ≠ 0 := χ.mem_activeSet.mp hi
  rw [ResolutionChartData.ratio]
  exact div_pos (by positivity) (by exact_mod_cast Nat.pos_of_ne_zero hei)

/-- **Chart-local read-off, cube form.** On the centered cube `[-R,R]^d`, the
loss-exponent monomial `mon e`, against the joint Lebesgue measure reweighted by
the Jacobian-exponent product density `mon h`, has the chart's sublevel-volume
exponents `(lam, theta)`. -/
theorem cube_readoff (χ : ResolutionChartData Ambient f w) {R : ℝ} (hR : 0 < R) :
    HasLLCExponentsOn
      (volume.withDensity fun u => ENNReal.ofReal (mon χ.h u))
      (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R)
      (fun u => mon χ.e u)
      χ.lam (χ.theta : ℝ) := by
  -- The read-off over the product of one-dimensional weighted measures.
  have hbase := hasLLCExponentsOn_weighted_monomial_support_nat
    χ.e (fun i => (χ.h i : ℝ)) (fun i => by positivity)
    (fun i hei => χ.lam_le_ratio (χ.mem_activeSet.mpr hei.ne'))
    (by
      obtain ⟨i, hi, hr⟩ := χ.exists_ratio_eq_lam
      exact ⟨i, Nat.pos_of_ne_zero (χ.mem_activeSet.mp hi), hr⟩)
    hR
  -- Move to the joint weighted measure.
  rw [MeasureTheory.Measure.pi_withDensity_abs_rpow (fun i => (χ.h i : ℝ))] at hbase
  -- Match densities, the read-off function, and the multiplicity to the goal.
  have hden : (fun u : Fin χ.d → ℝ => ENNReal.ofReal (mon χ.h u))
      = fun u => ENNReal.ofReal (∏ i, |u i| ^ (χ.h i : ℝ)) := by
    funext u
    refine congrArg ENNReal.ofReal (Finset.prod_congr rfl fun i _ => ?_)
    rw [Real.rpow_natCast]
  have hfun : (fun u : Fin χ.d → ℝ => mon χ.e u)
      = fun u => ∏ i, |u i| ^ (χ.e i : ℝ) := by
    funext u
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_natCast]
  have htheta : (χ.theta : ℝ)
      = ((Finset.univ.filter fun i => 0 < χ.e i
          ∧ ((χ.h i : ℝ) + 1) / (χ.e i : ℝ) = χ.lam).card : ℝ) := by
    refine congrArg _ ?_
    unfold ResolutionChartData.theta ResolutionChartData.activeSet ResolutionChartData.ratio
    rw [Finset.filter_filter]
    refine congrArg Finset.card (Finset.filter_congr fun i _ => ?_)
    constructor
    · rintro ⟨hne, hr⟩; exact ⟨Nat.pos_of_ne_zero hne, hr⟩
    · rintro ⟨hpos, hr⟩; exact ⟨hpos.ne', hr⟩
  rw [hden, hfun, htheta]
  exact hbase

/-- The Jacobian-exponent product density has finite mass on a centered cube: it
is bounded there (a finite product of bounded coordinate powers), and the cube is
compact, hence of finite Lebesgue measure. This is the finiteness side condition
for sandwiching the cube read-off and for the density reweighting. -/
theorem cube_finite (χ : ResolutionChartData Ambient f w) {R : ℝ} (_hR : 0 < R) :
    (volume.withDensity fun u => ENNReal.ofReal (mon χ.h u))
        (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R) ≠ ⊤ := by
  have hmeas : MeasurableSet (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  rw [withDensity_apply _ hmeas]
  set C : ℝ := ∏ i, (max R 1) ^ (χ.h i) with hCdef
  have hbd : ∀ u ∈ (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R),
      ENNReal.ofReal (mon χ.h u) ≤ ENNReal.ofReal C := by
    intro u hu
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mon, hCdef]
    refine Finset.prod_le_prod₀ (fun i _ => by positivity) fun i _ => ?_
    have hui : |u i| ≤ R := by
      have := hu i (Set.mem_univ i)
      rw [Set.mem_Icc] at this
      rw [abs_le]; exact this
    exact pow_le_pow_left₀ (abs_nonneg _) (le_trans hui (le_max_left R 1)) _
  have hcpt : IsCompact (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  refine ne_top_of_le_ne_top
    (b := ENNReal.ofReal C * volume (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hcpt.measure_ne_top (μ := volume))) ?_
  calc (∫⁻ u in (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R),
          ENNReal.ofReal (mon χ.h u) ∂volume)
      ≤ ∫⁻ _ in (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R),
          ENNReal.ofReal C ∂volume :=
        setLIntegral_mono_ae measurable_const.aemeasurable
          (Filter.Eventually.of_forall hbd)
    _ = ENNReal.ofReal C * volume (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R) := by
        rw [setLIntegral_const]

/-- **Chart-local source read-off.** On the part `K ∩ φ⁻¹U` of the chart box that
the chart map sends into the open set `U` (a neighborhood of the fixed point),
the loss pulled back through the chart map, taken against the Jacobian-weighted
Lebesgue measure, has the chart's sublevel-volume exponents `(lam, theta)`. This
is the source-side input to the per-chart scaling: the transport identity
carries it onto the chart image. -/
theorem source_readoff (χ : ResolutionChartData Ambient f w) {U : Set Ambient}
    (hU : IsOpen U) (hwU : w ∈ U) :
    HasLLCExponentsOn (volume.withDensity fun u => ENNReal.ofReal (χ.jacAbs u))
      (χ.K ∩ χ.φ ⁻¹' U) (fun u => f (χ.φ u)) χ.lam (χ.theta : ℝ) := by
  obtain ⟨R, hRpos, hKR⟩ := χ.exists_cube_superset
  obtain ⟨r, hrpos, hrK, hrU⟩ := χ.exists_subbox hU hwU
  have hsubr : (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-r) r) ⊆ χ.K ∩ χ.φ ⁻¹' U :=
    Set.subset_inter hrK (Set.image_subset_iff.mp hrU)
  have hsubR : χ.K ∩ χ.φ ⁻¹' U ⊆ (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-R) R) :=
    Set.inter_subset_left.trans hKR
  -- The monomial read-off transfers from the cube to the chart region by sandwich.
  have hmon : HasLLCExponentsOn (volume.withDensity fun u => ENNReal.ofReal (mon χ.h u))
      (χ.K ∩ χ.φ ⁻¹' U) (fun u => mon χ.e u) χ.lam (χ.theta : ℝ) :=
    HasLLCExponentsOn.of_sandwich (χ.cube_readoff hrpos) (χ.cube_readoff hRpos)
      hsubr hsubR (χ.cube_finite hRpos)
  -- Replace the monomial by the loss (bounded-factor comparability on the box).
  have hloss : HasLLCExponentsOn (volume.withDensity fun u => ENNReal.ofReal (mon χ.h u))
      (χ.K ∩ χ.φ ⁻¹' U) (fun u => f (χ.φ u)) χ.lam (χ.theta : ℝ) :=
    hmon.of_bounded_unit' χ.cf_pos χ.Cf_pos
      (fun u hu => χ.loss_lb u (Set.mem_of_mem_inter_left hu))
      (fun u hu => χ.loss_ub u (Set.mem_of_mem_inter_left hu))
  -- Reweight the density from the product power monomial to the Jacobian factor.
  have hSmeas : MeasurableSet (χ.K ∩ χ.φ ⁻¹' U) :=
    χ.K_measurable.inter (IsOpen.preimage χ.φ_continuous hU).measurableSet
  have hmonmeas : Measurable fun u => ENNReal.ofReal (mon χ.h u) :=
    ENNReal.measurable_ofReal.comp (by unfold mon; fun_prop)
  have hjacmeas : Measurable fun u => ENNReal.ofReal (χ.jacAbs u) :=
    ENNReal.measurable_ofReal.comp χ.jacAbs_measurable
  have hfin : (volume.withDensity fun u => ENNReal.ofReal (mon χ.h u))
      (χ.K ∩ χ.φ ⁻¹' U) ≠ ⊤ :=
    ne_top_of_le_ne_top (χ.cube_finite hRpos) (measure_mono hsubR)
  exact (hasLLCExponentsOn_withDensity_congr (μ := volume) (K := χ.K ∩ χ.φ ⁻¹' U)
    (f := fun u => f (χ.φ u)) (w := fun u => mon χ.h u) (jac := χ.jacAbs)
    (c := χ.cJ) (C := χ.CJ) hSmeas χ.loss_measurable hmonmeas hjacmeas χ.cJ_pos
    χ.CJ_pos.le (fun u hu => χ.jac_lb u (Set.mem_of_mem_inter_left hu))
    (fun u hu => χ.jac_ub u (Set.mem_of_mem_inter_left hu)) hfin).mpr hloss

/-- **Chart-local source read-off on a centered box inside the chart box.** On a
box `[-r, r]^d` contained in the chart box `K`, the loss pulled back through the
chart map, taken against the Jacobian-weighted Lebesgue measure, has the chart's
sublevel-volume exponents `(lam, theta)`. This is the box version of
`source_readoff`: because the box itself is the region of interest there is no
sandwich step — the cube read-off lands directly on it. It is the source-side
input to placing the family coefficient on a leading chart's subbox image. -/
theorem cube_source_readoff (χ : ResolutionChartData Ambient f w) {r : ℝ}
    (hr : 0 < r) (hrK : (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-r) r) ⊆ χ.K) :
    HasLLCExponentsOn (volume.withDensity fun u => ENNReal.ofReal (χ.jacAbs u))
      (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-r) r) (fun u => f (χ.φ u))
      χ.lam (χ.theta : ℝ) := by
  -- Replace the monomial by the loss (bounded-factor comparability on the box).
  have hloss : HasLLCExponentsOn (volume.withDensity fun u => ENNReal.ofReal (mon χ.h u))
      (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-r) r) (fun u => f (χ.φ u)) χ.lam (χ.theta : ℝ) :=
    (χ.cube_readoff hr).of_bounded_unit' χ.cf_pos χ.Cf_pos
      (fun u hu => χ.loss_lb u (hrK hu)) (fun u hu => χ.loss_ub u (hrK hu))
  -- Reweight the density from the product power monomial to the Jacobian factor.
  have hSmeas : MeasurableSet (Set.univ.pi fun _ : Fin χ.d => Set.Icc (-r) r) :=
    MeasurableSet.univ_pi fun _ => measurableSet_Icc
  have hmonmeas : Measurable fun u => ENNReal.ofReal (mon χ.h u) :=
    ENNReal.measurable_ofReal.comp (by unfold mon; fun_prop)
  have hjacmeas : Measurable fun u => ENNReal.ofReal (χ.jacAbs u) :=
    ENNReal.measurable_ofReal.comp χ.jacAbs_measurable
  exact (hasLLCExponentsOn_withDensity_congr (μ := volume)
    (K := Set.univ.pi fun _ : Fin χ.d => Set.Icc (-r) r)
    (f := fun u => f (χ.φ u)) (w := fun u => mon χ.h u) (jac := χ.jacAbs)
    (c := χ.cJ) (C := χ.CJ) hSmeas χ.loss_measurable hmonmeas hjacmeas χ.cJ_pos
    χ.CJ_pos.le (fun u hu => χ.jac_lb u (hrK hu))
    (fun u hu => χ.jac_ub u (hrK hu)) (χ.cube_finite hr)).mpr hloss

end ResolutionChartData

namespace MonomialChartCover

variable {Ambient : Type*} [MeasurableSpace Ambient] [TopologicalSpace Ambient]
  {μ : Measure Ambient} {f : Ambient → ℝ} {w : Ambient} {ι : Type*}
  [Fintype ι] [Nonempty ι]

/-- **Per-chart scaling on the chart image.** Transporting the chart-local source
read-off through the chart's change-of-variables identity gives that, on the
chart's image intersected with the neighborhood, the loss has the chart's
sublevel-volume exponents against the ambient measure. (The ambient loss is
assumed measurable, as a polynomial or analytic loss is.) -/
theorem chart_piece_scaling (D : MonomialChartCover Ambient μ f w ι) (α : ι)
    (hf : Measurable f) :
    HasLLCExponentsOn μ (D.U ∩ (D.chart α).φ '' (D.chart α).K) f
      (D.chart α).lam ((D.chart α).theta : ℝ) :=
  (D.transport α).hasLLCExponentsOn_image_inter Set.Subset.rfl hf
    ((D.chart α).source_readoff D.U_open D.w_mem_U)

/-- **The family coefficient on a leading chart's subbox image.** Some chart `β`
realizes the combinatorial least exponent and its multiplicity (the family
coefficient `(combLam, combTheta)`); for that chart there is a radius `r > 0`
such that, on the image under the chart map of the centered box `[-r, r]^d`, the
loss has the family coefficient as its sublevel-volume exponents against the
ambient measure. The proof chooses `r` so that the image lies inside the
neighborhood `D.U`, but the statement records only the exponents; the variant
recording the inclusion as well is `hasLLCExponentsOn_leading_subbox_image_subset`
(`CompactLocalize`), proved by the same argument. -/
theorem hasLLCExponentsOn_leading_subbox_image (D : MonomialChartCover Ambient μ f w ι)
    (hf : Measurable f) :
    ∃ β : ι, ∃ r > 0,
      HasLLCExponentsOn μ
        ((D.chart β).φ '' Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r)
        f D.combLam (D.combTheta : ℝ) := by
  obtain ⟨β, hlam, htheta⟩ := D.exists_leading
  obtain ⟨r, hrpos, hrK, hrU⟩ := (D.chart β).exists_subbox D.U_open D.w_mem_U
  refine ⟨β, r, hrpos, ?_⟩
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
