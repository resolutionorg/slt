/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.ChartFamily.Basic
public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.ChartFamily.Exponents
import SLT.VolumeScaling.Chart.Local
import SLT.VolumeScaling.Chart.Sandwich
import SLT.VolumeScaling.CompactLocalize
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.Tactic.Positivity.Finset

/-!
# Localizing the sublevel-volume exponents to closed cubes; the exponents as numbers

The general theorem `MonomialChartCover.hasLLCExponentsOn_cover`
(`SLT/VolumeScaling/ChartFamily/Exponents.lean`) gives the sublevel-volume
exponents `(combLam, combTheta)` of a chart family on its open set `D.U`: the volume of `{f ≤ ε}` in
`D.U` is of the order `ε^{combLam} (log 1/ε)^{combTheta − 1}` as `ε ↓ 0`. Here: the relation
localizes to every closed cube `closedBall w r ⊆ D.U`, since a leading chart has a centred subbox
whose image lies in the open ball `ball w r` and carries the exponents (`exists_subbox` for the
ball, `cube_source_readoff` transported through the chart's change of variables, the argument of
`hasLLCExponentsOn_leading_subbox_image_subset` with the open set free), and a set squeezed
between that image and `D.U` inherits them (`hasLLCExponentsOn_of_between`); `combLam` is the cast
of a positive rational, the least ratio `(h_i + 1)/e_i` of a leading chart; `1 ≤ combTheta` and
`combTheta ≤ n` when every chart has dimension `n`; and two families for the same loss at the same
point read off the same pair, by `HasLLCExponentsOn.unique` on a common closed cube. Two small
tools: a family's open set can be cut down to an open set containing `w` (`restrictU`, charts
unchanged), and the relation only sees the loss on the set (`hasLLCExponentsOn_congr_eqOn`).

These are the properties of the local learning coefficient and its multiplicity of [Watanabe's
singular learning theory][Wat09] that the existence theorem
(`LearningCoefficientExistence.lean`) states.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory

/-- The sublevel-volume relation sees the loss only on the set. -/
theorem hasLLCExponentsOn_congr_eqOn {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} {f g : α → ℝ} (h : EqOn f g s) {lam theta : ℝ} :
    HasLLCExponentsOn μ s f lam theta ↔ HasLLCExponentsOn μ s g lam theta := by
  have hvol : sublevelVol μ s f = sublevelVol μ s g := by
    funext ε
    unfold sublevelVol
    congr 2
    ext x
    constructor
    · rintro ⟨hs, hle⟩
      refine ⟨hs, ?_⟩
      change g x ≤ ε
      rw [← h hs]
      exact hle
    · rintro ⟨hs, hle⟩
      refine ⟨hs, ?_⟩
      change f x ≤ ε
      rw [h hs]
      exact hle
  unfold HasLLCExponentsOn
  rw [hvol]

namespace MonomialChartCover

section Generic

variable {Ambient : Type*} [MeasurableSpace Ambient] [TopologicalSpace Ambient]
  {μ : Measure Ambient} {f : Ambient → ℝ} {w : Ambient} {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The family with its open set cut down to an open set containing `w`: same charts, same
transports, same null set. -/
def restrictU (D : MonomialChartCover Ambient μ f w ι) {V : Set Ambient} (hV : IsOpen V)
    (hwV : w ∈ V) : MonomialChartCover Ambient μ f w ι where
  chart := D.chart
  transport := D.transport
  U := D.U ∩ V
  U_open := D.U_open.inter hV
  w_mem_U := ⟨D.w_mem_U, hwV⟩
  N := D.N
  N_measurable := D.N_measurable
  N_null := D.N_null
  cover := fun _ hx => D.cover ⟨hx.1.1, hx.2⟩

@[simp] theorem restrictU_chart (D : MonomialChartCover Ambient μ f w ι) {V : Set Ambient}
    (hV : IsOpen V) (hwV : w ∈ V) : (D.restrictU hV hwV).chart = D.chart := rfl

@[simp] theorem restrictU_U (D : MonomialChartCover Ambient μ f w ι) {V : Set Ambient}
    (hV : IsOpen V) (hwV : w ∈ V) : (D.restrictU hV hwV).U = D.U ∩ V := rfl

theorem restrictU_combLam (D : MonomialChartCover Ambient μ f w ι) {V : Set Ambient}
    (hV : IsOpen V) (hwV : w ∈ V) : (D.restrictU hV hwV).combLam = D.combLam := rfl

theorem restrictU_combTheta (D : MonomialChartCover Ambient μ f w ι) {V : Set Ambient}
    (hV : IsOpen V) (hwV : w ∈ V) : (D.restrictU hV hwV).combTheta = D.combTheta := rfl

end Generic

variable {n : ℕ} {f : (Fin n → ℝ) → ℝ} {w : Fin n → ℝ} {ι : Type} [Fintype ι] [Nonempty ι]

/-- The leading subbox inside a given open set: for an open `V ∋ w`, a leading chart and a centred
subbox whose image lies in `V` and carries the family's exponents (the argument of
`hasLLCExponentsOn_leading_subbox_image_subset` with the open set free). -/
theorem exists_leading_subbox_image_subset_of_isOpen
    (D : MonomialChartCover (Fin n → ℝ) volume f w ι) (hf : Measurable f) {V : Set (Fin n → ℝ)}
    (hV : IsOpen V) (hwV : w ∈ V) :
    ∃ β : ι, ∃ r > 0,
      (D.chart β).φ '' (Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r) ⊆ V ∧
      HasLLCExponentsOn volume
        ((D.chart β).φ '' Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r)
        f D.combLam (D.combTheta : ℝ) := by
  obtain ⟨β, hlam, htheta⟩ := D.exists_leading
  obtain ⟨r, hrpos, hrK, hrV⟩ := (D.chart β).exists_subbox hV hwV
  refine ⟨β, r, hrpos, hrV, ?_⟩
  have hsub : (Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r) ⊆ (D.chart β).φ ⁻¹' V :=
    Set.image_subset_iff.mp hrV
  have hsrc : HasLLCExponentsOn
      (volume.withDensity fun u => ENNReal.ofReal ((D.chart β).jacAbs u))
      ((Set.univ.pi fun _ : Fin (D.chart β).d => Set.Icc (-r) r) ∩ (D.chart β).φ ⁻¹' V)
      (fun u => f ((D.chart β).φ u)) (D.chart β).lam ((D.chart β).theta : ℝ) := by
    rw [Set.inter_eq_left.mpr hsub]
    exact (D.chart β).cube_source_readoff hrpos hrK
  have htr := (D.transport β).hasLLCExponentsOn_image_inter hrK hf hsrc
  rw [Set.inter_eq_right.mpr hrV, hlam, htheta] at htr
  exact htr

/-- Localization to a closed cube: on every closed cube `closedBall w r ⊆ D.U` the loss has the
family's exponents (`hasLLCExponentsOn_of_between`). -/
theorem hasLLCExponentsOn_closedBall (D : MonomialChartCover (Fin n → ℝ) volume f w ι)
    (hf : Measurable f) (hU : volume D.U ≠ ⊤) {r : ℝ} (hr : 0 < r)
    (hsub : Metric.closedBall w r ⊆ D.U) :
    HasLLCExponentsOn volume (Metric.closedBall w r) f D.combLam (D.combTheta : ℝ) := by
  obtain ⟨β, ρ, -, himg, hL⟩ :=
    D.exists_leading_subbox_image_subset_of_isOpen hf Metric.isOpen_ball (Metric.mem_ball_self hr)
  exact hasLLCExponentsOn_of_between hL (D.hasLLCExponentsOn_cover hf hU)
    (himg.trans Metric.ball_subset_closedBall) hsub hU

/-- Rationality: the combinatorial least exponent is the cast of a positive rational, the least
ratio `(h_i + 1)/e_i` of a leading chart. -/
theorem exists_rat_combLam (D : MonomialChartCover (Fin n → ℝ) volume f w ι) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) = D.combLam := by
  obtain ⟨β, hlam, -⟩ := D.exists_leading
  obtain ⟨i, hi, hratio⟩ := (D.chart β).exists_ratio_eq_lam
  refine ⟨(((D.chart β).h i : ℚ) + 1) / ((D.chart β).e i : ℚ), ?_, ?_⟩
  · have hei : (D.chart β).e i ≠ 0 := (D.chart β).mem_activeSet.mp hi
    exact div_pos (by positivity) (by exact_mod_cast Nat.pos_of_ne_zero hei)
  · rw [← hlam, ← hratio, ResolutionChartData.ratio]
    push_cast
    rfl

/-- The combinatorial multiplicity is at least one. -/
theorem one_le_combTheta (D : MonomialChartCover (Fin n → ℝ) volume f w ι) : 1 ≤ D.combTheta := by
  obtain ⟨β, -, htheta⟩ := D.exists_leading
  rw [← htheta]
  exact (D.chart β).theta_pos

/-- The combinatorial multiplicity is at most `n` when every chart has dimension `n`. -/
theorem combTheta_le_of_forall_d_eq (D : MonomialChartCover (Fin n → ℝ) volume f w ι)
    (hd : ∀ α, (D.chart α).d = n) : D.combTheta ≤ n := by
  obtain ⟨β, -, htheta⟩ := D.exists_leading
  rw [← htheta, ResolutionChartData.theta]
  calc _ ≤ Fintype.card (Fin (D.chart β).d) := Finset.card_le_univ _
    _ = n := by rw [Fintype.card_fin, hd β]

/-- Consistency: two chart families for the same loss at the same point read off the same pair
`(combLam, combTheta)` (`HasLLCExponentsOn.unique` on a common closed cube). -/
theorem combLam_eq_and_combTheta_eq {ι' : Type} [Fintype ι'] [Nonempty ι']
    (D : MonomialChartCover (Fin n → ℝ) volume f w ι)
    (D' : MonomialChartCover (Fin n → ℝ) volume f w ι') (hf : Measurable f)
    (hU : volume D.U ≠ ⊤) (hU' : volume D'.U ≠ ⊤) :
    D.combLam = D'.combLam ∧ D.combTheta = D'.combTheta := by
  obtain ⟨r, hr, hsub⟩ :=
    Metric.isOpen_iff.mp (D.U_open.inter D'.U_open) w ⟨D.w_mem_U, D'.w_mem_U⟩
  have hball : Metric.closedBall w (r / 2) ⊆ D.U ∩ D'.U :=
    (Metric.closedBall_subset_ball (half_lt_self hr)).trans hsub
  have h1 := D.hasLLCExponentsOn_closedBall hf hU (half_pos hr) (hball.trans inter_subset_left)
  have h2 := D'.hasLLCExponentsOn_closedBall hf hU' (half_pos hr) (hball.trans inter_subset_right)
  obtain ⟨hl, ht⟩ := h1.unique h2
  exact ⟨hl, Nat.cast_injective ht⟩

end MonomialChartCover

end SingularLearningTheory
