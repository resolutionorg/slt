/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.MonomialChart
public import SLT.Resolution.Orthant
import Mathlib.Order.CompletePartialOrder

/-!
# Finitely many monomialising charts covering the fibre over a compact part of `W₀`

Step 2 of the plan in [Hit26, Section 3.3.1]:
for a resolution `π : M → U` of `F = K φ₂ ∏ H_i` and a compact `T ⊆ U ∩ {K = 0}`, the fibre
`π⁻¹(T)` is compact (`π` is proper), each of its points has a monomialising chart
(`SingularLearningTheory.Resolution.exists_monomialChart`), and finitely many of the small open
boxes `(-a_i, a_i)^d`,
`a_i < b_i`, cover the fibre. The small box carries the bump of the partition of unity, the
large closed box `[-b_i, b_i]^d` is the chart cube of the atlas ([Wat09, Theorem 6.5] (1), with the
two box sizes the construction needs).

| Thesis | Lean |
| --- | --- |
| [Hit26, Section 3.3.1], plan, step 2 | |
| | `ChartCover`, `SingularLearningTheory.Resolution.exists_chartCover` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]

/-- The open box `(-a, a)^d`. -/
abbrev obox (d : ℕ) (a : ℝ) : Set (Fin d → ℝ) := Set.pi univ fun _ ↦ Ioo (-a) a

/-- Finitely many monomialising charts centred at points `P i` of the fibre `g⁻¹(T)`, with small
box radii `a i < b i`, whose small open boxes cover the fibre. -/
structure ChartCover (Kf φ₂ : (Fin d → ℝ) → ℝ) (H : Fin N → (Fin d → ℝ) → ℝ)
    (g : M → (Fin d → ℝ)) (T : Set (Fin d → ℝ)) where
  /-- The finite index type of the charts. -/
  I : Type
  [fintype : Fintype I]
  /-- The center of chart `i`, a point of the fiber $g^{-1}(T)$. -/
  P : I → M
  P_mem : ∀ i, g (P i) ∈ T
  /-- The monomializing chart (`SingularLearningTheory.MonomialChart`) centered at `P i`. -/
  ch : (i : I) → MonomialChart Kf φ₂ H g (P i)
  /-- The radius $a_i$ of the small open box $(-a_i, a_i)^d$ of chart `i`, which carries the bump
  of the partition of unity. It is less than $b_i$, the radius of the closed box $[-b_i, b_i]^d$ of
  the chart. -/
  a : I → ℝ
  a_pos : ∀ i, 0 < a i
  a_lt : ∀ i, a i < (ch i).b
  cover : g ⁻¹' T ⊆ ⋃ i, (ch i).e.symm '' obox d (a i)

attribute [instance] ChartCover.fintype

theorem isOpen_obox (d : ℕ) (a : ℝ) : IsOpen (obox d a) :=
  isOpen_set_pi finite_univ fun _ _ ↦ isOpen_Ioo

theorem zero_mem_obox {a : ℝ} (ha : 0 < a) : (0 : Fin d → ℝ) ∈ obox d a :=
  fun _ _ ↦ ⟨by simpa using ha, ha⟩

theorem MonomialChart.obox_half_subset_symm_source {Kf φ₂ : (Fin d → ℝ) → ℝ}
    {H : Fin N → (Fin d → ℝ) → ℝ}
    {g : M → (Fin d → ℝ)} {P : M} (c : MonomialChart Kf φ₂ H g P) :
    obox d (c.b / 2) ⊆ c.e.symm.source := by
  rw [OpenPartialHomeomorph.symm_source]
  refine (Set.pi_mono fun _ _ ↦ ?_).trans ((box_eq_pi d c.b).ge.trans
      (c.box_subset.trans c.O_subset))
  exact Ioo_subset_Icc_self.trans (Icc_subset_Icc (by linarith [c.b_pos]) (by linarith [c.b_pos]))

/-- [Hit26, Section 3.3.1], step 2 of the
plan: the fibre over a compact `T ⊆ U ∩ {K = 0}` is covered by finitely many monomialising
charts. -/
theorem Resolution.exists_chartCover {F Kf φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ}
    (R : Resolution F)
    (hF : ∀ w ∈ R.U, F w = Kf w * φ₂ w * ∏ i, H i w) (hK : AnalyticOnNhd ℝ Kf R.U)
    (hφ : AnalyticOnNhd ℝ φ₂ R.U) (hH : ∀ i, AnalyticOnNhd ℝ (H i) R.U) {T : Set (Fin d → ℝ)}
    (hT : IsCompact T) (hTV : T ⊆ R.U) (hTK : ∀ w ∈ T, Kf w = 0) :
    Nonempty (ChartCover Kf φ₂ H R.π T) := by
  have hfib : IsCompact (R.π ⁻¹' T) := R.proper T hTV hT
  have key : ∀ P : R.π ⁻¹' T, ∃ c : MonomialChart Kf φ₂ H R.π P,
      IsOpen (c.e.symm '' obox d (c.b / 2)) ∧ (P : R.M) ∈ c.e.symm '' obox d (c.b / 2) := by
    rintro ⟨P, hP⟩
    obtain ⟨c⟩ := R.exists_monomialChart hF hK hφ hH (hTK _ hP)
    refine ⟨c, ?_, ?_⟩
    · exact (c.e.symm.isOpen_image_iff_of_subset_source (MonomialChart.obox_half_subset_symm_source
        c)).mpr
        (isOpen_obox d _)
    · exact ⟨0, zero_mem_obox (half_pos c.b_pos), by simp [← c.e_P, c.e.left_inv c.mem_source]⟩
  choose ch hopen hmem using key
  obtain ⟨t, ht⟩ := hfib.elim_finite_subcover
    (fun P : R.π ⁻¹' T ↦ (ch P).e.symm '' obox d ((ch P).b / 2)) hopen
    (fun P hP ↦ Set.mem_iUnion.mpr ⟨⟨P, hP⟩, hmem ⟨P, hP⟩⟩)
  refine ⟨⟨{P : R.π ⁻¹' T // P ∈ t}, fun i ↦ (i.1 : R.M), fun i ↦ i.1.2,
    fun i ↦ ch i.1, fun i ↦ (ch i.1).b / 2, fun i ↦ half_pos (ch i.1).b_pos,
    fun i ↦ half_lt_self (ch i.1).b_pos, ?_⟩⟩
  intro P hP
  obtain ⟨Q, hQt, hPQ⟩ := Set.mem_iUnion₂.mp (ht hP)
  exact Set.mem_iUnion.mpr ⟨⟨Q, Finset.mem_coe.mp hQt⟩, hPQ⟩

end SingularLearningTheory
