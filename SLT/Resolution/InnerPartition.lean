/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.Chart.Cover
public import SLT.Geometry.Manifold.ChartBump
public import SLT.Geometry.Manifold.Cutoff
public import SLT.Resolution.Surjective
import Mathlib.Order.CompletePartialOrder
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# The inner partition of unity on a resolution

[Hit26, Section 3.3.1], the partition of unity
`ρ_α` subordinate to the charts of one resolution (definition
[Hit26, Definition 3.3.6]), chosen as in [Wat09, Theorem 6.5] (3)–(4)
so that every chart weight is positive at its centre. Built from bumps through the charts
(`OpenPartialHomeomorph.chartBump`) normalised on the open set `O` covered by the small boxes, and
multiplied by a
cut-off `κ̂ ∘ g` with `κ̂ = 1` on the compact base set `Bcl` and support in the saturated open
set `V \ g(M \ O)`, so that the normalised functions are smooth on all of `M` and sum to `1` over
`g⁻¹(Bcl)`.

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 3.3.6] on the resolution, positive at the | |
| chart centres ([Wat09, Theorem 6.5] (4)) | `SingularLearningTheory.ChartCover.InnerPartition`,
`SingularLearningTheory.ChartCover.exists_innerPartition` |
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d N : ℕ} {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {Kf φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ} {g : M → (Fin d → ℝ)}
  {T : Set (Fin d → ℝ)}

/-- The open set of `M` covered by the small boxes of a chart cover. -/
@[expose] def ChartCover.smallUnion (C : ChartCover Kf φ₂ H g T) : Set M :=
  ⋃ i, (C.ch i).e.symm '' obox d (C.a i)

/-- A partition of unity on `M` subordinate to the small boxes of the chart cover `C`: smooth in
every chart of the maximal analytic atlas, nonnegative, summing to `1` over `g⁻¹(Bcl)`, and
positive at every chart centre. -/
structure ChartCover.InnerPartition (C : ChartCover Kf φ₂ H g T) (Bcl : Set (Fin d → ℝ)) where
  /-- The functions $\rho_i$ on $M$, one for each chart $i$ of the cover, each supported in
  the image of its chart's small box. -/
  ρ : C.I → M → ℝ
  smooth : ∀ i, ∀ e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω M,
    ContDiffOn ℝ ∞ (ρ i ∘ e'.symm) e'.target
  continuous : ∀ i, Continuous (ρ i)
  nonneg : ∀ i P, 0 ≤ ρ i P
  support : ∀ i P, ρ i P ≠ 0 → P ∈ (C.ch i).e.symm '' obox d (C.a i)
  sum_eq_one : ∀ P, g P ∈ Bcl → ∑ i, ρ i P = 1
  pos_centre : ∀ i, 0 < ρ i (C.P i)

/-- [Hit26, Section 3.3.1], the inner
partition of unity, positive at the chart centres ([Wat09, Theorem 6.5] (4)): for a compact `Bcl ⊆
U` whose fibre lies in the union `O` of the small boxes and which contains the images of the
chart centres. -/
theorem ChartCover.exists_innerPartition {F : (Fin d → ℝ) → ℝ} {R : Resolution F}
    (C : ChartCover Kf φ₂ H R.π T)
    {Bcl : Set (Fin d → ℝ)} (hBcl : IsCompact Bcl) (hBV : Bcl ⊆ R.U)
    (hBO : R.π ⁻¹' Bcl ⊆ C.smallUnion) (hPB : ∀ i, R.π (C.P i) ∈ Bcl) :
    Nonempty (ChartCover.InnerPartition C Bcl) := by
  have hg : Continuous R.π := R.continuous_π
  -- bumps on the model space, supported in the small open boxes
  choose f hf_supp hf_smooth hf_range using
    fun i ↦ (isOpen_obox d (C.a i)).exists_contDiff_support_eq (n := ⊤)
  have hf0 : ∀ i u, 0 ≤ f i u := fun i u ↦ (hf_range i ⟨u, rfl⟩).1
  have hf_pos : ∀ i, ∀ u ∈ obox d (C.a i), 0 < f i u := fun i u hu ↦
    lt_of_le_of_ne (hf0 i u) (by rw [← hf_supp i] at hu; exact hu.symm)
  have hobox_box : ∀ i, obox d (C.a i) ⊆ box d (C.a i) := fun i ↦
    (Set.pi_mono fun _ _ ↦ Ioo_subset_Icc_self).trans (box_eq_pi d _).ge
  have htsupp_box : ∀ i, tsupport (f i) ⊆ box d (C.a i) := fun i ↦ by
    rw [tsupport, hf_supp i]
    exact closure_minimal (hobox_box i) isClosed_Icc
  have hbox_target : ∀ i, box d (C.a i) ⊆ (C.ch i).e.target := fun i ↦
    (Set.Icc_subset_Icc (fun _ ↦ neg_le_neg (C.a_lt i).le) (fun _ ↦ (C.a_lt i).le)).trans
      ((C.ch i).box_subset.trans (C.ch i).O_subset)
  have htsupp : ∀ i, tsupport (f i) ⊆ (C.ch i).e.target := fun i ↦
    (htsupp_box i).trans (hbox_target i)
  have hcpt : ∀ i, HasCompactSupport (f i) := fun i ↦
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _)
      (htsupp_box i)
  -- the bumps transported to `M`
  obtain ⟨θ, hθ⟩ :
      ∃ θ : C.I → R.M → ℝ, ∀ i, θ i = OpenPartialHomeomorph.chartBump (C.ch i).e (f i) :=
      ⟨_, fun _ ↦ rfl⟩
  have hθc : ∀ i, Continuous (θ i) := fun i ↦ by
    rw [hθ]; exact OpenPartialHomeomorph.continuous_chartBump _ _ (hf_smooth i).continuous
        (htsupp i) (hcpt i)
  have hθ0 : ∀ i P, 0 ≤ θ i P := fun i P
      ↦ by rw [hθ]; exact OpenPartialHomeomorph.chartBump_nonneg _ _ (hf0 i) P
  have hθsm : ∀ i, ∀ e' ∈ IsManifold.maximalAtlas 𝓘(ℝ, Fin d → ℝ) ω R.M,
      ContDiffOn ℝ ∞ (θ i ∘ e'.symm) e'.target := fun i e' he' ↦ by
    rw [hθ]
    exact OpenPartialHomeomorph.contDiffOn_chartBump_comp_symm _ _ (C.ch i).he he' (hf_smooth i)
        (htsupp i) (hcpt i)
  have hθsupp : ∀ i P, θ i P ≠ 0 → P ∈ (C.ch i).e.symm '' obox d (C.a i) := fun i P h ↦ by
    rw [hθ] at h
    obtain ⟨hPs, hPe⟩ := OpenPartialHomeomorph.mem_source_of_chartBump_ne_zero _ _ h
    rw [hf_supp i] at hPe
    exact ⟨_, hPe, (C.ch i).e.left_inv hPs⟩
  have hθpos : ∀ i, ∀ u ∈ obox d (C.a i), 0 < θ i ((C.ch i).e.symm u) := fun i u hu ↦ by
    rw [hθ, OpenPartialHomeomorph.chartBump_symm_apply _ _ (hbox_target i (hobox_box i hu))]
    exact hf_pos i u hu
  -- their sum, positive exactly on the union `O` of the small boxes
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : R.M → ℝ, ∀ P, Θ P = ∑ i, θ i P := ⟨_, fun _ ↦ rfl⟩
  have hΘc : Continuous Θ := by
    rw [funext hΘ]; exact continuous_finsetSum _ fun i _ ↦ hθc i
  have hΘpos : ∀ P, 0 < Θ P ↔ P ∈ C.smallUnion := by
    intro P
    rw [hΘ]
    constructor
    · intro hP
      by_contra h
      refine hP.ne' (Finset.sum_eq_zero fun i _ ↦ ?_)
      by_contra hi
      exact h (mem_iUnion.mpr ⟨i, hθsupp i P hi⟩)
    · intro hP
      obtain ⟨i, u, hu, rfl⟩ := mem_iUnion.mp hP
      exact (hθpos i u hu).trans_le
        (Finset.single_le_sum (f := fun j ↦ θ j _) (fun j _ ↦ hθ0 j _) (Finset.mem_univ i))
  have hOopen : IsOpen C.smallUnion := by
    refine isOpen_iUnion fun i ↦ ?_
    refine ((C.ch i).e.symm.isOpen_image_iff_of_subset_source ?_).mpr (isOpen_obox d _)
    rw [OpenPartialHomeomorph.symm_source]
    exact (hobox_box i).trans (hbox_target i)
  -- the saturated open set `A = U \ π(M \ O)` around `Bcl`
  have hAopen : IsOpen (R.U \ R.π '' C.smallUnionᶜ) := by
    have hcl := R.isClosed_image hOopen.isClosed_compl
    have : R.U \ R.π '' C.smallUnionᶜ = R.U ∩ (closure (R.π '' C.smallUnionᶜ))ᶜ := by
      ext w
      constructor
      · rintro ⟨hwV, hw⟩
        exact ⟨hwV, fun hc ↦ hw (hcl ⟨hwV, hc⟩)⟩
      · rintro ⟨hwV, hw⟩
        exact ⟨hwV, fun hc ↦ hw (subset_closure hc)⟩
    rw [this]
    exact R.isOpen_U.inter isClosed_closure.isOpen_compl
  have hBA : Bcl ⊆ R.U \ R.π '' C.smallUnionᶜ := fun w hw ↦
    ⟨hBV hw, fun ⟨P, hP, hPw⟩ ↦ hP (hBO (by rw [mem_preimage, hPw]; exact hw))⟩
  have hAO : ∀ P, R.π P ∈ R.U \ R.π '' C.smallUnionᶜ → P ∈ C.smallUnion := fun P hP ↦ by
    by_contra h
    exact hP.2 ⟨P, h, rfl⟩
  obtain ⟨χ, hχs, hχ0, -, hχB, hχsupp, -⟩ := exists_smooth_cutoff hBcl hAopen hBA
  -- where the sum vanishes, the cut-off vanishes on a neighbourhood
  have hopen_pos : IsOpen {P | 0 < Θ P} := isOpen_lt continuous_const hΘc
  have hopen_zero : IsOpen (R.π ⁻¹' (tsupport χ)ᶜ) :=
    (isClosed_tsupport χ).isOpen_compl.preimage hg
  have hzero : ∀ P, ¬ 0 < Θ P → P ∈ R.π ⁻¹' (tsupport χ)ᶜ := fun P hP hc ↦
    hP ((hΘpos P).mpr (hAO P (hχsupp hc)))
  have hρzero : ∀ i Q, Q ∈ R.π ⁻¹' (tsupport χ)ᶜ →
      (if 0 < Θ Q then χ (R.π Q) * θ i Q / Θ Q else 0) = 0 := fun i Q hQ ↦ by
    rw [image_eq_zero_of_notMem_tsupport hQ, zero_mul, zero_div, ite_self]
  refine ⟨⟨fun i P ↦ if 0 < Θ P then χ (R.π P) * θ i P / Θ P else 0, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · intro i e' he'
    apply contDiffOn_of_locally_contDiffOn
    intro v hv
    by_cases hpos : 0 < Θ (e'.symm v)
    · refine ⟨e'.target ∩ e'.symm ⁻¹' {P | 0 < Θ P}, e'.isOpen_inter_preimage_symm hopen_pos,
        ⟨hv, hpos⟩, ?_⟩
      have hgs : ContDiffOn ℝ ∞ (R.π ∘ e'.symm) e'.target :=
        (R.analytic_π.comp_contMDiffOn
          (contMDiffOn_symm_of_mem_maximalAtlas he')).contDiffOn.of_le le_top
      have hχg : ContDiffOn ℝ ∞ ((fun P ↦ χ (R.π P)) ∘ e'.symm) e'.target :=
        hχs.comp_contDiffOn hgs
      have hΘs : ContDiffOn ℝ ∞ (Θ ∘ e'.symm) e'.target := by
        rw [funext hΘ]
        exact ContDiffOn.sum fun j _ ↦ hθsm j e' he'
      refine ContDiffOn.mono ?_ inter_subset_right
      refine (((hχg.mono inter_subset_left).mul ((hθsm i e' he').mono inter_subset_left)).div
        (hΘs.mono inter_subset_left) fun w hw ↦ ?_).congr ?_
      · exact (hw.2 : 0 < Θ (e'.symm w)).ne'
      · intro w hw
        have hw2 : 0 < Θ (e'.symm w) := hw.2
        simp only [Function.comp_apply, Pi.div_apply, ite_eq_left hw2]
    · refine ⟨e'.target ∩ e'.symm ⁻¹' (R.π ⁻¹' (tsupport χ)ᶜ),
        e'.isOpen_inter_preimage_symm hopen_zero, ⟨hv, hzero _ hpos⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : ℝ))).congr ?_ |>.mono inter_subset_right
      intro w hw
      exact hρzero i (e'.symm w) hw.2
  · intro i
    rw [continuous_iff_continuousAt]
    intro P
    by_cases hpos : 0 < Θ P
    · refine ((((hχs.continuous.comp hg).continuousAt.mul (hθc i).continuousAt).div
        hΘc.continuousAt hpos.ne')).congr ?_
      filter_upwards [hopen_pos.mem_nhds hpos] with Q hQ
      have hQ' : 0 < Θ Q := hQ
      simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply, ite_eq_left hQ']
    · refine (continuousAt_const : ContinuousAt (fun _ : R.M ↦ (0 : ℝ)) P).congr ?_
      filter_upwards [hopen_zero.mem_nhds (hzero P hpos)] with Q hQ
      exact (hρzero i Q hQ).symm
  · intro i P
    split_ifs with h
    · exact div_nonneg (mul_nonneg (hχ0 _) (hθ0 i P)) h.le
    · exact le_rfl
  · intro i P hP
    split_ifs at hP with h
    · refine hθsupp i P fun h0 ↦ hP ?_
      rw [h0, mul_zero, zero_div]
    · exact absurd rfl hP
  · intro P hP
    have hPpos : 0 < Θ P := (hΘpos P).mpr (hBO hP)
    simp only [ite_eq_left hPpos, hχB _ hP, one_mul]
    rw [← Finset.sum_div, ← hΘ]
    exact div_self hPpos.ne'
  · intro i
    have hPi : C.P i = (C.ch i).e.symm 0 := by
      rw [← (C.ch i).e_P, (C.ch i).e.left_inv (C.ch i).mem_source]
    have hθi : 0 < θ i (C.P i) := by rw [hPi]; exact hθpos i 0 (zero_mem_obox (C.a_pos i))
    have hΘi : 0 < Θ (C.P i) := (hΘpos _).mpr (hBO (hPB i))
    rw [ite_eq_left hΘi, hχB _ (hPB i), one_mul]
    exact div_pos hθi hΘi

end SingularLearningTheory
