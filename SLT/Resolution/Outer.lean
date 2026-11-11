/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Resolution.InnerPartition
public import SLT.Resolution.Factorisation
import SLT.Resolution.Surjective
import Mathlib.Order.CompletePartialOrder

/-!
# Topological lemmas for the assembly of the atlas

[Hit26, Section 3.3.1], the choices left
implicit in the plan: the threshold `ε` with `W_ε ⊆ ⋃ V_σ` (here `δ` with `W ∩ {K ≤ δ}` inside
the union of the outer sets), the saturated open set `V \ g(M \ O)` around a compact part of
`W₀` (the set every point of whose fibre lies in the union `O` of the small boxes), the germ of
a product of analytic functions, and the normalisation of the semianalytic description of `W`
(a defining function `H_i ≡ 0` is replaced by the constant `1`, so that every `H_i` has a nonzero
germ everywhere). No thesis counterpart for the individual lemmas.
-/

public section

namespace SingularLearningTheory

open Set Filter Topology
open scoped Manifold ContDiff

variable {d N : ℕ}

/-- The threshold: for `W` compact, `K` continuous and nonnegative on `W`, and `B` an open set
containing `{w ∈ W | K w = 0}`, some sublevel set `W ∩ {K ≤ δ}` lies in `B`. -/
theorem _root_.IsCompact.exists_delta {W B : Set (Fin d → ℝ)} {K : (Fin d → ℝ) → ℝ}
    (hW : IsCompact W)
    (hK : ContinuousOn K W) (hK0 : ∀ w ∈ W, 0 ≤ K w) (hB : IsOpen B)
    (hWB : ∀ w ∈ W, K w = 0 → w ∈ B) :
    ∃ δ > 0, ∀ w ∈ W, K w ≤ δ → w ∈ B := by
  have hS : IsCompact (W \ B) := hW.diff hB
  rcases (W \ B).eq_empty_or_nonempty with hS0 | hSne
  · refine ⟨1, one_pos, fun w hw _ ↦ ?_⟩
    by_contra hwB
    exact (Set.eq_empty_iff_forall_notMem.mp hS0) w ⟨hw, hwB⟩
  obtain ⟨x₀, hx₀, hmin⟩ := hS.exists_isMinOn hSne (hK.mono sdiff_subset)
  have hpos : 0 < K x₀ :=
    lt_of_le_of_ne (hK0 x₀ hx₀.1) fun h ↦ hx₀.2 (hWB x₀ hx₀.1 h.symm)
  refine ⟨K x₀ / 2, half_pos hpos, fun w hw hKw ↦ ?_⟩
  by_contra hwB
  have : K x₀ ≤ K w := hmin ⟨hw, hwB⟩
  linarith [half_lt_self hpos]

/-- The germ of a finite product of analytic functions vanishes only if the germ of a factor
does (analytic germs form an integral domain). -/
theorem _root_.Finset.eventuallyEq_zero_of_prod {ι : Type*} (s : Finset ι) {f : ι → (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hf : ∀ i ∈ s, AnalyticAt ℝ (f i) x)
    (h : (fun y ↦ ∏ i ∈ s, f i y) =ᶠ[𝓝 x] 0) : ∃ i ∈ s, f i =ᶠ[𝓝 x] 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := h.self_of_nhds
    simp at this
  | insert a s ha ih =>
    have hprod : (fun y ↦ f a y * ∏ i ∈ s, f i y) =ᶠ[𝓝 x] 0 := by
      refine h.congr (Eventually.of_forall fun y ↦ ?_)
      simp [Finset.prod_insert ha]
    rcases (hf a (Finset.mem_insert_self a s)).eventuallyEq_zero_or_of_mul
        (Finset.analyticAt_fun_prod s fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)) hprod with
      hz | hz
    · exact ⟨a, Finset.mem_insert_self a s, hz⟩
    · obtain ⟨i, hi, hiz⟩ := ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)) hz
      exact ⟨i, Finset.mem_insert_of_mem hi, hiz⟩

/-- If `φ = φ₁ φ₂` near `w` with `φ₁ ≠ 0` there, a nonzero germ of `φ` gives a nonzero germ of
`φ₂`. -/
theorem _root_.not_eventuallyEq_zero_of_mul {φ φ₁ φ₂ : (Fin d → ℝ) → ℝ} {U : Set (Fin d → ℝ)}
    (hU : IsOpen U) {w : Fin d → ℝ} (hw : w ∈ U) (hφ : ∀ w ∈ U, φ w = φ₁ w * φ₂ w)
    (h : ¬ (φ =ᶠ[𝓝 w] 0)) : ¬ (φ₂ =ᶠ[𝓝 w] 0) := by
  intro h₂
  refine h ?_
  filter_upwards [h₂, hU.mem_nhds hw] with y hy hyU
  rw [hφ y hyU, hy]
  simp

/-- Normalising the semianalytic description of `W` on an open `U`: a defining function that
vanishes identically on a connected component of `U` is replaced by the constant `1` there; the
set cut out in `U` is unchanged and every defining function has a nonzero germ at every point of
`U` (the identity theorem on the component). -/
theorem _root_.exists_normalized_semianalytic {U : Set (Fin d → ℝ)} (hU : IsOpen U)
    {H : Fin N → (Fin d → ℝ) → ℝ} (hH : ∀ i, AnalyticOnNhd ℝ (H i) U) :
    ∃ H' : Fin N → (Fin d → ℝ) → ℝ, (∀ i, AnalyticOnNhd ℝ (H' i) U) ∧
      (∀ i, ∀ w ∈ U, ¬ (H' i =ᶠ[𝓝 w] 0)) ∧
      ∀ w ∈ U, ((∀ i, 0 ≤ H i w) ↔ ∀ i, 0 ≤ H' i w) := by
  classical
  -- `Z i w`: `H i` vanishes identically on the component of `U` through `w`
  let Z : Fin N → (Fin d → ℝ) → Prop := fun i w ↦ ∃ y ∈ connectedComponentIn U w, H i =ᶠ[𝓝 y] 0
  have hZeq : ∀ i w, ∀ y ∈ connectedComponentIn U w, (Z i y ↔ Z i w) := by
    intro i w y hy
    simp only [Z, connectedComponentIn_eq hy]
  have hZzero : ∀ i w, Z i w → ∀ y ∈ connectedComponentIn U w, H i y = 0 := by
    rintro i w ⟨y, hy, hy0⟩ z hz
    have hcomp := (hH i).mono (connectedComponentIn_subset U w)
    exact hcomp.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_connectedComponentIn
      hy hy0 hz
  have hnhds : ∀ w ∈ U, connectedComponentIn U w ∈ 𝓝 w := fun w hw ↦
    connectedComponentIn_mem_nhds (hU.mem_nhds hw)
  refine ⟨fun i w ↦ if Z i w then 1 else H i w, fun i w hw ↦ ?_, fun i w hw h ↦ ?_,
    fun w hw ↦ ?_⟩
  · by_cases hZ : Z i w
    · refine (analyticAt_const (v := (1 : ℝ)) (x := w)).congr ?_
      filter_upwards [hnhds w hw] with y hy
      simp [(hZeq i w y hy).mpr hZ]
    · refine (hH i w hw).congr ?_
      filter_upwards [hnhds w hw] with y hy
      simp [(hZeq i w y hy).not.mpr hZ]
  · by_cases hZ : Z i w
    · have := h.self_of_nhds
      simp [hZ] at this
    · refine hZ ⟨w, mem_connectedComponentIn hw, ?_⟩
      filter_upwards [h, hnhds w hw] with y hy hyC
      simpa [(hZeq i w y hyC).not.mpr hZ] using hy
  · refine forall_congr' fun i ↦ ?_
    by_cases hZ : Z i w
    · simp [hZ, hZzero i w hZ w (mem_connectedComponentIn hw)]
    · simp [hZ]

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Fin d → ℝ) M]
  {Kf φ₂ : (Fin d → ℝ) → ℝ} {H : Fin N → (Fin d → ℝ) → ℝ} {g : M → (Fin d → ℝ)}
  {T : Set (Fin d → ℝ)}

namespace ChartCover

variable (C : ChartCover Kf φ₂ H g T)

theorem isOpen_smallUnion : IsOpen C.smallUnion := by
  refine isOpen_iUnion fun i ↦ ?_
  refine ((C.ch i).e.symm.isOpen_image_iff_of_subset_source ?_).mpr (isOpen_obox d _)
  rw [OpenPartialHomeomorph.symm_source]
  refine (Set.pi_mono fun _ _ ↦ ?_).trans
    ((box_eq_pi _ _).ge.trans ((C.ch i).box_subset.trans (C.ch i).O_subset))
  exact Ioo_subset_Icc_self.trans (Icc_subset_Icc (neg_le_neg (C.a_lt i).le) (C.a_lt i).le)

/-- The saturated open set `V \ g(M \ O)`: the points of `V` all of whose preimages lie in the
union `O` of the small boxes. -/
@[expose] def saturated (V : Set (Fin d → ℝ)) : Set (Fin d → ℝ) := V \ g '' C.smallUnionᶜ

/-- For a chart cover of a resolution, the saturated set of `U` is open: `π` is a closed map into
`U`. -/
theorem isOpen_saturated {F : (Fin d → ℝ) → ℝ} {R : Resolution F} (C : ChartCover Kf φ₂ H R.π T) :
    IsOpen (C.saturated R.U) := by
  have hcl := R.isClosed_image C.isOpen_smallUnion.isClosed_compl
  have : C.saturated R.U = R.U ∩ (closure (R.π '' C.smallUnionᶜ))ᶜ := by
    ext w
    constructor
    · rintro ⟨hwV, hw⟩
      exact ⟨hwV, fun hc ↦ hw (hcl ⟨hwV, hc⟩)⟩
    · rintro ⟨hwV, hw⟩
      exact ⟨hwV, fun hc ↦ hw (subset_closure hc)⟩
  rw [this]
  exact R.isOpen_U.inter isClosed_closure.isOpen_compl

theorem subset_saturated {V : Set (Fin d → ℝ)} {S : Set (Fin d → ℝ)} (hSV : S ⊆ V)
    (hSO : g ⁻¹' S ⊆ C.smallUnion) : S ⊆ C.saturated V := fun w hw ↦
  ⟨hSV hw, fun ⟨P, hP, hPw⟩ ↦ hP (hSO (by rw [mem_preimage, hPw]; exact hw))⟩

theorem preimage_saturated_subset (V : Set (Fin d → ℝ)) :
    g ⁻¹' C.saturated V ⊆ C.smallUnion := fun P hP ↦ by
  by_contra h
  exact hP.2 ⟨P, h, rfl⟩

theorem saturated_subset (V : Set (Fin d → ℝ)) : C.saturated V ⊆ V := sdiff_subset

end ChartCover

end SingularLearningTheory
