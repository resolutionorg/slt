/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Gluing meromorphic continuations on expanding half-planes

Locally finite pole candidates ensure that the
half-plane continuations agree off the poles and define consistent meromorphic germs.
-/

public section

open MeasureTheory Set Filter Topology Complex

namespace Complex

section Topology

/-- `ℂ` minus a countable set is preconnected. -/
private theorem isPreconnected_compl_countable {S : Set ℂ} (hS : S.Countable) : IsPreconnected Sᶜ :=
  (hS.isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected

/-- The map `w ↦ (exp(Re w) + c, Im w)` parametrising the half-plane `{Re z > c}`. -/
private noncomputable def halfPlaneMap (c : ℝ) (w : ℂ) : ℂ := ⟨Real.exp w.re + c, w.im⟩

private theorem continuous_halfPlaneMap (c : ℝ) : Continuous (halfPlaneMap c) := by
  have : halfPlaneMap c = fun w ↦ ((Real.exp w.re + c : ℝ) : ℂ) + (w.im : ℂ) * Complex.I := by
    funext w
    apply Complex.ext <;> simp [halfPlaneMap, Complex.exp_ofReal_re]
  rw [this]
  fun_prop

private theorem halfPlaneMap_injective (c : ℝ) : Function.Injective (halfPlaneMap c) := by
  intro w₁ w₂ h
  simp only [halfPlaneMap, Complex.mk.injEq] at h
  exact Complex.ext (Real.exp_injective (by linarith [h.1])) h.2

private theorem range_halfPlaneMap (c : ℝ) : range (halfPlaneMap c) = {z : ℂ | c < z.re} := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    change c < (halfPlaneMap c w).re
    simp only [halfPlaneMap]
    linarith [Real.exp_pos w.re]
  · intro hz
    refine ⟨⟨Real.log (z.re - c), z.im⟩, ?_⟩
    simp only [halfPlaneMap, Real.exp_log (sub_pos.mpr hz)]
    apply Complex.ext <;> simp

/-- **A half-plane minus a countable set is preconnected.** -/
private theorem isPreconnected_halfPlane_diff_countable (c : ℝ) {S : Set ℂ} (hS : S.Countable) :
    IsPreconnected ({z : ℂ | c < z.re} \ S) := by
  have hpre : IsPreconnected (halfPlaneMap c ⁻¹' S)ᶜ :=
    isPreconnected_compl_countable (hS.preimage (halfPlaneMap_injective c))
  have himg : halfPlaneMap c '' (halfPlaneMap c ⁻¹' S)ᶜ = {z : ℂ | c < z.re} \ S := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨range_halfPlaneMap c ▸ mem_range_self w, hw⟩
    · rintro ⟨hz, hzS⟩
      obtain ⟨w, rfl⟩ := (range_halfPlaneMap c).symm ▸ hz
      exact ⟨w, hzS, rfl⟩
  rw [← himg]
  exact hpre.image _ (continuous_halfPlaneMap c).continuousOn

end Topology

section Glue

/-- A half-plane minus a set with finitely many points in every half-plane is open. -/
private theorem isOpen_halfPlane_diff_of_finite {P : Set ℂ}
    (hPfin : ∀ c : ℝ, (P ∩ {z : ℂ | c < z.re}).Finite) (c : ℝ) {S : Set ℂ} (hS : S ⊆ P) :
    IsOpen ({z : ℂ | c < z.re} \ S) := by
  have : {z : ℂ | c < z.re} \ S = {z : ℂ | c < z.re} \ (S ∩ {z : ℂ | c < z.re}) := by
    ext z
    simp only [Set.mem_sdiff, mem_inter_iff, not_and]
    tauto
  rw [this]
  exact (isOpen_lt continuous_const Complex.continuous_re).sdiff
    (((hPfin c).subset (inter_subset_inter_left _ hS)).isClosed)

theorem isOpen_compl_of_finite_halfPlanes {P : Set ℂ}
    (hPfin : ∀ c : ℝ, (P ∩ {z : ℂ | c < z.re}).Finite) : IsOpen Pᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  exact ⟨{w : ℂ | z.re - 1 < w.re} \ P, fun w hw ↦ hw.2,
    isOpen_halfPlane_diff_of_finite hPfin _ subset_rfl, ⟨by change z.re - 1 < z.re; linarith, hz⟩⟩

/-- **Gluing half-plane continuations.** Let `P` be a countable set with finitely many points in
every half-plane and lying in `Re z ≤ a`, and let `G N` extend `ζ` from `Re z > a` to the
half-plane `Re z > a − N`, holomorphic there off `P` and meromorphic there. Then there is a single
`F` extending `ζ` from `Re z > a`, meromorphic on `ℂ` and holomorphic off `P`. -/
theorem exists_meromorphic_glue (ζ : ℂ → ℂ) (a : ℝ) {P : Set ℂ} (hPc : P.Countable)
    (hPfin : ∀ c : ℝ, (P ∩ {z : ℂ | c < z.re}).Finite) (hPa : ∀ z ∈ P, z.re ≤ a)
    (G : ℕ → ℂ → ℂ) (hGeq : ∀ N, ∀ z : ℂ, a < z.re → ζ z = G N z)
    (hGd : ∀ N : ℕ, ∀ z₀ : ℂ, a - N < z₀.re → z₀ ∉ P → DifferentiableAt ℂ (G N) z₀)
    (hGm : ∀ N : ℕ, ∀ z₀ : ℂ, a - N < z₀.re → MeromorphicAt (G N) z₀) :
    ∃ F : ℂ → ℂ, (∀ z : ℂ, a < z.re → ζ z = F z) ∧ MeromorphicOn F univ ∧
      (∀ z₀ ∉ P, DifferentiableAt ℂ F z₀) ∧ ∀ z : ℂ, ∃ N : ℕ, F z = G N z := by
  have hopen : ∀ N : ℕ, IsOpen ({z : ℂ | a - N < z.re} \ P) := fun N ↦
    isOpen_halfPlane_diff_of_finite hPfin _ subset_rfl
  have hbase : ((a + 1 : ℝ) : ℂ) ∉ P := fun h ↦ by
    have := hPa _ h
    norm_num at this
  have hbase_mem : ((a + 1 : ℝ) : ℂ) ∈ {z : ℂ | a < z.re} := by
    change a < ((a + 1 : ℝ) : ℂ).re
    simp
  have hopen_a : IsOpen {z : ℂ | a < z.re} := isOpen_lt continuous_const Complex.continuous_re
  -- compatibility of the half-plane continuations
  have hcompat : ∀ N M : ℕ, N ≤ M → EqOn (G N) (G M) ({z : ℂ | a - N < z.re} \ P) := by
    intro N M hNM
    have hNM' : ∀ z : ℂ, a - N < z.re → a - M < z.re := fun z hz ↦ by
      have : (N : ℝ) ≤ M := by exact_mod_cast hNM
      linarith
    have hf : AnalyticOnNhd ℂ (G N) ({z : ℂ | a - N < z.re} \ P) := fun z hz ↦
      DifferentiableOn.analyticAt (fun w hw ↦ (hGd N w hw.1 hw.2).differentiableWithinAt)
        ((hopen N).mem_nhds hz)
    have hg : AnalyticOnNhd ℂ (G M) ({z : ℂ | a - N < z.re} \ P) := fun z hz ↦
      DifferentiableOn.analyticAt
        (fun w hw ↦ (hGd M w (hNM' w hw.1) hw.2).differentiableWithinAt)
        ((hopen N).mem_nhds hz)
    refine hf.eqOn_of_preconnected_of_eventuallyEq hg
      (isPreconnected_halfPlane_diff_countable _ hPc) (z₀ := ((a + 1 : ℝ) : ℂ))
      ⟨by change a - N < ((a + 1 : ℝ) : ℂ).re; simp; linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)],
        hbase⟩ ?_
    filter_upwards [hopen_a.mem_nhds hbase_mem] with z hz
    rw [← hGeq N z hz, ← hGeq M z hz]
  -- the glued function
  set Nz : ℂ → ℕ := fun z ↦ ⌈a - z.re⌉₊ + 1 with hNzdef
  have hNz : ∀ z : ℂ, a - (Nz z : ℝ) < z.re := fun z ↦ by
    have := Nat.le_ceil (a - z.re)
    simp only [hNzdef]
    push_cast
    linarith
  have hNz' : ∀ z : ℂ, a - (Nz z : ℝ) ≤ z.re - 1 := fun z ↦ by
    have := Nat.le_ceil (a - z.re)
    simp only [hNzdef]
    push_cast
    linarith
  have hloc : ∀ z₀ : ℂ, ∀ z ∈ {z : ℂ | z₀.re - 1 < z.re} \ P, G (Nz z) z = G (Nz z₀) z := by
    intro z₀ z hz
    have hz1 : z₀.re - 1 < z.re := hz.1
    have hzN₀ : z ∈ {z : ℂ | a - (Nz z₀ : ℝ) < z.re} \ P :=
      ⟨by change a - (Nz z₀ : ℝ) < z.re; linarith [hNz' z₀], hz.2⟩
    have hzN : z ∈ {w : ℂ | a - (Nz z : ℝ) < w.re} \ P := ⟨hNz z, hz.2⟩
    rcases le_total (Nz z) (Nz z₀) with h | h
    · exact hcompat _ _ h hzN
    · exact (hcompat _ _ h hzN₀).symm
  refine ⟨fun z ↦ G (Nz z) z, fun z hz ↦ hGeq (Nz z) z hz, fun z₀ _ ↦ ?_, fun z₀ hz₀ ↦ ?_,
    fun z ↦ ⟨Nz z, rfl⟩⟩
  · refine (hGm (Nz z₀) z₀ (hNz z₀)).congr ?_
    have hmem : {z : ℂ | z₀.re - 1 < z.re} \ (P \ {z₀}) ∈ 𝓝 z₀ :=
      (isOpen_halfPlane_diff_of_finite hPfin _ Set.sdiff_subset).mem_nhds
        ⟨by change z₀.re - 1 < z₀.re; linarith, fun h ↦ h.2 rfl⟩
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hmem] with z hz hz'
    exact (hloc z₀ z ⟨hz'.1, fun hP ↦ hz'.2 ⟨hP, hz⟩⟩).symm
  · refine (hGd (Nz z₀) z₀ (hNz z₀) hz₀).congr_of_eventuallyEq ?_
    filter_upwards [(isOpen_halfPlane_diff_of_finite hPfin _ subset_rfl).mem_nhds
      (⟨by change z₀.re - 1 < z₀.re; linarith, hz₀⟩ :
        z₀ ∈ {z : ℂ | z₀.re - 1 < z.re} \ P)] with z hz
    exact hloc z₀ z hz

end Glue

end Complex
