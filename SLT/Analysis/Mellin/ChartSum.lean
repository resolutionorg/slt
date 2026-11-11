/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.Mellin.SmoothContinuation
public import SLT.Analysis.Meromorphic.HalfPlaneGlue

/-!
# Meromorphic continuation of finite sums of smooth monomial integrals

The input is a finite family of monomial integrals; no statistical model or resolution atlas
is needed.
-/

public section

open MeasureTheory Set Finset Complex Filter Topology
open scoped ContDiff

namespace SingularLearningTheory.MellinAnalysis

variable {ι : Type*} {d : ℕ}

/-- Candidate poles contributed by a finite family of monomial charts. -/
@[expose] def polesSet (k h : ι → Fin d → ℕ) : Set ℂ :=
  {z | ∃ α p j, 0 < k α p ∧ z = chartPole (k α) (h α) p j}

theorem chartPole_re (k h : Fin d → ℕ) (p : Fin d) (j : ℕ) :
    (chartPole k h p j).re = -(((h p : ℝ) + j + 1) / (2 * k p)) := by
  simp only [chartPole, Complex.neg_re, Complex.ofReal_re]

private theorem chartPole_im (k h : Fin d → ℕ) (p : Fin d) (j : ℕ) :
    (chartPole k h p j).im = 0 := by
  simp only [chartPole, Complex.neg_im, Complex.ofReal_im, neg_zero]

private theorem polesSet_countable [Countable ι] (k h : ι → Fin d → ℕ) :
    (polesSet k h).Countable := by
  refine (Set.countable_range fun x : ι × Fin d × ℕ ↦
    chartPole (k x.1) (h x.1) x.2.1 x.2.2).mono ?_
  rintro z ⟨α, p, j, -, rfl⟩
  exact ⟨(α, p, j), rfl⟩

/-- **The candidates are real, negative and rational.** -/
theorem polesSet_subset_negRat (k h : ι → Fin d → ℕ) :
    polesSet k h ⊆ {z : ℂ | z.im = 0 ∧ z.re < 0 ∧ ∃ q : ℚ, (q : ℝ) = z.re} := by
  rintro z ⟨α, p, j, hk, rfl⟩
  refine ⟨chartPole_im _ _ _ _, ?_, ⟨-(((h α p : ℚ) + j + 1) / (2 * k α p)), ?_⟩⟩
  · rw [chartPole_re]
    have : (0 : ℝ) < ((h α p : ℝ) + j + 1) / (2 * k α p) := by positivity
    linarith
  · rw [chartPole_re]
    push_cast
    rfl

/-- Only finitely many candidates lie in the half-plane `Re z > −N`. -/
private theorem polesSet_inter_halfPlane_finite [Finite ι] (k h : ι → Fin d → ℕ) (N : ℕ) :
    (polesSet k h ∩ {z : ℂ | -(N : ℝ) < z.re}).Finite := by
  classical
  let := Fintype.ofFinite ι
  refine (Set.finite_iUnion fun α : ι ↦ Set.finite_iUnion fun p : Fin d ↦
    (Finset.range (2 * (∑ q, k α q) * N)).finite_toSet.biUnion fun j _ ↦
      Set.finite_singleton (chartPole (k α) (h α) p j)).subset ?_
  rintro z ⟨⟨α, p, j, hk, rfl⟩, hz⟩
  simp only [mem_iUnion, mem_singleton_iff, Finset.mem_coe, Finset.mem_range]
  refine ⟨α, p, j, ?_, rfl⟩
  have hz' : -(N : ℝ) < -(((h α p : ℝ) + j + 1) / (2 * k α p)) := by
    have := hz
    change -(N : ℝ) < (chartPole (k α) (h α) p j).re at this
    rwa [chartPole_re] at this
  have hk' : (0 : ℝ) < 2 * k α p := by positivity
  have h1 : ((h α p : ℝ) + j + 1) / (2 * k α p) < N := by linarith
  rw [div_lt_iff₀ hk'] at h1
  have h2 : (j : ℝ) < 2 * k α p * N := by
    linarith [(Nat.cast_nonneg (h α p) : (0 : ℝ) ≤ h α p)]
  have h3 : j < 2 * k α p * N := by exact_mod_cast h2
  have h4 : k α p ≤ ∑ q, k α q :=
    Finset.single_le_sum (fun q _ ↦ Nat.zero_le _) (Finset.mem_univ p)
  calc j < 2 * k α p * N := h3
    _ ≤ 2 * (∑ q, k α q) * N := by gcongr

private theorem polesSet_inter_finite [Finite ι] (k h : ι → Fin d → ℕ) (c : ℝ) :
    (polesSet k h ∩ {z : ℂ | c < z.re}).Finite := by
  refine (polesSet_inter_halfPlane_finite k h ⌈-c⌉₊).subset ?_
  rintro z ⟨hP, hz⟩
  refine ⟨hP, ?_⟩
  change -(⌈-c⌉₊ : ℝ) < z.re
  have := Nat.le_ceil (-c)
  have hz' : c < z.re := hz
  linarith

private theorem polesSet_re_le (k h : ι → Fin d → ℕ) : ∀ z ∈ polesSet k h, z.re ≤ 0 := fun _ hz ↦
  (polesSet_subset_negRat k h hz).2.1.le

private theorem isOpen_compl_polesSet [Finite ι] (k h : ι → Fin d → ℕ) : IsOpen (polesSet k h)ᶜ :=
  isOpen_compl_of_finite_halfPlanes (polesSet_inter_finite k h)


/-- A finite sum of smooth chart integrals has a meromorphic continuation, holomorphic
off the negative rational pole candidates and equal to the integrals wherever they converge. -/
theorem exists_continuation_chartSum [Fintype ι]
    (k h : ι → Fin d → ℕ) (b : ι → Fin d → ℝ) (hb : ∀ α p, 0 < b α p)
    (g : ι → (Fin d → ℝ) → ℂ) (hg : ∀ α, ContDiff ℝ ∞ (g α)) :
    ∃ F : ℂ → ℂ, MeromorphicOn F univ ∧
      (∀ z ∉ polesSet k h, DifferentiableAt ℂ F z) ∧
      ∀ z : ℂ, (∀ α p, -1 < (chartExp (k α) (h α) z p).re) →
        F z = ∑ α, remainderZeta (k α) (h α) (b α) (g α) z := by
  classical
  have hstage (N : ℕ) : ∃ G : ℂ → ℂ,
      (∀ z : ℂ, (∀ α p, -1 < (chartExp (k α) (h α) z p).re) →
        G z = ∑ α, remainderZeta (k α) (h α) (b α) (g α) z) ∧
      (∀ z : ℂ, -(N : ℝ) < z.re → z ∉ polesSet k h → DifferentiableAt ℂ G z) ∧
      (∀ z : ℂ, -(N : ℝ) < z.re → MeromorphicAt G z) := by
    have hF := fun α ↦ exists_continuation_remainderZeta (k α) (h α) (hb α)
      (g α) (hg α) (2 * (∑ q, k α q) * N)
    choose F hF using hF
    have hreg : ∀ α, ∀ z : ℂ, -(N : ℝ) < z.re →
        ∀ p, -1 < (chartExp (k α) (h α) z p).re + ((2 * (∑ q, k α q) * N : ℕ) : ℝ) := by
      intro α z hz p
      rw [chartExp_re]
      have hk : (k α p : ℝ) ≤ ∑ q, (k α q : ℝ) := by
        exact_mod_cast Finset.single_le_sum (fun q _ ↦ Nat.zero_le (k α q)) (Finset.mem_univ p)
      have hh0 : (0 : ℝ) ≤ h α p := Nat.cast_nonneg _
      have t1 : 0 ≤ 2 * (k α p : ℝ) * (z.re + N) :=
        mul_nonneg (by positivity) (by linarith)
      have t2 : (k α p : ℝ) * N ≤ (∑ q, (k α q : ℝ)) * N :=
        mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg N)
      push_cast
      nlinarith
    refine ⟨∑ α, F α, ?_, ?_, ?_⟩
    · intro z hz
      rw [Finset.sum_apply]
      exact Finset.sum_congr rfl fun α _ ↦ ((hF α).1 z (hz α)).symm
    · intro z hz hP
      exact DifferentiableAt.sum fun α _ ↦
        (hF α).2.1 z (hreg α z hz) fun p hk j _ hj ↦ hP ⟨α, p, j, hk, hj⟩
    · intro z hz
      exact MeromorphicAt.sum fun α _ ↦ (hF α).2.2 z (hreg α z hz)
  choose G hG using hstage
  have hpos {z : ℂ} (hz : 0 < z.re) : ∀ α p, -1 < (chartExp (k α) (h α) z p).re := by
    intro α p
    rw [chartExp_re]
    have : 0 ≤ 2 * (k α p : ℝ) * z.re := by positivity
    linarith [(Nat.cast_nonneg (h α p) : (0 : ℝ) ≤ h α p)]
  obtain ⟨F, _, hFm, hFd, hFG⟩ := exists_meromorphic_glue
    (fun z ↦ ∑ α, remainderZeta (k α) (h α) (b α) (g α) z)
    0 (polesSet_countable k h) (polesSet_inter_finite k h) (polesSet_re_le k h)
    G (fun N z hz ↦ ((hG N).1 z (hpos hz)).symm)
    (fun N z hz ↦ (hG N).2.1 z (by simpa using hz))
    (fun N z hz ↦ (hG N).2.2 z (by simpa using hz))
  refine ⟨F, hFm, hFd, fun z hz ↦ ?_⟩
  obtain ⟨N, hN⟩ := hFG z
  rw [hN, (hG N).1 z hz]

end SingularLearningTheory.MellinAnalysis
