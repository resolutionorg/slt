/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.BayesGibbs.CompactBase.Kernel
public import Mathlib.Topology.CompactOpen
import SLT.BayesGibbs.CompactBase.Quantise
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.MeasureTheory.Measure.RegularityCompacts
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Convergence of pair measures

Tensor convergence from compact families of kernel sections, without a finite-rank approximation
theorem.
-/

public section

namespace SingularLearningTheory.BayesGibbs

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {U Θ : Type*} [MetricSpace U] [CompactSpace U]
  [MeasurableSpace U] [BorelSpace U]

/-- The difference of two finite-measure integration functionals is Lipschitz
in the uniform norm, with the sum of their masses as bound. -/
private theorem abs_integral_difference_sub_le (μ ν : Measure U)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (a b : C(U, ℝ)) :
    |((∫ u, a u ∂μ) - ∫ u, a u ∂ν) -
      ((∫ u, b u ∂μ) - ∫ u, b u ∂ν)| ≤
        ‖a - b‖ * (μ.real univ + ν.real univ) := by
  have hI (ρ : Measure U) [IsFiniteMeasure ρ] (c : C(U, ℝ)) : Integrable c ρ :=
    Continuous.integrable_of_compactSpace ρ c.continuous
  have hb (ρ : Measure U) [IsFiniteMeasure ρ] :
      |∫ u, (a - b) u ∂ρ| ≤ ‖a - b‖ * ρ.real univ := by
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := ρ)
        (.of_forall fun u ↦ (a - b).norm_coe_le_norm u))
  calc
    _ = |(∫ u, (a - b) u ∂μ) - ∫ u, (a - b) u ∂ν| := by
      simp only [ContinuousMap.sub_apply, integral_sub (hI μ a) (hI μ b),
        integral_sub (hI ν a) (hI ν b)]
      congr 1
      ring
    _ ≤ |∫ u, (a - b) u ∂μ| + |∫ u, (a - b) u ∂ν| := abs_sub _ _
    _ ≤ ‖a - b‖ * μ.real univ + ‖a - b‖ * ν.real univ := add_le_add (hb μ) (hb ν)
    _ = _ := by ring

/-- Uniform convergence for every fixed continuous test, together with a
uniform mass bound, is uniform over any compact family of tests. -/
private theorem compact_tests_uniform_of_tests_uniform
    (μ : ℕ → Θ → Measure U) (ν : Θ → Measure U)
    [∀ n θ, IsFiniteMeasure (μ n θ)] [∀ θ, IsFiniteMeasure (ν θ)]
    (B : Set Θ) {C : ℝ} (hC : 0 < C)
    (hmass : ∀ᶠ n : ℕ in atTop, ∀ θ ∈ B,
      (μ n θ).real univ + (ν θ).real univ ≤ C)
    (htest : ∀ a : C(U, ℝ), ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ θ ∈ B,
      |(∫ u, a u ∂μ n θ) - ∫ u, a u ∂ν θ| ≤ ε)
    {S : Set C(U, ℝ)} (hS : IsCompact S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ θ ∈ B, ∀ a ∈ S,
      |(∫ u, a u ∂μ n θ) - ∫ u, a u ∂ν θ| ≤ ε := by
  classical
  let δ := ε / (2 * C)
  have hδ : 0 < δ := div_pos hε (mul_pos two_pos hC)
  obtain ⟨s, hsS, hsfin, hscover⟩ := hS.finite_cover_balls hδ
  have hfin : ∀ᶠ n : ℕ in atTop, ∀ a ∈ s, ∀ θ ∈ B,
      |(∫ u, a u ∂μ n θ) - ∫ u, a u ∂ν θ| ≤ ε / 2 :=
    (hsfin.eventually_all).mpr fun a _ ↦ htest a (ε / 2) (half_pos hε)
  filter_upwards [hmass, hfin] with n hn hnf θ hθ a ha
  obtain ⟨b, hb, hab⟩ : ∃ b ∈ s, dist a b < δ := by
    rcases mem_iUnion.mp (hscover ha) with ⟨b, hb⟩
    rcases mem_iUnion.mp hb with ⟨hbs, hab⟩
    exact ⟨b, hbs, hab⟩
  have hnorm : ‖a - b‖ ≤ δ := by simpa only [dist_eq_norm] using hab.le
  calc
    _ ≤ |((∫ u, a u ∂μ n θ) - ∫ u, a u ∂ν θ) -
          ((∫ u, b u ∂μ n θ) - ∫ u, b u ∂ν θ)| +
        |(∫ u, b u ∂μ n θ) - ∫ u, b u ∂ν θ| := by
      simpa only [sub_add_cancel] using
        (abs_add_le (((∫ u, a u ∂μ n θ) - ∫ u, a u ∂ν θ) -
          ((∫ u, b u ∂μ n θ) - ∫ u, b u ∂ν θ))
          ((∫ u, b u ∂μ n θ) - ∫ u, b u ∂ν θ))
    _ ≤ ‖a - b‖ * ((μ n θ).real univ + (ν θ).real univ) + ε / 2 :=
      add_le_add (abs_integral_difference_sub_le (μ n θ) (ν θ) a b) (hnf b hb θ hθ)
    _ ≤ δ * C + ε / 2 := add_le_add
      (mul_le_mul hnorm (hn θ hθ) (by positivity) hδ.le) le_rfl
    _ = ε := by dsimp only [δ]; field_simp [hC.ne']; ring

/-- Fubini bounds a tensor discrepancy by discrepancies of all kernel rows
and columns. This is the entire two-point argument after finite-net control. -/
private theorem abs_integral_prod_sub_le_of_sections
    (μ ν : Measure U) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (F : C(U × U, ℝ)) {δ : ℝ}
    (hrow : ∀ u, |(∫ v, F (u, v) ∂μ) - ∫ v, F (u, v) ∂ν| ≤ δ)
    (hcol : ∀ v, |(∫ u, F (u, v) ∂μ) - ∫ u, F (u, v) ∂ν| ≤ δ) :
    |(∫ z, F z ∂μ.prod μ) - ∫ z, F z ∂ν.prod ν| ≤
      δ * (μ.real univ + ν.real univ) := by
  have hI (ρ τ : Measure U) [IsFiniteMeasure ρ] [IsFiniteMeasure τ] :
      Integrable F (ρ.prod τ) :=
    Continuous.integrable_of_compactSpace (ρ.prod τ) F.continuous
  have hfirst : |(∫ z, F z ∂μ.prod μ) - ∫ z, F z ∂μ.prod ν| ≤ δ * μ.real univ := by
    rw [integral_prod _ (hI μ μ), integral_prod _ (hI μ ν),
      ← integral_sub (hI μ μ).integral_prod_left (hI μ ν).integral_prod_left]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := μ) (.of_forall fun u ↦ (show ‖(∫ v, F (u, v) ∂μ) - ∫ v, F (u, v) ∂ν‖ ≤ δ from by simpa only [Real.norm_eq_abs] using hrow u)))
  have hsecond : |(∫ z, F z ∂μ.prod ν) - ∫ z, F z ∂ν.prod ν| ≤ δ * ν.real univ := by
    rw [integral_prod_symm _ (hI μ ν), integral_prod_symm _ (hI ν ν),
      ← integral_sub (hI μ ν).integral_prod_right (hI ν ν).integral_prod_right]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_of_norm_le_const (μ := ν) (.of_forall fun v ↦ (show ‖(∫ u, F (u, v) ∂μ) - ∫ u, F (u, v) ∂ν‖ ≤ δ from by simpa only [Real.norm_eq_abs] using hcol v)))
  calc
    _ ≤ |(∫ z, F z ∂μ.prod μ) - ∫ z, F z ∂μ.prod ν| +
        |(∫ z, F z ∂μ.prod ν) - ∫ z, F z ∂ν.prod ν| := abs_sub_le _ _ _
    _ ≤ δ * μ.real univ + δ * ν.real univ := add_le_add hfirst hsecond
    _ = _ := by ring

/-- A continuous two-point kernel inherits the same uniform convergence as
single marks. Compact row/column families replace a Stone–Weierstrass argument. -/
theorem _root_.MeasureTheory.pair_integral_uniform_of_tests_uniform
    (μ : ℕ → Θ → Measure U) (ν : Θ → Measure U)
    [∀ n θ, IsFiniteMeasure (μ n θ)] [∀ θ, IsFiniteMeasure (ν θ)]
    (B : Set Θ) {C : ℝ} (hC : 0 < C)
    (hmass : ∀ᶠ n : ℕ in atTop, ∀ θ ∈ B,
      (μ n θ).real univ + (ν θ).real univ ≤ C)
    (htest : ∀ a : C(U, ℝ), ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ θ ∈ B,
      |(∫ u, a u ∂μ n θ) - ∫ u, a u ∂ν θ| ≤ ε)
    (F : C(U × U, ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ θ ∈ B,
      |(∫ z, F z ∂(μ n θ).prod (μ n θ)) -
        ∫ z, F z ∂(ν θ).prod (ν θ)| ≤ ε := by
  let Ft : C(U × U, ℝ) := F.comp ⟨Prod.swap, continuous_swap⟩
  have hS : IsCompact (range F.curry ∪ range Ft.curry) :=
    (isCompact_range F.curry.continuous).union (isCompact_range Ft.curry.continuous)
  have hsections := compact_tests_uniform_of_tests_uniform μ ν B hC hmass htest hS
    (div_pos hε hC)
  filter_upwards [hmass, hsections] with n hn hs θ hθ
  have hr (u : U) : |(∫ v, F (u, v) ∂μ n θ) - ∫ v, F (u, v) ∂ν θ| ≤ ε / C :=
    hs θ hθ (F.curry u) (Or.inl (mem_range_self u))
  have hc (v : U) : |(∫ u, F (u, v) ∂μ n θ) - ∫ u, F (u, v) ∂ν θ| ≤ ε / C :=
    hs θ hθ (Ft.curry v) (Or.inr (mem_range_self v))
  calc
    _ ≤ (ε / C) * ((μ n θ).real univ + (ν θ).real univ) :=
      abs_integral_prod_sub_le_of_sections (μ n θ) (ν θ) F hr hc
    _ ≤ (ε / C) * C := mul_le_mul_of_nonneg_left (hn θ hθ) (div_pos hε hC).le
    _ = ε := div_mul_cancel₀ ε hC.ne'

end SingularLearningTheory.BayesGibbs
