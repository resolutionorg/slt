/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Localized sublevel-volume scaling: the constant-carrying form and uniqueness

`HasLLCOn μ K f λ θ c` is the constant-carrying form of the scaling of the localized sublevel
volumes `sublevelVol μ K f` against the model scale `llcScale λ θ`: a ratio limit with leading
constant `c`, beside the exponent-level two-sided-bound form `HasLLCExponentsOn μ K f λ θ`.

The main results are the uniqueness theorems: the scale functions `ε ↦ ε^a (−log ε)^(b−1)` for
distinct `(a, b)` are pairwise non-Θ-comparable on `𝓝[>] 0` (`llcScale_isTheta_iff_eq`), hence
`(λ, θ)` is determined by `HasLLCExponentsOn` (`HasLLCExponentsOn.unique`) and `(λ, θ, c)` by
`HasLLCOn` with positive constants (`HasLLCOn.unique`). The volume-scaling library is written
in these definitions, and so are the chart form of a real-analytic function and the existence
of its local learning coefficient (`SLT.ChartForm.MonomialChartCoverExistence`,
`SLT.ChartForm.LearningCoefficientExistence`).
-/

@[expose] public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f : α → ℝ}

/-- `f` has local learning coefficient `lam`, order `theta`, and leading
constant `c` on `K` with respect to `μ`: the constant-carrying form
`V(ε) / (ε^λ (−log ε)^(θ−1)) → c` as `ε → 0⁺`. Positivity of `c` is
deliberately not bundled; theorems that need it take `0 < c`. -/
def HasLLCOn (μ : Measure α) (K : Set α) (f : α → ℝ) (lam theta c : ℝ) : Prop :=
  Tendsto (fun ε => sublevelVol μ K f ε / llcScale lam theta ε) (𝓝[>] 0) (𝓝 c)

theorem sublevelVol_nonneg (μ : Measure α) (K : Set α) (f : α → ℝ) (ε : ℝ) :
    0 ≤ sublevelVol μ K f ε :=
  ENNReal.toReal_nonneg

/-- Sublevel volumes are monotone in the localization set (the larger
set must carry finite measure for the `toReal` comparison). -/
theorem sublevelVol_mono_set {K₁ K₂ : Set α} (h : K₁ ⊆ K₂)
    (hfin : μ K₂ ≠ ⊤) (f : α → ℝ) (ε : ℝ) :
    sublevelVol μ K₁ f ε ≤ sublevelVol μ K₂ f ε :=
  ENNReal.toReal_mono
    (ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left))
    (measure_mono (Set.inter_subset_inter_left _ h))

/-! ## The scale function on `𝓝[>] 0` -/

theorem llcScale_pos {lam theta ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) :
    0 < llcScale lam theta ε := by
  have hlog : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε.1 hε.2)
  exact mul_pos (Real.rpow_pos_of_pos hε.1 _) (Real.rpow_pos_of_pos hlog _)

/-- Load-bearing positivity: the scale is eventually strictly positive on
`𝓝[>] 0`. -/
theorem llcScale_eventually_pos {lam theta : ℝ} :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < llcScale lam theta ε := by
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  exact llcScale_pos hε

/-- The substitution bridge: at `t = −log ε`, the scale is
`exp(−a·t) · t^(b−1)`. -/
theorem llcScale_eq_comp {ε : ℝ} (h0 : 0 < ε) (a b : ℝ) :
    llcScale a b ε = Real.exp (-a * -Real.log ε) * (-Real.log ε) ^ (b - 1) := by
  rw [llcScale, Real.rpow_def_of_pos h0,
    show Real.log ε * a = -a * -Real.log ε by ring]

theorem _root_.tendsto_neg_log_nhdsGT_zero :
    Tendsto (fun ε : ℝ => -Real.log ε) (𝓝[>] 0) atTop :=
  tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero

/-- `exp(δ·t) · t^β → ∞` for `δ > 0` (any real `β`). -/
theorem _root_.tendsto_exp_mul_mul_rpow_atTop {δ β : ℝ} (hδ : 0 < δ) :
    Tendsto (fun t : ℝ => Real.exp (δ * t) * t ^ β) atTop atTop := by
  refine (tendsto_exp_mul_div_rpow_atTop (-β) δ hδ).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  rw [Real.rpow_neg ht.le, div_inv_eq_mul]

theorem tendsto_llcScale_nhds_zero {a b : ℝ} (ha : 0 < a) :
    Tendsto (llcScale a b) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hcomp : Tendsto (fun t : ℝ => t ^ (b - 1) * Real.exp (-a * t)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (b - 1) a ha
  refine (hcomp.comp tendsto_neg_log_nhdsGT_zero).congr' ?_
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  change (-Real.log ε) ^ (b - 1) * Real.exp (-a * -Real.log ε) = llcScale a b ε
  rw [llcScale_eq_comp hε.1, mul_comm]

theorem tendsto_llcScale_atTop {a b : ℝ} (ha : a < 0) :
    Tendsto (llcScale a b) (𝓝[>] (0 : ℝ)) atTop := by
  have hcomp : Tendsto (fun t : ℝ => Real.exp (-a * t) * t ^ (b - 1)) atTop atTop :=
    tendsto_exp_mul_mul_rpow_atTop (neg_pos.mpr ha)
  refine (hcomp.comp tendsto_neg_log_nhdsGT_zero).congr' ?_
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  exact (llcScale_eq_comp hε.1 a b).symm

/-! ## Scale comparison: distinct exponents are not Θ-comparable -/

theorem llcScale_div_eq {ε : ℝ} (hε : ε ∈ Ioo (0 : ℝ) 1) (p q r s : ℝ) :
    llcScale p r ε / llcScale q s ε =
      Real.exp ((q - p) * -Real.log ε) * (-Real.log ε) ^ (r - s) := by
  have hlog : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε.1 hε.2)
  rw [llcScale_eq_comp hε.1 p r, llcScale_eq_comp hε.1 q s, mul_div_mul_comm,
    ← Real.exp_sub, ← Real.rpow_sub hlog,
    show -p * -Real.log ε - -q * -Real.log ε = (q - p) * -Real.log ε by ring,
    show r - 1 - (s - 1) = r - s by ring]

/-- If `p < q`, or `p = q` and `s < r`, the ratio
`llcScale p r / llcScale q s` blows up at `0⁺`. -/
theorem tendsto_llcScale_div_atTop {p q r s : ℝ} (h : p < q ∨ p = q ∧ s < r) :
    Tendsto (fun ε => llcScale p r ε / llcScale q s ε) (𝓝[>] (0 : ℝ)) atTop := by
  have hcomp : Tendsto (fun t : ℝ => Real.exp ((q - p) * t) * t ^ (r - s)) atTop atTop := by
    rcases h with hpq | ⟨rfl, hsr⟩
    · exact tendsto_exp_mul_mul_rpow_atTop (sub_pos.mpr hpq)
    · simpa using tendsto_rpow_atTop (sub_pos.mpr hsr)
  refine (hcomp.comp tendsto_neg_log_nhdsGT_zero).congr' ?_
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  exact (llcScale_div_eq hε p q r s).symm

theorem not_isBigO_llcScale {p q r s : ℝ} (h : p < q ∨ p = q ∧ s < r) :
    ¬(llcScale p r) =O[𝓝[>] (0 : ℝ)] (llcScale q s) := by
  intro hO
  have hne : ∀ᶠ ε in 𝓝[>] (0 : ℝ), llcScale q s ε ≠ 0 :=
    llcScale_eventually_pos.mono fun ε hε => hε.ne'
  have hbdd := (isBigO_iff_isBoundedUnder_le_div hne).mp hO
  have htop : Tendsto (fun ε => ‖llcScale p r ε‖ / ‖llcScale q s ε‖)
      (𝓝[>] (0 : ℝ)) atTop := by
    refine (tendsto_llcScale_div_atTop h).congr' ?_
    filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
    rw [Real.norm_of_nonneg (llcScale_pos hε).le,
      Real.norm_of_nonneg (llcScale_pos hε).le]
  exact not_isBoundedUnder_of_tendsto_atTop htop hbdd

/-- Scale comparison: two scales are Θ-comparable at `0⁺` iff their exponents
agree. The real content of uniqueness. -/
theorem llcScale_isTheta_iff_eq {a b a' b' : ℝ} :
    (llcScale a b) =Θ[𝓝[>] (0 : ℝ)] (llcScale a' b') ↔ a = a' ∧ b = b' := by
  constructor
  · intro h
    rcases lt_trichotomy a a' with hlt | heq | hgt
    · exact absurd h.1 (not_isBigO_llcScale (Or.inl hlt))
    · subst heq
      rcases lt_trichotomy b b' with hbb | heqb | hbb
      · exact absurd h.2 (not_isBigO_llcScale (Or.inr ⟨rfl, hbb⟩))
      · exact ⟨rfl, heqb⟩
      · exact absurd h.1 (not_isBigO_llcScale (Or.inr ⟨rfl, hbb⟩))
    · exact absurd h.2 (not_isBigO_llcScale (Or.inl hgt))
  · rintro ⟨rfl, rfl⟩
    exact isTheta_rfl

/-! ## Uniqueness -/

/-- Uniqueness of the exponents under two-sided bounds: no positivity or
finiteness hypotheses are needed. -/
theorem HasLLCExponentsOn.unique {l₁ t₁ l₂ t₂ : ℝ}
    (h₁ : HasLLCExponentsOn μ K f l₁ t₁) (h₂ : HasLLCExponentsOn μ K f l₂ t₂) :
    l₁ = l₂ ∧ t₁ = t₂ :=
  llcScale_isTheta_iff_eq.mp (h₁.symm.trans h₂)

/-- A positive-constant `HasLLCOn` yields the exponent-level form. -/
theorem HasLLCOn.hasLLCExponentsOn {lam theta c : ℝ}
    (h : HasLLCOn μ K f lam theta c) (hc : 0 < c) :
    HasLLCExponentsOn μ K f lam theta := by
  constructor
  · refine isBigO_of_div_tendsto_nhds ?_ c h
    exact llcScale_eventually_pos.mono fun ε hε h0 => absurd h0 hε.ne'
  · exact isBigO_of_div_tendsto_nhds_of_ne_zero h hc.ne'

/-- With the exponents fixed, the constant is unique — no positivity needed. -/
theorem HasLLCOn.unique_const {lam theta c₁ c₂ : ℝ}
    (h₁ : HasLLCOn μ K f lam theta c₁) (h₂ : HasLLCOn μ K f lam theta c₂) :
    c₁ = c₂ :=
  tendsto_nhds_unique h₁ h₂

/-- Full uniqueness of `(λ, θ, c)` for positive constants. -/
theorem HasLLCOn.unique {l₁ t₁ c₁ l₂ t₂ c₂ : ℝ}
    (h₁ : HasLLCOn μ K f l₁ t₁ c₁) (h₂ : HasLLCOn μ K f l₂ t₂ c₂)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) : l₁ = l₂ ∧ t₁ = t₂ ∧ c₁ = c₂ := by
  obtain ⟨hl, ht⟩ := (h₁.hasLLCExponentsOn hc₁).unique (h₂.hasLLCExponentsOn hc₂)
  subst hl; subst ht
  exact ⟨rfl, rfl, h₁.unique_const h₂⟩

/-! ## Two-sided bounds -/

/-- `HasLLCExponentsOn` unfolded to explicit two-sided eventual bounds
`c₁ · scale ≤ V ≤ c₂ · scale` with positive constants. -/
theorem hasLLCExponentsOn_iff_eventually_bounds {lam theta : ℝ} :
    HasLLCExponentsOn μ K f lam theta ↔
      ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        c₁ * llcScale lam theta ε ≤ sublevelVol μ K f ε ∧
        sublevelVol μ K f ε ≤ c₂ * llcScale lam theta ε := by
  constructor
  · rintro ⟨hVO, hOV⟩
    obtain ⟨c₂, hc₂, hb₂⟩ := isBigO_iff'.mp hVO
    obtain ⟨C, hC, hb₁⟩ := isBigO_iff'.mp hOV
    refine ⟨C⁻¹, by positivity, c₂, hc₂, ?_⟩
    filter_upwards [hb₂, hb₁, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε h₂ h₁ hε
    rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K f ε),
      Real.norm_of_nonneg (llcScale_pos hε).le] at h₂ h₁
    refine ⟨?_, h₂⟩
    have h3 : C⁻¹ * llcScale lam theta ε ≤ C⁻¹ * (C * sublevelVol μ K f ε) :=
      mul_le_mul_of_nonneg_left h₁ (inv_pos.mpr hC).le
    rwa [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul] at h3
  · rintro ⟨c₁, hc₁, c₂, hc₂, h⟩
    constructor
    · rw [isBigO_iff]
      refine ⟨c₂, ?_⟩
      filter_upwards [h, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hb hε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K f ε),
        Real.norm_of_nonneg (llcScale_pos hε).le]
      exact hb.2
    · rw [isBigO_iff]
      refine ⟨c₁⁻¹, ?_⟩
      filter_upwards [h, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hb hε
      rw [Real.norm_of_nonneg (llcScale_pos hε).le,
        Real.norm_of_nonneg (sublevelVol_nonneg μ K f ε)]
      have h3 : c₁⁻¹ * (c₁ * llcScale lam theta ε) ≤ c₁⁻¹ * sublevelVol μ K f ε :=
        mul_le_mul_of_nonneg_left hb.1 (inv_pos.mpr hc₁).le
      rwa [← mul_assoc, inv_mul_cancel₀ hc₁.ne', one_mul] at h3

/-! ## `IsEquivalent` forms -/

/-- For `c ≠ 0`, `HasLLCOn` gives asymptotic equivalence with `c · scale`. -/
theorem HasLLCOn.isEquivalent {lam theta c : ℝ}
    (h : HasLLCOn μ K f lam theta c) (hc : c ≠ 0) :
    (sublevelVol μ K f) ~[𝓝[>] (0 : ℝ)] (fun ε => c * llcScale lam theta ε) := by
  have hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * llcScale lam theta ε ≠ 0 :=
    llcScale_eventually_pos.mono fun ε hε => mul_ne_zero hc hε.ne'
  rw [isEquivalent_iff_tendsto_one hz]
  have h1 : Tendsto (fun ε => c⁻¹ * (sublevelVol μ K f ε / llcScale lam theta ε))
      (𝓝[>] (0 : ℝ)) (𝓝 (c⁻¹ * c)) := h.const_mul c⁻¹
  rw [inv_mul_cancel₀ hc] at h1
  refine h1.congr' (Eventually.of_forall fun ε => ?_)
  change c⁻¹ * (sublevelVol μ K f ε / llcScale lam theta ε)
      = (sublevelVol μ K f / fun ε => c * llcScale lam theta ε) ε
  rw [Pi.div_apply]
  field_simp

/-- Converse of `HasLLCOn.isEquivalent`. -/
theorem hasLLCOn_of_isEquivalent {lam theta c : ℝ}
    (h : (sublevelVol μ K f) ~[𝓝[>] (0 : ℝ)] (fun ε => c * llcScale lam theta ε))
    (hc : c ≠ 0) : HasLLCOn μ K f lam theta c := by
  have hz : ∀ᶠ ε in 𝓝[>] (0 : ℝ), c * llcScale lam theta ε ≠ 0 :=
    llcScale_eventually_pos.mono fun ε hε => mul_ne_zero hc hε.ne'
  rw [isEquivalent_iff_tendsto_one hz] at h
  have h1 : Tendsto (fun ε => c * (sublevelVol μ K f / fun ε => c * llcScale lam theta ε) ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (c * 1)) := h.const_mul c
  rw [mul_one] at h1
  refine h1.congr' (Eventually.of_forall fun ε => ?_)
  change c * (sublevelVol μ K f ε / (c * llcScale lam theta ε))
      = sublevelVol μ K f ε / llcScale lam theta ε
  field_simp

/-! ## The zero function -/

/-- The zero function has `(λ, θ, c) = (0, 1, μ(K).toReal)` on any `K`:
`sublevelVol μ K (fun _ => 0) ε = (μ K).toReal` for all `ε > 0` and the scale
is identically `1`. (When `μ K = ∞` this degenerates to the true-but-vacuous
`c = 0` instance.) -/
theorem hasLLCOn_const_zero (μ : Measure α) (K : Set α) :
    HasLLCOn μ K (fun _ => 0) 0 1 (μ K).toReal := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with ε hε
  simp [sublevelVol, llcScale, (Set.mem_Ioi.mp hε).le]

end SingularLearningTheory
