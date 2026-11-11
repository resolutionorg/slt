/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Invariance of the learning-coefficient exponents

Two facts of the form "the exponents `(λ, θ)` of `HasLLCExponentsOn` do not change under tame
modifications of the data":

* **Bounded-unit equivalence** — if `c₁·f ≤ g ≤ c₂·f` on `K` with `0 < c₁, c₂`, then `g`
  inherits `f`'s exponents (the constants get absorbed, which is exactly why this is a
  statement about `HasLLCExponentsOn` and not `HasLLCOn`).
* **Weight (prior) invariance** — re-weighting the measure by a density pinched between
  positive constants on `K` moves neither exponent (`HasLLCExponentsOn.withDensity`).

The analytic ingredient is dilation stability of the model scale:
`llcScale lam theta (ε/c) =Θ[𝓝[>] 0] llcScale lam theta`, via the ratio limit
`scale(ε/c)/scale(ε) → c^(−λ)`.

The finiteness hypothesis `μ K ≠ ∞` is load-bearing here: `ENNReal.toReal` is not monotone at
`∞`, and every sublevel set lies inside `K`, so finite `K`-mass makes the sandwich
`V_f(ε/c₂) ≤ V_g(ε) ≤ V_f(ε/c₁)` valid in `ℝ`. All intended applications have `K` compact. (A
finiteness-free variant of the bounded-unit transfer is `HasLLCExponentsOn.of_bounded_unit'` in
`Comparison`.) The square-threshold transfer at the end of the file lets the even-exponent
monomial read-off serve arbitrary exponents (`ArbitraryExponent`). Invariance under
measure-preserving changes of variables is in `Transport`.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal NNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f : α → ℝ}

/-- Dilation by a positive constant maps `𝓝[>] 0` to itself. -/
theorem _root_.tendsto_div_const_nhdsGT_zero {c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε : ℝ => ε / c) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h := (tendsto_id (x := 𝓝 (0 : ℝ))).div_const c
    rw [zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact div_pos hε hc

/-- The scale ratio under dilation converges: `scale(ε/c)/scale(ε) → c^(−λ)`.
(The `θ`-dependent log factor contributes only `(1 + log c/(−log ε))^(θ−1) → 1`.) -/
theorem tendsto_llcScale_div_const_ratio {lam theta c : ℝ} (hc : 0 < c) :
    Tendsto (fun ε => llcScale lam theta (ε / c) / llcScale lam theta ε)
      (𝓝[>] (0 : ℝ)) (𝓝 (c ^ (-lam))) := by
  have hinv : Tendsto (fun ε : ℝ => Real.log c * (-Real.log ε)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using (tendsto_neg_log_nhdsGT_zero.inv_tendsto_atTop).const_mul (Real.log c)
  have hbase : Tendsto (fun ε : ℝ => 1 + Real.log c * (-Real.log ε)⁻¹)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using (tendsto_const_nhds (α := ℝ) (x := (1 : ℝ))).add hinv
  have hpow : Tendsto (fun ε : ℝ => (1 + Real.log c * (-Real.log ε)⁻¹) ^ (theta - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hcont := (Real.continuousAt_rpow_const 1 (theta - 1) (Or.inl one_ne_zero)).tendsto
    have hcomp := hcont.comp hbase
    simpa [Function.comp_def, Real.one_rpow] using hcomp
  have hmul : Tendsto
      (fun ε : ℝ => c ^ (-lam) * (1 + Real.log c * (-Real.log ε)⁻¹) ^ (theta - 1))
      (𝓝[>] (0 : ℝ)) (𝓝 (c ^ (-lam))) := by
    simpa using hpow.const_mul (c ^ (-lam))
  refine hmul.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (lt_min one_pos hc)] with ε hε
  have hε0 : (0 : ℝ) < ε := hε.1
  have hε1 : ε < 1 := lt_of_lt_of_le hε.2 (min_le_left _ _)
  have hεc : ε < c := lt_of_lt_of_le hε.2 (min_le_right _ _)
  have ht : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε0 hε1)
  have hd0 : 0 < ε / c := div_pos hε0 hc
  have hd1 : ε / c < 1 := (div_lt_one hc).mpr hεc
  have ht' : 0 < -Real.log (ε / c) := neg_pos.mpr (Real.log_neg hd0 hd1)
  have h1 : Real.log ε ≠ 0 := (neg_pos.mp ht).ne
  have hbase_eq : (1 : ℝ) + Real.log c * (-Real.log ε)⁻¹
      = -Real.log (ε / c) / -Real.log ε := by
    rw [Real.log_div hε0.ne' hc.ne']
    field_simp
    ring
  rw [hbase_eq]
  unfold llcScale
  rw [mul_div_mul_comm, ← Real.div_rpow hd0.le hε0.le,
    (show ε / c / ε = c⁻¹ by field_simp),
    Real.inv_rpow hc.le, ← Real.rpow_neg hc.le,
    ← Real.div_rpow ht'.le ht.le]

/-- `llcScale` is Θ-stable under ε-dilation. -/
theorem isTheta_llcScale_comp_div {lam theta c : ℝ} (hc : 0 < c) :
    (fun ε => llcScale lam theta (ε / c)) =Θ[𝓝[>] (0 : ℝ)] llcScale lam theta := by
  have hr := tendsto_llcScale_div_const_ratio (lam := lam) (theta := theta) hc
  constructor
  · refine isBigO_of_div_tendsto_nhds ?_ _ hr
    exact llcScale_eventually_pos.mono fun ε hε h0 => absurd h0 hε.ne'
  · exact isBigO_of_div_tendsto_nhds_of_ne_zero hr (Real.rpow_pos_of_pos hc _).ne'

/-- **Bounded-unit equivalence**: if `c₁·f ≤ g ≤ c₂·f` on `K` with
`0 < c₁, c₂` and `μ K ≠ ∞`, then `g` inherits the exponents of `f`. No sign
condition on `f` is needed. -/
theorem HasLLCExponentsOn.of_bounded_unit {g : α → ℝ} {lam theta : ℝ}
    (hK : μ K ≠ ∞) (h : HasLLCExponentsOn μ K f lam theta)
    {c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hfg : ∀ x ∈ K, c₁ * f x ≤ g x) (hgf : ∀ x ∈ K, g x ≤ c₂ * f x) :
    HasLLCExponentsOn μ K g lam theta := by
  have hfin : ∀ (h : α → ℝ) (ε : ℝ), μ (K ∩ {x | h x ≤ ε}) ≠ ∞ := fun h ε =>
    (lt_of_le_of_lt (measure_mono inter_subset_left) (lt_top_iff_ne_top.mpr hK)).ne
  have hupper : ∀ ε : ℝ, sublevelVol μ K g ε ≤ sublevelVol μ K f (ε / c₁) := by
    intro ε
    refine ENNReal.toReal_mono (hfin _ _) (measure_mono ?_)
    rintro x ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [mem_ofPred_eq] at hx ⊢
    rw [le_div_iff₀ hc₁, mul_comm]
    exact le_trans (hfg x hxK) hx
  have hlower : ∀ ε : ℝ, sublevelVol μ K f (ε / c₂) ≤ sublevelVol μ K g ε := by
    intro ε
    refine ENNReal.toReal_mono (hfin _ _) (measure_mono ?_)
    rintro x ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [mem_ofPred_eq] at hx ⊢
    have h3 : c₂ * f x ≤ c₂ * (ε / c₂) := mul_le_mul_of_nonneg_left hx hc₂.le
    have h4 : c₂ * (ε / c₂) = ε := by field_simp
    exact le_trans (hgf x hxK) (h4 ▸ h3)
  have hO_upper : (fun ε => sublevelVol μ K g ε) =O[𝓝[>] (0 : ℝ)]
      (fun ε => sublevelVol μ K f (ε / c₁)) := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards with ε
    rw [one_mul, Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
      Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
    exact hupper ε
  have hO_lower : (fun ε => sublevelVol μ K f (ε / c₂)) =O[𝓝[>] (0 : ℝ)]
      (fun ε => sublevelVol μ K g ε) := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards with ε
    rw [one_mul, Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
      Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
    exact hlower ε
  have hcomp₁ : (fun ε => sublevelVol μ K f (ε / c₁)) =O[𝓝[>] (0 : ℝ)]
      (fun ε => llcScale lam theta (ε / c₁)) :=
    h.1.comp_tendsto (tendsto_div_const_nhdsGT_zero hc₁)
  have hcomp₂ : (fun ε => llcScale lam theta (ε / c₂)) =O[𝓝[>] (0 : ℝ)]
      (fun ε => sublevelVol μ K f (ε / c₂)) :=
    h.2.comp_tendsto (tendsto_div_const_nhdsGT_zero hc₂)
  constructor
  · exact hO_upper.trans (hcomp₁.trans (isTheta_llcScale_comp_div hc₁).1)
  · exact ((isTheta_llcScale_comp_div hc₂).2.trans hcomp₂).trans hO_lower

/-! ## Prior-density invariance -/

open MeasureTheory in
/-- **Weight (prior) invariance**: the exponents are stable under
re-weighting the measure by a density bounded above and below by positive
constants on `K`. Only `K` needs to be measurable — not `f` (the proof
stays on `μ.restrict K` and evaluates at raw sublevel sets via
`restrict_apply'`). For a smooth positive prior on compact `K`, the bounds
are supplied by continuity. -/
theorem HasLLCExponentsOn.withDensity {w : α → ℝ≥0∞} {c₁ c₂ : ℝ≥0}
    {lam theta : ℝ} (hKm : MeasurableSet K) (hK : μ K ≠ ∞) (hc₁ : 0 < c₁)
    (hw : ∀ x ∈ K, (c₁ : ℝ≥0∞) ≤ w x ∧ w x ≤ c₂)
    (h : HasLLCExponentsOn μ K f lam theta) :
    HasLLCExponentsOn (μ.withDensity w) K f lam theta := by
  have hae₁ : (fun _ => (c₁ : ℝ≥0∞)) ≤ᵐ[μ.restrict K] w :=
    (ae_restrict_iff' hKm).mpr (Filter.Eventually.of_forall fun x hx => (hw x hx).1)
  have hae₂ : w ≤ᵐ[μ.restrict K] fun _ => (c₂ : ℝ≥0∞) :=
    (ae_restrict_iff' hKm).mpr (Filter.Eventually.of_forall fun x hx => (hw x hx).2)
  have hlow : (c₁ : ℝ≥0∞) • μ.restrict K ≤ (μ.restrict K).withDensity w := by
    simpa [withDensity_const] using withDensity_mono hae₁
  have hupp : (μ.restrict K).withDensity w ≤ (c₂ : ℝ≥0∞) • μ.restrict K := by
    simpa [withDensity_const] using withDensity_mono hae₂
  -- pointwise ENNReal sandwich on the raw sublevel sets
  have hsand : ∀ ε : ℝ,
      (c₁ : ℝ≥0∞) * μ (K ∩ {x | f x ≤ ε})
        ≤ (μ.withDensity w) (K ∩ {x | f x ≤ ε}) ∧
      (μ.withDensity w) (K ∩ {x | f x ≤ ε})
        ≤ (c₂ : ℝ≥0∞) * μ (K ∩ {x | f x ≤ ε}) := by
    intro ε
    set S := {x | f x ≤ ε}
    have heval : (μ.withDensity w) (K ∩ S)
        = ((μ.restrict K).withDensity w) S := by
      rw [Set.inter_comm K S, ← Measure.restrict_apply' hKm, restrict_withDensity hKm]
    have hbase : μ (K ∩ S) = (μ.restrict K) S := by
      rw [Set.inter_comm K S, ← Measure.restrict_apply' hKm]
    constructor
    · rw [heval, hbase]
      have := Measure.le_iff'.mp hlow S
      simpa [Measure.smul_apply, smul_eq_mul] using this
    · rw [heval, hbase]
      have := Measure.le_iff'.mp hupp S
      simpa [Measure.smul_apply, smul_eq_mul] using this
  -- finiteness
  have hfin : ∀ ε : ℝ, μ (K ∩ {x | f x ≤ ε}) ≠ ∞ := fun ε =>
    (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
      (lt_top_iff_ne_top.mpr hK)).ne
  -- real-valued sandwich
  have hreal : ∀ ε : ℝ,
      (c₁ : ℝ) * sublevelVol μ K f ε ≤ sublevelVol (μ.withDensity w) K f ε ∧
      sublevelVol (μ.withDensity w) K f ε ≤ (c₂ : ℝ) * sublevelVol μ K f ε := by
    intro ε
    obtain ⟨hl, hu⟩ := hsand ε
    have hfinw : (μ.withDensity w) (K ∩ {x | f x ≤ ε}) ≠ ∞ :=
      (lt_of_le_of_lt hu (by
        exact ENNReal.mul_lt_top ENNReal.coe_lt_top
          (lt_top_iff_ne_top.mpr (hfin ε)))).ne
    constructor
    · have := ENNReal.toReal_mono hfinw hl
      rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
    · have := ENNReal.toReal_mono (by
        exact ENNReal.mul_ne_top ENNReal.coe_ne_top (hfin ε)) hu
      rwa [ENNReal.toReal_mul, ENNReal.coe_toReal] at this
  -- V' =Θ V, then transfer through h
  have hΘ : (sublevelVol (μ.withDensity w) K f)
      =Θ[𝓝[>] (0 : ℝ)] (sublevelVol μ K f) := by
    constructor
    · rw [isBigO_iff]
      refine ⟨(c₂ : ℝ), ?_⟩
      filter_upwards with ε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
        Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
      exact (hreal ε).2
    · rw [isBigO_iff]
      refine ⟨((c₁ : ℝ))⁻¹, ?_⟩
      filter_upwards with ε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _),
        Real.norm_of_nonneg (sublevelVol_nonneg _ _ _ _)]
      have hc₁' : (0 : ℝ) < c₁ := hc₁
      rw [inv_mul_eq_div, le_div_iff₀ hc₁', mul_comm]
      exact (hreal ε).1
  exact hΘ.trans h

/-! ## Square-threshold transfer -/

/-- **Square-threshold transfer.** If the squared function `g²` has exponents
`(λ/2, θ)` on `K`, and `g ≥ 0` on `K`, then `g` itself has exponents `(λ, θ)`.

Mechanism: for `ε > 0`, on `K` (where `g ≥ 0`) one has `g ≤ ε ↔ g² ≤ ε²`, so
the sublevel set of `g` at `ε` equals that of `g²` at `ε²`; hence
`V_g(ε) = V_{g²}(ε²)`. Composing the `Θ`-asymptotics of `V_{g²}` with the map
`ε ↦ ε²` (which tends to `0⁺`) and the model identity
`llcScale (λ/2) θ (ε²) = 2^(θ−1)·llcScale λ θ ε` transfers the exponents.

This is the bridge that lets the even-exponent monomial read-off
(stated for `∏|xᵢ|^{2kᵢ}`) serve an arbitrary natural exponent vector `e`:
apply the even read-off to the exponent `2e` — whose monomial is the square of
the `e`-monomial — and peel the square off here. -/
theorem HasLLCExponentsOn.of_sq {g : α → ℝ} {lam theta : ℝ}
    (hg : ∀ x ∈ K, 0 ≤ g x)
    (hsq : HasLLCExponentsOn μ K (fun x => g x ^ 2) (lam / 2) theta) :
    HasLLCExponentsOn μ K g lam theta := by
  -- (1) sublevel set equality for `ε > 0`.
  have hset : ∀ ε : ℝ, 0 < ε →
      K ∩ {x | g x ≤ ε} = K ∩ {x | g x ^ 2 ≤ ε ^ 2} := by
    intro ε hε
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hxK, h⟩; exact ⟨hxK, by nlinarith [hg x hxK]⟩
    · rintro ⟨hxK, h⟩; exact ⟨hxK, by nlinarith [hg x hxK]⟩
  -- (2) `V_g(ε) = V_{g²}(ε²)` eventually on `𝓝[>] 0`.
  have hvol : sublevelVol μ K g =ᶠ[𝓝[>] (0 : ℝ)]
      fun ε => sublevelVol μ K (fun x => g x ^ 2) (ε ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    change (μ (K ∩ {x | g x ≤ ε})).toReal = (μ (K ∩ {x | g x ^ 2 ≤ ε ^ 2})).toReal
    rw [hset ε (Set.mem_Ioi.mp hε)]
  -- (3) `ε ↦ ε²` maps `𝓝[>] 0` into itself.
  have htend : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have h0 : Tendsto (fun ε : ℝ => ε ^ 2) (𝓝 (0 : ℝ)) (𝓝 ((0 : ℝ) ^ 2)) :=
        (continuous_pow 2).tendsto 0
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact Set.mem_Ioi.mpr (pow_pos (Set.mem_Ioi.mp hε) 2)
  -- (4) compose the `g²` asymptotics with `ε ↦ ε²`.
  have hcomp : (fun ε => sublevelVol μ K (fun x => g x ^ 2) (ε ^ 2))
      =Θ[𝓝[>] (0 : ℝ)] fun ε => llcScale (lam / 2) theta (ε ^ 2) := by
    constructor
    · exact hsq.1.comp_tendsto htend
    · exact hsq.2.comp_tendsto htend
  -- (5) model identity `llcScale (λ/2) θ (ε²) = 2^(θ−1)·llcScale λ θ ε`.
  have hscalar : (fun ε : ℝ => llcScale (lam / 2) theta (ε ^ 2))
      =ᶠ[𝓝[>] (0 : ℝ)] fun ε => (2 : ℝ) ^ (theta - 1) * llcScale lam theta ε := by
    filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
    have hε0 : (0 : ℝ) < ε := hε.1
    have hlog : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε.1 hε.2)
    have hbase : (ε ^ 2 : ℝ) ^ (lam / 2) = ε ^ lam := by
      rw [← Real.rpow_natCast ε 2, ← Real.rpow_mul hε0.le]
      congr 1
      push_cast; ring
    have hlogeq : -Real.log (ε ^ 2) = 2 * (-Real.log ε) := by
      rw [Real.log_pow]; push_cast; ring
    simp only [llcScale]
    rw [hbase, hlogeq, Real.mul_rpow (by norm_num) hlog.le]
    ring
  have hc2 : (2 : ℝ) ^ (theta - 1) ≠ 0 := by positivity
  have hmodel : (fun ε : ℝ => llcScale (lam / 2) theta (ε ^ 2))
      =Θ[𝓝[>] (0 : ℝ)] llcScale lam theta :=
    hscalar.isTheta.trans ((isTheta_const_mul_left hc2).mpr isTheta_rfl)
  exact (hvol.isTheta.trans hcomp).trans hmodel

end SingularLearningTheory
