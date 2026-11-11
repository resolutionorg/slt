/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.Invariance
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Domination comparison for the volume-scaling exponents

A comparison principle for the exponents. Comparisons of learning coefficients through
inclusions of local ideals reduce to it, but it needs no ideals at all: if `g ≤ C·f` pointwise
on `K` with `C > 0`, the sublevel sets nest — `K ∩ {f ≤ ε} ⊆ K ∩ {g ≤ Cε}` — so `g`'s sublevel
volumes dominate `f`'s, and the scale calculus forces the lexicographic exponent comparison

  `λ_g < λ_f  ∨  (λ_g = λ_f ∧ θ_f ≤ θ_g)`

(`HasLLCExponentsOn.lex_le_of_dominated`). Domination makes `g` *more* singular-or-equal:
smaller `λ`, and at equal `λ` a larger-or-equal `θ`. Direction check: `g = x⁴ ≤ x² = f` on
`[-1,1]` has `λ_g = ¼ < ½ = λ_f`.

Mutual domination — the case of equal ideals — then pins both exponents
(`HasLLCExponentsOn.eq_of_mutually_dominated`).

The passage from ideal membership to domination (finite generating families, `⟨G⟩ ⊆ ⟨F⟩` with
bounded coefficients on compact `K` gives `g ≤ C·f`) is not part of this file.

No measure-finiteness hypotheses: the dominating side's own lower bound forces the relevant
measures finite (`toReal` positive ⇒ `≠ ⊤`). Of the corollaries at the end of the file, the
bounded-unit form `HasLLCExponentsOn.of_bounded_unit'` is what the chart-local read-off
(`ChartLocal`) uses to absorb the bounded positive factor of the loss; the unit-factor forms
`mul_unit` and `mul_unit'` are not used elsewhere in the library.
-/

public section

open Filter MeasureTheory Set Asymptotics
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f g : α → ℝ}

/-- Sublevel nesting under pointwise domination: `g ≤ C·f` on `K` puts the
`f`-sublevel set at `ε` inside the `g`-sublevel set at `Cε`. -/
theorem sublevelVol_le_of_dominated {C : ℝ} (hC : 0 < C)
    (hdom : ∀ x ∈ K, g x ≤ C * f x) {ε : ℝ}
    (hfin : μ (K ∩ {x | g x ≤ C * ε}) ≠ ⊤) :
    sublevelVol μ K f ε ≤ sublevelVol μ K g (C * ε) := by
  unfold sublevelVol
  refine ENNReal.toReal_mono hfin (measure_mono ?_)
  rintro x ⟨hxK, hxf⟩
  exact ⟨hxK, le_trans (hdom x hxK) (mul_le_mul_of_nonneg_left hxf hC.le)⟩

/-- The map `ε ↦ Cε` preserves the filter `𝓝[>] 0` (for `C > 0`). -/
theorem _root_.tendsto_const_mul_nhdsGT_zero {C : ℝ} (hC : 0 < C) :
    Tendsto (fun ε : ℝ => C * ε) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  refine (tendsto_div_const_nhdsGT_zero (inv_pos.mpr hC)).congr fun ε => ?_
  rw [div_inv_eq_mul, mul_comm]

/-- Positive form of the scale comparison (contrapositive of
`not_isBigO_llcScale` plus trichotomy): a big-O between scales forces the
lexicographic exponent ordering.  The form used by the domination argument
below. -/
theorem lex_le_of_isBigO_llcScale {lf tf lg tg : ℝ}
    (hO : (llcScale lf tf) =O[𝓝[>] (0 : ℝ)] (llcScale lg tg)) :
    lg < lf ∨ (lg = lf ∧ tf ≤ tg) := by
  by_contra hcon
  obtain ⟨h1, h2⟩ := not_or.mp hcon
  refine not_isBigO_llcScale ?_ hO
  rcases lt_or_eq_of_le (not_lt.mp h1) with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq, not_le.mp fun hle' => h2 ⟨heq.symm, hle'⟩⟩

/-- **Domination comparison.**  Pointwise domination `g ≤ C·f` on `K` forces the
lexicographic exponent comparison: `λ_g < λ_f`, or `λ_g = λ_f` with
`θ_f ≤ θ_g`. -/
theorem HasLLCExponentsOn.lex_le_of_dominated {lf tf lg tg C : ℝ}
    (hf : HasLLCExponentsOn μ K f lf tf) (hg : HasLLCExponentsOn μ K g lg tg)
    (hC : 0 < C) (hdom : ∀ x ∈ K, g x ≤ C * f x) :
    lg < lf ∨ (lg = lf ∧ tf ≤ tg) := by
  refine lex_le_of_isBigO_llcScale ?_
  -- the eventual lower bound of g, transported along ε ↦ Cε
  obtain ⟨c₁, hc₁, c₂, hc₂, hgb⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp hg
  have hmap := tendsto_const_mul_nhdsGT_zero hC
  have hgb' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      c₁ * llcScale lg tg (C * ε) ≤ sublevelVol μ K g (C * ε) ∧
      sublevelVol μ K g (C * ε) ≤ c₂ * llcScale lg tg (C * ε) :=
    hmap.eventually hgb
  -- eventual finiteness of the dominating sublevel measure
  have hfin : ∀ᶠ ε in 𝓝[>] (0 : ℝ), μ (K ∩ {x | g x ≤ C * ε}) ≠ ⊤ := by
    filter_upwards [hgb', hmap.eventually (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hb hCε
    intro htop
    have h0 : sublevelVol μ K g (C * ε) = 0 := by
      unfold sublevelVol
      rw [htop, ENNReal.toReal_top]
    have := hb.1
    rw [h0] at this
    have hpos : 0 < c₁ * llcScale lg tg (C * ε) :=
      mul_pos hc₁ (llcScale_pos hCε)
    linarith
  -- V_f(ε) ≤ V_g(Cε) eventually
  have hVle : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      sublevelVol μ K f ε ≤ sublevelVol μ K g (C * ε) := by
    filter_upwards [hfin] with ε hfε
    exact sublevelVol_le_of_dominated hC hdom hfε
  -- chain: scale_f =O V_f =O V_g(C·) =O scale_g(C·) =Θ scale_g
  have h1 : (llcScale lf tf) =O[𝓝[>] (0 : ℝ)] (sublevelVol μ K f) := hf.symm.1
  have h2 : (sublevelVol μ K f) =O[𝓝[>] (0 : ℝ)]
      (fun ε => sublevelVol μ K g (C * ε)) := by
    rw [isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [hVle] with ε hε
    rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K f ε),
      Real.norm_of_nonneg (sublevelVol_nonneg μ K g (C * ε)), one_mul]
    exact hε
  have h3 : (fun ε => sublevelVol μ K g (C * ε)) =O[𝓝[>] (0 : ℝ)]
      (fun ε => llcScale lg tg (C * ε)) := hg.1.comp_tendsto hmap
  have h4 : (fun ε => llcScale lg tg (C * ε)) =Θ[𝓝[>] (0 : ℝ)]
      (llcScale lg tg) := by
    simpa [div_inv_eq_mul, mul_comm] using
      isTheta_llcScale_comp_div (lam := lg) (theta := tg) (c := C⁻¹) (inv_pos.mpr hC)
  exact ((h1.trans h2).trans h3).trans h4.1

/-- Mutual domination transfers the exponents themselves: if `g` has
exponents `(λ, θ)` on `K` and `f`, `g` dominate each other pointwise on
`K`, then `f` has the same exponents. (The existence-transfer counterpart
of `eq_of_mutually_dominated`.) -/
theorem HasLLCExponentsOn.of_mutually_dominated {lg tg C C' : ℝ}
    (hg : HasLLCExponentsOn μ K g lg tg) (hC : 0 < C) (hC' : 0 < C')
    (hdom : ∀ x ∈ K, g x ≤ C * f x) (hdom' : ∀ x ∈ K, f x ≤ C' * g x) :
    HasLLCExponentsOn μ K f lg tg := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hgb⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp hg
  have hmapC := tendsto_const_mul_nhdsGT_zero hC
  have hmapC'inv := tendsto_const_mul_nhdsGT_zero (inv_pos.mpr hC')
  -- eventual finiteness of the g-sublevel measure at scaled thresholds `D·ε`
  have hfin : ∀ D : ℝ, 0 < D → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      μ (K ∩ {x | g x ≤ D * ε}) ≠ ⊤ := by
    intro D hD
    have hmapD := tendsto_const_mul_nhdsGT_zero hD
    filter_upwards [hmapD.eventually hgb,
      hmapD.eventually (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hb hDε
    intro htop
    have h0 : sublevelVol μ K g (D * ε) = 0 := by
      unfold sublevelVol
      rw [htop, ENNReal.toReal_top]
    have h1 := hb.1
    rw [h0] at h1
    have hpos : 0 < c₁ * llcScale lg tg (D * ε) :=
      mul_pos hc₁ (llcScale_pos hDε)
    linarith
  constructor
  · -- V_f =O scale: V_f(ε) ≤ V_g(Cε) =O scale(C·) =Θ scale
    have hVle : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        sublevelVol μ K f ε ≤ sublevelVol μ K g (C * ε) := by
      filter_upwards [hfin C hC] with ε hfε
      exact sublevelVol_le_of_dominated hC hdom hfε
    have h2 : (sublevelVol μ K f) =O[𝓝[>] (0 : ℝ)]
        (fun ε => sublevelVol μ K g (C * ε)) := by
      rw [isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [hVle] with ε hε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K f ε),
        Real.norm_of_nonneg (sublevelVol_nonneg μ K g (C * ε)), one_mul]
      exact hε
    have h3 : (fun ε => sublevelVol μ K g (C * ε)) =O[𝓝[>] (0 : ℝ)]
        (fun ε => llcScale lg tg (C * ε)) := hg.1.comp_tendsto hmapC
    have h4 : (fun ε => llcScale lg tg (C * ε)) =Θ[𝓝[>] (0 : ℝ)]
        (llcScale lg tg) := by
      simpa [div_inv_eq_mul, mul_comm] using
        isTheta_llcScale_comp_div (lam := lg) (theta := tg) (c := C⁻¹) (inv_pos.mpr hC)
    exact (h2.trans h3).trans h4.1
  · -- scale =O V_f: scale =Θ scale(C'⁻¹·) =O V_g(C'⁻¹·) ≤ V_f
    have hVle' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        sublevelVol μ K g (C'⁻¹ * ε) ≤ sublevelVol μ K f ε := by
      have hfin' : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          μ (K ∩ {x | f x ≤ C' * (C'⁻¹ * ε)}) ≠ ⊤ := by
        filter_upwards [hfin C hC] with ε hgε htop
        refine hgε (top_le_iff.mp (htop ▸ measure_mono ?_))
        rintro x ⟨hxK, hxf⟩
        refine ⟨hxK, le_trans (hdom x hxK) ?_⟩
        have : f x ≤ ε := by
          rw [mul_inv_cancel_left₀ hC'.ne'] at hxf
          exact hxf
        exact mul_le_mul_of_nonneg_left this hC.le
      have hstep : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
          sublevelVol μ K g (C'⁻¹ * ε)
            ≤ sublevelVol μ K f (C' * (C'⁻¹ * ε)) := by
        filter_upwards [hfin'] with ε hfε
        exact sublevelVol_le_of_dominated hC' hdom' hfε
      filter_upwards [hstep] with ε hε
      rwa [mul_inv_cancel_left₀ hC'.ne'] at hε
    have h2' : (fun ε => sublevelVol μ K g (C'⁻¹ * ε)) =O[𝓝[>] (0 : ℝ)]
        (sublevelVol μ K f) := by
      rw [isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [hVle'] with ε hε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K g (C'⁻¹ * ε)),
        Real.norm_of_nonneg (sublevelVol_nonneg μ K f ε), one_mul]
      exact hε
    have h3' : (fun ε => llcScale lg tg (C'⁻¹ * ε)) =O[𝓝[>] (0 : ℝ)]
        (fun ε => sublevelVol μ K g (C'⁻¹ * ε)) :=
      hg.symm.1.comp_tendsto hmapC'inv
    have h4' : (llcScale lg tg) =Θ[𝓝[>] (0 : ℝ)]
        (fun ε => llcScale lg tg (C'⁻¹ * ε)) := by
      simpa [div_eq_mul_inv, mul_comm] using
        (isTheta_llcScale_comp_div (lam := lg) (theta := tg) (c := C') hC').symm
    exact (h4'.1.trans h3').trans h2'

/-- **Mutual domination.**  Mutual domination pins both exponents. -/
theorem HasLLCExponentsOn.eq_of_mutually_dominated {lf tf lg tg C C' : ℝ}
    (hf : HasLLCExponentsOn μ K f lf tf) (hg : HasLLCExponentsOn μ K g lg tg)
    (hC : 0 < C) (hC' : 0 < C')
    (hdom : ∀ x ∈ K, g x ≤ C * f x) (hdom' : ∀ x ∈ K, f x ≤ C' * g x) :
    lf = lg ∧ tf = tg :=
  hf.unique (hg.of_mutually_dominated hC hC' hdom hdom')

/-- Bounded-unit equivalence without a finiteness hypothesis (compare
`HasLLCExponentsOn.of_bounded_unit` in `Invariance`): `μ K ≠ ∞` is not needed — the
known side's eventual
lower bound itself forces the finiteness of every sublevel measure the
nesting argument touches, and the whole transfer is an `IsTheta`
composition through the scale-shift absorber. -/
theorem HasLLCExponentsOn.of_bounded_unit' {g : α → ℝ} {c₁ c₂ lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hfg : ∀ x ∈ K, c₁ * f x ≤ g x) (hgf : ∀ x ∈ K, g x ≤ c₂ * f x) :
    HasLLCExponentsOn μ K g lam theta := by
  have hm₁ := tendsto_div_const_nhdsGT_zero hc₁
  have hm₂ := tendsto_div_const_nhdsGT_zero hc₂
  -- f's sublevel measures are eventually finite (forced by the lower bound)
  obtain ⟨d₁, hd₁, d₂, hd₂, hb⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp h
  have hffin : ∀ᶠ δ in 𝓝[>] (0:ℝ), μ (K ∩ {x | f x ≤ δ}) ≠ ⊤ := by
    filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with δ hbδ hδ
    intro htop
    have h0 : sublevelVol μ K f δ = 0 := by
      rw [sublevelVol, htop, ENNReal.toReal_top]
    have := lt_of_lt_of_le (mul_pos hd₁ (llcScale_pos hδ)) hbδ.1
    rw [h0] at this
    exact lt_irrefl 0 this
  -- nesting at the measure level
  have hsub₁ : ∀ ε : ℝ, K ∩ {x | g x ≤ ε} ⊆ K ∩ {x | f x ≤ ε / c₁} := by
    rintro ε x ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [mem_ofPred_eq] at hx ⊢
    rw [le_div_iff₀ hc₁, mul_comm]
    exact le_trans (hfg x hxK) hx
  have hsub₂ : ∀ ε : ℝ, K ∩ {x | f x ≤ ε / c₂} ⊆ K ∩ {x | g x ≤ ε} := by
    rintro ε x ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [mem_ofPred_eq] at hx ⊢
    rw [le_div_iff₀ hc₂, mul_comm] at hx
    exact le_trans (hgf x hxK) hx
  -- the two IsBigO arms
  constructor
  · -- V_g =O scale
    have harm : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        sublevelVol μ K g ε ≤ sublevelVol μ K f (ε / c₁) := by
      filter_upwards [hm₁.eventually hffin] with ε hfε
      exact ENNReal.toReal_mono hfε (measure_mono (hsub₁ ε))
    have h1 : (sublevelVol μ K g) =O[𝓝[>] (0:ℝ)]
        (fun ε => sublevelVol μ K f (ε / c₁)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [harm] with ε hε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K g ε),
        Real.norm_of_nonneg (sublevelVol_nonneg μ K f _), one_mul]
      exact hε
    have h2 : (fun ε => sublevelVol μ K f (ε / c₁)) =O[𝓝[>] (0:ℝ)]
        (fun ε => llcScale lam theta (ε / c₁)) := h.1.comp_tendsto hm₁
    exact (h1.trans h2).trans (isTheta_llcScale_comp_div hc₁).1
  · -- scale =O V_g
    have harm : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        sublevelVol μ K f (ε / c₂) ≤ sublevelVol μ K g ε := by
      filter_upwards [hm₁.eventually hffin] with ε hf₁
      have hgfin : μ (K ∩ {x | g x ≤ ε}) ≠ ⊤ :=
        (lt_of_le_of_lt (measure_mono (hsub₁ ε))
          (lt_top_iff_ne_top.mpr hf₁)).ne
      exact ENNReal.toReal_mono hgfin (measure_mono (hsub₂ ε))
    have h1 : (fun ε => sublevelVol μ K f (ε / c₂)) =O[𝓝[>] (0:ℝ)]
        (sublevelVol μ K g) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [harm] with ε hε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K f _),
        Real.norm_of_nonneg (sublevelVol_nonneg μ K g ε), one_mul]
      exact hε
    have h2 : (fun ε => llcScale lam theta (ε / c₂)) =O[𝓝[>] (0:ℝ)]
        (fun ε => sublevelVol μ K f (ε / c₂)) := h.symm.1.comp_tendsto hm₂
    exact ((isTheta_llcScale_comp_div hc₂).symm.1.trans h2).trans h1

/-- **The unit-factor corollary**: multiplying a nonnegative loss by a factor
pinched between positive constants moves neither exponent. -/
theorem HasLLCExponentsOn.mul_unit {u : α → ℝ} {c₁ c₂ lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta) (hf : ∀ x ∈ K, 0 ≤ f x)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hu : ∀ x ∈ K, c₁ ≤ u x ∧ u x ≤ c₂) :
    HasLLCExponentsOn μ K (fun x => u x * f x) lam theta :=
  h.of_bounded_unit' hc₁ hc₂
    (fun x hx => mul_le_mul_of_nonneg_right (hu x hx).1 (hf x hx))
    (fun x hx => mul_le_mul_of_nonneg_right (hu x hx).2 (hf x hx))

/-- **The unit-factor corollary without the sign condition**: the sign
condition on `f` is an artifact of wrapping through multiplicative bounds —
running the sublevel sandwich directly needs only `ε > 0`, since a negative
`f x` satisfies any positive threshold trivially. -/
theorem HasLLCExponentsOn.mul_unit' {u : α → ℝ} {c₁ c₂ lam theta : ℝ}
    (h : HasLLCExponentsOn μ K f lam theta)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hu : ∀ x ∈ K, c₁ ≤ u x ∧ u x ≤ c₂) :
    HasLLCExponentsOn μ K (fun x => u x * f x) lam theta := by
  have hm₁ := tendsto_div_const_nhdsGT_zero hc₁
  have hm₂ := tendsto_div_const_nhdsGT_zero hc₂
  obtain ⟨d₁, hd₁, d₂, hd₂, hb⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp h
  have hffin : ∀ᶠ δ in 𝓝[>] (0:ℝ), μ (K ∩ {x | f x ≤ δ}) ≠ ⊤ := by
    filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with δ hbδ hδ
    intro htop
    have h0 : sublevelVol μ K f δ = 0 := by
      rw [sublevelVol, htop, ENNReal.toReal_top]
    have := lt_of_lt_of_le (mul_pos hd₁ (llcScale_pos hδ)) hbδ.1
    rw [h0] at this
    exact lt_irrefl 0 this
  have hsub₁ : ∀ ε : ℝ, 0 < ε →
      K ∩ {x | u x * f x ≤ ε} ⊆ K ∩ {x | f x ≤ ε / c₁} := by
    rintro ε hε x ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [mem_ofPred_eq] at hx ⊢
    rcases le_or_gt (f x) 0 with hf0 | hf0
    · exact le_trans hf0 (by positivity)
    · rw [le_div_iff₀ hc₁, mul_comm]
      calc c₁ * f x ≤ u x * f x :=
            mul_le_mul_of_nonneg_right (hu x hxK).1 hf0.le
        _ ≤ ε := hx
  have hsub₂ : ∀ ε : ℝ, 0 < ε →
      K ∩ {x | f x ≤ ε / c₂} ⊆ K ∩ {x | u x * f x ≤ ε} := by
    rintro ε hε x ⟨hxK, hx⟩
    refine ⟨hxK, ?_⟩
    rw [mem_ofPred_eq] at hx ⊢
    rcases le_or_gt (f x) 0 with hf0 | hf0
    · calc u x * f x ≤ u x * 0 :=
            mul_le_mul_of_nonneg_left hf0
              (le_trans hc₁.le (hu x hxK).1)
        _ = 0 := mul_zero _
        _ ≤ ε := hε.le
    · calc u x * f x ≤ c₂ * f x :=
            mul_le_mul_of_nonneg_right (hu x hxK).2 hf0.le
        _ ≤ c₂ * (ε / c₂) := by
            exact mul_le_mul_of_nonneg_left hx hc₂.le
        _ = ε := by field_simp
  constructor
  · have harm : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        sublevelVol μ K (fun x => u x * f x) ε ≤ sublevelVol μ K f (ε / c₁) := by
      filter_upwards [hm₁.eventually hffin, self_mem_nhdsWithin]
        with ε hfε (hε : 0 < ε)
      exact ENNReal.toReal_mono hfε (measure_mono (hsub₁ ε hε))
    have h1 : (sublevelVol μ K (fun x => u x * f x)) =O[𝓝[>] (0:ℝ)]
        (fun ε => sublevelVol μ K f (ε / c₁)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [harm] with ε hε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K _ ε),
        Real.norm_of_nonneg (sublevelVol_nonneg μ K f _), one_mul]
      exact hε
    exact (h1.trans (h.1.comp_tendsto hm₁)).trans
      (isTheta_llcScale_comp_div hc₁).1
  · have harm : ∀ᶠ ε in 𝓝[>] (0:ℝ),
        sublevelVol μ K f (ε / c₂) ≤ sublevelVol μ K (fun x => u x * f x) ε := by
      filter_upwards [hm₁.eventually hffin, self_mem_nhdsWithin]
        with ε hf₁ (hε : 0 < ε)
      have hgfin : μ (K ∩ {x | u x * f x ≤ ε}) ≠ ⊤ :=
        (lt_of_le_of_lt (measure_mono (hsub₁ ε hε))
          (lt_top_iff_ne_top.mpr hf₁)).ne
      exact ENNReal.toReal_mono hgfin (measure_mono (hsub₂ ε hε))
    have h1 : (fun ε => sublevelVol μ K f (ε / c₂)) =O[𝓝[>] (0:ℝ)]
        (sublevelVol μ K (fun x => u x * f x)) := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨1, ?_⟩
      filter_upwards [harm] with ε hε
      rw [Real.norm_of_nonneg (sublevelVol_nonneg μ K f _),
        Real.norm_of_nonneg (sublevelVol_nonneg μ K _ ε), one_mul]
      exact hε
    exact ((isTheta_llcScale_comp_div hc₂).symm.1.trans
      (h.symm.1.comp_tendsto hm₂)).trans h1

end SingularLearningTheory
