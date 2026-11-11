/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

import SLT.VolumeScaling.Basic
public import SLT.VolumeScaling.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.Topology.Algebra.Module.Determinant
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init


/-!
# C¹-diffeomorphism invariance of the volume-scaling exponents (K0.4)

The last piece of the K0 invariance package: composing the loss with a map
`Φ` whose derivative exists along `K` and whose Jacobian determinant is
bounded above and below by positive constants moves neither `λ` nor `θ`.
This is what K4's blow-up charts consume: each affine chart of a blow-up is
such a map away from the exceptional locus, and A2 transfers per-chart
sublevel volumes through it.

Unlike the affine case (K0.3), the transfer is genuinely *exponent-level*:
the constant picks up the Jacobian distortion (`Φ = 2x`, `f = x²` has
`f∘Φ = 4x²` with the same `(½, 1)` but constant `1` against `2`), so the
statement lives on `HasLLCExponentsOn`.

The proof is a sandwich: the image identity
`Φ '' (K ∩ {f∘Φ ≤ ε}) = (Φ '' K) ∩ {f ≤ ε}` costs nothing
(`Set.image_inter_preimage`), and Mathlib's area formula bounds
(`addHaar_image_le_lintegral_abs_det_fderiv` and, with injectivity,
`lintegral_abs_det_fderiv_le_addHaar_image`) pin

  `c₁ · μ(K ∩ {f∘Φ ≤ ε}) ≤ μ((Φ''K) ∩ {f ≤ ε}) ≤ c₂ · μ(K ∩ {f∘Φ ≤ ε})`.

Measure finiteness for the `toReal` arithmetic is self-certified by the
known side's eventual lower bound (the K1.1 pattern: positive `toReal`
forces a finite measure).
-/

public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

/-- **K0.4.** If `Φ` has derivative `Φ' x` along `K` at every `x ∈ K`, is
injective on `K`, and `c₁ ≤ |det Φ' x| ≤ c₂` with `c₁ > 0`, then
volume-scaling data for `f` on `Φ '' K` transfers to `f ∘ Φ` on `K` with
the same exponents. -/
theorem HasLLCExponentsOn.comp_diffeo {K : Set E} {f : E → ℝ} {Φ : E → E}
    {Φ' : E → E →L[ℝ] E} {c₁ c₂ lam theta : ℝ}
    (hK : MeasurableSet K) (hΦm : Measurable Φ) (hfm : Measurable f)
    (hΦ : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    (hinj : Set.InjOn Φ K) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hdet : ∀ x ∈ K, c₁ ≤ |(Φ' x).det| ∧ |(Φ' x).det| ≤ c₂)
    (h : HasLLCExponentsOn μ (Φ '' K) f lam theta) :
    HasLLCExponentsOn μ K (fun x => f (Φ x)) lam theta := by
  rw [hasLLCExponentsOn_iff_eventually_bounds] at h ⊢
  obtain ⟨d₁, hd₁, d₂, hd₂, hb⟩ := h
  refine ⟨d₁ / c₂, by positivity, d₂ / c₁, by positivity, ?_⟩
  filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hbε hε
  set s : Set E := K ∩ {x | f (Φ x) ≤ ε} with hs
  have hsm : MeasurableSet s :=
    hK.inter ((hfm.comp hΦm) measurableSet_Iic)
  have himg : Φ '' s = (Φ '' K) ∩ {y | f y ≤ ε} := by
    rw [hs, show {x | f (Φ x) ≤ ε} = Φ ⁻¹' {y | f y ≤ ε} from rfl,
      Set.image_inter_preimage]
  -- the ENNReal sandwich
  have hup : μ (Φ '' s) ≤ ENNReal.ofReal c₂ * μ s := by
    refine le_trans (addHaar_image_le_lintegral_abs_det_fderiv μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)) ?_
    calc (∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ)
        ≤ ∫⁻ _ in s, ENNReal.ofReal c₂ ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).2))
      _ = ENNReal.ofReal c₂ * μ s := by
          rw [setLIntegral_const]
  have hlow : ENNReal.ofReal c₁ * μ s ≤ μ (Φ '' s) := by
    refine le_trans ?_ (lintegral_abs_det_fderiv_le_addHaar_image μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)
      (hinj.mono inter_subset_left))
    calc ENNReal.ofReal c₁ * μ s
        = ∫⁻ _ in s, ENNReal.ofReal c₁ ∂μ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).1))
  -- the image volume in the hypothesis bounds
  have hVim : sublevelVol μ (Φ '' K) f ε = (μ (Φ '' s)).toReal := by
    rw [sublevelVol, himg]
  -- finiteness, self-certified by the lower bound of h
  have hpos : 0 < sublevelVol μ (Φ '' K) f ε :=
    lt_of_lt_of_le (mul_pos hd₁ (llcScale_pos hε)) hbε.1
  have himne : μ (Φ '' s) ≠ ⊤ := by
    intro htop
    rw [hVim, htop, ENNReal.toReal_top] at hpos
    exact lt_irrefl 0 hpos
  have hsne : μ s ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (fun h0 =>
      absurd (ENNReal.ofReal_eq_zero.mp h0) (not_le.mpr hc₁))] at hlow
    exact himne (top_le_iff.mp hlow)
  -- pass the sandwich to ℝ
  have hupR : (μ (Φ '' s)).toReal ≤ c₂ * (μ s).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂.le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsne) hup
  have hlowR : c₁ * (μ s).toReal ≤ (μ (Φ '' s)).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁.le] using
      ENNReal.toReal_mono himne hlow
  -- conclude
  have hVs : sublevelVol μ K (fun x => f (Φ x)) ε = (μ s).toReal := rfl
  constructor
  · -- lower: (d₁/c₂)·scale ≤ V_s
    rw [hVs]
    have h1 : d₁ * llcScale lam theta ε ≤ (μ (Φ '' s)).toReal := by
      rw [← hVim]; exact hbε.1
    have h2 := le_trans h1 hupR
    rw [div_mul_eq_mul_div, div_le_iff₀ hc₂]
    simpa [mul_comm] using h2
  · -- upper: V_s ≤ (d₂/c₁)·scale
    rw [hVs]
    have h1 : (μ (Φ '' s)).toReal ≤ d₂ * llcScale lam theta ε := by
      rw [← hVim]; exact hbε.2
    have h2 := le_trans hlowR h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
    simpa [mul_comm] using h2

/-- **K0.4, reverse direction** (same sandwich, no inverse data needed):
volume-scaling data for the pullback `f ∘ Φ` on `K` transfers to `f` on
`Φ '' K` with the same exponents. -/
theorem HasLLCExponentsOn.of_comp_diffeo {K : Set E} {f : E → ℝ} {Φ : E → E}
    {Φ' : E → E →L[ℝ] E} {c₁ c₂ lam theta : ℝ}
    (hK : MeasurableSet K) (hΦm : Measurable Φ) (hfm : Measurable f)
    (hΦ : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    (hinj : Set.InjOn Φ K) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hdet : ∀ x ∈ K, c₁ ≤ |(Φ' x).det| ∧ |(Φ' x).det| ≤ c₂)
    (h : HasLLCExponentsOn μ K (fun x => f (Φ x)) lam theta) :
    HasLLCExponentsOn μ (Φ '' K) f lam theta := by
  rw [hasLLCExponentsOn_iff_eventually_bounds] at h ⊢
  obtain ⟨d₁, hd₁, d₂, hd₂, hb⟩ := h
  refine ⟨d₁ * c₁, by positivity, d₂ * c₂, by positivity, ?_⟩
  filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hbε hε
  set s : Set E := K ∩ {x | f (Φ x) ≤ ε} with hs
  have hsm : MeasurableSet s :=
    hK.inter ((hfm.comp hΦm) measurableSet_Iic)
  have himg : Φ '' s = (Φ '' K) ∩ {y | f y ≤ ε} := by
    rw [hs, show {x | f (Φ x) ≤ ε} = Φ ⁻¹' {y | f y ≤ ε} from rfl,
      Set.image_inter_preimage]
  have hup : μ (Φ '' s) ≤ ENNReal.ofReal c₂ * μ s := by
    refine le_trans (addHaar_image_le_lintegral_abs_det_fderiv μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)) ?_
    calc (∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ)
        ≤ ∫⁻ _ in s, ENNReal.ofReal c₂ ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).2))
      _ = ENNReal.ofReal c₂ * μ s := by rw [setLIntegral_const]
  have hlow : ENNReal.ofReal c₁ * μ s ≤ μ (Φ '' s) := by
    refine le_trans ?_ (lintegral_abs_det_fderiv_le_addHaar_image μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)
      (hinj.mono inter_subset_left))
    calc ENNReal.ofReal c₁ * μ s
        = ∫⁻ _ in s, ENNReal.ofReal c₁ ∂μ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).1))
  have hVs : sublevelVol μ K (fun x => f (Φ x)) ε = (μ s).toReal := rfl
  have hVim : sublevelVol μ (Φ '' K) f ε = (μ (Φ '' s)).toReal := by
    rw [sublevelVol, himg]
  -- finiteness: the known side (domain) self-certifies, image inherits
  have hpos : 0 < sublevelVol μ K (fun x => f (Φ x)) ε :=
    lt_of_lt_of_le (mul_pos hd₁ (llcScale_pos hε)) hbε.1
  have hsne : μ s ≠ ⊤ := by
    intro htop
    rw [hVs, htop, ENNReal.toReal_top] at hpos
    exact lt_irrefl 0 hpos
  have himne : μ (Φ '' s) ≠ ⊤ :=
    (lt_of_le_of_lt hup (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hsne))).ne
  have hupR : (μ (Φ '' s)).toReal ≤ c₂ * (μ s).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂.le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsne) hup
  have hlowR : c₁ * (μ s).toReal ≤ (μ (Φ '' s)).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁.le] using
      ENNReal.toReal_mono himne hlow
  constructor
  · rw [hVim]
    have h1 : d₁ * llcScale lam theta ε ≤ (μ s).toReal := by
      rw [← hVs]; exact hbε.1
    calc d₁ * c₁ * llcScale lam theta ε
        = c₁ * (d₁ * llcScale lam theta ε) := by ring
      _ ≤ c₁ * (μ s).toReal := mul_le_mul_of_nonneg_left h1 hc₁.le
      _ ≤ (μ (Φ '' s)).toReal := hlowR
  · rw [hVim]
    have h1 : (μ s).toReal ≤ d₂ * llcScale lam theta ε := by
      rw [← hVs]; exact hbε.2
    calc (μ (Φ '' s)).toReal ≤ c₂ * (μ s).toReal := hupR
      _ ≤ c₂ * (d₂ * llcScale lam theta ε) := mul_le_mul_of_nonneg_left h1 hc₂.le
      _ = d₂ * c₂ * llcScale lam theta ε := by ring

/-! ## Closed-set variants

The only role of the measurability hypotheses above is to certify
`MeasurableSet (K ∩ {x | f (Φ x) ≤ ε})`. When `K` is closed and the
pullback `f ∘ Φ` is continuous on it, that set is closed — which avoids
proving global measurability for maps (like polynomial charts with
matrix inverses) that are only well-behaved on the good set. The
proofs are those of `comp_diffeo`/`of_comp_diffeo` with the one-line
`hsm` derivation swapped. -/

/-- **K0.4, closed-set variant.** -/
theorem HasLLCExponentsOn.comp_diffeo' {K : Set E} {f : E → ℝ} {Φ : E → E}
    {Φ' : E → E →L[ℝ] E} {c₁ c₂ lam theta : ℝ}
    (hK : IsClosed K) (hfΦ : ContinuousOn (fun x => f (Φ x)) K)
    (hΦ : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    (hinj : Set.InjOn Φ K) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hdet : ∀ x ∈ K, c₁ ≤ |(Φ' x).det| ∧ |(Φ' x).det| ≤ c₂)
    (h : HasLLCExponentsOn μ (Φ '' K) f lam theta) :
    HasLLCExponentsOn μ K (fun x => f (Φ x)) lam theta := by
  rw [hasLLCExponentsOn_iff_eventually_bounds] at h ⊢
  obtain ⟨d₁, hd₁, d₂, hd₂, hb⟩ := h
  refine ⟨d₁ / c₂, by positivity, d₂ / c₁, by positivity, ?_⟩
  filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hbε hε
  set s : Set E := K ∩ {x | f (Φ x) ≤ ε} with hs
  have hsm : MeasurableSet s :=
    (hfΦ.preimage_isClosed_of_isClosed hK isClosed_Iic).measurableSet
  have himg : Φ '' s = (Φ '' K) ∩ {y | f y ≤ ε} := by
    rw [hs, show {x | f (Φ x) ≤ ε} = Φ ⁻¹' {y | f y ≤ ε} from rfl,
      Set.image_inter_preimage]
  have hup : μ (Φ '' s) ≤ ENNReal.ofReal c₂ * μ s := by
    refine le_trans (addHaar_image_le_lintegral_abs_det_fderiv μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)) ?_
    calc (∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ)
        ≤ ∫⁻ _ in s, ENNReal.ofReal c₂ ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).2))
      _ = ENNReal.ofReal c₂ * μ s := by
          rw [setLIntegral_const]
  have hlow : ENNReal.ofReal c₁ * μ s ≤ μ (Φ '' s) := by
    refine le_trans ?_ (lintegral_abs_det_fderiv_le_addHaar_image μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)
      (hinj.mono inter_subset_left))
    calc ENNReal.ofReal c₁ * μ s
        = ∫⁻ _ in s, ENNReal.ofReal c₁ ∂μ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).1))
  have hVim : sublevelVol μ (Φ '' K) f ε = (μ (Φ '' s)).toReal := by
    rw [sublevelVol, himg]
  have hpos : 0 < sublevelVol μ (Φ '' K) f ε :=
    lt_of_lt_of_le (mul_pos hd₁ (llcScale_pos hε)) hbε.1
  have himne : μ (Φ '' s) ≠ ⊤ := by
    intro htop
    rw [hVim, htop, ENNReal.toReal_top] at hpos
    exact lt_irrefl 0 hpos
  have hsne : μ s ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.mul_top (fun h0 =>
      absurd (ENNReal.ofReal_eq_zero.mp h0) (not_le.mpr hc₁))] at hlow
    exact himne (top_le_iff.mp hlow)
  have hupR : (μ (Φ '' s)).toReal ≤ c₂ * (μ s).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂.le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsne) hup
  have hlowR : c₁ * (μ s).toReal ≤ (μ (Φ '' s)).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁.le] using
      ENNReal.toReal_mono himne hlow
  have hVs : sublevelVol μ K (fun x => f (Φ x)) ε = (μ s).toReal := rfl
  constructor
  · rw [hVs]
    have h1 : d₁ * llcScale lam theta ε ≤ (μ (Φ '' s)).toReal := by
      rw [← hVim]; exact hbε.1
    have h2 := le_trans h1 hupR
    rw [div_mul_eq_mul_div, div_le_iff₀ hc₂]
    simpa [mul_comm] using h2
  · rw [hVs]
    have h1 : (μ (Φ '' s)).toReal ≤ d₂ * llcScale lam theta ε := by
      rw [← hVim]; exact hbε.2
    have h2 := le_trans hlowR h1
    rw [div_mul_eq_mul_div, le_div_iff₀ hc₁]
    simpa [mul_comm] using h2

/-- **K0.4 reverse, closed-set variant.** -/
theorem HasLLCExponentsOn.of_comp_diffeo' {K : Set E} {f : E → ℝ}
    {Φ : E → E} {Φ' : E → E →L[ℝ] E} {c₁ c₂ lam theta : ℝ}
    (hK : IsClosed K) (hfΦ : ContinuousOn (fun x => f (Φ x)) K)
    (hΦ : ∀ x ∈ K, HasFDerivWithinAt Φ (Φ' x) K x)
    (hinj : Set.InjOn Φ K) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hdet : ∀ x ∈ K, c₁ ≤ |(Φ' x).det| ∧ |(Φ' x).det| ≤ c₂)
    (h : HasLLCExponentsOn μ K (fun x => f (Φ x)) lam theta) :
    HasLLCExponentsOn μ (Φ '' K) f lam theta := by
  rw [hasLLCExponentsOn_iff_eventually_bounds] at h ⊢
  obtain ⟨d₁, hd₁, d₂, hd₂, hb⟩ := h
  refine ⟨d₁ * c₁, by positivity, d₂ * c₂, by positivity, ?_⟩
  filter_upwards [hb, (Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hbε hε
  set s : Set E := K ∩ {x | f (Φ x) ≤ ε} with hs
  have hsm : MeasurableSet s :=
    (hfΦ.preimage_isClosed_of_isClosed hK isClosed_Iic).measurableSet
  have himg : Φ '' s = (Φ '' K) ∩ {y | f y ≤ ε} := by
    rw [hs, show {x | f (Φ x) ≤ ε} = Φ ⁻¹' {y | f y ≤ ε} from rfl,
      Set.image_inter_preimage]
  have hup : μ (Φ '' s) ≤ ENNReal.ofReal c₂ * μ s := by
    refine le_trans (addHaar_image_le_lintegral_abs_det_fderiv μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)) ?_
    calc (∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ)
        ≤ ∫⁻ _ in s, ENNReal.ofReal c₂ ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).2))
      _ = ENNReal.ofReal c₂ * μ s := by rw [setLIntegral_const]
  have hlow : ENNReal.ofReal c₁ * μ s ≤ μ (Φ '' s) := by
    refine le_trans ?_ (lintegral_abs_det_fderiv_le_addHaar_image μ hsm
      (fun x hx => (hΦ x hx.1).mono inter_subset_left)
      (hinj.mono inter_subset_left))
    calc ENNReal.ofReal c₁ * μ s
        = ∫⁻ _ in s, ENNReal.ofReal c₁ ∂μ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ x in s, ENNReal.ofReal |(Φ' x).det| ∂μ := by
          refine lintegral_mono_ae ((ae_restrict_iff' hsm).mpr
            (Filter.Eventually.of_forall fun x hx =>
              ENNReal.ofReal_le_ofReal (hdet x hx.1).1))
  have hVs : sublevelVol μ K (fun x => f (Φ x)) ε = (μ s).toReal := rfl
  have hVim : sublevelVol μ (Φ '' K) f ε = (μ (Φ '' s)).toReal := by
    rw [sublevelVol, himg]
  have hpos : 0 < sublevelVol μ K (fun x => f (Φ x)) ε :=
    lt_of_lt_of_le (mul_pos hd₁ (llcScale_pos hε)) hbε.1
  have hsne : μ s ≠ ⊤ := by
    intro htop
    rw [hVs, htop, ENNReal.toReal_top] at hpos
    exact lt_irrefl 0 hpos
  have himne : μ (Φ '' s) ≠ ⊤ :=
    (lt_of_le_of_lt hup (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (lt_top_iff_ne_top.mpr hsne))).ne
  have hupR : (μ (Φ '' s)).toReal ≤ c₂ * (μ s).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₂.le] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hsne) hup
  have hlowR : c₁ * (μ s).toReal ≤ (μ (Φ '' s)).toReal := by
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc₁.le] using
      ENNReal.toReal_mono himne hlow
  constructor
  · rw [hVim]
    have h1 : d₁ * llcScale lam theta ε ≤ (μ s).toReal := by
      rw [← hVs]; exact hbε.1
    calc d₁ * c₁ * llcScale lam theta ε
        = c₁ * (d₁ * llcScale lam theta ε) := by ring
      _ ≤ c₁ * (μ s).toReal := mul_le_mul_of_nonneg_left h1 hc₁.le
      _ ≤ (μ (Φ '' s)).toReal := hlowR
  · rw [hVim]
    have h1 : (μ s).toReal ≤ d₂ * llcScale lam theta ε := by
      rw [← hVs]; exact hbε.2
    calc (μ (Φ '' s)).toReal ≤ c₂ * (μ s).toReal := hupR
      _ ≤ c₂ * (d₂ * llcScale lam theta ε) := mul_le_mul_of_nonneg_left h1 hc₂.le
      _ = d₂ * c₂ * llcScale lam theta ε := by ring

end SingularLearningTheory
