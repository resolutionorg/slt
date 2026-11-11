/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.VolumeScaling.Laplace.Asymptotic
import SLT.VolumeScaling.Laplace.Model
import SLT.VolumeScaling.Laplace.Representation
public import SLT.VolumeScaling.Laplace.Scale
public import SLT.VolumeScaling.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Weighted sublevel-volume kernels and moments

The loss cumulants under the deterministic Gibbs posterior are read off from
the raw moments `M_n(s) = ∫_K f^n e^{−s·f} dμ`, expressed through
the weighted sublevel-volume kernels

  `SingularLearningTheory.momentKernel μ K f n ε = ε^n · V(ε)`,   `V = sublevelVol μ K f`,

and the integrals `A_n(s) = ∫_{Ioi 0} e^{−s·ε} · momentKernel ε dε`.

This file proves the foundation: the kernel, its nonnegativity,
measurability, the model-scale shift
`ε^n · llcScale λ θ ε = llcScale (λ+n) θ ε`, the polynomial bound
`SingularLearningTheory.momentKernel ≤ μK · ε^n`, and integrability of the Laplace-weighted
kernel on right rays. The asymptotic of `A_n` and the moment recursion build on these.
-/

public section

open Filter MeasureTheory Asymptotics Set
open scoped Topology ENNReal

namespace SingularLearningTheory

open SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α} {f : α → ℝ}

/-- The `n`-th weighted sublevel-volume kernel `ε^n · V(ε)`. -/
@[expose] noncomputable def momentKernel (μ : Measure α) (K : Set α) (f : α → ℝ)
    (n : ℕ) (ε : ℝ) : ℝ :=
  ε ^ n * sublevelVol μ K f ε

private theorem momentKernel_nonneg (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    0 ≤ momentKernel μ K f n ε :=
  mul_nonneg (pow_nonneg hε n) (sublevelVol_nonneg μ K f ε)

private theorem measurable_momentKernel (hfin : μ K ≠ ⊤) (n : ℕ) :
    Measurable (momentKernel μ K f n) :=
  (measurable_id.pow_const n).mul (measurable_sublevelVol hfin)

/-- The polynomial envelope: `ε^n · V(ε) ≤ (μ K).toReal · ε^n` for
`ε ≥ 0`. -/
private theorem momentKernel_le (hfin : μ K ≠ ⊤) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    momentKernel μ K f n ε ≤ (μ K).toReal * ε ^ n := by
  rw [momentKernel]
  calc ε ^ n * sublevelVol μ K f ε
      ≤ ε ^ n * (μ K).toReal :=
        mul_le_mul_of_nonneg_left (sublevelVol_le hfin ε) (pow_nonneg hε n)
    _ = (μ K).toReal * ε ^ n := mul_comm _ _

/-- **The model-scale shift.** On `Ioo 0 1` (where the log base is
positive), weighting the model scale by `ε^n` shifts the exponent:
`ε^n · llcScale λ θ ε = llcScale (λ + n) θ ε`. -/
private theorem rpow_natCast_mul_llcScale {lam theta : ℝ} (n : ℕ) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) :
    ε ^ n * llcScale lam theta ε = llcScale (lam + n) theta ε := by
  have hε0 : (0 : ℝ) < ε := hε.1
  rw [llcScale, llcScale, ← Real.rpow_natCast ε n, ← mul_assoc,
    ← Real.rpow_add hε0, add_comm (n : ℝ) lam]

/-- The Gamma-type kernel `e^{−s·ε} · ε^n` is integrable on `Ioi 0`
(for `s > 0`). -/
private theorem integrableOn_exp_neg_mul_pow {s : ℝ} (hs : 0 < s) (n : ℕ) :
    IntegrableOn (fun ε => Real.exp (-(s * ε)) * ε ^ n) (Ioi (0 : ℝ)) := by
  -- `f u = e^{−u} u^n` integrable on `Ioi 0`; pull back along `u = s·ε`.
  have hpn : (-1 : ℝ) < (n : ℝ) := lt_of_lt_of_le (by norm_num) (Nat.cast_nonneg n)
  have hf : IntegrableOn (fun u : ℝ => Real.exp (-u) * u ^ (n : ℝ))
      (Ioi (0 : ℝ)) := integrableOn_exp_neg_rpow hpn
  have hcomp : IntegrableOn
      (fun ε : ℝ => Real.exp (-(s * ε)) * (s * ε) ^ (n : ℝ)) (Ioi (0 : ℝ)) :=
    (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => Real.exp (-u) * u ^ (n : ℝ)) 0 hs).mpr (by simpa using hf)
  -- `f (s·ε) = e^{−s·ε} · (s·ε)^n = s^n · e^{−s·ε} · ε^n`.
  have hscaled := hcomp.const_mul ((s : ℝ) ^ (n : ℝ))⁻¹
  refine MeasureTheory.IntegrableOn.congr_fun hscaled (fun ε hε => ?_)
    measurableSet_Ioi
  rw [mem_Ioi] at hε
  rw [Real.mul_rpow hs.le hε.le, Real.rpow_natCast ε n, Real.rpow_natCast s n]
  rw [show ((s : ℝ) ^ n)⁻¹ * (Real.exp (-(s * ε)) * ((s : ℝ) ^ n * ε ^ n))
      = (((s : ℝ) ^ n)⁻¹ * (s : ℝ) ^ n) * (Real.exp (-(s * ε)) * ε ^ n) by ring,
    inv_mul_cancel₀ (by positivity : (s : ℝ) ^ n ≠ 0), one_mul]

/-- The Laplace-weighted moment kernel `e^{−s·ε} · ε^n · V(ε)` is
integrable on `Ioi 0` (for `s > 0`, `μ K ≠ ⊤`): dominate by
`(μ K).toReal · e^{−s·ε} · ε^n`. -/
private theorem integrableOn_exp_mul_momentKernel (hfin : μ K ≠ ⊤) {s : ℝ}
    (hs : 0 < s) (n : ℕ) :
    IntegrableOn (fun ε => Real.exp (-(s * ε)) * momentKernel μ K f n ε)
      (Ioi (0 : ℝ)) := by
  refine Integrable.mono'
    ((integrableOn_exp_neg_mul_pow hs n).const_mul (μ K).toReal) ?_ ?_
  · exact ((measurable_id.const_mul s).neg.exp.mul
      (measurable_momentKernel hfin n)).aestronglyMeasurable
  · refine (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun ε hε => ?_)
    rw [mem_Ioi] at hε
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _)
      (momentKernel_nonneg n hε.le))]
    calc Real.exp (-(s * ε)) * momentKernel μ K f n ε
        ≤ Real.exp (-(s * ε)) * ((μ K).toReal * ε ^ n) :=
          mul_le_mul_of_nonneg_left (momentKernel_le hfin n hε.le)
            (Real.exp_nonneg _)
      _ = (μ K).toReal * (Real.exp (-(s * ε)) * ε ^ n) := by ring

/-! ## Algebraic glue for the weighted-kernel asymptotic -/

/-- The Laplace scale at a shifted exponent factors off a power of `s`:
`laplaceScale (λ+n) θ s = s^{−n} · laplaceScale λ θ s` for `s > 0`. This
is what lets the `s^{−n}` from the moment-tail cancel against the scale
shift, reducing the tail estimate to the unshifted exponential decay. -/
theorem laplaceScale_add_natCast {lam theta : ℝ} (n : ℕ) {s : ℝ}
    (hs : 0 < s) :
    laplaceScale (lam + n) theta s
      = s ^ (-(n : ℝ)) * laplaceScale lam theta s := by
  unfold laplaceScale
  rw [show -(lam + (n : ℝ)) = -(n : ℝ) + -lam by ring, Real.rpow_add hs]
  ring

/-- **Window transfer.** If the sublevel volume is pinched between
`(c∓δ)·llcScale λ θ` on `(0, ε₀]` (with `ε₀ < 1`), the weighted kernel
`ε^n · V` is pinched between the same constants times
`llcScale (λ+n) θ` — the exponent shift moves the whole window up by
`n`. -/
private theorem momentKernel_window {lam theta c δ ε₀ : ℝ} (n : ℕ) (hε₀1 : ε₀ < 1)
    (hwin : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (c - δ) * llcScale lam theta ε ≤ sublevelVol μ K f ε ∧
      sublevelVol μ K f ε ≤ (c + δ) * llcScale lam theta ε) :
    ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (c - δ) * llcScale (lam + n) theta ε ≤ momentKernel μ K f n ε ∧
      momentKernel μ K f n ε ≤ (c + δ) * llcScale (lam + n) theta ε := by
  intro ε hε
  have hεmem : ε ∈ Ioo (0 : ℝ) 1 := ⟨hε.1, lt_of_le_of_lt hε.2 hε₀1⟩
  have hshift : ε ^ n * llcScale lam theta ε = llcScale (lam + n) theta ε :=
    rpow_natCast_mul_llcScale n hεmem
  have hpow : (0 : ℝ) ≤ ε ^ n := pow_nonneg hε.1.le n
  obtain ⟨hlo, hhi⟩ := hwin ε hε
  refine ⟨?_, ?_⟩
  · calc (c - δ) * llcScale (lam + n) theta ε
        = ε ^ n * ((c - δ) * llcScale lam theta ε) := by rw [← hshift]; ring
      _ ≤ ε ^ n * sublevelVol μ K f ε :=
          mul_le_mul_of_nonneg_left hlo hpow
      _ = momentKernel μ K f n ε := rfl
  · calc momentKernel μ K f n ε
        = ε ^ n * sublevelVol μ K f ε := rfl
      _ ≤ ε ^ n * ((c + δ) * llcScale lam theta ε) :=
          mul_le_mul_of_nonneg_left hhi hpow
      _ = (c + δ) * llcScale (lam + n) theta ε := by rw [← hshift]; ring

/-! ## The weighted-kernel asymptotic -/

/-- Head/tail split of `A_n(s) = ∫_{Ioi 0} e^{−s·ε}(ε^n V)` at `ε₀ > 0`. -/
private theorem setIntegral_exp_momentKernel_split (hfin : μ K ≠ ⊤) {s : ℝ}
    (hs : 0 < s) {ε₀ : ℝ} (hε₀ : 0 < ε₀) (n : ℕ) :
    ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε
      = (∫ ε in Ioc (0 : ℝ) ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε)
        + ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε := by
  rw [← Ioc_union_Ioi_eq_Ioi hε₀.le]
  exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    ((integrableOn_exp_mul_momentKernel hfin hs n).mono_set Ioc_subset_Ioi_self)
    ((integrableOn_exp_mul_momentKernel hfin hs n).mono_set
      (Ioi_subset_Ioi hε₀.le))

/-- A uniform bound `e^{−v/2} v^n ≤ M` for `v ≥ 0` (the half-rate
exponential dominates any fixed power): the constant the moment-tail
estimate factors through. -/
private theorem exp_neg_half_pow_le (n : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ v : ℝ, 0 ≤ v →
      Real.exp (-(1 / 2 * v)) * v ^ n ≤ M := by
  obtain ⟨B, hB, hBbd⟩ := Real.exists_exp_rpow_le_exp_half (n : ℝ)
  refine ⟨max B 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun v hv => ?_⟩
  rcases le_or_gt 1 v with h1 | h1
  · have hbb := hBbd v h1
    rw [Real.rpow_natCast] at hbb
    have hsplit : Real.exp (-(1 / 2 * v)) * v ^ n
        = Real.exp (1 / 2 * v) * (Real.exp (-v) * v ^ n) := by
      rw [← mul_assoc, ← Real.exp_add]
      ring_nf
    rw [hsplit]
    calc Real.exp (1 / 2 * v) * (Real.exp (-v) * v ^ n)
        ≤ Real.exp (1 / 2 * v) * (B * Real.exp (-(1 / 2 * v))) :=
          mul_le_mul_of_nonneg_left hbb (Real.exp_nonneg _)
      _ = B := by
          rw [show B * Real.exp (-(1 / 2 * v))
              = Real.exp (-(1 / 2 * v)) * B by ring, ← mul_assoc,
            ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ max B 1 := le_max_left _ _
  · have hvn : v ^ n ≤ 1 := pow_le_one₀ hv h1.le
    calc Real.exp (-(1 / 2 * v)) * v ^ n
        ≤ 1 * 1 :=
          mul_le_mul (Real.exp_le_one_iff.mpr (by linarith)) hvn
            (pow_nonneg hv n) zero_le_one
      _ = 1 := by ring
      _ ≤ max B 1 := le_max_right _ _

/-- **The moment tail is little-o of the shifted scale.** For `ε₀ > 0`,
`s · ∫_{Ioi ε₀} e^{−s·ε}(ε^n V) =o[atTop] laplaceScale (λ+n) θ`. The
`s^{−n}` produced by the polynomial envelope cancels against the scale
shift, reducing the claim to the unshifted exponential decay. -/
private theorem momentTail_isLittleO (hfin : μ K ≠ ⊤) {lam theta ε₀ : ℝ}
    (hε₀ : 0 < ε₀) (n : ℕ) :
    (fun s => s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε)
      =o[atTop] laplaceScale (lam + n) theta := by
  obtain ⟨M, hM, hMbd⟩ := exp_neg_half_pow_le n
  -- Step 1: the tail is `=O` of `s^{−n}·e^{−(ε₀/2)s}`.
  have hbig : (fun s => s * ∫ ε in Ioi ε₀,
      Real.exp (-(s * ε)) * momentKernel μ K f n ε)
      =O[atTop] (fun s => s ^ (-(n : ℝ))
        * Real.exp (-(s * (ε₀ / 2)))) := by
    rw [Asymptotics.isBigO_iff]
    refine ⟨2 * M * (μ K).toReal, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs0
    have hs2 : (0 : ℝ) < s / 2 := by linarith
    -- pointwise: `e^{−sε}·(ε^n V) ≤ M μK s^{−n} e^{−(s/2)ε}` on Ioi ε₀
    have hptbd : ∀ ε ∈ Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε
        ≤ (M * (μ K).toReal * s ^ (-(n : ℝ))) * Real.exp (-(s / 2 * ε)) := by
      intro ε hε
      rw [mem_Ioi] at hε
      have hε0 : (0 : ℝ) < ε := hε₀.trans hε
      have hμ : (0 : ℝ) ≤ (μ K).toReal := ENNReal.toReal_nonneg
      -- e^{−sε}ε^n ≤ M s^{−n} e^{−(s/2)ε}
      have hk : Real.exp (-(s * ε)) * ε ^ n
          ≤ M * s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε)) := by
        have hsv := hMbd (s * ε) (by positivity)
        -- hsv : e^{−(1/2)(sε)}·(sε)^n ≤ M
        have he : Real.exp (-(1 / 2 * (s * ε))) * Real.exp (-(s / 2 * ε))
            = Real.exp (-(s * ε)) := by
          rw [← Real.exp_add]; congr 1; ring
        have hp : (s * ε) ^ n * s ^ (-(n : ℝ)) = ε ^ n := by
          rw [mul_pow, ← Real.rpow_natCast s n,
            show s ^ (n : ℝ) * ε ^ n * s ^ (-(n : ℝ))
              = ε ^ n * (s ^ (n : ℝ) * s ^ (-(n : ℝ))) by ring,
            ← Real.rpow_add hs0, add_neg_cancel, Real.rpow_zero, mul_one]
        have hid : Real.exp (-(s * ε)) * ε ^ n
            = (Real.exp (-(1 / 2 * (s * ε))) * (s * ε) ^ n)
              * (s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε))) := by
          rw [show (Real.exp (-(1 / 2 * (s * ε))) * (s * ε) ^ n)
                * (s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε)))
              = (Real.exp (-(1 / 2 * (s * ε))) * Real.exp (-(s / 2 * ε)))
                * ((s * ε) ^ n * s ^ (-(n : ℝ))) by ring, he, hp]
        rw [hid]
        have hfac : (0 : ℝ) ≤ s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε)) := by positivity
        calc (Real.exp (-(1 / 2 * (s * ε))) * (s * ε) ^ n)
              * (s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε)))
            ≤ M * (s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε))) :=
              mul_le_mul_of_nonneg_right hsv hfac
          _ = M * s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε)) := by ring
      calc Real.exp (-(s * ε)) * momentKernel μ K f n ε
          ≤ Real.exp (-(s * ε)) * ((μ K).toReal * ε ^ n) :=
            mul_le_mul_of_nonneg_left (momentKernel_le hfin n hε0.le)
              (Real.exp_nonneg _)
        _ = (μ K).toReal * (Real.exp (-(s * ε)) * ε ^ n) := by ring
        _ ≤ (μ K).toReal * (M * s ^ (-(n : ℝ)) * Real.exp (-(s / 2 * ε))) :=
            mul_le_mul_of_nonneg_left hk hμ
        _ = (M * (μ K).toReal * s ^ (-(n : ℝ))) * Real.exp (-(s / 2 * ε)) := by ring
    -- integrate the pointwise bound
    have hint_tail : IntegrableOn
        (fun ε => Real.exp (-(s * ε)) * momentKernel μ K f n ε) (Ioi ε₀) :=
      (integrableOn_exp_mul_momentKernel hfin hs0 n).mono_set (Ioi_subset_Ioi hε₀.le)
    have hint_bd : IntegrableOn
        (fun ε => (M * (μ K).toReal * s ^ (-(n : ℝ))) * Real.exp (-(s / 2 * ε)))
        (Ioi ε₀) := by
      have h := (exp_neg_integrableOn_Ioi ε₀ hs2).const_mul
        (M * (μ K).toReal * s ^ (-(n : ℝ)))
      refine MeasureTheory.IntegrableOn.congr_fun h (fun ε _ => ?_) measurableSet_Ioi
      rw [neg_mul]
    have hmono : ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε
        ≤ ∫ ε in Ioi ε₀, (M * (μ K).toReal * s ^ (-(n : ℝ)))
            * Real.exp (-(s / 2 * ε)) :=
      setIntegral_mono_on hint_tail hint_bd measurableSet_Ioi hptbd
    have hival : ∫ ε in Ioi ε₀,
        (M * (μ K).toReal * s ^ (-(n : ℝ))) * Real.exp (-(s / 2 * ε))
        = (M * (μ K).toReal * s ^ (-(n : ℝ))) * ((s / 2)⁻¹ * Real.exp (-(s / 2 * ε₀))) := by
      rw [integral_const_mul, integral_exp_neg_mul_Ioi hs2]
    have htail_nn : 0 ≤ ∫ ε in Ioi ε₀,
        Real.exp (-(s * ε)) * momentKernel μ K f n ε :=
      setIntegral_nonneg measurableSet_Ioi fun ε hε =>
        mul_nonneg (Real.exp_nonneg _) (momentKernel_nonneg n (le_of_lt (hε₀.trans hε)))
    rw [Real.norm_of_nonneg (mul_nonneg hs0.le htail_nn),
      Real.norm_of_nonneg (by positivity)]
    calc s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε
        ≤ s * ((M * (μ K).toReal * s ^ (-(n : ℝ)))
            * ((s / 2)⁻¹ * Real.exp (-(s / 2 * ε₀)))) := by
          rw [← hival]; exact mul_le_mul_of_nonneg_left hmono hs0.le
      _ = 2 * M * (μ K).toReal * (s ^ (-(n : ℝ)) * Real.exp (-(s * (ε₀ / 2)))) := by
          rw [show (s / 2)⁻¹ = 2 * s⁻¹ by rw [mul_comm]; field_simp,
            show -(s / 2 * ε₀) = -(s * (ε₀ / 2)) by ring]
          field_simp
  -- Step 2: `s^{−n}·e^{−(ε₀/2)s} =o laplaceScale (λ+n) θ`.
  have hlittle : (fun s => s ^ (-(n : ℝ)) * Real.exp (-(s * (ε₀ / 2))))
      =o[atTop] laplaceScale (lam + n) theta := by
    have hexp : (fun s : ℝ => Real.exp (-(s * (ε₀ / 2))))
        =o[atTop] laplaceScale lam theta :=
      isLittleO_exp_neg_laplaceScale (by linarith : (0 : ℝ) < ε₀ / 2)
    have hmul := (Asymptotics.isBigO_refl (fun s : ℝ => s ^ (-(n : ℝ))) atTop).mul_isLittleO hexp
    refine hmul.trans_isBigO ?_
    rw [Asymptotics.isBigO_iff]
    refine ⟨1, ?_⟩
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs0
    rw [one_mul, laplaceScale_add_natCast n hs0]
  exact hbig.trans_isLittleO hlittle

/-- The ratio-window sandwich for `A_n`: under a `(λ+n)`-window on the
weighted kernel, `(s·A_n)/laplaceScale(λ+n)θ` is eventually pinched
between `(c∓δ)` times the normalized head, up to the moment tail. -/
private theorem momentKernel_ratio_window {lam theta c δ ε₀ : ℝ} (n : ℕ)
    (hfin : μ K ≠ ⊤) (hlamn : (-1 : ℝ) < lam + n) (hε₀ : 0 < ε₀)
    (hε₀1 : ε₀ < 1)
    (hwin : ∀ ε ∈ Ioc (0 : ℝ) ε₀,
      (c - δ) * llcScale (lam + n) theta ε ≤ momentKernel μ K f n ε ∧
      momentKernel μ K f n ε ≤ (c + δ) * llcScale (lam + n) theta ε) :
    ∀ᶠ s in atTop,
      (c - δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
          * (u ^ (lam + n) * (Real.log s - Real.log u) ^ (theta - 1)))
        / Real.log s ^ (theta - 1))
        ≤ (s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε)
            / laplaceScale (lam + n) theta s ∧
      (s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε)
          / laplaceScale (lam + n) theta s
        ≤ (c + δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ (lam + n) * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1))
          + (s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε)
              / laplaceScale (lam + n) theta s := by
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with s hs1 hlog1
  have hs0 : (0 : ℝ) < s := one_pos.trans hs1
  have hΛpos : (0 : ℝ) < laplaceScale (lam + n) theta s := laplaceScale_pos hs1
  have hsplit := setIntegral_exp_momentKernel_split (f := f) hfin hs0 hε₀ n
  have hVint : IntegrableOn
      (fun ε => Real.exp (-(s * ε)) * momentKernel μ K f n ε) (Ioc (0 : ℝ) ε₀) :=
    (integrableOn_exp_mul_momentKernel hfin hs0 n).mono_set Ioc_subset_Ioi_self
  have hSint : IntegrableOn
      (fun ε => Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
      (Ioc (0 : ℝ) ε₀) :=
    integrableOn_exp_mul_llcScale hlamn hs0 hε₀ hε₀1
  have hVub : ∫ ε in Ioc (0 : ℝ) ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε
        ≤ (c + δ) * ∫ ε in Ioc (0 : ℝ) ε₀,
            Real.exp (-(s * ε)) * llcScale (lam + n) theta ε := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on hVint (hSint.const_mul _)
      measurableSet_Ioc fun ε hε => ?_
    calc Real.exp (-(s * ε)) * momentKernel μ K f n ε
        ≤ Real.exp (-(s * ε)) * ((c + δ) * llcScale (lam + n) theta ε) :=
          mul_le_mul_of_nonneg_left (hwin ε hε).2 (Real.exp_nonneg _)
      _ = (c + δ) * (Real.exp (-(s * ε)) * llcScale (lam + n) theta ε) := by ring
  have hVlb : (c - δ) * (∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
        ≤ ∫ ε in Ioc (0 : ℝ) ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (hSint.const_mul _) hVint
      measurableSet_Ioc fun ε hε => ?_
    calc (c - δ) * (Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
        = Real.exp (-(s * ε)) * ((c - δ) * llcScale (lam + n) theta ε) := by ring
      _ ≤ Real.exp (-(s * ε)) * momentKernel μ K f n ε :=
          mul_le_mul_of_nonneg_left (hwin ε hε).1 (Real.exp_nonneg _)
  have h2a := mul_setIntegral_head_eq_subst
    (lam := lam + n) (theta := theta) (ε₀ := ε₀) hs0
  have hslam : (0 : ℝ) < s ^ (-(lam + n)) := Real.rpow_pos_of_pos hs0 _
  have hHR : s * (∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
        / laplaceScale (lam + n) theta s
        = (∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ (lam + n) * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1) := by
    rw [h2a, show laplaceScale (lam + n) theta s
        = s ^ (-(lam + n)) * Real.log s ^ (theta - 1) from rfl,
      mul_div_mul_left _ _ hslam.ne']
  have htail_nn : 0 ≤ ∫ ε in Ioi ε₀,
      Real.exp (-(s * ε)) * momentKernel μ K f n ε :=
    setIntegral_nonneg measurableSet_Ioi fun ε hε =>
      mul_nonneg (Real.exp_nonneg _)
        (momentKernel_nonneg n (le_of_lt (hε₀.trans (mem_Ioi.mp hε))))
  have hAsplit : s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε
      = s * (∫ ε in Ioc (0 : ℝ) ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε)
        + s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε := by
    rw [hsplit]; ring
  have habs_lo : (c - δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
      Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
        ≤ s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε := by
    rw [hAsplit]
    have h1 : (c - δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
        Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
          = s * ((c - δ) * ∫ ε in Ioc (0 : ℝ) ε₀,
              Real.exp (-(s * ε)) * llcScale (lam + n) theta ε) := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hVlb hs0.le
    nlinarith [mul_nonneg hs0.le htail_nn]
  have habs_hi : s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε
      ≤ (c + δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
          Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
        + s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε := by
    rw [hAsplit]
    have h2 := mul_le_mul_of_nonneg_left hVub hs0.le
    nlinarith [h2]
  refine ⟨?_, ?_⟩
  · rw [← hHR, ← mul_div_assoc]
    gcongr
  · rw [← hHR]
    calc (s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε)
          / laplaceScale (lam + n) theta s
        ≤ ((c + δ) * (s * ∫ ε in Ioc (0 : ℝ) ε₀,
            Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
          + s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε)
            / laplaceScale (lam + n) theta s := by gcongr
      _ = (c + δ) * (s * (∫ ε in Ioc (0 : ℝ) ε₀,
            Real.exp (-(s * ε)) * llcScale (lam + n) theta ε)
            / laplaceScale (lam + n) theta s)
          + (s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε)
              / laplaceScale (lam + n) theta s := by
          rw [add_div, mul_div_assoc, mul_div_assoc]

/-- **The weighted-kernel Laplace asymptotic.** Under
`HasLLCOn μ K f λ θ c` (`c > 0`), the weighted Laplace integral
`A_n(s) = ∫_{Ioi 0} e^{−s·ε}(ε^n V)` carries the asymptotic at the
shifted exponent: `s · A_n(s) / laplaceScale (λ+n) θ → c · Γ(λ+n+1)`. -/
theorem _root_.SingularLearningTheory.HasLLCOn.momentKernel_div_tendsto {lam theta c : ℝ} (n : ℕ)
    (h : HasLLCOn μ K f lam theta c) (hc : 0 < c) (hfin : μ K ≠ ⊤) :
    Tendsto (fun s => (s * ∫ ε in Ioi (0 : ℝ),
        Real.exp (-(s * ε)) * momentKernel μ K f n ε)
        / laplaceScale (lam + n) theta s) atTop
      (𝓝 (c * Real.Gamma (lam + n + 1))) := by
  have hexp := h.hasLLCExponentsOn hc
  have hlam0 : 0 ≤ lam := hexp.nonneg_lam hfin
  have hlamn : (-1 : ℝ) < lam + n := by
    have : (0 : ℝ) ≤ (n : ℝ) := by positivity
    linarith
  have hΓ : 0 < Real.Gamma (lam + n + 1) :=
    Real.Gamma_pos_of_pos (by positivity)
  -- window extractor (V-window from HasLLCOn, lifted to the kernel)
  have hwinex : ∀ δ : ℝ, 0 < δ → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ < 1 ∧
      ∀ ε ∈ Ioc (0 : ℝ) ε₀,
        (c - δ) * llcScale (lam + n) theta ε ≤ momentKernel μ K f n ε ∧
        momentKernel μ K f n ε ≤ (c + δ) * llcScale (lam + n) theta ε := by
    intro δ hδ
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        sublevelVol μ K f ε / llcScale lam theta ε ∈ Ioo (c - δ) (c + δ) :=
      h (Ioo_mem_nhds (by linarith) (by linarith))
    have hev2 := hev.and (llcScale_eventually_pos (lam := lam) (theta := theta))
    obtain ⟨b, hbmem, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev2
    rw [mem_Ioi] at hbmem
    refine ⟨min (b / 2) (1 / 2), lt_min (by linarith) (by norm_num),
      lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
    apply momentKernel_window n (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    intro ε hε
    have hmem : ε ∈ Ioo (0 : ℝ) b := by
      refine ⟨hε.1, ?_⟩
      calc ε ≤ min (b / 2) (1 / 2) := hε.2
        _ ≤ b / 2 := min_le_left _ _
        _ < b := by linarith
    obtain ⟨hratio, hpos⟩ := hsub hmem
    rw [mem_Ioo] at hratio
    refine ⟨?_, ?_⟩
    · have h1 := hratio.1; rw [lt_div_iff₀ hpos] at h1; linarith
    · have h1 := hratio.2; rw [div_lt_iff₀ hpos] at h1; linarith
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · set δ : ℝ := min (c / 2)
      ((c * Real.Gamma (lam + n + 1) - a)
        / (2 * (c + Real.Gamma (lam + n + 1) + 1))) with hδdef
    have hnum : 0 < c * Real.Gamma (lam + n + 1) - a := by linarith
    have hden : (0 : ℝ) < 2 * (c + Real.Gamma (lam + n + 1) + 1) := by positivity
    have hδpos : 0 < δ := lt_min (by linarith) (div_pos hnum hden)
    have hδc : δ ≤ c / 2 := min_le_left _ _
    have hδ2 : δ * (2 * (c + Real.Gamma (lam + n + 1) + 1))
        ≤ c * Real.Gamma (lam + n + 1) - a := by
      have := min_le_right (c / 2) ((c * Real.Gamma (lam + n + 1) - a)
        / (2 * (c + Real.Gamma (lam + n + 1) + 1)))
      calc δ * (2 * (c + Real.Gamma (lam + n + 1) + 1))
          ≤ (c * Real.Gamma (lam + n + 1) - a)
              / (2 * (c + Real.Gamma (lam + n + 1) + 1))
              * (2 * (c + Real.Gamma (lam + n + 1) + 1)) :=
            mul_le_mul_of_nonneg_right this hden.le
        _ = c * Real.Gamma (lam + n + 1) - a := div_mul_cancel₀ _ hden.ne'
    obtain ⟨ε₀, hε₀, hε₀1, hwin⟩ := hwinex δ hδpos
    have hsand := momentKernel_ratio_window (μ := μ) (K := K) (f := f) n
      hfin hlamn hε₀ hε₀1 hwin
    have hR := Real.head_subst_div_tendsto_gamma
      (lam := lam + n) (theta := theta) (ε₀ := ε₀) hlamn hε₀ hε₀1
    have hRev := hR.eventually (Ioo_mem_nhds
      (show Real.Gamma (lam + n + 1) - δ < Real.Gamma (lam + n + 1) by linarith)
      (show Real.Gamma (lam + n + 1) < Real.Gamma (lam + n + 1) + δ by linarith))
    filter_upwards [hsand, hRev] with s hs hRs
    have hcδ : 0 < c - δ := by linarith
    have hkey : a < (c - δ) * (Real.Gamma (lam + n + 1) - δ) := by
      nlinarith [hδ2, hnum, hδpos, sq_nonneg δ]
    calc a < (c - δ) * (Real.Gamma (lam + n + 1) - δ) := hkey
      _ ≤ (c - δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ (lam + n) * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1)) :=
          mul_le_mul_of_nonneg_left hRs.1.le hcδ.le
      _ ≤ _ := hs.1
  · set δ : ℝ := min (min (c / 2) 1)
      ((b - c * Real.Gamma (lam + n + 1))
        / (2 * (c + Real.Gamma (lam + n + 1) + 2))) with hδdef
    have hnum : 0 < b - c * Real.Gamma (lam + n + 1) := by linarith
    have hden : (0 : ℝ) < 2 * (c + Real.Gamma (lam + n + 1) + 2) := by positivity
    have hδpos : 0 < δ :=
      lt_min (lt_min (by linarith) one_pos) (div_pos hnum hden)
    have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
    have hδ2 : δ * (2 * (c + Real.Gamma (lam + n + 1) + 2))
        ≤ b - c * Real.Gamma (lam + n + 1) := by
      have hm := min_le_right (min (c / 2) 1) ((b - c * Real.Gamma (lam + n + 1))
        / (2 * (c + Real.Gamma (lam + n + 1) + 2)))
      calc δ * (2 * (c + Real.Gamma (lam + n + 1) + 2))
          ≤ (b - c * Real.Gamma (lam + n + 1))
              / (2 * (c + Real.Gamma (lam + n + 1) + 2))
              * (2 * (c + Real.Gamma (lam + n + 1) + 2)) :=
            mul_le_mul_of_nonneg_right hm hden.le
        _ = b - c * Real.Gamma (lam + n + 1) := div_mul_cancel₀ _ hden.ne'
    obtain ⟨ε₀, hε₀, hε₀1, hwin⟩ := hwinex δ hδpos
    have hsand := momentKernel_ratio_window (μ := μ) (K := K) (f := f) n
      hfin hlamn hε₀ hε₀1 hwin
    have hR := Real.head_subst_div_tendsto_gamma
      (lam := lam + n) (theta := theta) (ε₀ := ε₀) hlamn hε₀ hε₀1
    have hRev := hR.eventually (Ioo_mem_nhds
      (show Real.Gamma (lam + n + 1) - δ < Real.Gamma (lam + n + 1) by linarith)
      (show Real.Gamma (lam + n + 1) < Real.Gamma (lam + n + 1) + δ by linarith))
    have htail0 := momentTail_isLittleO (μ := μ) (K := K) (f := f)
      (lam := lam) (theta := theta) hfin hε₀ n
    have htailto : Tendsto (fun s => (s * ∫ ε in Ioi ε₀,
        Real.exp (-(s * ε)) * momentKernel μ K f n ε)
        / laplaceScale (lam + n) theta s) atTop (𝓝 0) :=
      htail0.tendsto_div_nhds_zero
    have htle := htailto.eventually_lt_const hδpos
    filter_upwards [hsand, hRev, htle] with s hs hRs htl
    have hδsq : δ * δ ≤ δ := by nlinarith [hδ1, hδpos]
    have hkey : (c + δ) * (Real.Gamma (lam + n + 1) + δ) + δ < b := by
      nlinarith [hδ2, hnum, hδsq]
    calc (s * ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f n ε)
          / laplaceScale (lam + n) theta s
        ≤ (c + δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
            * (u ^ (lam + n) * (Real.log s - Real.log u) ^ (theta - 1)))
          / Real.log s ^ (theta - 1))
          + (s * ∫ ε in Ioi ε₀, Real.exp (-(s * ε)) * momentKernel μ K f n ε)
              / laplaceScale (lam + n) theta s := hs.2
      _ ≤ (c + δ) * (Real.Gamma (lam + n + 1) + δ) + δ := by
          have h1 : (c + δ) * ((∫ u in Ioc (0 : ℝ) (s * ε₀), Real.exp (-u)
              * (u ^ (lam + n) * (Real.log s - Real.log u) ^ (theta - 1)))
            / Real.log s ^ (theta - 1))
              ≤ (c + δ) * (Real.Gamma (lam + n + 1) + δ) :=
            mul_le_mul_of_nonneg_left hRs.2.le (by linarith)
          linarith [htl]
      _ < b := hkey

/-! ## The moment-recursion kernel identity -/

/-- The antiderivative identity behind the moment recursion:
for `t ≥ 0`, `s > 0`, and any `n`,
`∫_{Ioi t} (s·ε^n − n·ε^{n−1}) e^{−s·ε} dε = t^n e^{−s·t}`, since
`−ε^n e^{−s·ε}` is an antiderivative vanishing at `+∞`. -/
theorem _root_.integral_momentRec_kernel {s t : ℝ} (hs : 0 < s) (ht : 0 ≤ t)
    (n : ℕ) :
    ∫ ε in Ioi t, (s * ε ^ n - (n : ℝ) * ε ^ (n - 1)) * Real.exp (-(s * ε))
      = t ^ n * Real.exp (-(s * t)) := by
  set F : ℝ → ℝ := fun ε => -(ε ^ n * Real.exp (-(s * ε))) with hFdef
  set F' : ℝ → ℝ :=
    fun ε => (s * ε ^ n - (n : ℝ) * ε ^ (n - 1)) * Real.exp (-(s * ε)) with hF'def
  have hderiv : ∀ ε ∈ Ici t, HasDerivAt F (F' ε) ε := by
    intro ε _
    have hpow : HasDerivAt (fun x : ℝ => x ^ n) ((n : ℝ) * ε ^ (n - 1)) ε :=
      hasDerivAt_pow n ε
    have hexp : HasDerivAt (fun x : ℝ => Real.exp (-(s * x)))
        (Real.exp (-(s * ε)) * (-s)) ε := by
      have hinner : HasDerivAt (fun x : ℝ => -(s * x)) (-s) ε :=
        (((hasDerivAt_id ε).const_mul s).neg).congr_deriv (by ring)
      refine ((Real.hasDerivAt_exp (-(s * ε))).comp ε hinner).congr_deriv ?_
      ring
    have hmul := hpow.mul hexp
    have hF : HasDerivAt F
        (-((n : ℝ) * ε ^ (n - 1) * Real.exp (-(s * ε))
          + ε ^ n * (Real.exp (-(s * ε)) * (-s)))) ε := hmul.neg
    convert hF using 1
    simp only [hF'def]
    ring
  have hint : IntegrableOn F' (Ioi t) := by
    have h1 : IntegrableOn (fun ε => Real.exp (-(s * ε)) * ε ^ n) (Ioi t) :=
      (integrableOn_exp_neg_mul_pow hs n).mono_set (Ioi_subset_Ioi ht)
    have h2 : IntegrableOn (fun ε => Real.exp (-(s * ε)) * ε ^ (n - 1)) (Ioi t) :=
      (integrableOn_exp_neg_mul_pow hs (n - 1)).mono_set (Ioi_subset_Ioi ht)
    refine MeasureTheory.IntegrableOn.congr_fun
      ((h1.const_mul s).sub (h2.const_mul (n : ℝ))) (fun ε _ => ?_)
      measurableSet_Ioi
    simp only [hF'def, Pi.sub_apply]; ring
  have htend : Tendsto F atTop (𝓝 0) := by
    have hb : Tendsto (fun ε : ℝ => ε ^ (n : ℝ) * Real.exp (-(s * ε)))
        atTop (𝓝 0) := by
      have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) s hs
      refine h.congr' ?_
      filter_upwards with ε
      rw [neg_mul]
    have hb' : Tendsto (fun ε : ℝ => ε ^ n * Real.exp (-(s * ε)))
        atTop (𝓝 0) := by
      refine hb.congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with ε hε
      rw [Real.rpow_natCast]
    have := hb'.neg
    rw [neg_zero] at this
    exact this
  have hmain := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend
  rw [hmain, hFdef]
  simp

/-! ## The Fubini lift to the raw-moment recursion -/

/-- The single-power tail `t ↦ ∫_{ε>t} ε^k e^{−sε}` is integrable over a
finite-measure localization `K` (for `s > 0`, `f ≥ 0` a.e. on `K`): it is
bounded by the full integral `∫_{ε>0} ε^k e^{−sε}` and antitone-measurable
once composed with the a.e.-nonnegative `f`. -/
private theorem integrableOn_tail_pow_exp (hfin : μ K ≠ ⊤)
    (hf_mble : AEMeasurable f (μ.restrict K)) (hf0 : 0 ≤ᵐ[μ.restrict K] f)
    {s : ℝ} (hs : 0 < s) (k : ℕ) :
    IntegrableOn
      (fun x => ∫ ε in Ioi (f x), ε ^ k * Real.exp (-(s * ε))) K μ := by
  set g : ℝ → ℝ := fun ε => ε ^ k * Real.exp (-(s * ε)) with hg
  have hg_int : ∀ a : ℝ, 0 ≤ a → IntegrableOn g (Ioi a) volume := by
    intro a ha
    exact MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_exp_neg_mul_pow hs k).mono_set (Ioi_subset_Ioi ha))
      (fun ε _ => mul_comm _ _) measurableSet_Ioi
  have hg_nonneg : ∀ a : ℝ, 0 ≤ a → ∀ ε ∈ Ioi a, 0 ≤ g ε := by
    intro a ha ε hε
    have : 0 < ε := lt_of_le_of_lt ha hε
    rw [hg]; positivity
  -- antitone extension `T t = ∫_{ε > max t 0} g`
  set T : ℝ → ℝ := fun t => ∫ ε in Ioi (max t 0), g ε with hT
  have hT_anti : Antitone T := by
    intro t₁ t₂ h₁₂
    have hmax : max t₁ 0 ≤ max t₂ 0 := by
      rcases le_total t₂ 0 with h | h
      · simp [max_eq_right (h₁₂.trans h), max_eq_right h]
      · exact (max_le_max h₁₂ le_rfl)
    refine setIntegral_mono_set (hg_int _ (le_max_right _ _)) ?_ ?_
    · exact ae_restrict_of_forall_mem measurableSet_Ioi
        (fun ε hε => hg_nonneg _ (le_max_right _ _) ε hε)
    · exact (Set.Ioi_subset_Ioi hmax).eventuallyLE
  have hT_meas : Measurable T := hT_anti.measurable
  -- our function equals `T ∘ f` a.e. on `K`
  have hcomp : (fun x => ∫ ε in Ioi (f x), g ε) =ᵐ[μ.restrict K] (T ∘ f) := by
    filter_upwards [hf0] with x hx
    have hmx : max (f x) 0 = f x := max_eq_left hx
    simp only [Function.comp_apply, hT]
    rw [hmx]
  have hmeas : AEStronglyMeasurable
      (fun x => ∫ ε in Ioi (f x), g ε) (μ.restrict K) :=
    (hT_meas.comp_aemeasurable hf_mble).aestronglyMeasurable.congr hcomp.symm
  refine Integrable.mono' (g := fun _ => ∫ ε in Ioi (0:ℝ), g ε)
    (integrableOn_const hfin) hmeas ?_
  filter_upwards [hf0] with x hx
  have hnn : 0 ≤ ∫ ε in Ioi (f x), g ε :=
    setIntegral_nonneg measurableSet_Ioi (fun ε hε => hg_nonneg _ hx ε hε)
  rw [Real.norm_of_nonneg hnn]
  exact setIntegral_mono_set (hg_int 0 le_rfl)
    (ae_restrict_of_forall_mem measurableSet_Ioi (fun ε hε => hg_nonneg 0 le_rfl ε hε))
    (Set.Ioi_subset_Ioi hx).eventuallyLE

/-- **The Bochner composed layer cake (`<` form).** For a finite measure `ν`,
a measurable a.e.-nonnegative `f`, and `g ≥ 0` integrable near `0`, the
average initial segment equals the superlevel-weighted integral:
`∫ (∫_0^{f x} g) dν = ∫_{ε>0} g ε · ν{ε < f}`. The real-integral translation
of `lintegral_comp_eq_lintegral_meas_lt_mul`. -/
private theorem integral_intervalIntegral_eq_integral_meas_lt (ν : Measure α)
    [IsFiniteMeasure ν] (hf_meas : Measurable f) (hf_nn : 0 ≤ᵐ[ν] f)
    {g : ℝ → ℝ} (hg_cont : Continuous g) (hg_nn : ∀ ε, 0 ≤ ε → 0 ≤ g ε) :
    (∫ x, (∫ ε in (0 : ℝ)..f x, g ε) ∂ν)
      = ∫ ε in Ioi (0 : ℝ), g ε * (ν {x | ε < f x}).toReal := by
  have hg_intI : ∀ t > (0 : ℝ), IntervalIntegrable g volume 0 t :=
    fun t _ => hg_cont.intervalIntegrable 0 t
  have hg_nn_ae : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] g :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (ae_of_all _ (fun ε hε => hg_nn ε hε.le))
  have key := lintegral_comp_eq_lintegral_meas_lt_mul ν hf_nn hf_meas.aemeasurable
    hg_intI hg_nn_ae
  have hGcont : Continuous (fun t => ∫ ε in (0 : ℝ)..t, g ε) :=
    intervalIntegral.continuous_primitive
      (fun a b => hg_cont.intervalIntegrable a b) 0
  have hJ_meas : AEStronglyMeasurable
      (fun x => ∫ ε in (0 : ℝ)..f x, g ε) ν :=
    (hGcont.measurable.comp hf_meas).aestronglyMeasurable
  have hJ_nn : 0 ≤ᵐ[ν] fun x => ∫ ε in (0 : ℝ)..f x, g ε := by
    filter_upwards [hf_nn] with x hx
    exact intervalIntegral.integral_nonneg hx (fun u hu => hg_nn u hu.1)
  have hfin_lt : ∀ ε : ℝ, ν {x | ε < f x} ≠ ⊤ := fun ε => measure_ne_top ν _
  have hR_meas : AEStronglyMeasurable
      (fun ε => g ε * (ν {x | ε < f x}).toReal)
      (volume.restrict (Ioi (0 : ℝ))) := by
    refine (hg_cont.measurable.mul (Measurable.ennreal_toReal ?_)).aestronglyMeasurable
    exact Antitone.measurable
      (fun a b hab => measure_mono (fun x hx => lt_of_le_of_lt hab hx))
  have hR_nn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun ε => g ε * (ν {x | ε < f x}).toReal := by
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ (fun ε hε => ?_))
    exact mul_nonneg (hg_nn ε hε.le) ENNReal.toReal_nonneg
  rw [integral_eq_lintegral_of_nonneg_ae hJ_nn hJ_meas,
      integral_eq_lintegral_of_nonneg_ae hR_nn hR_meas]
  congr 1
  rw [key]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun ε hε => ?_)
  rw [ENNReal.ofReal_mul (hg_nn ε hε.le), ENNReal.ofReal_toReal (hfin_lt ε),
    mul_comm]

/-- **Single-piece / tail Cavalieri.** Integrating the decreasing
tail `I_k(f x) = ∫_{ε>f x} g` of the loss over a finite measure `ν`
reproduces the sublevel-weighted integral:
`∫ (∫_{ε>f x} g) dν = ∫_{ε>0} g ε · ν{f ≤ ε}`. -/
private theorem integral_tail_eq_integral_meas_le (ν : Measure α) [IsFiniteMeasure ν]
    (hf_meas : Measurable f) (hf_nn : 0 ≤ᵐ[ν] f) {g : ℝ → ℝ}
    (hg_cont : Continuous g) (hg_int : IntegrableOn g (Ioi 0) volume)
    (hg_nn : ∀ ε, 0 ≤ ε → 0 ≤ g ε) :
    (∫ x, (∫ ε in Ioi (f x), g ε) ∂ν)
      = ∫ ε in Ioi (0 : ℝ), g ε * (ν {x | f x ≤ ε}).toReal := by
  set C : ℝ := ∫ ε in Ioi (0 : ℝ), g ε with hC
  have hGcont : Continuous (fun t => ∫ ε in (0 : ℝ)..t, g ε) :=
    intervalIntegral.continuous_primitive
      (fun a b => hg_cont.intervalIntegrable a b) 0
  -- the initial-segment function is integrable on `ν` (bounded by `C`)
  have hJ_int : Integrable (fun x => ∫ ε in (0 : ℝ)..f x, g ε) ν := by
    refine Integrable.mono' (integrable_const C)
      (hGcont.measurable.comp hf_meas).aestronglyMeasurable ?_
    filter_upwards [hf_nn] with x hx
    have hx0 : (0 : ℝ) ≤ f x := hx
    have hJnn : (0 : ℝ) ≤ ∫ ε in (0 : ℝ)..f x, g ε :=
      intervalIntegral.integral_nonneg hx0 (fun u hu => hg_nn u hu.1)
    rw [Real.norm_of_nonneg hJnn, intervalIntegral.integral_of_le hx0, hC]
    exact setIntegral_mono_set hg_int
      (ae_restrict_of_forall_mem measurableSet_Ioi (fun ε hε => hg_nn ε hε.le))
      Set.Ioc_subset_Ioi_self.eventuallyLE
  -- tail = total − initial, a.e.
  have htail : (fun x => ∫ ε in Ioi (f x), g ε)
      =ᵐ[ν] fun x => C - ∫ ε in (0 : ℝ)..f x, g ε := by
    filter_upwards [hf_nn] with x hx
    have hx0 : (0 : ℝ) ≤ f x := hx
    have hsplit : C = (∫ ε in (0 : ℝ)..f x, g ε) + ∫ ε in Ioi (f x), g ε := by
      rw [hC, intervalIntegral.integral_of_le hx0,
        ← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
          (hg_int.mono_set Set.Ioc_subset_Ioi_self)
          (hg_int.mono_set (Set.Ioi_subset_Ioi hx0)),
        Ioc_union_Ioi_eq_Ioi hx0]
    linarith
  -- boundedness factor for the superlevel integral
  have hbdd : ∀ ε, (ν {x | ε < f x}).toReal ≤ (ν Set.univ).toReal := fun ε =>
    ENNReal.toReal_mono (measure_ne_top ν _) (measure_mono (Set.subset_univ _))
  have hlt_meas : Measurable (fun ε => (ν {x | ε < f x}).toReal) :=
    Measurable.ennreal_toReal
      (Antitone.measurable
        (fun a b hab => measure_mono (fun x hx => lt_of_le_of_lt hab hx)))
  have hglt_int : IntegrableOn (fun ε => g ε * (ν {x | ε < f x}).toReal)
      (Ioi (0 : ℝ)) volume :=
    MeasureTheory.IntegrableOn.congr_fun
      (hg_int.bdd_mul hlt_meas.aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ε => by
          rw [Real.norm_of_nonneg ENNReal.toReal_nonneg]; exact hbdd ε)))
      (fun ε _ => mul_comm _ _) measurableSet_Ioi
  rw [integral_congr_ae htail,
    integral_sub (integrable_const C) hJ_int, integral_const, smul_eq_mul,
    integral_intervalIntegral_eq_integral_meas_lt ν hf_meas hf_nn hg_cont hg_nn,
    hC, ← integral_const_mul,
    ← integral_sub (hg_int.const_mul _) hglt_int]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ε hε => ?_)
  have hcompl : (ν {x | f x ≤ ε}).toReal
      = (ν Set.univ).toReal - (ν {x | ε < f x}).toReal := by
    rw [← ENNReal.toReal_sub_of_le (measure_mono (Set.subset_univ _))
        (measure_ne_top ν _)]
    congr 1
    rw [← measure_compl (measurableSet_lt measurable_const hf_meas)
      (measure_ne_top ν _)]
    congr 1
    ext x; simp [not_lt]
  rw [hcompl]; simp only [measureReal_def]; ring

/-- **Specialized.** The Laplace-weighted moment kernel `A_k` is the
loss-average of the tail `∫_{ε>f x} ε^k e^{−sε}`. -/
theorem setIntegral_tail_eq_momentKernel (hfin : μ K ≠ ⊤)
    (hf_meas : Measurable f) (hf0 : 0 ≤ᵐ[μ.restrict K] f) {s : ℝ} (hs : 0 < s)
    (k : ℕ) :
    (∫ x in K, (∫ ε in Ioi (f x), ε ^ k * Real.exp (-(s * ε))) ∂μ)
      = ∫ ε in Ioi (0 : ℝ), Real.exp (-(s * ε)) * momentKernel μ K f k ε := by
  haveI : IsFiniteMeasure (μ.restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin.lt_top⟩
  have hg_cont : Continuous (fun ε => ε ^ k * Real.exp (-(s * ε))) := by fun_prop
  have hg_int : IntegrableOn (fun ε => ε ^ k * Real.exp (-(s * ε)))
      (Ioi (0 : ℝ)) volume :=
    MeasureTheory.IntegrableOn.congr_fun (integrableOn_exp_neg_mul_pow hs k)
      (fun ε _ => mul_comm _ _) measurableSet_Ioi
  have hg_nn : ∀ ε, 0 ≤ ε → 0 ≤ ε ^ k * Real.exp (-(s * ε)) :=
    fun ε hε => mul_nonneg (pow_nonneg hε k) (Real.exp_nonneg _)
  rw [integral_tail_eq_integral_meas_le (μ.restrict K) hf_meas hf0 hg_cont
    hg_int hg_nn]
  refine setIntegral_congr_fun measurableSet_Ioi (fun ε hε => ?_)
  have hset : (μ.restrict K) {x | f x ≤ ε} = μ (K ∩ {x | f x ≤ ε}) := by
    rw [Measure.restrict_apply (measurableSet_le hf_meas measurable_const),
      Set.inter_comm]
  simp only [momentKernel, sublevelVol, hset]
  ring

/-- **The recursion.** The raw loss moment
`M_{n+1}(s) = ∫_K f^{n+1} e^{−s f} dμ` satisfies
`M_{n+1} = s·A_{n+1} − (n+1)·A_n`, where
`A_k(s) = ∫_{ε>0} e^{−sε} · momentKernel μ K f k ε dε`. -/
theorem setIntegral_pow_mul_exp_eq_momentRecursion (hfin : μ K ≠ ⊤)
    (hf_meas : Measurable f) (hf0 : 0 ≤ᵐ[μ.restrict K] f) {s : ℝ} (hs : 0 < s)
    (n : ℕ) :
    (∫ x in K, f x ^ (n + 1) * Real.exp (-(s * f x)) ∂μ)
      = s * (∫ ε in Ioi (0 : ℝ),
            Real.exp (-(s * ε)) * momentKernel μ K f (n + 1) ε)
        - (n + 1 : ℝ) * (∫ ε in Ioi (0 : ℝ),
            Real.exp (-(s * ε)) * momentKernel μ K f n ε) := by
  -- pointwise: f^{n+1} e^{−sf} = s·I_{n+1}(f) − (n+1)·I_n(f), by the kernel identity
  have hpt : (fun x => f x ^ (n + 1) * Real.exp (-(s * f x)))
      =ᵐ[μ.restrict K] fun x =>
        s * (∫ ε in Ioi (f x), ε ^ (n + 1) * Real.exp (-(s * ε)))
          - (n + 1 : ℝ) * (∫ ε in Ioi (f x), ε ^ n * Real.exp (-(s * ε))) := by
    filter_upwards [hf0] with x hx
    have hx0 : (0 : ℝ) ≤ f x := hx
    have hk := integral_momentRec_kernel hs hx0 (n + 1)
    rw [Nat.add_sub_cancel] at hk
    have hint1 : IntegrableOn (fun ε => ε ^ (n + 1) * Real.exp (-(s * ε)))
        (Ioi (f x)) volume :=
      MeasureTheory.IntegrableOn.congr_fun
        ((integrableOn_exp_neg_mul_pow hs (n + 1)).mono_set
          (Set.Ioi_subset_Ioi hx0)) (fun ε _ => mul_comm _ _) measurableSet_Ioi
    have hint0 : IntegrableOn (fun ε => ε ^ n * Real.exp (-(s * ε)))
        (Ioi (f x)) volume :=
      MeasureTheory.IntegrableOn.congr_fun
        ((integrableOn_exp_neg_mul_pow hs n).mono_set
          (Set.Ioi_subset_Ioi hx0)) (fun ε _ => mul_comm _ _) measurableSet_Ioi
    rw [← hk, ← integral_const_mul, ← integral_const_mul,
      ← integral_sub (hint1.const_mul s) (hint0.const_mul _)]
    refine setIntegral_congr_fun measurableSet_Ioi (fun ε _ => ?_)
    push_cast; ring
  have hI1 := integrableOn_tail_pow_exp hfin hf_meas.aemeasurable hf0 hs (n + 1)
  have hI0 := integrableOn_tail_pow_exp hfin hf_meas.aemeasurable hf0 hs n
  rw [integral_congr_ae hpt,
    integral_sub (hI1.const_mul s) (hI0.const_mul _),
    integral_const_mul, integral_const_mul,
    setIntegral_tail_eq_momentKernel hfin hf_meas hf0 hs (n + 1),
    setIntegral_tail_eq_momentKernel hfin hf_meas hf0 hs n]

end SingularLearningTheory
