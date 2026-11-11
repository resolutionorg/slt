/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Defs
import SLT.VolumeScaling.Basic
import SLT.VolumeScaling.Transport

/-!
# Power composition of the scaling exponents

Raising a nonnegative function to a positive power `c` rescales `λ` by `1/c` and keeps `θ`
unchanged: the sublevel sets satisfy `{g^c ≤ ε} = {g ≤ ε^{1/c}}` exactly, and the model scale
obeys the exact identity `llcScale lam θ (ε^a) = a^{θ-1} · llcScale (a·lam) θ ε` on `(0,1)`.
This is how a reduced monomial block lands on the `(∏ zᵢ)²` shape of `LFoldProduct`: the block
`∏|zᵢ|^{1/λ}` is `((∏ zᵢ)²)^{1/(2λ)}` (`BlockKernel`).
-/

public section

open Filter MeasureTheory Asymptotics Set Real
open scoped Topology ENNReal

namespace SingularLearningTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : Set α}
  {g : α → ℝ} {lam theta : ℝ}

/-- The model scale composed with a power of `ε`: an exact identity on
`(0,1)`. -/
theorem llcScale_rpow_comp {a : ℝ} (ha : 0 < a) {ε : ℝ}
    (hε : ε ∈ Ioo (0 : ℝ) 1) :
    llcScale lam theta (ε ^ a)
      = a ^ (theta - 1) * llcScale (a * lam) theta ε := by
  have hlog : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε.1 hε.2)
  unfold llcScale
  rw [← Real.rpow_mul hε.1.le, Real.log_rpow hε.1, neg_mul_eq_mul_neg,
    Real.mul_rpow ha.le hlog.le, mul_comm a lam]
  ring

/-- The power map preserves the right-neighborhood filter at zero. -/
theorem _root_.tendsto_rpow_nhdsGT_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => ε ^ a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h := (Real.continuousAt_rpow_const 0 a (Or.inr ha.le)).tendsto
    rw [Real.zero_rpow ha.ne'] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with ε (hε : 0 < ε)
    exact Real.rpow_pos_of_pos hε a

/-- **Exponents under sublevel power-reparametrization**: if the
sublevel volumes of `f` are those of `g` at threshold `ε^a`, the
exponent pairs match with `λ` scaled by `a`. -/
theorem hasLLCExponentsOn_comp_rpow_sublevel {β : Type*}
    [MeasurableSpace β] {ν : Measure β} {K' : Set β} {f : α → ℝ}
    {g : β → ℝ} {a : ℝ} (ha : 0 < a)
    (hV : ∀ ε ∈ Ioo (0 : ℝ) 1,
      sublevelVol μ K f ε = sublevelVol ν K' g (ε ^ a)) :
    HasLLCExponentsOn μ K f (a * lam) theta ↔
      HasLLCExponentsOn ν K' g lam theta := by
  constructor
  · intro h
    -- recover g's volumes from f's at ε^(1/a)
    have hV' : ∀ ε ∈ Ioo (0 : ℝ) 1,
        sublevelVol ν K' g ε = sublevelVol μ K f (ε ^ a⁻¹) := by
      intro ε hε
      have hmem : ε ^ a⁻¹ ∈ Ioo (0 : ℝ) 1 :=
        ⟨Real.rpow_pos_of_pos hε.1 _,
         Real.rpow_lt_one hε.1.le hε.2 (inv_pos.mpr ha)⟩
      rw [hV _ hmem, ← Real.rpow_mul hε.1.le, inv_mul_cancel₀ ha.ne',
        Real.rpow_one]
    have hg : HasLLCExponentsOn μ K f (a * lam) theta := h
    unfold HasLLCExponentsOn at hg ⊢
    have hcomp : (fun ε : ℝ => sublevelVol μ K f (ε ^ a⁻¹))
        =Θ[𝓝[>] (0 : ℝ)]
        fun ε => llcScale (a * lam) theta (ε ^ a⁻¹) :=
      ⟨hg.1.comp_tendsto (tendsto_rpow_nhdsGT_zero (inv_pos.mpr ha)),
       hg.2.comp_tendsto (tendsto_rpow_nhdsGT_zero (inv_pos.mpr ha))⟩
    rw [Filter.EventuallyEq.isTheta_congr_left (l := 𝓝[>] (0 : ℝ))
      (f := sublevelVol ν K' g)
      (g := fun ε => sublevelVol μ K f (ε ^ a⁻¹))
      (by filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
          exact hV' ε hε)]
    refine hcomp.trans ?_
    have hsc : (fun ε : ℝ => llcScale (a * lam) theta (ε ^ a⁻¹))
        =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε => a⁻¹ ^ (theta - 1) * llcScale (a⁻¹ * (a * lam)) theta ε := by
      filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
      exact llcScale_rpow_comp (inv_pos.mpr ha) hε
    have hred : a⁻¹ * (a * lam) = lam := by
      field_simp
    rw [Filter.EventuallyEq.isTheta_congr_left hsc, hred,
      isTheta_const_mul_left
        (Real.rpow_pos_of_pos (inv_pos.mpr ha) _).ne']
    exact isTheta_rfl
  · intro h
    unfold HasLLCExponentsOn at h ⊢
    have hcomp : (fun ε : ℝ => sublevelVol ν K' g (ε ^ a))
        =Θ[𝓝[>] (0 : ℝ)]
        fun ε => llcScale lam theta (ε ^ a) :=
      ⟨h.1.comp_tendsto (tendsto_rpow_nhdsGT_zero ha),
       h.2.comp_tendsto (tendsto_rpow_nhdsGT_zero ha)⟩
    rw [Filter.EventuallyEq.isTheta_congr_left (l := 𝓝[>] (0 : ℝ))
      (f := sublevelVol μ K f)
      (g := fun ε => sublevelVol ν K' g (ε ^ a))
      (by filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
          exact hV ε hε)]
    refine hcomp.trans ?_
    have hsc : (fun ε : ℝ => llcScale lam theta (ε ^ a))
        =ᶠ[𝓝[>] (0 : ℝ)]
        fun ε => a ^ (theta - 1) * llcScale (a * lam) theta ε := by
      filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
      exact llcScale_rpow_comp ha hε
    rw [Filter.EventuallyEq.isTheta_congr_left hsc,
      isTheta_const_mul_left (Real.rpow_pos_of_pos ha _).ne']
    exact isTheta_rfl

/-- **Power composition**: raising a nonnegative function to a positive
power `c` divides `λ` by `c` and preserves `θ`. -/
theorem HasLLCExponentsOn.rpow_comp {c : ℝ} (hc : 0 < c)
    (hg : ∀ x ∈ K, 0 ≤ g x)
    (h : HasLLCExponentsOn μ K g lam theta) :
    HasLLCExponentsOn μ K (fun x => g x ^ c) (lam / c) theta := by
  have hV : ∀ ε ∈ Ioo (0 : ℝ) 1,
      sublevelVol μ K (fun x => g x ^ c) ε
        = sublevelVol μ K g (ε ^ c⁻¹) := by
    intro ε hε
    have hset : K ∩ {x | g x ^ c ≤ ε} = K ∩ {x | g x ≤ ε ^ c⁻¹} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq,
        and_congr_right_iff]
      intro hx
      constructor
      · intro hle
        rw [← rpow_le_rpow_iff (hg x hx)
            (Real.rpow_pos_of_pos hε.1 _).le hc]
        rwa [← Real.rpow_mul hε.1.le, inv_mul_cancel₀ hc.ne',
          Real.rpow_one]
      · intro hle
        have h2 := (rpow_le_rpow_iff (hg x hx)
          (Real.rpow_pos_of_pos hε.1 _).le hc).mpr hle
        rwa [← Real.rpow_mul hε.1.le, inv_mul_cancel₀ hc.ne',
          Real.rpow_one] at h2
    unfold sublevelVol
    rw [hset]
  have hiff := hasLLCExponentsOn_comp_rpow_sublevel
    (μ := μ) (K := K) (f := fun x => g x ^ c)
    (ν := μ) (K' := K) (g := g)
    (lam := lam) (theta := theta) (inv_pos.mpr hc) hV
  have hred : c⁻¹ * lam = lam / c := by
    rw [div_eq_inv_mul]
  rw [← hred]
  exact hiff.mpr h

end SingularLearningTheory
