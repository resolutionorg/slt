/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Elliott, Claude
-/
module

public import SLT.VolumeScaling.Product.Monomial
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# The L-fold product monomial

On the cube `[-1,1]^L`, the sublevel volume of `|∏ᵢ xᵢ|` has the exact closed form

  `vol {x ∈ [-1,1]^L : |∏ᵢ xᵢ| ≤ δ} = 2^L · δ · ∑_{k<L} (-log δ)^k / k!`

for `δ ∈ (0,1)`, and consequently `(∏ᵢ xᵢ)²` satisfies `HasLLCOn` with

  `(λ, θ, c) = (1/2, L, 2/(L-1)!)`.

This is the basic example of a learning coefficient with multiplicity larger than one
([Wat09]): the product of `L` coordinates has exponent `1/2` and multiplicity `L`. The
equal-exponent block (`BlockKernel`) is derived from it.

The proof is induction on the dimension, peeling one coordinate via
`measurePreserving_piFinSuccAbove` and slicing with the `sliceHalfLen` machinery of the
two-dimensional case (`ProductMonomial`); the slice integral is driven by
`∫ t in δ..1, (log (t/δ))^k / t = (-log δ)^{k+1}/(k+1)` (the fundamental theorem of calculus).
-/

@[expose] public section

open MeasureTheory Set Filter Topology intervalIntegral

namespace SingularLearningTheory

/-- The positive-cube profile `F_L(u) = u · ∑_{k<L} (-log u)^k / k!`.
`F_L(1) = 1` for `L ≥ 1`, matching the full-cube volume; the signed-cube
volume at threshold `δ` is `2^L · F_L(δ)`. -/
noncomputable def prodProfile (L : ℕ) (u : ℝ) : ℝ :=
  u * ∑ k ∈ Finset.range L, (-Real.log u) ^ k / k.factorial

theorem prodProfile_one {L : ℕ} (hL : 0 < L) : prodProfile L 1 = 1 := by
  unfold prodProfile
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [Real.log_one, zero_pow hk]
  · intro h
    exact absurd (Finset.mem_range.mpr hL) h

theorem prodProfile_pos {L : ℕ} {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    0 < prodProfile (L + 1) u := by
  unfold prodProfile
  have hlog : 0 ≤ -Real.log u := by
    have := Real.log_nonpos hu0.le hu1
    linarith
  refine mul_pos hu0 ?_
  refine Finset.sum_pos' (fun k _ => by positivity) ⟨0, Finset.mem_range.mpr (Nat.succ_pos L), ?_⟩
  simp

/-- The driving FTC integral: `∫ t in δ..1, (log (t/δ))^k / t dt
= (-log δ)^{k+1} / (k+1)`. -/
theorem _root_.integral_log_pow_div {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (k : ℕ) :
    ∫ t in δ..1, (Real.log (t / δ)) ^ k / t = (-Real.log δ) ^ (k + 1) / (k + 1) := by
  have key : ∀ t ∈ uIcc δ 1, HasDerivAt (fun s => (Real.log (s / δ)) ^ (k + 1) / (k + 1))
      ((Real.log (t / δ)) ^ k / t) t := by
    intro t ht
    rw [uIcc_of_le hδ1] at ht
    have ht0 : 0 < t := lt_of_lt_of_le hδ0 ht.1
    have h1 : HasDerivAt (fun s : ℝ => Real.log (s / δ)) (1 / t) t := by
      have hd : HasDerivAt (fun s : ℝ => s / δ) (1 / δ) t := by
        simpa using (hasDerivAt_id t).div_const δ
      have hlog : HasDerivAt Real.log (t / δ)⁻¹ (t / δ) :=
        Real.hasDerivAt_log (by positivity)
      have := hlog.comp t hd
      have heq : (t / δ)⁻¹ * (1 / δ) = 1 / t := by
        rw [inv_div]
        field_simp
      exact heq ▸ this
    have h2 := (h1.pow (k + 1)).div_const ((k : ℝ) + 1)
    have hk : ((k : ℝ) + 1) ≠ 0 := by positivity
    have heq2 : (((k + 1 : ℕ) : ℝ)) * Real.log (t / δ) ^ (k + 1 - 1) * (1 / t)
        / ((k : ℝ) + 1) = Real.log (t / δ) ^ k / t := by
      push_cast [Nat.add_sub_cancel]
      field_simp
    exact heq2 ▸ h2
  have hcont : ContinuousOn (fun t => (Real.log (t / δ)) ^ k / t) (uIcc δ 1) := by
    rw [uIcc_of_le hδ1]
    refine ContinuousOn.div ?_ continuousOn_id
      (fun x hx => (lt_of_lt_of_le hδ0 hx.1).ne') ; clear key
    refine ContinuousOn.pow ?_ k
    refine ContinuousOn.log (continuousOn_id.div_const δ) ?_
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hδ0 hx.1
    have : (0 : ℝ) < x / δ := by positivity
    simpa using this.ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt key (hcont.intervalIntegrable)]
  rw [div_self hδ0.ne', Real.log_one, one_div, Real.log_inv]
  simp [zero_pow (Nat.succ_ne_zero k)]

/-- Continuity of the slice profile `t ↦ prodProfile (L+1) (sliceHalfLen δ t)`:
`sliceHalfLen` is continuous and strictly positive, and `prodProfile (L+1)` is
continuous on positives. -/
theorem continuous_prodProfile_sliceHalfLen {L : ℕ} {δ : ℝ} (hδ0 : 0 < δ) :
    Continuous fun t => prodProfile (L + 1) (sliceHalfLen δ t) := by
  have hm := continuous_sliceHalfLen hδ0
  have hpos : ∀ t, sliceHalfLen δ t ≠ 0 := fun t => (sliceHalfLen_pos hδ0 t).ne'
  unfold prodProfile
  exact hm.mul (continuous_finsetSum _ fun k _ =>
    (((hm.log hpos).neg.pow k).div_const _))

/-- The slice-profile integral that drives the induction:
`∫ t in -1..1, prodProfile (L+1) (sliceHalfLen δ t) = 2 · prodProfile (L+2) δ`
for `δ ∈ (0,1)`.  Mid piece `[-δ,δ]` contributes `2δ`; each outer piece
contributes `δ ∑_{k<L+1} (-log δ)^{k+1}/(k+1)!` via `integral_log_pow_div`. -/
theorem integral_prodProfile_sliceHalfLen {L : ℕ} {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    ∫ t in (-1 : ℝ)..1, prodProfile (L + 1) (sliceHalfLen δ t)
      = 2 * prodProfile (L + 2) δ := by
  have hm := continuous_prodProfile_sliceHalfLen (L := L) hδ0
  have hδle : -δ ≤ δ := by linarith
  have hi : ∀ a b : ℝ, IntervalIntegrable
      (fun t => prodProfile (L + 1) (sliceHalfLen δ t)) volume a b :=
    fun a b => hm.intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (a := (-1 : ℝ)) (b := -δ)
      (c := 1) (hi _ _) (hi _ _),
    ← intervalIntegral.integral_add_adjacent_intervals (a := (-δ : ℝ)) (b := δ)
      (c := 1) (hi _ _) (hi _ _)]
  -- the outer-piece value
  set R : ℝ := δ * ∑ k ∈ Finset.range (L + 1), (-Real.log δ) ^ (k + 1) / (k + 1).factorial
    with hR
  -- mid piece: sliceHalfLen = 1, prodProfile (L+1) 1 = 1
  have hmid : ∫ t in (-δ : ℝ)..δ, prodProfile (L + 1) (sliceHalfLen δ t) = 2 * δ := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) ?_]
    · rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    · intro t ht
      rw [uIcc_of_le hδle, mem_Icc] at ht
      dsimp only
      rw [sliceHalfLen_of_abs_le hδ0 (abs_le.mpr ⟨ht.1, ht.2⟩),
        prodProfile_one (Nat.succ_pos L)]
  -- right piece
  have hout : ∫ t in (δ : ℝ)..1, prodProfile (L + 1) (sliceHalfLen δ t) = R := by
    rw [intervalIntegral.integral_congr
        (g := fun t => ∑ k ∈ Finset.range (L + 1),
          (δ / k.factorial) * ((Real.log (t / δ)) ^ k / t)) ?_]
    · rw [intervalIntegral.integral_finsetSum fun k _ => ?_]
      · rw [hR, Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [intervalIntegral.integral_const_mul, integral_log_pow_div hδ0 hδ1 k]
        rw [Nat.factorial_succ]
        push_cast
        field_simp
      · exact ((((((continuousOn_id.div_const δ).log fun x hx => by
              rw [uIcc_of_le hδ1] at hx
              have : 0 < x := lt_of_lt_of_le hδ0 hx.1
              exact div_ne_zero this.ne' hδ0.ne').pow k).div continuousOn_id fun x hx => by
              rw [uIcc_of_le hδ1] at hx
              exact (lt_of_lt_of_le hδ0 hx.1).ne').intervalIntegrable).const_mul _)
    · intro t ht
      rw [uIcc_of_le hδ1, mem_Icc] at ht
      have ht0 : 0 < t := lt_of_lt_of_le hδ0 ht.1
      dsimp only
      rw [sliceHalfLen_of_le_abs (by rw [abs_of_pos ht0]; exact ht.1), abs_of_pos ht0]
      unfold prodProfile
      have hlog : -Real.log (δ / t) = Real.log (t / δ) := by
        rw [Real.log_div hδ0.ne' ht0.ne', Real.log_div ht0.ne' hδ0.ne']
        ring
      rw [hlog, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
      field_simp
  -- left piece equals the right piece by the reflection t ↦ -t
  have hleft : ∫ t in (-1 : ℝ)..(-δ), prodProfile (L + 1) (sliceHalfLen δ t) = R := by
    have hrefl : ∀ t : ℝ, sliceHalfLen δ (-t) = sliceHalfLen δ t := by
      intro t
      unfold sliceHalfLen
      rw [abs_neg]
    calc ∫ t in (-1 : ℝ)..(-δ), prodProfile (L + 1) (sliceHalfLen δ t)
        = ∫ t in (δ : ℝ)..1, prodProfile (L + 1) (sliceHalfLen δ (-t)) := by
          rw [← intervalIntegral.integral_comp_neg
            (fun t => prodProfile (L + 1) (sliceHalfLen δ t))]
      _ = ∫ t in (δ : ℝ)..1, prodProfile (L + 1) (sliceHalfLen δ t) := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [hrefl]
      _ = R := hout
  rw [hmid, hout, hleft]
  unfold prodProfile
  rw [hR]
  -- 2δ + 2·δ∑_{k<L+1}(-log δ)^{k+1}/(k+1)! = 2·δ·∑_{j<L+2}(-log δ)^j/j!
  rw [Finset.sum_range_succ' (fun j => (-Real.log δ) ^ j / (j.factorial : ℝ)) (L + 1)]
  simp only [Nat.factorial_zero, Nat.cast_one, pow_zero]
  ring

/-- On the cube, the product is bounded by one in absolute value. -/
theorem abs_prod_le_one {n : ℕ} {y : Fin n → ℝ}
    (hy : y ∈ Set.univ.pi fun _ : Fin n => Icc (-1 : ℝ) 1) : |∏ j, y j| ≤ 1 := by
  rw [Finset.abs_prod]
  refine Finset.prod_le_one₀ (fun j _ => abs_nonneg _) fun j _ => ?_
  exact abs_le.mpr ⟨(hy j (Set.mem_univ j)).1, (hy j (Set.mem_univ j)).2⟩

/-- The measure-level exact L-fold sublevel volume, by induction on the
dimension.  The induction peels the first coordinate to `ℝ × (Fin n → ℝ)`
via `measurePreserving_piFinSuccAbove`, identifies each slice as the
`n`-dimensional sublevel set at threshold `sliceHalfLen δ t` (the `δ ≤ 1`
form of the statement makes this uniform in `t` — no case split), and
integrates the profile with `integral_prodProfile_sliceHalfLen`. -/
theorem measure_abs_prod_pi (L : ℕ) :
    ∀ {δ : ℝ}, 0 < δ → δ ≤ 1 →
    volume ((Set.univ.pi fun _ : Fin (L + 1) => Icc (-1 : ℝ) 1)
        ∩ {x | |∏ i, x i| ≤ δ})
      = ENNReal.ofReal (2 ^ (L + 1) * prodProfile (L + 1) δ) := by
  induction L with
  | zero =>
    intro δ hδ0 hδ1
    have hset : (Set.univ.pi fun _ : Fin 1 => Icc (-1 : ℝ) 1)
        ∩ {x | |∏ i, x i| ≤ δ}
        = Set.univ.pi fun _ : Fin 1 => Icc (-δ) δ := by
      ext x
      simp only [mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_const, mem_ofPred_eq,
        Fin.prod_univ_one, mem_Icc, Fin.forall_fin_one, ← abs_le]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨le_trans h hδ1, h⟩
    rw [hset, volume_pi_pi, Finset.prod_const, Real.volume_Icc]
    simp only [Finset.card_univ, Fintype.card_fin]
    rw [show δ - -δ = 2 * δ by ring]
    unfold prodProfile
    simp
  | succ n ih =>
    intro δ hδ0 hδ1
    -- peel the first coordinate
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0 with he
    set Box : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun _ => Icc (-1 : ℝ) 1 with hBox
    set S : Set (ℝ × (Fin (n + 1) → ℝ)) :=
      (Icc (-1 : ℝ) 1 ×ˢ Box) ∩ {p | |p.1 * ∏ j, p.2 j| ≤ δ} with hS
    have hSm : MeasurableSet S := by
      refine ((measurableSet_Icc.prod ?_).inter ?_)
      · exact MeasurableSet.univ_pi fun _ => measurableSet_Icc
      · refine measurableSet_le ?_ measurable_const
        exact (measurable_fst.mul (Finset.univ.measurable_prod
          fun j _ => (measurable_pi_apply j).comp measurable_snd)).abs
    have hpre : (Set.univ.pi fun _ : Fin (n + 2) => Icc (-1 : ℝ) 1)
        ∩ {x | |∏ i, x i| ≤ δ} = e ⁻¹' S := by
      ext x
      simp only [hS, hBox, mem_inter_iff, Set.mem_pi, Set.mem_univ, forall_const,
        mem_ofPred_eq, Set.mem_preimage, Set.mem_prod,
        Fin.forall_fin_succ, Fin.prod_univ_succ]
      tauto
    have hmp : MeasurePreserving e volume (volume.prod volume) := by
      rw [he, MeasureTheory.volume_pi,
        show (volume : Measure (Fin (n + 1) → ℝ)) = Measure.pi fun _ => volume from
          MeasureTheory.volume_pi]
      exact measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => (volume : Measure ℝ)) 0
    rw [hpre, hmp.measure_preimage hSm.nullMeasurableSet]
    -- slice the product measure
    rw [Measure.prod_apply hSm]
    -- identify each slice
    have hslice : ∀ t : ℝ,
        volume (Prod.mk t ⁻¹' S)
          = Set.indicator (Icc (-1 : ℝ) 1)
              (fun t => ENNReal.ofReal
                (2 ^ (n + 1) * prodProfile (n + 1) (sliceHalfLen δ t))) t := by
      intro t
      by_cases ht : t ∈ Icc (-1 : ℝ) 1
      · rw [Set.indicator_of_mem ht]
        have hsec : Prod.mk t ⁻¹' S
            = Box ∩ {y | |∏ j, y j| ≤ sliceHalfLen δ t} := by
          ext y
          simp only [hS, Set.mem_preimage, mem_inter_iff, Set.mem_prod, mem_ofPred_eq]
          constructor
          · rintro ⟨⟨_, hy⟩, hxy⟩
            exact ⟨hy, ((abs_le_sliceHalfLen_iff hδ0 _).mp
              ⟨abs_prod_le_one hy, hxy⟩)⟩
          · rintro ⟨hy, hle⟩
            obtain ⟨_, h2⟩ := (abs_le_sliceHalfLen_iff hδ0 (∏ j, y j)).mpr hle
            exact ⟨⟨ht, hy⟩, h2⟩
        rw [hsec, ih (sliceHalfLen_pos hδ0 t) (sliceHalfLen_le_one hδ0 t)]
      · rw [Set.indicator_of_notMem ht]
        have : Prod.mk t ⁻¹' S = ∅ := by
          ext y
          simp only [hS, Set.mem_preimage, mem_inter_iff, Set.mem_prod, mem_ofPred_eq,
            Set.mem_empty_iff_false, iff_false]
          rintro ⟨⟨ht', _⟩, _⟩
          exact ht ht'
        rw [this, measure_empty]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Icc]
    -- ENNReal → Bochner
    have hg : Continuous fun t => 2 ^ (n + 1) * prodProfile (n + 1) (sliceHalfLen δ t) :=
      (continuous_prodProfile_sliceHalfLen hδ0).const_mul _
    have hnn : ∀ t : ℝ, 0 ≤ 2 ^ (n + 1) * prodProfile (n + 1) (sliceHalfLen δ t) :=
      fun t => by
        have := prodProfile_pos (L := n) (sliceHalfLen_pos hδ0 t) (sliceHalfLen_le_one hδ0 t)
        positivity
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal
        (hg.integrableOn_Icc) (Filter.Eventually.of_forall hnn)]
    -- evaluate the profile integral
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (by linarith : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_const_mul, integral_prodProfile_sliceHalfLen hδ0 hδ1]
    ring_nf

/-- The exact L-fold sublevel volume on the signed cube: for `δ ∈ (0,1]`,
`vol {x ∈ [-1,1]^(L+1) : |∏ᵢ xᵢ| ≤ δ} = 2^(L+1) · prodProfile (L+1) δ`. -/
theorem sublevelVol_abs_prod_pi (L : ℕ) {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    sublevelVol volume (Set.univ.pi fun _ : Fin (L + 1) => Icc (-1 : ℝ) 1)
        (fun x => |∏ i, x i|) δ
      = 2 ^ (L + 1) * prodProfile (L + 1) δ := by
  unfold sublevelVol
  rw [measure_abs_prod_pi L hδ0 hδ1, ENNReal.toReal_ofReal]
  have := prodProfile_pos (L := L) hδ0 hδ1
  positivity

/-- Squared form: for `ε ∈ (0,1)`,
`vol {x ∈ [-1,1]^(L+1) : (∏ᵢ xᵢ)² ≤ ε} = 2^(L+1) · prodProfile (L+1) √ε`. -/
theorem sublevelVol_prod_sq_pi (L : ℕ) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    sublevelVol volume (Set.univ.pi fun _ : Fin (L + 1) => Icc (-1 : ℝ) 1)
        (fun x => (∏ i, x i) ^ 2) ε
      = 2 ^ (L + 1) * prodProfile (L + 1) (ε ^ ((2 : ℝ))⁻¹) := by
  have hδ0 : 0 < ε ^ ((2 : ℝ))⁻¹ := Real.rpow_pos_of_pos hε0 _
  have hδ1 : ε ^ ((2 : ℝ))⁻¹ < 1 :=
    Real.rpow_lt_one hε0.le hε1 (by norm_num : (0:ℝ) < (2:ℝ)⁻¹)
  have hset : {x : Fin (L + 1) → ℝ | (∏ i, x i) ^ 2 ≤ ε}
      = {x | |∏ i, x i| ≤ ε ^ ((2 : ℝ))⁻¹} := by
    ext x
    rw [mem_ofPred_eq, mem_ofPred_eq,
      Real.le_rpow_inv_iff_of_pos (abs_nonneg _) hε0.le (by norm_num : (0:ℝ) < 2),
      show ((2:ℝ)) = ((2:ℕ) : ℝ) by norm_num, Real.rpow_natCast, sq_abs]
  unfold sublevelVol
  rw [hset]
  have := sublevelVol_abs_prod_pi L hδ0 hδ1.le
  unfold sublevelVol at this
  rw [this]

/-- **The exponents of the L-fold product**: `(∏ᵢ xᵢ)²` on `[-1,1]^(L+1)` has
`(λ, θ, c) = (1/2, L+1, 2/L!)`.  The ratio against the model scale is the
polynomial `∑_{k≤L} (2^{L+1-k}/k!) u^{L-k}` evaluated at `u = (-log ε)⁻¹`,
which tends to its constant term `2/L!`. -/
theorem hasLLCOn_prod_sq (L : ℕ) :
    HasLLCOn volume (Set.univ.pi fun _ : Fin (L + 1) => Icc (-1 : ℝ) 1)
      (fun x => (∏ i, x i) ^ 2) (1 / 2) (L + 1) (2 / L.factorial) := by
  set Q : ℝ → ℝ := fun u => ∑ k ∈ Finset.range (L + 1),
    (2 ^ (L + 1 - k) / k.factorial) * u ^ (L - k) with hQ
  have hQ0 : Q 0 = 2 / L.factorial := by
    simp only [hQ]
    rw [Finset.sum_eq_single L]
    · simp
    · intro k hk hkL
      have : L - k ≠ 0 := by
        rw [Finset.mem_range] at hk
        omega
      simp [zero_pow this]
    · intro h
      exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self L)) h
  have hQcont : Continuous Q := by
    rw [hQ]
    exact continuous_finsetSum _ fun k _ => (continuous_pow _).const_mul _
  have hu : Tendsto (fun ε : ℝ => (-Real.log ε)⁻¹) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_neg_log_nhdsGT_zero.inv_tendsto_atTop
  have hlim : Tendsto (fun ε : ℝ => Q ((-Real.log ε)⁻¹)) (𝓝[>] (0 : ℝ))
      (𝓝 (2 / L.factorial)) := by
    rw [← hQ0]
    exact (hQcont.tendsto 0).comp hu
  refine Tendsto.congr' ?_ hlim
  filter_upwards [(Ioo_mem_nhdsGT (zero_lt_one' ℝ))] with ε hε
  have hε0 : (0 : ℝ) < ε := hε.1
  have hlog : 0 < -Real.log ε := neg_pos.mpr (Real.log_neg hε.1 hε.2)
  have hrpow : (0 : ℝ) < ε ^ ((2 : ℝ))⁻¹ := Real.rpow_pos_of_pos hε0 _
  rw [sublevelVol_prod_sq_pi L hε.1 hε.2]
  unfold prodProfile llcScale
  rw [Real.log_rpow hε0,
    show ((L : ℝ) + 1) - 1 = (L : ℝ) by ring,
    show (1 : ℝ) / 2 = ((2 : ℝ))⁻¹ by norm_num,
    Real.rpow_natCast (-Real.log ε) L]
  simp only [hQ]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkL : k ≤ L := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  obtain ⟨m, hm⟩ : ∃ m, L = k + m := ⟨L - k, by omega⟩
  have h1 : L - k = m := by omega
  have h2 : L + 1 - k = m + 1 := by omega
  have hfac : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hlogne : Real.log ε ≠ 0 := (neg_pos.mp hlog).ne
  rw [h1, h2, hm, pow_add (-Real.log ε) k m, inv_pow]
  have hpm : (-Real.log ε) ^ m ≠ 0 := pow_ne_zero m hlog.ne'
  have key : ((-1 : ℝ) / 2) ^ k * 2 ^ k = (-1) ^ k := by
    rw [← mul_pow]
    norm_num
  field_simp
  linear_combination (-(Real.log ε ^ k * 2 ^ m * 2)) * key

end SingularLearningTheory
