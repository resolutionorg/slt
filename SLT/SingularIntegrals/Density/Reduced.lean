/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Density.Slice

/-!
# Reduced monomial slice densities

Factor out the power of the level variable and freeze the solved coordinate.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.SliceDensity
open SingularLearningTheory.MellinAnalysis

lemma ae_pos_box {n : ℕ} {b : ℝ} :
    ∀ᵐ y ∂(volume.restrict (Icc (0 : Fin n → ℝ) fun _ ↦ b)), ∀ j, 0 < y j :=
  (ae_box_pos (fun _ ↦ b)).mono fun _ hy j ↦ (hy j).1

section Reduced

variable {n : ℕ} (k h : Fin (n + 1) → ℕ) (b : ℝ) (f : (Fin (n + 1) → ℝ) → ℝ) (p : Fin (n + 1))
  (ρ : ℝ)

/-- `λ_p = (h_p + 1)/(2k_p)`, the exponent of the solved coordinate. -/
@[expose] noncomputable def lamP : ℝ := ((h p : ℝ) + 1) / aExp k p

/-- The reduced slice integrand `1_{t < A b^a} (t/A)^{λ_p − ρ} A^{−ρ}/a · f(x(t,y), y) ∏ y^h`. -/
@[expose] noncomputable def redInt (y : Fin n → ℝ) (t : ℝ) : ℝ≥0∞ :=
  (Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)).indicator (fun t ↦
    ENNReal.ofReal ((t / chartA k p y) ^ (lamP k h p - ρ) * chartA k p y ^ (-ρ) / aExp k p) *
      (ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) *
        ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j))))) t

/-- The reduced density `G(t) = v(t)/t^{ρ−1}`. -/
@[expose] noncomputable def redDens (t : ℝ) : ℝ≥0∞ := ∫⁻ y in Icc 0 (fun _ ↦ b),
    redInt k h b f p ρ y t

variable {k h b f p ρ}

theorem aExp_pos (hkp : 0 < k p) : 0 < aExp k p := by unfold aExp; positivity

theorem chartA_pos {y : Fin n → ℝ} (hy : ∀ j, 0 < y j) : 0 < chartA k p y :=
  Finset.prod_pos fun j _ ↦ pow_pos (hy j) _

/-- The exponent identity behind the factorisation `v(t) = t^{ρ−1} G(t)`. -/
private theorem slice_factor_eq {t A : ℝ} (ht : 0 < t) (hA : 0 < A) (ha : 0 < aExp k p) :
    t ^ (1 / aExp k p - 1) / (aExp k p * A ^ (1 / aExp k p)) *
        ((t / A) ^ (1 / aExp k p)) ^ (h p) =
      t ^ (ρ - 1) * ((t / A) ^ (lamP k h p - ρ) * A ^ (-ρ) / aExp k p) := by
  set a := aExp k p with ha_def
  have key : ∀ u v : ℝ, t ^ u * t ^ v = t ^ (u + v) := fun u v ↦ (Real.rpow_add ht u v).symm
  have keyA : ∀ u v : ℝ, A ^ u * A ^ v = A ^ (u + v) := fun u v ↦ (Real.rpow_add hA u v).symm
  have hx : ((t / A) ^ (1 / a)) ^ (h p) = t ^ ((h p : ℝ) / a) * A ^ (-((h p : ℝ) / a)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos ht hA).le, Real.div_rpow ht.le hA.le,
      Real.rpow_neg hA.le, div_eq_mul_inv (t ^ _), show 1 / a * (h p : ℝ) = (h p : ℝ) / a by ring]
  have hq : (t / A) ^ (lamP k h p - ρ) = t ^ (lamP k h p - ρ) * A ^ (-(lamP k h p - ρ)) := by
    rw [Real.div_rpow ht.le hA.le, Real.rpow_neg hA.le, div_eq_mul_inv (t ^ _)]
  have hinv : (A ^ (1 / a))⁻¹ = A ^ (-(1 / a)) := (Real.rpow_neg hA.le _).symm
  rw [hx, hq]
  calc t ^ (1 / a - 1) / (a * A ^ (1 / a)) * (t ^ ((h p : ℝ) / a) * A ^ (-((h p : ℝ) / a)))
      = (t ^ (1 / a - 1) * t ^ ((h p : ℝ) / a)) *
          ((A ^ (1 / a))⁻¹ * A ^ (-((h p : ℝ) / a))) / a := by
        ring
    _ = t ^ (1 / a - 1 + (h p : ℝ) / a) * A ^ (-(1 / a) + -((h p : ℝ) / a)) / a := by
        rw [key, hinv, keyA]
    _ = t ^ (ρ - 1 + (lamP k h p - ρ)) * A ^ (-(lamP k h p - ρ) + -ρ) / a := by
        have e1 : 1 / a - 1 + (h p : ℝ) / a = ρ - 1 + (lamP k h p - ρ) := by
          unfold lamP; rw [← ha_def]; field_simp; ring
        have e2 : -(1 / a) + -((h p : ℝ) / a) = -(lamP k h p - ρ) + -ρ := by
          unfold lamP; rw [← ha_def]; field_simp; ring
        rw [e1, e2]
    _ = t ^ (ρ - 1) * (t ^ (lamP k h p - ρ) * A ^ (-(lamP k h p - ρ)) * A ^ (-ρ) / a) := by
        rw [← key, ← keyA]; ring

private theorem sliceInt_eq_redInt {y : Fin n → ℝ} {t : ℝ} (ht : 0 < t) (hy : ∀ j, 0 < y j)
    (ha : 0 < aExp k p) :
    sliceInt k h b f p y t = ENNReal.ofReal (t ^ (ρ - 1)) * redInt k h b f p ρ y t := by
  unfold sliceInt redInt
  by_cases hmem : t ∈ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    have hA := chartA_pos (k := k) (p := p) hy
    have key : ENNReal.ofReal (t ^ (1 / aExp k p - 1) /
          (aExp k p * chartA k p y ^ (1 / aExp k p))) * ENNReal.ofReal (xOf k p t y ^ h p) =
        ENNReal.ofReal (t ^ (ρ - 1)) * ENNReal.ofReal
          ((t / chartA k p y) ^ (lamP k h p - ρ) * chartA k p y ^ (-ρ) / aExp k p) := by
      rw [← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg ht.le _)
          (mul_pos ha (Real.rpow_pos_of_pos hA _)).le),
        ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), xOf,
        slice_factor_eq (ρ := ρ) ht hA ha]
    calc _ = (ENNReal.ofReal (t ^ (1 / aExp k p - 1) /
          (aExp k p * chartA k p y ^ (1 / aExp k p))) * ENNReal.ofReal (xOf k p t y ^ h p)) *
          (ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) *
            ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j)))) := by ring
      _ = _ := by rw [key]; ring
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, mul_zero]

/-- **The factorisation `v(t) = t^{ρ−1} G(t)`** for `t > 0`. -/
theorem sliceDens_eq_redDens {t : ℝ} (ht : 0 < t) (ha : 0 < aExp k p) :
    sliceDens k h b f p t = ENNReal.ofReal (t ^ (ρ - 1)) * redDens k h b f p ρ t := by
  unfold sliceDens redDens
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr_ae ?_
  filter_upwards [ae_pos_box (n := n) (b := b)] with y hy
  exact sliceInt_eq_redInt ht hy ha

private theorem measurable_redInt_uncurry (hfm : Measurable f) :
    Measurable (fun q : (Fin n → ℝ) × ℝ ↦ redInt k h b f p ρ q.1 q.2) := by
  have hS : MeasurableSet {q : (Fin n → ℝ) × ℝ | 0 < q.2 ∧ q.2 < chartA k p q.1 * b ^ aExp k p} :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd ((measurable_chartA.comp measurable_fst).mul_const _))
  have hins : Measurable (fun q : (Fin n → ℝ) × ℝ ↦
      p.insertNth (α := fun _ ↦ ℝ) (xOf k p q.2 q.1) q.1) := by
    have := (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) p).symm.measurable.comp
      ((measurable_xOf_uncurry (k := k) (p := p)).prodMk measurable_fst)
    exact this
  have hG : Measurable (fun q : (Fin n → ℝ) × ℝ ↦
      ENNReal.ofReal ((q.2 / chartA k p q.1) ^ (lamP k h p - ρ) * chartA k p q.1 ^ (-ρ) /
          aExp k p) *
        (ENNReal.ofReal (f (p.insertNth (xOf k p q.2 q.1) q.1)) *
          ∏ j, ENNReal.ofReal (q.1 j ^ (h (p.succAbove j))))) := by
    refine ((((measurable_snd.div (measurable_chartA.comp measurable_fst)).pow_const _).mul
      ((measurable_chartA.comp measurable_fst).pow_const _)).div_const _).ennreal_ofReal.mul
      ((hfm.comp hins).ennreal_ofReal.mul ?_)
    exact Finset.measurable_prod _ fun j _ ↦
      ((measurable_pi_apply j).comp measurable_fst).pow_const _ |>.ennreal_ofReal
  convert hG.indicator hS using 1
  funext q
  simp only [redInt, Set.indicator_apply, Set.mem_Ioo, Set.mem_ofPred_eq]

/-- Membership of the solved point `(x(t, y), y)` in the box. -/
private theorem insertNth_mem_box {y : Fin n → ℝ} {x : ℝ} (hy : y ∈ Icc 0 fun _ ↦ b) (hx0 : 0 ≤ x)
    (hxb : x ≤ b) : p.insertNth (α := fun _ ↦ ℝ) x y ∈ Icc 0 fun _ ↦ b := by
  rw [← Set.pi_univ_Icc] at hy ⊢
  simp only [Set.mem_pi, Set.mem_univ, true_implies] at hy ⊢
  rw [Fin.forall_iff_succAbove p]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  exact ⟨⟨hx0, hxb⟩, hy⟩

private theorem xOf_le {y : Fin n → ℝ} {t : ℝ} (hb : 0 < b) (hy : ∀ j, 0 < y j) (ha : 0 < aExp k p)
    (ht : 0 ≤ t) (htA : t < chartA k p y * b ^ aExp k p) : xOf k p t y ≤ b := by
  unfold xOf
  have hA := chartA_pos (k := k) (p := p) hy
  calc (t / chartA k p y) ^ (1 / aExp k p)
      ≤ (b ^ aExp k p) ^ (1 / aExp k p) :=
        Real.rpow_le_rpow (div_nonneg ht hA.le) (by rw [div_le_iff₀ hA]; linarith)
          (by positivity)
    _ = b := by rw [one_div, Real.rpow_rpow_inv hb.le ha.ne']


end Reduced

section PerChart

variable {n : ℕ} (k h : Fin (n + 1) → ℕ) (b : ℝ) (f : (Fin (n + 1) → ℝ) → ℝ) (p : Fin (n + 1))

/-- The weight with the solved coordinate frozen at `0`. -/
@[expose] noncomputable def frozenWt (u : Fin (n + 1) → ℝ) : ℝ := f (Function.update u p 0)

variable {k h b f p}

private theorem frozenWt_insertNth (x : ℝ) (y : Fin n → ℝ) :
    frozenWt f p (p.insertNth x y) = f (p.insertNth 0 y) := by
  unfold frozenWt
  rw [Fin.update_insertNth]

theorem update_mem_box {u : Fin (n + 1) → ℝ} (hu : u ∈ Icc 0 fun _ ↦ b) (hb : 0 ≤ b) :
    Function.update u p 0 ∈ Icc 0 fun _ ↦ b := by
  rw [← Set.pi_univ_Icc] at hu ⊢
  simp only [Set.mem_pi, Set.mem_univ, true_implies] at hu ⊢
  intro q
  by_cases hq : q = p
  · subst hq; simp [hb]
  · rw [Function.update_of_ne hq]; exact hu q

theorem measurable_frozenWt (hfm : Measurable f) : Measurable (frozenWt f p) :=
  hfm.comp measurable_update_left

/-- The frozen weight inherits the summed Lipschitz bound. -/
private theorem frozenWt_lipschitz {L : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ u ∈ Icc 0 (fun _ ↦ b), ∀ u' ∈ Icc 0 (fun _ ↦ b),
      |f u - f u'| ≤ L * ∑ q, |u q - u' q|) (hb : 0 ≤ b) :
    ∀ u ∈ Icc 0 (fun _ ↦ b), ∀ u' ∈ Icc 0 (fun _ ↦ b),
      |frozenWt f p u - frozenWt f p u'| ≤ L * ∑ q, |u q - u' q| := by
  intro u hu u' hu'
  refine (hfL _ (update_mem_box hu hb) _ (update_mem_box hu' hb)).trans
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun q _ ↦ ?_) hL)
  by_cases hq : q = p
  · subst hq; simp
  · rw [Function.update_of_ne hq, Function.update_of_ne hq]

/-- The Lipschitz bound along the solved coordinate: `|f(x, y) − f(0, y)| ≤ L x`. -/
private theorem abs_sub_frozen_le {L : ℝ}
    (hfL : ∀ u ∈ Icc 0 (fun _ ↦ b), ∀ u' ∈ Icc 0 (fun _ ↦ b),
      |f u - f u'| ≤ L * ∑ q, |u q - u' q|) {x : ℝ} {y : Fin n → ℝ} (hy : y ∈ Icc 0 fun _ ↦ b)
    (hx0 : 0 ≤ x) (hxb : x ≤ b) :
    |f (p.insertNth x y) - f (p.insertNth 0 y)| ≤ L * x := by
  have h := hfL _ (insertNth_mem_box (p := p) hy hx0 hxb) _
    (insertNth_mem_box (p := p) hy le_rfl (hx0.trans hxb))
  have hsum : ∑ q, |(p.insertNth (α := fun _ ↦ ℝ) x y) q - (p.insertNth (α := fun _ ↦ ℝ) 0 y) q|
      = x := by
    rw [Fin.sum_univ_succAbove _ p]
    simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove, sub_self, abs_zero,
      Finset.sum_const_zero, add_zero, sub_zero, abs_of_nonneg hx0]
  rwa [hsum] at h

/-- The reduced integrand of the frozen weight at `ρ = λ_p` does not depend on `t` inside the
indicator. -/
private theorem redInt_frozen (y : Fin n → ℝ) (t : ℝ) :
    redInt k h b (frozenWt f p) p (lamP k h p) y t =
      (Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)).indicator (fun _ ↦
        ENNReal.ofReal (chartA k p y ^ (-(lamP k h p)) / aExp k p) *
          (ENNReal.ofReal (f (p.insertNth 0 y)) *
            ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j))))) t := by
  unfold redInt
  by_cases hmem : t ∈ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, sub_self, Real.rpow_zero, one_mul,
      frozenWt_insertNth]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-- **The reduced density of the frozen weight is antitone on `(0, ∞)`.** -/
theorem redDens_frozen_antitone {s t : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    redDens k h b (frozenWt f p) p (lamP k h p) t ≤
      redDens k h b (frozenWt f p) p (lamP k h p) s := by
  unfold redDens
  refine lintegral_mono fun y ↦ ?_
  rw [redInt_frozen, redInt_frozen]
  by_cases hmem : t ∈ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem
      (show s ∈ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p) from ⟨hs, lt_of_le_of_lt hst hmem.2⟩)]
  · rw [Set.indicator_of_notMem hmem]
    exact bot_le

/-- The density of the weight `u ↦ u_p` is the density of the chart with `h_p + 1`. -/
theorem sliceDens_coord_eq (t : ℝ) :
    sliceDens k h b (fun u ↦ u p) p t =
      sliceDens k (Function.update h p (h p + 1)) b (fun _ ↦ 1) p t := by
  unfold sliceDens
  refine lintegral_congr fun y ↦ ?_
  unfold sliceInt
  by_cases hmem : t ∈ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    have hx0 : 0 ≤ xOf k p t y := by
      unfold xOf
      exact Real.rpow_nonneg (div_nonneg hmem.1.le
        (Finset.prod_nonneg fun j _ ↦ (even_two_mul _).pow_nonneg _)) _
    have hprod : ∀ j, Function.update h p (h p + 1) (p.succAbove j) = h (p.succAbove j) :=
      fun j ↦ Function.update_of_ne (Fin.succAbove_ne p j) _ _
    simp only [Fin.insertNth_apply_same, Function.update_self, hprod, pow_succ,
      ENNReal.ofReal_mul (pow_nonneg hx0 _), ENNReal.ofReal_one, mul_one]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]


/-- The perturbation inequalities `G_f ≤ G_{f₀} + L G_g` and `G_{f₀} ≤ G_f + L G_g` for the
reduced densities, `g(u) = u_p`. -/
private theorem redDens_perturb (hb : 0 < b) (hkp : 0 < k p) (hfm : Measurable f)
    (hf0 : ∀ u, 0 ≤ f u)
    {L : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ u ∈ Icc 0 (fun _ ↦ b), ∀ u' ∈ Icc 0 (fun _ ↦ b),
      |f u - f u'| ≤ L * ∑ q, |u q - u' q|) (t : ℝ) :
    redDens k h b f p (lamP k h p) t ≤ redDens k h b (frozenWt f p) p (lamP k h p) t +
        ENNReal.ofReal L * redDens k h b (fun u ↦ u p) p (lamP k h p) t ∧
      redDens k h b (frozenWt f p) p (lamP k h p) t ≤ redDens k h b f p (lamP k h p) t +
        ENNReal.ofReal L * redDens k h b (fun u ↦ u p) p (lamP k h p) t := by
  have ha := aExp_pos (k := k) hkp
  have hpt : ∀ᵐ y ∂(volume.restrict (Icc 0 fun _ ↦ b)),
      redInt k h b f p (lamP k h p) y t ≤ redInt k h b (frozenWt f p) p (lamP k h p) y t +
          ENNReal.ofReal L * redInt k h b (fun u ↦ u p) p (lamP k h p) y t ∧
        redInt k h b (frozenWt f p) p (lamP k h p) y t ≤ redInt k h b f p (lamP k h p) y t +
          ENNReal.ofReal L * redInt k h b (fun u ↦ u p) p (lamP k h p) y t := by
    filter_upwards [ae_pos_box (n := n) (b := b), ae_restrict_mem measurableSet_Icc]
      with y hy hyb
    unfold redInt
    by_cases hmem : t ∈ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p)
    · simp only [Set.indicator_of_mem hmem, frozenWt_insertNth, Fin.insertNth_apply_same]
      have hA := chartA_pos (k := k) (p := p) hy
      have hx0 : 0 ≤ xOf k p t y := Real.rpow_nonneg (div_nonneg hmem.1.le hA.le) _
      have hxb := xOf_le hb hy ha hmem.1.le hmem.2
      have hlip := abs_sub_frozen_le (p := p) hfL hyb hx0 hxb
      rw [abs_le] at hlip
      set X := ENNReal.ofReal ((t / chartA k p y) ^ (lamP k h p - lamP k h p) *
        chartA k p y ^ (-lamP k h p) / aExp k p)
      set P := ∏ j, ENNReal.ofReal (y j ^ (h (p.succAbove j)))
      have h1 : ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) ≤
          ENNReal.ofReal (f (p.insertNth 0 y)) +
            ENNReal.ofReal L * ENNReal.ofReal (xOf k p t y) := by
        rw [← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_add (hf0 _) (mul_nonneg hL hx0)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hlip.2])
      have h2 : ENNReal.ofReal (f (p.insertNth 0 y)) ≤
          ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) +
            ENNReal.ofReal L * ENNReal.ofReal (xOf k p t y) := by
        rw [← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_add (hf0 _) (mul_nonneg hL hx0)]
        exact ENNReal.ofReal_le_ofReal (by linarith [hlip.1])
      constructor
      · calc X * (ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) * P)
            ≤ X * ((ENNReal.ofReal (f (p.insertNth 0 y)) +
                ENNReal.ofReal L * ENNReal.ofReal (xOf k p t y)) * P) :=
              mul_le_mul' le_rfl (mul_le_mul' h1 le_rfl)
          _ = X * (ENNReal.ofReal (f (p.insertNth 0 y)) * P) +
              ENNReal.ofReal L * (X * (ENNReal.ofReal (xOf k p t y) * P)) := by ring
      · calc X * (ENNReal.ofReal (f (p.insertNth 0 y)) * P)
            ≤ X * ((ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) +
                ENNReal.ofReal L * ENNReal.ofReal (xOf k p t y)) * P) :=
              mul_le_mul' le_rfl (mul_le_mul' h2 le_rfl)
          _ = X * (ENNReal.ofReal (f (p.insertNth (xOf k p t y) y)) * P) +
              ENNReal.ofReal L * (X * (ENNReal.ofReal (xOf k p t y) * P)) := by ring
    · simp only [Set.indicator_of_notMem hmem, mul_zero, add_zero, le_refl, and_self]
  have hm0 : Measurable fun y ↦ redInt k h b (frozenWt f p) p (lamP k h p) y t :=
    (measurable_redInt_uncurry (ρ := lamP k h p) (measurable_frozenWt hfm)).of_uncurry_right
  have hmf : Measurable fun y ↦ redInt k h b f p (lamP k h p) y t :=
    (measurable_redInt_uncurry (ρ := lamP k h p) hfm).of_uncurry_right
  have hmg : Measurable fun y ↦ redInt k h b (fun u ↦ u p) p (lamP k h p) y t :=
    (measurable_redInt_uncurry (ρ := lamP k h p) (measurable_pi_apply p)).of_uncurry_right
  unfold redDens
  constructor
  · calc ∫⁻ y in Icc 0 (fun _ ↦ b), redInt k h b f p (lamP k h p) y t
        ≤ ∫⁻ y in Icc 0 (fun _ ↦ b), (redInt k h b (frozenWt f p) p (lamP k h p) y t +
            ENNReal.ofReal L * redInt k h b (fun u ↦ u p) p (lamP k h p) y t) :=
          lintegral_mono_ae (hpt.mono fun y hy ↦ hy.1)
      _ = _ := by
          rw [lintegral_add_left hm0, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  · calc ∫⁻ y in Icc 0 (fun _ ↦ b), redInt k h b (frozenWt f p) p (lamP k h p) y t
        ≤ ∫⁻ y in Icc 0 (fun _ ↦ b), (redInt k h b f p (lamP k h p) y t +
            ENNReal.ofReal L * redInt k h b (fun u ↦ u p) p (lamP k h p) y t) :=
          lintegral_mono_ae (hpt.mono fun y hy ↦ hy.2)
      _ = _ := by
          rw [lintegral_add_left hmf, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]


/-- Freezing the solved coordinate perturbs the density by at most its coordinate-weight density. -/
theorem sliceDens_perturb (hb : 0 < b) (hkp : 0 < k p) (hfm : Measurable f)
    (hf0 : ∀ u, 0 ≤ f u) {L : ℝ} (hL : 0 ≤ L)
    (hfL : ∀ u ∈ Icc 0 (fun _ ↦ b), ∀ u' ∈ Icc 0 (fun _ ↦ b),
      |f u - f u'| ≤ L * ∑ q, |u q - u' q|) {t : ℝ} (ht : 0 < t) :
    sliceDens k h b f p t ≤ sliceDens k h b (frozenWt f p) p t +
        ENNReal.ofReal L * sliceDens k h b (fun u ↦ u p) p t ∧
      sliceDens k h b (frozenWt f p) p t ≤ sliceDens k h b f p t +
        ENNReal.ofReal L * sliceDens k h b (fun u ↦ u p) p t := by
  have hh := redDens_perturb (h := h) hb hkp hfm hf0 hL hfL t
  have ha := aExp_pos hkp
  rw [sliceDens_eq_redDens (ρ := lamP k h p) ht ha,
    sliceDens_eq_redDens (ρ := lamP k h p) ht ha,
    sliceDens_eq_redDens (ρ := lamP k h p) ht ha]
  constructor
  · calc _ ≤ ENNReal.ofReal (t ^ (lamP k h p - 1)) *
        (redDens k h b (frozenWt f p) p (lamP k h p) t +
          ENNReal.ofReal L * redDens k h b (fun u ↦ u p) p (lamP k h p) t) :=
        mul_le_mul' le_rfl hh.1
      _ = _ := by ring
  · calc _ ≤ ENNReal.ofReal (t ^ (lamP k h p - 1)) *
        (redDens k h b f p (lamP k h p) t +
          ENNReal.ofReal L * redDens k h b (fun u ↦ u p) p (lamP k h p) t) :=
        mul_le_mul' le_rfl hh.2
      _ = _ := by ring

end PerChart

end SingularLearningTheory.SliceDensity
