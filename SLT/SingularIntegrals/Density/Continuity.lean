/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.Density.Reduced
public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Continuity of the monomial slice density

Positive monomial level sets have zero volume unless the monomial is constant.
Below the constant chart threshold this makes the moving slice boundary negligible,
so dominated convergence gives continuity of the slice density.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.SliceDensity
open SingularLearningTheory.MellinAnalysis

/-- A nonconstant monomial on a positive cube has no atoms in its level distribution. -/
private theorem ae_monomial_ne {d : ℕ} {k : Fin d → ℕ} {b : ℝ}
    (hb : 0 < b) (hk : ∃ j, 0 < k j) (t : ℝ) :
    ∀ᵐ u ∂(volume.restrict (Icc 0 fun _ ↦ b)), (∏ j, u j ^ (2 * k j)) ≠ t := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := by
    obtain ⟨j, _⟩ := hk
    exact ⟨d - 1, by have := j.isLt; omega⟩
  obtain ⟨p, hp⟩ := hk
  have heq := map_monomial_eq_withDensity_sliceDens (k := k) (h := fun _ ↦ 0)
    (f := fun _ ↦ 1) hb hp measurable_const
  simp only [ENNReal.ofReal_one, pow_zero, Finset.prod_const_one, mul_one,
    withDensity_const, one_smul] at heq
  have h := congrArg (fun μ : Measure ℝ ↦ μ {t}) heq
  rw [Measure.map_apply measurable_monomial (measurableSet_singleton t), measure_singleton] at h
  rw [ae_iff]
  convert h using 2
  ext u
  simp only [Set.mem_ofPred_eq, not_not, Set.mem_preimage, Set.mem_singleton_iff]

/-- The moving slice endpoint avoids a fixed level almost everywhere below `b^(2kₚ)`. -/
private theorem ae_chartA_mul_ne {n : ℕ} {k : Fin (n + 1) → ℕ} {b t : ℝ} {p : Fin (n + 1)}
    (hb : 0 < b) (ht : t < b ^ aExp k p) :
    ∀ᵐ y ∂(volume.restrict (Icc 0 fun _ ↦ b)), t ≠ chartA k p y * b ^ aExp k p := by
  by_cases hk : ∃ j, 0 < k (p.succAbove j)
  · filter_upwards [ae_monomial_ne hb hk (t / b ^ aExp k p)] with y hy
    intro heq
    apply hy
    exact (div_eq_iff (Real.rpow_pos_of_pos hb _).ne').mpr heq |>.symm
  · have hk0 : ∀ j, k (p.succAbove j) = 0 := by simpa using hk
    filter_upwards [] with y
    simpa [chartA, hk0] using ht.ne

/-- Integrating a continuous kernel over a moving interval preserves continuity when its
boundary has zero measure. -/
private theorem continuousAt_lintegral_indicator {d : ℕ} {S : Set (Fin d → ℝ)}
    (hS : IsCompact S) {A : (Fin d → ℝ) → ℝ} (hA : Continuous A)
    {F : ℝ × (Fin d → ℝ) → ℝ} (hF : Continuous F) {t : ℝ} (ht : 0 < t)
    (hne : ∀ᵐ y ∂(volume.restrict S), t ≠ A y) :
    ContinuousAt (fun s ↦ ∫⁻ y in S,
      (Ioo (0 : ℝ) (A y)).indicator (fun s ↦ ENNReal.ofReal (F (s, y))) s) t := by
  obtain ⟨M, hM⟩ := (show IsCompact (Icc (t - 1) (t + 1) ×ˢ S) from
    isCompact_Icc.prod hS).exists_bound_of_continuousOn hF.continuousOn
  have hneigh : Ioo (t - 1) (t + 1) ∈ 𝓝 t := Ioo_mem_nhds (by linarith) (by linarith)
  apply tendsto_lintegral_filter_of_dominated_convergence (fun _ ↦ ENNReal.ofReal M)
  · filter_upwards [] with s
    have hset : MeasurableSet {y | 0 < s ∧ s < A y} := by measurability
    have hm : Measurable (fun y ↦ ENNReal.ofReal (F (s, y))) := by fun_prop
    convert hm.indicator hset using 1
    funext y
    simp only [Set.indicator_apply, Set.mem_Ioo, Set.mem_ofPred_eq]
  · filter_upwards [hneigh] with s hs
    filter_upwards [ae_restrict_mem hS.measurableSet] with y hy
    by_cases hx : s ∈ Ioo (0 : ℝ) (A y)
    · rw [Set.indicator_of_mem hx]
      exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
        (by simpa only [Real.norm_eq_abs] using hM (s, y) ⟨⟨hs.1.le, hs.2.le⟩, hy⟩))
    · simp only [Set.indicator_of_notMem hx]; exact zero_le
  · simp only [lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (by simpa only [Measure.restrict_apply_univ] using hS.measure_ne_top (μ := volume))
  · filter_upwards [hne] with y hy
    by_cases hty : t < A y
    · have he : ∀ᶠ s in 𝓝 t, s ∈ Ioo (0 : ℝ) (A y) := Ioo_mem_nhds ht hty
      rw [Set.indicator_of_mem (show t ∈ Ioo (0 : ℝ) (A y) from ⟨ht, hty⟩)]
      have hc : Continuous (fun s ↦ ENNReal.ofReal (F (s, y))) :=
        ENNReal.continuous_ofReal.comp (hF.comp (continuous_id.prodMk continuous_const))
      exact hc.continuousAt.tendsto.congr' (he.mono fun s hs ↦
        (Set.indicator_of_mem hs _).symm)
    · have he : ∀ᶠ s in 𝓝 t, A y < s := Ioi_mem_nhds (lt_of_le_of_ne (not_lt.mp hty) hy.symm)
      have heq : ∀ᶠ s in 𝓝 t,
          (Ioo (0 : ℝ) (A y)).indicator (fun s ↦ ENNReal.ofReal (F (s, y))) s = 0 :=
        he.mono fun s hs ↦ Set.indicator_of_notMem (fun hx ↦ (not_lt.mpr hs.le) hx.2) _
      simpa only [Set.indicator_of_notMem (show t ∉ Ioo (0 : ℝ) (A y) from fun hx ↦ hty hx.2)]
        using tendsto_const_nhds.congr' (heq.mono fun _ h ↦ h.symm)

/-- A continuous kernel on a compact slice has finite integral. -/
private theorem lintegral_indicator_ne_top {d : ℕ} {S : Set (Fin d → ℝ)}
    (hS : IsCompact S) (A : (Fin d → ℝ) → ℝ)
    {F : ℝ × (Fin d → ℝ) → ℝ} (hF : Continuous F) (t : ℝ) :
    (∫⁻ y in S, (Ioo (0 : ℝ) (A y)).indicator
      (fun t ↦ ENNReal.ofReal (F (t, y))) t) ≠ ⊤ := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn
    (hF.comp (continuous_const.prodMk continuous_id)).continuousOn
  apply ne_top_of_le_ne_top (b := ENNReal.ofReal M * volume S)
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_ne_top)
  rw [← Measure.restrict_apply_univ S, ← lintegral_const]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hS.measurableSet] with y hy
  by_cases hx : t ∈ Ioo (0 : ℝ) (A y)
  · rw [Set.indicator_of_mem hx]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs, Function.comp_apply, id_eq] using hM y hy))
  · simp only [Set.indicator_of_notMem hx]; exact zero_le

/-- The slice density is continuous and finite below the solved-coordinate threshold. -/
theorem continuousAt_sliceDens {n : ℕ} {k h : Fin (n + 1) → ℕ} {b t : ℝ}
    {f : (Fin (n + 1) → ℝ) → ℝ} {p : Fin (n + 1)}
    (hb : 0 < b) (hp : 0 < k p) (hf : Continuous f)
    (ht : 0 < t) (htb : t < b ^ aExp k p) :
    ContinuousAt (sliceDens k h b f p) t ∧ sliceDens k h b f p t ≠ ⊤ := by
  let a := aExp k p
  have ha : 0 < a := aExp_pos hp
  let T : ℝ → ℝ := fun s ↦ max s (t / 2)
  let B : (Fin n → ℝ) → ℝ := fun y ↦ max (chartA k p y) (t / (2 * b ^ a))
  have hT : ∀ s, 0 < T s := fun s ↦ lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hB : ∀ y, 0 < B y := fun y ↦ lt_of_lt_of_le (by positivity) (le_max_right _ _)
  have hcT : Continuous T := continuous_id.max continuous_const
  have hcA : Continuous (chartA k p) := continuous_finsetProd _ fun j _ ↦
    (continuous_apply j).pow _
  have hcB : Continuous B := hcA.max continuous_const
  let x : ℝ × (Fin n → ℝ) → ℝ := fun z ↦ (T z.1 / B z.2) ^ (1 / a)
  have hcx : Continuous x := ((hcT.comp continuous_fst).div
    (hcB.comp continuous_snd) (fun _ ↦ (hB _).ne')).rpow_const
      (fun z ↦ Or.inl (div_pos (hT z.1) (hB z.2)).ne')
  let F : ℝ × (Fin n → ℝ) → ℝ := fun z ↦
    T z.1 ^ (1 / a - 1) / (a * B z.2 ^ (1 / a)) *
      (x z ^ h p * max (f (p.insertNth (x z) z.2)) 0 *
        ∏ j, max (z.2 j ^ h (p.succAbove j)) 0)
  have hF : Continuous F := by
    have hi : Continuous (fun z : ℝ × (Fin n → ℝ) ↦
        p.insertNth (α := fun _ ↦ ℝ) (x z) z.2) := by
      fun_prop
    exact (((hcT.comp continuous_fst).rpow_const (fun z ↦ Or.inl (hT z.1).ne')).div
      (continuous_const.mul ((hcB.comp continuous_snd).rpow_const
        (fun z ↦ Or.inl (hB z.2).ne')))
      (fun z ↦ (mul_pos ha (Real.rpow_pos_of_pos (hB z.2) _)).ne')).mul
      (((hcx.pow _).mul ((hf.comp hi).max continuous_const)).mul
        (continuous_finsetProd _ fun j _ ↦
          (((continuous_apply j).comp continuous_snd).pow _).max continuous_const))
  let D : ℝ → ℝ≥0∞ := fun s ↦ ∫⁻ y in Icc 0 (fun _ ↦ b),
    (Ioo (0 : ℝ) (chartA k p y * b ^ a)).indicator (fun s ↦ ENNReal.ofReal (F (s, y))) s
  have hEq : ∀ s, t / 2 < s → sliceDens k h b f p s = D s := by
    intro s hs
    apply lintegral_congr_ae
    filter_upwards [ae_pos_box (n := n) (b := b)] with y hy
    by_cases hm : s ∈ Ioo (0 : ℝ) (chartA k p y * b ^ a)
    · have hBA : t / (2 * b ^ a) ≤ chartA k p y := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hm.2]
      have hxe : x (s, y) = xOf k p s y := by
        simp only [x, T, B, max_eq_left hs.le, max_eq_left hBA, xOf, a]
      have hfac : 0 ≤ s ^ (1 / a - 1) / (a * chartA k p y ^ (1 / a)) := by
        exact (div_pos (Real.rpow_pos_of_pos hm.1 _) (mul_pos ha
          (Real.rpow_pos_of_pos (chartA_pos hy) _))).le
      have hm' : s ∈ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p) := hm
      simp only [sliceInt, Set.indicator_of_mem hm, Set.indicator_of_mem hm', F, T, B,
        max_eq_left hs.le, max_eq_left hBA, hxe]
      have hx0 : 0 ≤ xOf k p s y := Real.rpow_nonneg
        (div_pos hm.1 (chartA_pos hy)).le _
      rw [ENNReal.ofReal_mul hfac,
        ENNReal.ofReal_mul (mul_nonneg (pow_nonneg hx0 (h p)) (le_max_right _ _)),
        ENNReal.ofReal_mul (pow_nonneg hx0 (h p))]
      simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (zero_le : (0 : ℝ≥0∞) ≤ _),
        ENNReal.ofReal_prod_of_nonneg (fun j _ ↦ le_max_right _ _)]
      rfl
    · have hm' : s ∉ Ioo (0 : ℝ) (chartA k p y * b ^ aExp k p) := hm
      simp only [sliceInt, Set.indicator_of_notMem hm, Set.indicator_of_notMem hm']
  have hEt : sliceDens k h b f p t = D t := hEq t (by linarith)
  have hEA : sliceDens k h b f p =ᶠ[𝓝 t] D := by
    filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith)] with s hs using hEq s hs
  have hcD : ContinuousAt D t := continuousAt_lintegral_indicator
    isCompact_Icc (hcA.mul continuous_const) hF ht (ae_chartA_mul_ne hb htb)
  exact ⟨hcD.congr hEA.symm, hEt ▸ lintegral_indicator_ne_top isCompact_Icc _ hF t⟩

end SingularLearningTheory.SliceDensity
