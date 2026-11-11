/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.AnalyticDivision
public import Mathlib.Analysis.Analytic.Constructions

/-!
# Factorisation of analytic functions along a monomial ([Wat09, Theorem 2.7])

| Thesis | Lean |
| --- | --- |
| [Hit26, Theorem 3.3.1], from one function to | |
| several ([Wat09, Theorem 2.8] via [Wat09, Theorem 2.7]) | `AnalyticAt.exists_unit_factorization`,
|
| | `exists_unit_factorization_pi` |

[Wat09, §2.5]: if `f₁ f₂ = S x^k` near `0` with `S ≠ 0`, then `f_i = a_i x^{k^i}` with `a_i`
analytic nonvanishing near `0` and `k¹ + k² = k`. The proof is by induction on `|k|`: on the
hyperplane `{x_j = 0}` (`k_j ≥ 1`) the product vanishes, so one factor vanishes there (analytic
functions on a connected set form an integral domain), that factor is divisible by `x_j`
(`AnalyticAt.analyticAt_factor_coordinate`), and `x_j` is cancelled. All statements are germs at
`0`.
-/

public section

namespace AnalyticAt

open SingularLearningTheory

open Filter Topology Set AnalyticDivision

variable {d : ℕ}

/-- Analytic germs form an integral domain: if `f₁ f₂ = 0` near `x`, one factor vanishes
near `x`. No thesis counterpart; used by `exists_unit_factorization`. -/
theorem eventuallyEq_zero_or_of_mul {f₁ f₂ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (h₁ : AnalyticAt ℝ f₁ x) (h₂ : AnalyticAt ℝ f₂ x)
    (h : (fun y ↦ f₁ y * f₂ y) =ᶠ[𝓝 x] 0) : f₁ =ᶠ[𝓝 x] 0 ∨ f₂ =ᶠ[𝓝 x] 0 := by
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp
    (h.and (h₁.eventually_analyticAt.and h₂.eventually_analyticAt))
  have hB : IsPreconnected (Metric.ball x r) := (convex_ball x r).isPreconnected
  have h₁B : AnalyticOnNhd ℝ f₁ (Metric.ball x r) := fun y hy ↦ (hball (by simpa using hy)).2.1
  have h₂B : AnalyticOnNhd ℝ f₂ (Metric.ball x r) := fun y hy ↦ (hball (by simpa using hy)).2.2
  by_cases hz : ∀ y ∈ Metric.ball x r, f₁ y = 0
  · exact Or.inl ((Metric.eventually_nhds_iff.mpr ⟨r, hr, fun y hy ↦ hz y (by simpa using hy)⟩))
  push Not at hz
  obtain ⟨y, hy, hfy⟩ := hz
  right
  -- near `y`, `f₁ ≠ 0`, so `f₂ = 0`; the identity theorem spreads this over the ball
  have hne : ∀ᶠ z in 𝓝 y, f₁ z ≠ 0 := (h₁B y hy).continuousAt.eventually_ne hfy
  have hy' : ∀ᶠ z in 𝓝 y, z ∈ Metric.ball x r := Metric.isOpen_ball.mem_nhds hy
  have hf₂y : f₂ =ᶠ[𝓝 y] 0 := by
    filter_upwards [hne, hy'] with z hz hzB
    have := (hball (by simpa using hzB)).1
    simp only [Pi.zero_apply] at this ⊢
    exact (mul_eq_zero.mp this).resolve_left hz
  have hzero : EqOn f₂ 0 (Metric.ball x r) :=
    h₂B.eqOn_zero_of_preconnected_of_eventuallyEq_zero hB hy hf₂y
  exact Metric.eventually_nhds_iff.mpr ⟨r, hr, fun z hz ↦ hzero (by simpa using hz)⟩

/-- The hyperplane version: if `f₁ f₂ = 0` on `{x_j = 0}` near `0`, one factor vanishes on
`{x_j = 0}` near `0` (pull back along the coordinate projection `coordProj j`, which is linear,
so `f ∘ coordProj j` is analytic). No thesis counterpart. -/
private theorem eventually_eq_zero_on_hyperplane_or {f₁ f₂ : (Fin d → ℝ) → ℝ}
    (h₁ : AnalyticAt ℝ f₁ 0) (h₂ : AnalyticAt ℝ f₂ 0) (j : Fin d)
    (h : ∀ᶠ x in 𝓝 0, x j = 0 → f₁ x * f₂ x = 0) :
    (∀ᶠ x in 𝓝 0, x j = 0 → f₁ x = 0) ∨ ∀ᶠ x in 𝓝 0, x j = 0 → f₂ x = 0 := by
  have hproj : coordProj j (0 : Fin d → ℝ) = 0 := map_zero _
  have hfix : ∀ x : Fin d → ℝ, x j = 0 → coordProj j x = x := fun x hx ↦ by
    funext i
    rw [coordProj_apply]
    split_ifs with hi
    · rw [hi, hx]
    · rfl
  have hg₁ : AnalyticAt ℝ (f₁ ∘ coordProj j) 0 := by
    rw [← hproj] at h₁
    exact h₁.comp ((coordProj j).analyticAt 0)
  have hg₂ : AnalyticAt ℝ (f₂ ∘ coordProj j) 0 := by
    rw [← hproj] at h₂
    exact h₂.comp ((coordProj j).analyticAt 0)
  have hprod : (fun y ↦ (f₁ ∘ coordProj j) y * (f₂ ∘ coordProj j) y) =ᶠ[𝓝 0] 0 := by
    have hc : Tendsto (coordProj j) (𝓝 0) (𝓝 0) := by
      simpa [hproj] using (coordProj j).continuous.tendsto 0
    filter_upwards [hc.eventually h] with x hx
    exact hx (coordProj_apply_self j x)
  rcases hg₁.eventuallyEq_zero_or_of_mul hg₂ hprod with hz | hz
  · left
    filter_upwards [hz] with x hx hxj
    rw [← hfix x hxj]
    exact hx
  · right
    filter_upwards [hz] with x hx hxj
    rw [← hfix x hxj]
    exact hx

/-- [Wat09, Theorem 2.7] ([Hit26, Theorem 3.3.1], the
step from the resolution of a product to the factors): if `f₁ f₂ = a x^k` near `0` with `a`
analytic, then `f_i = a_i x^{k^i}` near `0` with `a_i` analytic, `a₁ a₂ = a` (so both nonvanishing
where `a` is) and `k¹ + k² = k`. The [Wat09] has a constant `a = S ≠ 0`; the analytic unit is what
the induction over several factors (`exists_unit_factorization_pi`) needs. -/
theorem exists_unit_factorization {f₁ f₂ : (Fin d → ℝ) → ℝ} (h₁ : AnalyticAt ℝ f₁ 0)
    (h₂ : AnalyticAt ℝ f₂ 0) {a : (Fin d → ℝ) → ℝ} (ha : AnalyticAt ℝ a 0) {k : Fin d → ℕ}
    (h : ∀ᶠ x in 𝓝 0, f₁ x * f₂ x = a x * ∏ i, x i ^ k i) :
    ∃ (k₁ k₂ : Fin d → ℕ) (a₁ a₂ : (Fin d → ℝ) → ℝ), k₁ + k₂ = k ∧
      AnalyticAt ℝ a₁ 0 ∧ AnalyticAt ℝ a₂ 0 ∧ (∀ᶠ x in 𝓝 0, a₁ x * a₂ x = a x) ∧
      (∀ᶠ x in 𝓝 0, f₁ x = a₁ x * ∏ i, x i ^ k₁ i) ∧
      ∀ᶠ x in 𝓝 0, f₂ x = a₂ x * ∏ i, x i ^ k₂ i := by
  suffices H : ∀ (N : ℕ) (k : Fin d → ℕ), ∑ i, k i = N → ∀ {f₁ f₂ : (Fin d → ℝ) → ℝ},
      AnalyticAt ℝ f₁ 0 → AnalyticAt ℝ f₂ 0 →
      (∀ᶠ x in 𝓝 0, f₁ x * f₂ x = a x * ∏ i, x i ^ k i) →
      ∃ (k₁ k₂ : Fin d → ℕ) (a₁ a₂ : (Fin d → ℝ) → ℝ), k₁ + k₂ = k ∧
        AnalyticAt ℝ a₁ 0 ∧ AnalyticAt ℝ a₂ 0 ∧ (∀ᶠ x in 𝓝 0, a₁ x * a₂ x = a x) ∧
        (∀ᶠ x in 𝓝 0, f₁ x = a₁ x * ∏ i, x i ^ k₁ i) ∧
        ∀ᶠ x in 𝓝 0, f₂ x = a₂ x * ∏ i, x i ^ k₂ i from
    H _ k rfl h₁ h₂ h
  intro N
  induction N with
  | zero =>
    intro k hk f₁ f₂ h₁ h₂ h
    have hk0 : k = 0 := funext fun i ↦ Finset.sum_eq_zero_iff.mp hk i (Finset.mem_univ i)
    subst hk0
    refine ⟨0, 0, f₁, f₂, by simp, h₁, h₂, ?_, ?_, ?_⟩
    · filter_upwards [h] with x hx
      simpa using hx
    · exact Eventually.of_forall fun x ↦ by simp
    · exact Eventually.of_forall fun x ↦ by simp
  | succ N ih =>
    intro k hk f₁ f₂ h₁ h₂ h
    obtain ⟨j, hj⟩ : ∃ j, 0 < k j := by
      by_contra hc
      push Not at hc
      have : ∑ i, k i = 0 := Finset.sum_eq_zero fun i _ ↦ Nat.le_zero.mp (hc i)
      omega
    have hk' : ∑ i, Function.update k j (k j - 1) i = N := by
      rw [Finset.sum_update_sub_one hj, hk]
      rfl
    -- the product vanishes on the hyperplane `{x_j = 0}`
    have hvan : ∀ᶠ x in 𝓝 0, x j = 0 → f₁ x * f₂ x = 0 := by
      filter_upwards [h] with x hx hxj
      rw [hx, Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hxj]; exact zero_pow hj.ne'),
        mul_zero]
    -- cancelling `x_j`: if `f = x_j • G` and `f * f' = S x^k` near `0`, then `G * f' = S x^{k'}`
    have cancel : ∀ {f f' G : (Fin d → ℝ) → ℝ}, AnalyticAt ℝ G 0 → AnalyticAt ℝ f' 0 →
        (∀ᶠ x in 𝓝 0, f x = x j • G x) → (∀ᶠ x in 𝓝 0, f x * f' x = a x * ∏ i, x i ^ k i) →
        ∀ᶠ x in 𝓝 0, G x * f' x = a x * ∏ i, x i ^ Function.update k j (k j - 1) i := by
      intro f f' G hG hf' hfG hff'
      set k' := Function.update k j (k j - 1) with hk'_def
      have hmon : AnalyticAt ℝ (fun x : Fin d → ℝ ↦ a x * ∏ i, x i ^ k' i) 0 :=
        ha.mul (Finset.analyticAt_fun_prod _ fun i _ ↦
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) i).analyticAt _).pow _)
      -- the difference `D` is analytic near `0` and vanishes where `x_j ≠ 0`
      have hD : AnalyticAt ℝ (fun x ↦ G x * f' x - a x * ∏ i, x i ^ k' i) 0 :=
        (hG.mul hf').sub hmon
      have hDzero : ∀ᶠ x in 𝓝 0, x j ≠ 0 → G x * f' x - a x * ∏ i, x i ^ k' i = 0 := by
        filter_upwards [hfG, hff'] with x hx1 hx2 hxj
        have hx3 : x j * (G x * f' x) = x j * (a x * ∏ i, x i ^ k' i) := by
          calc x j * (G x * f' x) = f x * f' x := by rw [hx1, smul_eq_mul]; ring
            _ = a x * ∏ i, x i ^ k i := hx2
            _ = x j * (a x * ∏ i, x i ^ k' i) := by
              rw [hk'_def, Finset.prod_pow_update_sub_one hj x]; ring
        rw [sub_eq_zero]
        exact mul_left_cancel₀ hxj hx3
      -- so it vanishes near a point with `x_j ≠ 0`, hence on a whole ball by the identity theorem
      obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp (hD.eventually_analyticAt.and hDzero)
      have hB : IsPreconnected (Metric.ball (0 : Fin d → ℝ) r) := (convex_ball _ r).isPreconnected
      set z₀ : Fin d → ℝ := Pi.single j (r / 2) with hz₀
      have hz₀B : z₀ ∈ Metric.ball (0 : Fin d → ℝ) r := by
        rw [Metric.mem_ball, dist_zero_right, hz₀, Pi.norm_single, Real.norm_eq_abs,
          abs_of_pos (half_pos hr)]
        linarith
      have hz₀j : z₀ j ≠ 0 := by
        rw [hz₀, Pi.single_eq_same]
        exact (half_pos hr).ne'
      have hDz₀ : (fun x ↦ G x * f' x - a x * ∏ i, x i ^ k' i) =ᶠ[𝓝 z₀] 0 := by
        have hne : ∀ᶠ x in 𝓝 z₀, x j ≠ 0 :=
          ((continuous_apply j).tendsto z₀).eventually_ne hz₀j
        filter_upwards [hne, Metric.isOpen_ball.mem_nhds hz₀B] with x hx hxB
        exact (hball (by simpa using hxB)).2 hx
      have hEq : EqOn (fun x ↦ G x * f' x - a x * ∏ i, x i ^ k' i) 0 (Metric.ball 0 r) :=
        AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          (fun y hy ↦ (hball (by simpa using hy)).1) hB hz₀B hDz₀
      filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) hr] with x hx
      exact sub_eq_zero.mp (hEq hx)
    rcases eventually_eq_zero_on_hyperplane_or h₁ h₂ j hvan with hv | hv
    · obtain ⟨G, hG, hfG⟩ := analyticAt_factor_coordinate h₁ j hv
      obtain ⟨k₁, k₂, a₁, a₂, hsum, ha₁, ha₂, hprod, hG1, hf2⟩ :=
        ih _ hk' hG h₂ (cancel hG h₂ hfG h)
      refine ⟨Function.update k₁ j (k₁ j + 1), k₂, a₁, a₂, ?_, ha₁, ha₂, hprod, ?_, hf2⟩
      · funext i
        have := congrFun hsum i
        simp only [Pi.add_apply] at this ⊢
        by_cases hi : i = j
        · subst hi
          simp only [Function.update_self] at this ⊢
          omega
        · simp only [Function.update_of_ne hi] at this ⊢
          exact this
      · filter_upwards [hfG, hG1] with x hx1 hx2
        have hupd : ∏ i, x i ^ Function.update k₁ j (k₁ j + 1) i = x j * ∏ i, x i ^ k₁ i := by
          rw [Finset.prod_pow_update_sub_one (k := Function.update k₁ j (k₁ j + 1)) (j := j)
            (by simp) x]
          simp only [Function.update_self, Nat.add_sub_cancel, Function.update_idem,
            Function.update_eq_self]
        rw [hupd, hx1, hx2, smul_eq_mul]
        ring
    · obtain ⟨G, hG, hfG⟩ := analyticAt_factor_coordinate h₂ j hv
      have h' : ∀ᶠ x in 𝓝 0, f₂ x * f₁ x = a x * ∏ i, x i ^ k i := by
        filter_upwards [h] with x hx
        rw [mul_comm]
        exact hx
      obtain ⟨k₂, k₁, a₂, a₁, hsum, ha₂, ha₁, hprod, hG2, hf1⟩ :=
        ih _ hk' hG h₁ (cancel hG h₁ hfG h')
      refine ⟨k₁, Function.update k₂ j (k₂ j + 1), a₁, a₂, ?_, ha₁, ha₂, ?_, hf1, ?_⟩
      · funext i
        have := congrFun hsum i
        simp only [Pi.add_apply] at this ⊢
        by_cases hi : i = j
        · subst hi
          simp only [Function.update_self] at this ⊢
          omega
        · simp only [Function.update_of_ne hi] at this ⊢
          omega
      · filter_upwards [hprod] with x hx
        rw [mul_comm]
        exact hx
      · filter_upwards [hfG, hG2] with x hx1 hx2
        have hupd : ∏ i, x i ^ Function.update k₂ j (k₂ j + 1) i = x j * ∏ i, x i ^ k₂ i := by
          rw [Finset.prod_pow_update_sub_one (k := Function.update k₂ j (k₂ j + 1)) (j := j)
            (by simp) x]
          simp only [Function.update_self, Nat.add_sub_cancel, Function.update_idem,
            Function.update_eq_self]
        rw [hupd, hx1, hx2, smul_eq_mul]
        ring

/-- [Wat09, Theorem 2.8]'s algebra: a finite product of analytic functions equal to `a x^k` near
`0`, `a` analytic, splits into analytic factors `a_i x^{K_i}` with `∑ K_i = k` and `∏ a_i = a`. -/
theorem _root_.exists_unit_factorization_pi {n : ℕ} {F : Fin n → (Fin d → ℝ) → ℝ}
    (hF : ∀ i, AnalyticAt ℝ (F i) 0) {a : (Fin d → ℝ) → ℝ} (ha : AnalyticAt ℝ a 0)
    {k : Fin d → ℕ} (h : ∀ᶠ x in 𝓝 0, ∏ i, F i x = a x * ∏ j, x j ^ k j) :
    ∃ (K : Fin n → Fin d → ℕ) (b : Fin n → (Fin d → ℝ) → ℝ), (∑ i, K i) = k ∧
      (∀ i, AnalyticAt ℝ (b i) 0) ∧ (∀ᶠ x in 𝓝 0, ∏ i, b i x = a x) ∧
      ∀ i, ∀ᶠ x in 𝓝 0, F i x = b i x * ∏ j, x j ^ K i j := by
  induction n generalizing a k with
  | zero =>
    -- the empty product is `1`, so `k = 0` and `a = 1` near `0`
    have hk : k = 0 := by
      by_contra hne
      obtain ⟨j, hj⟩ : ∃ j, 0 < k j := by
        by_contra hc
        push Not at hc
        exact hne (funext fun j ↦ Nat.le_zero.mp (hc j))
      have h0 := h.self_of_nhds
      simp only [Finset.univ_eq_empty, Finset.prod_empty, Pi.zero_apply] at h0
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (zero_pow hj.ne'), mul_zero] at h0
      exact one_ne_zero h0
    subst hk
    refine ⟨fun i ↦ i.elim0, fun i ↦ i.elim0, by simp, fun i ↦ i.elim0, ?_, fun i ↦ i.elim0⟩
    filter_upwards [h] with x hx
    simpa using hx
  | succ n ih =>
    have hprod : ∀ x, ∏ i, F i x = F 0 x * ∏ i : Fin n, F i.succ x := fun x ↦
      Fin.prod_univ_succ fun i ↦ F i x
    have h₂ : AnalyticAt ℝ (fun x ↦ ∏ i : Fin n, F i.succ x) 0 :=
      Finset.analyticAt_fun_prod _ fun i _ ↦ hF i.succ
    obtain ⟨k₁, k₂, a₁, a₂, hsum, ha₁, ha₂, hprod₁₂, hF0, hrest⟩ :=
      exists_unit_factorization (hF 0) h₂ ha (by simpa only [hprod] using h)
    obtain ⟨K', b', hK', hb', hprodb', hF'⟩ := ih (fun i ↦ hF i.succ) ha₂ hrest
    refine ⟨Fin.cons k₁ K', Fin.cons a₁ b', ?_, ?_, ?_, ?_⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hK', hsum]
    · intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simpa using ha₁
      · simpa using hb' i
    · filter_upwards [hprod₁₂, hprodb'] with x hx1 hx2
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hx2, hx1]
    · intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simpa using hF0
      · simpa using hF' i

end AnalyticAt
