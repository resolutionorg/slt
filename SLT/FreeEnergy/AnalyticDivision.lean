/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Analytic.Composition

/-!
# Analytic division by coordinate monomials

The analytic core of [Hit26, Lemma 5.2.3] ([Wat09,
Theorem 6.1]), in a corrected form: a Banach-space-valued real analytic map
`A` near `0 ∈ ℝ^d` with `‖T (A u)‖ ≤ C u^k` on a small open positive cube (`T` a continuous
injective linear map) factors as `A u = u^k • G u` with `G` analytic near `0`.

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 5.2.3], analytic divisibility (one coordinate) | |
| | `AnalyticAt.analyticAt_factor_coordinate` |
| the identity theorem, from the positive cube (used for `K ∘ g = u^{2k}` and the mean identity) | |
| | `AnalyticAt.eventually_eq_zero_of_ocube` |
| the low coefficients vanish (one coordinate; identity theorem in the parameters) | |
| | `analyticAt_vanish_hyperplane_of_bound` |
| [Hit26, Lemma 5.2.3], analytic divisibility (monomial) | |
| | `AnalyticAt.analyticAt_factor_monomial_of_bound` |

Division by one coordinate `u_j` uses a
telescoping series. With `P_j x = x − x_j e_j` and `A` with power series `p` at `0`,
`p_{n+1}(x, …, x) − p_{n+1}(P_j x, …, P_j x) = x_j • q_n(x, …, x)` where
`q_n = Σ_ℓ p_{n+1}(P_j ·, …, P_j ·, e_j, ·, …, ·)` (`e_j` in position `ℓ`),
`‖q_n‖ ≤ (n+1) ‖p_{n+1}‖`,
so `q` has positive radius and `A x − A (P_j x) = x_j • q.sum x`. No monomial-coefficient API is
needed. The vanishing of `A` on `{x_j = 0}` follows from the bound along `u_j ↓ 0` at positive
parameters and the identity theorem in the parameter variables.
-/

public section

open Filter Topology

namespace SingularLearningTheory

/-- The open cube `(0, b)^m`; it differs from `cube m b` by a null set. -/
abbrev ocube (m : ℕ) (b : ℝ) : Set (Fin m → ℝ) := Set.pi Set.univ fun _ ↦ Set.Ioo 0 b

namespace AnalyticDivision

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `j`-th coordinate vector `e_j`. -/
private noncomputable abbrev coordVec (j : Fin d) : Fin d → ℝ := Pi.single j 1

/-- The projection `P_j x = x − x_j e_j` killing the `j`-th coordinate. -/
@[expose] noncomputable def coordProj (j : Fin d) : (Fin d → ℝ) →L[ℝ] (Fin d → ℝ) :=
  ContinuousLinearMap.id ℝ _ -
    (ContinuousLinearMap.single ℝ (fun _ : Fin d ↦ ℝ) j).comp (ContinuousLinearMap.proj j)

theorem coordProj_apply (j : Fin d) (x : Fin d → ℝ) (i : Fin d) :
    coordProj j x i = if i = j then 0 else x i := by
  simp only [coordProj, sub_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    ContinuousLinearMap.single_apply, Pi.sub_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem coordProj_apply_self (j : Fin d) (x : Fin d → ℝ) : coordProj j x j = 0 := by
  simp [coordProj_apply]

private theorem coordProj_add_smul (j : Fin d) (x : Fin d → ℝ) :
    coordProj j x + x j • coordVec j = x := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, coordProj_apply, coordVec, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · simp [h]

private theorem norm_coordProj_apply_le (j : Fin d) (x : Fin d → ℝ) : ‖coordProj j x‖ ≤ ‖x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr fun i ↦ ?_
  rw [coordProj_apply]
  split_ifs
  · simp
  · exact norm_le_pi_norm x i

private theorem norm_coordProj_le (j : Fin d) : ‖coordProj j‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ by
    rw [one_mul]; exact norm_coordProj_apply_le j x

private theorem norm_coordVec (j : Fin d) : ‖coordVec j‖ = 1 := by
  simp [coordVec, Pi.norm_single]

/-- The permutation of `Fin (n + 1)` sending `ℓ ↦ 0` and `ℓ.succAbove i ↦ i.succ`, so that
`Fin.cons y v ∘ shift ℓ = Fin.insertNth ℓ y v`. -/
private def shift {n : ℕ} (ℓ : Fin (n + 1)) : Fin (n + 1) ≃ Fin (n + 1) :=
  (finSuccEquiv' ℓ).trans (finSuccEquiv n).symm

private theorem cons_comp_shift {n : ℕ} (ℓ : Fin (n + 1)) (y : Fin d → ℝ) (v : Fin n → Fin d → ℝ) :
    (Fin.cons y v : Fin (n + 1) → Fin d → ℝ) ∘ shift ℓ = Fin.insertNth ℓ y v := by
  funext i
  simp only [Function.comp, shift, Equiv.trans_apply]
  refine Fin.succAboveCases ℓ ?_ (fun k ↦ ?_) i
  · simp
  · simp [finSuccEquiv'_succAbove]

/-! ### The quotient series -/

/-- The `ℓ`-th summand of the `n`-th coefficient of the quotient series:
`(v_1, …, v_n) ↦ p_{n+1}(P_j v_1, …, P_j v_ℓ, e_j, v_{ℓ+1}, …, v_n)`. -/
private noncomputable def quotTerm (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E) (j : Fin d) (n : ℕ)
    (ℓ : Fin (n + 1)) : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ Fin d → ℝ) E :=
  (((p (n + 1)).domDomCongr (shift ℓ)).curryLeft (coordVec j)).compContinuousLinearMap
    fun i ↦ if (i : ℕ) < ℓ then coordProj j else ContinuousLinearMap.id ℝ _

private theorem quotTerm_apply (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E) (j : Fin d) (n : ℕ)
    (ℓ : Fin (n + 1)) (v : Fin n → Fin d → ℝ) :
    quotTerm p j n ℓ v = p (n + 1)
      (Fin.insertNth ℓ (coordVec j) fun i ↦ if (i : ℕ) < ℓ then coordProj j (v i) else v i) := by
  simp only [quotTerm, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.curryLeft_apply, ContinuousMultilinearMap.domDomCongr_apply]
  rw [← cons_comp_shift]
  congr 1
  funext i
  simp only [Function.comp]
  congr 1
  funext i'
  split_ifs <;> rfl

private theorem norm_quotTerm_le (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E) (j : Fin d) (n : ℕ)
    (ℓ : Fin (n + 1)) : ‖quotTerm p j n ℓ‖ ≤ ‖p (n + 1)‖ := by
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hg : ‖((p (n + 1)).domDomCongr (shift ℓ)).curryLeft (coordVec j)‖ ≤ ‖p (n + 1)‖ := by
    calc ‖((p (n + 1)).domDomCongr (shift ℓ)).curryLeft (coordVec j)‖
        ≤ ‖((p (n + 1)).domDomCongr (shift ℓ)).curryLeft‖ * ‖coordVec j‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖p (n + 1)‖ := by
          rw [ContinuousMultilinearMap.curryLeft_norm, ContinuousMultilinearMap.norm_domDomCongr,
            norm_coordVec, mul_one]
  have hL : ∏ i : Fin n,
      ‖(if (i : ℕ) < ℓ then coordProj j else ContinuousLinearMap.id ℝ (Fin d → ℝ))‖ ≤ 1 := by
    refine Finset.prod_le_one₀ (fun _ _ ↦ norm_nonneg _) fun i _ ↦ ?_
    split_ifs
    · exact norm_coordProj_le j
    · exact ContinuousLinearMap.norm_id_le
  calc _ ≤ ‖p (n + 1)‖ * 1 := mul_le_mul hg hL (by positivity) (norm_nonneg _)
    _ = _ := mul_one _

/-- The telescoping identity
`p_{n+1}(x, …, x) − p_{n+1}(P_j x, …, P_j x) = x_j • Σ_ℓ q_{n,ℓ}(x, …, x)`. -/
private theorem sub_apply_diag_eq (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E) (j : Fin d) (n : ℕ)
    (x : Fin d → ℝ) :
    p (n + 1) (fun _ ↦ x) - p (n + 1) (fun _ ↦ coordProj j x)
      = x j • ∑ ℓ : Fin (n + 1), quotTerm p j n ℓ (fun _ ↦ x) := by
  set w : ℕ → Fin (n + 1) → Fin d → ℝ := fun ℓ i ↦ if (i : ℕ) < ℓ then coordProj j x else x
    with hw
  have h0 : w 0 = fun _ ↦ x := by funext i; simp [hw]
  have hN : w (n + 1) = fun _ ↦ coordProj j x := by funext i; simp [hw, i.isLt]
  have hstep : ∀ ℓ : Fin (n + 1),
      p (n + 1) (w ℓ) - p (n + 1) (w (ℓ + 1)) = x j • quotTerm p j n ℓ (fun _ ↦ x) := by
    intro ℓ
    rw [quotTerm_apply]
    have hupd : w ℓ = Function.update (w (ℓ + 1)) ℓ x := by
      funext i
      by_cases hi : i = ℓ
      · subst hi; simp [hw]
      · rw [Function.update_of_ne hi]
        have : (i : ℕ) < ℓ ↔ (i : ℕ) < ℓ + 1 := by
          have := Fin.val_ne_of_ne hi
          omega
        simp only [hw, this]
    have hupd' : w (ℓ + 1) = Function.update (w (ℓ + 1)) ℓ (coordProj j x) := by
      funext i
      by_cases hi : i = ℓ
      · subst hi; simp [hw]
      · rw [Function.update_of_ne hi]
    have hins : Function.update (w (ℓ + 1)) ℓ (coordVec j)
        = Fin.insertNth ℓ (coordVec j) fun i ↦ if (i : ℕ) < ℓ then coordProj j x else x := by
      funext i
      refine Fin.succAboveCases ℓ ?_ (fun m ↦ ?_) i
      · simp
      · rw [Function.update_of_ne (Fin.succAbove_ne ℓ m), Fin.insertNth_apply_succAbove]
        simp only [hw]
        have : ((ℓ.succAbove m : Fin (n + 1)) : ℕ) < ℓ + 1 ↔ (m : ℕ) < ℓ := by
          unfold Fin.succAbove
          split_ifs with h
          · rw [Fin.lt_def, Fin.val_castSucc] at h
            simp only [Fin.val_castSucc]
            omega
          · rw [Fin.lt_def, Fin.val_castSucc, not_lt] at h
            simp only [Fin.val_succ]
            omega
        simp only [this]
    have key : p (n + 1) (Function.update (w (ℓ + 1)) ℓ x)
        = p (n + 1) (Function.update (w (ℓ + 1)) ℓ (coordProj j x)) +
          x j • p (n + 1) (Function.update (w (ℓ + 1)) ℓ (coordVec j)) := by
      have := (p (n + 1)).map_update_add (w (ℓ + 1)) ℓ (coordProj j x) (x j • coordVec j)
      rw [coordProj_add_smul, ContinuousMultilinearMap.map_update_smul] at this
      exact this
    rw [hupd, key, ← hupd', hins]
    abel
  have hsum : ∑ ℓ : Fin (n + 1), (p (n + 1) (w ℓ) - p (n + 1) (w (ℓ + 1)))
      = p (n + 1) (w 0) - p (n + 1) (w (n + 1)) := by
    rw [Fin.sum_univ_eq_sum_range (fun ℓ ↦ p (n + 1) (w ℓ) - p (n + 1) (w (ℓ + 1))) (n + 1)]
    exact Finset.sum_range_sub' (fun ℓ ↦ p (n + 1) (w ℓ)) (n + 1)
  rw [← h0, ← hN, ← hsum, Finset.smul_sum]
  exact Finset.sum_congr rfl fun ℓ _ ↦ hstep ℓ

/-- The quotient series `q_n = Σ_ℓ q_{n,ℓ}`. -/
private noncomputable def quotSeries (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E) (j : Fin d) :
    FormalMultilinearSeries ℝ (Fin d → ℝ) E :=
  fun n ↦ ∑ ℓ : Fin (n + 1), quotTerm p j n ℓ

private theorem norm_quotSeries_le (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E) (j : Fin d)
    (n : ℕ) :
    ‖quotSeries p j n‖ ≤ (n + 1) * ‖p (n + 1)‖ := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ ℓ : Fin (n + 1), ‖quotTerm p j n ℓ‖ ≤ ∑ _ℓ : Fin (n + 1), ‖p (n + 1)‖ :=
        Finset.sum_le_sum fun ℓ _ ↦ norm_quotTerm_le p j n ℓ
    _ = (n + 1) * ‖p (n + 1)‖ := by simp

private theorem sub_apply_diag_eq_quotSeries (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E)
    (j : Fin d)
    (n : ℕ) (x : Fin d → ℝ) :
    p (n + 1) (fun _ ↦ x) - p (n + 1) (fun _ ↦ coordProj j x)
      = x j • quotSeries p j n (fun _ ↦ x) := by
  rw [sub_apply_diag_eq, quotSeries, sum_apply]

private theorem radius_quotSeries_pos (p : FormalMultilinearSeries ℝ (Fin d → ℝ) E) (j : Fin d)
    (hp : 0 < p.radius) : 0 < (quotSeries p j).radius := by
  obtain ⟨r', hr'0, hr'⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  obtain ⟨C, hC0, hC⟩ := p.norm_mul_pow_le_of_lt_radius hr'
  have hr'0' : (0 : NNReal) < r' := by exact_mod_cast hr'0
  have hr'pos : (0 : ℝ) < r' := hr'0'
  refine lt_of_lt_of_le ?_ ((quotSeries p j).le_radius_of_bound (2 * C / r') (r := r' / 2)
    fun n ↦ ?_)
  · exact_mod_cast half_pos hr'0'
  · have h1 := norm_quotSeries_le p j n
    have h2 := hC (n + 1)
    have h3 : ((n : ℝ) + 1) ≤ 2 ^ n := by exact_mod_cast Nat.lt_two_pow_self
    have hpn : 0 ≤ ‖p (n + 1)‖ := norm_nonneg _
    have h4 : 0 < (2 : ℝ) ^ n := by positivity
    calc ‖quotSeries p j n‖ * ((r' / 2 : NNReal) : ℝ) ^ n
        ≤ (n + 1) * ‖p (n + 1)‖ * ((r' : ℝ) / 2) ^ n := by
          push_cast; gcongr
      _ = ((n + 1) / 2 ^ n) * (‖p (n + 1)‖ * (r' : ℝ) ^ (n + 1)) / r' := by
          rw [div_pow, pow_succ]; field_simp
      _ ≤ 1 * C / r' := by
          gcongr
          exact (div_le_one h4).mpr h3
      _ ≤ 2 * C / r' := by gcongr; linarith

/-- Analytic division by one coordinate: an analytic `A` vanishing on `{x_j = 0}` near `0`
is `x_j • G x` with `G` analytic at `0`. -/
theorem _root_.AnalyticAt.analyticAt_factor_coordinate [CompleteSpace E] {A : (Fin d → ℝ) → E}
    (hA : AnalyticAt ℝ A 0) (j : Fin d) (hvan : ∀ᶠ x in 𝓝 0, x j = 0 → A x = 0) :
    ∃ G : (Fin d → ℝ) → E, AnalyticAt ℝ G 0 ∧ ∀ᶠ x in 𝓝 0, A x = x j • G x := by
  obtain ⟨p, R, hp⟩ := hA
  have hrad : 0 < p.radius := lt_of_lt_of_le hp.r_pos hp.r_le
  have hq := radius_quotSeries_pos p j hrad
  refine ⟨(quotSeries p j).sum, ((quotSeries p j).hasFPowerSeriesOnBall hq).analyticAt, ?_⟩
  obtain ⟨ε, hε, hvan'⟩ := Metric.eventually_nhds_iff.mp hvan
  have h1 : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x ∈ Metric.eball (0 : Fin d → ℝ) R :=
    Metric.eball_mem_nhds 0 hp.r_pos
  have h2 : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), x ∈ Metric.eball (0 : Fin d → ℝ) (quotSeries p j).radius :=
    Metric.eball_mem_nhds 0 hq
  have h3 : ∀ᶠ x in 𝓝 (0 : Fin d → ℝ), dist x 0 < ε := Metric.ball_mem_nhds 0 hε
  filter_upwards [h1, h2, h3] with x hxR hxq hxε
  have hPx : coordProj j x ∈ Metric.eball (0 : Fin d → ℝ) R := by
    rw [Metric.mem_eball, edist_zero_right] at hxR ⊢
    rw [← ofReal_norm] at hxR ⊢
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (norm_coordProj_apply_le j x)) hxR
  have hAx := hp.hasSum hxR
  have hAPx := hp.hasSum hPx
  have hGx := ((quotSeries p j).hasFPowerSeriesOnBall hq).hasSum hxq
  simp only [zero_add] at hAx hAPx hGx
  have hAPx0 : A (coordProj j x) = 0 := by
    refine hvan' ?_ (coordProj_apply_self j x)
    rw [dist_zero_right] at hxε ⊢
    exact lt_of_le_of_lt (norm_coordProj_apply_le j x) hxε
  have hdiff := hAx.sub hAPx
  rw [← hasSum_nat_add_iff' 1] at hdiff
  have h0 : p 0 (fun _ ↦ x) - p 0 (fun _ ↦ coordProj j x) = 0 := by
    rw [sub_eq_zero]
    congr 1
    funext i
    exact i.elim0
  simp only [Finset.sum_range_one, h0, sub_zero] at hdiff
  have hdiff' : HasSum (fun n ↦ x j • quotSeries p j n (fun _ ↦ x)) (A x - A (coordProj j x)) := by
    refine hdiff.congr_fun fun n ↦ ?_
    rw [sub_apply_diag_eq_quotSeries]
  rw [hAPx0, sub_zero] at hdiff'
  exact hdiff'.unique (hGx.const_smul (x j))

/-! ### Vanishing on a hyperplane from a one-sided bound -/

private theorem isOpen_ocube (ε : ℝ) : IsOpen (ocube d ε) :=
  isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_Ioo

theorem norm_lt_of_mem_ocube {ε : ℝ} {x : Fin d → ℝ} (hε : 0 < ε) (hx : x ∈ ocube d ε) :
    ‖x‖ < ε := by
  refine (pi_norm_lt_iff hε).mpr fun i ↦ ?_
  obtain ⟨h0, h1⟩ := hx i (Set.mem_univ i)
  rw [Real.norm_eq_abs, abs_of_pos h0]
  exact h1

/-- The identity theorem in the form used throughout: an analytic map vanishing on the open
positive cube `(0, ε)^d` vanishes near `0`. -/
theorem _root_.AnalyticAt.eventually_eq_zero_of_ocube [CompleteSpace E] {B : (Fin d → ℝ) → E}
    (hB : AnalyticAt ℝ B 0) {ε : ℝ} (hε : 0 < ε) (hvan : ∀ u ∈ ocube d ε, B u = 0) :
    ∀ᶠ x in 𝓝 0, B x = 0 := by
  obtain ⟨δ, hδ, hBδ⟩ := Metric.eventually_nhds_iff.mp hB.eventually_analyticAt
  have hBδ' : AnalyticOnNhd ℝ B (Metric.ball 0 δ) := fun y hy ↦ hBδ (by simpa using hy)
  set ε' := min ε δ with hε'_def
  have hε' : 0 < ε' := lt_min hε hδ
  have hz₀ : (fun _ ↦ ε' / 2 : Fin d → ℝ) ∈ ocube d ε' := fun i _ ↦ ⟨by positivity, by linarith⟩
  have hz₀δ : (fun _ ↦ ε' / 2 : Fin d → ℝ) ∈ Metric.ball (0 : Fin d → ℝ) δ := by
    rw [Metric.mem_ball, dist_zero_right]
    exact (norm_lt_of_mem_ocube hε' hz₀).trans_le (min_le_right _ _)
  have hEq : Set.EqOn B 0 (Metric.ball 0 δ) := by
    refine hBδ'.eqOn_zero_of_preconnected_of_eventuallyEq_zero (convex_ball 0 δ).isPreconnected
      hz₀δ ?_
    filter_upwards [(isOpen_ocube ε').mem_nhds hz₀] with v hv
    exact hvan v fun i hi ↦ ⟨(hv i hi).1, (hv i hi).2.trans_le (min_le_left _ _)⟩
  filter_upwards [Metric.ball_mem_nhds (0 : Fin d → ℝ) hδ] with x hx
  exact hEq hx

/-- If `‖T (A u)‖ ≤ C u^k` on a positive cube with `k_j > 0`, then `A` vanishes on `{x_j = 0}`
near `0`: letting `u_j ↓ 0` at positive parameters gives `T (A (0, v)) = 0`, hence
`A (0, v) = 0`, and the identity theorem in `v` extends this to all small `v`. -/
private theorem analyticAt_vanish_hyperplane_of_bound [CompleteSpace E] {L : Type*}
    [NormedAddCommGroup L] [NormedSpace ℝ L] {A : (Fin d → ℝ) → E} (hA : AnalyticAt ℝ A 0)
    (T : E →L[ℝ] L)
    (hT : Function.Injective T) {k : Fin d → ℕ} {j : Fin d} (hkj : 0 < k j) {C ε : ℝ}
    (hε : 0 < ε) (hbound : ∀ u ∈ ocube d ε, ‖T (A u)‖ ≤ C * ∏ i, u i ^ k i) :
    ∀ᶠ x in 𝓝 0, x j = 0 → A x = 0 := by
  obtain ⟨δ, hδ, hAδ⟩ := Metric.eventually_nhds_iff.mp hA.eventually_analyticAt
  have hAδ' : AnalyticOnNhd ℝ A (Metric.ball 0 δ) := fun y hy ↦ hAδ (by simpa using hy)
  set ε' := min ε δ with hε'_def
  have hε' : 0 < ε' := lt_min hε hδ
  have hPball : ∀ x ∈ Metric.ball (0 : Fin d → ℝ) δ,
      coordProj j x ∈ Metric.ball (0 : Fin d → ℝ) δ := by
    intro x hx
    rw [Metric.mem_ball, dist_zero_right] at hx ⊢
    exact lt_of_le_of_lt (norm_coordProj_apply_le j x) hx
  have hB : AnalyticOnNhd ℝ (fun x ↦ A (coordProj j x)) (Metric.ball 0 δ) := fun x hx ↦
    (hAδ' _ (hPball x hx)).comp ((coordProj j).analyticAt x)
  -- `A (P_j v) = 0` for `v` in the small positive cube
  have hvan : ∀ v ∈ ocube d ε', A (coordProj j v) = 0 := by
    intro v hv
    have hvδ : v ∈ Metric.ball (0 : Fin d → ℝ) δ := by
      rw [Metric.mem_ball, dist_zero_right]
      exact (norm_lt_of_mem_ocube hε' hv).trans_le (min_le_right _ _)
    have hcont : ContinuousAt (fun t : ℝ ↦ T (A (coordProj j v + t • coordVec j))) 0 := by
      have h2 : ContinuousAt (fun t : ℝ ↦ coordProj j v + t • coordVec j) 0 :=
        (continuous_const.add (continuous_id.smul continuous_const)).continuousAt
      have h1 : ContinuousAt A (coordProj j v + (0 : ℝ) • coordVec j) := by
        rw [zero_smul, add_zero]
        exact (hAδ' _ (hPball v hvδ)).continuousAt
      exact T.continuous.continuousAt.comp
        (ContinuousAt.comp (f := fun t : ℝ ↦ coordProj j v + t • coordVec j) h1 h2)
    have hlim : Tendsto (fun t : ℝ ↦ T (A (coordProj j v + t • coordVec j))) (𝓝[>] 0)
        (𝓝 (T (A (coordProj j v)))) := by
      have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
      simpa using this
    -- the bound along `t ↓ 0`
    have hmemcube : ∀ᶠ t : ℝ in 𝓝[>] 0, coordProj j v + t • coordVec j ∈ ocube d ε := by
      have : ∀ᶠ t : ℝ in 𝓝[>] 0, t < ε :=
        eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds hε)
      filter_upwards [this, self_mem_nhdsWithin] with t ht ht0
      intro i _
      simp only [Pi.add_apply, Pi.smul_apply, coordProj_apply, coordVec, smul_eq_mul]
      by_cases hi : i = j
      · subst hi; simp only [ite_true, Pi.single_eq_same, mul_one, zero_add]
        exact ⟨ht0, ht⟩
      · simp only [hi, ite_false, Pi.single_eq_of_ne hi, mul_zero, add_zero]
        obtain ⟨h0, h1⟩ := hv i (Set.mem_univ i)
        exact ⟨h0, h1.trans_le (min_le_left _ _)⟩
    have hcoord : ∀ t : ℝ, ∀ i, (coordProj j v + t • coordVec j) i
        = if i = j then t else coordProj j v i := by
      intro t i
      simp only [Pi.add_apply, Pi.smul_apply, coordProj_apply, coordVec, smul_eq_mul]
      by_cases hi : i = j
      · subst hi; simp
      · simp [hi]
    have hprod : ∀ t : ℝ, ∏ i, (coordProj j v + t • coordVec j) i ^ k i
        = t ^ k j * ∏ i ∈ Finset.univ.erase j, coordProj j v i ^ k i := by
      intro t
      calc ∏ i, (coordProj j v + t • coordVec j) i ^ k i
          = ∏ i, (if i = j then t else coordProj j v i) ^ k i :=
            Finset.prod_congr rfl fun i _ ↦ by rw [hcoord t i]
        _ = t ^ k j * ∏ i ∈ Finset.univ.erase j, coordProj j v i ^ k i := by
            rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j), ite_eq_left rfl]
            congr 1
            exact Finset.prod_congr rfl fun i hi ↦ by rw [ite_eq_right (Finset.ne_of_mem_erase hi)]
    have hbnd : ∀ᶠ t : ℝ in 𝓝[>] 0, ‖T (A (coordProj j v + t • coordVec j))‖
        ≤ C * (t ^ k j * ∏ i ∈ Finset.univ.erase j, coordProj j v i ^ k i) := by
      filter_upwards [hmemcube] with t ht
      rw [← hprod]
      exact hbound _ ht
    have hto0 : Tendsto
        (fun t : ℝ ↦ C * (t ^ k j * ∏ i ∈ Finset.univ.erase j, coordProj j v i ^ k i))
        (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto
          (fun t : ℝ ↦ C * (t ^ k j * ∏ i ∈ Finset.univ.erase j, coordProj j v i ^ k i))
          (𝓝 0) (𝓝 (C * (0 ^ k j * ∏ i ∈ Finset.univ.erase j, coordProj j v i ^ k i))) :=
        (continuous_const.mul ((continuous_pow _).mul continuous_const)).tendsto 0
      rw [zero_pow hkj.ne', zero_mul, mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hnorm0 : Tendsto (fun t : ℝ ↦ ‖T (A (coordProj j v + t • coordVec j))‖) (𝓝[>] 0)
        (𝓝 0) :=
      tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hto0
        (Eventually.of_forall fun _ ↦ norm_nonneg _) hbnd
    have : ‖T (A (coordProj j v))‖ = 0 := tendsto_nhds_unique hlim.norm hnorm0
    exact hT (by rw [norm_eq_zero.mp this, map_zero])
  -- identity theorem in the parameters
  have hB0 : AnalyticAt ℝ (fun x ↦ A (coordProj j x)) 0 := hB 0 (Metric.mem_ball_self hδ)
  filter_upwards [AnalyticAt.eventually_eq_zero_of_ocube hB0 hε' hvan] with x hx hxj
  have hx' : coordProj j x = x := by
    conv_rhs => rw [← coordProj_add_smul j x]
    rw [hxj, zero_smul, add_zero]
  simpa [hx'] using hx

/-! ### Division by a monomial -/

theorem _root_.Finset.prod_pow_update_sub_one {k : Fin d → ℕ} {j : Fin d} (hkj : 0 < k j)
    (u : Fin d → ℝ) :
    ∏ i, u i ^ k i = u j * ∏ i, u i ^ Function.update k j (k j - 1) i := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.mul_prod_erase Finset.univ (fun i ↦ u i ^ Function.update k j (k j - 1) i)
      (Finset.mem_univ j), Function.update_self, ← mul_assoc, ← pow_succ',
    Nat.sub_add_cancel hkj]
  congr 1
  exact Finset.prod_congr rfl fun i hi ↦ by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

theorem _root_.Finset.sum_update_sub_one {k : Fin d → ℕ} {j : Fin d} (hkj : 0 < k j) :
    ∑ i, Function.update k j (k j - 1) i = (∑ i, k i) - 1 := by
  rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j),
    ← Finset.add_sum_erase Finset.univ k (Finset.mem_univ j), Function.update_self]
  rw [Finset.sum_congr rfl fun i hi ↦ Function.update_of_ne (Finset.ne_of_mem_erase hi) _ _]
  omega

/-- Analytic division by a monomial (the analytic core of [Hit26,
Lemma 5.2.3]): if `A` is analytic at `0` and `‖T (A u)‖ ≤
C u^k` on a positive cube, for a continuous injective linear `T`, then `A x = x^k • G x` near `0`
with `G` analytic at `0`. Induction on `|k|`, extracting one coordinate at a time with
`analyticAt_vanish_hyperplane_of_bound` and `AnalyticAt.analyticAt_factor_coordinate`. -/
theorem _root_.AnalyticAt.analyticAt_factor_monomial_of_bound [CompleteSpace E] {L : Type*}
    [NormedAddCommGroup L]
    [NormedSpace ℝ L] (T : E →L[ℝ] L) (hT : Function.Injective T) :
    ∀ (N : ℕ) (k : Fin d → ℕ), ∑ i, k i = N → ∀ {A : (Fin d → ℝ) → E}, AnalyticAt ℝ A 0 →
      ∀ {C ε : ℝ}, 0 < ε → (∀ u ∈ ocube d ε, ‖T (A u)‖ ≤ C * ∏ i, u i ^ k i) →
      ∃ G : (Fin d → ℝ) → E, AnalyticAt ℝ G 0 ∧ ∀ᶠ x in 𝓝 0, A x = (∏ i, x i ^ k i) • G x := by
  intro N
  induction N with
  | zero =>
    intro k hk A hA C ε hε _
    have hk0 : ∀ i, k i = 0 := fun i ↦ by
      have := Finset.sum_eq_zero_iff.mp hk i (Finset.mem_univ i)
      exact this
    refine ⟨A, hA, Eventually.of_forall fun x ↦ ?_⟩
    simp [hk0]
  | succ N ih =>
    intro k hk A hA C ε hε hbound
    obtain ⟨j, hj⟩ : ∃ j, 0 < k j := by
      by_contra h
      push Not at h
      have : ∑ i, k i = 0 := Finset.sum_eq_zero fun i _ ↦ Nat.le_zero.mp (h i)
      omega
    obtain ⟨B, hB, hAB⟩ := AnalyticAt.analyticAt_factor_coordinate hA j
      (analyticAt_vanish_hyperplane_of_bound hA T hT hj hε hbound)
    obtain ⟨δ, hδ, hAB'⟩ := Metric.eventually_nhds_iff.mp hAB
    set ε' := min ε δ with hε'_def
    have hε' : 0 < ε' := lt_min hε hδ
    have hboundB : ∀ u ∈ ocube d ε',
        ‖T (B u)‖ ≤ C * ∏ i, u i ^ Function.update k j (k j - 1) i := by
      intro u hu
      have huε : u ∈ ocube d ε := fun i hi ↦
        ⟨(hu i hi).1, (hu i hi).2.trans_le (min_le_left _ _)⟩
      have huδ : dist u 0 < δ := by
        rw [dist_zero_right]
        exact (norm_lt_of_mem_ocube hε' hu).trans_le (min_le_right _ _)
      have huj : 0 < u j := (hu j (Set.mem_univ j)).1
      have h1 := hbound u huε
      rw [hAB' huδ, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos huj,
        Finset.prod_pow_update_sub_one hj, ← mul_assoc, mul_comm C, mul_assoc] at h1
      exact le_of_mul_le_mul_left h1 huj
    obtain ⟨G, hG, hBG⟩ := ih (Function.update k j (k j - 1))
      (by rw [Finset.sum_update_sub_one hj, hk]; rfl) hB hε' hboundB
    refine ⟨G, hG, ?_⟩
    filter_upwards [hAB, hBG] with x hx1 hx2
    rw [hx1, hx2, smul_smul, ← Finset.prod_pow_update_sub_one hj]

end AnalyticDivision

end SingularLearningTheory
