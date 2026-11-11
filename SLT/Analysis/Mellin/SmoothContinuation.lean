/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.Analysis.Mellin.Remainder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Meromorphic.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# [Wat09, Theorem 6.6] — the chart zeta function of a smooth amplitude continues meromorphically

For a chart `[0,b]^d` with monomial data `k h` and a `C^∞` amplitude `g` the chart zeta function
`remainderZeta k h b g z = ∫_{[0,b]^d} u^{2kz+h} g(u) du` converges on `Re(2kₚz + hₚ) > −1`.
The book pushes the continuation left by Taylor-expanding `g`; for `d ≥ 2` a single remainder
bounded by `C ∏ uₚ^{nₚ}` with all `nₚ` large does not exist (`g(u) = u₁^N` has the mixed terms
`u₁^j u₂^N r(u₂)`), so this file uses **integration by parts one coordinate at a time**:

`∫ u^{s} g = (bₚ^{sₚ}/(sₚ+1)) ∫ u^{s'} g(u[p := bₚ]) − (1/(sₚ+1)) ∫ u^{s+eₚ} ∂ₚg`

(`s' = s` with `sₚ := 0`, both new amplitudes again `C^∞`), which lowers the convergence
threshold of coordinate `p` by one at the cost of the pole candidate `−(hₚ+1)/(2kₚ)`.  Iterating
along a shift vector `r : Fin d → ℕ` (induction on `∑ₚ rₚ`) gives, for every `r`, a function `F`
equal to the chart zeta function on its convergence region, holomorphic at every `z₀` with
`Re(2kₚz₀ + hₚ) + rₚ > −1` off the candidates `−(hₚ + j + 1)/(2kₚ)`, `j < rₚ`, and meromorphic
on that half-plane (`exists_continuation_remainderZeta`).

Ingredients: the slicing of the box integral along one coordinate (`setIntegral_box_insertNth`,
via `MeasurableEquiv.piFinSuccAbove`), the one-variable integration by parts on `[0, bₚ]` with
`x^{s+1}/(s+1)` vanishing at `0` (`integral_cpow_mul_ibp`), and the chart identity
`remainderZeta_ibp`.

The proof integrates by parts one coordinate at a time.
-/

public section

open MeasureTheory Set Finset Complex Filter
open scoped ENNReal

namespace SingularLearningTheory.MellinAnalysis

/-- The smooth order `C^∞` as an element of `WithTop ℕ∞`. -/
local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Slicing

variable {n : ℕ}

/-- The preimage of the box under the coordinate splitting `u ↦ (uₚ, u ∘ succAbove p)` is a
product of boxes. -/
theorem _root_.preimage_box_piFinSuccAbove (b : Fin (n + 1) → ℝ) (p : Fin (n + 1)) :
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) p).symm ⁻¹' Icc 0 b =
      Icc 0 (b p) ×ˢ Icc 0 (b ∘ p.succAbove) := by
  exact ((Fin.insertNthOrderIso (fun _ ↦ ℝ) p).preimage_Icc _ _).trans (Icc_prod_eq _ _)

/-- Slicing the box integral along coordinate `p`:
`∫_{[0,b]} Φ = ∫_{y} ∫_{x ∈ [0,bₚ]} Φ(insert x y)`. -/
private theorem setIntegral_box_insertNth (b : Fin (n + 1) → ℝ) (p : Fin (n + 1))
    (Φ : (Fin (n + 1) → ℝ) → ℂ) (hΦ : IntegrableOn Φ (Icc 0 b)) :
    ∫ u in Icc 0 b, Φ u =
      ∫ y in Icc 0 (b ∘ p.succAbove), ∫ x in Icc (0 : ℝ) (b p), Φ (p.insertNth x y) := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) p).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) p).symm _
  have hbox := preimage_box_piFinSuccAbove b p
  have hint : IntegrableOn (Φ ∘ e) (Icc 0 (b p) ×ˢ Icc 0 (b ∘ p.succAbove)) := by
    rw [← hbox]; exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hΦ
  have hint' : Integrable (Φ ∘ e) (((volume : Measure ℝ).restrict (Icc 0 (b p))).prod
      ((volume : Measure (Fin n → ℝ)).restrict (Icc 0 (b ∘ p.succAbove)))) := by
    rw [Measure.prod_restrict]; exact hint
  rw [← hem.map_eq, setIntegral_map_equiv, hbox, Measure.volume_eq_prod, ← Measure.prod_restrict]
  exact integral_prod_symm (fun x ↦ Φ (e x)) hint'

/-- The inner integrals of a sliced integrable function are integrable in the outer variable. -/
private theorem integrableOn_inner_insertNth (b : Fin (n + 1) → ℝ) (p : Fin (n + 1))
    (Φ : (Fin (n + 1) → ℝ) → ℂ) (hΦ : IntegrableOn Φ (Icc 0 b)) :
    IntegrableOn (fun y ↦ ∫ x in Icc (0 : ℝ) (b p), Φ (p.insertNth x y))
      (Icc 0 (b ∘ p.succAbove)) := by
  set e : ℝ × (Fin n → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ ↦ ℝ) p).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) p).symm _
  have hbox := preimage_box_piFinSuccAbove b p
  have hint : IntegrableOn (Φ ∘ e) (Icc 0 (b p) ×ˢ Icc 0 (b ∘ p.succAbove)) := by
    rw [← hbox]; exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 hΦ
  have hint' : Integrable (Φ ∘ e) (((volume : Measure ℝ).restrict (Icc 0 (b p))).prod
      ((volume : Measure (Fin n → ℝ)).restrict (Icc 0 (b ∘ p.succAbove)))) := by
    rw [Measure.prod_restrict]; exact hint
  exact hint'.integral_prod_right

end Slicing

section IBP

variable {n : ℕ}

/-- Integration by parts on `[0, b]` against `x^s`, `Re s > −1`: for `G` continuous on `[0,b]` with
derivative `G'` on `(0,b)`,
`∫₀^b x^s G(x) dx = b^{s+1} G(b)/(s+1) − (1/(s+1)) ∫₀^b x^{s+1} G'(x) dx`. -/
private theorem integral_cpow_mul_ibp {b : ℝ} (hb : 0 < b) {s : ℂ} (hs : -1 < s.re) {G G' : ℝ → ℂ}
    (hG : ContinuousOn G (Icc 0 b)) (hG' : ∀ x ∈ Ioo 0 b, HasDerivAt G (G' x) x)
    (hG'i : IntervalIntegrable G' volume 0 b) :
    ∫ x in Icc (0 : ℝ) b, (x : ℂ) ^ s * G x =
      (b : ℂ) ^ (s + 1) / (s + 1) * G b -
        1 / (s + 1) * ∫ x in Icc (0 : ℝ) b, (x : ℂ) ^ (s + 1) * G' x := by
  have hre : 0 < (s + 1).re := by simp; linarith
  have hs1 : s + 1 ≠ 0 := fun h ↦ by simp [h] at hre
  have hs1' : s ≠ -1 := fun h ↦ hs1 (by rw [h]; ring)
  have hIcc : uIcc (0 : ℝ) b = Icc 0 b := uIcc_of_le hb.le
  have hv : ContinuousOn (fun x : ℝ ↦ (x : ℂ) ^ (s + 1) / (s + 1)) (Icc 0 b) := fun x _ ↦
    ((continuousAt_ofReal_cpow_const x (s + 1) (Or.inl hre)).div_const _).continuousWithinAt
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDeriv_right
    (u := G) (v := fun x : ℝ ↦ (x : ℂ) ^ (s + 1) / (s + 1)) (u' := G')
    (v' := fun x : ℝ ↦ (x : ℂ) ^ s) (a := 0) (b := b) (hIcc ▸ hG) (hIcc ▸ hv)
    (fun x hx ↦
      (hG' x (by simpa [min_eq_left hb.le, max_eq_right hb.le] using hx)).hasDerivWithinAt)
    (fun x hx ↦ by
      have hx0 : x ≠ 0 := by
        simp only [min_eq_left hb.le, max_eq_right hb.le] at hx
        exact hx.1.ne'
      exact (hasDerivAt_ofReal_cpow_const' hx0 hs1').hasDerivWithinAt)
    hG'i (intervalIntegral.intervalIntegrable_cpow' hs)
  simp only [Complex.ofReal_zero, Complex.zero_cpow hs1, zero_div, mul_zero, sub_zero] at hibp
  rw [intervalIntegral.integral_of_le hb.le, intervalIntegral.integral_of_le hb.le] at hibp
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  have h1 : ∀ x : ℝ, (x : ℂ) ^ s * G x = G x * (x : ℂ) ^ s := fun x ↦ mul_comm _ _
  have h2 : ∀ x : ℝ,
      G' x * ((x : ℂ) ^ (s + 1) / (s + 1)) = 1 / (s + 1) * ((x : ℂ) ^ (s + 1) * G' x) :=
    fun x ↦ by ring
  simp_rw [h1, hibp, h2, integral_const_mul]
  ring

/-- `x ↦ p.insertNth x y` has derivative `Pi.single p 1`. -/
private theorem hasDerivAt_insertNth (p : Fin (n + 1)) (y : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ p.insertNth x y) (Pi.single p 1 : Fin (n + 1) → ℝ) x := by
  rw [hasDerivAt_pi]
  intro q
  rcases eq_or_ne q p with rfl | hq
  · simp only [Fin.insertNth_apply_same, Pi.single_eq_same]
    exact hasDerivAt_id x
  · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hq
    simp only [Fin.insertNth_apply_succAbove, Pi.single_eq_of_ne hq]
    exact hasDerivAt_const x _

end IBP

section CoordDeriv

variable {d : ℕ}

/-- The partial derivative `∂ₚ g(u) = Dg(u)(eₚ)`. -/
private noncomputable def coordDeriv (p : Fin d) (g : (Fin d → ℝ) → ℂ) (u : Fin d → ℝ) : ℂ :=
  fderiv ℝ g u (Pi.single p 1)

private theorem contDiff_coordDeriv (p : Fin d) {g : (Fin d → ℝ) → ℂ} (hg : ContDiff ℝ ∞' g) :
    ContDiff ℝ ∞' (coordDeriv p g) :=
  (hg.fderiv_right (m := ∞') (by exact_mod_cast (le_top : (⊤ : ℕ∞) + 1 ≤ ⊤))).clm_apply
    contDiff_const

private theorem ContDiff.continuous_smooth {g : (Fin d → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞' g) : Continuous g :=
  hg.continuous

/-- The derivative of `x ↦ g(p.insertNth x y)` is `∂ₚg`. -/
private theorem hasDerivAt_comp_insertNth {n : ℕ} (p : Fin (n + 1)) {g : (Fin (n + 1) → ℝ) → ℂ}
    (hg : ContDiff ℝ ∞' g) (y : Fin n → ℝ) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ g (p.insertNth x y)) (coordDeriv p g (p.insertNth x y)) x :=
  ((hg.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt
    x (hasDerivAt_insertNth p y x)

end CoordDeriv

section ChartIBP

variable {n : ℕ}

/-- The product of coordinate powers along a slice. -/
private theorem prod_cpow_insertNth (e : Fin (n + 1) → ℂ) (p : Fin (n + 1)) (x : ℝ)
    (y : Fin n → ℝ) :
    ∏ q, ((p.insertNth (α := fun _ ↦ ℝ) x y q : ℝ) : ℂ) ^ e q =
      (x : ℂ) ^ e p * ∏ j, ((y j : ℝ) : ℂ) ^ e (p.succAbove j) := by
  rw [Fin.prod_univ_succAbove _ p]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

private theorem chartExp_update_zero (k h : Fin (n + 1) → ℕ) (z : ℂ) (p : Fin (n + 1)) :
    chartExp (Function.update k p 0) (Function.update h p 0) z p = 0 := by
  simp [chartExp]

private theorem chartExp_update_zero_succAbove (k h : Fin (n + 1) → ℕ) (z : ℂ) (p : Fin (n + 1))
    (j : Fin n) :
    chartExp (Function.update k p 0) (Function.update h p 0) z (p.succAbove j) =
      chartExp k h z (p.succAbove j) := by
  simp [chartExp]

private theorem chartExp_update_succ (k h : Fin (n + 1) → ℕ) (z : ℂ) (p : Fin (n + 1)) :
    chartExp k (Function.update h p (h p + 1)) z p = chartExp k h z p + 1 := by
  simp only [chartExp, Function.update_self]
  push_cast
  ring

private theorem chartExp_update_succ_succAbove (k h : Fin (n + 1) → ℕ) (z : ℂ) (p : Fin (n + 1))
    (j : Fin n) :
    chartExp k (Function.update h p (h p + 1)) z (p.succAbove j) =
      chartExp k h z (p.succAbove j) := by
  simp [chartExp]

/-- **Integration by parts in coordinate `p`** for the chart zeta function of a smooth amplitude,
on the convergence region:
`∫ u^{s} g = (bₚ^{sₚ}/(sₚ+1)) ∫ u^{s[p:=0]} g(u[p := bₚ]) − (1/(sₚ+1)) ∫ u^{s+eₚ} ∂ₚg`. -/
private theorem remainderZeta_ibp (k h : Fin (n + 1) → ℕ) {b : Fin (n + 1) → ℝ} (hb : ∀ q, 0 < b q)
    (p : Fin (n + 1)) {g : (Fin (n + 1) → ℝ) → ℂ} (hg : ContDiff ℝ ∞' g) {z : ℂ}
    (hz : ∀ q, -1 < (chartExp k h z q).re) :
    remainderZeta k h b g z =
      (b p : ℂ) ^ chartExp k h z p / (chartExp k h z p + 1) *
          remainderZeta (Function.update k p 0) (Function.update h p 0) b
            (fun u ↦ g (Function.update u p (b p))) z -
        1 / (chartExp k h z p + 1) *
          remainderZeta k (Function.update h p (h p + 1)) b (coordDeriv p g) z := by
  have hbp : (b p : ℂ) ≠ 0 := by exact_mod_cast (hb p).ne'
  have hsre : -1 < (chartExp k h z p).re := hz p
  have hcomp : IsCompact (Icc 0 b) := isCompact_Icc
  have hgc : Continuous g := hg.continuous
  have hg1c : Continuous fun u : Fin (n + 1) → ℝ ↦ g (Function.update u p (b p)) :=
    hgc.comp (continuous_id.update p continuous_const)
  have hg2c : Continuous (coordDeriv p g) := (contDiff_coordDeriv p hg).continuous
  have hz1 : ∀ q, -1 < (chartExp (Function.update k p 0) (Function.update h p 0) z q).re := by
    intro q
    rcases eq_or_ne q p with rfl | hq
    · rw [chartExp_update_zero]; simp
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hq
      rw [chartExp_update_zero_succAbove]; exact hz _
  have hz2 : ∀ q, -1 < (chartExp k (Function.update h p (h p + 1)) z q).re := by
    intro q
    rcases eq_or_ne q p with rfl | hq
    · rw [chartExp_update_succ, Complex.add_re, Complex.one_re]; linarith
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hq
      rw [chartExp_update_succ_succAbove]; exact hz _
  have hI : IntegrableOn (fun u : Fin (n + 1) → ℝ ↦ (∏ q, (u q : ℂ) ^ chartExp k h z q) * g u)
      (Icc 0 b) :=
    (integrableOn_box_cpow b _ hz).mul_continuousOn hgc.continuousOn hcomp
  have hI₁ : IntegrableOn (fun u : Fin (n + 1) → ℝ ↦
      (∏ q, (u q : ℂ) ^ chartExp (Function.update k p 0) (Function.update h p 0) z q) *
        g (Function.update u p (b p))) (Icc 0 b) :=
    (integrableOn_box_cpow b _ hz1).mul_continuousOn hg1c.continuousOn hcomp
  have hI₂ : IntegrableOn (fun u : Fin (n + 1) → ℝ ↦
      (∏ q, (u q : ℂ) ^ chartExp k (Function.update h p (h p + 1)) z q) * coordDeriv p g u)
      (Icc 0 b) :=
    (integrableOn_box_cpow b _ hz2).mul_continuousOn hg2c.continuousOn hcomp
  unfold remainderZeta
  rw [setIntegral_box_insertNth b p _ hI, setIntegral_box_insertNth b p _ hI₁,
    setIntegral_box_insertNth b p _ hI₂]
  have hint₁ := integrableOn_inner_insertNth b p _ hI₁
  have hint₂ := integrableOn_inner_insertNth b p _ hI₂
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_sub (hint₁.const_mul _) (hint₂.const_mul _)]
  refine setIntegral_congr_fun measurableSet_Icc fun y _ ↦ ?_
  set P : ℂ := ∏ j, ((y j : ℝ) : ℂ) ^ chartExp k h z (p.succAbove j) with hP
  have hPr : ∀ x : ℝ, ∏ q, ((p.insertNth (α := fun _ ↦ ℝ) x y q : ℝ) : ℂ) ^ chartExp k h z q =
      (x : ℂ) ^ chartExp k h z p * P := fun x ↦ prod_cpow_insertNth _ p x y
  have hPr₁ : ∀ x : ℝ, ∏ q, ((p.insertNth (α := fun _ ↦ ℝ) x y q : ℝ) : ℂ) ^
      chartExp (Function.update k p 0) (Function.update h p 0) z q = P := by
    intro x
    rw [prod_cpow_insertNth, chartExp_update_zero, Complex.cpow_zero, one_mul, hP]
    exact Finset.prod_congr rfl fun j _ ↦ by rw [chartExp_update_zero_succAbove]
  have hPr₂ : ∀ x : ℝ, ∏ q, ((p.insertNth (α := fun _ ↦ ℝ) x y q : ℝ) : ℂ) ^
      chartExp k (Function.update h p (h p + 1)) z q = (x : ℂ) ^ (chartExp k h z p + 1) * P := by
    intro x
    rw [prod_cpow_insertNth, chartExp_update_succ, hP]
    congr 1
    exact Finset.prod_congr rfl fun j _ ↦ by rw [chartExp_update_succ_succAbove]
  have hupd : ∀ x : ℝ, Function.update (p.insertNth (α := fun _ ↦ ℝ) x y) p (b p) =
      p.insertNth (α := fun _ ↦ ℝ) (b p) y :=
    fun x ↦ Fin.update_insertNth (α := fun _ ↦ ℝ) p x (b p) y
  simp only [hPr, hPr₁, hPr₂, hupd]
  have hibp := integral_cpow_mul_ibp (hb p) hsre (G := fun x ↦ g (p.insertNth x y))
    (G' := fun x ↦ coordDeriv p g (p.insertNth x y))
    (hgc.comp (continuous_id.finInsertNth p continuous_const)).continuousOn
    (fun x _ ↦ hasDerivAt_comp_insertNth p hg y x)
    ((hg2c.comp (continuous_id.finInsertNth p continuous_const)).intervalIntegrable _ _)
  have e1 : ∀ x : ℝ, (x : ℂ) ^ chartExp k h z p * P * g (p.insertNth x y) =
      P * ((x : ℂ) ^ chartExp k h z p * g (p.insertNth x y)) := fun x ↦ by ring
  have e2 : ∀ x : ℝ, (x : ℂ) ^ (chartExp k h z p + 1) * P * coordDeriv p g (p.insertNth x y) =
      P * ((x : ℂ) ^ (chartExp k h z p + 1) * coordDeriv p g (p.insertNth x y)) :=
    fun x ↦ by ring
  simp_rw [e1, e2, integral_const_mul, hibp, setIntegral_const,
    Real.volume_real_Icc_of_le (hb p).le, sub_zero, Complex.real_smul]
  rw [Complex.cpow_add _ _ hbp, Complex.cpow_one]
  ring

end ChartIBP

section Continuation

variable {d : ℕ}

theorem eq_chartPole_zero_of_add_one_eq_zero (k h : Fin d → ℕ) {p : Fin d} (hk : 0 < k p) {z : ℂ}
    (hz : chartExp k h z p + 1 = 0) : z = chartPole k h p 0 := by
  have hk' : (2 * (k p : ℂ)) ≠ 0 := by
    have : (0 : ℝ) < 2 * k p := by positivity
    exact_mod_cast this.ne'
  unfold chartPole
  push_cast
  rw [← neg_div, eq_div_iff hk']
  unfold chartExp at hz
  linear_combination hz

/-- `chartExp k h z p + 1 ≠ 0` off the first pole candidate (automatic when `kₚ = 0`). -/
private theorem chartExp_add_one_ne_zero' (k h : Fin d → ℕ) (p : Fin d) {z : ℂ}
    (hz : 0 < k p → z ≠ chartPole k h p 0) : chartExp k h z p + 1 ≠ 0 := by
  intro h0
  rcases Nat.eq_zero_or_pos (k p) with hk | hk
  · have := congrArg Complex.re h0
    simp [chartExp, hk] at this
    linarith [(Nat.cast_nonneg (h p) : (0 : ℝ) ≤ h p)]
  · exact hz hk (eq_chartPole_zero_of_add_one_eq_zero k h hk h0)

private theorem chartPole_update_zero {n : ℕ} (k h : Fin (n + 1) → ℕ) (p q : Fin (n + 1))
    (hq : q ≠ p)
    (j : ℕ) :
    chartPole (Function.update k p 0) (Function.update h p 0) q j = chartPole k h q j := by
  simp [chartPole, Function.update_of_ne hq]

private theorem chartPole_update_succ_ne {n : ℕ} (k h : Fin (n + 1) → ℕ) (p q : Fin (n + 1))
    (hq : q ≠ p)
    (j : ℕ) : chartPole k (Function.update h p (h p + 1)) q j = chartPole k h q j := by
  simp [chartPole, Function.update_of_ne hq]

private theorem chartPole_update_succ {n : ℕ} (k h : Fin (n + 1) → ℕ) (p : Fin (n + 1)) (j : ℕ) :
    chartPole k (Function.update h p (h p + 1)) p j = chartPole k h p (j + 1) := by
  simp only [chartPole, Function.update_self]
  push_cast
  ring_nf

/-- `F` continues the chart zeta function of `g` with shift vector `r`: equal on the convergence
region, holomorphic where `Re(2kₚz + hₚ) + rₚ > −1` off the candidates `−(hₚ+j+1)/(2kₚ)`, `j < rₚ`,
and meromorphic on that half-plane. -/
private def IsChartContinuation (k h : Fin d → ℕ) (b : Fin d → ℝ) (g : (Fin d → ℝ) → ℂ)
    (r : Fin d → ℕ)
    (F : ℂ → ℂ) : Prop :=
  (∀ z : ℂ, (∀ p, -1 < (chartExp k h z p).re) → remainderZeta k h b g z = F z) ∧
  (∀ z₀ : ℂ, (∀ p, -1 < (chartExp k h z₀ p).re + r p) →
    (∀ p, 0 < k p → ∀ j < r p, z₀ ≠ chartPole k h p j) → DifferentiableAt ℂ F z₀) ∧
  (∀ z₀ : ℂ, (∀ p, -1 < (chartExp k h z₀ p).re + r p) → MeromorphicAt F z₀)

private theorem isOpen_convergence (k h : Fin d → ℕ) :
    IsOpen {z : ℂ | ∀ p, -1 < (chartExp k h z p).re} := by
  rw [Set.ofPred_forall]
  exact isOpen_iInter_of_finite fun p ↦
    isOpen_lt continuous_const (Complex.continuous_re.comp (by unfold chartExp; fun_prop))

/-- The base case `r = 0`: the chart zeta function itself. -/
private theorem isChartContinuation_zero (k h : Fin d → ℕ) (b : Fin d → ℝ) {g : (Fin d → ℝ) → ℂ}
    (hg : Continuous g) : IsChartContinuation k h b g 0 (remainderZeta k h b g) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg.continuousOn
  have hdiff : ∀ z₀ : ℂ, (∀ p, -1 < (chartExp k h z₀ p).re) →
      DifferentiableAt ℂ (remainderZeta k h b g) z₀ := fun z₀ hz₀ ↦
    differentiableAt_remainderZeta k h 0 hg.measurable (C := C) (fun u hu ↦ by simpa using hC u hu)
      (fun p ↦ by have := hz₀ p; rw [chartExp_re] at this; simpa [domExp] using this)
  refine ⟨fun z _ ↦ rfl, fun z₀ hz₀ _ ↦ hdiff z₀ (by simpa using hz₀), fun z₀ hz₀ ↦ ?_⟩
  have hz₀' : z₀ ∈ {z : ℂ | ∀ p, -1 < (chartExp k h z p).re} := by simpa using hz₀
  exact (DifferentiableOn.analyticAt (fun z hz ↦ (hdiff z hz).differentiableWithinAt)
    ((isOpen_convergence k h).mem_nhds hz₀')).meromorphicAt

private theorem contDiff_update_left (p : Fin d) (c : ℝ) :
    ContDiff ℝ ∞' fun u : Fin d → ℝ ↦ Function.update u p c := by
  refine contDiff_pi.2 fun q ↦ ?_
  simp only [Function.update_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_apply ℝ (fun _ ↦ ℝ) q

/-- **The inductive step**: one integration by parts in coordinate `p` (with `rₚ > 0`) reduces the
continuation of `g` to those of the face amplitude `g(u[p := bₚ])` (shift `r[p := 0]`) and of the
derivative `∂ₚg` (shift `r[p := rₚ − 1]`, exponent `h[p := hₚ + 1]`). -/
private theorem isChartContinuation_step {n : ℕ} (k h : Fin (n + 1) → ℕ) {b : Fin (n + 1) → ℝ}
    (hb : ∀ q, 0 < b q) (p : Fin (n + 1)) {g : (Fin (n + 1) → ℝ) → ℂ} (hg : ContDiff ℝ ∞' g)
    (r : Fin (n + 1) → ℕ) (hr : 0 < r p) {F₁ F₂ : ℂ → ℂ}
    (h₁ : IsChartContinuation (Function.update k p 0) (Function.update h p 0) b
      (fun u ↦ g (Function.update u p (b p))) (Function.update r p 0) F₁)
    (h₂ : IsChartContinuation k (Function.update h p (h p + 1)) b (coordDeriv p g)
      (Function.update r p (r p - 1)) F₂) :
    IsChartContinuation k h b g r fun z ↦
      (b p : ℂ) ^ chartExp k h z p / (chartExp k h z p + 1) * F₁ z -
        1 / (chartExp k h z p + 1) * F₂ z := by
  have hbp : (b p : ℂ) ≠ 0 := by exact_mod_cast (hb p).ne'
  -- the conditions for the two pieces
  have hc₁ : ∀ z₀ : ℂ, (∀ q, -1 < (chartExp k h z₀ q).re + r q) →
      ∀ q, -1 < (chartExp (Function.update k p 0) (Function.update h p 0) z₀ q).re +
        Function.update r p 0 q := by
    intro z₀ hz₀ q
    rcases eq_or_ne q p with rfl | hq
    · rw [chartExp_update_zero]; simp
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hq
      rw [chartExp_update_zero_succAbove, Function.update_of_ne hq]; exact hz₀ _
  have hc₂ : ∀ z₀ : ℂ, (∀ q, -1 < (chartExp k h z₀ q).re + r q) →
      ∀ q, -1 < (chartExp k (Function.update h p (h p + 1)) z₀ q).re +
        Function.update r p (r p - 1) q := by
    intro z₀ hz₀ q
    rcases eq_or_ne q p with rfl | hq
    · rw [chartExp_update_succ, Function.update_self, Complex.add_re, Complex.one_re,
        Nat.cast_sub hr, Nat.cast_one]
      linarith [hz₀ q]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hq
      rw [chartExp_update_succ_succAbove, Function.update_of_ne hq]; exact hz₀ _
  have hlin : ∀ z₀ : ℂ, DifferentiableAt ℂ (fun z ↦ chartExp k h z p + 1) z₀ := fun z₀ ↦ by
    unfold chartExp; fun_prop
  have hcpow : ∀ z₀ : ℂ, DifferentiableAt ℂ (fun z ↦ (b p : ℂ) ^ chartExp k h z p) z₀ :=
    fun z₀ ↦
      (by unfold chartExp; fun_prop : DifferentiableAt ℂ (fun z ↦ chartExp k h z p) z₀).const_cpow
        (Or.inl hbp)
  refine ⟨fun z hz ↦ ?_, fun z₀ hz₀ hpole ↦ ?_, fun z₀ hz₀ ↦ ?_⟩
  · -- the identity on the convergence region
    have hz1 : ∀ q, -1 < (chartExp (Function.update k p 0) (Function.update h p 0) z q).re := by
      intro q
      rcases eq_or_ne q p with rfl | hq
      · rw [chartExp_update_zero]; simp
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hq
        rw [chartExp_update_zero_succAbove]; exact hz _
    have hz2 : ∀ q, -1 < (chartExp k (Function.update h p (h p + 1)) z q).re := by
      intro q
      rcases eq_or_ne q p with rfl | hq
      · rw [chartExp_update_succ, Complex.add_re, Complex.one_re]; linarith [hz q]
      · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq hq
        rw [chartExp_update_succ_succAbove]; exact hz _
    rw [remainderZeta_ibp k h hb p hg hz, h₁.1 z hz1, h₂.1 z hz2]
  · -- holomorphy off the poles
    have hne : chartExp k h z₀ p + 1 ≠ 0 :=
      chartExp_add_one_ne_zero' k h p fun hk ↦ hpole p hk 0 hr
    have hF₁ : DifferentiableAt ℂ F₁ z₀ := by
      refine h₁.2.1 z₀ (hc₁ z₀ hz₀) fun q hkq j hj ↦ ?_
      rcases eq_or_ne q p with rfl | hq
      · simp at hkq
      · rw [chartPole_update_zero k h p q hq]
        rw [Function.update_of_ne hq] at hkq hj
        exact hpole q hkq j hj
    have hF₂ : DifferentiableAt ℂ F₂ z₀ := by
      refine h₂.2.1 z₀ (hc₂ z₀ hz₀) fun q hkq j hj ↦ ?_
      rcases eq_or_ne q p with rfl | hq
      · rw [chartPole_update_succ]
        rw [Function.update_self] at hj
        exact hpole q hkq (j + 1) (by omega)
      · rw [chartPole_update_succ_ne k h p q hq]
        rw [Function.update_of_ne hq] at hj
        exact hpole q hkq j hj
    exact (((hcpow z₀).div (hlin z₀) hne).mul hF₁).sub
      (((differentiableAt_const _).div (hlin z₀) hne).mul hF₂)
  · -- meromorphy
    have hF₁ : MeromorphicAt F₁ z₀ := h₁.2.2 z₀ (hc₁ z₀ hz₀)
    have hF₂ : MeromorphicAt F₂ z₀ := h₂.2.2 z₀ (hc₂ z₀ hz₀)
    have hlm : MeromorphicAt (fun z ↦ chartExp k h z p + 1) z₀ :=
      ((Differentiable.analyticAt (fun z ↦ (hlin z)) z₀)).meromorphicAt
    have hcm : MeromorphicAt (fun z ↦ (b p : ℂ) ^ chartExp k h z p) z₀ :=
      ((Differentiable.analyticAt (fun z ↦ (hcpow z)) z₀)).meromorphicAt
    exact ((hcm.div hlm).mul hF₁).sub (((MeromorphicAt.const (1 : ℂ) z₀).div hlm).mul hF₂)

/-- **Meromorphic continuation of the chart zeta function of a smooth amplitude** along any shift
vector `r`, by induction on `∑ₚ rₚ`. -/
private theorem exists_isChartContinuation (k h : Fin d → ℕ) {b : Fin d → ℝ} (hb : ∀ p, 0 < b p)
    (g : (Fin d → ℝ) → ℂ) (hg : ContDiff ℝ ∞' g) (r : Fin d → ℕ) :
    ∃ F : ℂ → ℂ, IsChartContinuation k h b g r F := by
  suffices H : ∀ N : ℕ, ∀ r : Fin d → ℕ, ∑ p, r p ≤ N → ∀ (k h : Fin d → ℕ) (g : (Fin d → ℝ) → ℂ),
      ContDiff ℝ ∞' g → ∃ F : ℂ → ℂ, IsChartContinuation k h b g r F from
    H _ r le_rfl k h g hg
  intro N
  induction N with
  | zero =>
    intro r hr k h g hg
    have hr0 : r = 0 := by
      funext p
      have := Finset.single_le_sum (fun q _ ↦ Nat.zero_le (r q)) (Finset.mem_univ p)
      simp only [Pi.zero_apply]; omega
    subst hr0
    exact ⟨_, isChartContinuation_zero k h b hg.continuous⟩
  | succ N ih =>
    intro r hr k h g hg
    by_cases h0 : ∑ p, r p ≤ N
    · exact ih r h0 k h g hg
    · obtain ⟨p, -, hp⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ) (f := r)
        (by omega)
      have hp : 0 < r p := Nat.pos_of_ne_zero hp
      obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Fin.pos p).ne'
      have hsum : ∑ q, r q = r p + ∑ q ∈ Finset.univ.erase p, r q :=
        (Finset.add_sum_erase Finset.univ r (Finset.mem_univ p)).symm
      have hsum₁ : ∑ q, Function.update r p 0 q = ∑ q ∈ Finset.univ.erase p, r q := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ p), Function.update_self,
          zero_add]
        exact Finset.sum_congr rfl fun q hq ↦ Function.update_of_ne (Finset.ne_of_mem_erase hq) _ _
      have hsum₂ : ∑ q, Function.update r p (r p - 1) q =
          (r p - 1) + ∑ q ∈ Finset.univ.erase p, r q := by
        rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ p), Function.update_self]
        congr 1
        exact Finset.sum_congr rfl fun q hq ↦ Function.update_of_ne (Finset.ne_of_mem_erase hq) _ _
      obtain ⟨F₁, hF₁⟩ := ih (Function.update r p 0) (by omega) (Function.update k p 0)
        (Function.update h p 0) (fun u ↦ g (Function.update u p (b p)))
        (hg.comp (contDiff_update_left p (b p)))
      obtain ⟨F₂, hF₂⟩ := ih (Function.update r p (r p - 1)) (by omega) k
        (Function.update h p (h p + 1)) (coordDeriv p g) (contDiff_coordDeriv p hg)
      exact ⟨_, isChartContinuation_step k h hb p hg r hp hF₁ hF₂⟩

/-- **Theorem 6.6 for one chart with a smooth amplitude.** For every `N` there is `F` equal to
`∫_{[0,b]^d} u^{2kz+h} g(u) du` on the convergence region `Re(2kₚz + hₚ) > −1`, holomorphic at
every `z₀` with `Re(2kₚz₀ + hₚ) + N > −1` for all `p` off the finitely many candidates
`−(hₚ + j + 1)/(2kₚ)` (`j < N`, `kₚ > 0`), and meromorphic on that half-plane. -/
theorem exists_continuation_remainderZeta (k h : Fin d → ℕ) {b : Fin d → ℝ} (hb : ∀ p, 0 < b p)
    (g : (Fin d → ℝ) → ℂ) (hg : ContDiff ℝ ∞' g) (N : ℕ) :
    ∃ F : ℂ → ℂ,
      (∀ z : ℂ, (∀ p, -1 < (chartExp k h z p).re) → remainderZeta k h b g z = F z) ∧
      (∀ z₀ : ℂ, (∀ p, -1 < (chartExp k h z₀ p).re + N) →
        (∀ p, 0 < k p → ∀ j < N, z₀ ≠ chartPole k h p j) → DifferentiableAt ℂ F z₀) ∧
      (∀ z₀ : ℂ, (∀ p, -1 < (chartExp k h z₀ p).re + N) → MeromorphicAt F z₀) :=
  exists_isChartContinuation k h hb g hg fun _ ↦ N

end Continuation

end SingularLearningTheory.MellinAnalysis
