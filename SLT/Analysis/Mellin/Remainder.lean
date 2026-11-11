/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Murfet
-/
module

public import SLT.Analysis.Mellin.Monomial
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Holomorphy of a monomial Mellin integral with a vanishing amplitude

A coordinatewise monomial bound controls the integrand
and its derivative on smaller convergence regions. The smooth continuation uses these
lemmas after integrating by parts one coordinate at a time.
-/

public section

open MeasureTheory Set Finset Complex Filter
open scoped ENNReal

namespace SingularLearningTheory.MellinAnalysis

/-- `|log x| ≤ x^{−ε}/ε` for `0 < x ≤ 1`, `ε > 0`. -/
private theorem abs_log_le_rpow_div {x ε : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hε : 0 < ε) :
    |Real.log x| ≤ x ^ (-ε) / ε := by
  have hlog : Real.log x ≤ 0 := Real.log_nonpos hx0.le hx1
  rw [abs_of_nonpos hlog, le_div_iff₀ hε]
  have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 (-ε))
  rw [Real.log_rpow hx0] at h
  linarith

variable {d : ℕ}

/-- Almost every point of the box has all coordinates in `(0, bₚ]`. -/
theorem ae_box_pos (b : Fin d → ℝ) :
    ∀ᵐ u : Fin d → ℝ ∂(volume.restrict (Icc 0 b)), ∀ p, 0 < u p ∧ u p ≤ b p := by
  have h1 : ∀ᵐ u : Fin d → ℝ ∂(volume.restrict (Icc 0 b)), ∀ p, u p ≠ 0 := by
    refine ae_restrict_of_ae ?_
    rw [ae_all_iff]
    intro p
    rw [volume_pi]
    exact Measure.ae_eval_ne (μ := fun _ : Fin d ↦ (volume : Measure ℝ)) p 0
  filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with u hu hmem p
  have hp : u p ∈ Icc (0 : ℝ) (b p) := ⟨hmem.1 p, hmem.2 p⟩
  exact ⟨lt_of_le_of_ne hp.1 (hu p).symm, hp.2⟩

/-- The remainder integral `∫_{[0,b]^d} u^{2kz+h} R(u) du`. -/
@[expose] noncomputable def remainderZeta (k h : Fin d → ℕ) (b : Fin d → ℝ) (R : (Fin d → ℝ) → ℂ)
    (z : ℂ) : ℂ :=
  ∫ u in Icc 0 b, (∏ p, (u p : ℂ) ^ chartExp k h z p) * R u

/-- `L(u) = ∑ₚ 2kₚ log uₚ`. -/
private noncomputable def logWeight (k : Fin d → ℕ) (u : Fin d → ℝ) : ℝ := ∑ p, 2 * k p * Real.log
    (u p)

/-- `B(u) = ∑ₚ hₚ log uₚ`. -/
private noncomputable def logShift (h : Fin d → ℕ) (u : Fin d → ℝ) : ℝ := ∑ p, h p * Real.log (u p)

/-- Away from the coordinate hyperplanes, `u^{2kz+h} = exp(z L(u) + B(u))`. -/
private theorem prod_cpow_eq_exp (k h : Fin d → ℕ) {u : Fin d → ℝ} (hu : ∀ p, 0 < u p) (z : ℂ) :
    ∏ p, (u p : ℂ) ^ chartExp k h z p = exp (z * logWeight k u + logShift h u) := by
  have : ∀ p, (u p : ℂ) ^ chartExp k h z p
      = exp ((2 * (k p : ℂ) * Real.log (u p)) * z + (h p : ℂ) * Real.log (u p)) := by
    intro p
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (hu p).ne'), ← Complex.ofReal_log (hu p).le,
      chartExp]
    congr 1; ring
  simp_rw [this]
  rw [← Complex.exp_sum, logWeight, logShift]
  push_cast
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  congr 2
  exact sum_congr rfl fun p _ ↦ by ring

/-- `‖u^{2kz+h}‖ = ∏ₚ uₚ^{2kₚ Re z + hₚ}` for positive coordinates. -/
private theorem norm_prod_cpow (k h : Fin d → ℕ) {u : Fin d → ℝ} (hu : ∀ p, 0 < u p) (z : ℂ) :
    ‖∏ p, (u p : ℂ) ^ chartExp k h z p‖ = ∏ p, u p ^ (2 * k p * z.re + h p) := by
  rw [norm_prod]
  exact prod_congr rfl fun p _ ↦ by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (hu p), chartExp_re]

section Main

variable (k h n : Fin d → ℕ) {b : Fin d → ℝ} {C : ℝ} {R : (Fin d → ℝ) → ℂ}

/-- The dominating exponents `c_q = 2k_q a + h_q + n_q` at real part `a`. -/
@[expose] def domExp (a : ℝ) (q : Fin d) : ℝ := 2 * k q * a + h q + n q

/-- Integrability of a product of powers on the box (exponents `> −1`). -/
private theorem integrableOn_box_prod_rpow (b : Fin d → ℝ) (c : Fin d → ℝ) (hc : ∀ p, -1 < c p) :
    IntegrableOn (fun u : Fin d → ℝ ↦ ∏ p, u p ^ c p) (Icc 0 b) := by
  have h1 : ∀ p, IntegrableOn (fun x : ℝ ↦ x ^ c p) (Icc (0 : ℝ) (b p)) := fun p ↦ by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (intervalIntegral.intervalIntegrable_rpow' (hc p)).1.mono_set fun x hx ↦ by
      simpa using hx
  unfold IntegrableOn
  rw [← Set.pi_univ_Icc, volume_pi, Measure.restrict_pi_pi]
  exact Integrable.fintype_prod (E := ℝ) (μ := fun p ↦ volume.restrict (Icc (0 : ℝ) (b p)))
    (f := fun p (x : ℝ) ↦ x ^ c p) h1

/-- `max 1 bₚ`, the radius constant of a chart coordinate. -/
private def radiusMax (b : Fin d → ℝ) (p : Fin d) : ℝ := max 1 (b p)

private theorem one_le_radiusMax (b : Fin d → ℝ) (p : Fin d) : 1 ≤ radiusMax b p := le_max_left _ _

private theorem le_radiusMax {b : Fin d → ℝ} {u : Fin d → ℝ} {p : Fin d} (hu : u p ≤ b p) :
    u p ≤ radiusMax b p := hu.trans (le_max_right _ _)

/-- `u^r ≤ M^s · u^a` for `0 < u ≤ M`, `M ≥ 1`, `a ≤ r ≤ a + s`. -/
private theorem rpow_le_radius_mul {u M a r s : ℝ} (hu : 0 < u) (huM : u ≤ M) (hM : 1 ≤ M)
    (hr₁ : a ≤ r) (hr₂ : r ≤ a + s) : u ^ r ≤ M ^ s * u ^ a := by
  have hs : 0 ≤ s := by linarith
  rcases le_or_gt u 1 with h1 | h1
  · have h2 : u ^ r ≤ u ^ a := Real.rpow_le_rpow_of_exponent_ge hu h1 hr₁
    have h3 : (1 : ℝ) ≤ M ^ s := Real.one_le_rpow hM hs
    have h4 : 0 ≤ u ^ a := Real.rpow_nonneg hu.le a
    nlinarith
  · calc u ^ r ≤ u ^ (a + s) := Real.rpow_le_rpow_of_exponent_le h1.le hr₂
      _ = u ^ a * u ^ s := Real.rpow_add hu a s
      _ ≤ u ^ a * M ^ s :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hu.le huM hs) (Real.rpow_nonneg hu.le a)
      _ = M ^ s * u ^ a := mul_comm _ _

/-- `|log u| ≤ u^{−ε}/ε + log M` for `0 < u ≤ M`, `M ≥ 1`, `ε > 0`. -/
private theorem abs_log_le_rpow_div_add {u M ε : ℝ} (hu : 0 < u) (huM : u ≤ M) (hM : 1 ≤ M)
    (hε : 0 < ε) : |Real.log u| ≤ u ^ (-ε) / ε + Real.log M := by
  rcases le_or_gt u 1 with h1 | h1
  · have := abs_log_le_rpow_div hu h1 hε
    have := Real.log_nonneg hM
    linarith
  · rw [abs_of_nonneg (Real.log_nonneg h1.le)]
    have := Real.log_le_log hu huM
    have : 0 ≤ u ^ (-ε) / ε := by positivity
    linarith

/-- The pointwise bound at a point with coordinates in `(0, bₚ]`: for `a ≤ Re z ≤ a + s`,
`‖u^{2kz+h}‖ · ‖R u‖ ≤ (∏ₚ max(1,bₚ)^{2kₚs}) · C ∏_q u_q^{c_q(a)}`. -/
private theorem norm_le_dom {u : Fin d → ℝ} (hu : ∀ p, 0 < u p ∧ u p ≤ b p)
    (hR : ‖R u‖ ≤ C * ∏ p, u p ^ n p) {z : ℂ} {a s : ℝ} (hre : a ≤ z.re ∧ z.re ≤ a + s) :
    ‖(∏ p, (u p : ℂ) ^ chartExp k h z p) * R u‖
      ≤ (∏ p, radiusMax b p ^ (2 * k p * s)) * (C * ∏ q, u q ^ domExp k h n a q) := by
  rw [norm_mul, norm_prod_cpow k h (fun p ↦ (hu p).1)]
  have h1 : ∏ p, u p ^ (2 * k p * z.re + h p)
      ≤ ∏ p, radiusMax b p ^ (2 * k p * s) * u p ^ (2 * k p * a + h p) := by
    refine prod_le_prod₀ (fun p _ ↦ by have := (hu p).1; positivity) fun p _ ↦ ?_
    have hk0 : (0 : ℝ) ≤ k p := Nat.cast_nonneg _
    exact rpow_le_radius_mul (hu p).1 (le_radiusMax (hu p).2) (one_le_radiusMax b p)
      (by nlinarith [hre.1]) (by nlinarith [hre.2])
  rw [prod_mul_distrib] at h1
  have h2 : (∏ p, u p ^ (2 * k p * a + h p)) * ∏ p, u p ^ n p = ∏ q, u q ^ domExp k h n a q := by
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun p _ ↦ ?_
    rw [← Real.rpow_natCast, ← Real.rpow_add (hu p).1, domExp]
  have hM0 : 0 ≤ ∏ p, radiusMax b p ^ (2 * k p * s) :=
    prod_nonneg fun p _ ↦ Real.rpow_nonneg (by linarith [one_le_radiusMax b p]) _
  calc (∏ p, u p ^ (2 * k p * z.re + h p)) * ‖R u‖
      ≤ ((∏ p, radiusMax b p ^ (2 * k p * s)) * ∏ p, u p ^ (2 * k p * a + h p))
          * (C * ∏ p, u p ^ n p) :=
        mul_le_mul h1 hR (norm_nonneg _) (mul_nonneg hM0 (prod_nonneg fun p _ ↦ by
          have := (hu p).1; positivity))
    _ = (∏ p, radiusMax b p ^ (2 * k p * s)) * (C * ∏ q, u q ^ domExp k h n a q) := by
        rw [← h2]; ring

/-- The pointwise bound on the derivative: `|L(u)| ≤ ∑ₚ 2kₚ (uₚ^{−ε}/ε + log max(1,bₚ))`. -/
private theorem abs_logWeight_le {u : Fin d → ℝ} (hu : ∀ p, 0 < u p ∧ u p ≤ b p) {ε : ℝ}
    (hε : 0 < ε) :
    |logWeight k u| ≤ ∑ p, 2 * k p * (u p ^ (-ε) / ε + Real.log (radiusMax b p)) := by
  unfold logWeight
  refine (Finset.abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p _ ↦ ?_)
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * k p)]
  exact mul_le_mul_of_nonneg_left
    (abs_log_le_rpow_div_add (hu p).1 (le_radiusMax (hu p).2) (one_le_radiusMax b p) hε)
    (by positivity)

/-- The dominating function of the derivative:
`bound(u) = ∑ₚ 2kₚ (uₚ^{−ε}/ε + log max(1,bₚ)) · Mtot · C ∏_q u_q^{c_q(a)}`. -/
private noncomputable def derivBound (b : Fin d → ℝ) (C a ε Mtot : ℝ) (u : Fin d → ℝ) : ℝ :=
  ∑ p, 2 * k p * (u p ^ (-ε) / ε + Real.log (radiusMax b p))
    * (Mtot * (C * ∏ q, u q ^ domExp k h n a q))

/-- Each term of the bound is a product of one-variable powers: `uₚ^{−ε} ∏_q u_q^{c_q}
= ∏_q u_q^{c_q − ε[q = p]}`. -/
private theorem rpow_mul_prod_eq {u : Fin d → ℝ} (hu : ∀ p, 0 < u p) (c : Fin d → ℝ) (ε : ℝ)
    (p : Fin d) :
    u p ^ (-ε) * ∏ q, u q ^ c q = ∏ q, u q ^ (c q - if q = p then ε else 0) := by
  classical
  have : ∏ q, u q ^ (c q - if q = p then ε else 0)
      = ∏ q, u q ^ c q * u q ^ (-if q = p then ε else 0) := by
    refine prod_congr rfl fun q _ ↦ ?_
    rw [← Real.rpow_add (hu q)]; ring_nf
  rw [this, prod_mul_distrib]
  have h2 : ∏ q, u q ^ (-if q = p then ε else 0) = u p ^ (-ε) := by
    rw [Finset.prod_eq_single p]
    · simp
    · intro q _ hq; simp [hq]
    · intro h; exact absurd (Finset.mem_univ p) h
  rw [h2, mul_comm]

/-- The derivative bound is integrable on the box when `c_q(a) − ε > −1` for all `q`. -/
private theorem integrableOn_derivBound (b : Fin d → ℝ) (C a Mtot : ℝ) {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ q, -1 < domExp k h n a q - ε) :
    IntegrableOn (derivBound k h n b C a ε Mtot) (Icc 0 b) := by
  classical
  unfold derivBound
  refine integrable_finsetSum _ fun p _ ↦ ?_
  have hpos : ∀ᵐ u ∂(volume.restrict (Icc 0 b)), ∀ q, 0 < u q := (ae_box_pos b).mono
    fun u hu q ↦ (hu q).1
  have hint := integrableOn_box_prod_rpow (d := d) b
    (fun q ↦ domExp k h n a q - if q = p then ε else 0) fun q ↦ by
      by_cases hq : q = p
      · simp only [hq, ite_true]; exact hc p
      · simp only [hq, ite_false, sub_zero]; linarith [hc q, hε]
  have hint2 := integrableOn_box_prod_rpow (d := d) b (domExp k h n a) fun q ↦ by
    linarith [hc q, hε]
  refine ((hint.const_mul (2 * k p / ε * (Mtot * C))).add
    (hint2.const_mul (2 * k p * Real.log (radiusMax b p) * (Mtot * C)))).congr
    (hpos.mono fun u hu ↦ ?_)
  simp only [Pi.add_apply]
  rw [← rpow_mul_prod_eq hu (fun q ↦ domExp k h n a q) ε p]
  ring

/-- The integrand `u^{2kz+h} R(u)` and its `z`-derivative `L(u) u^{2kz+h} R(u)`. -/
private noncomputable def remIntegrand (R : (Fin d → ℝ) → ℂ) (z : ℂ) (u : Fin d → ℝ) : ℂ :=
  (∏ p, (u p : ℂ) ^ chartExp k h z p) * R u

/-- The $z$-derivative $L(u)\,u^{2kz+h}R(u)$ of
`SingularLearningTheory.MellinAnalysis.remIntegrand`, where $L$ is
`SingularLearningTheory.MellinAnalysis.logWeight`. Its integral over the box is the derivative of
`SingularLearningTheory.MellinAnalysis.remainderZeta`
(`SingularLearningTheory.MellinAnalysis.hasDerivAt_remainderZeta`). -/
private noncomputable def remIntegrand' (R : (Fin d → ℝ) → ℂ) (z : ℂ) (u : Fin d → ℝ) : ℂ :=
  (logWeight k u : ℂ) * remIntegrand k h R z u

private theorem measurable_remIntegrand (hRm : Measurable R) (z : ℂ) :
    Measurable (remIntegrand k h R z) :=
  (Finset.measurable_prod _ fun p _ ↦
    (Complex.measurable_ofReal.comp (measurable_pi_apply p)).pow_const _).mul hRm

private theorem measurable_logWeight : Measurable (logWeight k) :=
  Finset.measurable_sum _ fun p _ ↦
    (Real.measurable_log.comp (measurable_pi_apply p)).const_mul _

/-- Real parts on the ball of radius `δ` lie within `δ` of `Re z₀`. -/
private theorem re_bounds_of_mem_ball {z z₀ : ℂ} {δ : ℝ} (hz : z ∈ Metric.ball z₀ δ) :
    z₀.re - δ ≤ z.re ∧ z.re ≤ z₀.re + δ := by
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have := Complex.abs_re_le_norm (z - z₀)
  rw [sub_re] at this
  constructor <;> linarith [abs_le.mp this]

/-- **Holomorphy of the remainder term (Theorem 6.6).** If `R` is measurable with
`‖R(u)‖ ≤ C ∏ₚ uₚ^{nₚ}` on the box `∏ₚ [0, bₚ]`, then at every `z₀` with
`Re(2kₚz₀ + hₚ) + nₚ ≥ −1 + γ` (`γ > 0`) for all `p`, `z ↦ ∫_{box} u^{2kz+h} R(u) du` is
complex-differentiable, with derivative `∫ (∑ₚ 2kₚ log uₚ) u^{2kz₀+h} R(u) du`. -/
private theorem hasDerivAt_remainderZeta (hRm : Measurable R)
    (hR : ∀ u ∈ Icc 0 b, ‖R u‖ ≤ C * ∏ p, u p ^ n p) {z₀ : ℂ} {γ : ℝ} (hγ : 0 < γ)
    (hz : ∀ p, -1 + γ ≤ domExp k h n z₀.re p) :
    HasDerivAt (remainderZeta k h b R) (∫ u in Icc 0 b, remIntegrand' k h R z₀ u) z₀ := by
  -- the radius of the disc and the log-exponent
  set K : ℝ := ∑ p, 2 * (k p : ℝ) with hK
  have hK0 : 0 ≤ K := sum_nonneg fun p _ ↦ by positivity
  set δ : ℝ := γ / (4 * (K + 1)) with hδ
  have hδ0 : 0 < δ := by positivity
  set ε : ℝ := γ / 4 with hε
  have hε0 : 0 < ε := by positivity
  have hkδ : ∀ p, 2 * (k p : ℝ) * δ ≤ γ / 4 := fun p ↦ by
    have h1 : 2 * (k p : ℝ) ≤ K :=
      Finset.single_le_sum (f := fun p ↦ 2 * (k p : ℝ)) (fun _ _ ↦ by positivity)
        (Finset.mem_univ p)
    calc 2 * (k p : ℝ) * δ ≤ (K + 1) * δ := by nlinarith
      _ = γ / 4 := by rw [hδ]; field_simp
  set a : ℝ := z₀.re - δ with ha
  set Mtot : ℝ := ∏ p, radiusMax b p ^ (2 * k p * (2 * δ)) with hMtot
  have hdom : ∀ q, domExp k h n a q = domExp k h n z₀.re q - 2 * k q * δ := fun q ↦ by
    simp only [domExp, ha]; ring
  have hc : ∀ q, -1 < domExp k h n a q - ε := fun q ↦ by
    rw [hdom]; linarith [hz q, hkδ q]
  have hc0 : ∀ q, -1 < domExp k h n a q := fun q ↦ by linarith [hc q]
  -- almost every point of the box has coordinates in `(0, bₚ]` and lies in the box
  have hae : ∀ᵐ u ∂(volume.restrict (Icc 0 b)), (∀ q, 0 < u q ∧ u q ≤ b q) ∧ u ∈ Icc 0 b := by
    filter_upwards [ae_box_pos b, ae_restrict_mem measurableSet_Icc] with u hu hmem
    exact ⟨hu, hmem⟩
  have hmeasF : ∀ z, AEStronglyMeasurable (remIntegrand k h R z) (volume.restrict (Icc 0 b)) :=
    fun z ↦ (measurable_remIntegrand k h hRm z).aestronglyMeasurable
  have hmeasF' : AEStronglyMeasurable (remIntegrand' k h R z₀) (volume.restrict (Icc 0 b)) :=
    ((Complex.measurable_ofReal.comp (measurable_logWeight k)).mul
      (measurable_remIntegrand k h hRm z₀)).aestronglyMeasurable
  have hre₀ : a ≤ z₀.re ∧ z₀.re ≤ a + 2 * δ := ⟨by linarith, by linarith⟩
  -- integrability of the integrand at `z₀`
  have hint : Integrable (remIntegrand k h R z₀) (volume.restrict (Icc 0 b)) := by
    refine (((integrableOn_box_prod_rpow b (domExp k h n a) hc0).const_mul C).const_mul
      Mtot).mono' (hmeasF z₀) (hae.mono fun u hu ↦ ?_)
    exact norm_le_dom k h n hu.1 (hR u hu.2) hre₀
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Icc 0 b))
    (F := remIntegrand k h R) (F' := remIntegrand' k h R) (x₀ := z₀)
    (bound := derivBound k h n b C a ε Mtot) (Metric.ball_mem_nhds z₀ hδ0)
    (Filter.Eventually.of_forall hmeasF) hint hmeasF' ?_
    (integrableOn_derivBound k h n b C a Mtot hε0 hc) ?_
  · exact key.2
  · -- the bound on the derivative
    refine hae.mono fun u hu z hzb ↦ ?_
    have hu0 : ∀ p, 0 < u p := fun p ↦ (hu.1 p).1
    rw [remIntegrand', norm_mul, Complex.norm_real, Real.norm_eq_abs, derivBound,
      ← Finset.sum_mul]
    have hre : a ≤ z.re ∧ z.re ≤ a + 2 * δ := by
      obtain ⟨h1, h2⟩ := re_bounds_of_mem_ball hzb
      constructor <;> linarith
    have h1 := abs_logWeight_le k hu.1 hε0
    have h2 := norm_le_dom k h n hu.1 (hR u hu.2) hre
    exact mul_le_mul h1 h2 (norm_nonneg _) (sum_nonneg fun p _ ↦ by
      have := hu0 p
      have := Real.log_nonneg (one_le_radiusMax b p)
      positivity)
  · -- the derivative in `z`
    refine hae.mono fun u hu z _ ↦ ?_
    have hu0 : ∀ p, 0 < u p := fun p ↦ (hu.1 p).1
    have e : (fun z ↦ remIntegrand k h R z u)
        = fun z ↦ exp (z * (logWeight k u : ℂ) + (logShift h u : ℂ)) * R u :=
      funext fun z ↦ by simp only [remIntegrand]; rw [prod_cpow_eq_exp k h hu0 z]
    have e' : remIntegrand' k h R z u
        = exp (z * (logWeight k u : ℂ) + (logShift h u : ℂ)) * (1 * (logWeight k u : ℂ)) * R u := by
      simp only [remIntegrand', remIntegrand]; rw [prod_cpow_eq_exp k h hu0 z]; ring
    rw [e, e']
    exact ((((hasDerivAt_id z).mul_const _).add_const _).cexp).mul_const _

end Main


/-- A general-`d` form of the remainder holomorphy: `∫ u^{2kz+h} R(u) du` is differentiable at
`z₀` whenever `Re(2kₚz₀ + hₚ) + nₚ > −1` for all `p`. -/
theorem differentiableAt_remainderZeta (k h n : Fin d → ℕ) {b : Fin d → ℝ}
    {C : ℝ} {R : (Fin d → ℝ) → ℂ} (hRm : Measurable R)
    (hR : ∀ u ∈ Icc 0 b, ‖R u‖ ≤ C * ∏ p, u p ^ n p) {z₀ : ℂ}
    (hz : ∀ p, -1 < domExp k h n z₀.re p) :
    DifferentiableAt ℂ (remainderZeta k h b R) z₀ := by
  rcases isEmpty_or_nonempty (Fin d) with hd | hd
  · exact (hasDerivAt_remainderZeta k h n hRm hR (γ := 1) one_pos
      fun p ↦ (hd.false p).elim).differentiableAt
  · obtain ⟨p₀, -, hp₀⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Fin d))
      (fun p : Fin d ↦ domExp k h n z₀.re p + 1)
    have hγ : 0 < univ.inf' Finset.univ_nonempty (fun p : Fin d ↦ domExp k h n z₀.re p + 1) := by
      rw [hp₀]; linarith [hz p₀]
    refine (hasDerivAt_remainderZeta k h n hRm hR hγ fun p ↦ ?_).differentiableAt
    have := Finset.inf'_le (fun p : Fin d ↦ domExp k h n z₀.re p + 1) (Finset.mem_univ p)
    linarith

/-- Integrability of the remainder integrand on the box. -/
private theorem integrableOn_remIntegrand (k h n : Fin d → ℕ) {b : Fin d → ℝ}
    {C : ℝ} {R : (Fin d → ℝ) → ℂ} (hRm : Measurable R)
    (hR : ∀ u ∈ Icc 0 b, ‖R u‖ ≤ C * ∏ p, u p ^ n p) {z : ℂ}
    (hz : ∀ p, -1 < domExp k h n z.re p) :
    IntegrableOn (remIntegrand k h R z) (Icc 0 b) := by
  have hae : ∀ᵐ u ∂(volume.restrict (Icc 0 b)), (∀ q, 0 < u q ∧ u q ≤ b q) ∧ u ∈ Icc 0 b := by
    filter_upwards [ae_box_pos b, ae_restrict_mem measurableSet_Icc] with u hu hmem
    exact ⟨hu, hmem⟩
  refine (((integrableOn_box_prod_rpow b (domExp k h n z.re) hz).const_mul C).const_mul
    (∏ p, radiusMax b p ^ (2 * k p * (0 : ℝ)))).mono'
    (measurable_remIntegrand k h hRm z).aestronglyMeasurable (hae.mono fun u hu ↦ ?_)
  exact norm_le_dom k h n hu.1 (hR u hu.2) ⟨le_rfl, by simp⟩

end SingularLearningTheory.MellinAnalysis
