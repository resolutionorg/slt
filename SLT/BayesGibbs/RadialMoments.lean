/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Gamma
public import Mathlib.Algebra.Order.Star.Real
public import SLT.FreeEnergy.Main
public import SLT.FreeEnergy.StochasticAsymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Radial moments of the frozen kernel

The derivative of the frozen inner integral `frozenInner` in its parameter, the recurrence it
satisfies, and the self-normalised moment bounds.

Derived from the grammar package of this repository at revision
`703492578ada74ae70da33649b541c9ada776eee`.
-/

public section

open Real MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

namespace SingularLearningTheory.GaussianPosterior

/-- The donor order of factors, as an identity for the radial integral. -/
private theorem frozenInner_eq_fluctuationIntegral (β lam a : ℝ) :
    frozenInner lam β a =
      ∫ t in Ioi (0 : ℝ), t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t) := by
  unfold frozenInner
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
  congr 2; ring

/-- Integrability in the donor factor order, delegated to the existing frozen-kernel bound. -/
private theorem fluctuation_integrableOn (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    IntegrableOn (fun t : ℝ ↦ t ^ (lam - 1) *
      Real.exp (-β * t + β * a * Real.sqrt t)) (Ioi 0) := by
  simpa only [neg_mul, mul_assoc, mul_comm a] using
    (NormalCrossing.integrableOn_rpow_mul_exp_frozen (lam := lam) hlam hβ (ξ := a) le_rfl)


/-- Property (i): `S'_λ(a) = β · S_{λ+1/2}(a)` (grammar §4 `lem:fluctuation_properties`).
Differentiate under the integral: the `a`-derivative of the phase `-βt + βa√t` is `β√t`, and
`t^{λ-1}·√t = t^{(λ+1/2)-1}`, so the derivative integral is `β · S_{λ+1/2}`. -/
theorem hasDerivAt_fluctuation (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    HasDerivAt (fun a ↦ frozenInner lam β a) (β * frozenInner (lam + 1 / 2) β a) a := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ → ℝ → ℝ := fun b t ↦ t ^ (lam - 1) * Real.exp (-β * t + β * b * Real.sqrt t)
  let G : ℝ → ℝ → ℝ := fun b t ↦
    t ^ ((lam + 1 / 2) - 1) * Real.exp (-β * t + β * b * Real.sqrt t)
  let D : ℝ → ℝ → ℝ := fun b t ↦ β * G b t
  have hFi : ∀ b, Integrable (F b) μ := fun b ↦ fluctuation_integrableOn β lam hβ hlam b
  have hDi : ∀ b, Integrable (D b) μ := fun b ↦
    (fluctuation_integrableOn β (lam + 1 / 2) hβ (by linarith) b).const_mul β
  -- Pointwise derivative in the parameter `b`, normalised to the shifted integrand `D`.
  have hpoint : ∀ t, 0 < t → ∀ b, HasDerivAt (fun b ↦ F b t) (D b t) b := by
    intro t ht b
    have hphase : HasDerivAt (fun b : ℝ ↦ -β * t + β * b * Real.sqrt t) (β * Real.sqrt t) b := by
      simpa using ((((hasDerivAt_id b).const_mul β).mul_const (Real.sqrt t)).const_add (-β * t))
    have hpow : t ^ (lam - 1) * Real.sqrt t = t ^ (lam + 1 / 2 - 1) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]; congr 1; ring
    have hraw := (hphase.exp).const_mul (t ^ (lam - 1))
    have hval : t ^ (lam - 1) * (Real.exp (-β * t + β * b * Real.sqrt t) * (β * Real.sqrt t))
        = D b t := by
      change _ = β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * b * Real.sqrt t))
      rw [← hpow]; ring
    rwa [hval] at hraw
  have hpos : ∀ᵐ t ∂μ, 0 < t := ae_restrict_mem measurableSet_Ioi
  have hFmeas : ∀ᶠ b in nhds a, AEStronglyMeasurable (F b) μ :=
    Filter.Eventually.of_forall fun b ↦ (hFi b).aestronglyMeasurable
  -- Uniform domination on `ball a 1`: the derivative integrand increases in `b`.
  have hbound : ∀ᵐ t ∂μ, ∀ b ∈ Metric.ball a 1, ‖D b t‖ ≤ D (a + 1) t := by
    filter_upwards [hpos] with t ht b hb
    have hb' : b ≤ a + 1 := by
      have habs : |b - a| < 1 := by simpa only [Metric.mem_ball, Real.dist_eq] using hb
      have := (abs_lt.mp habs).2; linarith
    have hphase : -β * t + β * b * Real.sqrt t ≤ -β * t + β * (a + 1) * Real.sqrt t := by
      have hmul : β * b * Real.sqrt t ≤ β * (a + 1) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb' hβ.le) (Real.sqrt_nonneg t)
      linarith
    have hexp := Real.exp_le_exp.mpr hphase
    have hDnn : 0 ≤ D b t := by
      change 0 ≤ β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * b * Real.sqrt t))
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hDnn]
    change β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * b * Real.sqrt t))
      ≤ β * (t ^ (lam + 1 / 2 - 1) * Real.exp (-β * t + β * (a + 1) * Real.sqrt t))
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg ht.le _)) hβ.le
  have hdiff : ∀ᵐ t ∂μ, ∀ b ∈ Metric.ball a 1, HasDerivAt (fun b ↦ F b t) (D b t) b := by
    filter_upwards [hpos] with t ht b _
    exact hpoint t ht b
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (F := F) (F' := D)
    (x₀ := a) (bound := D (a + 1)) (s := Metric.ball a 1)
    (Metric.ball_mem_nhds a one_pos) hFmeas (hFi a)
    (hDi a).aestronglyMeasurable hbound (hDi (a + 1)) hdiff
  have h2 := h.2
  have hkey : (∫ t, D a t ∂μ) = β * frozenInner (lam + 1 / 2) β a := by
    simpa only [frozenInner_eq_fluctuationIntegral] using integral_const_mul β (G a)
  rw [hkey] at h2
  simpa only [frozenInner_eq_fluctuationIntegral] using h2



/-- The integration-by-parts recurrence (grammar §4 `eq:fluctuation_recurrence`):
`S_{λ+1}(a) = (a/2)·S_{λ+1/2}(a) + (λ/β)·S_λ(a)`, from `∫₀^∞ d/dt[t^λ e^{phase}] = 0`. -/
theorem fluctuation_recurrence (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    frozenInner (lam + 1) β a
      = (a / 2) * frozenInner (lam + 1 / 2) β a + (lam / β) * frozenInner lam β a := by
  set e : ℝ → ℝ := fun t ↦ Real.exp (-β * t + β * a * Real.sqrt t) with he_def
  -- `g t = t^λ e^{phase}`; its derivative `D` decomposed with exponents matching `fluctuation`.
  let g : ℝ → ℝ := fun t ↦ t ^ lam * e t
  let D : ℝ → ℝ := fun t ↦
    lam * (t ^ (lam - 1) * e t) - β * (t ^ (lam + 1 - 1) * e t)
      + (β * a / 2) * (t ^ (lam + 1 / 2 - 1) * e t)
  have hderiv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt g (D t) t := by
    intro t ht
    have ht0 : (0 : ℝ) < t := ht
    have hpow : HasDerivAt (fun t : ℝ ↦ t ^ lam) (lam * t ^ (lam - 1)) t :=
      Real.hasDerivAt_rpow_const (Or.inl ht0.ne')
    have hsqrt : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt t)) t := Real.hasDerivAt_sqrt ht0.ne'
    have h1 : HasDerivAt (fun t : ℝ ↦ -β * t) (-β) t := by
      simpa using (hasDerivAt_id t).const_mul (-β)
    have h2 : HasDerivAt (fun t : ℝ ↦ β * a * Real.sqrt t) (β * a * (1 / (2 * Real.sqrt t))) t :=
      hsqrt.const_mul (β * a)
    have hph : HasDerivAt (fun t : ℝ ↦ -β * t + β * a * Real.sqrt t)
        (-β + β * a * (1 / (2 * Real.sqrt t))) t := h1.add h2
    have he : HasDerivAt e (e t * (-β + β * a * (1 / (2 * Real.sqrt t)))) t := hph.exp
    have hg := hpow.mul he
    have hsq : Real.sqrt t = t ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow t
    have hA : t ^ (lam + 1 - 1) = t ^ lam := by rw [show lam + 1 - 1 = lam by ring]
    have hII : t ^ (lam + 1 / 2 - 1) = t ^ lam * (Real.sqrt t)⁻¹ := by
      rw [hsq, ← Real.rpow_neg ht0.le, ← Real.rpow_add ht0]; congr 1; ring
    have hval : lam * t ^ (lam - 1) * e t
        + t ^ lam * (e t * (-β + β * a * (1 / (2 * Real.sqrt t)))) = D t := by
      change _ = lam * (t ^ (lam - 1) * e t) - β * (t ^ (lam + 1 - 1) * e t)
        + β * a / 2 * (t ^ (lam + 1 / 2 - 1) * e t)
      rw [hA, hII]; ring
    exact hval ▸ hg
  -- Boundary continuity at 0: `g 0 = 0` for `λ > 0`.
  have hcont : ContinuousWithinAt g (Set.Ici 0) 0 := by
    have hce : Continuous e := by rw [he_def]; fun_prop
    have hcp : ContinuousWithinAt (fun t : ℝ ↦ t ^ lam) (Set.Ici 0) 0 :=
      (continuousAt_rpow_const 0 lam (Or.inr hlam.le)).continuousWithinAt
    exact hcp.mul hce.continuousWithinAt
  -- `t^λ e^{phase} → 0` at `atTop` (super-polynomial decay of the phase).
  have htop : Filter.Tendsto g Filter.atTop (nhds 0) := by
    have hmaj : Filter.Tendsto (fun t : ℝ ↦ Real.exp (β * a ^ 2 / 2) * (t ^ lam *
        Real.exp (-(β / 2) * t))) Filter.atTop (nhds 0) := by
      have := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero lam (β / 2) (by linarith)).const_mul
        (Real.exp (β * a ^ 2 / 2))
      simpa using this
    refine squeeze_zero' ?_ ?_ hmaj
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      exact mul_nonneg (Real.rpow_nonneg ht0.le lam) (by rw [he_def]; exact (Real.exp_pos _).le)
    · filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht0
      have hexp : Real.exp (-β * t + β * a * Real.sqrt t)
          ≤ Real.exp (β * a ^ 2 / 2) * Real.exp (-(β / 2) * t) := by
        rw [← Real.exp_add]; apply Real.exp_le_exp.mpr
        nlinarith [sq_nonneg (Real.sqrt t - a), Real.sq_sqrt ht0.le]
      calc g t = t ^ lam * e t := rfl
        _ ≤ Real.exp (β * a ^ 2 / 2) * (t ^ lam * Real.exp (-(β / 2) * t)) := by
            rw [he_def]; nlinarith [Real.rpow_nonneg ht0.le lam, hexp, Real.exp_pos
              (-β * t + β * a * Real.sqrt t)]
  have hDint : IntegrableOn D (Set.Ioi 0) := by
    have h0 := fluctuation_integrableOn β lam hβ hlam a
    have h1 := fluctuation_integrableOn β (lam + 1) hβ (by linarith) a
    have hh := fluctuation_integrableOn β (lam + 1 / 2) hβ (by linarith) a
    exact ((h0.const_mul lam).sub (h1.const_mul β)).add (hh.const_mul (β * a / 2))
  have hg0 : g 0 = 0 := by
    simp only [g, Real.zero_rpow hlam.ne', zero_mul]
  have hFTC : (∫ t in Set.Ioi (0 : ℝ), D t) = 0 := by
    have := integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hDint htop
    rwa [hg0, sub_zero] at this
  -- Decompose the integral into the three fluctuation values.
  have hsplit : (∫ t in Set.Ioi (0 : ℝ), D t)
      = lam * frozenInner lam β a - β * frozenInner (lam + 1) β a
        + (β * a / 2) * frozenInner (lam + 1 / 2) β a := by
    have h0 : IntegrableOn (fun t ↦ t ^ (lam - 1) * e t) (Set.Ioi 0) := by
      rw [he_def]; exact fluctuation_integrableOn β lam hβ hlam a
    have h1 : IntegrableOn (fun t ↦ t ^ (lam + 1 - 1) * e t) (Set.Ioi 0) := by
      rw [he_def]; exact fluctuation_integrableOn β (lam + 1) hβ (by linarith) a
    have hh : IntegrableOn (fun t ↦ t ^ (lam + 1 / 2 - 1) * e t) (Set.Ioi 0) := by
      rw [he_def]; exact fluctuation_integrableOn β (lam + 1 / 2) hβ (by linarith) a
    have hDe : D = fun t ↦ lam * (t ^ (lam - 1) * e t) - β * (t ^ (lam + 1 - 1) * e t)
        + β * a / 2 * (t ^ (lam + 1 / 2 - 1) * e t) := rfl
    have ia : IntegrableOn (fun t ↦ lam * (t ^ (lam - 1) * e t)
        - β * (t ^ (lam + 1 - 1) * e t)) (Set.Ioi 0) := (h0.const_mul lam).sub (h1.const_mul β)
    have ib : IntegrableOn (fun t ↦ β * a / 2 * (t ^ (lam + 1 / 2 - 1) * e t)) (Set.Ioi 0) :=
      hh.const_mul (β * a / 2)
    rw [hDe, integral_add ia ib, integral_sub (h0.const_mul lam) (h1.const_mul β),
      integral_const_mul, integral_const_mul, integral_const_mul]
    simp only [frozenInner_eq_fluctuationIntegral]
    rfl
  rw [hFTC] at hsplit
  have hβ' : β ≠ 0 := hβ.ne'
  field_simp at hsplit ⊢
  linarith [hsplit]
section Basic

variable {β lam : ℝ}

/-- The fluctuation integrand. -/
private noncomputable def fluctIntegrandFn (β lam a t : ℝ) : ℝ :=
  t ^ (lam - 1) * Real.exp (-β * t + β * a * Real.sqrt t)

private theorem fluctuation_eq_integral (β lam a : ℝ) :
    frozenInner lam β a = ∫ t in Ioi (0 : ℝ), fluctIntegrandFn β lam a t := by
  rw [frozenInner_eq_fluctuationIntegral]
  rfl

private theorem fluctIntegrandFn_pos {a t : ℝ} (ht : 0 < t) : 0 < fluctIntegrandFn β lam a t :=
  mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)

private theorem fluctIntegrandFn_nonneg_ae (β lam a : ℝ) :
    0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] fluctIntegrandFn β lam a := by
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
  exact Filter.Eventually.of_forall fun t ht ↦ (fluctIntegrandFn_pos ht).le

private theorem integrableOn_fluctIntegrandFn (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ) :
    IntegrableOn (fluctIntegrandFn β lam a) (Ioi 0) :=
  fluctuation_integrableOn β lam hβ hlam a

end Basic

/-! ### The posterior Cauchy–Schwarz inequality -/

section CauchySchwarz

variable {β lam : ℝ} (hβ : 0 < β) (hlam : 0 < lam) (a : ℝ)
include hβ hlam

omit hβ hlam in
private theorem fluctIntegrandFn_mul_sqrt (t : ℝ) (ht : 0 < t) :
    fluctIntegrandFn β lam a t * Real.sqrt t = fluctIntegrandFn β (lam + 1 / 2) a t := by
  unfold fluctIntegrandFn
  rw [Real.sqrt_eq_rpow, mul_right_comm, ← Real.rpow_add ht]
  ring_nf

omit hβ hlam in
private theorem fluctIntegrandFn_mul_self (t : ℝ) (ht : 0 < t) :
    fluctIntegrandFn β lam a t * t = fluctIntegrandFn β (lam + 1) a t := by
  unfold fluctIntegrandFn
  rw [mul_right_comm]
  nth_rewrite 2 [show t = t ^ (1 : ℝ) from (Real.rpow_one t).symm]
  rw [← Real.rpow_add ht]
  ring_nf

/-- `0 ≤ ∫ t^{λ−1} e^{…} (√t − r)² dt = S_{λ+1} − 2r S_{λ+1/2} + r² S_λ`. -/
private theorem fluctuation_quadratic_nonneg (r : ℝ) :
    0 ≤ frozenInner (lam + 1) β a - 2 * r * frozenInner (lam + 1 / 2) β a +
      r ^ 2 * frozenInner lam β a := by
  have h2 := integrableOn_fluctIntegrandFn (lam := lam + 1) hβ (by linarith) a
  have h1 := integrableOn_fluctIntegrandFn (lam := lam + 1 / 2) hβ (by linarith) a
  have h0 := integrableOn_fluctIntegrandFn (lam := lam) hβ hlam a
  have hA : Integrable (fun t ↦ fluctIntegrandFn β (lam + 1) a t -
      2 * r * fluctIntegrandFn β (lam + 1 / 2) a t) (volume.restrict (Ioi 0)) :=
    h2.sub (h1.const_mul _)
  have hint : ∫ t in Ioi (0 : ℝ), (fluctIntegrandFn β (lam + 1) a t -
      2 * r * fluctIntegrandFn β (lam + 1 / 2) a t + r ^ 2 * fluctIntegrandFn β lam a t) =
      frozenInner (lam + 1) β a - 2 * r * frozenInner (lam + 1 / 2) β a +
        r ^ 2 * frozenInner lam β a := by
    rw [integral_add hA (h0.const_mul _), integral_sub h2 (h1.const_mul _),
      integral_const_mul, integral_const_mul]
    simp only [frozenInner_eq_fluctuationIntegral]
    rfl
  rw [← hint]
  refine setIntegral_nonneg measurableSet_Ioi fun t ht ↦ ?_
  have ht' : (0 : ℝ) < t := ht
  rw [← fluctIntegrandFn_mul_self a t ht', ← fluctIntegrandFn_mul_sqrt a t ht']
  have hf := (fluctIntegrandFn_pos (β := β) (lam := lam) (a := a) ht').le
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht'.le
  calc (0 : ℝ) ≤ fluctIntegrandFn β lam a t * (Real.sqrt t - r) ^ 2 := by positivity
    _ = _ := by linear_combination fluctIntegrandFn β lam a t * hsq

/-- **Posterior Cauchy–Schwarz**: `S_{λ+1/2}(a)² ≤ S_λ(a) S_{λ+1}(a)`. -/
theorem fluctuation_half_sq_le :
    frozenInner (lam + 1 / 2) β a ^ 2 ≤ frozenInner lam β a * frozenInner (lam + 1) β a := by
  have h0 := frozenInner_pos hlam hβ a
  have hq := fluctuation_quadratic_nonneg hβ hlam a
    (frozenInner (lam + 1 / 2) β a / frozenInner lam β a)
  have h0' : frozenInner lam β a ≠ 0 := h0.ne'
  have heq : frozenInner (lam + 1) β a -
      2 * (frozenInner (lam + 1 / 2) β a / frozenInner lam β a) * frozenInner (lam + 1 / 2) β a +
      (frozenInner (lam + 1 / 2) β a / frozenInner lam β a) ^ 2 * frozenInner lam β a =
      frozenInner (lam + 1) β a - frozenInner (lam + 1 / 2) β a ^ 2 / frozenInner lam β a := by
    field_simp
    ring
  rw [heq, sub_nonneg, div_le_iff₀ h0] at hq
  linarith

/-- **The second-moment ratio is quadratically bounded**:
`S_{λ+1}(a) ≤ (2λ/β + a₊²/4) S_λ(a)`. -/
theorem fluctuation_succ_le :
    frozenInner (lam + 1) β a ≤ (2 * lam / β + max a 0 ^ 2 / 4) * frozenInner lam β a := by
  have h0 := frozenInner_pos hlam hβ a
  have h1 := frozenInner_pos (by linarith : 0 < lam + 1 / 2) hβ a
  have hcs := fluctuation_half_sq_le hβ hlam a
  have hrec := fluctuation_recurrence β lam hβ hlam a
  set S0 := frozenInner lam β a
  set S1 := frozenInner (lam + 1 / 2) β a
  set S2 := frozenInner (lam + 1) β a
  have hmax : a ≤ max a 0 := le_max_left _ _
  have hmax0 : 0 ≤ max a 0 := le_max_right _ _
  -- `S2 = (a/2) S1 + (λ/β) S0 ≤ (a₊/2) S1 + (λ/β) S0` and `(a₊/2) S1 ≤ a₊² S0/8 + S1²/(2 S0)`
  have hAM : max a 0 / 2 * S1 ≤ max a 0 ^ 2 / 8 * S0 + S1 ^ 2 / (2 * S0) := by
    have hS0 : 0 < 2 * S0 := by linarith
    have hS0' : S0 ≠ 0 := h0.ne'
    rw [← sub_nonneg]
    have : max a 0 ^ 2 / 8 * S0 + S1 ^ 2 / (2 * S0) - max a 0 / 2 * S1 =
        (max a 0 / 2 * S0 - S1) ^ 2 / (2 * S0) := by
      field_simp
      ring
    rw [this]
    positivity
  have hS1sq : S1 ^ 2 / (2 * S0) ≤ S2 / 2 := by
    rw [div_le_div_iff₀ (by linarith) two_pos]
    nlinarith
  have hstep : S2 ≤ max a 0 / 2 * S1 + lam / β * S0 := by
    rw [hrec]
    have : a / 2 * S1 ≤ max a 0 / 2 * S1 := by
      apply mul_le_mul_of_nonneg_right _ h1.le
      linarith
    linarith
  have hlb : 0 < lam / β := div_pos hlam hβ
  have : S2 ≤ max a 0 ^ 2 / 8 * S0 + S2 / 2 + lam / β * S0 := by linarith
  have h2 : S2 / 2 ≤ max a 0 ^ 2 / 8 * S0 + lam / β * S0 := by linarith
  calc S2 = 2 * (S2 / 2) := by ring
    _ ≤ 2 * (max a 0 ^ 2 / 8 * S0 + lam / β * S0) := by linarith
    _ = (2 * lam / β + max a 0 ^ 2 / 4) * S0 := by ring

/-- **The first-moment ratio is linearly bounded**:
`S_{λ+1/2}(a) ≤ √(2λ/β + a₊²/4) S_λ(a)`. -/
theorem fluctuation_half_le :
    frozenInner (lam + 1 / 2) β a ≤
      Real.sqrt (2 * lam / β + max a 0 ^ 2 / 4) * frozenInner lam β a := by
  have h0 := frozenInner_pos hlam hβ a
  have h1 := frozenInner_pos (by linarith : 0 < lam + 1 / 2) hβ a
  have hcs := fluctuation_half_sq_le hβ hlam a
  have hsucc := fluctuation_succ_le hβ hlam a
  have hB : 0 ≤ 2 * lam / β + max a 0 ^ 2 / 4 := by positivity
  have hsq : frozenInner (lam + 1 / 2) β a ^ 2 ≤
      (2 * lam / β + max a 0 ^ 2 / 4) * frozenInner lam β a ^ 2 := by
    calc frozenInner (lam + 1 / 2) β a ^ 2 ≤ frozenInner lam β a * frozenInner (lam + 1) β a := hcs
      _ ≤ frozenInner lam β a * ((2 * lam / β + max a 0 ^ 2 / 4) * frozenInner lam β a) :=
          mul_le_mul_of_nonneg_left hsucc h0.le
      _ = _ := by ring
  have := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq h1.le, Real.sqrt_mul hB, Real.sqrt_sq h0.le] at this
  exact this

end CauchySchwarz

end SingularLearningTheory.GaussianPosterior
