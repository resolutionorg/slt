/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.StochasticAsymptotics
public import SLT.MeasureTheory.Function.AsympUnifIntegrable
public import SLT.FreeEnergy.FundamentalConditions
public import SLT.SingularIntegrals.DeterministicFreeEnergy
import SLT.Analysis.SpecialFunctions.Pow.LogBounds

/-!
# The Free Energy Formula

[Hit26, Theorem 5.2.9].

| Thesis | Lean |
| --- | --- |
| `Y(ξ) > 0` (implicit in `−log Y(ξ)`; needs `NondegenerateResolutionAtlas`) | |
| | `NondegenerateResolutionAtlas.limitFunctional_pos` |
| `Z_n^0 > 0` (implicit in `F_n^0 = −log Z_n^0`) | `NondegenerateResolutionAtlas.normalizedEvidence_pos` |
| `F_n^0 = −log Z_n^0` | `ResolutionAtlas.EmpiricalProcessInput.normalizedFreeEnergy` |
| `R_n`, defined by [Hit26, Equation (5.2.11)] | |
| | `ResolutionAtlas.EmpiricalProcessInput.Rn` |
| [Hit26, Equation (5.2.11)] (the identity) | |
| | `ResolutionAtlas.EmpiricalProcessInput.freeEnergy_eq`, `…normalizedFreeEnergy_eq` |
| [Hit26, Theorem 5.2.9], `R_n` converges in distribution | |
| | `NondegenerateResolutionAtlas.free_energy_formula` |
| the two-sided bound on `A_n = R_n` in the proof of the expectation part | |
| | `…EmpiricalProcessInput.exists_normalized_normalizedEvidence_le`, |
| | `NondegenerateResolutionAtlas.exists_abs_Rn_le` |
| "fundamental condition I with `s = 4`" as consumed: fourth moments of `ξ_n`, `B_n` | |
| | `ResolutionAtlas.IntegrableEmpiricalProcessInput` |
| `A_n` is AUI | `NondegenerateResolutionAtlas.asympUnifIntegrable_Rn` |
| [Hit26, Theorem 5.2.9], `E[R_n]` converges | |
| | `NondegenerateResolutionAtlas.tendsto_integral_Rn` |
| [Hit26, Equation (5.2.12)], for `F_n^0` | |
| | `NondegenerateResolutionAtlas.eventually_integral_normalizedFreeEnergy_eq` |
| the fourth moments from [Hit26, Lemma 4.2.4] with `s = 4` | |
| | `ResolutionAtlas.ResolvedLikelihood.integrableEmpiricalProcessInput` |

## Statement

[Hit26] writes `F_n = nβL_n(w₀) + λ log n − (m−1) log log n + R_n` with `R_n` "a random variable
which converges in distribution", and in the proof sets `R_n = −log Y(ξ_n)`. Since the display is an
identity, `R_n` is forced to be `−log (n^λ Z_n^0 / (log n)^{m-1})`; that is the
definition used here, and the theorem is that it converges in distribution to `−log Y(ξ)`, by
[Wat09, Theorem 6.7] (`tendstoInDistribution_normalizedEvidence`) and the continuous mapping theorem
for `−log` on `(0, ∞)`. `Y(ξ) > 0` needs positive essential trace mass, hence
`NondegenerateResolutionAtlas`. The relation `F_n = nβ L_n(w₀) + F_n^0` is the definition of `K_n`
as the translate of `L_n`; `L_n(w₀)` enters only through this identity and is an arbitrary real
random variable in `freeEnergy_eq`.

The expectation part: with fourth-moment bounds on `ξ_n` and on the tail control `B_n`
(`IntegrableEmpiricalProcessInput`, [Hit26]'s "fundamental condition I with `s = 4`" via
[Hit26, Lemma 4.2.4]), `R_n` is dominated by `β(‖ξ_n‖² + B_n²)/2 + K`, hence
AUI, hence `E[R_n] → E[−log Y(ξ)]` and `E[F_n^0] = λ log n − (m−1) log log n + E[R_n]` for
large `n`. The lower bound on `Z_n^0` is the trace-mass bound, not [Hit26]'s `inf φ` (item
24). [Hit26]'s `E[F_n] = nβ L₀ + …` adds `E[nβ L_n(w₀)] = nβ L₀`, which is the definition
of `L₀`.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory

namespace ResolutionAtlas

/-- `J` is monotone in `x`: `J(−M) ≤ J(x)` for `|x| ≤ M`. No thesis counterpart. -/
theorem _root_.SingularLearningTheory.frozenInner_ge {lam β : ℝ} (hlam0 : 0 < lam) (hβ : 0 < β)
    {x M : ℝ} (hx : |x| ≤ M) :
    frozenInner lam β (-M) ≤ frozenInner lam β x := by
  have hM : |-M| ≤ M := by rw [abs_neg, abs_of_nonneg ((abs_nonneg x).trans hx)]
  refine setIntegral_mono_on (NormalCrossing.integrableOn_rpow_mul_exp_frozen hlam0 hβ hM)
    (NormalCrossing.integrableOn_rpow_mul_exp_frozen hlam0 hβ hx) measurableSet_Ioi fun t ht ↦ ?_
  have ht : 0 < t := ht
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (Real.rpow_nonneg ht.le _)
  have h1 := (abs_le.mp hx).1
  have h2 : 0 ≤ β * Real.sqrt t := by positivity
  linarith [mul_le_mul_of_nonneg_left h1 h2]

/-- `J(x) > 0`. No thesis counterpart. -/
theorem _root_.SingularLearningTheory.frozenInner_pos {lam β : ℝ} (hlam0 : 0 < lam) (hβ : 0 < β)
    (x : ℝ) :
    0 < frozenInner lam β x := by
  rw [frozenInner, integral_pos_iff_support_of_nonneg_ae]
  · refine lt_of_lt_of_le ?_ (measure_mono (s := Ioi (0 : ℝ)) fun t ht ↦ ?_)
    · rw [Measure.restrict_apply_self, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · have ht : 0 < t := ht
      exact (mul_pos (Real.rpow_pos_of_pos ht _) (Real.exp_pos _)).ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht : 0 < t := ht
    positivity
  · exact NormalCrossing.integrableOn_rpow_mul_exp_frozen hlam0 hβ le_rfl

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

theorem chartGamma_pos (α : R.ι) : 0 < R.chartGamma α := by
  unfold chartGamma
  have : 0 < ∏ j ∈ R.primary α, (R.k α j : ℝ) :=
    Finset.prod_pos fun j hj ↦ Nat.cast_pos.mpr (R.k_pos_of_mem_primary hj)
  positivity

theorem traceWeight_nonneg (α : R.ι) {v : Fin d → ℝ} (hv : v ∈ cube d (R.b α)) :
    0 ≤ R.traceWeight α v :=
  mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv.1 j) _)
    (R.weight_nonneg α _ (R.primaryZero α v).2)

theorem chartLimit_nonneg {β : ℝ} (hβ : 0 < β) (α : R.ι) (ζ : C(cube d (R.b α), ℝ)) :
    0 ≤ R.chartLimit β α ζ := by
  rw [chartLimit_eq]
  refine mul_nonneg (div_nonneg (R.chartGamma_pos α).le (pow_nonneg (R.b_pos α).le _))
    (setIntegral_nonneg measurableSet_Icc fun v hv ↦ ?_)
  exact mul_nonneg (R.traceWeight_nonneg α hv) (frozenInner_pos R.rlct_pos hβ _).le

/-- The essential trace mass is the integral of the trace weight (the two ways of putting
the primary coordinates to `0` agree on the cube). -/
theorem essentialTraceMass_eq (α : R.ι) :
    R.essentialTraceMass α = ∫ v in cube d (R.b α), R.traceWeight α v := by
  refine setIntegral_congr_fun measurableSet_Icc fun v hv ↦ ?_
  simp only [traceWeight]
  congr 2
  funext j
  by_cases hj : j ∈ R.primary α
  · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simpa using hj)]
    simp [primaryZero, hj]
  · obtain ⟨h0, hb⟩ := mem_cube.1 hv j
    rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_compl.mpr hj)]
    simp [primaryZero, hj, min_eq_right hb, max_eq_right h0]

/-- `Y^α(ζ) > 0` when the chart carries positive essential trace mass: the inner integral is
bounded below by `J(−‖ζ‖) > 0`. -/
theorem chartLimit_pos_of_traceMass_pos {β : ℝ} (hβ : 0 < β) {α : R.ι}
    (hT : 0 < R.essentialTraceMass α) (ζ : C(cube d (R.b α), ℝ)) : 0 < R.chartLimit β α ζ := by
  rw [chartLimit_eq]
  refine mul_pos (div_pos (R.chartGamma_pos α) (pow_pos (R.b_pos α) _)) ?_
  calc 0 < frozenInner R.rlct β (-‖ζ‖) * R.essentialTraceMass α :=
        mul_pos (frozenInner_pos R.rlct_pos hβ _) hT
    _ = ∫ v in cube d (R.b α), R.traceWeight α v * frozenInner R.rlct β (-‖ζ‖) := by
        rw [R.essentialTraceMass_eq, integral_mul_const, mul_comm]
    _ ≤ ∫ v in cube d (R.b α), R.traceWeight α v * frozenInner R.rlct β (ζ (R.primaryZero α v)) :=
        setIntegral_mono_on ((R.integrableOn_traceWeight α).mul_const _)
          (R.integrableOn_traceWeight_mul_frozenInner hβ α ζ)
          measurableSet_Icc fun v hv ↦
          mul_le_mul_of_nonneg_left (frozenInner_ge R.rlct_pos hβ
            ((Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm ζ _)))
            (R.traceWeight_nonneg α hv)

/-- The first display of the proof of [Hit26, Theorem 5.1.1], for a
chart functional: `Z_n^α(ζ) ≥ e^{-β‖ζ‖²/2} Z_α(n)` at inverse temperature `3β/2`. -/
theorem exp_mul_chartIntegral_le_chartPartition {β : ℝ} (hβ : 0 < β) (α : R.ι) {n : ℝ}
    (hn : 0 ≤ n) (ζ : C(cube d (R.b α), ℝ)) :
    Real.exp (-(β * ‖ζ‖ ^ 2 / 2)) * R.chartIntegral α (3 * β / 2) n
      ≤ R.chartPartition α β n ζ := by
  have hcube : MeasurableSet (cube d (R.b α)) := measurableSet_Icc
  rw [chartIntegral, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · filter_upwards [ae_restrict_mem hcube] with u hu
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le (mul_nonneg
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
      (R.weight_nonneg α u hu)))
  · refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ (R.weight_continuousOn α))
    · refine (Real.continuous_exp.comp ?_).continuousOn
      refine ((continuous_const.mul (continuous_finsetProd _ fun j _ ↦
        (continuous_apply j).pow _)).neg).add
        ((continuous_const.mul (continuous_finsetProd _ fun j _ ↦
          (continuous_apply j).pow _)).mul ((map_continuous ζ).comp (R.continuous_clamp α)))
    · exact (continuous_finsetProd _ fun j _ ↦
        (Real.continuous_rpow_const (Nat.cast_nonneg _)).comp (continuous_apply j)).continuousOn
  · filter_upwards [ae_restrict_mem hcube] with u hu
    have hU : Real.sqrt (∏ j, u j ^ (2 * R.k α j)) = ∏ j, u j ^ R.k α j := by
      rw [Finset.prod_pow_two_mul, Real.sqrt_sq (Finset.prod_nonneg fun j _ ↦
        pow_nonneg (hu.1 j) _)]
    have hK : 0 ≤ ∏ j, u j ^ (2 * R.k α j) :=
      Finset.prod_nonneg fun j _ ↦ Even.pow_nonneg (even_two_mul _) _
    have hζ : |ζ (R.clamp α u)| ≤ ‖ζ‖ :=
      (Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm ζ _)
    have h1 := (NormalCrossing.exponent_bounds hK hn hβ.le hζ).1
    rw [hU] at h1
    have h2 : 0 ≤ (∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u :=
      mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
        (R.weight_nonneg α u hu)
    calc Real.exp (-(β * ‖ζ‖ ^ 2 / 2)) * (Real.exp (-(n * (3 * β / 2) * ∏ j, u j ^ (2 * R.k α j))) *
            ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u))
        = Real.exp (-(n * (3 * β / 2) * ∏ j, u j ^ (2 * R.k α j)) + -(β * ‖ζ‖ ^ 2 / 2)) *
            ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u) := by rw [Real.exp_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) h2

/-- The upper half of the first display of the proof of [Hit26,
Theorem 5.1.1], for a chart functional: `Z_n^α(ζ) ≤ e^{β‖ζ‖²/2} Z_α(n)` at
inverse temperature `β/2`. -/
theorem chartPartition_le_exp_mul_chartIntegral {β : ℝ} (hβ : 0 < β) (α : R.ι) {n : ℝ}
    (hn : 0 ≤ n) (ζ : C(cube d (R.b α), ℝ)) :
    R.chartPartition α β n ζ ≤ Real.exp (β * ‖ζ‖ ^ 2 / 2) * R.chartIntegral α (β / 2) n := by
  have hcube : MeasurableSet (cube d (R.b α)) := measurableSet_Icc
  rw [chartIntegral, ← integral_const_mul]
  refine integral_mono_of_nonneg ?_ ?_ ?_
  · filter_upwards [ae_restrict_mem hcube] with u hu
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg
      (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
      (R.weight_nonneg α u hu))
  · refine Integrable.const_mul ?_ _
    refine ContinuousOn.integrableOn_compact isCompact_Icc ?_
    refine ContinuousOn.mul ?_ (ContinuousOn.mul ?_ (R.weight_continuousOn α))
    · exact (Real.continuous_exp.comp ((continuous_const.mul (continuous_finsetProd _ fun j _ ↦
        (continuous_apply j).pow _)).neg)).continuousOn
    · exact (continuous_finsetProd _ fun j _ ↦
        (Real.continuous_rpow_const (Nat.cast_nonneg _)).comp (continuous_apply j)).continuousOn
  · filter_upwards [ae_restrict_mem hcube] with u hu
    have hU : Real.sqrt (∏ j, u j ^ (2 * R.k α j)) = ∏ j, u j ^ R.k α j := by
      rw [Finset.prod_pow_two_mul, Real.sqrt_sq (Finset.prod_nonneg fun j _ ↦
        pow_nonneg (hu.1 j) _)]
    have hK : 0 ≤ ∏ j, u j ^ (2 * R.k α j) :=
      Finset.prod_nonneg fun j _ ↦ Even.pow_nonneg (even_two_mul _) _
    have hζ : |ζ (R.clamp α u)| ≤ ‖ζ‖ :=
      (Real.norm_eq_abs _).symm.le.trans (ContinuousMap.norm_coe_le_norm ζ _)
    have h1 := (NormalCrossing.exponent_bounds hK hn hβ.le hζ).2
    rw [hU] at h1
    have h2 : 0 ≤ (∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u :=
      mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu.1 j) _)
        (R.weight_nonneg α u hu)
    calc Real.exp (-(n * β * ∏ j, u j ^ (2 * R.k α j)) +
            Real.sqrt n * β * (∏ j, u j ^ R.k α j) * ζ (R.clamp α u)) *
            ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u)
        ≤ Real.exp (-(n * (β / 2) * ∏ j, u j ^ (2 * R.k α j)) + β * ‖ζ‖ ^ 2 / 2) *
            ((∏ j, u j ^ (R.h α j : ℝ)) * R.weight α u) :=
          mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr h1) h2
      _ = _ := by rw [Real.exp_add]; ring

namespace EmpiricalProcessInput

variable {R}
variable {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.EmpiricalProcessInput β P P')

/-- `F_n^0 = −log Z_n^0`, [Hit26,
Equation (5.0.4)]. -/
@[expose] noncomputable def normalizedFreeEnergy (n : ℕ) (ω : Ω) : ℝ := -Real.log
    (I.normalizedEvidence n ω)

/-- `R_n = −log (n^λ Z_n^0 / (log n)^{m-1})`, the remainder forced by
[Hit26, Equation (5.2.11)]. -/
@[expose] noncomputable def Rn (n : ℕ) (ω : Ω) : ℝ :=
  -Real.log ((n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω)

/-- [Hit26, Equation (5.2.11)]:
`F_n = nβ L_n(w₀) + λ log n − (m−1) log log n + R_n`, where `F_n = nβ L_n(w₀) + F_n^0` and
`L_n(w₀)` is any real random variable; valid for `n ≥ 2` wherever `Z_n^0 > 0`. -/
theorem freeEnergy_eq (Ln : ℕ → Ω → ℝ) {n : ℕ} (hn : 2 ≤ n) {ω : Ω}
    (hZ : 0 < I.normalizedEvidence n ω) :
    n * β * Ln n ω + I.normalizedFreeEnergy n ω
      = n * β * Ln n ω + R.rlct * Real.log n - ((R.mult - 1 : ℕ) : ℝ) * Real.log (Real.log n)
        + I.Rn n ω := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  simp only [normalizedFreeEnergy, Rn]
  rw [Real.log_mul (div_pos (Real.rpow_pos_of_pos hn0 _) (pow_pos hlog _)).ne' hZ.ne',
    Real.log_div (Real.rpow_pos_of_pos hn0 _).ne' (pow_pos hlog _).ne', Real.log_rpow hn0,
    Real.log_pow]
  ring

/-- `F_n^0 = λ log n − (m−1) log log n + R_n` for `n ≥ 2` wherever `Z_n^0 > 0`. -/
theorem normalizedFreeEnergy_eq {n : ℕ} (hn : 2 ≤ n) {ω : Ω} (hZ : 0 < I.normalizedEvidence n ω) :
    I.normalizedFreeEnergy n ω
      = R.rlct * Real.log n - ((R.mult - 1 : ℕ) : ℝ) * Real.log (Real.log n) + I.Rn n ω := by
  have := I.freeEnergy_eq (fun _ _ ↦ 0) hn hZ
  simpa using this

theorem aemeasurable_normalizedEvidence (hφi : IntegrableOn φ W) (n : ℕ) : AEMeasurable
    (I.normalizedEvidence n) P := by
  have : AEStronglyMeasurable
      (fun p : Ω × (Fin d → ℝ) ↦ Real.exp (-(n * β * I.Kn n p.1 p.2)) * φ p.2)
      (P.prod (volume.restrict W)) :=
    (Real.measurable_exp.comp
      (measurable_const.mul (I.Kn_measurable n)).neg).aestronglyMeasurable.mul
      hφi.aestronglyMeasurable.comp_snd
  exact this.integral_prod_right'.aemeasurable

theorem aestronglyMeasurable_Rn (hφi : IntegrableOn φ W) (n : ℕ) :
    AEStronglyMeasurable (I.Rn n) P :=
  (Real.measurable_log.comp_aemeasurable
    (aemeasurable_const.mul (I.aemeasurable_normalizedEvidence hφi n))).neg.aestronglyMeasurable

/-- The upper bound `n^λ Z_n^0 / (log n)^{m-1} ≤ C (e^{β‖ξ_n‖²/2} + e^{βB_n²/2})` of the
proof of the expectation part of [Hit26, Theorem 5.2.9], from [Wat09,
Theorem 4.8] on every chart and [Hit26, Equation (5.2.6)]. -/
theorem exists_normalized_normalizedEvidence_le (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hβ : 0 < β) :
    ∃ C > 0, ∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P,
      (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω
        ≤ C * (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) := by
  choose Cα hCα using fun α ↦ R.rpow_mul_chartIntegral_le α (half_pos hβ)
  obtain ⟨Ct, hCt⟩ :=
    Real.exists_rpow_mul_exp_neg_le (lam := R.rlct) (div_pos (mul_pos hβ R.δ_pos) two_pos)
  have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hcφ : 0 ≤ ∫ w in W, φ w := setIntegral_nonneg hW hφ
  refine ⟨∑ α, |Cα α| + |Ct| * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) + 1, by positivity,
    fun n hn ↦ ?_⟩
  filter_upwards [I.ae_normalizedEvidence_eq hW hφ hφi hβ (by omega : 1 ≤ n),
    I.tail_le hW hφ hφi hβ n]
    with ω hω hτ
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos (by linarith)
  have hpow : Real.log 2 ^ (R.mult - 1) ≤ Real.log n ^ (R.mult - 1) :=
    pow_le_pow_left₀ hl2.le (Real.log_le_log two_pos hn2) _
  have ha0 : 0 ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) :=
    div_nonneg (Real.rpow_nonneg hn0.le _) (pow_nonneg hlog.le _)
  have hex0 : 0 ≤ Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2) := by
    positivity
  have hchart : ∀ α, (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
      R.chartPartition α β n (I.Ξ n ω α)
        ≤ |Cα α| * (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) := by
    intro α
    have hCn := hCα α n hn2
    have hnorm : ‖I.Ξ n ω α‖ ≤ ‖I.Ξ n ω‖ := norm_le_pi_norm _ α
    have hexp : Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2) ≤ Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) := by
      gcongr
    have hdiv : (n : ℝ) ^ R.rlct * R.chartIntegral α (β / 2) n / Real.log n ^ (R.mult - 1)
        ≤ Cα α := by
      rw [div_le_iff₀ (pow_pos hlog _)]; exact hCn
    calc (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * R.chartPartition α β n (I.Ξ n ω α)
        ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
            (Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2) * R.chartIntegral α (β / 2) n) :=
          mul_le_mul_of_nonneg_left
            (R.chartPartition_le_exp_mul_chartIntegral hβ α hn0.le _) ha0
      _ = Real.exp (β * ‖I.Ξ n ω α‖ ^ 2 / 2) *
            ((n : ℝ) ^ R.rlct * R.chartIntegral α (β / 2) n / Real.log n ^ (R.mult - 1)) := by
          ring
      _ ≤ Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) * Cα α :=
          mul_le_mul hexp hdiv (div_nonneg (mul_nonneg (Real.rpow_nonneg hn0.le _)
            (R.chartIntegral_nonneg α _ _)) (pow_nonneg hlog.le _)) (Real.exp_pos _).le
      _ ≤ |Cα α| * (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) := by
          rw [mul_comm]
          exact mul_le_mul (le_abs_self _) (le_add_of_nonneg_right (Real.exp_pos _).le)
            (Real.exp_pos _).le (abs_nonneg _)
  have hCt0 : 0 < Ct :=
    lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos one_pos _) (Real.exp_pos _)) (hCt 1 le_rfl)
  have htail : (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.tail n ω
      ≤ |Ct| * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) *
          (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) := by
    have h1 : (n : ℝ) ^ R.rlct * Real.exp (-(β * R.δ / 2 * n)) ≤ Ct := hCt n (by linarith)
    calc (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.tail n ω
        ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
            (Real.exp (-(n * β * R.δ / 2) + β * I.B n ω ^ 2 / 2) * ∫ w in W, φ w) :=
          mul_le_mul_of_nonneg_left hτ ha0
      _ = (n : ℝ) ^ R.rlct * Real.exp (-(β * R.δ / 2 * n)) / Real.log n ^ (R.mult - 1) *
            (Real.exp (β * I.B n ω ^ 2 / 2) * ∫ w in W, φ w) := by
          rw [Real.exp_add, show -(β * R.δ / 2 * n) = -(n * β * R.δ / 2) by ring]; ring
      _ ≤ Ct / Real.log 2 ^ (R.mult - 1) *
            (Real.exp (β * I.B n ω ^ 2 / 2) * ∫ w in W, φ w) := by
          gcongr
      _ ≤ |Ct| * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) *
            (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) := by
          rw [abs_of_pos hCt0]
          have : 0 ≤ Ct * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) := by positivity
          calc Ct / Real.log 2 ^ (R.mult - 1) *
                (Real.exp (β * I.B n ω ^ 2 / 2) * ∫ w in W, φ w)
              = Ct * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) *
                  Real.exp (β * I.B n ω ^ 2 / 2) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (Real.exp_pos _).le) this
  calc (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω
      = ∑ α, (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * R.chartPartition α β n (I.Ξ n ω α) +
          (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.tail n ω := by
        rw [hω, mul_add, Finset.mul_sum]
    _ ≤ ∑ α, |Cα α| * (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) +
          |Ct| * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1) *
            (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) :=
        add_le_add (Finset.sum_le_sum fun α _ ↦ hchart α) htail
    _ = (∑ α, |Cα α| + |Ct| * (∫ w in W, φ w) / Real.log 2 ^ (R.mult - 1)) *
          (Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2) + Real.exp (β * I.B n ω ^ 2 / 2)) := by
        rw [← Finset.sum_mul, add_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ hex0
        linarith

end EmpiricalProcessInput

end ResolutionAtlas

namespace NondegenerateResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : NondegenerateResolutionAtlas K φ W)

/-- `Y(ζ) > 0` for every `ζ` when some essential chart carries positive trace mass. -/
theorem limitFunctional_pos {β : ℝ} (hβ : 0 < β) (ζ : R.ChartFunctions) :
    0 < R.limitFunctional β ζ := by
  classical
  obtain ⟨α₀, hess, hT⟩ := R.traceMass_pos
  unfold ResolutionAtlas.limitFunctional
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun α ↦
    if R.IsEssential α then R.chartLimit β α (ζ α) else 0) (fun α _ ↦ ?_) (Finset.mem_univ α₀))
  · simp only [ite_eq_left hess]
    exact R.chartLimit_pos_of_traceMass_pos hβ hT _
  · split_ifs
    · exact R.chartLimit_nonneg hβ _ _
    · exact le_rfl

variable {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (I : R.toResolutionAtlas.EmpiricalProcessInput β P P')

/-- `Z_n^0 > 0` almost surely for `n ≥ 2`: the essential chart with positive trace mass
contributes at least `e^{-β‖ξ_n‖²/2}` times a positive deterministic chart integral. -/
theorem normalizedEvidence_pos (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W)
    (hβ : 0 < β) {n : ℕ} (hn : 2 ≤ n) : ∀ᵐ ω ∂P, 0 < I.normalizedEvidence n ω := by
  obtain ⟨α₀, -, hT⟩ := R.traceMass_pos
  obtain ⟨c, hc, hcI⟩ := R.le_chartIntegral_of_traceMass_pos hT (β := 3 * β / 2) (by positivity)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hn1
  filter_upwards [I.ae_normalizedEvidence_eq hW hφ hφi hβ (by omega : 1 ≤ n)] with ω hω
  rw [hω]
  have h1 : 0 < R.chartPartition α₀ β n (I.Ξ n ω α₀) := by
    refine lt_of_lt_of_le (mul_pos (Real.exp_pos _) (lt_of_lt_of_le ?_ (hcI n hn1)))
      (R.exp_mul_chartIntegral_le_chartPartition hβ α₀ (Nat.cast_nonneg n) _)
    exact div_pos (mul_pos hc (pow_pos hlog _)) (Real.rpow_pos_of_pos (by linarith) _)
  have h2 : R.chartPartition α₀ β n (I.Ξ n ω α₀) ≤ ∑ α, R.chartPartition α β n (I.Ξ n ω α) :=
    Finset.single_le_sum (f := fun α ↦ R.chartPartition α β n (I.Ξ n ω α))
      (fun α _ ↦ R.chartPartition_nonneg α β n _) (Finset.mem_univ α₀)
  linarith [I.tail_nonneg hW hφ n ω]

/-- [Hit26, Theorem 5.2.9], stochastic part: the remainder
`R_n = F_n^0 − λ log n + (m−1) log log n` (`freeEnergy_eq`) converges in distribution to
`−log Y(ξ)`. [Wat09, Theorem 6.7] plus the continuous mapping theorem for `−log` on `(0, ∞)`; the
limit is positive by `limitFunctional_pos`.

Source statement: [Wat09, Main Theorem 6.2 (1)] -/
theorem free_energy_formula (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hβ : 0 < β)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α))) :
    TendstoInDistribution I.Rn atTop
      (fun ω' ↦ -Real.log (R.limitFunctional β (I.Ξlim ω'))) (fun _ ↦ P) P' :=
  tendstoInDistribution_comp_of_continuousOn_Ioi (g := fun x ↦ -Real.log x)
    (I.tendstoInDistribution_normalizedEvidence hW hφ hφi hβ hLip)
    (Real.continuousOn_log.mono fun _ hx ↦ ne_of_gt hx).neg Real.measurable_log.neg
    (Filter.Eventually.of_forall fun _ ↦ R.limitFunctional_pos hβ _)

/-- The two-sided bound `|R_n| ≤ β(‖ξ_n‖² + B_n²)/2 + K` of the proof of the expectation part
of [Hit26, Theorem 5.2.9], almost surely for `n ≥ 2`. The lower bound on
`Z_n^0` is the trace-mass bound, not [Hit26]'s `inf φ`. -/
theorem exists_abs_Rn_le (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφi : IntegrableOn φ W)
    (hβ : 0 < β) :
    ∃ K : ℝ, ∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P,
      |I.Rn n ω| ≤ β * (‖I.Ξ n ω‖ ^ 2 + I.B n ω ^ 2) / 2 + K := by
  obtain ⟨α₀, hess, hT⟩ := R.traceMass_pos
  obtain ⟨c, hc, hcI⟩ := R.le_chartIntegral_of_traceMass_pos hT (β := 3 * β / 2) (by positivity)
  obtain ⟨C, hC, hCle⟩ := I.exists_normalized_normalizedEvidence_le hW hφ hφi hβ
  refine ⟨|Real.log c| + |Real.log (2 * C)|, fun n hn ↦ ?_⟩
  filter_upwards [I.ae_normalizedEvidence_eq hW hφ hφi hβ (by omega : 1 ≤ n), hCle n hn,
    R.normalizedEvidence_pos I hW hφ hφi hβ hn] with ω hω hup hpos
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : 0 < Real.log n := Real.log_pos hn1
  have ha : 0 < (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) :=
    div_pos (Real.rpow_pos_of_pos hn0 _) (pow_pos hlog _)
  have hnorm : ‖I.Ξ n ω α₀‖ ≤ ‖I.Ξ n ω‖ := norm_le_pi_norm _ α₀
  -- lower bound on `n^λ Z_n^0 / (log n)^{m-1}`
  have hlow : c * Real.exp (-(β * ‖I.Ξ n ω‖ ^ 2 / 2))
      ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω := by
    have h1 : R.chartPartition α₀ β n (I.Ξ n ω α₀) ≤ ∑ α, R.chartPartition α β n (I.Ξ n ω α) :=
      Finset.single_le_sum (f := fun α ↦ R.chartPartition α β n (I.Ξ n ω α))
        (fun α _ ↦ R.chartPartition_nonneg α β n _) (Finset.mem_univ α₀)
    have h2 := R.exp_mul_chartIntegral_le_chartPartition hβ α₀ hn0.le (I.Ξ n ω α₀)
    have h3 := hcI n hn1
    rw [hess.1, hess.2] at h3
    have h4 : Real.exp (-(β * ‖I.Ξ n ω‖ ^ 2 / 2)) ≤ Real.exp (-(β * ‖I.Ξ n ω α₀‖ ^ 2 / 2)) := by
      gcongr
    have h5 : (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
        (c * Real.log n ^ (R.mult - 1) / n ^ R.rlct) = c := by
      field_simp
    calc c * Real.exp (-(β * ‖I.Ξ n ω‖ ^ 2 / 2))
        ≤ c * Real.exp (-(β * ‖I.Ξ n ω α₀‖ ^ 2 / 2)) := mul_le_mul_of_nonneg_left h4 hc.le
      _ = ((n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
            (c * Real.log n ^ (R.mult - 1) / n ^ R.rlct)) *
            Real.exp (-(β * ‖I.Ξ n ω α₀‖ ^ 2 / 2)) := by rw [h5]
      _ = (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
            (Real.exp (-(β * ‖I.Ξ n ω α₀‖ ^ 2 / 2)) *
              (c * Real.log n ^ (R.mult - 1) / n ^ R.rlct)) := by ring
      _ ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) *
            (Real.exp (-(β * ‖I.Ξ n ω α₀‖ ^ 2 / 2)) * R.chartIntegral α₀ (3 * β / 2) n) := by
          gcongr
      _ ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * R.chartPartition α₀ β n (I.Ξ n ω α₀) :=
          mul_le_mul_of_nonneg_left h2 ha.le
      _ ≤ (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω := by
          rw [hω]
          exact mul_le_mul_of_nonneg_left (h1.trans (le_add_of_nonneg_right
            (I.tail_nonneg hW hφ n ω))) ha.le
  -- upper bound, combined
  have hup' : (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω
      ≤ 2 * C * Real.exp (β * (‖I.Ξ n ω‖ ^ 2 + I.B n ω ^ 2) / 2) := by
    refine hup.trans ?_
    have e1 : Real.exp (β * ‖I.Ξ n ω‖ ^ 2 / 2)
        ≤ Real.exp (β * (‖I.Ξ n ω‖ ^ 2 + I.B n ω ^ 2) / 2) := by
      gcongr; nlinarith [sq_nonneg (I.B n ω)]
    have e2 : Real.exp (β * I.B n ω ^ 2 / 2)
        ≤ Real.exp (β * (‖I.Ξ n ω‖ ^ 2 + I.B n ω ^ 2) / 2) := by
      gcongr; nlinarith [sq_nonneg ‖I.Ξ n ω‖]
    nlinarith
  have hpos' : 0 < (n : ℝ) ^ R.rlct / Real.log n ^ (R.mult - 1) * I.normalizedEvidence n ω :=
      mul_pos ha hpos
  have hlogup := Real.log_le_log hpos' hup'
  have hloglow := Real.log_le_log (mul_pos hc (Real.exp_pos _)) hlow
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlogup
  rw [Real.log_mul hc.ne' (Real.exp_pos _).ne', Real.log_exp] at hloglow
  have hB2 : 0 ≤ β * I.B n ω ^ 2 := mul_nonneg hβ.le (sq_nonneg _)
  have hΞ2 : 0 ≤ β * ‖I.Ξ n ω‖ ^ 2 := mul_nonneg hβ.le (sq_nonneg _)
  have h6 := le_abs_self (Real.log (2 * C))
  have h7 := neg_abs_le (Real.log c)
  have h8 := abs_nonneg (Real.log c)
  have h9 := abs_nonneg (Real.log (2 * C))
  rw [ResolutionAtlas.EmpiricalProcessInput.Rn, abs_le]
  constructor <;> linarith

end NondegenerateResolutionAtlas

namespace ResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} (R : ResolutionAtlas K φ W)

/-- The random inputs of [Hit26, Theorem 5.2.6] with the fourth-moment
bounds the expectation part of [Hit26, Theorem 5.2.9] needs ("fundamental
condition I with `s = 4`" via [Hit26, Lemma 4.2.4]:
`E[‖ξ_n‖⁴] < ∞` and `E[sup_{K ≥ ε} |ψ_n|⁴] < ∞`, uniformly in `n`). -/
structure IntegrableEmpiricalProcessInput (β : ℝ) {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] (P : Measure Ω) (P' : Measure Ω') [IsProbabilityMeasure P]
    [IsProbabilityMeasure P'] extends R.EmpiricalProcessInput β P P' where
  Ξ_moment : ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ n, ∫⁻ ω, ‖Ξ n ω‖ₑ ^ 4 ∂P ≤ C
  B_moment : ∃ C : ENNReal, C ≠ ⊤ ∧ ∀ n, ∫⁻ ω, ‖B n ω‖ₑ ^ 4 ∂P ≤ C

end ResolutionAtlas

namespace NondegenerateResolutionAtlas

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : NondegenerateResolutionAtlas K φ W)
  {β : ℝ} {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {P : Measure Ω}
  {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
  (J : R.toResolutionAtlas.IntegrableEmpiricalProcessInput β P P')

/-- `R_n` is AUI under fourth-moment bounds: it is dominated by
`β(‖ξ_n‖² + B_n²)/2 + K`, whose second moment is bounded. -/
theorem asympUnifIntegrable_Rn (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hβ : 0 < β) :
    AsympUnifIntegrable P J.toEmpiricalProcessInput.Rn := by
  obtain ⟨K, hK⟩ := R.exists_abs_Rn_le J.toEmpiricalProcessInput hW hφ hφi hβ
  obtain ⟨CΞ, hCΞ, hΞ⟩ := J.Ξ_moment
  obtain ⟨CB, hCB, hB⟩ := J.B_moment
  set D : ℕ → Ω → ℝ := fun n ω ↦ β * (‖J.Ξ n ω‖ ^ 2 + J.B n ω ^ 2) / 2 + |K| with hD_def
  refine AsympUnifIntegrable.of_abs_le (Y := D) ?_ ?_
  · refine asympUnifIntegrable_of_lintegral_sq_le
      (C := ENNReal.ofReal (3 * (β / 2) ^ 2) * (CΞ + CB) + ENNReal.ofReal (3 * K ^ 2))
      (ENNReal.add_ne_top.mpr ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hCΞ, hCB⟩), ENNReal.ofReal_ne_top⟩)
      (Filter.Eventually.of_forall fun n ↦ ?_)
    have hpt : ∀ ω, ‖D n ω‖ₑ ^ 2
        ≤ ENNReal.ofReal (3 * (β / 2) ^ 2) * (‖J.Ξ n ω‖ₑ ^ 4 + ‖J.B n ω‖ₑ ^ 4) +
          ENNReal.ofReal (3 * K ^ 2) := by
      intro ω
      have hD0 : 0 ≤ D n ω := by simp only [hD_def]; positivity
      have hreal : D n ω ^ 2
          ≤ 3 * (β / 2) ^ 2 * (‖J.Ξ n ω‖ ^ 4 + |J.B n ω| ^ 4) + 3 * K ^ 2 := by
        simp only [hD_def]
        have h1 : |J.B n ω| ^ 4 = (J.B n ω ^ 2) ^ 2 := by
          rw [← sq_abs (J.B n ω), ← pow_mul]
        rw [h1, show ‖J.Ξ n ω‖ ^ 4 = (‖J.Ξ n ω‖ ^ 2) ^ 2 by ring]
        nlinarith [sq_nonneg (β / 2 * ‖J.Ξ n ω‖ ^ 2 - β / 2 * J.B n ω ^ 2),
          sq_nonneg (β / 2 * ‖J.Ξ n ω‖ ^ 2 - |K|), sq_nonneg (β / 2 * J.B n ω ^ 2 - |K|),
          sq_abs K]
      calc ‖D n ω‖ₑ ^ 2 = ENNReal.ofReal (D n ω ^ 2) := by
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg hD0, ENNReal.ofReal_pow hD0]
        _ ≤ ENNReal.ofReal (3 * (β / 2) ^ 2 * (‖J.Ξ n ω‖ ^ 4 + |J.B n ω| ^ 4) + 3 * K ^ 2) :=
            ENNReal.ofReal_le_ofReal hreal
        _ = _ := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_pow (norm_nonneg _), ENNReal.ofReal_pow (abs_nonneg _),
              ofReal_norm, ← Real.norm_eq_abs, ofReal_norm]
    have hmΞ : AEMeasurable (fun ω ↦ ‖J.Ξ n ω‖ₑ ^ 4) P :=
      ((J.Ξ_measurable n).enorm.pow_const 4).aemeasurable
    have hmB : AEMeasurable (fun ω ↦ ‖J.B n ω‖ₑ ^ 4) P :=
      ((J.B_measurable n).enorm.pow_const 4).aemeasurable
    calc ∫⁻ ω, ‖D n ω‖ₑ ^ 2 ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (3 * (β / 2) ^ 2) * (‖J.Ξ n ω‖ₑ ^ 4 + ‖J.B n ω‖ₑ ^ 4) +
            ENNReal.ofReal (3 * K ^ 2)) ∂P := lintegral_mono hpt
      _ = ENNReal.ofReal (3 * (β / 2) ^ 2) *
            ((∫⁻ ω, ‖J.Ξ n ω‖ₑ ^ 4 ∂P) + ∫⁻ ω, ‖J.B n ω‖ₑ ^ 4 ∂P) +
            ENNReal.ofReal (3 * K ^ 2) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' hmΞ]
      _ ≤ _ := by gcongr <;> [exact hΞ n; exact hB n]
  · refine Filter.eventually_atTop.mpr ⟨2, fun n hn ↦ ?_⟩
    filter_upwards [hK n hn] with ω hω
    exact hω.trans (add_le_add le_rfl (le_abs_self K))

/-- [Hit26, Theorem 5.2.9], expectation part, the convergence:
`E[R_n] → E[−log Y(ξ)]`.

Source statement: [Wat09, Main Theorem 6.2 (2)] -/
theorem tendsto_integral_Rn (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hβ : 0 < β)
    (hLip : ∀ α, R.IsEssential α →
      ∃ L : NNReal, LipschitzOnWith L (R.weight α) (cube d (R.b α))) :
    Tendsto (fun n ↦ ∫ ω, J.toEmpiricalProcessInput.Rn n ω ∂P) atTop
      (𝓝 (∫ ω', -Real.log (R.limitFunctional β (J.Ξlim ω')) ∂P')) :=
  (R.asympUnifIntegrable_Rn J hW hφ hφi hβ).tendsto_integral
    (R.free_energy_formula J.toEmpiricalProcessInput hW hφ hφi hβ hLip)

/-- [Hit26, Equation (5.2.12)] for `F_n^0`:
`E[F_n^0] = λ log n − (m−1) log log n + E[R_n]` for all large `n` ([Hit26]'s
`E[F_n] = nβL₀ + …` adds `E[nβ L_n(w₀)] = nβ L₀`). -/
theorem eventually_integral_normalizedFreeEnergy_eq (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφi : IntegrableOn φ W) (hβ : 0 < β) :
    ∀ᶠ n : ℕ in atTop, ∫ ω, J.toEmpiricalProcessInput.normalizedFreeEnergy n ω ∂P
      = R.rlct * Real.log n - ((R.mult - 1 : ℕ) : ℝ) * Real.log (Real.log n) +
        ∫ ω, J.toEmpiricalProcessInput.Rn n ω ∂P := by
  filter_upwards [(R.asympUnifIntegrable_Rn J hW hφ hφi hβ).eventually_integrable
    (J.toEmpiricalProcessInput.aestronglyMeasurable_Rn hφi), eventually_ge_atTop 2] with n hn hn2
  have heq : J.toEmpiricalProcessInput.normalizedFreeEnergy n =ᵐ[P] fun ω ↦
      (R.rlct * Real.log n - ((R.mult - 1 : ℕ) : ℝ) * Real.log (Real.log n)) +
        J.toEmpiricalProcessInput.Rn n ω := by
    filter_upwards [R.normalizedEvidence_pos J.toEmpiricalProcessInput hW hφ hφi hβ hn2] with ω hω
    exact J.toEmpiricalProcessInput.normalizedFreeEnergy_eq hn2 hω
  rw [integral_congr_ae heq, integral_add (integrable_const _) hn, integral_const,
    probReal_univ, one_smul]

end NondegenerateResolutionAtlas

namespace ResolutionAtlas.ResolvedLikelihood

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)} {R : ResolutionAtlas K φ W}
  {X : Type*} [MeasurableSpace X] {q : Measure X} {f : X → (Fin d → ℝ) → ℝ}
  (L : R.ResolvedLikelihood q f) {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
  {Xs : ℕ → Ω → X}

/-- The random inputs with the fourth moments the expectation part of
[Hit26, Theorem 5.2.9] needs, from [Hit26, Lemma 4.2.4] ([Wat09,
Theorem 5.8]) with `s = 4` for the chart process and for `ψ_n` on `{K ≥ δ}`. -/
@[expose] noncomputable def integrableEmpiricalProcessInput (β : ℝ) (P : Measure Ω)
    (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hf : Measurable (Function.uncurry f)) (hK : ∀ w, K w = ∫ x, f x w ∂q)
    (hc : IsCompact {w | w ∈ W ∧ R.δ ≤ K w})
    (E : EmpiricalProcessLimit q (fun x (p : (α : R.ι) × cube d (R.b α)) ↦ L.a p.1 x p.2)
      Xs P P')
    (hlip : R.PrimaryLipschitzTight E.Ψ P)
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ R.δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P P')
    (hE : E.MomentBound 4) (hT : T.MomentBound 4) :
    R.IntegrableEmpiricalProcessInput β P P' :=
  haveI : CompactSpace {w // w ∈ W ∧ R.δ ≤ K w} := isCompact_iff_compactSpace.mp hc
  { L.empiricalProcessInput β P P' hX hlaw hf hK hc E hlip T with
    Ξ_moment := by
      obtain ⟨C, hC, hCn⟩ := hE
      refine ⟨C, hC, fun n ↦ le_trans (lintegral_mono fun ω ↦ ?_) (hCn n)⟩
      change ‖-(R.toChartFunctions (E.Ψ n ω))‖ₑ ^ 4 ≤ _
      rw [enorm_neg]
      exact pow_le_pow_left' (R.enorm_toChartFunctions_le _) 4
    B_moment := by
      obtain ⟨C, hC, hCn⟩ := hT
      refine ⟨C, hC, fun n ↦ le_trans (lintegral_mono fun ω ↦ ?_) (hCn n)⟩
      change ‖‖T.Ψ n ω‖‖ₑ ^ 4 ≤ _
      rw [enorm_norm]
      exact pow_le_pow_left' (ContinuousMap.enorm_le_iSup_enorm _) 4 }

end ResolutionAtlas.ResolvedLikelihood

end SingularLearningTheory
