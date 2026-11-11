/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Floor.Semifield
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# A witness: the Bernoulli model

Every hypothesis of the free energy formula
(`SingularLearningTheory.free_energy_formula`) is inhabited:
`p(true | w) = w`, `p(false | w) = 1 − w` on `W = [1/4, 3/4]`, the uniform prior `φ = 1`, the
true parameter `w₀ = 1/2`, and the coordinate sample on `Bool^ℕ`, every hypothesis holds, so the
free energy formula for this model is an unconditional theorem.
No thesis counterpart; guards against vacuity of the fundamental conditions.

The Kullback–Leibler divergence is `K(w) = −log(4 w (1 − w)) / 2`, with
`(2w − 1)² / 2 ≤ K(w)` (from `log y ≤ y − 1`) and `∫ f(x, w)² q(dx) ≤ 4 (2w − 1)²` (from
`|log x| ≤ 2 |x − 1|` on `[1/2, 3/2]`), which gives relatively finite variance with `C = 1/8`.
-/

@[expose] public section

namespace BernoulliModel

open MeasureTheory Set Filter Topology ProbabilityTheory
open SingularLearningTheory
open scoped ENNReal

/-- The true distribution: a fair coin on `Bool`. -/
noncomputable def q : Measure Bool :=
  (1 / 2 : ℝ≥0∞) • Measure.dirac true + (1 / 2 : ℝ≥0∞) • Measure.dirac false

instance : IsProbabilityMeasure q :=
  ⟨by simp [q, Measure.add_apply, ENNReal.inv_two_add_inv_two]⟩

private lemma integral_q (g : Bool → ℝ) : ∫ x, g x ∂q = g true / 2 + g false / 2 := by
  haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac true) :=
    Measure.smul_finite _ (by norm_num)
  haveI : IsFiniteMeasure ((1 / 2 : ℝ≥0∞) • Measure.dirac false) :=
    Measure.smul_finite _ (by norm_num)
  simp only [q]
  rw [integral_add_measure Integrable.of_finite Integrable.of_finite, integral_smul_measure,
    integral_smul_measure, integral_dirac, integral_dirac]
  simp [div_eq_inv_mul]

/-- The model `p(true | w) = w`, `p(false | w) = 1 − w`, one real parameter `w : Fin 1 → ℝ`. -/
def p (w : Fin 1 → ℝ) (x : Bool) : ℝ := if x then w 0 else 1 - w 0

/-- The parameter space `W = [1/4, 3/4]`. -/
def W : Set (Fin 1 → ℝ) := {w | 1 / 4 ≤ w 0 ∧ w 0 ≤ 3 / 4}

/-- The open neighbourhood `U = (0, 1)` of `W` on which the model is regular. -/
def U : Set (Fin 1 → ℝ) := {w | 0 < w 0 ∧ w 0 < 1}

/-- The true parameter `w₀ = 1/2`. -/
noncomputable def w₀ : Fin 1 → ℝ := fun _ ↦ 1 / 2

/-- The uniform prior `φ = 1` on `W`. -/
def φ : (Fin 1 → ℝ) → ℝ := fun _ ↦ 1

/-- The sample: the coordinates of the infinite product `Bool^ℕ`. -/
def Xs (i : ℕ) (ω : ℕ → Bool) : Bool := ω i

/-- The law of the sample: the product of copies of `q`. -/
noncomputable def P : Measure (ℕ → Bool) := Measure.infinitePi fun _ ↦ q

instance : IsProbabilityMeasure P := by
  unfold P; infer_instance

theorem isCompact_W : IsCompact W := by
  have : W = Set.pi univ fun _ ↦ Icc (1 / 4 : ℝ) (3 / 4) := by
    ext w; simp only [W, mem_ofPred_eq, mem_univ_pi, mem_Icc, Fin.forall_fin_one]
  rw [this]
  exact isCompact_univ_pi fun _ ↦ isCompact_Icc

theorem isOpen_U : IsOpen U :=
  (isOpen_lt continuous_const (continuous_apply 0)).inter
    (isOpen_lt (continuous_apply 0) continuous_const)

theorem W_subset_U : W ⊆ U := fun w hw ↦ ⟨by linarith [hw.1], by linarith [hw.2]⟩

theorem w₀_mem : w₀ ∈ W := by norm_num [W, w₀]

theorem measurable_p : Measurable (Function.uncurry p) :=
  measurable_from_prod_countable_left fun x ↦ by
    cases x <;> simp only [Function.uncurry_apply_pair, p, Bool.false_eq_true, ↓reduceIte] <;>
      fun_prop

theorem p_pos : ∀ᵐ x ∂q, ∀ w ∈ W, 0 < p w x :=
  Eventually.of_forall fun x w hw ↦ by cases x <;> simp [p] <;> linarith [hw.1, hw.2]

private lemma loss_true {w : Fin 1 → ℝ} (h0 : 0 < w 0) :
    logDensityRatio p w₀ true w = Real.log (1 / 2) - Real.log (w 0) := by
  simp only [logDensityRatio, p, w₀, ite_true]
  exact Real.log_div (by norm_num) h0.ne'

private lemma loss_false {w : Fin 1 → ℝ} (h1 : w 0 < 1) :
    logDensityRatio p w₀ false w = Real.log (1 / 2) - Real.log (1 - w 0) := by
  simp only [logDensityRatio, p, w₀, Bool.false_eq_true, ite_false]
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
  exact Real.log_div (by norm_num) (by linarith)

/-- `|log x| ≤ 2 |x − 1|` for `x ≥ 1/2`. -/
private lemma abs_log_le {x : ℝ} (hx : 1 / 2 ≤ x) : |Real.log x| ≤ 2 * |x - 1| := by
  have hpos : 0 < x := by linarith
  have h1 := Real.log_le_sub_one_of_pos hpos
  have h2 := Real.one_sub_inv_le_log_of_pos hpos
  rcases le_or_gt 1 x with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h), abs_of_nonneg (by linarith)]
    linarith
  · rw [abs_of_neg (Real.log_neg hpos h), abs_of_neg (by linarith)]
    have : x⁻¹ ≤ 3 - 2 * x := by
      rw [inv_eq_one_div, div_le_iff₀ hpos]
      nlinarith [mul_nonneg (by linarith : 0 ≤ 2 * x - 1) (by linarith : 0 ≤ 1 - x)]
    linarith

/-- `K(w) = (log (1/2) − log w) / 2 + (log (1/2) − log (1 − w)) / 2` on `U`. -/
theorem K_eq {w : Fin 1 → ℝ} (hw : w ∈ U) :
    excessLoss q p w₀ w = (Real.log (1 / 2) - Real.log (w 0)) / 2
      + (Real.log (1 / 2) - Real.log (1 - w 0)) / 2 := by
  obtain ⟨h0, h1⟩ := hw
  rw [excessLoss, integral_q, loss_true h0, loss_false h1]

/-- `(2w − 1)² / 2 ≤ K(w)` on `U`. -/
theorem sq_le_K {w : Fin 1 → ℝ} (hw : w ∈ U) : (2 * w 0 - 1) ^ 2 / 2 ≤ excessLoss q p w₀ w := by
  rw [K_eq hw]
  obtain ⟨h0, h1⟩ := hw
  have h1' : 0 < 1 - w 0 := by linarith
  have hlog : Real.log (4 * w 0 * (1 - w 0)) ≤ 4 * w 0 * (1 - w 0) - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_mul (by positivity) h1'.ne', Real.log_mul (by norm_num) h0.ne'] at hlog
  have h4 : Real.log 4 = -2 * Real.log (1 / 2) := by
    rw [one_div, Real.log_inv, show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  nlinarith

theorem K_nonneg : ∀ w ∈ W, 0 ≤ excessLoss q p w₀ w := fun w hw ↦
  le_trans (by positivity) (sq_le_K (W_subset_U hw))

theorem rfv : RelativelyFiniteVariance q p w₀ W := by
  refine ⟨1 / 8, by norm_num, fun w hw ↦ ⟨?_, ?_⟩⟩
  · refine MemLp.of_bound (measurable_of_countable _).aestronglyMeasurable
      (max ‖logDensityRatio p w₀ true w‖ ‖logDensityRatio p w₀ false w‖)
          (Eventually.of_forall fun x ↦ ?_)
    cases x
    · exact le_max_right _ _
    · exact le_max_left _ _
  · obtain ⟨h0, h1⟩ := W_subset_U hw
    have ha : Real.log (1 / 2) - Real.log (w 0) = -Real.log (2 * w 0) := by
      rw [Real.log_mul two_ne_zero h0.ne', one_div, Real.log_inv]; ring
    have hb : Real.log (1 / 2) - Real.log (1 - w 0) = -Real.log (2 * (1 - w 0)) := by
      rw [Real.log_mul two_ne_zero (by linarith), one_div, Real.log_inv]; ring
    have ha' : (Real.log (1 / 2) - Real.log (w 0)) ^ 2 ≤ (2 * (2 * w 0 - 1)) ^ 2 := by
      rw [ha, sq_le_sq, abs_neg, abs_mul, abs_two]
      exact abs_log_le (by linarith [hw.1])
    have hb' : (Real.log (1 / 2) - Real.log (1 - w 0)) ^ 2 ≤ (2 * (2 * w 0 - 1)) ^ 2 := by
      rw [hb, sq_le_sq, abs_neg, abs_mul, abs_two, ← abs_neg (2 * w 0 - 1)]
      exact (abs_log_le (by linarith [hw.2])).trans_eq (by ring_nf)
    have hK := sq_le_K (W_subset_U hw)
    rw [integral_q, loss_true h0, loss_false h1]
    nlinarith

theorem continuousOn_loss : ∀ᵐ x ∂q, ContinuousOn (logDensityRatio p w₀ x) W :=
  Eventually.of_forall fun x ↦ by
    have hp : ∀ w ∈ W, 0 < p w x := fun w hw ↦ by
      cases x <;> simp [p] <;> linarith [hw.1, hw.2]
    have hc : Continuous fun w ↦ p w x := by
      cases x <;> simp only [p, Bool.false_eq_true, ↓reduceIte] <;> fun_prop
    exact ContinuousOn.log (continuousOn_const.div hc.continuousOn fun w hw ↦ (hp w hw).ne')
      fun w hw ↦ (div_pos (hp w₀ w₀_mem) (hp w hw)).ne'

/-- Fundamental condition I for every index `s ≥ 2`. -/
theorem fcI (s : ℝ≥0∞) [Fact (1 ≤ s)] (hs : 2 ≤ s) :
    FundamentalConditionI s q (logDensityRatio p w₀) (excessLoss q p w₀) W where
  two_le := hs
  K_eq := fun _ ↦ rfl
  ls_analytic := by
    refine ⟨U, isOpen_U, W_subset_U, (fun w ↦ (Real.log (1 / 2) - Real.log (w 0)) •
        indicatorConstLp s (measurableSet_singleton true) (measure_ne_top q _) (1 : ℝ)
      + (Real.log (1 / 2) - Real.log (1 - w 0)) •
        indicatorConstLp s (measurableSet_singleton false) (measure_ne_top q _) (1 : ℝ)), ?_, ?_⟩
    · intro w hw
      obtain ⟨h0, h1⟩ := hw
      have hproj : AnalyticAt ℝ (fun w : Fin 1 → ℝ ↦ w 0) w :=
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0).analyticAt w
      have ha : AnalyticAt ℝ (fun w : Fin 1 → ℝ ↦ Real.log (1 / 2) - Real.log (w 0)) w :=
        analyticAt_const.sub ((analyticAt_log h0).comp (f := fun w : Fin 1 → ℝ ↦ w 0) hproj)
      have hb : AnalyticAt ℝ (fun w : Fin 1 → ℝ ↦ Real.log (1 / 2) - Real.log (1 - w 0)) w :=
        analyticAt_const.sub ((analyticAt_log (by linarith)).comp (f := fun w : Fin 1 → ℝ ↦ 1 - w 0)
          (analyticAt_const.sub hproj))
      exact (ha.smul analyticAt_const).add (hb.smul analyticAt_const)
    · intro w hw
      obtain ⟨h0, h1⟩ := hw
      refine ((Lp.coeFn_add _ _).trans
        (((Lp.coeFn_smul _ _).trans (EventuallyEq.rfl.smul indicatorConstLp_coeFn)).add
          ((Lp.coeFn_smul _ _).trans (EventuallyEq.rfl.smul indicatorConstLp_coeFn)))).trans
        (Eventually.of_forall fun x ↦ ?_)
      cases x <;> simp [loss_true h0, loss_false h1]

theorem fcII : FundamentalConditionII φ W where
  semianalytic := by
    refine ⟨univ, 2, ![fun w ↦ w 0 - 1 / 4, fun w ↦ 3 / 4 - w 0], isOpen_univ, subset_univ _,
      ?_, fun w _ ↦ ?_⟩
    · intro i
      fin_cases i
      · exact ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0).analyticOnNhd
          univ).sub analyticOnNhd_const
      · exact analyticOnNhd_const.sub
          ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 ↦ ℝ) 0).analyticOnNhd univ)
    · simp only [W, mem_ofPred_eq, Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        sub_nonneg]
  factor := ⟨univ, isOpen_univ, subset_univ _, fun _ ↦ 1, fun _ ↦ 1, fun _ _ ↦ one_pos,
    contDiffOn_const, fun _ _ ↦ zero_le_one, analyticOnNhd_const, fun _ _ ↦ (one_mul 1).symm⟩

theorem measurePreserving (i : ℕ) : MeasurePreserving (Xs i) P q :=
  ⟨measurable_pi_apply i, Measure.infinitePi_map_eval (μ := fun _ ↦ q) i⟩

theorem indep : iIndepFun Xs P :=
  iIndepFun_infinitePi (P := fun _ ↦ q) (X := fun _ ↦ id) fun _ ↦ measurable_id

theorem K_germ : ∀ w ∈ W, excessLoss q p w₀ w = 0 → ¬ (excessLoss q p w₀ =ᶠ[𝓝 w] 0) := by
  intro w hw hK0 h
  have hw0 : w 0 = 1 / 2 := by
    have hsq := sq_le_K (W_subset_U hw)
    rw [hK0] at hsq
    have : (2 * w 0 - 1) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    linarith [(pow_eq_zero_iff two_ne_zero).mp this]
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp h
  set t := min (r / 2) (1 / 4) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have htr : t < r := (min_le_left _ _).trans_lt (by linarith)
  have ht4 : t ≤ 1 / 4 := min_le_right _ _
  have hdist : dist (fun _ : Fin 1 ↦ w 0 + t) w < r := by
    rw [dist_pi_lt_iff hr]
    intro b
    rw [Subsingleton.elim b 0, Real.dist_eq, add_sub_cancel_left, abs_of_pos ht0]
    exact htr
  have hK := hball hdist
  simp only [Pi.zero_apply] at hK
  have hsq := sq_le_K (w := fun _ ↦ w 0 + t) ⟨by linarith, by linarith⟩
  rw [hK, show 2 * (w 0 + t) - 1 = 2 * t by rw [hw0]; ring] at hsq
  have : 0 < (2 * t) ^ 2 / 2 := by positivity
  linarith

theorem φ_germ : ∀ w ∈ W, excessLoss q p w₀ w = 0 → ¬ (φ =ᶠ[𝓝 w] 0) := fun w _ _ h ↦
  one_ne_zero (h.eq_of_nhds : φ w = 0)

theorem vol_pos : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | excessLoss q p w₀ w < ε}, ENNReal.ofReal (φ w) := by
  intro ε hε
  have hcont : ContinuousAt (excessLoss q p w₀) w₀ := by
    have hU : U ∈ 𝓝 w₀ := isOpen_U.mem_nhds (W_subset_U w₀_mem)
    refine ContinuousAt.congr ?_ (eventuallyEq_of_mem hU fun w hw ↦ (K_eq hw).symm)
    have h0 : w₀ 0 ≠ 0 := by norm_num [w₀]
    have h1 : 1 - w₀ 0 ≠ 0 := by norm_num [w₀]
    have hp : ContinuousAt (fun w : Fin 1 → ℝ ↦ w 0) w₀ := (continuous_apply 0).continuousAt
    have ha : ContinuousAt (fun w : Fin 1 → ℝ ↦ Real.log (w 0)) w₀ :=
      (Real.continuousAt_log h0).comp (f := fun w : Fin 1 → ℝ ↦ w 0) hp
    have hb : ContinuousAt (fun w : Fin 1 → ℝ ↦ Real.log (1 - w 0)) w₀ :=
      (Real.continuousAt_log h1).comp (f := fun w : Fin 1 → ℝ ↦ 1 - w 0) (continuousAt_const.sub hp)
    exact ((continuousAt_const.sub ha).div_const _).add ((continuousAt_const.sub hb).div_const _)
  have hK0 : excessLoss q p w₀ w₀ = 0 := by rw [K_eq (W_subset_U w₀_mem)]; norm_num [w₀]
  have hev : ∀ᶠ w in 𝓝 w₀, excessLoss q p w₀ w < ε :=
    hcont.eventually_lt continuousAt_const (by rw [hK0]; exact hε)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hev
  have hm : 0 < min r (1 / 4) := lt_min hr (by norm_num)
  have hsub : Metric.ball w₀ (min r (1 / 4)) ⊆ W ∩ {w | excessLoss q p w₀ w < ε} := fun w hw ↦ by
    rw [Metric.mem_ball] at hw
    have h1 : |w 0 - 1 / 2| < 1 / 4 :=
      (dist_le_pi_dist w w₀ 0).trans_lt (hw.trans_le (min_le_right _ _))
    rw [abs_lt] at h1
    exact ⟨⟨by linarith [h1.1], by linarith [h1.2]⟩, hball (hw.trans_le (min_le_left _ _))⟩
  calc (0 : ℝ≥0∞) < volume (Metric.ball w₀ (min r (1 / 4))) :=
        Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr hm)
    _ ≤ volume (W ∩ {w | excessLoss q p w₀ w < ε}) := measure_mono hsub
    _ = ∫⁻ w in W ∩ {w | excessLoss q p w₀ w < ε}, ENNReal.ofReal (φ w) := by
        simp only [φ, ENNReal.ofReal_one, setLIntegral_one]

/-- **The free energy formula for the Bernoulli model**: every hypothesis of
`SingularLearningTheory.free_energy_formula` is discharged. -/
theorem free_energy_formula (β : ℝ) (hβ : 0 < β) :
    ∃ (lam : ℝ) (m : ℕ) (Rn : ℕ → (ℕ → Bool) → ℝ),
      0 < lam ∧ 1 ≤ m ∧ IsSingularityType (excessLoss q p w₀) φ W lam m ∧
      (∀ n : ℕ, 2 ≤ n → ∀ᵐ ω ∂P,
        freeEnergy p W φ β Xs n ω =
          n * β * empiricalNegativeLogLikelihood p Xs n ω w₀ + lam * Real.log n
          - ((m : ℝ) - 1) * Real.log (Real.log n) + Rn n ω) ∧
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (ξ : Ω' → ℝ), TendstoInDistribution Rn atTop ξ (fun _ ↦ P) P' := by
  obtain ⟨lam, m, hl, hm, htype, h⟩ :=
    SingularLearningTheory.free_energy_formula q p W w₀
      ⟨measurable_p, isCompact_W, p_pos, w₀_mem, rfv, fcI 2 le_rfl, continuousOn_loss⟩
      φ fcII ⟨K_germ, φ_germ, vol_pos⟩
  obtain ⟨Rn, h1, h2⟩ := h β hβ (ℕ → Bool) Xs P ⟨measurePreserving, indep⟩
  exact ⟨lam, m, Rn, hl, hm, htype, h1, h2⟩

end BernoulliModel
