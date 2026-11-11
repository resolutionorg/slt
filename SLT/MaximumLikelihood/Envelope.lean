/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Geometry
public import SLT.FreeEnergy.Discharge
public import SLT.MeasureTheory.Function.AsympUnifIntegrable
public import Mathlib.MeasureTheory.Integral.Prod
public import SLT.FreeEnergy.SamplewiseResolution
public import SLT.FreeEnergy.FundamentalConditions

/-!
# The relative envelope of the empirical loss

When the charts of a resolution atlas cover the parameters with $K < \delta$, the scaled
deviation of the empirical loss satisfies
$$\sqrt{n}\,|K_n(w) - K(w)| \le \sqrt{K(w)}\,H_n \quad\text{for all } w \in W,$$
with $H_n$ the larger of the norms of the empirical processes on the charts and on the tail
$\{K \ge \delta\}$. Under fundamental condition (I) at $s = 4$ and an analytic resolution of the
log density ratio, $H_n$ has uniformly bounded fourth moments. For a minimizer $\hat w$ of the
empirical loss the envelope localizes the scaled errors: $0 \le nK(\hat w) \le H_n^2$ and
$-H_n^2/4 \le nK_n(\hat w) \le 0$. Both scaled errors are therefore asymptotically uniformly
integrable, which turns their convergence in law into convergence of expectations in
[Wat09, Main Theorem 6.4].

## Main results

* `SingularLearningTheory.MaximumLikelihood.sampleLoss_chart_ae`: almost surely, on every chart,
  $nK_n(g(u)) = nu^{2k} + \sqrt{n}\,u^k\Psi_n(u)$ for the empirical process $\Psi_n$.
* `SingularLearningTheory.empiricalLoss_centered_tail`: where $K > 0$,
  $\sqrt{n}(K_n - K) = \sqrt{K}$ times the tail process.
* `SingularLearningTheory.MaximumLikelihood.relative_envelope_of_chart_and_tail`: the envelope on all
  of $W$.
* `SingularLearningTheory.MaximumLikelihood.exists_relative_envelope_fourth`: an envelope $H_n$ with
  uniformly bounded fourth moments that dominates the norm of the chart process.
* `SingularLearningTheory.MaximumLikelihood.mle_localization_ae`: the localization bounds on
  $nK(\hat w)$ and $nK_n(\hat w)$.
* `SingularLearningTheory.MaximumLikelihood.mle_aui_of_relative_envelope`: both scaled errors are
  asymptotically uniformly integrable.
* `SingularLearningTheory.MaximumLikelihood.mle_eventually_integrable_of_aui`: for a measurable
  estimator, both scaled errors are integrable for all large $n$.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.MaximumLikelihood

variable {d : ℕ}

/-- Remove one factor sqrt(n) from a centered sample-objective identity. -/
theorem centered_deviation_of_sample_identity {n : ℕ} (hn : 0 < n)
    {a b c : ℝ} (h : (n : ℝ) * a = (n : ℝ) * b + Real.sqrt n * c) :
    Real.sqrt n * (a - b) = c := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  have heq : Real.sqrt n * (Real.sqrt n * (a - b)) = Real.sqrt n * c := by
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    nlinarith [h]
  exact mul_left_cancel₀ hs heq

/-- The exact centered tail identity. This is algebra at one sample; no density
normalization, expectation, or logarithm-integrability assertion is used. -/
theorem _root_.SingularLearningTheory.empiricalLoss_centered_tail {X Ω : Type*}
    (K : (Fin d → ℝ) → ℝ) (f : X → (Fin d → ℝ) → ℝ) (Xs : ℕ → Ω → X)
    {n : ℕ} (hn : 0 < n) (ω : Ω) {w : Fin d → ℝ} (hK : 0 < K w) :
    Real.sqrt n * (empiricalLoss f Xs n ω w - K w) =
      Real.sqrt (K w) * tailProcess K f Xs n ω w := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : Real.sqrt n * Real.sqrt (K w) * tailProcess K f Xs n ω w =
      ∑ i ∈ Finset.range n, (f (Xs i ω) w - K w) := by
    rw [tailProcess, mul_comm, div_mul_cancel₀ _ (by positivity)]
  apply centered_deviation_of_sample_identity hn
  calc (n : ℝ) * empiricalLoss f Xs n ω w
      = (n : ℝ) * K w +
          Real.sqrt n * Real.sqrt (K w) * tailProcess K f Xs n ω w := by
        rw [hsum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, empiricalLoss, mul_div_cancel₀ _ hn'.ne']
        ring
    _ = (n : ℝ) * K w + Real.sqrt n *
        (Real.sqrt (K w) * tailProcess K f Xs n ω w) := by ring

section RelativeEnvelope

variable {X Ω Ω' ΩT : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  [MeasurableSpace Ω'] [MeasurableSpace ΩT]
  {q : Measure X} [IsProbabilityMeasure q]
  {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P']
  {PT : Measure ΩT} [IsProbabilityMeasure PT]
  {Xs : ℕ → Ω → X} {f : X → (Fin d → ℝ) → ℝ}
  {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W) (L : R.ResolvedLikelihood q f)

omit [IsProbabilityMeasure q] in
/-- The sample objective on every chart, on one common full-measure event.
The plus sign is essential: the supplied process is the centered field Ψ, while
the book's chart process is −Ψ. -/
theorem sampleLoss_chart_ae
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (E : EmpiricalProcessLimit q (fun x (u : ResolutionAtlas.Domain R) ↦ L.a u.1 x u.2) Xs P P')
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, ∀ α (u : cube d (R.b α)),
      (n : ℝ) * empiricalLoss f Xs n ω (R.g α u) =
        (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
          Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * E.Ψ n ω ⟨α, u⟩ := by
  have hall : ∀ᵐ ω ∂P, ∀ α, ∀ u : cube d (R.b α),
      empiricalLoss f Xs n ω (R.g α u) =
        (∏ j, (u : Fin d → ℝ) j ^ (2 * R.k α j)) -
          (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) *
            L.chartProcess Xs n ω α u :=
    ae_all_iff.mpr fun α ↦ L.empiricalLoss_comp_g Xs hX hlaw hn α
  have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hs : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn').ne'
  have hni : (n : ℝ) * (Real.sqrt n)⁻¹ = Real.sqrt n := by
    calc (n : ℝ) * (Real.sqrt n)⁻¹
        = (Real.sqrt n * Real.sqrt n) * (Real.sqrt n)⁻¹ := by
            rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
      _ = Real.sqrt n := by rw [mul_assoc, mul_inv_cancel₀ hs, mul_one]
  filter_upwards [hall, L.ae_chartProcess_eq E n] with ω hc hsign α u
  rw [hc α u, hsign]
  simp only [Pi.neg_apply, ContinuousMap.neg_apply, ResolutionAtlas.toChartFunctions_apply]
  rw [monomial_square]
  calc (n : ℝ) * ((∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 -
        (Real.sqrt n)⁻¹ * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * (-E.Ψ n ω ⟨α, u⟩))
      = (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        ((n : ℝ) * (Real.sqrt n)⁻¹) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) *
          E.Ψ n ω ⟨α, u⟩ := by ring
    _ = _ := by rw [hni]

omit [IsProbabilityMeasure q] in
/-- A relative fluctuation envelope on all of W. The tail process may live on an
independently chosen limit probability space; only its finite-sample functions are used.
The explicit coverage threshold need not equal R.δ. -/
private theorem relative_envelope_of_chart_and_tail
    (hK : ∀ w, K w = ∫ x, f x w ∂q) {δ : ℝ} (hδ : 0 < δ)
    [CompactSpace {w // w ∈ W ∧ δ ≤ K w}]
    (hcover : ∀ w ∈ W, K w < δ → ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (E : EmpiricalProcessLimit q (fun x (u : ResolutionAtlas.Domain R) ↦ L.a u.1 x u.2) Xs P P')
    (T : EmpiricalProcessLimit q
      (fun x (w : {w // w ∈ W ∧ δ ≤ K w}) ↦ f x w / Real.sqrt (K w)) Xs P PT)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P, ∀ w ∈ W,
      Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤
        Real.sqrt (K w) * max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖ := by
  have hn0 : 0 < n := by omega
  filter_upwards [sampleLoss_chart_ae R L hX hlaw E hn, T.Ψ_ae_eq n]
    with ω hc ht w hw
  by_cases hwlow : K w < δ
  · obtain ⟨α, u, hgu⟩ := hcover w hw hwlow
    subst w
    let h : ℝ := ∏ j, (u : Fin d → ℝ) j ^ R.k α j
    have hh0 : 0 ≤ h := monomial_nonneg
      (fun j ↦ u.property.1 j)
    have hKg : K (R.g α u) = h ^ 2 := ResolutionAtlas.K_g_eq_square R α u
    have hdev : Real.sqrt n *
        (empiricalLoss f Xs n ω (R.g α u) - K (R.g α u)) = h * E.Ψ n ω ⟨α, u⟩ := by
      apply centered_deviation_of_sample_identity hn0
      rw [hc α u, hKg]
      change (n : ℝ) * h ^ 2 + Real.sqrt n * h * E.Ψ n ω ⟨α, u⟩ =
        (n : ℝ) * h ^ 2 + Real.sqrt n * (h * E.Ψ n ω ⟨α, u⟩)
      ring
    have hnorm : |E.Ψ n ω ⟨α, u⟩| ≤ ‖E.Ψ n ω‖ := by
      simpa only [Real.norm_eq_abs] using (E.Ψ n ω).norm_coe_le_norm ⟨α, u⟩
    calc Real.sqrt n * |empiricalLoss f Xs n ω (R.g α u) - K (R.g α u)|
        = |Real.sqrt n * (empiricalLoss f Xs n ω (R.g α u) - K (R.g α u))| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = h * |E.Ψ n ω ⟨α, u⟩| := by rw [hdev, abs_mul, abs_of_nonneg hh0]
      _ ≤ h * ‖E.Ψ n ω‖ := mul_le_mul_of_nonneg_left hnorm hh0
      _ ≤ Real.sqrt (K (R.g α u)) * max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖ := by
          rw [hKg, Real.sqrt_sq hh0]
          exact mul_le_mul_of_nonneg_left (le_max_left _ _) hh0
  · have hwδ : δ ≤ K w := le_of_not_gt hwlow
    have hKw : 0 < K w := hδ.trans_le hwδ
    let v : {w // w ∈ W ∧ δ ≤ K w} := ⟨w, hw, hwδ⟩
    have htval : T.Ψ n ω v = tailProcess K f Xs n ω w := by
      rw [ht v, tailProcess_eq_empiricalProcess hK]
      rfl
    have hnorm : |tailProcess K f Xs n ω w| ≤ ‖T.Ψ n ω‖ := by
      rw [← htval, ← Real.norm_eq_abs]
      exact (T.Ψ n ω).norm_coe_le_norm v
    calc Real.sqrt n * |empiricalLoss f Xs n ω w - K w|
        = |Real.sqrt n * (empiricalLoss f Xs n ω w - K w)| := by
            rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
      _ = Real.sqrt (K w) * |tailProcess K f Xs n ω w| := by
          rw [empiricalLoss_centered_tail K f Xs hn0 ω hKw, abs_mul,
            abs_of_nonneg (Real.sqrt_nonneg _)]
      _ ≤ Real.sqrt (K w) * ‖T.Ψ n ω‖ :=
          mul_le_mul_of_nonneg_left hnorm (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt (K w) * max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖ :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) (Real.sqrt_nonneg _)

end RelativeEnvelope

section FourthMoments

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- The fourth moment of the maximum of two process norms is bounded by the sum
of their fourth moments, with no multiplicative constant. -/
private theorem max_norm_fourth_moment_le {U V : Type*} [TopologicalSpace U] [CompactSpace U]
    [TopologicalSpace V] [CompactSpace V]
    {Ψ : ℕ → Ω → C(U, ℝ)} {Φ : ℕ → Ω → C(V, ℝ)}
    (hΨm : ∀ n, Measurable (Ψ n))
    {CΨ CΦ : ℝ≥0∞}
    (hΨ : ∀ n, ∫⁻ ω, ‖Ψ n ω‖ₑ ^ 4 ∂P ≤ CΨ)
    (hΦ : ∀ n, ∫⁻ ω, ‖Φ n ω‖ₑ ^ 4 ∂P ≤ CΦ) (n : ℕ) :
    ∫⁻ ω, ‖max ‖Ψ n ω‖ ‖Φ n ω‖‖ₑ ^ 4 ∂P ≤ CΨ + CΦ := by
  have hpt : ∀ ω, ‖max ‖Ψ n ω‖ ‖Φ n ω‖‖ₑ ^ 4 ≤
      ‖Ψ n ω‖ₑ ^ 4 + ‖Φ n ω‖ₑ ^ 4 := by
    intro ω
    rcases le_total ‖Ψ n ω‖ ‖Φ n ω‖ with h | h
    · rw [max_eq_right h, enorm_norm]
      exact le_add_of_nonneg_left bot_le
    · rw [max_eq_left h, enorm_norm]
      exact le_add_of_nonneg_right bot_le
  calc ∫⁻ ω, ‖max ‖Ψ n ω‖ ‖Φ n ω‖‖ₑ ^ 4 ∂P
      ≤ ∫⁻ ω, (‖Ψ n ω‖ₑ ^ 4 + ‖Φ n ω‖ₑ ^ 4) ∂P := lintegral_mono hpt
    _ = (∫⁻ ω, ‖Ψ n ω‖ₑ ^ 4 ∂P) + ∫⁻ ω, ‖Φ n ω‖ₑ ^ 4 ∂P :=
        lintegral_add_left ((hΨm n).enorm.pow_const 4) _
    _ ≤ CΨ + CΦ := add_le_add (hΨ n) (hΦ n)

/-- The square of a uniformly fourth-moment-bounded real sequence is AUI. -/
private theorem asympUnifIntegrable_square_of_fourth_moment {H : ℕ → Ω → ℝ}
    {C : ℝ≥0∞} (hC : C ≠ ⊤) (hH : ∀ n, ∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P ≤ C) :
    AsympUnifIntegrable P (fun n ω ↦ (H n ω) ^ 2) := by
  apply asympUnifIntegrable_of_lintegral_sq_le hC
  refine Filter.Eventually.of_forall fun n ↦ ?_
  simpa only [enorm_pow, ← pow_mul] using hH n

end FourthMoments

section Construction

variable {X Ω Ω' : Type*} [MeasurableSpace X] [MeasurableSpace Ω] [MeasurableSpace Ω']
  {q : Measure X} [IsProbabilityMeasure q] {P : Measure Ω} [IsProbabilityMeasure P]
  {P' : Measure Ω'} [IsProbabilityMeasure P'] {Xs : ℕ → Ω → X}
  {f : X → (Fin d → ℝ) → ℝ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- Construct the relative envelope with its uniform fourth moment, from the
analytic hypotheses. The chart limit space P' is preserved; only a separate tail limit
is chosen. This theorem does not choose an estimator. -/
theorem exists_relative_envelope_fourth
    (I : FundamentalConditionI 4 q f K W) (L : R.AnalyticResolvedLikelihood 4 q f)
    (hW : IsCompact W) (hf_meas : ∀ w, Measurable fun x ↦ f x w)
    (hcont : ∀ᵐ x ∂q, ContinuousOn (f x) W)
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ w ∈ W, K w < δ → ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hX : ∀ i, Measurable (Xs i)) (hlaw : ∀ i, P.map (Xs i) = q)
    (hind : iIndepFun Xs P)
    (E : EmpiricalProcessLimit q (fun x (u : ResolutionAtlas.Domain R) ↦ L.a u.1 x u.2) Xs P P') :
    ∃ H : ℕ → Ω → ℝ,
      (∀ n, Measurable (H n)) ∧
      (∀ n ω, 0 ≤ H n ω) ∧
      (∀ n ω, ‖E.Ψ n ω‖ ≤ H n ω) ∧
      (∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ n, ∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P ≤ C) ∧
      (∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ w ∈ W,
        Real.sqrt n * |empiricalLoss f Xs n ω w - K w| ≤ Real.sqrt (K w) * H n ω) := by
  have : CompactSpace {w // w ∈ W ∧ δ ≤ K w} :=
    isCompact_iff_compactSpace.mp (I.isCompact_tail hW δ)
  obtain ⟨PT, hPT, ⟨T⟩⟩ :=
    I.exists_tail_empiricalProcessLimit hW hf_meas hcont hδ hX hlaw hind
  have := hPT
  let H : ℕ → Ω → ℝ := fun n ω ↦ max ‖E.Ψ n ω‖ ‖T.Ψ n ω‖
  obtain ⟨CE, hCE, hEn⟩ := L.momentBound_chart hX hlaw hind E
  obtain ⟨CT, hCT, hTn⟩ := I.momentBound_tail hW hcont hδ hX hlaw hind T
  have hE : ∀ n, ∫⁻ ω, ‖E.Ψ n ω‖ₑ ^ 4 ∂P ≤ CE := fun n ↦
    le_trans (lintegral_mono fun ω ↦
      pow_le_pow_left' (ContinuousMap.enorm_le_iSup_enorm _) 4) (hEn n)
  have hT : ∀ n, ∫⁻ ω, ‖T.Ψ n ω‖ₑ ^ 4 ∂P ≤ CT := fun n ↦
    le_trans (lintegral_mono fun ω ↦
      pow_le_pow_left' (ContinuousMap.enorm_le_iSup_enorm _) 4) (hTn n)
  refine ⟨H, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    exact (E.Ψ_measurable n).norm.max (T.Ψ_measurable n).norm
  · intro n ω
    exact (norm_nonneg _).trans (le_max_left _ _)
  · intro n ω
    exact le_max_left _ _
  · refine ⟨CE + CT, ENNReal.add_ne_top.mpr ⟨hCE, hCT⟩, fun n ↦ ?_⟩
    exact max_norm_fourth_moment_le E.Ψ_measurable hE hT n
  · intro n hn
    exact relative_envelope_of_chart_and_tail R L.toResolvedLikelihood
      I.K_eq hδ hcover hX hlaw E T hn

end Construction

section Localization

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {K : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  {Kn : ℕ → Ω → (Fin d → ℝ) → ℝ} {H : ℕ → Ω → ℝ}
  {ŵ : ℕ → Ω → Fin d → ℝ}

/-- Localize any a.e. feasible empirical minimizer. Universal parameter bounds stay
inside the a.e. event, so evaluation at the random estimator is legitimate. -/
theorem mle_localization_ae
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hH0 : ∀ n ω, 0 ≤ H n ω)
    (henv : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ w ∈ W,
      Real.sqrt n * |Kn n ω w - K w| ≤ Real.sqrt (K w) * H n ω)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hŵW : ∀ n, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W, Kn n ω (ŵ n ω) ≤ Kn n ω w)
    {n : ℕ} (hn : 1 ≤ n) :
    ∀ᵐ ω ∂P,
      0 ≤ (n : ℝ) * K (ŵ n ω) ∧
      (n : ℝ) * K (ŵ n ω) ≤ (H n ω) ^ 2 ∧
      -((H n ω) ^ 2) / 4 ≤ (n : ℝ) * Kn n ω (ŵ n ω) ∧
      (n : ℝ) * Kn n ω (ŵ n ω) ≤ 0 := by
  filter_upwards [henv n hn, hŵW n, hmin n] with ω henvω hŵω hminω
  have hS : ∀ w ∈ W, (n : ℝ) * Kn n ω w =
      (n : ℝ) * K w + Real.sqrt n * (Real.sqrt n * (Kn n ω w - K w)) := by
    intro w _
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg n)]
    ring
  have hpre : ∀ w ∈ W, |Real.sqrt n * (Kn n ω w - K w)| ≤
      Real.sqrt (K w) * H n ω := by
    intro w hw
    simpa only [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)] using henvω w hw
  have hloc := mle_localization hK0 (show 0 < n by omega) (hH0 n ω) hS hpre hw₀ hw₀K hŵω
    (fun w hw ↦ mul_le_mul_of_nonneg_left (hminω w hw) (Nat.cast_nonneg n))
  exact ⟨mul_nonneg (Nat.cast_nonneg n) (hK0 _ hŵω), hloc⟩

/-- Fourth moments of the relative envelope give AUI of both scaled MLE errors.
No measurability of the estimator is needed for this domination step; it is supplied
separately when invoking eventual integrability or convergence of expectations. -/
theorem mle_aui_of_relative_envelope
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hH0 : ∀ n ω, 0 ≤ H n ω)
    {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hHm : ∀ n, ∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P ≤ C)
    (henv : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ w ∈ W,
      Real.sqrt n * |Kn n ω w - K w| ≤ Real.sqrt (K w) * H n ω)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hŵW : ∀ n, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (hmin : ∀ n, ∀ᵐ ω ∂P, ∀ w ∈ W, Kn n ω (ŵ n ω) ≤ Kn n ω w) :
    AsympUnifIntegrable P (fun n ω ↦ (n : ℝ) * K (ŵ n ω)) ∧
      AsympUnifIntegrable P (fun n ω ↦ (n : ℝ) * Kn n ω (ŵ n ω)) := by
  have hA := asympUnifIntegrable_square_of_fourth_moment hC hHm
  have hb : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P,
      0 ≤ (n : ℝ) * K (ŵ n ω) ∧
      (n : ℝ) * K (ŵ n ω) ≤ (H n ω) ^ 2 ∧
      -((H n ω) ^ 2) / 4 ≤ (n : ℝ) * Kn n ω (ŵ n ω) ∧
      (n : ℝ) * Kn n ω (ŵ n ω) ≤ 0 :=
    fun n hn ↦ mle_localization_ae hK0 hH0 henv hw₀ hw₀K hŵW hmin hn
  constructor
  · apply hA.of_abs_le
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hb n hn] with ω hω
    rw [abs_of_nonneg hω.1]
    exact hω.2.1
  · apply hA.of_abs_le
    filter_upwards [eventually_ge_atTop 1] with n hn
    filter_upwards [hb n hn] with ω hω
    rw [abs_of_nonpos hω.2.2.2]
    nlinarith [hω.2.2.1, sq_nonneg (H n ω)]

end Localization

section Measurability

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]
  {q : Measure X} [IsProbabilityMeasure q]
  {K : (Fin d → ℝ) → ℝ} {f : X → (Fin d → ℝ) → ℝ}
  {Xs : ℕ → Ω → X} {ŵ : ℕ → Ω → Fin d → ℝ}

/-- Global measurability of K from the integral definition, even outside W and
without any integrability claim there. Bochner integration is totalized. -/
theorem measurable_K_of_integral (hf : Measurable (Function.uncurry f))
    (hK : ∀ w, K w = ∫ x, f x w ∂q) : Measurable K := by
  have heq : K = fun w ↦ ∫ x, f x w ∂q := funext hK
  rw [heq]
  exact hf.stronglyMeasurable.integral_prod_left.measurable

theorem measurable_scaled_generalization (hK : Measurable K)
    (hŵ : ∀ n, Measurable (ŵ n)) (n : ℕ) :
    Measurable fun ω ↦ (n : ℝ) * K (ŵ n ω) :=
  measurable_const.mul (hK.comp (hŵ n))

theorem measurable_scaled_training (hf : Measurable (Function.uncurry f))
    (hX : ∀ i, Measurable (Xs i)) (hŵ : ∀ n, Measurable (ŵ n)) (n : ℕ) :
    Measurable fun ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω) :=
  measurable_const.mul
    ((measurable_uncurry_empiricalLoss hf hX n).comp (measurable_id.prodMk (hŵ n)))

/-- The measurability inputs needed to turn the two AUI conclusions into the
requested eventual integrability. The two integrals are taken separately only here,
after domination of each scaled excess loss has been established. -/
theorem mle_eventually_integrable_of_aui {P : Measure Ω} [IsProbabilityMeasure P]
    (hf : Measurable (Function.uncurry f)) (hK : ∀ w, K w = ∫ x, f x w ∂q)
    (hX : ∀ i, Measurable (Xs i)) (hŵ : ∀ n, Measurable (ŵ n))
    (hG : AsympUnifIntegrable P (fun n ω ↦ (n : ℝ) * K (ŵ n ω)))
    (hT : AsympUnifIntegrable P
      (fun n ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω))) :
    ∀ᶠ n : ℕ in atTop,
      Integrable (fun ω ↦ (n : ℝ) * K (ŵ n ω)) P ∧
      Integrable (fun ω ↦ (n : ℝ) * empiricalLoss f Xs n ω (ŵ n ω)) P := by
  have hKm := measurable_K_of_integral hf hK
  have hGi := hG.eventually_integrable fun n ↦
    (measurable_scaled_generalization hKm hŵ n).aestronglyMeasurable
  have hTi := hT.eventually_integrable fun n ↦
    (measurable_scaled_training hf hX hŵ n).aestronglyMeasurable
  exact hGi.and hTi

end Measurability
end SingularLearningTheory.MaximumLikelihood
