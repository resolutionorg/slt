/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MeasureTheory.Integral.Lebesgue.Minkowski
public import SLT.Analysis.Analytic.Monomials
public import SLT.MeasureTheory.Constructions.BorelSpace.Tsum
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Analysis.Analytic.Basic

/-!
# Local `L²(q)`-expansions of the integrand

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 4.2.2], as used in the proofs of | |
| [Hit26, Lemma 4.2.4] and | |
| [Hit26, Lemma 4.2.8] | `L2Expansion`,
`HasFPowerSeriesOnBall.exists_l2Expansion` |

[Hit26] expands `f(x, w) = Σ_α a_α(x) (w − w*)^α` around each `w* ∈ W` with coefficients
`a_α ∈ L^s(q)` and `Σ_α ‖a_α‖_s r^{|α|} < ∞`, and bounds `ψ_n` on the ball by the series of the
coefficient processes. `L2Expansion q f B` records what those proofs use of such an expansion on
a patch `B`: countably many coefficients `b_i ∈ L²(q)` with measurable representatives, monomials
`m_i` bounded by `c_i` and `lip_i`-Lipschitz on `B`, summable weights `Σ c_i ‖b_i‖₂`,
`Σ lip_i ‖b_i‖₂`, and the samplewise identity `f(x, u) = Σ_i b_i(x) m_i(u)`.

`HasFPowerSeriesOnBall.exists_l2Expansion` produces one from a power series `F : ℝ^d → L²(q)` at
`c₀`
(`HasFPowerSeriesOnBall`), on every patch mapped by a `1`-Lipschitz `e : U → ℝ^d` into a small
ball around `c₀`: the coefficients are measurable representatives of `p_k(e_{j₁}, …, e_{j_k})`,
`j : Fin k → Fin d`, and the monomials are `∏ᵢ (e(u) − c₀)_{jᵢ}`. The samplewise identity holds
for each `u` almost everywhere; `L2Expansion.ae_forall_hasSum` upgrades it to a common null set
when `f(x, ·)` is continuous on `B` for almost every `x` (the chapter's standing hypothesis),
by density of a countable subset of `B`.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {X : Type*} [MeasurableSpace X] {q : Measure X} {U : Type*} [PseudoMetricSpace U]

/-- An `L²(q)`-expansion of `f` on the patch `B`: `f(x, u) = Σ_i b_i(x) m_i(u)` for `u ∈ B`,
almost everywhere for each `u`, with `|m_i| ≤ c_i` and `|m_i(u) − m_i(v)| ≤ lip_i dist(u, v)` on
`B`, and `Σ_i c_i ‖b_i‖₂`, `Σ_i lip_i ‖b_i‖₂` finite. -/
structure L2Expansion (q : Measure X) (f : X → U → ℝ) (B : Set U) where
  /-- The countable index type of the terms of the expansion. -/
  ι : Type
  [countable : Countable ι]
  /-- The coefficients $b_i \in L^2(q)$, as measurable functions on `X`. -/
  b : ι → X → ℝ
  b_measurable : ∀ i, Measurable (b i)
  b_memLp : ∀ i, MemLp (b i) 2 q
  /-- The functions $m_i$ on `U` that the coefficients multiply. In the expansions built by
  `HasFPowerSeriesOnBall.exists_l2Expansion` they are monomials. -/
  m : ι → U → ℝ
  /-- The bounds $|m_i| \le c_i$ on the patch `B`. -/
  c : ι → ℝ
  /-- The Lipschitz constants of the functions $m_i$ on the patch `B`. -/
  lip : ι → ℝ
  c_nonneg : ∀ i, 0 ≤ c i
  lip_nonneg : ∀ i, 0 ≤ lip i
  abs_m_le : ∀ i, ∀ u ∈ B, |m i u| ≤ c i
  abs_m_sub_le : ∀ i, ∀ u ∈ B, ∀ v ∈ B, |m i u - m i v| ≤ lip i * dist u v
  summable_c : Summable fun i ↦ c i * (eLpNorm (b i) 2 q).toReal
  summable_lip : Summable fun i ↦ lip i * (eLpNorm (b i) 2 q).toReal
  summable_abs : ∀ᵐ x ∂q, Summable fun i ↦ |b i x| * c i
  expansion : ∀ u ∈ B, ∀ᵐ x ∂q, HasSum (fun i ↦ b i x * m i u) (f x u)

attribute [instance] L2Expansion.countable

namespace L2Expansion

variable {f : X → U → ℝ} {B : Set U} (E : L2Expansion q f B)

/-- The coefficients lie in `L^s(q)` with `Σ_i c_i ‖b_i‖_s < ∞` ([Hit26]'s `L^s(q)`-valued
analyticity; `s = 4` for [Wat09, Theorem 5.8] in the expectation part of the free energy formula).
-/
@[expose] def HigherMoment (s : ℝ≥0∞) : Prop :=
  (∀ i, MemLp (E.b i) s q) ∧ Summable fun i ↦ E.c i * (eLpNorm (E.b i) s q).toReal

theorem continuousOn_m (i : E.ι) : ContinuousOn (E.m i) B :=
  (LipschitzOnWith.of_dist_le_mul fun u hu v hv ↦ by
    rw [Real.dist_eq, Real.coe_toNNReal _ (E.lip_nonneg i)]
    exact E.abs_m_sub_le i u hu v hv).continuousOn

theorem summable_mul {x : X} (hx : Summable fun i ↦ |E.b i x| * E.c i) {u : U} (hu : u ∈ B) :
    Summable fun i ↦ E.b i x * E.m i u :=
  hx.of_norm_bounded fun i ↦ by
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (E.abs_m_le i u hu) (abs_nonneg _)

/-- The series `u ↦ Σ_i b_i(x) m_i(u)` is continuous on `B` where the majorant is summable. -/
protected theorem continuousOn_tsum {x : X} (hx : Summable fun i ↦ |E.b i x| * E.c i) :
    ContinuousOn (fun u ↦ ∑' i, E.b i x * E.m i u) B := by
  refine _root_.continuousOn_tsum (fun i ↦ (E.continuousOn_m i).const_smul (E.b i x)) hx
    fun i u hu ↦ ?_
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left (E.abs_m_le i u hu) (abs_nonneg _)

/-- An expansion of `r` is an expansion of any `f` with `f(·, u) = r(·, u)` a.e. for `u ∈ B`. -/
@[expose] protected def congr {r : X → U → ℝ} (E : L2Expansion q r B)
    (h : ∀ u ∈ B, (fun x ↦ r x u) =ᵐ[q] fun x ↦ f x u) : L2Expansion q f B :=
  { E with
    expansion := fun u hu ↦ by
      filter_upwards [E.expansion u hu, h u hu] with x hx hx'
      rw [← hx']
      exact hx }

protected theorem HigherMoment.congr {r : X → U → ℝ} {E : L2Expansion q r B} {s : ℝ≥0∞}
    (h4 : E.HigherMoment s) (h : ∀ u ∈ B, (fun x ↦ r x u) =ᵐ[q] fun x ↦ f x u) :
    (E.congr h).HigherMoment s := h4

/-- The samplewise identity with a common null set: when `f(x, ·)` is continuous on `B` for
almost every `x`, the expansion holds for almost every `x` simultaneously for all `u ∈ B`
(identify on a countable dense subset of `B`, then by continuity). -/
theorem ae_forall_hasSum (hB : TopologicalSpace.IsSeparable B)
    (hf : ∀ᵐ x ∂q, ContinuousOn (f x) B) :
    ∀ᵐ x ∂q, ∀ u ∈ B, HasSum (fun i ↦ E.b i x * E.m i u) (f x u) := by
  obtain ⟨D, hDB, hDc, hBD⟩ := hB.exists_countable_dense_subset
  have h1 : ∀ᵐ x ∂q, ∀ u ∈ D, HasSum (fun i ↦ E.b i x * E.m i u) (f x u) :=
    (ae_ball_iff hDc).mpr fun u hu ↦ E.expansion u (hDB hu)
  filter_upwards [h1, E.summable_abs, hf] with x hx hsum hcont
  have hg : ContinuousOn (fun u ↦ ∑' i, E.b i x * E.m i u) B := E.continuousOn_tsum hsum
  have heq : EqOn (f x) (fun u ↦ ∑' i, E.b i x * E.m i u) B :=
    EqOn.of_subset_closure (fun u hu ↦ (hx u hu).tsum_eq.symm) hcont hg hDB hBD
  intro u hu
  rw [heq hu]
  exact (E.summable_mul hsum hu).hasSum

end L2Expansion

/-! ### From a power series in `L²(q)` to an `L²(q)`-expansion -/

/-- The coercion to functions of a finite sum in `L^p` is the sum of the coercions, a.e. -/
private theorem _root_.MeasureTheory.Lp.coeFn_finset_sum {ι : Type*} {p : ℝ≥0∞} (s : Finset ι)
    (g : ι → Lp ℝ p q) : ⇑(∑ i ∈ s, g i) =ᵐ[q] fun x ↦ ∑ i ∈ s, g i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Lp.coeFn_zero ℝ p q
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [Lp.coeFn_add (g a) (∑ i ∈ s, g i), ih] with x h1 h2
    rw [h1, Pi.add_apply, h2, Finset.sum_insert ha]

namespace PowerSeriesExpansion

variable {d : ℕ} {s : ℝ≥0∞} [Fact (1 ≤ s)]

/-- The index set of the monomial expansion: a degree `k` and a tuple `j : Fin k → Fin d`. -/
private abbrev Index (d : ℕ) : Type := Σ k : ℕ, (Fin k → Fin d)

variable (p : FormalMultilinearSeries ℝ (Fin d → ℝ) (Lp ℝ s q))

/-- The coefficient `p_k(e_{j₁}, …, e_{j_k}) ∈ L^s(q)`. -/
private noncomputable def coef (i : Index d) : Lp ℝ s q := p i.1 fun l ↦ Pi.single (i.2 l) 1

/-- A measurable representative of `coef p i`. -/
private noncomputable def coefRep (i : Index d) : X → ℝ :=
  AEStronglyMeasurable.mk (coef p i : X → ℝ) (Lp.aestronglyMeasurable _)

private theorem coefRep_ae_eq (i : Index d) : coefRep p i =ᵐ[q] coef p i :=
  (Lp.aestronglyMeasurable (coef p i)).ae_eq_mk.symm

private theorem measurable_coefRep (i : Index d) : Measurable (coefRep p i) :=
  (Lp.aestronglyMeasurable (coef p i)).stronglyMeasurable_mk.measurable

private theorem memLp_coefRep (i : Index d) : MemLp (coefRep p i) s q :=
  (Lp.memLp (coef p i)).ae_eq (coefRep_ae_eq p i).symm

private theorem eLpNorm_coefRep (i : Index d) : eLpNorm (coefRep p
    i) s q = ENNReal.ofReal ‖coef p i‖ := by
  rw [eLpNorm_congr_ae (coefRep_ae_eq p i), Lp.norm_def,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]

private theorem toReal_eLpNorm_coefRep (i : Index d) : (eLpNorm (coefRep p i) s
    q).toReal = ‖coef p i‖ := by
  rw [eLpNorm_coefRep, ENNReal.toReal_ofReal (norm_nonneg _)]

private theorem norm_coef_le (i : Index d) : ‖coef p i‖ ≤ ‖p i.1‖ :=
  ContinuousMultilinearMap.norm_apply_single_le (p i.1) i.2

/-- The monomial `∏ₗ (e(u) − c₀)_{jₗ}`. -/
private def monomial (c₀ : Fin d → ℝ) (e : U → Fin d → ℝ) (i : Index d) (u : U) : ℝ :=
  ∏ l, (e u - c₀) (i.2 l)

private theorem apply_const_eq_sum_coef (y : Fin d → ℝ) (k : ℕ) :
    p k (fun _ ↦ y) = ∑ j : Fin k → Fin d, (∏ l, y (j l)) • coef p ⟨k, j⟩ :=
  ContinuousMultilinearMap.apply_const_eq_sum (p k) y

/-- Summability over the index set of a degree-wise weight times the coefficient norms. -/
private theorem summable_weight {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hs : Summable fun k ↦ ‖p k‖ * (d : ℝ) ^ k * w k) :
    Summable fun i : Index d ↦ w i.1 * ‖coef p i‖ := by
  refine (summable_sigma_of_nonneg fun i ↦ mul_nonneg (hw i.1) (norm_nonneg _)).mpr
    ⟨fun k ↦ Summable.of_finite, ?_⟩
  refine Summable.of_nonneg_of_le (fun k ↦ tsum_nonneg fun j ↦ mul_nonneg (hw k) (norm_nonneg _))
    (fun k ↦ ?_) hs
  rw [tsum_fintype]
  calc ∑ j : Fin k → Fin d, w k * ‖coef p ⟨k, j⟩‖
      ≤ ∑ j : Fin k → Fin d, w k * ‖p k‖ :=
        Finset.sum_le_sum fun j _ ↦ mul_le_mul_of_nonneg_left (norm_coef_le p ⟨k, j⟩) (hw k)
    _ = ‖p k‖ * (d : ℝ) ^ k * w k := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
          Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

variable [IsProbabilityMeasure q]

/-- The weighted series of the coefficient representatives converges almost everywhere when the
weighted series of `L²`-norms does (the `L¹` majorant `Σ_i w_i |b_i(x)|` is integrable). -/
private theorem ae_summable_abs_mul {w : Index d → ℝ} (hw : ∀ i, 0 ≤ w i)
    (hs : Summable fun i ↦ w i * ‖coef p i‖) :
    ∀ᵐ x ∂q, Summable fun i ↦ |coefRep p i x| * w i := by
  have hfin : ∫⁻ x, ∑' i, ‖coefRep p i x‖ₑ * ENNReal.ofReal (w i) ∂q < ⊤ := by
    rw [lintegral_tsum fun i ↦ ((measurable_coefRep p i).enorm.mul_const _).aemeasurable]
    calc ∑' i, ∫⁻ x, ‖coefRep p i x‖ₑ * ENNReal.ofReal (w i) ∂q
        = ∑' i, (∫⁻ x, ‖coefRep p i x‖ₑ ∂q) * ENNReal.ofReal (w i) := by
          simp_rw [lintegral_mul_const _ (measurable_coefRep p _).enorm]
      _ ≤ ∑' i, ENNReal.ofReal (w i * ‖coef p i‖) := by
          refine ENNReal.tsum_le_tsum fun i ↦ ?_
          rw [← eLpNorm_one_eq_lintegral_enorm (measurable_coefRep p i).aestronglyMeasurable,
            ENNReal.ofReal_mul (hw i), ← eLpNorm_coefRep, mul_comm]
          gcongr
          exact eLpNorm_le_eLpNorm_of_exponent_le Fact.out
      _ = ENNReal.ofReal (∑' i, w i * ‖coef p i‖) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun i ↦ mul_nonneg (hw i) (norm_nonneg _)) hs).symm
      _ < ⊤ := ENNReal.ofReal_lt_top
  filter_upwards [ae_lt_top (Measurable.tsum fun i ↦
    (measurable_coefRep p i).enorm.mul_const _) hfin.ne] with x hx
  have hx' : ∑' i, ((‖coefRep p i x‖₊ * (w i).toNNReal : ℝ≥0) : ℝ≥0∞) ≠ ⊤ := by
    refine ne_of_lt (lt_of_eq_of_lt ?_ hx)
    congr 1
  have := ENNReal.tsum_coe_ne_top_iff_summable.mp hx'
  have := NNReal.summable_coe.mpr this
  refine this.congr fun i ↦ ?_
  rw [NNReal.coe_mul, coe_nnnorm, Real.norm_eq_abs, Real.coe_toNNReal _ (hw i)]

variable {p}

/-- [Hit26, Definition 4.2.2], in the form the proofs of
[Hit26, Lemma 4.2.4], [Hit26, Lemma 4.2.8] and
[Hit26, Lemma 5.2.3] use: a power series `F : ℝ^d → L²(q)` at
`c₀` yields, on every patch `B` mapped `1`-Lipschitz by `e` into a small closed ball around `c₀`, a
samplewise representative `r(x, u) = Σ_i b_i(x) m_i(u)` of `F(e(u))`, measurable in `x`, with an
`L²(q)`-expansion. -/
theorem _root_.HasFPowerSeriesOnBall.exists_l2Expansion_repr (hs : 2 ≤ s)
    {F : (Fin d → ℝ) → Lp ℝ s q} {c₀ : Fin d → ℝ}
    {r : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F p c₀ r) (e : U → Fin d → ℝ) :
    ∃ ρ > 0, ∀ B : Set U, (∀ u ∈ B, dist (e u) c₀ ≤ ρ) →
      (∀ u ∈ B, ∀ v ∈ B, dist (e u) (e v) ≤ dist u v) →
      ∃ rep : X → U → ℝ, (∀ u, Measurable fun x ↦ rep x u) ∧ (∀ᵐ x ∂q, ContinuousOn (rep x) B) ∧
        (∀ u ∈ B, edist (e u) c₀ < r ∧ (fun x ↦ rep x u) =ᵐ[q] F (e u)) ∧
        ∃ E : L2Expansion q rep B, E.HigherMoment s := by
  obtain ⟨R, -, hR0, hRr⟩ := ENNReal.lt_iff_exists_real_btwn.mp hF.r_pos
  have hR : 0 < R := ENNReal.ofReal_pos.mp hR0
  set ρ : ℝ := R / (2 * (d + 1)) with hρ
  have hρ0 : 0 < ρ := by positivity
  have hρR : 2 * (d + 1) * ρ ≤ R := le_of_eq (by rw [hρ]; field_simp)
  obtain ⟨hsum_c, hsum_lip⟩ := FormalMultilinearSeries.summable_weights p hR (hRr.trans_le hF.r_le)
      hρ0.le hρR
  refine ⟨ρ, hρ0, fun B hB he ↦ ?_⟩
  have hc : Summable fun i : Index d ↦ ρ ^ i.1 * ‖coef p i‖ :=
    summable_weight p (w := fun k ↦ ρ ^ k) (fun k ↦ pow_nonneg hρ0.le k) hsum_c
  have hlip : Summable fun i : Index d ↦ (i.1 * ρ ^ (i.1 - 1)) * ‖coef p i‖ :=
    summable_weight p (w := fun k ↦ k * ρ ^ (k - 1)) (fun k ↦ by positivity) hsum_lip
  have habs := ae_summable_abs_mul p (fun i : Index d ↦ pow_nonneg hρ0.le i.1) hc
  -- the monomial bounds on `B`
  have hmb : ∀ i : Index d, ∀ u ∈ B, |monomial c₀ e i u| ≤ ρ ^ i.1 := fun i u hu ↦
    Finset.abs_prod_le_pow _ fun l ↦ (norm_le_pi_norm (e u - c₀) (i.2 l)).trans
      (by rw [← dist_eq_norm]; exact hB u hu)
  have hml : ∀ i : Index d, ∀ u ∈ B, ∀ v ∈ B,
      |monomial c₀ e i u - monomial c₀ e i v| ≤ (i.1 * ρ ^ (i.1 - 1)) * dist u v := by
    intro i u hu v hv
    refine Finset.abs_prod_sub_prod_le hρ0.le _ _
      (fun l ↦ (norm_le_pi_norm (e u - c₀) (i.2 l)).trans (by rw [← dist_eq_norm]; exact hB u hu))
      (fun l ↦ (norm_le_pi_norm (e v - c₀) (i.2 l)).trans (by rw [← dist_eq_norm]; exact hB v hv))
      fun l ↦ ?_
    have : (e u - c₀) (i.2 l) - (e v - c₀) (i.2 l) = (e u - e v) (i.2 l) := by simp
    rw [this]
    exact (norm_le_pi_norm (e u - e v) (i.2 l)).trans (by rw [← dist_eq_norm]; exact he u hu v hv)
  have h2s : ∀ i : Index d, (eLpNorm (coefRep p i) 2 q).toReal ≤ ‖coef p i‖ := fun i ↦ by
    rw [← toReal_eLpNorm_coefRep p i]
    exact ENNReal.toReal_mono (memLp_coefRep p i).eLpNorm_ne_top
      (eLpNorm_le_eLpNorm_of_exponent_le hs)
  let E : L2Expansion q (fun x u ↦ ∑' i : Index d, coefRep p i x * monomial c₀ e i u) B :=
    ⟨Index d, coefRep p, measurable_coefRep p, fun i ↦ (memLp_coefRep p i).mono_exponent hs,
      monomial c₀ e, fun i ↦ ρ ^ i.1, fun i ↦ i.1 * ρ ^ (i.1 - 1), fun i ↦ pow_nonneg hρ0.le _,
      fun i ↦ by positivity, hmb, hml,
      hc.of_nonneg_of_le (fun i ↦ mul_nonneg (pow_nonneg hρ0.le _) ENNReal.toReal_nonneg)
        (fun i ↦ mul_le_mul_of_nonneg_left (h2s i) (pow_nonneg hρ0.le _)),
      hlip.of_nonneg_of_le (fun i ↦ mul_nonneg (by positivity) ENNReal.toReal_nonneg)
        (fun i ↦ mul_le_mul_of_nonneg_left (h2s i) (by positivity)), habs, fun u hu ↦ by
        filter_upwards [habs] with x hx
        exact (hx.of_norm_bounded fun i ↦ by
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_left (hmb i u hu) (abs_nonneg _)).hasSum⟩
  refine ⟨fun x u ↦ ∑' i : Index d, coefRep p i x * monomial c₀ e i u,
    fun u ↦ Measurable.real_tsum fun i ↦ (measurable_coefRep p i).mul_const _, ?_, ?_,
    ⟨E, memLp_coefRep p, by
      change Summable fun i : Index d ↦ ρ ^ i.1 * (eLpNorm (coefRep p i) s q).toReal
      simpa only [toReal_eLpNorm_coefRep] using hc⟩⟩
  · filter_upwards [habs] with x hx
    exact E.continuousOn_tsum hx
  -- the representative property for a fixed `u ∈ B`
  intro u hu
  have hball : e u - c₀ ∈ Metric.eball (0 : Fin d → ℝ) r := by
    rw [Metric.mem_eball, edist_zero_right, ← edist_eq_enorm_sub, edist_dist]
    calc ENNReal.ofReal (dist (e u) c₀) ≤ ENNReal.ofReal ρ := ENNReal.ofReal_le_ofReal (hB u hu)
      _ < ENNReal.ofReal R := (ENNReal.ofReal_lt_ofReal_iff hR).mpr (by
          rw [hρ]; exact div_lt_self hR (by linarith [(d.cast_nonneg : (0 : ℝ) ≤ d)]))
      _ < r := hRr
  have hedist : edist (e u) c₀ < r := by
    rwa [Metric.mem_eball, edist_zero_right, ← edist_eq_enorm_sub] at hball
  have hS := hF.hasSum hball
  rw [add_sub_cancel] at hS
  -- the partial sums in `L²(q)` and their representatives
  set S : ℕ → Lp ℝ s q := fun N ↦
    ∑ k ∈ Finset.range N, ∑ j : Fin k → Fin d, monomial c₀ e ⟨k, j⟩ u • coef p ⟨k, j⟩ with hSdef
  have hStend : Tendsto S atTop (𝓝 (F (e u))) := by
    have := hS.tendsto_sum_nat
    refine this.congr fun N ↦ ?_
    simp only [hSdef]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [apply_const_eq_sum_coef]
    rfl
  set sN : ℕ → X → ℝ := fun N x ↦
    ∑ k ∈ Finset.range N, ∑ j : Fin k → Fin d, coefRep p ⟨k, j⟩ x * monomial c₀ e ⟨k, j⟩ u
    with hsdef
  have hs_meas : ∀ N, Measurable (sN N) := fun N ↦
    Finset.measurable_sum _ fun k _ ↦ Finset.measurable_sum _ fun j _ ↦
      (measurable_coefRep p _).mul_const _
  have hrep : ∀ N, (S N : X → ℝ) =ᵐ[q] sN N := by
    have h1 : ∀ᵐ x ∂q, ∀ (k : ℕ) (j : Fin k → Fin d),
        ((monomial c₀ e ⟨k, j⟩ u • coef p ⟨k, j⟩ : Lp ℝ s q) : X → ℝ) x
          = coefRep p ⟨k, j⟩ x * monomial c₀ e ⟨k, j⟩ u := by
      rw [ae_all_iff]
      intro k
      rw [ae_all_iff]
      intro j
      filter_upwards [Lp.coeFn_smul (monomial c₀ e ⟨k, j⟩ u) (coef p ⟨k, j⟩),
        coefRep_ae_eq p ⟨k, j⟩] with x hx hx'
      rw [hx, Pi.smul_apply, smul_eq_mul, hx', mul_comm]
    have h2 : ∀ᵐ x ∂q, ∀ k : ℕ,
        ((∑ j : Fin k → Fin d, monomial c₀ e ⟨k, j⟩ u • coef p ⟨k, j⟩ : Lp ℝ s q) : X → ℝ) x
          = ∑ j : Fin k → Fin d,
            ((monomial c₀ e ⟨k, j⟩ u • coef p ⟨k, j⟩ : Lp ℝ s q) : X → ℝ) x := by
      rw [ae_all_iff]
      intro k
      exact Lp.coeFn_finset_sum _ _
    have h3 : ∀ᵐ x ∂q, ∀ N : ℕ, (S N : X → ℝ) x = ∑ k ∈ Finset.range N,
        ((∑ j : Fin k → Fin d, monomial c₀ e ⟨k, j⟩ u • coef p ⟨k, j⟩ : Lp ℝ s q) : X → ℝ) x := by
      rw [ae_all_iff]
      intro N
      exact Lp.coeFn_finset_sum _ _
    intro N
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [hx3 N, hsdef]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hx2 k]
    exact Finset.sum_congr rfl fun j _ ↦ hx1 k j
  have hL : Tendsto (fun N ↦ eLpNorm (sN N - (F (e u) : X → ℝ)) s q) atTop (𝓝 0) := by
    have heq : ∀ N, eLpNorm (sN N - (F (e u) : X → ℝ)) s q = ENNReal.ofReal ‖S N - F (e u)‖ := by
      intro N
      rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
      refine eLpNorm_congr_ae ?_
      filter_upwards [hrep N, Lp.coeFn_sub (S N) (F (e u))] with x hx hx'
      rw [Pi.sub_apply, hx', Pi.sub_apply, hx]
    simp_rw [heq]
    have := (tendsto_iff_norm_sub_tendsto_zero.mp hStend)
    simpa using ENNReal.tendsto_ofReal this
  have hpt : ∀ᵐ x ∂q, Tendsto (fun N ↦ sN N x) atTop
      (𝓝 (∑' i : Index d, coefRep p i x * monomial c₀ e i u)) := by
    filter_upwards [habs] with x hx
    have hsum : Summable fun i : Index d ↦ coefRep p i x * monomial c₀ e i u :=
      hx.of_norm_bounded fun i ↦ by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_left (hmb i u hu) (abs_nonneg _)
    have hsig := hsum.hasSum.sigma (γ := fun k ↦ Fin k → Fin d) fun k ↦ hasSum_fintype _
    have := hsig.tendsto_sum_nat
    refine this.congr fun N ↦ ?_
    simp only [hsdef]
  exact ⟨hedist, (ae_eq_of_tendsto_eLpNorm_of_tendsto_ae' (zero_lt_one.trans_le Fact.out).ne'
    (fun N ↦ (hs_meas N).aestronglyMeasurable) (Lp.aestronglyMeasurable _) hL hpt).symm⟩

/-- [Hit26, Definition 4.2.2], in the form the proofs of
[Hit26, Lemma 4.2.4] and [Hit26, Lemma 4.2.8]
use: a power series `F : ℝ^d → L²(q)` at `c₀` yields, on every patch `B` mapped `1`-Lipschitz by
`e` into a small closed ball around `c₀`, an `L²(q)`-expansion of `f` (where `f(·, u)` represents
`F(e(u))`). -/
theorem _root_.HasFPowerSeriesOnBall.exists_l2Expansion (hs : 2 ≤ s) {F : (Fin d → ℝ) → Lp ℝ s q}
    {c₀ : Fin d → ℝ}
    {r : ℝ≥0∞} (hF : HasFPowerSeriesOnBall F p c₀ r) (e : U → Fin d → ℝ) (f : X → U → ℝ)
    (hf : ∀ u, edist (e u) c₀ < r → (F (e u) : X → ℝ) =ᵐ[q] fun x ↦ f x u) :
    ∃ ρ > 0, ∀ B : Set U, (∀ u ∈ B, dist (e u) c₀ ≤ ρ) →
      (∀ u ∈ B, ∀ v ∈ B, dist (e u) (e v) ≤ dist u v) →
      ∃ E : L2Expansion q f B, E.HigherMoment s := by
  obtain ⟨ρ, hρ, h⟩ := HasFPowerSeriesOnBall.exists_l2Expansion_repr hs hF e
  refine ⟨ρ, hρ, fun B hB he ↦ ?_⟩
  obtain ⟨rep, -, -, hrep, E, hE⟩ := h B hB he
  exact ⟨E.congr fun u hu ↦ (hrep u hu).2.trans (hf u (hrep u hu).1), hE⟩

end PowerSeriesExpansion

end SingularLearningTheory
