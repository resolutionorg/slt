/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.SingularIntegrals.TypeOfAtlas
public import SLT.VolumeScaling.Stability
import SLT.VolumeScaling.ScaleDominance
public import SLT.SingularIntegrals.SingularityType
import SLT.VolumeScaling.Comparison
import SLT.VolumeScaling.Basic
public import SLT.StandardForm.FundamentalConditionI
import Mathlib.Order.CompletePartialOrder
import Std.Tactic.BVDecide.Normalize.Prop

/-!
# The local singularity type at a point

The singularity type of `(K, φ)` *at a point* `x` of `W`: the pair `(λ, m)` that is the
singularity type (`IsSingularityType`) of `(K, φ, W ∩ B̄(x, r))` for every sufficiently small
closed ball. This is Larsson's local `(λ(x), m(x))`, the `(λ, m)` of [Hit26]'s local learning
coefficient ([Hit26, Definition 6.2.1], whose remark
[Hit26, Remark 6.2.3] gives the volume-scaling
characterisation), in the "basis form" of the volume-scaling library (`HasLLCExponentsAt`,
`VolumeScaling/Stability.lean`, which also records why the type on one ball is not the local
type). No statement of `SLTChallenge` is proved here.

| Thesis | Lean |
| --- | --- |
| [Hit26, Definition 6.2.1], by volume scaling | `HasLocalSingularityType` |
| remark after it (independence of the resolution), local form | `HasLocalSingularityType.unique` |

## What is here, and what is not

* `HasLocalSingularityType`, its uniqueness, and the bridge to `HasLLCExponentsAt` for the prior
  measure restricted to `W` (`hasLocalSingularityType_iff`).
* `MoreSingular`: the lexicographic order on types (smaller `λ`, or equal `λ` and larger `m`), in
  which a set's type is at least as singular as any subset's
  (`IsSingularityType.moreSingular_of_subset`). Hence the ball types are monotone in the radius,
  and the local type is lower semicontinuous: points near `x` are at most as singular as `x`
  (`HasLocalSingularityType.eventually_moreSingular`).
* A chart of a resolution atlas centred at `x` with positive weight at its origin bounds the local
  type: every small ball at `x` is at least as singular as `(λ_α, m_α)`
  (`ResolutionAtlas.moreSingular_chart_of_center`).
* `Semianalytic` is stable under intersection with a closed ball (a box, for the sup metric of
  `Fin d → ℝ`), so `singularity_type_exists` applies to `W ∩ B̄(x, r)`.
* The existence of the local type under the analytic and prior hypotheses is not proved here.
-/

public section

namespace SingularLearningTheory

open MeasureTheory Set Filter Topology Asymptotics SingularLearningTheory Metric
open scoped ENNReal

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-! ## The lexicographic order on types -/

/-- `(λ₁, m₁)` is at least as singular as `(λ₂, m₂)`: `λ₁ < λ₂`, or `λ₁ = λ₂` and `m₂ ≤ m₁`.
Equivalently the scale `ε^{λ₂} (−log ε)^{m₂−1}` is `O` of `ε^{λ₁} (−log ε)^{m₁−1}` as `ε → 0⁺`
(`moreSingular_iff_isBigO`). -/
@[expose] def MoreSingular (lam₁ : ℝ) (m₁ : ℕ) (lam₂ : ℝ) (m₂ : ℕ) : Prop :=
  lam₁ < lam₂ ∨ (lam₁ = lam₂ ∧ m₂ ≤ m₁)

protected theorem MoreSingular.refl (lam : ℝ) (m : ℕ) : MoreSingular lam m lam m := Or.inr ⟨rfl,
    le_rfl⟩

protected theorem MoreSingular.trans {l₁ l₂ l₃ : ℝ} {m₁ m₂ m₃ : ℕ} (h₁ : MoreSingular l₁ m₁ l₂ m₂)
    (h₂ : MoreSingular l₂ m₂ l₃ m₃) : MoreSingular l₁ m₁ l₃ m₃ := by
  rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨rfl, h₂⟩
  · exact Or.inl (h₁.trans h₂)
  · exact Or.inl h₁
  · exact Or.inl h₂
  · exact Or.inr ⟨rfl, h₂.trans h₁⟩

protected theorem MoreSingular.antisymm {l₁ l₂ : ℝ} {m₁ m₂ : ℕ} (h₁ : MoreSingular l₁ m₁ l₂ m₂)
    (h₂ : MoreSingular l₂ m₂ l₁ m₁) : l₁ = l₂ ∧ m₁ = m₂ := by
  rcases h₁ with h₁ | ⟨rfl, h₁⟩ <;> rcases h₂ with h₂ | ⟨h₂, h₂'⟩
  · exact absurd (h₁.trans h₂) (lt_irrefl _)
  · exact absurd h₁ (h₂ ▸ lt_irrefl _)
  · exact absurd h₂ (lt_irrefl _)
  · exact ⟨rfl, le_antisymm h₂' h₁⟩

/-- The order on types is the `O`-comparison of the scales. -/
theorem moreSingular_iff_isBigO {lam₁ lam₂ : ℝ} {m₁ m₂ : ℕ} :
    MoreSingular lam₁ m₁ lam₂ m₂ ↔ llcScale lam₂ m₂ =O[𝓝[>] (0 : ℝ)] llcScale lam₁ m₁ := by
  constructor
  · rintro (h | ⟨h, h'⟩)
    · exact isBigO_llcScale_of_lex (Or.inl h)
    · exact isBigO_llcScale_of_lex (Or.inr ⟨h, by exact_mod_cast h'⟩)
  · intro h
    rcases lex_le_of_isBigO_llcScale h with h | ⟨h, h'⟩
    · exact Or.inl h
    · exact Or.inr ⟨h, by exact_mod_cast h'⟩

/-- A set is at least as singular as any of its subsets: if `A ⊆ B` and both have singularity
types, the type of `B` is at least as singular as that of `A`. -/
theorem IsSingularityType.moreSingular_of_subset {A B : Set (Fin d → ℝ)} (hAB : A ⊆ B)
    (hB : MeasurableSet B) (hφ : ∀ w ∈ B, 0 ≤ φ w) (hφm : AEMeasurable φ (volume.restrict B))
    {l₁ l₂ : ℝ} {m₁ m₂ : ℕ} (hA : IsSingularityType K φ A l₁ m₁)
    (hB' : IsSingularityType K φ B l₂ m₂) : MoreSingular l₂ m₂ l₁ m₁ := by
  rw [moreSingular_iff_isBigO]
  have hAT := hA.isTheta
  have hBV := (isSingularityType_iff hB hφ hφm).mp hB'
  obtain ⟨c₁, hc₁, c₂, hc₂, hb⟩ := hasLLCExponentsOn_iff_eventually_bounds.mp hBV
  obtain ⟨c₁', hc₁', c₂', hc₂', hbA⟩ := hA
  -- `0 ≤ V_A ≤ V_B` eventually: `V_B` is finite where it is bounded below by a positive scale
  have hle : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 ≤ ∫ w in A ∩ {w | K w ≤ ε}, φ w ∧
      ∫ w in A ∩ {w | K w ≤ ε}, φ w ≤ ∫ w in B ∩ {w | K w ≤ ε}, φ w := by
    filter_upwards [hb, hbA, llcScale_eventually_pos (lam := l₂) (theta := m₂),
      llcScale_eventually_pos (lam := l₁) (theta := m₁)] with ε h hA' hs hs'
    refine ⟨le_trans (mul_pos hc₁' hs').le hA'.1, ?_⟩
    have hfin : priorMeasure φ Set.univ (B ∩ {w | K w ≤ ε}) ≠ ⊤ := by
      intro htop
      have h0 : sublevelVol (priorMeasure φ Set.univ) B K ε = 0 := by
        rw [sublevelVol, htop, ENNReal.toReal_top]
      have := h.1
      rw [h0] at this
      linarith [mul_pos hc₁ hs]
    have hsub : volume.restrict (A ∩ {w | K w ≤ ε}) ≤ volume.restrict B :=
      Measure.restrict_mono (inter_subset_left.trans hAB) le_rfl
    have hA_eq :
        ∫ w in A ∩ {w | K w ≤ ε}, φ w = sublevelVol (priorMeasure φ Set.univ) A K ε := by
      rw [sublevelVol, priorMeasure, Measure.restrict_univ,
        withDensity_apply' _ (A ∩ {w | K w ≤ ε}),
        integral_eq_lintegral_of_nonneg_ae
          (ae_mono hsub ((ae_restrict_iff' hB).mpr (.of_forall hφ)))
          (hφm.mono_measure hsub).aestronglyMeasurable]
    rw [hA_eq, ← sublevelVol_priorMeasure hB hφ hφm]
    exact ENNReal.toReal_mono hfin (measure_mono (inter_subset_inter_left _ hAB))
  -- `scale_A =O V_A =O V_B =O scale_B`
  refine hAT.symm.1.trans ((IsBigO.of_bound 1 ?_).trans hB'.isTheta.1)
  filter_upwards [hle] with ε h
  rw [one_mul, Real.norm_of_nonneg h.1, Real.norm_of_nonneg (h.1.trans h.2)]
  exact h.2

/-! ## The local type -/

/-- The *local singularity type* of `(K, φ)` at `x`, relative to `W` ([Hit26,
Definition 6.2.1], by volume scaling): `(λ, m)` is the singularity type
of `(K, φ, W ∩ B̄(x, r))` for every sufficiently small closed ball. Larsson's `(λ(x), m(x))`. -/
@[expose] def HasLocalSingularityType (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) (x : Fin d → ℝ)
    (lam : ℝ) (m : ℕ) : Prop :=
  ∀ᶠ r in 𝓝[>] (0 : ℝ), IsSingularityType K φ (W ∩ closedBall x r) lam m

/-- The local type is unique. -/
theorem HasLocalSingularityType.unique {x : Fin d → ℝ} {l₁ l₂ : ℝ} {m₁ m₂ : ℕ}
    (h₁ : HasLocalSingularityType K φ W x l₁ m₁) (h₂ : HasLocalSingularityType K φ W x l₂ m₂) :
    l₁ = l₂ ∧ m₁ = m₂ := by
  obtain ⟨r, hr₁, hr₂⟩ := (h₁.and h₂).exists
  exact hr₁.unique hr₂

/-- Introduction rule with an explicit threshold. -/
theorem hasLocalSingularityType_of_forall_Ioc {x : Fin d → ℝ} {lam : ℝ} {m : ℕ} {r₀ : ℝ}
    (hr₀ : 0 < r₀)
    (h : ∀ r ∈ Ioc (0 : ℝ) r₀, IsSingularityType K φ (W ∩ closedBall x r) lam m) :
    HasLocalSingularityType K φ W x lam m :=
  eventually_iff_exists_mem.mpr ⟨Ioc 0 r₀, Ioc_mem_nhdsGT hr₀, h⟩

/-- The sublevel volumes of `(φ dw)|_W` on a closed ball are those of `φ dw` on `W ∩ B̄(x, r)`. -/
private theorem sublevelVol_restrict_closedBall (hW : MeasurableSet W) (x : Fin d → ℝ) (r ε : ℝ) :
    sublevelVol ((priorMeasure φ Set.univ).restrict W) (closedBall x r) K ε
      = sublevelVol (priorMeasure φ Set.univ) (W ∩ closedBall x r) K ε := by
  rw [sublevelVol, sublevelVol, Measure.restrict_apply' hW]
  congr 2
  ext w
  simp only [mem_inter_iff, mem_ofPred_eq]
  tauto

/-- The type of `W ∩ B̄(x, r)` is the library's `HasLLCExponentsOn` of the prior measure
restricted to `W`, localised to the closed ball. -/
private theorem isSingularityType_inter_closedBall_iff (hW : MeasurableSet W)
    (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφm : AEMeasurable φ (volume.restrict W)) {x : Fin d → ℝ} {r lam : ℝ} {m : ℕ} :
    IsSingularityType K φ (W ∩ closedBall x r) lam m ↔
      HasLLCExponentsOn ((priorMeasure φ Set.univ).restrict W) (closedBall x r) K lam m := by
  rw [isSingularityType_iff (hW.inter measurableSet_closedBall) (fun w hw ↦ hφ w hw.1)
    (hφm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)), HasLLCExponentsOn,
    HasLLCExponentsOn, funext (sublevelVol_restrict_closedBall hW x r)]

/-- The local type is the library's `HasLLCExponentsAt` (hironaka's `VolumeScaling/Defs.lean`;
its API is in `VolumeScaling/Stability.lean`) for the prior measure restricted to `W`. -/
theorem hasLocalSingularityType_iff (hW : MeasurableSet W) (hφ : ∀ w ∈ W, 0 ≤ φ w)
    (hφm : AEMeasurable φ (volume.restrict W)) {x : Fin d → ℝ} {lam : ℝ} {m : ℕ} :
    HasLocalSingularityType K φ W x lam m ↔
      HasLLCExponentsAt ((priorMeasure φ Set.univ).restrict W) K x lam m := by
  unfold HasLocalSingularityType HasLLCExponentsAt
  simp only [isSingularityType_inter_closedBall_iff hW hφ hφm]

/-- **Lower semicontinuity of the local type.** Points near `x` are at most as singular as `x`:
if the local type at `x` is `(λ, m)`, then every `y` close enough to `x` at which a local type
`(λ', m')` exists has `(λ, m)` at least as singular as `(λ', m')`. (A small ball at `y` lies
inside a ball at `x` carrying `(λ, m)`.) -/
theorem HasLocalSingularityType.eventually_moreSingular (hW : MeasurableSet W)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφm : AEMeasurable φ (volume.restrict W)) {x : Fin d → ℝ}
    {lam : ℝ} {m : ℕ} (hx : HasLocalSingularityType K φ W x lam m) :
    ∀ᶠ y in 𝓝 x, ∀ (lam' : ℝ) (m' : ℕ), HasLocalSingularityType K φ W y lam' m' →
      MoreSingular lam m lam' m' := by
  obtain ⟨R, hR, hRx⟩ := (hx.and eventually_mem_nhdsWithin).exists
  rw [mem_Ioi] at hRx
  filter_upwards [Metric.ball_mem_nhds x (half_pos hRx)] with y hy lam' m' hy'
  obtain ⟨r, hr, hry⟩ := (hy'.and (eventually_nhdsWithin_of_eventually_nhds
    (eventually_lt_nhds (half_pos hRx)))).exists
  have hsub : W ∩ closedBall y r ⊆ W ∩ closedBall x R := by
    refine inter_subset_inter_right _ (closedBall_subset_closedBall' ?_)
    rw [mem_ball] at hy
    linarith
  exact hr.moreSingular_of_subset hsub (hW.inter measurableSet_closedBall)
    (fun w hw ↦ hφ w hw.1) (hφm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl))
    hR

/-- **Monotonicity of the ball types in the radius**: a larger ball is at least as singular. -/
theorem IsSingularityType.moreSingular_of_radius_le (hW : MeasurableSet W)
    (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφm : AEMeasurable φ (volume.restrict W)) {x : Fin d → ℝ}
    {r r' : ℝ} (hrr : r' ≤ r) {l l' : ℝ} {m m' : ℕ}
    (h : IsSingularityType K φ (W ∩ closedBall x r) l m)
    (h' : IsSingularityType K φ (W ∩ closedBall x r') l' m') : MoreSingular l m l' m' :=
  h'.moreSingular_of_subset (inter_subset_inter_right _ (closedBall_subset_closedBall hrr))
    (hW.inter measurableSet_closedBall) (fun w hw ↦ hφ w hw.1)
    (hφm.mono_measure (Measure.restrict_mono inter_subset_left le_rfl)) h

/-! ## Semianalytic sets and closed balls -/

/-- The intersection of two semianalytic sets is semianalytic. -/
private theorem Semianalytic.inter {A B : Set (Fin d → ℝ)} (hA : Semianalytic A)
    (hB : Semianalytic B) :
    Semianalytic (A ∩ B) := by
  obtain ⟨U₁, N₁, H₁, hU₁, hAU₁, hH₁, hA⟩ := hA
  obtain ⟨U₂, N₂, H₂, hU₂, hBU₂, hH₂, hB⟩ := hB
  refine ⟨U₁ ∩ U₂, N₁ + N₂, fun i ↦ Sum.elim H₁ H₂ (finSumFinEquiv.symm i), hU₁.inter hU₂,
    inter_subset_inter hAU₁ hBU₂, fun i ↦ ?_, fun w hw ↦ ?_⟩
  · obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
    simp only [Equiv.symm_apply_apply]
    rcases s with j | j
    · exact (hH₁ j).mono inter_subset_left
    · exact (hH₂ j).mono inter_subset_right
  · rw [mem_inter_iff, hA w hw.1, hB w hw.2]
    refine Iff.trans ?_ (finSumFinEquiv.symm.surjective.forall
      (p := fun s ↦ 0 ≤ Sum.elim H₁ H₂ s w))
    rw [Sum.forall]
    exact Iff.rfl

/-- A closed ball of `Fin d → ℝ` (a box, for the sup metric) is semianalytic. -/
private theorem semianalytic_closedBall (x : Fin d → ℝ) (r : ℝ) : Semianalytic
    (closedBall x r) := by
  rcases lt_or_ge r 0 with hr | hr
  · refine ⟨univ, 1, fun _ _ ↦ -1, isOpen_univ, subset_univ _, fun _ ↦ analyticOnNhd_const,
      fun w _ ↦ ?_⟩
    simp [closedBall_eq_empty.mpr hr]
  · refine ⟨univ, d + d, fun i ↦ Sum.elim (fun j w ↦ r - (w j - x j)) (fun j w ↦ r + (w j - x j))
      (finSumFinEquiv.symm i), isOpen_univ, subset_univ _, fun i ↦ ?_, fun w _ ↦ ?_⟩
    · have hproj : ∀ j : Fin d, AnalyticOnNhd ℝ (fun w : Fin d → ℝ ↦ w j - x j) univ := fun j ↦
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d ↦ ℝ) j).analyticOnNhd univ).sub
          analyticOnNhd_const
      obtain ⟨s, rfl⟩ := finSumFinEquiv.surjective i
      simp only [Equiv.symm_apply_apply]
      rcases s with j | j
      · exact analyticOnNhd_const.sub (hproj j)
      · exact analyticOnNhd_const.add (hproj j)
    · rw [closedBall_pi x hr, mem_univ_pi]
      simp only [Real.closedBall_eq_Icc, mem_Icc]
      refine Iff.trans ?_ (finSumFinEquiv.symm.surjective.forall
        (p := fun s ↦ 0 ≤ Sum.elim (fun j w ↦ r - (w j - x j)) (fun j w ↦ r + (w j - x j)) s w))
      rw [Sum.forall]
      simp only [Sum.elim_inl, Sum.elim_inr]
      constructor
      · intro h
        exact ⟨fun j ↦ by linarith [(h j).2], fun j ↦ by linarith [(h j).1]⟩
      · rintro ⟨h1, h2⟩ j
        exact ⟨by linarith [h2 j], by linarith [h1 j]⟩

/-- `W ∩ B̄(x, r)` is compact and semianalytic when `W` is. -/
theorem Semianalytic.inter_closedBall {W : Set (Fin d → ℝ)} (hW : Semianalytic W) (x : Fin d → ℝ)
    (r : ℝ) : Semianalytic (W ∩ closedBall x r) :=
  hW.inter (semianalytic_closedBall x r)

end SingularLearningTheory
