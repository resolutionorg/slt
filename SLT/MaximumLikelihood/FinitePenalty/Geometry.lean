/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Penalty.Core
public import SLT.MaximumLikelihood.Penalty.Functionals

/-!
# Deterministic bounds for a penalized minimizer

Fix a sample size $n$ and a field $\Psi$ on the chart cubes of a resolution atlas, and let $S$ be
an objective that on every chart is $nu^{2k} + \sqrt{n}\,u^k\Psi(u)$, as $nK_n$ is. Let $\hat w$
minimize $S + a\sigma$ over $W$, with $nK(\hat w) \le Q^2$, $\max(0, -\Psi) \le B$ on the resolved
zeros, $\Psi$ Lipschitz with constant $C$ and $\sigma \circ g$ Lipschitz with constant $\Lambda$
on each chart. Then $S(\hat w) + a\sigma(\hat w)$ is within $BCr/2 + (Cr)^2/4 + a\Lambda r$ of
minus the penalized reward, and $nK(\hat w) - a\sigma(\hat w)$ is within an explicit error of the
reward, where $r$ bounds the distance from the localized estimator to the zeros. The proof
projects $\hat w$ to a nearby resolved zero and compares it with a recovery point near the
maximizer of the reward. These bounds give the finite-penalty limits of
[Wat09, Main Theorem 6.4(2)] once $r \to 0$.

## Main results

* `SingularLearningTheory.ResolutionAtlas.finitePenalty_core_at_and_exists_resolvedZero`: both
  bounds, together with a resolved zero $v$ near $\hat w$ where $\sigma$ is close to $\sigma(\hat
  w)$, $\max(0, -\Psi(v))^2/4$ is close to $nK(\hat w)$, and the reward objective is close to the
  reward.
* `SingularLearningTheory.ResolutionAtlas.finitePenalty_core_at`: the two bounds alone.
* `SingularLearningTheory.ResolutionAtlas.finitePenalty_weight_correction`: centering at weight $a$
  an estimator that minimizes with weight $a'$ costs at most $2|a' - a|\sup_W|\sigma|$ in each
  bound.
-/

public section

open MeasureTheory Set Filter Topology

namespace SingularLearningTheory.ResolutionAtlas

open SingularLearningTheory.MaximumLikelihood

variable {d : ℕ} {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- A localized penalized optimizer. Q controls its localization, B controls the
field; this separation allows the chartRadius with a deterministic cap Q. -/
theorem finitePenalty_core_at_and_exists_resolvedZero {n : ℕ} (hn : 0 < n) (Ψ : C(Domain R, ℝ))
    {S σ : (Fin d → ℝ) → ℝ}
    (hS : ∀ α (u : cube d (R.b α)), S (R.g α u) =
      (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ ⟨α, u⟩)
    {δ : ℝ} (hcover : ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hσ : Continuous (chartPenalty R σ))
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hσLip : ∀ α (u v : cube d (R.b α)),
      |σ (R.g α u) - σ (R.g α v)| ≤ Λ * dist u v)
    {a B Q r C : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hBQ : B ^ 2 ≤ Q ^ 2)
    (hrad : ∀ α, (Q ^ 2 / (n : ℝ)) ^
      (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) ≤ r)
    (hδ : Q ^ 2 / (n : ℝ) < δ)
    (hlev : ∀ α, B ^ 2 / (4 * (n : ℝ)) ≤ ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2)
    (hLip : ∀ α (u v : cube d (R.b α)),
      |Ψ ⟨α, u⟩ - Ψ ⟨α, v⟩| ≤ C * dist u v)
    {ŵ : Fin d → ℝ} (hŵ : ŵ ∈ W)
    (hmin : ∀ w ∈ W, S ŵ + a * σ ŵ ≤ S w + a * σ w)
    (hloc : (n : ℝ) * K ŵ ≤ Q ^ 2) (hM : positiveMax R Ψ ≤ B) :
    |S ŵ + a * σ ŵ + penalizedLikelihoodRewardSup R σ a Ψ| ≤
        B * (C * r) / 2 + (C * r) ^ 2 / 4 + a * Λ * r ∧
      |(n : ℝ) * K ŵ - a * σ ŵ - penalizedLikelihoodRewardSup R σ a Ψ| ≤
        mleErr' B (C * r) (B * (C * r) / 2 + 2 * (a * Λ * r)) +
          B * (C * r) + (C * r) ^ 2 / 4 + 3 * (a * Λ * r) ∧
      ∃ v ∈ resolvedZeroSet R,
        |a * σ ŵ - a * chartPenalty R σ v| ≤ a * Λ * r ∧
        penalizedLikelihoodRewardSup R σ a Ψ -
          ((max 0 (-Ψ v)) ^ 2 / 4 - a * chartPenalty R σ v) ≤
            B * (C * r) + (C * r) ^ 2 / 4 + 2 * (a * Λ * r) ∧
        |(n : ℝ) * K ŵ - (max 0 (-Ψ v)) ^ 2 / 4| ≤
          mleErr' B (C * r) (B * (C * r) / 2 + 2 * (a * Λ * r)) := by
  have hθ : 0 ≤ C * r := mul_nonneg hC hr
  have hc : 0 ≤ a * Λ * r := mul_nonneg (mul_nonneg ha hΛ) hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hKŵ : K ŵ ≤ Q ^ 2 / (n : ℝ) := by rw [le_div_iff₀ hn']; linarith
  obtain ⟨α, û, hgû⟩ := hcover ŵ hŵ (hKŵ.trans_lt hδ)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = ∏ j, (û : Fin d → ℝ) j ^ R.k α j := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := hh ▸ monomial_nonneg
    (fun j ↦ û.property.1 j)
  have hKh : K ŵ = h ^ 2 := by rw [← hgû, K_g_eq_square R α û, ← hh]
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Ψ ⟨α, û⟩ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt n * h := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ mul_nonneg hsn.le hh0
  have hx2 : x ^ 2 = (n : ℝ) * K ŵ := by
    rw [hx, mul_pow, Real.sq_sqrt hn'.le, hKh]
  have hq : S ŵ = x ^ 2 + x * z := by
    rw [← hgû, hS α û, ← hh, ← hz, hx, mul_pow, Real.sq_sqrt hn'.le]
  have hsum : ∀ α, (∑ j, R.k α j) ≠ 0 := fun α ↦ sum_k_ne_zero (R.active α)
  obtain ⟨vz, hvz, hdvz⟩ := exists_resolved_zero_dist_le R α û
  have hdvzr : dist û vz ≤ r := by
    rw [← hh] at hdvz
    exact hdvz.trans ((Real.rpow_inv_le_of_sq_le hh0
      (by rw [← hKh]; exact hKŵ) (hsum α)).trans (hrad α))
  have hzvz : |z - Ψ ⟨α, vz⟩| ≤ C * r := by
    rw [hz]
    exact (hLip α û vz).trans (mul_le_mul_of_nonneg_left hdvzr hC)
  let mz := max 0 (-Ψ ⟨α, vz⟩)
  have hmz0 : 0 ≤ mz := le_max_left _ _
  have hmzB : mz ≤ B := (le_positiveMax R Ψ hvz).trans hM
  have hproj : max 0 (-z) ≤ mz + C * r := by
    have h1 := le_max_right 0 (-Ψ ⟨α, vz⟩)
    have h2 := (abs_le.mp hzvz).1
    exact max_le (by linarith) (by dsimp [mz] at *; linarith)
  have hσfoot : |a * σ ŵ - a * σ (R.g α vz)| ≤ a * Λ * r := by
    rw [← mul_sub, abs_mul, abs_of_nonneg ha, ← hgû, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      ((hσLip α û vz).trans (mul_le_mul_of_nonneg_left hdvzr hΛ)) ha
  have hFz : mz ^ 2 / 4 - a * σ (R.g α vz) ≤
      penalizedLikelihoodRewardSup R σ a Ψ :=
    le_penalizedMax R (chartPenalty R σ) hσ a Ψ hvz
  obtain ⟨⟨α', v'⟩, hv'Z, hFeq⟩ :=
    exists_penalizedMax_eq R (chartPenalty R σ) hσ a Ψ
  let m' := max 0 (-Ψ ⟨α', v'⟩)
  have hm'0 : 0 ≤ m' := le_max_left _ _
  have hm'B : m' ≤ B := (le_positiveMax R Ψ hv'Z).trans hM
  change penalizedLikelihoodRewardSup R σ a Ψ = m' ^ 2 / 4 - a * σ (R.g α' v') at hFeq
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = m' / (2 * Real.sqrt n) := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := hℓ ▸ div_nonneg hm'0 (by positivity)
  have hℓsq : ℓ ^ 2 = m' ^ 2 / (4 * (n : ℝ)) := by
    rw [hℓ, div_pow, mul_pow, Real.sq_sqrt hn'.le]; ring
  have hℓB : ℓ ^ 2 ≤ B ^ 2 / (4 * (n : ℝ)) := by
    rw [hℓsq]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hm'0 hm'B 2) (by positivity)
  have hℓlev : ℓ ≤ (R.b α' / 2) ^ (∑ j, R.k α' j) := by
    exact pow_le_pow_iff_left₀ hℓ0 (pow_nonneg (half_pos (R.b_pos α')).le _)
      two_ne_zero |>.mp (hℓB.trans (hlev α'))
  obtain ⟨u', hu'ℓ, hdu', hgu'⟩ :=
    exists_resolved_recovery_point R α' v' hv'Z hℓ0 hℓlev
  have hBρ : B ^ 2 / (4 * (n : ℝ)) ≤ Q ^ 2 / (n : ℝ) := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg B]) hn'.le
  have hdu'r : dist u' v' ≤ r :=
    hdu'.trans ((Real.rpow_inv_le_of_sq_le hℓ0 (hℓB.trans hBρ) (hsum α')).trans (hrad α'))
  have hqu' : S (R.g α' u') = m' ^ 2 / 4 + m' / 2 * Ψ ⟨α', u'⟩ := by
    have e1 : (n : ℝ) * (m' / (2 * Real.sqrt n)) ^ 2 = m' ^ 2 / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hn'.le]
      field_simp [hn'.ne']; ring
    have e2 : Real.sqrt n * (m' / (2 * Real.sqrt n)) = m' / 2 := by field_simp [hsn.ne']
    rw [hS α' u', hu'ℓ, hℓ, e1, e2]
  have hzu' : |Ψ ⟨α', u'⟩ - Ψ ⟨α', v'⟩| ≤ C * r :=
    (hLip α' u' v').trans (mul_le_mul_of_nonneg_left hdu'r hC)
  have hσu' : a * σ (R.g α' u') ≤ a * σ (R.g α' v') + a * Λ * r := by
    have h1 := (hσLip α' u' v').trans (mul_le_mul_of_nonneg_left hdu'r hΛ)
    have h2 := mul_le_mul_of_nonneg_left (abs_le.mp h1).2 ha
    nlinarith only [h2]
  have hrecval : m' / 2 * Ψ ⟨α', u'⟩ ≤ m' / 2 * (-m' + C * r) := by
    rcases eq_or_lt_of_le hm'0 with hm'z | hmpos
    · rw [← hm'z]; simp
    · have hMv : m' = -Ψ ⟨α', v'⟩ := by
        dsimp [m']
        rcases le_or_gt (-Ψ ⟨α', v'⟩) 0 with hneg | hpos
        · simp only [m', max_eq_left hneg] at hmpos
          linarith
        · exact max_eq_right hpos.le
      have h2 : Ψ ⟨α', u'⟩ ≤ -m' + C * r := by
        have := (abs_le.mp hzu').2
        linarith
      exact mul_le_mul_of_nonneg_left h2 (by linarith)
  have hrec : S ŵ + a * σ ŵ ≤
      -penalizedLikelihoodRewardSup R σ a Ψ + B * (C * r) / 2 + a * Λ * r := by
    have hcmp := hmin _ hgu'
    rw [hqu'] at hcmp
    have hmω := mul_le_mul_of_nonneg_right hm'B hθ
    rw [hFeq]
    nlinarith only [hcmp, hrecval, hσu', hmω]
  obtain ⟨hT, hG, hgap, hcore⟩ := penalized_core_bounds
    (M := B) (mz := mz) (pŵ := a * σ ŵ) (pz := a * σ (R.g α vz))
    (F := penalizedLikelihoodRewardSup R σ a Ψ)
    (Fz := mz ^ 2 / 4 - a * σ (R.g α vz))
    hx0 hθ hmz0 hmzB hc hq rfl hproj rfl hFz hσfoot hrec
  rw [hx2] at hG hcore
  exact ⟨hT, hG, ⟨α, vz⟩, hvz, hσfoot, hgap, hcore⟩

theorem finitePenalty_core_at {n : ℕ} (hn : 0 < n) (Ψ : C(Domain R, ℝ))
    {S σ : (Fin d → ℝ) → ℝ}
    (hS : ∀ α (u : cube d (R.b α)), S (R.g α u) =
      (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ ⟨α, u⟩)
    {δ : ℝ} (hcover : ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    (hσ : Continuous (chartPenalty R σ))
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hσLip : ∀ α (u v : cube d (R.b α)),
      |σ (R.g α u) - σ (R.g α v)| ≤ Λ * dist u v)
    {a B Q r C : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hBQ : B ^ 2 ≤ Q ^ 2)
    (hrad : ∀ α, (Q ^ 2 / (n : ℝ)) ^
      (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) ≤ r)
    (hδ : Q ^ 2 / (n : ℝ) < δ)
    (hlev : ∀ α, B ^ 2 / (4 * (n : ℝ)) ≤ ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2)
    (hLip : ∀ α (u v : cube d (R.b α)),
      |Ψ ⟨α, u⟩ - Ψ ⟨α, v⟩| ≤ C * dist u v)
    {ŵ : Fin d → ℝ} (hŵ : ŵ ∈ W)
    (hmin : ∀ w ∈ W, S ŵ + a * σ ŵ ≤ S w + a * σ w)
    (hloc : (n : ℝ) * K ŵ ≤ Q ^ 2) (hM : positiveMax R Ψ ≤ B) :
    |S ŵ + a * σ ŵ + penalizedLikelihoodRewardSup R σ a Ψ| ≤
        B * (C * r) / 2 + (C * r) ^ 2 / 4 + a * Λ * r ∧
      |(n : ℝ) * K ŵ - a * σ ŵ - penalizedLikelihoodRewardSup R σ a Ψ| ≤
        mleErr' B (C * r) (B * (C * r) / 2 + 2 * (a * Λ * r)) +
          B * (C * r) + (C * r) ^ 2 / 4 + 3 * (a * Λ * r) := by
  obtain ⟨hT, hG, -⟩ := finitePenalty_core_at_and_exists_resolvedZero R hn Ψ hS hcover hσ hΛ hσLip
    ha hB hr hC hBQ hrad hδ hlev hLip hŵ hmin hloc hM
  exact ⟨hT, hG⟩

/-- Correct both the estimator's shift and the reward when the optimization uses
weight a' but the theorem centers at weight a. -/
theorem finitePenalty_weight_correction {σ : (Fin d → ℝ) → ℝ}
    (hσ : Continuous (chartPenalty R σ)) {Sg : ℝ}
    (hσb : ∀ w ∈ W, |σ w| ≤ Sg) {ŵ : Fin d → ℝ} (hŵ : ŵ ∈ W)
    (Ψ : C(Domain R, ℝ)) (a a' x q : ℝ) :
    |x - a * σ ŵ - penalizedLikelihoodRewardSup R σ a Ψ| ≤
      |x - a' * σ ŵ - penalizedLikelihoodRewardSup R σ a' Ψ| + 2 * |a' - a| * Sg ∧
    |q + a * σ ŵ + penalizedLikelihoodRewardSup R σ a Ψ| ≤
      |q + a' * σ ŵ + penalizedLikelihoodRewardSup R σ a' Ψ| + 2 * |a' - a| * Sg := by
  have hF := abs_penalizedMax_sub_le R (chartPenalty R σ) hσ
    (fun v _ ↦ hσb _ (R.g_mapsTo v.1 v.2.property)) a' a Ψ
  have hp : |(a' - a) * σ ŵ| ≤ |a' - a| * Sg := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hσb _ hŵ) (abs_nonneg _)
  change |penalizedLikelihoodRewardSup R σ a' Ψ -
    penalizedLikelihoodRewardSup R σ a Ψ| ≤ |a' - a| * Sg at hF
  constructor
  · have ht := abs_add_le (x - a' * σ ŵ - penalizedLikelihoodRewardSup R σ a' Ψ)
      ((a' - a) * σ ŵ +
        (penalizedLikelihoodRewardSup R σ a' Ψ - penalizedLikelihoodRewardSup R σ a Ψ))
    have he : x - a' * σ ŵ - penalizedLikelihoodRewardSup R σ a' Ψ +
        ((a' - a) * σ ŵ + (penalizedLikelihoodRewardSup R σ a' Ψ -
          penalizedLikelihoodRewardSup R σ a Ψ)) =
        x - a * σ ŵ - penalizedLikelihoodRewardSup R σ a Ψ := by ring
    rw [he] at ht
    linarith [abs_add_le ((a' - a) * σ ŵ)
      (penalizedLikelihoodRewardSup R σ a' Ψ - penalizedLikelihoodRewardSup R σ a Ψ)]
  · have ht := abs_sub (q + a' * σ ŵ + penalizedLikelihoodRewardSup R σ a' Ψ)
      ((a' - a) * σ ŵ +
        (penalizedLikelihoodRewardSup R σ a' Ψ - penalizedLikelihoodRewardSup R σ a Ψ))
    have he : q + a' * σ ŵ + penalizedLikelihoodRewardSup R σ a' Ψ -
        ((a' - a) * σ ŵ + (penalizedLikelihoodRewardSup R σ a' Ψ -
          penalizedLikelihoodRewardSup R σ a Ψ)) =
        q + a * σ ŵ + penalizedLikelihoodRewardSup R σ a Ψ := by ring
    rw [he] at ht
    linarith [abs_add_le ((a' - a) * σ ŵ)
      (penalizedLikelihoodRewardSup R σ a' Ψ - penalizedLikelihoodRewardSup R σ a Ψ)]

end SingularLearningTheory.ResolutionAtlas
