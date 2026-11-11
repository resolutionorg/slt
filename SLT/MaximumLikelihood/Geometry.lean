/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Core
public import SLT.Resolution.Atlas
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Order.Compact

/-!
# Slice geometry and deterministic maximum-likelihood bounds

The arguments use the resolution atlas and its feasible cubes.

On a box `[0, r]^d` with the chart monomial `u^k = ∏ᵢ uᵢ^{kᵢ}` (`k ≠ 0`), the zero slice is
`Z = {u^k = 0}`. Two elementary facts replace the `(t, v)` coordinates of [Wat09, §6.4]
(Theorem 6.11) in the proof of Main Theorem 6.4:

* **projection**: every `u` in the box is within sup-distance `(u^k)^{1/S}` of the zero slice,
  `S = ∑ kᵢ` (zero the smallest active coordinate: `m^S ≤ u^k`, `exists_slice_point_dist_le`);
* **recovery**: from every zero-slice point `v`, every level `0 ≤ ℓ ≤ (r/2)^S` of the monomial is
  attained on the segment from `v` to the centre of the box within sup-distance `ℓ^{1/S}` of `v`
  (intermediate value theorem, `exists_recovery_point`).

`pow_sum_le_prod` is the monomial lower bound `m^{∑k} ≤ ∏ uᵢ^{kᵢ}` for `0 ≤ m ≤ uᵢ` on the active
coordinates.
-/

public section

open Set Finset Filter Topology

namespace SingularLearningTheory.ResolutionAtlas

open SingularLearningTheory.MaximumLikelihood

variable {d : ℕ}

theorem _root_.SingularLearningTheory.MaximumLikelihood.monomial_nonneg {k : Fin d → ℕ}
    {u : Fin d → ℝ} (hu : ∀ i, 0 ≤ u i) :
    0 ≤ ∏ i, u i ^ k i :=
  Finset.prod_nonneg fun i _ ↦ pow_nonneg (hu i) _

/-- `m^{∑k} ≤ ∏ uᵢ^{kᵢ}` when `0 ≤ m ≤ uᵢ` on every active coordinate. -/
private theorem pow_sum_le_prod {k : Fin d → ℕ} {u : Fin d → ℝ} {m : ℝ} (hm : 0 ≤ m)
    (hle : ∀ i, 0 < k i → m ≤ u i) : m ^ (∑ i, k i) ≤ ∏ i, u i ^ k i := by
  rw [← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun i _ ↦ pow_nonneg hm _) fun i _ ↦ ?_
  rcases Nat.eq_zero_or_pos (k i) with h | h
  · simp [h]
  · exact pow_le_pow_left₀ hm (hle i h) _

theorem _root_.SingularLearningTheory.MaximumLikelihood.sum_k_ne_zero {k : Fin d → ℕ}
    (hk : ∃ i, 0 < k i) : (∑ i, k i) ≠ 0 := by
  obtain ⟨i, hi⟩ := hk
  exact (Finset.sum_pos' (fun _ _ ↦ Nat.zero_le _) ⟨i, mem_univ i, hi⟩).ne'

private theorem mem_cube_iff {r : ℝ} {u : Fin d → ℝ} :
    u ∈ cube d r ↔ ∀ i, 0 ≤ u i ∧ u i ≤ r :=
  ⟨fun h i ↦ ⟨h.1 i, h.2 i⟩, fun h ↦ ⟨fun i ↦ (h i).1, fun i ↦ (h i).2⟩⟩

/-- **Projection to the zero slice.** Every point of the box is within sup-distance `(u^k)^{1/S}`
of a zero-slice point. -/
private theorem exists_slice_point_dist_le {k : Fin d → ℕ} (hk : ∃ i, 0 < k i) {r : ℝ}
    {u : Fin d → ℝ}
    (hu : u ∈ cube d r) :
    ∃ v ∈ cube d r, (∏ j, v j ^ k j) = 0 ∧
      dist u v ≤ (∏ j, u j ^ k j) ^ (((∑ j, k j : ℕ) : ℝ)⁻¹) := by
  classical
  rw [mem_cube_iff] at hu
  obtain ⟨i₀, hi₀, hmin⟩ := (Finset.univ.filter fun i ↦ 0 < k i).exists_min_image u
    ⟨hk.choose, by simp [hk.choose_spec]⟩
  have hk₀ : 0 < k i₀ := (Finset.mem_filter.mp hi₀).2
  have hS := sum_k_ne_zero hk
  refine ⟨Function.update u i₀ 0, ?_, ?_, ?_⟩
  · rw [mem_cube_iff]
    intro i
    by_cases h : i = i₀
    · subst h
      simp only [Function.update_self, le_refl, true_and]
      exact (hu i).1.trans (hu i).2
    · rw [Function.update_of_ne h]
      exact hu i
  · refine Finset.prod_eq_zero (mem_univ i₀) ?_
    rw [Function.update_self]
    exact zero_pow hk₀.ne'
  · have hd : dist u (Function.update u i₀ 0) ≤ u i₀ := by
      rw [dist_pi_le_iff (hu i₀).1]
      intro j
      by_cases h : j = i₀
      · subst h
        rw [Function.update_self, Real.dist_eq, sub_zero, abs_of_nonneg (hu j).1]
      · rw [Function.update_of_ne h, dist_self]
        exact (hu i₀).1
    refine hd.trans ?_
    have hpow : u i₀ ^ (∑ j, k j) ≤ ∏ j, u j ^ k j :=
      pow_sum_le_prod (hu i₀).1 fun i hi ↦ hmin i (by simp [hi])
    calc u i₀ = (u i₀ ^ (∑ j, k j)) ^ (((∑ j, k j : ℕ) : ℝ)⁻¹) :=
          (Real.pow_rpow_inv_natCast (hu i₀).1 hS).symm
      _ ≤ (∏ j, u j ^ k j) ^ (((∑ j, k j : ℕ) : ℝ)⁻¹) :=
          Real.rpow_le_rpow (pow_nonneg (hu i₀).1 _) hpow (by positivity)

/-- **Recovery of a monomial level near a zero-slice point.** From `v` with `v^k = 0`, every level
`0 ≤ ℓ ≤ (r/2)^S` is attained on the segment to the centre of the box within sup-distance
`ℓ^{1/S}`. -/
private theorem exists_recovery_point {k : Fin d → ℕ} (hk : ∃ i, 0 < k i) {r : ℝ} (hr : 0 < r)
    {v : Fin d → ℝ} (hv : v ∈ cube d r) (hv0 : (∏ j, v j ^ k j) = 0) {ℓ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ (r / 2) ^ (∑ j, k j)) :
    ∃ u ∈ cube d r, (∏ j, u j ^ k j) = ℓ ∧
      dist u v ≤ ℓ ^ (((∑ j, k j : ℕ) : ℝ)⁻¹) := by
  classical
  rw [mem_cube_iff] at hv
  have hS := sum_k_ne_zero hk
  have hr2 : 0 < r / 2 := half_pos hr
  obtain ⟨seg, hseg⟩ : ∃ seg : ℝ → Fin d → ℝ, seg = fun τ j ↦ (1 - τ) * v j + τ * (r / 2) :=
    ⟨_, rfl⟩
  have hsegc : Continuous seg := by
    rw [hseg]
    exact continuous_pi fun j ↦
      ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)
  have hsegbox : ∀ τ ∈ Icc (0 : ℝ) 1, seg τ ∈ cube d r := by
    intro τ hτ
    rw [mem_cube_iff]
    intro j
    have h1 := (hv j).1
    have h2 := (hv j).2
    simp only [hseg]
    constructor
    · nlinarith [hτ.1, hτ.2]
    · nlinarith [hτ.1, hτ.2]
  have hseg0 : seg 0 = v := by
    funext j
    simp [hseg]
  have hseglow : ∀ τ ∈ Icc (0 : ℝ) 1, (τ * (r / 2)) ^ (∑ j, k j) ≤ ∏ j, seg τ j ^ k j := by
    intro τ hτ
    refine pow_sum_le_prod (mul_nonneg hτ.1 hr2.le) fun j _ ↦ ?_
    simp only [hseg]
    nlinarith [(hv j).1, hτ.2]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ℓ ^ (((∑ j, k j : ℕ) : ℝ)⁻¹) := ⟨_, rfl⟩
  have hρ0 : 0 ≤ ρ := hρ ▸ Real.rpow_nonneg hℓ0 _
  have hρS : ρ ^ (∑ j, k j) = ℓ := hρ ▸ Real.rpow_inv_natCast_pow hℓ0 hS
  have hρle : ρ ≤ r / 2 := by
    have : ρ ≤ ((r / 2) ^ (∑ j, k j)) ^ (((∑ j, k j : ℕ) : ℝ)⁻¹) := by
      rw [hρ]
      exact Real.rpow_le_rpow hℓ0 hℓ (by positivity)
    rwa [Real.pow_rpow_inv_natCast hr2.le hS] at this
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : ℝ, τ₁ = ρ / (r / 2) := ⟨_, rfl⟩
  have hτ₁0 : 0 ≤ τ₁ := hτ₁ ▸ div_nonneg hρ0 hr2.le
  have hτ₁1 : τ₁ ≤ 1 := hτ₁ ▸ (div_le_one hr2).mpr hρle
  have hτ₁ρ : τ₁ * (r / 2) = ρ := hτ₁ ▸ div_mul_cancel₀ _ hr2.ne'
  have hcont : ContinuousOn (fun τ ↦ ∏ j, seg τ j ^ k j) (Icc 0 τ₁) :=
    (continuous_finsetProd _ fun j _ ↦ ((continuous_apply j).comp hsegc).pow _).continuousOn
  have h0 : (∏ j, seg 0 j ^ k j) = 0 := by
    rw [hseg0]
    exact hv0
  have h1 : ℓ ≤ ∏ j, seg τ₁ j ^ k j := by
    have := hseglow τ₁ ⟨hτ₁0, hτ₁1⟩
    rwa [hτ₁ρ, hρS] at this
  obtain ⟨τ, hτ, hτℓ⟩ := intermediate_value_Icc hτ₁0 hcont ⟨by rw [h0]; exact hℓ0, h1⟩
  refine ⟨seg τ, hsegbox τ ⟨hτ.1, hτ.2.trans hτ₁1⟩, hτℓ, ?_⟩
  rw [← hρ, dist_pi_le_iff hρ0]
  intro j
  have h1 := (hv j).1
  have h2 := (hv j).2
  simp only [hseg]
  rw [Real.dist_eq]
  have e : (1 - τ) * v j + τ * (r / 2) - v j = τ * (r / 2 - v j) := by ring
  rw [e, abs_mul, abs_of_nonneg hτ.1]
  calc τ * |r / 2 - v j| ≤ τ * (r / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hτ.1
        rw [abs_le]
        constructor <;> linarith
    _ ≤ τ₁ * (r / 2) := mul_le_mul_of_nonneg_right hτ.2 hr2.le
    _ = ρ := hτ₁ρ


/-- Rewrite the potential monomial as the square of its nonnegative half-monomial. -/
theorem _root_.SingularLearningTheory.MaximumLikelihood.monomial_square (k : Fin d → ℕ)
    (u : Fin d → ℝ) :
    (∏ j, u j ^ (2 * k j)) = (∏ j, u j ^ k j) ^ 2 := by
  rw [← Finset.prod_pow]
  exact Finset.prod_congr rfl fun j _ ↦ pow_mul' _ _ _

/-- Monomial root bound used for projection and recovery. -/
theorem _root_.Real.rpow_inv_le_of_sq_le {h a : ℝ} (hh0 : 0 ≤ h) (hha : h ^ 2 ≤ a)
    {S : ℕ} (hS : S ≠ 0) :
    h ^ ((S : ℝ)⁻¹) ≤ a ^ (((2 : ℝ) * (S : ℝ))⁻¹) := by
  have hS' : (S : ℝ) ≠ 0 := by exact_mod_cast hS
  have e : h ^ ((S : ℝ)⁻¹) = (h ^ 2) ^ (((2 : ℝ) * (S : ℝ))⁻¹) := by
    rw [← Real.rpow_natCast_mul hh0]
    congr 1
    push_cast
    field_simp
  rw [e]
  exact Real.rpow_le_rpow (sq_nonneg h) hha (by positivity)

section Atlas

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

/-- Only a type alias for the sigma of cubes, not an alternative atlas. -/
abbrev Domain := (α : R.ι) × SingularLearningTheory.cube d (R.b α)

/-- The resolved zero set: the points of the chart cubes where the loss monomial vanishes. -/
@[expose] def resolvedZeroSet : Set (Domain R) :=
  {v | (∏ j, (v.2 : Fin d → ℝ) j ^ (2 * R.k v.1 j)) = 0}

/-- The reward: the supremum over `S` of $\max(0, -\Psi(v))^2 / 4$. -/
@[expose] noncomputable def likelihoodRewardSup (S : Set (Domain R)) (Ψ : C(Domain R, ℝ)) : ℝ :=
  sSup ((fun v ↦ (max 0 (-Ψ v)) ^ 2 / 4) '' S)

/-- The supremum over `S` of the positive part $\max(0, -\Psi(v))$ of $-\Psi$. On a nonempty
compact `S` it is attained (`SingularLearningTheory.ResolutionAtlas.exists_positiveMaxOn_eq`),
it is 1-Lipschitz in $\Psi$
(`SingularLearningTheory.MaximumLikelihood.lipschitzWith_positiveMaxOn`), and its square over
four is `SingularLearningTheory.ResolutionAtlas.likelihoodRewardSup`
(`SingularLearningTheory.ResolutionAtlas.likelihoodRewardSup_eq_positiveMaxOn_sq`). -/
noncomputable def positiveMaxOn (S : Set (Domain R)) (Ψ : C(Domain R, ℝ)) : ℝ :=
  sSup ((fun v ↦ max 0 (-Ψ v)) '' S)

/-- `SingularLearningTheory.ResolutionAtlas.positiveMaxOn` over the resolved zero set
`SingularLearningTheory.ResolutionAtlas.resolvedZeroSet`, where $K \circ g$ vanishes. When
$\Psi$ is the chart process at sample size $n$ and $\hat w$ the maximum likelihood estimate,
$nK(\hat w)$ minus its square over four tends to zero in probability
(`SingularLearningTheory.MaximumLikelihood.mle_jointError_tendstoInMeasure`). -/
noncomputable abbrev positiveMax (Ψ : C(Domain R, ℝ)) : ℝ :=
  positiveMaxOn R (resolvedZeroSet R) Ψ

theorem mem_resolvedZeroSet_iff {v : Domain R} :
    v ∈ resolvedZeroSet R ↔ (∏ j, (v.2 : Fin d → ℝ) j ^ R.k v.1 j) = 0 := by
  change (∏ j, (v.2 : Fin d → ℝ) j ^ (2 * R.k v.1 j)) = 0 ↔ _
  rw [monomial_square]
  exact sq_eq_zero_iff

theorem K_g_eq_square (α : R.ι) (u : cube d (R.b α)) :
    K (R.g α u) = (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 := by
  rw [R.monomial α u u.property]
  exact monomial_square _ _

theorem mem_resolvedZeroSet_iff_K_eq_zero {v : Domain R} :
    v ∈ resolvedZeroSet R ↔ K (R.g v.1 v.2) = 0 := by
  rw [mem_resolvedZeroSet_iff, K_g_eq_square R v.1 v.2]
  exact sq_eq_zero_iff.symm

private theorem continuous_chartMonomial :
    Continuous fun v : Domain R ↦ ∏ j, (v.2 : Fin d → ℝ) j ^ R.k v.1 j := by
  refine continuous_sigma fun α ↦ ?_
  change Continuous fun u : cube d (R.b α) ↦ ∏ j, (u : Fin d → ℝ) j ^ R.k α j
  exact continuous_finsetProd _ fun j _ ↦
    ((continuous_apply j).comp continuous_subtype_val).pow _

private theorem isClosed_resolvedZeroSet : IsClosed (resolvedZeroSet R) := by
  have hset : resolvedZeroSet R =
      {v : Domain R | (∏ j, (v.2 : Fin d → ℝ) j ^ R.k v.1 j) = 0} :=
    Set.ext fun _ ↦ mem_resolvedZeroSet_iff R
  rw [hset]
  exact isClosed_eq (continuous_chartMonomial R) continuous_const

theorem isCompact_resolvedZeroSet : IsCompact (resolvedZeroSet R) :=
  (isClosed_resolvedZeroSet R).isCompact

theorem resolvedZeroSet_nonempty : (resolvedZeroSet R).Nonempty := by
  classical
  let α : R.ι := Classical.choice inferInstance
  let u : cube d (R.b α) := ⟨0, fun _ ↦ le_rfl, fun _ ↦ (R.b_pos α).le⟩
  refine ⟨⟨α, u⟩, (mem_resolvedZeroSet_iff R).mpr ?_⟩
  obtain ⟨j, hj⟩ := R.active α
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [u, hj.ne'])

/-- Typed projection, avoiding any metric on the disjoint union itself. -/
theorem exists_resolved_zero_dist_le (α : R.ι) (u : cube d (R.b α)) :
    ∃ v : cube d (R.b α), (⟨α, v⟩ : Domain R) ∈ resolvedZeroSet R ∧
      dist u v ≤ (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^
        (((∑ j, R.k α j : ℕ) : ℝ)⁻¹) := by
  obtain ⟨v, hv, hv0, hd⟩ := exists_slice_point_dist_le (R.active α) u.property
  exact ⟨⟨v, hv⟩, (mem_resolvedZeroSet_iff R).mpr hv0, hd⟩

/-- Typed recovery. Every recovered point maps into the original feasible set by
`R.g_mapsTo`; no extra admissibility-radius structure is required. -/
theorem exists_resolved_recovery_point (α : R.ι) (v : cube d (R.b α))
    (hv : (⟨α, v⟩ : Domain R) ∈ resolvedZeroSet R) {ℓ : ℝ}
    (hℓ0 : 0 ≤ ℓ) (hℓ : ℓ ≤ (R.b α / 2) ^ (∑ j, R.k α j)) :
    ∃ u : cube d (R.b α), (∏ j, (u : Fin d → ℝ) j ^ R.k α j) = ℓ ∧
      dist u v ≤ ℓ ^ (((∑ j, R.k α j : ℕ) : ℝ)⁻¹) ∧ R.g α u ∈ W := by
  obtain ⟨u, hu, huℓ, hd⟩ := exists_recovery_point (R.active α) (R.b_pos α)
    v.property ((mem_resolvedZeroSet_iff R).mp hv) hℓ0 hℓ
  exact ⟨⟨u, hu⟩, huℓ, hd, R.g_mapsTo α hu⟩

section CompactSubset

variable (S : Set (Domain R)) (hS : IsCompact S) (hne : S.Nonempty)
  (Ψ Ψ' : C(Domain R, ℝ))

private theorem continuousOn_posPart : ContinuousOn (fun v : Domain R ↦ max 0 (-Ψ v)) S :=
  (continuous_const.max Ψ.continuous.neg).continuousOn

include hS hne

theorem exists_positiveMaxOn_eq :
    ∃ v ∈ S, positiveMaxOn R S Ψ = max 0 (-Ψ v) :=
  hS.exists_sSup_image_eq hne (continuousOn_posPart R S Ψ)

omit hne in
theorem le_positiveMaxOn {v : Domain R} (hv : v ∈ S) :
    max 0 (-Ψ v) ≤ positiveMaxOn R S Ψ :=
  le_csSup (hS.image_of_continuousOn (continuousOn_posPart R S Ψ)).bddAbove
    (mem_image_of_mem _ hv)

theorem positiveMaxOn_nonneg : 0 ≤ positiveMaxOn R S Ψ := by
  obtain ⟨v, -, hv⟩ := exists_positiveMaxOn_eq R S hS hne Ψ
  rw [hv]
  exact le_max_left _ _

theorem positiveMaxOn_le_norm : positiveMaxOn R S Ψ ≤ ‖Ψ‖ := by
  obtain ⟨v, -, hv⟩ := exists_positiveMaxOn_eq R S hS hne Ψ
  rw [hv]
  refine max_le (norm_nonneg _) ?_
  have := Ψ.norm_coe_le_norm v
  rw [Real.norm_eq_abs] at this
  linarith [neg_abs_le (Ψ v)]

private theorem positiveMaxOn_le_add :
    positiveMaxOn R S Ψ ≤ positiveMaxOn R S Ψ' + ‖Ψ - Ψ'‖ := by
  obtain ⟨v, hvS, hv⟩ := exists_positiveMaxOn_eq R S hS hne Ψ
  rw [hv]
  have h1 := le_positiveMaxOn R S hS Ψ' hvS
  have h2 : |Ψ v - Ψ' v| ≤ ‖Ψ - Ψ'‖ := by
    rw [← ContinuousMap.sub_apply, ← Real.norm_eq_abs]
    exact (Ψ - Ψ').norm_coe_le_norm v
  have h3 : max 0 (-Ψ v) ≤ max 0 (-Ψ' v) + |Ψ v - Ψ' v| := by
    rcases le_total 0 (-Ψ v) with h | h
    · rw [max_eq_right h]
      have := le_max_right 0 (-Ψ' v)
      linarith [le_abs_self (Ψ' v - Ψ v), abs_sub_comm (Ψ v) (Ψ' v)]
    · rw [max_eq_left h]
      exact add_nonneg (le_max_left _ _) (abs_nonneg _)
  linarith

private theorem abs_positiveMaxOn_sub_le :
    |positiveMaxOn R S Ψ - positiveMaxOn R S Ψ'| ≤ ‖Ψ - Ψ'‖ := by
  rw [abs_sub_le_iff]
  constructor
  · linarith [positiveMaxOn_le_add R S hS hne Ψ Ψ']
  · have := positiveMaxOn_le_add R S hS hne Ψ' Ψ
    rw [norm_sub_rev] at this
    linarith

private theorem lipschitzWith_positiveMaxOn : LipschitzWith 1 (positiveMaxOn R S) := by
  refine LipschitzWith.of_dist_le_mul fun Ψ Ψ' ↦ ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  exact abs_positiveMaxOn_sub_le R S hS hne Ψ Ψ'

private theorem continuous_positiveMaxOn : Continuous (positiveMaxOn R S) :=
  (lipschitzWith_positiveMaxOn R S hS hne).continuous

/-- The sSup-of-rewards formulation agrees exactly with the square of the attained
positive maximum. This works for every nonempty compact subset, including penalty minimizers. -/
theorem likelihoodRewardSup_eq_positiveMaxOn_sq :
    likelihoodRewardSup R S Ψ = (positiveMaxOn R S Ψ) ^ 2 / 4 := by
  have hc : ContinuousOn (fun v : Domain R ↦ (max 0 (-Ψ v)) ^ 2 / 4) S :=
    (((continuous_const.max Ψ.continuous.neg).pow 2).div_const 4).continuousOn
  have hb := (hS.image_of_continuousOn hc).bddAbove
  obtain ⟨v, hv, heq⟩ := exists_positiveMaxOn_eq R S hS hne Ψ
  apply le_antisymm
  · refine csSup_le (hne.image _) ?_
    rintro y ⟨u, hu, rfl⟩
    exact div_le_div_of_nonneg_right
      (pow_le_pow_left₀ (le_max_left _ _) (le_positiveMaxOn R S hS Ψ hu) 2)
      (by norm_num)
  · rw [heq]
    exact le_csSup hb (mem_image_of_mem _ hv)

theorem likelihoodRewardSup_nonneg : 0 ≤ likelihoodRewardSup R S Ψ := by
  rw [likelihoodRewardSup_eq_positiveMaxOn_sq R S hS hne Ψ]
  positivity

theorem likelihoodRewardSup_le_norm_sq : likelihoodRewardSup R S Ψ ≤ ‖Ψ‖ ^ 2 / 4 := by
  rw [likelihoodRewardSup_eq_positiveMaxOn_sq R S hS hne Ψ]
  exact div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (positiveMaxOn_nonneg R S hS hne Ψ)
      (positiveMaxOn_le_norm R S hS hne Ψ) 2) (by norm_num)

theorem continuous_likelihoodRewardSup : Continuous (likelihoodRewardSup R S) := by
  have heq : likelihoodRewardSup R S = fun Ψ ↦ (positiveMaxOn R S Ψ) ^ 2 / 4 :=
    funext fun Ψ ↦ likelihoodRewardSup_eq_positiveMaxOn_sq R S hS hne Ψ
  rw [heq]
  exact ((continuous_positiveMaxOn R S hS hne).pow 2).div_const 4

/-- The continuous mapping used for the requested JOINT limit. -/
theorem continuous_jointLikelihoodReward :
    Continuous fun Ψ : C(Domain R, ℝ) ↦
      (likelihoodRewardSup R S Ψ, -likelihoodRewardSup R S Ψ) :=
  (continuous_likelihoodRewardSup R S hS hne).prodMk
    (continuous_likelihoodRewardSup R S hS hne).neg

end CompactSubset

/-- Convenience versions for the entire resolved zero set. -/
private theorem exists_positiveMax_eq (Ψ : C(Domain R, ℝ)) :
    ∃ v ∈ resolvedZeroSet R, positiveMax R Ψ = max 0 (-Ψ v) :=
  exists_positiveMaxOn_eq R _ (isCompact_resolvedZeroSet R) (resolvedZeroSet_nonempty R) Ψ

theorem le_positiveMax (Ψ : C(Domain R, ℝ)) {v : Domain R}
    (hv : v ∈ resolvedZeroSet R) : max 0 (-Ψ v) ≤ positiveMax R Ψ :=
  le_positiveMaxOn R _ (isCompact_resolvedZeroSet R) Ψ hv

private theorem positiveMax_nonneg (Ψ : C(Domain R, ℝ)) : 0 ≤ positiveMax R Ψ :=
  positiveMaxOn_nonneg R _ (isCompact_resolvedZeroSet R) (resolvedZeroSet_nonempty R) Ψ

theorem positiveMax_le_norm (Ψ : C(Domain R, ℝ)) : positiveMax R Ψ ≤ ‖Ψ‖ :=
  positiveMaxOn_le_norm R _ (isCompact_resolvedZeroSet R) (resolvedZeroSet_nonempty R) Ψ

private theorem lipschitzWith_positiveMax : LipschitzWith 1 (positiveMax R) :=
  lipschitzWith_positiveMaxOn R _ (isCompact_resolvedZeroSet R) (resolvedZeroSet_nonempty R)

theorem continuous_positiveMax : Continuous (positiveMax R) :=
  (lipschitzWith_positiveMax R).continuous

private theorem likelihoodRewardSup_resolvedZeroSet (Ψ : C(Domain R, ℝ)) :
    likelihoodRewardSup R (resolvedZeroSet R) Ψ = (positiveMax R Ψ) ^ 2 / 4 :=
  likelihoodRewardSup_eq_positiveMaxOn_sq R _
    (isCompact_resolvedZeroSet R) (resolvedZeroSet_nonempty R) Ψ

/-- Deterministic MLE bounds at a fixed sample. The empirical objective and field
are explicit inputs. -/
private theorem mle_core_at {n : ℕ} (hn : 0 < n) (Ψ : C(Domain R, ℝ))
    {S : (Fin d → ℝ) → ℝ}
    (hS : ∀ α (u : cube d (R.b α)), S (R.g α u) =
      (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ ⟨α, u⟩)
    {δ : ℝ}
    (hcover : ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {B r C : ℝ} (_hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hrad : ∀ α,
      (B ^ 2 / (n : ℝ)) ^ (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) ≤ r)
    (hδ : B ^ 2 / (n : ℝ) < δ)
    (hlev : ∀ α, B ^ 2 / (4 * (n : ℝ)) ≤ ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2)
    (hLip : ∀ α (u v : cube d (R.b α)),
      |Ψ ⟨α, u⟩ - Ψ ⟨α, v⟩| ≤ C * dist u v)
    {ŵ : Fin d → ℝ} (hŵ : ŵ ∈ W) (hmin : ∀ w ∈ W, S ŵ ≤ S w)
    (hloc : (n : ℝ) * K ŵ ≤ B ^ 2) (hM : positiveMax R Ψ ≤ B) :
    |S ŵ + (positiveMax R Ψ) ^ 2 / 4| ≤
        positiveMax R Ψ * (C * r) / 2 + (C * r) ^ 2 / 4 ∧
      |(n : ℝ) * K ŵ - (positiveMax R Ψ) ^ 2 / 4| ≤
        mleErr (positiveMax R Ψ) (C * r) := by
  let M := positiveMax R Ψ
  have hM0 : 0 ≤ M := positiveMax_nonneg R Ψ
  have hM' : M ≤ B := hM
  have hω0 : 0 ≤ C * r := mul_nonneg hC hr
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.mpr hn'
  have hKŵ : K ŵ ≤ B ^ 2 / (n : ℝ) := by rw [le_div_iff₀ hn']; linarith
  obtain ⟨α, û, hgû⟩ := hcover ŵ hŵ (hKŵ.trans_lt hδ)
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = ∏ j, (û : Fin d → ℝ) j ^ R.k α j := ⟨_, rfl⟩
  have hh0 : 0 ≤ h := hh ▸ monomial_nonneg
    (fun j ↦ û.property.1 j)
  have hKh : K ŵ = h ^ 2 := by
    rw [← hgû, K_g_eq_square R α û, ← hh]
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Ψ ⟨α, û⟩ := ⟨_, rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt n * h := ⟨_, rfl⟩
  have hx0 : 0 ≤ x := hx ▸ mul_nonneg hsn.le hh0
  have hx2 : x ^ 2 = (n : ℝ) * K ŵ := by
    rw [hx, mul_pow, Real.sq_sqrt hn'.le, hKh]
  have hq : S ŵ = x ^ 2 + x * z := by
    rw [← hgû, hS α û, ← hh, ← hz, hx, mul_pow, Real.sq_sqrt hn'.le]
  have hsum : ∀ α, (∑ j, R.k α j) ≠ 0 := fun α ↦ sum_k_ne_zero (R.active α)
  -- Project the lifted estimator to a zero in the same chart.
  obtain ⟨vz, hvz, hdvz⟩ := exists_resolved_zero_dist_le R α û
  have hdvzr : dist û vz ≤ r := by
    rw [← hh] at hdvz
    exact hdvz.trans
      ((Real.rpow_inv_le_of_sq_le hh0 (by rw [← hKh]; exact hKŵ) (hsum α)).trans (hrad α))
  have hzvz : |z - Ψ ⟨α, vz⟩| ≤ C * r := by
    rw [hz]
    exact (hLip α û vz).trans (mul_le_mul_of_nonneg_left hdvzr hC)
  have hproj : max 0 (-z) ≤ M + C * r := by
    have h1 : max 0 (-Ψ ⟨α, vz⟩) ≤ M := le_positiveMax R Ψ hvz
    have h2 := le_max_right 0 (-Ψ ⟨α, vz⟩)
    have h3 := (abs_le.mp hzvz).1
    refine max_le (by linarith) (by linarith)
  -- Recover a near-optimal monomial level near an attained zero-set maximizer.
  obtain ⟨⟨α', v'⟩, hv'Z, hMeq⟩ := exists_positiveMax_eq R Ψ
  change M = max 0 (-Ψ ⟨α', v'⟩) at hMeq
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : ℝ, ℓ = M / (2 * Real.sqrt n) := ⟨_, rfl⟩
  have hℓ0 : 0 ≤ ℓ := hℓ ▸ div_nonneg hM0 (by positivity)
  have hℓsq : ℓ ^ 2 = M ^ 2 / (4 * (n : ℝ)) := by
    rw [hℓ, div_pow, mul_pow, Real.sq_sqrt hn'.le]
    ring
  have hℓB : ℓ ^ 2 ≤ B ^ 2 / (4 * (n : ℝ)) := by
    rw [hℓsq]
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hM0 hM' 2) (by positivity)
  have hℓlev : ℓ ≤ (R.b α' / 2) ^ (∑ j, R.k α' j) := by
    have hc0 : 0 ≤ (R.b α' / 2) ^ (∑ j, R.k α' j) :=
      pow_nonneg (half_pos (R.b_pos α')).le _
    exact pow_le_pow_iff_left₀ hℓ0 hc0 two_ne_zero |>.mp (hℓB.trans (hlev α'))
  obtain ⟨u', hu'ℓ, hdu', hgu'⟩ :=
    exists_resolved_recovery_point R α' v' hv'Z hℓ0 hℓlev
  have hdu'r : dist u' v' ≤ r := by
    refine hdu'.trans ((Real.rpow_inv_le_of_sq_le hℓ0 ?_ (hsum α')).trans (hrad α'))
    refine hℓB.trans ?_
    exact div_le_div_of_nonneg_left (sq_nonneg B) hn' (by linarith)
  have hqu' : S (R.g α' u') = M ^ 2 / 4 + M / 2 * Ψ ⟨α', u'⟩ := by
    have e1 : (n : ℝ) * (M / (2 * Real.sqrt n)) ^ 2 = M ^ 2 / 4 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hn'.le]
      field_simp [hn'.ne']; ring
    have e2 : Real.sqrt n * (M / (2 * Real.sqrt n)) = M / 2 := by
      field_simp [hsn.ne']
    rw [hS α' u', hu'ℓ, hℓ, e1, e2]
  have hzu' : |Ψ ⟨α', u'⟩ - Ψ ⟨α', v'⟩| ≤ C * r :=
    (hLip α' u' v').trans (mul_le_mul_of_nonneg_left hdu'r hC)
  have hrec : S ŵ ≤ -(M ^ 2) / 4 + M * (C * r) / 2 := by
    have h1 := hmin _ hgu'
    rw [hqu'] at h1
    rcases eq_or_lt_of_le hM0 with hM0' | hMpos
    · rw [← hM0'] at h1 ⊢
      simpa using h1
    · have hMv : M = -Ψ ⟨α', v'⟩ := by
        rw [hMeq]
        rcases le_or_gt (-Ψ ⟨α', v'⟩) 0 with hneg | hpos
        · rw [max_eq_left hneg] at hMeq
          linarith
        · exact max_eq_right hpos.le
      have h2 : Ψ ⟨α', u'⟩ ≤ -M + C * r := by
        have := (abs_le.mp hzu').2
        linarith
      have h3 : M / 2 * Ψ ⟨α', u'⟩ ≤ M / 2 * (-M + C * r) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
      nlinarith
  obtain ⟨hb1, hb2⟩ := mle_core_bounds hx0 hω0 hM0 hq rfl hproj hrec
  rw [hx2] at hb2
  exact ⟨hb1, hb2⟩

/-- A deterministic bound uniform over fields with positive maximum at most B. -/
theorem mle_core_at_le {n : ℕ} (hn : 0 < n) (Ψ : C(Domain R, ℝ))
    {S : (Fin d → ℝ) → ℝ}
    (hS : ∀ α (u : cube d (R.b α)), S (R.g α u) =
      (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ ⟨α, u⟩)
    {δ : ℝ}
    (hcover : ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {B r C : ℝ} (hB : 0 ≤ B) (hr : 0 ≤ r) (hC : 0 ≤ C)
    (hrad : ∀ α,
      (B ^ 2 / (n : ℝ)) ^ (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) ≤ r)
    (hδ : B ^ 2 / (n : ℝ) < δ)
    (hlev : ∀ α, B ^ 2 / (4 * (n : ℝ)) ≤ ((R.b α / 2) ^ (∑ j, R.k α j)) ^ 2)
    (hLip : ∀ α (u v : cube d (R.b α)),
      |Ψ ⟨α, u⟩ - Ψ ⟨α, v⟩| ≤ C * dist u v)
    {ŵ : Fin d → ℝ} (hŵ : ŵ ∈ W) (hmin : ∀ w ∈ W, S ŵ ≤ S w)
    (hloc : (n : ℝ) * K ŵ ≤ B ^ 2) (hM : positiveMax R Ψ ≤ B) :
    |S ŵ + likelihoodRewardSup R (resolvedZeroSet R) Ψ| ≤
        B * (C * r) / 2 + (C * r) ^ 2 / 4 ∧
      |(n : ℝ) * K ŵ - likelihoodRewardSup R (resolvedZeroSet R) Ψ| ≤
        mleErr B (C * r) := by
  rw [likelihoodRewardSup_resolvedZeroSet]
  obtain ⟨h1, h2⟩ := mle_core_at R hn Ψ hS hcover hB hr hC hrad hδ hlev hLip hŵ hmin hloc hM
  refine ⟨h1.trans ?_, h2.trans ?_⟩
  · have := mul_le_mul_of_nonneg_right hM (mul_nonneg hC hr)
    linarith
  · exact mleErr_mono_left (mul_nonneg hC hr) (positiveMax_nonneg R Ψ) hM

end Atlas
end SingularLearningTheory.ResolutionAtlas
