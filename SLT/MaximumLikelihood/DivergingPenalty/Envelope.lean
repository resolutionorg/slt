/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.MaximumLikelihood.Penalty.Envelope
public import SLT.MaximumLikelihood.Geometry
public import SLT.MeasureTheory.Function.AsympUnifIntegrable

/-!
# DivergingPenaltyEnvelope

Sharp localization for a subpolynomial diverging penalty.
-/

public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace SingularLearningTheory.MaximumLikelihood

/-- The scalar root estimate used for sharp localization. -/
private theorem rpow_inv_natCast_le_one_add {x : ℝ} (hx : 0 ≤ x) {S : ℕ} (hS : S ≠ 0) :
    x ^ ((S : ℝ)⁻¹) ≤ 1 + x := by
  have hS1 : (1 : ℝ) ≤ S := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hS
  have hinv : (S : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hS1
  rcases le_or_gt x 1 with hx1 | hx1
  · have := Real.rpow_le_one hx hx1 (by positivity : (0 : ℝ) ≤ (S : ℝ)⁻¹)
    linarith
  · calc x ^ ((S : ℝ)⁻¹) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1.le hinv
      _ = x := Real.rpow_one x
      _ ≤ 1 + x := by linarith

section Deterministic
variable {d : ℕ} {K φ σ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)

private theorem penalized_sharp_localization_at {n : ℕ} (hn : 0 < n)
    (Ψ : C(ResolutionAtlas.Domain R, ℝ)) {S : (Fin d → ℝ) → ℝ}
    (hS : ∀ α (u : cube d (R.b α)), S (R.g α u) =
      (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ ⟨α, u⟩)
    {δ : ℝ} (hcover : ∀ w ∈ W, K w < δ →
      ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {Λ a Sg H : ℝ} (hΛ : 0 ≤ Λ) (ha : 0 ≤ a) (hH : 0 ≤ H)
    (hσLip : ∀ α (u v : cube d (R.b α)),
      |σ (R.g α u) - σ (R.g α v)| ≤ Λ * dist u v)
    (hsmall : 4 * a * Sg ≤ (n : ℝ) * δ / 2)
    (hscale : ∀ α, a * Λ / (n : ℝ) ^ (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) ≤ 1)
    (hNorm : ‖Ψ‖ ≤ H) {ŵ : Fin d → ℝ} (hŵ : ŵ ∈ W)
    (hmin : ∀ w ∈ W, S ŵ + a * σ ŵ ≤ S w + a * σ w)
    (hloc : (n : ℝ) * K ŵ ≤ 2 * H ^ 2 + 4 * a * Sg)
    (hT : |S ŵ| ≤ 2 * ((n : ℝ) * K ŵ) + H ^ 2) :
    (n : ℝ) * K ŵ ≤ 4 * H ^ 2 + 8 ∧ |S ŵ| ≤ 9 * H ^ 2 + 16 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn'
  suffices hK : (n : ℝ) * K ŵ ≤ 4 * H ^ 2 + 8 by constructor <;> linarith
  by_cases hKδ : δ ≤ K ŵ
  · have h1 := mul_le_mul_of_nonneg_left hKδ hn'.le
    nlinarith [sq_nonneg H]
  · obtain ⟨α, û, hgû⟩ := hcover ŵ hŵ (not_le.mp hKδ)
    obtain ⟨h, hh⟩ : ∃ h : ℝ, h = ∏ j, (û : Fin d → ℝ) j ^ R.k α j := ⟨_, rfl⟩
    have hh0 : 0 ≤ h := hh ▸ monomial_nonneg (fun j ↦ û.property.1 j)
    have hKh : K ŵ = h ^ 2 := by rw [← hgû, ResolutionAtlas.K_g_eq_square R α û, ← hh]
    obtain ⟨z, hz⟩ : ∃ z : ℝ, z = Ψ ⟨α, û⟩ := ⟨_, rfl⟩
    have hzH : |z| ≤ H := by
      rw [hz]
      have hp := Ψ.norm_coe_le_norm ⟨α, û⟩
      rw [Real.norm_eq_abs] at hp
      exact hp.trans hNorm
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = Real.sqrt n * h := ⟨_, rfl⟩
    have hx0 : 0 ≤ x := hx ▸ mul_nonneg hsn.le hh0
    have hx2 : x ^ 2 = (n : ℝ) * K ŵ := by
      rw [hx, mul_pow, Real.sq_sqrt hn'.le, hKh]
    have hq : S ŵ = x ^ 2 + x * z := by
      rw [← hgû, hS α û, ← hh, ← hz, hx, mul_pow, Real.sq_sqrt hn'.le]
    obtain ⟨vz, hvz, hdvz⟩ := ResolutionAtlas.exists_resolved_zero_dist_le R α û
    have hvz0 := (ResolutionAtlas.mem_resolvedZeroSet_iff R).mp hvz
    have hSfoot : S (R.g α vz) = 0 := by rw [hS α vz, hvz0]; ring
    have hcmp := hmin _ (R.g_mapsTo α vz.property)
    rw [hSfoot, zero_add, hq] at hcmp
    have hσ : σ (R.g α vz) - σ ŵ ≤ Λ * dist û vz := by
      rw [← hgû]
      have hp := (abs_le.mp (hσLip α vz û)).2
      rw [dist_comm] at hp
      exact hp
    have hsum := sum_k_ne_zero (R.active α)
    have hroot : h ^ (((∑ j, R.k α j : ℕ) : ℝ)⁻¹) =
        x ^ (((∑ j, R.k α j : ℕ) : ℝ)⁻¹) /
          (n : ℝ) ^ (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) := by
      have hhx : h = x / Real.sqrt n := by rw [hx]; field_simp [hsn.ne']
      rw [hhx, Real.div_rpow hx0 hsn.le, Real.sqrt_eq_rpow, ← Real.rpow_mul hn'.le]
      congr 2
      field_simp
    have hxS := rpow_inv_natCast_le_one_add hx0 hsum
    have hq_le : x ^ 2 + x * z ≤ 1 + x := by
      have h1 : x ^ 2 + x * z ≤ a * (Λ * dist û vz) := by
        have hp := mul_le_mul_of_nonneg_left hσ ha
        nlinarith only [hp, hcmp]
      have h2 : a * (Λ * dist û vz) ≤ a * Λ * h ^ (((∑ j, R.k α j : ℕ) : ℝ)⁻¹) := by
        rw [← hh] at hdvz
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hdvz (mul_nonneg ha hΛ)
      have h3 : a * Λ * h ^ (((∑ j, R.k α j : ℕ) : ℝ)⁻¹) =
          (a * Λ / (n : ℝ) ^ (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹)) *
            x ^ (((∑ j, R.k α j : ℕ) : ℝ)⁻¹) := by rw [hroot]; ring
      have h4 := mul_le_mul (hscale α) hxS (Real.rpow_nonneg hx0 _) zero_le_one
      rw [← h3, one_mul] at h4
      exact h1.trans (h2.trans h4)
    have hxz : -(x * H) ≤ x * z := by
      have hp := (abs_le.mp hzH).1
      nlinarith
    have hxb : x ≤ H + 2 := by
      by_contra hcon
      push Not at hcon
      nlinarith
    rw [← hx2]
    nlinarith [sq_nonneg (H - 2)]

end Deterministic

section Stochastic
variable {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {K φ σ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}
  (R : ResolutionAtlas K φ W)
  {Ψ : ℕ → Ω → C(ResolutionAtlas.Domain R, ℝ)} {H : ℕ → Ω → ℝ}
  {Kn : ℕ → Ω → (Fin d → ℝ) → ℝ} {ŵ : ℕ → Ω → Fin d → ℝ}
  {aSeq : ℕ → ℝ}

theorem divergingPenalty_sharp_localization_ae
    (hK0 : ∀ w ∈ W, 0 ≤ K w) (hH0 : ∀ n ω, 0 ≤ H n ω)
    (henv : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ w ∈ W,
      Real.sqrt n * |Kn n ω w - K w| ≤ Real.sqrt (K w) * H n ω)
    {w₀ : Fin d → ℝ} (hw₀ : w₀ ∈ W) (hw₀K : K w₀ = 0)
    (hŵW : ∀ n, ∀ᵐ ω ∂P, ŵ n ω ∈ W)
    (haSeq : ∀ n, 0 ≤ aSeq n) {Sg : ℝ} (hSg : 0 ≤ Sg)
    (hσb : ∀ w ∈ W, |σ w| ≤ Sg)
    (hmin : ∀ n : ℕ, ∀ᵐ ω ∂P, ∀ w ∈ W,
      (n : ℝ) * Kn n ω (ŵ n ω) + aSeq n * σ (ŵ n ω) ≤
        (n : ℝ) * Kn n ω w + aSeq n * σ w)
    {δ : ℝ} (hδ : 0 < δ)
    (hcover : ∀ w ∈ W, K w < δ → ∃ α, ∃ u : cube d (R.b α), R.g α u = w)
    {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hσLip : ∀ α (u v : cube d (R.b α)),
      |σ (R.g α u) - σ (R.g α v)| ≤ Λ * dist u v)
    (hNorm : ∀ n ω, ‖Ψ n ω‖ ≤ H n ω)
    (hS : ∀ n : ℕ, 1 ≤ n → ∀ᵐ ω ∂P, ∀ α (u : cube d (R.b α)),
      (n : ℝ) * Kn n ω (R.g α u) = (n : ℝ) * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) ^ 2 +
        Real.sqrt n * (∏ j, (u : Fin d → ℝ) j ^ R.k α j) * Ψ n ω ⟨α, u⟩)
    (hslow : ∀ r : ℝ, 0 < r → Tendsto (fun n : ℕ ↦ aSeq n / (n : ℝ) ^ r) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      0 ≤ (n : ℝ) * K (ŵ n ω) ∧
      (n : ℝ) * K (ŵ n ω) ≤ 4 * (H n ω) ^ 2 + 8 ∧
      |(n : ℝ) * Kn n ω (ŵ n ω)| ≤ 9 * (H n ω) ^ 2 + 16 := by
  have hev1 : ∀ᶠ n : ℕ in atTop, 4 * aSeq n * Sg ≤ (n : ℝ) * δ / 2 := by
    have ht : Tendsto (fun n : ℕ ↦ 4 * Sg * (aSeq n / (n : ℝ))) atTop (𝓝 0) := by
      simpa only [Real.rpow_one, mul_zero] using (hslow 1 one_pos).const_mul (4 * Sg)
    filter_upwards [ht.eventually (eventually_lt_nhds (half_pos hδ)), eventually_ge_atTop 1]
      with n hn hn1
    have hn' : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    -- The equivalent division form avoids assumptions about Sg being nonzero.
    have hdiv : (4 * aSeq n * Sg) / (n : ℝ) < δ / 2 := by
      convert hn using 1 <;> ring
    have hb := (div_lt_iff₀ hn').mp hdiv
    linarith
  have hev2 : ∀ᶠ n : ℕ in atTop, ∀ α, aSeq n * Λ / (n : ℝ) ^
      (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) ≤ 1 := by
    rw [eventually_all]
    intro α
    have hs := sum_k_ne_zero (R.active α)
    have hc : (0 : ℝ) < (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹) := by positivity
    have ht : Tendsto (fun n : ℕ ↦ aSeq n * Λ / (n : ℝ) ^
        (((2 : ℝ) * ((∑ j, R.k α j : ℕ) : ℝ))⁻¹)) atTop (𝓝 0) := by
      convert (hslow _ hc).mul_const Λ using 1
      · funext n; ring
      · simp
    exact (ht.eventually (eventually_lt_nhds zero_lt_one)).mono fun n hn ↦ hn.le
  filter_upwards [hev1, hev2, eventually_ge_atTop 1] with n hn1 hn2 hn
  filter_upwards [penalized_localization_ae hK0 hH0 henv hw₀ hw₀K hŵW haSeq hSg hσb hmin hn,
    hŵW n, hmin n, hS n hn] with ω hloc hw hm hs
  exact ⟨hloc.1, penalized_sharp_localization_at R (S := fun w ↦ (n : ℝ) * Kn n ω w)
    (by omega) (Ψ n ω) hs hcover
    hΛ (haSeq n) (hH0 n ω) hσLip hn1 hn2 (hNorm n ω) hw hm hloc.2.1 hloc.2.2⟩

/-- Sharp localization gives AUI from the same fourth-moment envelope, without any
factor aSeq n in the dominating family. -/
theorem divergingPenalty_aui [IsProbabilityMeasure P]
    (hHm : ∀ n, Measurable (H n)) {D : ℝ≥0∞} (hD : D ≠ ⊤)
    (hfour : ∀ n, ∫⁻ ω, ‖H n ω‖ₑ ^ 4 ∂P ≤ D)
    (hsharp : ∀ᶠ n : ℕ in atTop, ∀ᵐ ω ∂P,
      0 ≤ (n : ℝ) * K (ŵ n ω) ∧
      (n : ℝ) * K (ŵ n ω) ≤ 4 * (H n ω) ^ 2 + 8 ∧
      |(n : ℝ) * Kn n ω (ŵ n ω)| ≤ 9 * (H n ω) ^ 2 + 16) :
    AsympUnifIntegrable P (fun n ω ↦ (n : ℝ) * K (ŵ n ω)) ∧
      AsympUnifIntegrable P (fun n ω ↦ (n : ℝ) * Kn n ω (ŵ n ω)) := by
  have hG := asympUnifIntegrable_affine_square hHm hD hfour 4 8
  have hT := asympUnifIntegrable_affine_square hHm hD hfour 9 16
  refine ⟨hG.of_abs_le ?_, hT.of_abs_le ?_⟩
  · filter_upwards [hsharp] with n hn
    filter_upwards [hn] with ω hω
    rw [abs_of_nonneg hω.1]
    exact hω.2.1
  · exact hsharp.mono fun n hn ↦ hn.mono fun ω hω ↦ hω.2.2

end Stochastic
end SingularLearningTheory.MaximumLikelihood
