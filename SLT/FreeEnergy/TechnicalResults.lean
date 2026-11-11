/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.Analysis.SpecialFunctions.Pow.LogBounds
public import SLT.SingularIntegrals.NormalCrossing

/-!
# Two technical results

Formalises the elementary inequalities of [Hit26,
Section 5.1] — the pieces of [Wat09, Theorems 4.8 and
4.9] that stand on their own, independently of the normal-crossing computation.

| Thesis | Lean |
| --- | --- |
| [Hit26, Lemma 5.2.4] | `half_sq_sub_sq_le` |
| [Hit26, Lemma 5.1.2] (1) | `exists_log_rpow_le` |
| [Hit26, Lemma 5.1.2] (1), `ℕ` exponents | `Real.exists_log_pow_le`
|
| [Hit26, Lemma 5.1.2] (2) | `Real.exists_log_pow_div_rpow_le` |
| first display in the proof of [Hit26, Theorem 5.1.1] | `Real.abs_sqrt_mul_le`, |
| | `SingularLearningTheory.NormalCrossing.exponent_bounds` |
| [Hit26, Equation (5.1.1)], `Z^p(n, ξ, φ)` | `normalCrossingIntegral` |
| [Hit26, Theorem 5.1.1] ([Wat09, Theorem 4.8]) | `blockIntegral_bounds` |

[Wat09, Theorem 4.8] is proved here from [Wat09, Theorem 4.7] (`blockIntegral₀_lower_bound`,
`blockIntegral₀_upper_bound`); [Wat09, Theorem 4.9] is proved quantitatively in
`FreeEnergy/QuantitativeApprox.lean`. The qualitative frozen-kernel estimate used by the free energy
proof is in `FreeEnergy/FrozenKernel.lean`.
-/

public section

open MeasureTheory Nat Set

namespace SingularLearningTheory

open SingularLearningTheory.NormalCrossing

/-! ## The `a`-`b`-`n` inequality -/

/-- [Hit26, Lemma 5.2.4]: for `n ≥ 1`,
`n a² - a b ≥ ½ (a² - b²)`.

Used in the proof of [Hit26, Theorem 5.2.6] to bound `n K_n(w)` below
by `½ (n K(w) - ψ_n(w)²)` on the region `{K ≥ ε}`. -/
private theorem half_sq_sub_sq_le (a b : ℝ) {n : ℝ} (hn : 1 ≤ n) :
    (a ^ 2 - b ^ 2) / 2 ≤ n * a ^ 2 - a * b := by
  nlinarith [sq_nonneg (a - b), sq_nonneg a]

/-- The arithmetic-geometric bound opening the proof of [Hit26,
Theorem 5.1.1]: `|√c · ξ| ≤ ½ (c + ξ²)` for `c ≥ 0`.

[Hit26] applies this with `c = n K(u, v)`, giving
`|√(n K) ξ| ≤ ½ (n K + ‖ξ‖²)`, which is what turns `Z^p(n, ξ, φ)` into a
two-sided sandwich between `Z^p(3n/2)` and `Z^p(n/2)`. -/
theorem _root_.Real.abs_sqrt_mul_le {c : ℝ} (hc : 0 ≤ c) (ξ : ℝ) :
    |Real.sqrt c * ξ| ≤ (c + ξ ^ 2) / 2 := by
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg c)]
  nlinarith [sq_nonneg (Real.sqrt c - |ξ|), sq_abs ξ, abs_nonneg ξ,
    Real.sqrt_nonneg c]

/-! ## Simple bounds

[Hit26, Lemma 5.1.2]. Both parts say that a
smaller power of `log n`, or a larger power of `n` in the denominator, can be
absorbed into a constant. -/

/-- [Hit26, Lemma 5.1.2], part 1: for
`1 ≤ r ≤ s` there is `C > 0` with `(log n)^r ≤ C (log n)^s` for all `n ≥ 2`.

`C = 1` is *not* enough: `log 2 ≈ 0.693 < 1`, so for `n` just above `2` raising to
the larger exponent `s` makes the quantity *smaller*. The constant below handles
that range by bounding `(log n)^r` by `1` and `(log n)^s` below by `(log 2)^s`. -/
private theorem exists_log_rpow_le {r s : ℝ} (hr : 1 ≤ r) (hrs : r ≤ s) :
    ∃ C > 0, ∀ n : ℝ, 2 ≤ n → Real.log n ^ r ≤ C * Real.log n ^ s := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos (hr.trans hrs)
  have h2s : (0 : ℝ) < Real.log 2 ^ s := Real.rpow_pos_of_pos hl2 s
  refine ⟨max 1 (Real.log 2 ^ s)⁻¹, lt_of_lt_of_le one_pos (le_max_left _ _), fun n hn ↦ ?_⟩
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos hn
  have hlpos : (0 : ℝ) < Real.log n := lt_of_lt_of_le hl2 hln
  have hns : (0 : ℝ) < Real.log n ^ s := Real.rpow_pos_of_pos hlpos s
  rcases le_or_gt 1 (Real.log n) with h1 | h1
  · -- `log n ≥ 1`: the larger exponent dominates, so the `1` in the `max` suffices.
    calc Real.log n ^ r ≤ Real.log n ^ s := Real.rpow_le_rpow_of_exponent_le h1 hrs
      _ ≤ max 1 (Real.log 2 ^ s)⁻¹ * Real.log n ^ s := by
          nlinarith [le_max_left (1 : ℝ) (Real.log 2 ^ s)⁻¹]
  · -- `log 2 ≤ log n < 1`: bound the numerator by `1` and the denominator by `(log 2)^s`.
    have hr1 : Real.log n ^ r ≤ 1 :=
      Real.rpow_le_one hlpos.le h1.le (by linarith)
    have h2n : Real.log 2 ^ s ≤ Real.log n ^ s := Real.rpow_le_rpow hl2.le hln hs0.le
    have : (1 : ℝ) ≤ (Real.log 2 ^ s)⁻¹ * Real.log n ^ s := by
      rw [le_inv_mul_iff₀ h2s, mul_one]; exact h2n
    calc Real.log n ^ r ≤ 1 := hr1
      _ ≤ (Real.log 2 ^ s)⁻¹ * Real.log n ^ s := this
      _ ≤ max 1 (Real.log 2 ^ s)⁻¹ * Real.log n ^ s :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hns.le

/-- `(log n)^r ≤ C (log n)^s` for `r ≤ s` and `n ≥ 2`. Natural-exponent version of
[Hit26, Lemma 5.1.2] (1), which also covers `r = 0`.
No thesis counterpart as stated. -/
theorem _root_.Real.exists_log_pow_le {r s : ℕ} (hrs : r ≤ s) :
    ∃ C > 0, ∀ n : ℝ, 2 ≤ n → Real.log n ^ r ≤ C * Real.log n ^ s := by
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨(Real.log 2 ^ (s - r))⁻¹, by positivity, fun n hn ↦ ?_⟩
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos hn
  have h2 : Real.log 2 ^ (s - r) ≤ Real.log n ^ (s - r) := pow_le_pow_left₀ hl2.le hln _
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  calc Real.log n ^ r * Real.log 2 ^ (s - r) ≤ Real.log n ^ r * Real.log n ^ (s - r) :=
        mul_le_mul_of_nonneg_left h2 (pow_nonneg (hl2.le.trans hln) r)
    _ = Real.log n ^ s := by rw [← pow_add, Nat.add_sub_cancel' hrs]

/-- [Hit26, Lemma 5.1.2], part 2: for
`r s : ℕ` and `λ, δ > 0` there is `C > 0` with
`(log n)^r / n^(λ+δ) ≤ C (log n)^s / n^λ` for all `n ≥ 2`.

Since `n^(λ+δ) = n^λ · n^δ`, this reduces to `(log n)^r ≤ C n^δ (log n)^s`, which
follows from `Real.log_le_rpow_div` (with `c = δ/r`) and `(log n)^s ≥ (log 2)^s`.
Note `r ≤ s` is *not* needed: `n^δ` beats every power of `log n`. [Hit26]'s
hypothesis `λ > 0` is likewise unused, and is kept only for fidelity. -/
theorem _root_.Real.exists_log_pow_div_rpow_le (r s : ℕ) {lam delta : ℝ} (_hlam : 0 < lam)
    (hdelta : 0 < delta) :
    ∃ C > 0, ∀ n : ℝ, 2 ≤ n →
      Real.log n ^ r / n ^ (lam + delta) ≤ C * (Real.log n ^ s / n ^ lam) := by
  -- Step 1: `(log n)^r ≤ A * n^δ` for an explicit `A`.
  obtain ⟨A, hA0, hA⟩ : ∃ A > 0, ∀ n : ℝ, 2 ≤ n → Real.log n ^ r ≤ A * n ^ delta := by
    rcases Nat.eq_zero_or_pos r with rfl | hr
    · exact ⟨1, one_pos, fun n hn ↦ by
        simpa using Real.one_le_rpow (by linarith) hdelta.le⟩
    · refine ⟨(r / delta) ^ r, pow_pos (div_pos (by exact_mod_cast hr) hdelta) r, fun n hn ↦ ?_⟩
      have hn1 : (1 : ℝ) ≤ n := by linarith
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
      have hstep : Real.log n ≤ (r / delta) * n ^ (delta / r) := by
        have h := Real.log_le_rpow_div (zero_le_one.trans hn1) (div_pos hdelta hrpos)
        calc Real.log n ≤ n ^ (delta / r) / (delta / r) := h
          _ = (r / delta) * n ^ (delta / r) := by field_simp
      have hpow := pow_le_pow_left₀ (Real.log_nonneg hn1) hstep r
      rw [mul_pow, ← Real.rpow_natCast (n ^ (delta / (r : ℝ))) r, ← Real.rpow_mul (by linarith),
        div_mul_cancel₀ _ hrpos.ne'] at hpow
      exact hpow
  -- Step 2: divide through by `n^λ` and bound `(log n)^s` below by `(log 2)^s`.
  have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  refine ⟨A / Real.log 2 ^ s, div_pos hA0 (pow_pos hl2 s), fun n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) < n := by linarith
  have hnlam : (0 : ℝ) < n ^ lam := Real.rpow_pos_of_pos hn0 lam
  have hndelta : (0 : ℝ) < n ^ delta := Real.rpow_pos_of_pos hn0 delta
  have hln : Real.log 2 ≤ Real.log n := Real.log_le_log two_pos hn
  have h2s : Real.log 2 ^ s ≤ Real.log n ^ s := pow_le_pow_left₀ hl2.le hln s
  have key : Real.log n ^ r / n ^ delta ≤ A / Real.log 2 ^ s * Real.log n ^ s := by
    rw [div_le_iff₀ hndelta]
    calc Real.log n ^ r ≤ A * n ^ delta := hA n hn
      _ ≤ A / Real.log 2 ^ s * Real.log n ^ s * n ^ delta := by
          have hAle : A ≤ A / Real.log 2 ^ s * Real.log n ^ s := by
            rw [div_mul_eq_mul_div, le_div_iff₀ (pow_pos hl2 s)]
            exact mul_le_mul_of_nonneg_left h2s hA0.le
          nlinarith
  rw [Real.rpow_add hn0, div_mul_eq_div_div]
  have hmul := mul_le_mul_of_nonneg_right key (inv_pos.mpr hnlam).le
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

/-! ## [Wat09, Theorem 4.8] -/

/-- [Hit26, Equation (5.1.1)]:
`Z^p(n, ξ, φ) = ∫_{[0,b]^{m+m'}} K^p e^{-nβK + √n β √K ξ} u^h v^{h'} φ du dv`:
`SingularLearningTheory.normalCrossingIntegral` in block coordinates, with real exponents. -/
@[expose] noncomputable def NormalCrossing.blockIntegral {m m' : ℕ} (k : Fin m → ℕ) (h : Fin m → ℝ)
    (k' : Fin m' → ℕ)
    (h' : Fin m' → ℝ) (b β p n : ℝ) (ξ f : (Fin m → ℝ) × (Fin m' → ℝ) → ℝ) : ℝ :=
  ∫ z in cube m b ×ˢ cube m' b,
    potential k k' z ^ p *
      Real.exp (-(n * β * potential k k' z) +
        Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
      NormalCrossing.monomialWeight h h' z * f z

/-- The first display in the proof of [Hit26, Theorem 5.1.1], in
exponent form: for `K ≥ 0`, `n ≥ 0`, `β ≥ 0` and `|ξ| ≤ Mξ`, the exponent of
`Z^p(n, ξ, φ)` lies between those of `Z^p(3n/2)` and `Z^p(n/2)`, shifted by `∓ β Mξ² / 2`. -/
theorem NormalCrossing.exponent_bounds {K n β ξ Mξ : ℝ} (hK : 0 ≤ K) (hn : 0 ≤ n) (hβ : 0 ≤ β)
    (hξ : |ξ| ≤ Mξ) :
    -(n * (3 * β / 2) * K) + -(β * Mξ ^ 2 / 2)
        ≤ -(n * β * K) + Real.sqrt n * β * Real.sqrt K * ξ ∧
      -(n * β * K) + Real.sqrt n * β * Real.sqrt K * ξ
        ≤ -(n * (β / 2) * K) + β * Mξ ^ 2 / 2 := by
  have hsq : ξ ^ 2 ≤ Mξ ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hξ 2
  have habs := Real.abs_sqrt_mul_le (mul_nonneg hn hK) ξ
  rw [abs_le] at habs
  have hmul : Real.sqrt n * β * Real.sqrt K * ξ = β * (Real.sqrt (n * K) * ξ) := by
    rw [Real.sqrt_mul hn]; ring
  rw [hmul]
  have h1 := mul_le_mul_of_nonneg_left habs.1 hβ
  have h2 := mul_le_mul_of_nonneg_left habs.2 hβ
  have h3 := mul_le_mul_of_nonneg_left hsq hβ
  constructor <;> nlinarith

/-- The weight `u^h v^{h'}` is nonnegative on the cube. No thesis counterpart. -/
theorem NormalCrossing.monomialWeight_nonneg {m m' : ℕ} (h : Fin m → ℝ) (h' : Fin m' → ℝ)
    {z : (Fin m → ℝ) × (Fin m' → ℝ)} (hu : ∀ j, 0 ≤ z.1 j) (hv : ∀ j, 0 ≤ z.2 j) :
    0 ≤ NormalCrossing.monomialWeight h h' z :=
  mul_nonneg (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hu j) _)
    (Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hv j) _)

/-- The integrand of `Z^p(n, ξ, φ)` is integrable on the (open) cube when `ξ` and `φ` are
measurable and bounded there: the weight is integrable and the remaining factor is bounded.
No thesis counterpart. -/
theorem NormalCrossing.integrable_blockIntegral_integrand {m m' : ℕ} (k : Fin m → ℕ) {h : Fin m → ℝ}
    (k' : Fin m' → ℕ)
    {h' : Fin m' → ℝ} {b β p n : ℝ} {ξ f : (Fin m → ℝ) × (Fin m' → ℝ) → ℝ} {Mξ Mf : ℝ}
    (hh : ∀ j, -1 < h j) (hh' : ∀ j, -1 < h' j) (hb : 0 < b) (hβ : 0 ≤ β) (hp : 0 ≤ p)
    (hn : 0 ≤ n) (hξm : Measurable ξ) (hfm : Measurable f)
    (hξ : ∀ z ∈ cube m b ×ˢ cube m' b, |ξ z| ≤ Mξ)
    (hf : ∀ z ∈ cube m b ×ˢ cube m' b, |f z| ≤ Mf) :
    Integrable (fun z ↦ potential k k' z ^ p *
        Real.exp (-(n * β * potential k k' z) +
          Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
        NormalCrossing.monomialWeight h h' z * f z)
      ((volume.restrict (ocube m b)).prod (volume.restrict (ocube m' b))) := by
  have hw : Integrable (NormalCrossing.monomialWeight h h')
      ((volume.restrict (ocube m b)).prod (volume.restrict (ocube m' b))) := by
    rw [restrict_ocube_eq, restrict_ocube_eq]
    exact (integrableOn_cube_rpow hh hb).mul_prod (integrableOn_cube_rpow hh' hb)
  have hKm := measurable_potential k k'
  have hmeas : Measurable fun z ↦ potential k k' z ^ p *
      Real.exp (-(n * β * potential k k' z) +
        Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) * f z :=
    ((hKm.pow_const p).mul (Real.measurable_exp.comp
      (((hKm.const_mul _).neg).add
        ((hKm.sqrt.const_mul _).mul hξm)))).mul hfm
  refine (hw.bdd_mul (c := (b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j)) ^ p *
    Real.exp (β * Mξ ^ 2 / 2) * Mf) hmeas.aestronglyMeasurable ?_).congr
    (Filter.Eventually.of_forall fun z ↦ by ring)
  filter_upwards [ae_prod_ocube (m := m) (m' := m') b] with z hz
  have hu : ∀ j, z.1 j ∈ Icc 0 b := fun j ↦ Ioo_subset_Icc_self (hz.1 j)
  have hv : ∀ j, z.2 j ∈ Icc 0 b := fun j ↦ Ioo_subset_Icc_self (hz.2 j)
  have hzS : z ∈ cube m b ×ˢ cube m' b := ⟨mem_cube.2 hu, mem_cube.2 hv⟩
  have hK0 : 0 ≤ potential k k' z :=
    potential_nonneg k k' (fun j ↦ (hu j).1) fun j ↦ (hv j).1
  have hE := (NormalCrossing.exponent_bounds hK0 hn hβ (hξ z hzS)).2
  have hKp : potential k k' z ^ p ≤ (b ^ (2 * ∑ j, k j) * b ^ (2 * ∑ j, k' j)) ^ p :=
    Real.rpow_le_rpow hK0 (potential_le k k' hb hu hv) hp
  have hexp : Real.exp (-(n * β * potential k k' z) +
      Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) ≤ Real.exp (β * Mξ ^ 2 / 2) :=
    Real.exp_le_exp.mpr (hE.trans (by nlinarith [mul_nonneg hn hK0]))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hK0 _)
    (Real.exp_pos _).le)]
  exact mul_le_mul (mul_le_mul hKp hexp (Real.exp_pos _).le (by positivity)) (hf z hzS)
    (abs_nonneg _) (by positivity)

/-- [Hit26, Theorem 5.1.1] ([Wat09, Theorem 4.8]). Stated with explicit
bounds `|ξ| ≤ Mξ` and `0 ≤ mf ≤ φ ≤ Mf` on the cube in place of [Hit26]'s `‖ξ‖`, `inf φ`
and `‖φ‖` (take `Mξ = ‖ξ‖`, `mf = inf φ`, `Mf = ‖φ‖` to recover it); measurability replaces
[Hit26]'s `C¹`, which the proof never uses. Two corrections to [Hit26]: `φ ≥ 0` is
needed (the two-sided bound fails for signed `φ`), and the range is `n ≥ 2`, not `n > 1`. The
constants depend only on the exponent
data, `b`, `β` and `p`. The test function is bound as `f`, since `φ` is `Nat.totient` under
`open Nat`. -/
theorem NormalCrossing.blockIntegral_bounds {r m' : ℕ} {k : Fin (r + 1) → ℕ} {h : Fin (r + 1) → ℝ}
    {k' : Fin m' → ℕ}
    {h' : Fin m' → ℝ} {lam b β p : ℝ}
    (hk : ∀ j, 0 < k j) (hlam : ∀ j, (h j + 1) / (2 * k j) = lam)
    (hlam0 : 0 < lam) (hsec : ∀ j, 2 * k' j * lam < h' j + 1) (hb : 0 < b) (hβ : 0 < β)
    (hp : 0 ≤ p) :
    ∃ a₁ > 0, ∃ a₂ > 0, ∀ (ξ f : (Fin (r + 1) → ℝ) × (Fin m' → ℝ) → ℝ) (Mξ mf Mf : ℝ),
      Measurable ξ → Measurable f → 0 ≤ mf →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |ξ z| ≤ Mξ) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, mf ≤ f z) →
      (∀ z ∈ cube (r + 1) b ×ˢ cube m' b, f z ≤ Mf) →
      ∀ n : ℝ, 2 ≤ n →
        a₁ * Real.log n ^ r / n ^ (lam + p) * Real.exp (-(β * Mξ ^ 2 / 2)) * mf
            ≤ NormalCrossing.blockIntegral k h k' h' b β p n ξ f ∧
        NormalCrossing.blockIntegral k h k' h' b β p n ξ f
            ≤ a₂ * Real.log n ^ r / n ^ (lam + p) * Real.exp (β * Mξ ^ 2 / 2) * Mf := by
  obtain ⟨hh, hh', -, -⟩ := NormalCrossing.exponents_aux hk hlam hlam0 hsec hp
  obtain ⟨a₁, ha₁, hZ₁⟩ :=
    blockIntegral₀_lower_bound hk hlam hlam0 hsec hb (by positivity : 0 < 3 * β / 2) hp
  obtain ⟨a₂, ha₂, hZ₂⟩ := blockIntegral₀_upper_bound hk hlam hlam0 hsec hb
      (by positivity : 0 < β / 2) hp
  refine ⟨a₁, ha₁, a₂, ha₂, fun ξ f Mξ mf Mf hξm hfm hmf hξ hfl hfu n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hS : MeasurableSet (cube (r + 1) b ×ˢ cube m' b) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hfabs : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b, |f z| ≤ Mf := fun z hz ↦ by
    rw [abs_of_nonneg (hmf.trans (hfl z hz))]; exact hfu z hz
  -- integrability of the three integrands on the closed product cube
  have hint : IntegrableOn (fun z ↦ potential k k' z ^ p *
      Real.exp (-(n * β * potential k k' z) +
        Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
      NormalCrossing.monomialWeight h h' z * f z) (cube (r + 1) b ×ˢ cube m' b) := by
    have := integrable_blockIntegral_integrand k k' hh hh' hb hβ.le hp hn0 hξm hfm hξ hfabs
    rwa [restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict] at this
  have hintZ : ∀ β' : ℝ, 0 ≤ β' → IntegrableOn (fun z ↦ potential k k' z ^ p *
      Real.exp (-(n * β' * potential k k' z)) * NormalCrossing.monomialWeight h h' z)
      (cube (r + 1) b ×ˢ cube m' b) := fun β' hβ' ↦ by
    have := integrable_blockIntegral₀_integrand k k' hh hh' hb hβ' hp hn0
    rwa [restrict_ocube_eq, restrict_ocube_eq, Measure.prod_restrict] at this
  -- the pointwise sandwich
  have hpt : ∀ z ∈ cube (r + 1) b ×ˢ cube m' b,
      potential k k' z ^ p * Real.exp (-(n * (3 * β / 2) * potential k k' z)) *
          NormalCrossing.monomialWeight h h' z * (Real.exp (-(β * Mξ ^ 2 / 2)) * mf)
        ≤ potential k k' z ^ p *
            Real.exp (-(n * β * potential k k' z) +
              Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
            NormalCrossing.monomialWeight h h' z * f z ∧
      potential k k' z ^ p *
            Real.exp (-(n * β * potential k k' z) +
              Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
            NormalCrossing.monomialWeight h h' z * f z
        ≤ potential k k' z ^ p * Real.exp (-(n * (β / 2) * potential k k' z)) *
            NormalCrossing.monomialWeight h h' z * (Real.exp (β * Mξ ^ 2 / 2) * Mf) := by
    intro z hz
    have hu : ∀ j, 0 ≤ z.1 j := fun j ↦ hz.1.1 j
    have hv : ∀ j, 0 ≤ z.2 j := fun j ↦ hz.2.1 j
    have hK0 := potential_nonneg k k' hu hv
    have hA : 0 ≤ potential k k' z ^ p * NormalCrossing.monomialWeight h h' z :=
      mul_nonneg (Real.rpow_nonneg hK0 _) (monomialWeight_nonneg h h' hu hv)
    obtain ⟨hE₁, hE₂⟩ := NormalCrossing.exponent_bounds hK0 hn0 hβ.le (hξ z hz)
    have hf0 : 0 ≤ f z := hmf.trans (hfl z hz)
    constructor
    · calc potential k k' z ^ p * Real.exp (-(n * (3 * β / 2) * potential k k' z)) *
            NormalCrossing.monomialWeight h h' z * (Real.exp (-(β * Mξ ^ 2 / 2)) * mf)
          = (potential k k' z ^ p * NormalCrossing.monomialWeight h h' z) *
            (Real.exp (-(n * (3 * β / 2) * potential k k' z) + -(β * Mξ ^ 2 / 2)) * mf) := by
            rw [Real.exp_add]; ring
        _ ≤ (potential k k' z ^ p * NormalCrossing.monomialWeight h h' z) *
            (Real.exp (-(n * β * potential k k' z) +
              Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) * f z) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (Real.exp_le_exp.mpr hE₁) (hfl z hz) hmf (Real.exp_pos _).le) hA
        _ = _ := by ring
    · calc potential k k' z ^ p *
            Real.exp (-(n * β * potential k k' z) +
              Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) *
            NormalCrossing.monomialWeight h h' z * f z
          = (potential k k' z ^ p * NormalCrossing.monomialWeight h h' z) *
            (Real.exp (-(n * β * potential k k' z) +
              Real.sqrt n * β * Real.sqrt (potential k k' z) * ξ z) * f z) := by ring
        _ ≤ (potential k k' z ^ p * NormalCrossing.monomialWeight h h' z) *
            (Real.exp (-(n * (β / 2) * potential k k' z) + β * Mξ ^ 2 / 2) * Mf) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul (Real.exp_le_exp.mpr hE₂) (hfu z hz) hf0 (Real.exp_pos _).le) hA
        _ = _ := by rw [Real.exp_add]; ring
  -- integrate the sandwich
  have hlow : NormalCrossing.blockIntegral₀ k h k' h' b (3 * β / 2) p n *
      (Real.exp (-(β * Mξ ^ 2 / 2)) * mf)
      ≤ NormalCrossing.blockIntegral k h k' h' b β p n ξ f := by
    rw [NormalCrossing.blockIntegral₀, NormalCrossing.blockIntegral, ← integral_mul_const]
    exact setIntegral_mono_on ((hintZ _ (by positivity)).mul_const _) hint hS
      fun z hz ↦ (hpt z hz).1
  have hupp : NormalCrossing.blockIntegral k h k' h' b β p n ξ f
      ≤ NormalCrossing.blockIntegral₀ k h k' h' b (β / 2) p n * (Real.exp (β * Mξ ^ 2 / 2) * Mf) :=
          by
    rw [NormalCrossing.blockIntegral₀, NormalCrossing.blockIntegral, ← integral_mul_const]
    exact setIntegral_mono_on hint ((hintZ _ (by positivity)).mul_const _) hS
      fun z hz ↦ (hpt z hz).2
  have hc₁ : 0 ≤ Real.exp (-(β * Mξ ^ 2 / 2)) * mf := by positivity
  have hc₂ : 0 ≤ Real.exp (β * Mξ ^ 2 / 2) * Mf := by
    have h0 : ((0 : Fin (r + 1) → ℝ), (0 : Fin m' → ℝ)) ∈ cube (r + 1) b ×ˢ cube m' b :=
      ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, ⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩⟩
    exact mul_nonneg (Real.exp_pos _).le ((hmf.trans (hfl _ h0)).trans (hfu _ h0))
  constructor
  · calc a₁ * Real.log n ^ r / n ^ (lam + p) * Real.exp (-(β * Mξ ^ 2 / 2)) * mf
        = a₁ * Real.log n ^ r / n ^ (lam + p) * (Real.exp (-(β * Mξ ^ 2 / 2)) * mf) := by ring
      _ ≤ NormalCrossing.blockIntegral₀ k h k' h' b (3 * β / 2) p n *
          (Real.exp (-(β * Mξ ^ 2 / 2)) * mf) :=
          mul_le_mul_of_nonneg_right (hZ₁ n (by linarith)) hc₁
      _ ≤ _ := hlow
  · calc NormalCrossing.blockIntegral k h k' h' b β p n ξ f
        ≤ NormalCrossing.blockIntegral₀ k h k' h' b (β / 2) p n *
            (Real.exp (β * Mξ ^ 2 / 2) * Mf) := hupp
      _ ≤ a₂ * Real.log n ^ r / n ^ (lam + p) * (Real.exp (β * Mξ ^ 2 / 2) * Mf) :=
          mul_le_mul_of_nonneg_right (hZ₂ n hn) hc₂
      _ = _ := by ring

end SingularLearningTheory
