/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import SLT.FreeEnergy.FrozenKernel
public import SLT.StandardForm.FundamentalConditionI
public import SLT.SingularIntegrals.SingularityType
public import SLT.Setting.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.TangentCone.Pi
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Presheaf
import SLT.FreeEnergy.QuantitativeApprox
import SLT.SingularIntegrals.Density.FromResolution
import SLT.SingularIntegrals.Resolution
import SLT.SingularIntegrals.TypeOfAtlas
import SLT.SingularIntegrals.Volume.Atlas
import SLT.SingularIntegrals.Volume.Consequences
public import SLT.SingularIntegrals.Defs

/-!
# The singular-integrals chapter: proofs

The theorems of `SLTChallenge/SingularIntegrals.lean`, proved from the library: the
normal-crossing bounds of `SingularIntegrals/NormalCrossing.lean` and
`FreeEnergy/FrozenKernel.lean` in the single-coordinate formulation (the exponent data
`k, h : Fin d → ℕ` with the threshold, primary set and multiplicity derived from them; the
integrals over the subtype `[0, b]^d` are transported to set integrals and the coordinates
permuted into the library's block form), and [Wat09, Theorem 7.1] from the exact sublevel volume
(`SingularIntegrals/Volume/`) and the state-density asymptotic (`SingularIntegrals/Density/`).

The definitions are in `SLT/SingularIntegrals/Defs.lean`.
-/

@[expose] public section

-- These statements mirror SLTChallenge word for word, so they keep hypotheses of the book
-- that the delegated proofs here don't need.
set_option linter.unusedVariables false

namespace SingularLearningTheory

open MeasureTheory (IntegrableOn volume)
open Set (Icc Ioi)
open Real (exp log)

variable {d : ℕ}

open MeasureTheory Set Filter Topology

section SingularityType

/-- The volume scaling determines the singularity type `(λ, m)`. With
`zetaFunction_meromorphic_continuation` and `zetaFunction_continuation_unique`, any `(λ, m)`
satisfying `IsSingularityType` is therefore the largest pole of the zeta function and its
order.

Relation to the source.
* **Gap.** [Wat09, Theorem 2.4], that the real log canonical threshold does not depend on the
  resolution, is for an analytic function on a compact set with Lebesgue measure; here the pair is a
  loss $K$ and a prior $\varphi$ on $W$, the setting of [Wat09, Chapter 6]. With
  `SLTResolution.isSingularityType`, the uniqueness gives the independence from the resolution in
  that setting. -/
theorem singularity_type_unique {d : ℕ} (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (lam lam' : ℝ) (m m' : ℕ) (h : IsSingularityType K φ W lam m)
    (h' : IsSingularityType K φ W lam' m') : lam = lam' ∧ m = m' :=
  SingularLearningTheory.IsSingularityType.unique h h'

end SingularityType

/-! ## [Wat09, Theorem 7.1]

The hypotheses give the exact volume asymptotic `V(t) ~ C t^λ (−log t)^(m−1)` through a
resolution (`singularityType_exact_sublevelVolume`); parts (1), (2) and (4) follow from it by the
Laplace representation of `laplaceIntegral` and direct limits (`sublevelVolume_limit_consequences`).
Part (3) uses resolution-chart slices, continuity and a monotone-density argument
(`singularityType_stateDensity`). -/

/-- The exact volume asymptotic and its consequences, shared by the proofs of [Wat09, Theorem 7.1].
-/
private theorem exactVolume_consequences
    (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hKg : ∀ w ∈ W, K w = 0 → ¬ (K =ᶠ[𝓝 w] 0))
    (hφg : ∀ w ∈ W, K w = 0 → ¬ (φ =ᶠ[𝓝 w] 0))
    (hvol : ∀ ε > 0, 0 < ∫⁻ w in W ∩ {w | K w < ε}, ENNReal.ofReal (φ w))
    (lam : ℝ) (m : ℕ) (hm : 1 ≤ m) (htype : IsSingularityType K φ W lam m) :
    ∃ C : ℝ, 0 < C ∧
      (∀ β > 0, Tendsto (fun n : ℝ ↦ n ^ lam / log n ^ (m - 1) * laplaceIntegral K φ W β n)
        atTop (𝓝 (C * Real.Gamma (lam + 1) / β ^ lam))) ∧
      Tendsto (fun n : ℝ ↦ -log (laplaceIntegral K φ W 1 n) / log n) atTop (𝓝 lam) ∧
      (∀ a : ℝ, 0 < a → a ≠ 1 → Tendsto
        (fun t ↦ log (SingularLearningTheory.sublevelVolume K φ W (a * t) /
          SingularLearningTheory.sublevelVolume K φ W t) / log a)
        (𝓝[>] 0) (𝓝 lam)) := by
  have hφ : ∀ w ∈ W, 0 ≤ φ w := fun w hw ↦ II.nonneg hw
  have hφi : IntegrableOn φ W := (II.continuousOn).integrableOn_compact hW
  obtain ⟨C, hC, hV⟩ := singularityType_exact_sublevelVolume K φ W hW hKa hK
    II hKg hφg hvol lam m htype
  exact ⟨C, hC, sublevelVolume_limit_consequences hW hKa.continuousOn hK hφ hφi hm hC hV⟩

/-- **Asymptotics of the partition function.** For every `β > 0`, the normalised partition function
has the exact asymptotic `Z₀(n) ~ c₁ (log n)^(m−1) / n^λ`, with a constant depending on `β`.

Relation to the source.
* **Correction.** The book prints the normalisation inverted, $(\log n)^{m-1}/n^\lambda$, where
  $n^\lambda/(\log n)^{m-1}$ must multiply the integral.
* **Strengthening.** Every inverse temperature $\beta > 0$ is allowed, where the book has
  $\beta = 1$.

Source statement: [Wat09, Theorem 7.1(1)] -/
theorem tendsto_rpow_div_log_pow_mul_laplaceIntegral {d : ℕ}
    (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions K φ W)
    (lam : ℝ) (m : ℕ) (hlam : 0 < lam) (hm : 1 ≤ m)
    (htype : IsSingularityType K φ W lam m) :
    ∀ β > 0, ∃ c₁ : ℝ, 0 < c₁ ∧
      Tendsto (fun n : ℝ ↦ n ^ lam / log n ^ (m - 1) * laplaceIntegral K φ W β n) atTop (𝓝 c₁) := by
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  obtain ⟨C, hC, hZ, -, -⟩ :=
    exactVolume_consequences K φ W hW hKa hK II hKg hφg hvol lam m hm htype
  exact fun β hβ ↦ ⟨_, div_pos (mul_pos hC (Real.Gamma_pos_of_pos (by linarith)))
    (by positivity), hZ β hβ⟩

/-- **The learning coefficient from the partition function.** `λ = −lim log Z₀(n) / log n`, at `β =
1` as in the book.

Source statement: [Wat09, Theorem 7.1(2)] -/
-- `hlam` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
theorem tendsto_neg_log_laplaceIntegral_div_log {d : ℕ}
    (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions K φ W)
    (lam : ℝ) (m : ℕ) (hlam : 0 < lam) (hm : 1 ≤ m)
    (htype : IsSingularityType K φ W lam m) :
    Tendsto (fun n : ℝ ↦ -log (laplaceIntegral K φ W 1 n) / log n) atTop (𝓝 lam) :=
  (exactVolume_consequences K φ W hW hKa hK II hZ.loss_germ hZ.prior_germ hZ.sublevel_mass lam m hm
    htype).choose_spec.2.2.1

/-- **Asymptotics of the state density.** The state density has the exact asymptotic `v(t) ~ c₂
t^(λ−1) (−log t)^(m−1)` as `t → 0⁺`. Here `v` is `stateDensity`, the derivative of the volume, so
the statement also asserts that `V` is differentiable on some interval `(0, ε)`.

Source statement: [Wat09, Theorem 7.1(3)] -/
-- `hlam` and `hm` are unused: they follow from the other hypotheses.
@[nolint unusedArguments]
theorem tendsto_stateDensity_div_rpow_mul_neg_log_pow {d : ℕ}
    (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions K φ W)
    (lam : ℝ) (m : ℕ) (hlam : 0 < lam) (hm : 1 ≤ m)
    (htype : IsSingularityType K φ W lam m) :
    ∃ c₂ : ℝ, 0 < c₂ ∧
      (∀ᶠ t in 𝓝[>] 0, DifferentiableAt ℝ (SingularLearningTheory.sublevelVolume K φ W) t) ∧
      Tendsto (fun t ↦ stateDensity K φ W t / (t ^ (lam - 1) * (-log t) ^ (m - 1)))
        (𝓝[>] 0) (𝓝 c₂) := by
  obtain ⟨hKg, hφg, hvol⟩ := hZ
  exact singularityType_stateDensity K φ W hW hKa hK
    II hKg hφg hvol lam m
    htype

/-- **The learning coefficient from the volume function.** `λ = lim log(V(at) / V(t)) / log a` as `t
→ 0⁺`, for every `a > 0` with `a ≠ 1`. The book's volume uses `K < t`; `sublevelVolume` uses `K ≤
t`.

Source statement: [Wat09, Theorem 7.1(4)] -/
-- `hlam` is unused here: the challenge's statement keeps the book's hypotheses.
@[nolint unusedArguments]
theorem tendsto_log_sublevelVolume_ratio_div_log {d : ℕ}
    (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions K φ W)
    (lam : ℝ) (m : ℕ) (hlam : 0 < lam) (hm : 1 ≤ m)
    (htype : IsSingularityType K φ W lam m) :
    ∀ a : ℝ, 0 < a → a ≠ 1 → Tendsto
      (fun t ↦ log (SingularLearningTheory.sublevelVolume K φ W (a * t) /
        SingularLearningTheory.sublevelVolume K φ W t) / log a)
      (𝓝[>] 0) (𝓝 lam) :=
  (exactVolume_consequences K φ W hW hKa hK II hZ.loss_germ hZ.prior_germ hZ.sublevel_mass lam m hm
    htype).choose_spec.2.2.2

/-! ## Normal crossing integrals: bridges to the library

The library (`FreeEnergy/FrozenKernel.lean`) works with a bare exponent vector `(k, h)` on `ℝ^d`
through `activeIdx`, `expThreshold`, `expPrimary`, `expMult`, and with the block form
`normalCrossingIntegral₀ k h k' h'` after a permutation of the coordinates. The challenge's
definitions are the same objects with `h` a natural vector and the integrals over the subtype
`[0, b]^d`. -/

section NormalCrossingBridges

variable {k h : Fin d → ℕ}

/-- The active coordinates are nonempty. -/
private theorem activeIdx_nonempty (hk : ∃ j, 0 < k j) : (activeIdx k).Nonempty := by
  obtain ⟨j, hj⟩ := hk
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩

/-- The challenge's threshold is the library's. -/
private theorem monomialRlct_eq (hk : ∃ j, 0 < k j) :
    monomialRlct k h hk = expThreshold k (fun j ↦ (h j : ℝ)) (activeIdx_nonempty hk) := rfl

/-- The challenge's primary set is the library's. -/
private theorem criticalCoords_eq (hk : ∃ j, 0 < k j) :
    criticalCoords k h hk = expPrimary k (fun j ↦ (h j : ℝ)) (activeIdx_nonempty hk) := by
  ext j
  rw [criticalCoords, expPrimary, activeIdx, Finset.mem_filter, Finset.mem_filter,
    Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, expRatio, monomialRlct_eq]

/-- The challenge's multiplicity is the library's. -/
private theorem monomialMultiplicity_eq (hk : ∃ j, 0 < k j) :
    monomialMultiplicity k h hk = expMult k (fun j ↦ (h j : ℝ)) (activeIdx_nonempty hk) := by
  rw [monomialMultiplicity, criticalCoords_eq]
  rfl

private theorem measurableSet_cube (b : ℝ) : MeasurableSet (cube d b) := measurableSet_Icc

/-- `Z^p(n)` on the subtype is the library's cube integral. -/
private theorem normalCrossingIntegral₀_eq_integral_cube (b β p n : ℝ) :
    normalCrossingIntegral₀ k h b β p n
      = ∫ u in cube d b, cubeIntegrand k (fun j ↦ (h j : ℝ)) β p n u := by
  simp only
      [normalCrossingIntegral₀, normalCrossingIntegral, ContinuousMap.zero_apply,
      ContinuousMap.one_apply, mul_zero, add_zero,
    mul_one]
  rw [integral_subtype_comap (measurableSet_cube b) (f := fun u ↦
    normalCrossing k u ^ p * exp (-(n * β * normalCrossing k u)) * monomialWeight h u)]
  rfl

end NormalCrossingBridges

/-! ## [Wat09, Theorem 4.7] -/

/-- **Bounds on the monomial partition function**, for real `n ≥ 2`: the exponents `k, h` determine
`λ`, the critical coordinates and their number `m` (the book's `r`).

Relation to the source.
* **Strengthening.** The exponents determine the critical coordinates, instead of the book's split
  into $r$ critical and $s$ other coordinates, and coordinates with $k_j = 0$ are allowed.
* **Formalisation note.** $n$ is real with $n \ge 2$, where the book takes natural $n > 1$; for real
  $n$ near $1$ the upper bound fails when $m \ge 2$.

Source statement: [Wat09, Theorem 4.7] -/
theorem normalCrossingIntegral₀_bounds {d : ℕ} (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j) (b β p : ℝ)
    (hb : 0 < b) (hβ : 0 < β) (hp : 0 ≤ p) :
    let lam := monomialRlct k h hk
    let m := monomialMultiplicity k h hk
    let Zp := normalCrossingIntegral₀ k h b β p
    ∃ a₁ > 0, ∃ a₂ > 0, ∀ (n : ℝ) (hn : 2 ≤ n),
      a₁ * log n ^ (m - 1) / n ^ (lam + p) ≤ Zp n ∧
        Zp n ≤ a₂ * log n ^ (m - 1) / n ^ (lam + p) := by
  intro lam m Zp
  have hh : ∀ j, -1 < ((fun j ↦ (h j : ℝ)) j) := fun j ↦
    neg_one_lt_zero.trans_le (Nat.cast_nonneg _)
  obtain ⟨a₁, ha₁, a₂, ha₂, H⟩ :=
    integral_cube_bounds_general k (fun j ↦ (h j : ℝ)) (activeIdx_nonempty hk) hh hb hβ hp
  refine ⟨a₁, ha₁, a₂, ha₂, fun n hn ↦ ?_⟩
  simp only
      [Zp, lam, m, normalCrossingIntegral₀_eq_integral_cube, monomialRlct_eq,
      monomialMultiplicity_eq]
  exact H n hn


/-! ## [Wat09, Theorem 4.8]

The bridges: the integrand of `Z^p(n, ξ, φ)` on the ambient space, for `ξ, φ` extended by `0`
off the cube, and `Z^p(n)` as a set integral. -/

section GB48

variable {k h : Fin d → ℕ} {b : ℝ}

open Classical in
/-- A continuous function on the cube, extended by `0`. -/
private noncomputable def ext (ξ : C(cube d b, ℝ)) (x : Fin d → ℝ) : ℝ :=
  if hx : x ∈ cube d b then ξ ⟨x, hx⟩ else 0

private theorem ext_coe (ξ : C(cube d b, ℝ)) (x : cube d b) : ext ξ x = ξ x := by
  simp [ext, x.2]

private theorem continuousOn_ext (ξ : C(cube d b, ℝ)) : ContinuousOn (ext ξ) (cube d b) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have : (cube d b).domRestrict (ext ξ) = ξ := funext fun x ↦ ext_coe ξ x
  rw [this]
  exact ξ.continuous

private theorem abs_ext_le (ξ : C(cube d b, ℝ)) {x : Fin d → ℝ} (hx : x ∈ cube d b) :
    |ext ξ x| ≤ ‖ξ‖ := by
  have := ContinuousMap.norm_coe_le_norm ξ ⟨x, hx⟩
  rw [Real.norm_eq_abs] at this
  simpa [ext, hx] using this

/-- The integrand of `Z^p(n, ξ, φ)` on the ambient space. -/
private noncomputable def zIntegrand (k h : Fin d → ℕ) (β p n : ℝ) (ξ φ : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) : ℝ :=
  normalCrossing k x ^ p *
    exp (-(n * β * normalCrossing k x) + √n * β * √(normalCrossing k x) * ξ x) *
    monomialWeight h x * φ x

/-- The integrand of `Z^p(n)` on the ambient space. -/
private noncomputable def zIntegrand₀ (k h : Fin d → ℕ) (β p n : ℝ) (x : Fin d → ℝ) : ℝ :=
  normalCrossing k x ^ p * exp (-(n * β * normalCrossing k x)) * monomialWeight h x

private theorem normalCrossingIntegral_eq_setIntegral (β p n : ℝ) (ξ φ : C(cube d b, ℝ)) :
    normalCrossingIntegral k h b β p n ξ φ = ∫ x in cube d b, zIntegrand k h β p n (ext ξ) (ext φ)
        x := by
  simp only [normalCrossingIntegral]
  rw [← integral_subtype_comap (measurableSet_cube b)
    (f := zIntegrand k h β p n (ext ξ) (ext φ))]
  congr 1
  funext x
  simp only [zIntegrand, ext_coe]

private theorem normalCrossingIntegral₀_eq_setIntegral (β p n : ℝ) :
    normalCrossingIntegral₀ k h b β p n = ∫ x in cube d b, zIntegrand₀ k h β p n x := by
  rw [normalCrossingIntegral₀_eq_integral_cube]
  rfl

private theorem continuous_normalCrossing : Continuous (normalCrossing k) :=
  continuous_finsetProd _ fun j _ ↦ (continuous_apply j).pow _

private theorem continuous_monomialWeight : Continuous (monomialWeight h) :=
  continuous_finsetProd _ fun j _ ↦
    (continuous_apply j).rpow_const fun _ ↦ Or.inr (Nat.cast_nonneg _)

private theorem continuousOn_zIntegrand {β p n : ℝ} (hp : 0 ≤ p) {ξ φ : (Fin d → ℝ) → ℝ}
    (hξ : ContinuousOn ξ (cube d b)) (hφ : ContinuousOn φ (cube d b)) :
    ContinuousOn (zIntegrand k h β p n ξ φ) (cube d b) := by
  have hK := (continuous_normalCrossing (k := k)).continuousOn (s := cube d b)
  refine (((hK.rpow_const fun _ _ ↦ Or.inr hp).mul ?_).mul
    continuous_monomialWeight.continuousOn).mul hφ
  exact ((continuousOn_const.mul hK).neg.add ((continuousOn_const.mul hK.sqrt).mul hξ)).rexp

private theorem continuous_zIntegrand₀ {β p n : ℝ} (hp : 0 ≤ p) :
    Continuous (zIntegrand₀ k h β p n) := by
  have hK := continuous_normalCrossing (k := k)
  exact ((hK.rpow_const fun _ ↦ Or.inr hp).mul (continuous_const.mul hK).neg.rexp).mul
    continuous_monomialWeight

private theorem normalCrossing_nonneg' {x : Fin d → ℝ} (hx : x ∈ cube d b) :
    0 ≤ normalCrossing k x :=
  Finset.prod_nonneg fun j _ ↦ pow_nonneg (hx.1 j) _

private theorem monomialWeight_nonneg' {x : Fin d → ℝ} (hx : x ∈ cube d b) :
    0 ≤ monomialWeight h x :=
  Finset.prod_nonneg fun j _ ↦ Real.rpow_nonneg (hx.1 j) _

/-- The pointwise sandwich of the integrand, for `|ξ| ≤ M` and `0 ≤ φ`: the Cauchy–Schwarz step
in the proof of [Wat09, Theorem 4.8]. -/
private theorem zIntegrand_sandwich {β p n M : ℝ} (hβ : 0 < β) (hn : 0 ≤ n)
    {ξ φ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hx : x ∈ cube d b) (hξ : |ξ x| ≤ M)
    {c C : ℝ} (hc : 0 ≤ c) (hφc : c ≤ φ x) (hφC : φ x ≤ C) :
    zIntegrand₀ k h (3 * β / 2) p n x * (exp (-(β * M ^ 2 / 2)) * c)
        ≤ zIntegrand k h β p n ξ φ x ∧
      zIntegrand k h β p n ξ φ x ≤ zIntegrand₀ k h (β / 2) p n x * (exp (β * M ^ 2 / 2) * C) := by
  have hK0 := normalCrossing_nonneg' (k := k) hx
  have hA : 0 ≤ normalCrossing k x ^ p * monomialWeight h x :=
    mul_nonneg (Real.rpow_nonneg hK0 _) (monomialWeight_nonneg' hx)
  obtain ⟨hE₁, hE₂⟩ := NormalCrossing.exponent_bounds hK0 hn hβ.le hξ
  have hφ0 : 0 ≤ φ x := hc.trans hφc
  constructor
  · calc zIntegrand₀ k h (3 * β / 2) p n x * (exp (-(β * M ^ 2 / 2)) * c)
        = (normalCrossing k x ^ p * monomialWeight h x) *
          (exp (-(n * (3 * β / 2) * normalCrossing k x) + -(β * M ^ 2 / 2)) * c) := by
          rw [Real.exp_add]; unfold zIntegrand₀; ring
      _ ≤ (normalCrossing k x ^ p * monomialWeight h x) *
          (exp (-(n * β * normalCrossing k x) + √n * β * √(normalCrossing k x) * ξ x) * φ x) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.exp_le_exp.mpr hE₁) hφc hc (Real.exp_pos _).le) hA
      _ = _ := by unfold zIntegrand; ring
  · calc zIntegrand k h β p n ξ φ x
        = (normalCrossing k x ^ p * monomialWeight h x) *
          (exp (-(n * β * normalCrossing k x) + √n * β * √(normalCrossing k x) * ξ x) * φ x) := by
          unfold zIntegrand; ring
      _ ≤ (normalCrossing k x ^ p * monomialWeight h x) *
          (exp (-(n * (β / 2) * normalCrossing k x) + β * M ^ 2 / 2) * C) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul (Real.exp_le_exp.mpr hE₂) hφC hφ0 (Real.exp_pos _).le) hA
      _ = _ := by rw [Real.exp_add]; unfold zIntegrand₀; ring

end GB48

/-- **Bounds on the monomial partition function with an external field.** For continuous `ξ` and
`φ ≥ 0` with `φ(0) > 0`, and real `n ≥ 2`; the lower constant `a₁` depends on `φ`.

Relation to the source.
* **Gap.** The book's lower bound is a constant independent of $\varphi$ times $\min \varphi$, which
  is $0$ when $\varphi$ vanishes on the boundary of the cube, as the partition-of-unity weights of
  the free energy formula do. Here $\varphi(0) > 0$ and the constant $a_1$ depends on $\varphi$, so
  neither bound implies the other.
* **Strengthening.** $\xi$ and $\varphi$ are continuous rather than $C^1$.

Source statement: [Wat09, Theorem 4.8] -/
theorem normalCrossingIntegral_bounds_of_nonneg {d : ℕ} (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j)
    (b β p : ℝ)
    (hb : 0 < b) (hβ : 0 < β) (hp : 0 ≤ p) :
    let lam := monomialRlct k h hk
    let m := monomialMultiplicity k h hk
    let Zp := normalCrossingIntegral k h b β p
    ∃ a₂ > 0,
    ∀ (φ : C(cube d b, ℝ)) (hφ : ∀ x, 0 ≤ φ x)
      -- `0` is a point of the cube since `0 ≤ b`
      (hφ0 : 0 < φ ⟨0, zero_mem_cube hb.le⟩),
    ∃ a₁ > 0,
    ∀ (ξ : C(cube d b, ℝ)) (n : ℝ) (hn : 2 ≤ n),
        a₁ * log n ^ (m - 1) / n ^ (lam + p) * exp (-(β * ‖ξ‖ ^ 2 / 2))
          ≤ Zp n ξ φ ∧
        Zp n ξ φ
          ≤ a₂ * log n ^ (m - 1) / n ^ (lam + p) * exp (β * ‖ξ‖ ^ 2 / 2) * ‖φ‖ := by
  intro lam m Zp
  have hcube : MeasurableSet (cube d b) := measurableSet_cube b
  -- the upper constant: Theorem 4.7 at inverse temperature `β/2`
  obtain ⟨_, -, a₂, ha₂, H₂⟩ := normalCrossingIntegral₀_bounds k h hk b (β / 2) p hb
      (by positivity) hp
  refine ⟨a₂, ha₂, fun φ hφ hφ0 ↦ ?_⟩
  set x₀ : cube d b := ⟨0, ⟨le_rfl, fun _ ↦ hb.le⟩⟩ with hx₀
  -- the subcube `[0, b']^d` on which `φ ≥ φ(0)/2`
  obtain ⟨δ, hδ, hφδ⟩ := Metric.continuousAt_iff.mp (φ.continuous.continuousAt (x := x₀))
    (φ x₀ / 2) (by positivity)
  set b' : ℝ := min b (δ / 2) with hb'_def
  have hb' : 0 < b' := lt_min hb (by positivity)
  have hb'b : b' ≤ b := min_le_left _ _
  have hsub : cube d b' ⊆ cube d b := Icc_subset_Icc le_rfl fun _ ↦ hb'b
  have hφ_half : ∀ x ∈ cube d b', φ x₀ / 2 ≤ ext φ x := by
    intro x hx
    have hxb : x ∈ cube d b := hsub hx
    have hdist : dist (⟨x, hxb⟩ : cube d b) x₀ < δ := by
      rw [Subtype.dist_eq, hx₀, dist_zero_right]
      refine (pi_norm_le_iff_of_nonneg hb'.le).mpr (fun j ↦ ?_) |>.trans_lt ?_
      · rw [Real.norm_eq_abs, abs_of_nonneg (hx.1 j)]
        exact hx.2 j
      · exact (min_le_right _ _).trans_lt (by linarith)
    have := hφδ hdist
    rw [Real.dist_eq, abs_lt] at this
    simp only [ext, hxb, dite_eq_left]
    linarith [this.1]
  -- the lower constant: Theorem 4.7 at inverse temperature `3β/2` on the subcube
  obtain ⟨a₁, ha₁, _, -, H₁⟩ :=
    normalCrossingIntegral₀_bounds k h hk b' (3 * β / 2) p hb' (by positivity) hp
  refine ⟨a₁ * (φ x₀ / 2), by positivity, fun ξ n hn ↦ ?_⟩
  have hn0 : (0 : ℝ) ≤ n := by linarith
  have hint : IntegrableOn (zIntegrand k h β p n (ext ξ) (ext φ)) (cube d b) :=
    (continuousOn_zIntegrand hp (continuousOn_ext ξ) (continuousOn_ext φ)).integrableOn_compact
      isCompact_Icc
  have hint₀ : ∀ β' b'', IntegrableOn (zIntegrand₀ k h β' p n) (cube d b'') := fun β' b'' ↦
    (continuous_zIntegrand₀ hp).continuousOn.integrableOn_compact isCompact_Icc
  have hφ_ext : ∀ x ∈ cube d b, 0 ≤ ext φ x ∧ ext φ x ≤ ‖φ‖ := fun x hx ↦
    ⟨by simpa [ext, hx] using hφ ⟨x, hx⟩, (le_abs_self _).trans (abs_ext_le φ hx)⟩
  have hsand := fun x (hx : x ∈ cube d b) ↦
    zIntegrand_sandwich (k := k) (h := h) (p := p) hβ hn0 hx (abs_ext_le ξ hx) (hφ_ext x hx).1 le_rfl
      (hφ_ext x hx).2
  simp only [Zp, normalCrossingIntegral_eq_setIntegral]
  constructor
  · -- restrict to the subcube, where `φ ≥ φ(0)/2`
    have hnonneg : ∀ x ∈ cube d b, 0 ≤ zIntegrand k h β p n (ext ξ) (ext φ) x := fun x hx ↦
      (mul_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg (normalCrossing_nonneg' hx) _)
        (Real.exp_pos _).le) (monomialWeight_nonneg' hx)) (hφ_ext x hx).1)
    have hstep₁ : ∫ x in cube d b', zIntegrand k h β p n (ext ξ) (ext φ) x
        ≤ ∫ x in cube d b, zIntegrand k h β p n (ext ξ) (ext φ) x :=
      setIntegral_mono_set hint ((ae_restrict_mem hcube).mono fun x hx ↦ hnonneg x hx)
        hsub.eventuallyLE
    have hstep₂ : ∫ x in cube d b', zIntegrand₀ k h (3 * β / 2) p n x *
          (exp (-(β * ‖ξ‖ ^ 2 / 2)) * (φ x₀ / 2))
        ≤ ∫ x in cube d b', zIntegrand k h β p n (ext ξ) (ext φ) x := by
      refine setIntegral_mono_on ((hint₀ _ _).mul_const _) (hint.mono_set hsub)
        (measurableSet_cube b') fun x hx ↦ ?_
      exact (zIntegrand_sandwich (p := p) hβ hn0 (hsub hx) (abs_ext_le ξ (hsub hx)) (by positivity)
        (hφ_half x hx) le_rfl).1
    rw [integral_mul_const, ← normalCrossingIntegral₀_eq_setIntegral] at hstep₂
    have := H₁ n hn
    calc a₁ * (φ x₀ / 2) * log n ^ (m - 1) / n ^ (lam + p) * exp (-(β * ‖ξ‖ ^ 2 / 2))
        = a₁ * log n ^ (m - 1) / n ^ (lam + p) * (exp (-(β * ‖ξ‖ ^ 2 / 2)) * (φ x₀ / 2)) := by
          ring
      _ ≤ normalCrossingIntegral₀ k h b' (3 * β / 2) p n *
          (exp (-(β * ‖ξ‖ ^ 2 / 2)) * (φ x₀ / 2)) :=
          mul_le_mul_of_nonneg_right this.1 (by positivity)
      _ ≤ _ := hstep₂.trans hstep₁
  · have hstep : ∫ x in cube d b, zIntegrand k h β p n (ext ξ) (ext φ) x
        ≤ ∫ x in cube d b, zIntegrand₀ k h (β / 2) p n x * (exp (β * ‖ξ‖ ^ 2 / 2) * ‖φ‖) :=
      setIntegral_mono_on hint ((hint₀ _ _).mul_const _) hcube fun x hx ↦ (hsand x hx).2
    rw [integral_mul_const, ← normalCrossingIntegral₀_eq_setIntegral] at hstep
    have := H₂ n hn
    calc _ ≤ _ := hstep
      _ ≤ a₂ * log n ^ (m - 1) / n ^ (lam + p) * (exp (β * ‖ξ‖ ^ 2 / 2) * ‖φ‖) :=
          mul_le_mul_of_nonneg_right this.2 (by positivity)
      _ = _ := by ring


/-! ## [Wat09, Theorem 4.9]: bridges

The primary coordinates `I = criticalCoords k h hk` are enumerated by `Fin (m)` and their complement
by `Fin (d − m)`; along the coordinate permutation `MeasurableEquiv.blockEquiv eP eS` the
challenge's integrals become
the library's block integrals (`FreeEnergy/QuantitativeApprox.lean`). -/

section GB49

variable {k h : Fin d → ℕ} {hk : ∃ j, 0 < k j} {b : ℝ}

/-- A primary coordinate is active. -/
private theorem k_pos_of_mem_primary {j : Fin d} (hj : j ∈ criticalCoords k h hk) : 0 < k j :=
  (Finset.mem_filter.mp hj).2.1

/-- A primary coordinate attains the threshold. -/
private theorem ratio_eq_of_mem_primary {j : Fin d} (hj : j ∈ criticalCoords k h hk) :
    ((h j : ℝ) + 1) / (2 * k j) = monomialRlct k h hk :=
  (Finset.mem_filter.mp hj).2.2

/-- A secondary coordinate has `2 k_j λ < h_j + 1` (vacuous when `k_j = 0`). -/
private theorem secondary_lt_of_notMem_primary {j : Fin d} (hj : j ∉ criticalCoords k h hk) :
    2 * (k j : ℝ) * monomialRlct k h hk < (h j : ℝ) + 1 := by
  by_cases hkj : 0 < k j
  · have hle : monomialRlct k h hk ≤ ((h j : ℝ) + 1) / (2 * k j) :=
      Finset.inf'_le _ (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hkj⟩)
    have hne : ((h j : ℝ) + 1) / (2 * k j) ≠ monomialRlct k h hk := fun heq ↦
      hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hkj, heq⟩)
    have hlt := lt_of_le_of_ne hle hne.symm
    have hk' : (0 : ℝ) < k j := by exact_mod_cast hkj
    rw [lt_div_iff₀ (by positivity)] at hlt
    linarith
  · have hk0 : k j = 0 := by omega
    simp only [hk0, Nat.cast_zero, mul_zero, zero_mul]
    positivity

private theorem monomialRlct_pos (hk : ∃ j, 0 < k j) : 0 < monomialRlct k h hk := by
  obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ.filter fun j ↦ 0 < k j)
    (by obtain ⟨j, hj⟩ := hk; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
    (fun j ↦ ((h j : ℝ) + 1) / (2 * k j))
  have hkj : (0 : ℝ) < k j := by exact_mod_cast (Finset.mem_filter.mp hj).2
  rw [monomialRlct, hjeq]
  positivity

/-- The extension by `0` of the restriction of `ξ` to the cube is measurable when `ξ` is
continuous on the cube. -/
private theorem measurable_ext {ξ : (Fin d → ℝ) → ℝ} (hξ : ContinuousOn ξ (cube d b)) :
    Measurable (ext (⟨fun x ↦ ξ x, hξ.domRestrict⟩ : C(cube d b, ℝ))) := by
  classical
  have : ext (⟨fun x ↦ ξ x, hξ.domRestrict⟩ : C(cube d b, ℝ)) = (cube d b).piecewise ξ 0 := by
    funext x
    by_cases hx : x ∈ cube d b
    · simp only [ext, dite_eq_left hx, Set.piecewise_eq_of_mem _ _ _ hx]
      rfl
    · simp [ext, hx]
  rw [this]
  exact ContinuousOn.measurable_piecewise hξ continuousOn_const (measurableSet_cube b)

/-- `ext ξ` on a point of the cube given by its coordinates. -/
private theorem ext_apply_of_mem {ξ : (Fin d → ℝ) → ℝ} (hξ : ContinuousOn ξ (cube d b))
    {x : Fin d → ℝ} (hx : x ∈ cube d b) :
    ext (⟨fun x ↦ ξ x, hξ.domRestrict⟩ : C(cube d b, ℝ)) x = ξ x := by
  simp only [ext, dite_eq_left hx]
  rfl

variable {r s : ℕ} (eP : Fin (r + 1) ≃ {j // j ∈ criticalCoords k h hk})
  (eS : Fin s ≃ {j // j ∉ criticalCoords k h hk})

/-- `MeasurableEquiv.blockEquiv` maps the block cube into the cube. -/
private theorem blockEquiv_mem_cube {z : (Fin (r + 1) → ℝ) × (Fin s → ℝ)}
    (hz : z ∈ cube (r + 1) b ×ˢ cube s b) :
    MeasurableEquiv.blockEquiv eP eS z ∈ cube d b := by
  rw [← MeasurableEquiv.blockEquiv_preimage_cube eP eS] at *
  exact hz

/-- The challenge's `Z^p(n, ξ, φ)` is the library's block `Z^p(n, ξ ∘ e, φ ∘ e)` along the
coordinate permutation `e = blockEquiv eP eS`. -/
private theorem normalCrossingIntegral_eq_block (β p n : ℝ) (ξ φ : C(cube d b, ℝ)) :
    normalCrossingIntegral k h b β p n ξ φ
      = SingularLearningTheory.NormalCrossing.blockIntegral (fun i ↦ k (eP i))
          (fun i ↦ (h (eP i) : ℝ))
          (fun i ↦ k (eS i))
          (fun i ↦ (h (eS i) : ℝ)) b β p n (ext ξ ∘ MeasurableEquiv.blockEquiv eP eS)
          (ext φ ∘ MeasurableEquiv.blockEquiv eP eS) := by
  rw [normalCrossingIntegral_eq_setIntegral, ← (MeasurableEquiv.blockEquiv_measurePreserving eP
      eS).setIntegral_preimage_emb
    (MeasurableEquiv.blockEquiv eP eS).measurableEmbedding,
        MeasurableEquiv.blockEquiv_preimage_cube,
            SingularLearningTheory.NormalCrossing.blockIntegral]
  refine setIntegral_congr_fun (measurableSet_Icc.prod
    measurableSet_Icc) fun z _ ↦ ?_
  simp only [zIntegrand, normalCrossing, monomialWeight,
      SingularLearningTheory.NormalCrossing.potential,
    SingularLearningTheory.NormalCrossing.monomialWeight, Function.comp]
  rw [MeasurableEquiv.prod_blockEquiv eP eS fun j x ↦ x ^ (2 * k j), MeasurableEquiv.prod_blockEquiv
      eP eS fun j x ↦ x ^ (h j : ℝ)]


/-! ### The secondary coordinates -/

/-- The underlying point of `toCriticalFace`, on the ambient secondary coordinates. -/
private noncomputable def toCriticalFaceFn (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j)
    (v : {j // j ∉ criticalCoords k h hk} → ℝ) : Fin d → ℝ :=
  fun j ↦ if hj : j ∈ criticalCoords k h hk then 0 else v ⟨j, hj⟩

private theorem toCriticalFace_val (hb : 0 ≤ b)
    (v : Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b)) :
    ((toCriticalFace k h hk hb v : cube d b) : Fin d → ℝ) = toCriticalFaceFn k h hk v := rfl

private theorem toCriticalFaceFn_mem (hb : 0 ≤ b)
    {v : {j // j ∉ criticalCoords k h hk} → ℝ}
    (hv : v ∈ Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b)) :
    toCriticalFaceFn k h hk v ∈ cube d b :=
  (toCriticalFace k h hk hb ⟨v, hv⟩).2

/-- The reindexing of the secondary coordinates by `eS`. -/
private noncomputable abbrev secEquiv (eS : Fin s ≃ {j // j ∉ criticalCoords k h hk}) :
    (Fin s → ℝ) ≃ᵐ ({j // j ∉ criticalCoords k h hk} → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) eS

private theorem secEquiv_apply (w : Fin s → ℝ) (i : Fin s) : secEquiv eS w (eS i) = w i :=
  MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ) eS w i

/-- `toCriticalFace` of the reindexed `w` is the block point `(0, w)`. -/
private theorem toCriticalFaceFn_secEquiv (w : Fin s → ℝ) :
    toCriticalFaceFn k h hk (secEquiv eS w) = MeasurableEquiv.blockEquiv eP eS (0, w) := by
  funext j
  obtain ⟨t, rfl⟩ := (Equiv.blockIndex eP eS).surjective j
  rcases t with i | i
  · have hj : (eP i : Fin d) ∈ criticalCoords k h hk := (eP i).2
    rw [Equiv.blockIndex_inl, MeasurableEquiv.blockEquiv_apply_inl]
    simp only [toCriticalFaceFn]
    rw [dite_eq_left hj]
    rfl
  · have hj : (eS i : Fin d) ∉ criticalCoords k h hk := (eS i).2
    rw [Equiv.blockIndex_inr, MeasurableEquiv.blockEquiv_apply_inr]
    simp only [toCriticalFaceFn]
    rw [dite_eq_right hj, Subtype.coe_eta]
    exact secEquiv_apply eS w i

private theorem secEquiv_preimage_Icc (b : ℝ) :
    secEquiv eS ⁻¹' Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b)
      = cube s b := by
  ext w
  simp only [mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply, cube]
  constructor
  · rintro ⟨h0, hb⟩
    refine ⟨fun i ↦ ?_, fun i ↦ ?_⟩ <;> rw [← secEquiv_apply eS w i]
    · exact h0 _
    · exact hb _
  · rintro ⟨h0, hb⟩
    refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩ <;> obtain ⟨i, rfl⟩ := eS.surjective j <;> rw [secEquiv_apply]
    · exact h0 i
    · exact hb i

/-- The secondary monomial along the reindexing is the library's `NormalCrossing.secondaryWeight`.
-/
private theorem prod_secEquiv (w : Fin s → ℝ) (lam : ℝ) :
    ∏ j : {j // j ∉ criticalCoords k h hk}, secEquiv eS w j ^ ((h j : ℝ) - 2 * k j * lam)
      = NormalCrossing.secondaryWeight (fun i ↦ k (eS i)) (fun i ↦ (h (eS i) : ℝ)) lam w := by
  rw [← Equiv.prod_comp eS fun j ↦ secEquiv eS w j ^ ((h j : ℝ) - 2 * k j * lam)]
  simp only [secEquiv_apply, NormalCrossing.secondaryWeight]

/-- The challenge's `γ_b` is the library's `gammaConst` of the primary block: the exponent
`|h| + m − 2|k|λ` vanishes on the primary coordinates. -/
private theorem gammaConst_eq_block (hm : monomialMultiplicity k h hk = r + 1) :
    gammaConst k h hk
      = SingularLearningTheory.NormalCrossing.gammaConst (fun i ↦ k (eP i)) (fun i ↦ (h
          (eP i) : ℝ))
          (monomialRlct k h hk) b := by
  have hexp : (∑ i, (h (eP i) : ℝ)) + ((r : ℝ) + 1) - 2 * (∑ i, (k (eP i) : ℝ)) *
      monomialRlct k h hk = 0 := by
    have : ∀ i, (h (eP i) : ℝ) + 1 - 2 * k (eP i) * monomialRlct k h hk = 0 := fun i ↦ by
      have hr := ratio_eq_of_mem_primary (eP i).2
      have hkp : (0 : ℝ) < k (eP i) := by exact_mod_cast k_pos_of_mem_primary (eP i).2
      rw [div_eq_iff (by positivity)] at hr
      linarith
    have hsum := Finset.sum_eq_zero fun i (_ : i ∈ Finset.univ) ↦ this i
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
    have hmul : ∑ x, 2 * (k (eP x) : ℝ) * monomialRlct k h hk
        = 2 * (∑ x, (k (eP x) : ℝ)) * monomialRlct k h hk := by
      rw [Finset.mul_sum, Finset.sum_mul]
    push_cast at hsum
    linarith
  have hprod : ∏ j ∈ criticalCoords k h hk, (k j : ℝ) = ∏ i, (k (eP i) : ℝ) := by
    rw [Finset.prod_subtype (criticalCoords k h hk) (fun _ ↦ Iff.rfl) fun j ↦ (k j : ℝ)]
    exact (Equiv.prod_comp eP fun a : {j // j ∈ criticalCoords k h hk} ↦ (k a : ℝ)).symm
  simp only [gammaConst, SingularLearningTheory.NormalCrossing.gammaConst, hm, hprod,
      Nat.add_sub_cancel]
  push_cast
  rw [hexp, Real.rpow_zero]

/-- Integrability of the `Y^p` integrand on `(0, ∞) × [0, b]^s` for bounded measurable traces. -/
private theorem integrable_ypIntegrand_block {lam p β : ℝ} (hlam0 : 0 < lam + p) (hb : 0 < b)
    (hβ : 0 < β) {μ : Fin s → ℝ} (hμ : ∀ i, -1 < μ i) {ξ₀ φ₀ : (Fin s → ℝ) → ℝ}
    (hξm : Measurable ξ₀) (hφm : Measurable φ₀) {M P : ℝ} (hM : 0 ≤ M)
    (hξM : ∀ w ∈ cube s b, |ξ₀ w| ≤ M)
    (hφP : ∀ w ∈ cube s b, |φ₀ w| ≤ P) :
    Integrable (fun z : ℝ × (Fin s → ℝ) ↦ z.1 ^ (lam + p - 1) *
        exp (-(β * z.1) + β * √z.1 * ξ₀ z.2) * (∏ i, z.2 i ^ μ i) * φ₀ z.2)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (cube s b))) := by
  have hcube : MeasurableSet (cube s b) :=
    measurableSet_Icc
  have hg : IntegrableOn (fun t : ℝ ↦ t ^ (lam + p - 1) * exp (-(β * t) + β * √t * M)) (Ioi 0) :=
    NormalCrossing.integrableOn_rpow_mul_exp_frozen hlam0 hβ (abs_of_nonneg hM).le
  have hsw : IntegrableOn (fun w : Fin s → ℝ ↦ (∏ i, w i ^ μ i) * P)
      (cube s b) := (integrableOn_cube_rpow hμ hb).mul_const P
  have hmeas : Measurable fun z : ℝ × (Fin s → ℝ) ↦ z.1 ^ (lam + p - 1) *
      exp (-(β * z.1) + β * √z.1 * ξ₀ z.2) * (∏ i, z.2 i ^ μ i) * φ₀ z.2 := by
    refine (((measurable_fst.pow_const _).mul (Real.measurable_exp.comp ?_)).mul ?_).mul
      (hφm.comp measurable_snd)
    · exact ((measurable_const.mul measurable_fst).neg).add
        ((measurable_const.mul (Real.continuous_sqrt.measurable.comp measurable_fst)).mul
          (hξm.comp measurable_snd))
    · exact Finset.measurable_prod _ fun i _ ↦
        ((measurable_pi_apply i).comp measurable_snd).pow_const _
  refine Integrable.mono' (hg.mul_prod hsw) hmeas.aestronglyMeasurable ?_
  rw [Measure.prod_restrict]
  filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod hcube)] with z hz
  obtain ⟨ht, hw⟩ := hz
  have ht : (0 : ℝ) < z.1 := ht
  have hprod : 0 ≤ ∏ i, z.2 i ^ μ i :=
    Finset.prod_nonneg fun i _ ↦ Real.rpow_nonneg (hw.1 i) _
  have hexp : exp (-(β * z.1) + β * √z.1 * ξ₀ z.2) ≤ exp (-(β * z.1) + β * √z.1 * M) := by
    gcongr
    exact (le_abs_self _).trans (hξM _ hw)
  simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg ht.le _),
    abs_of_pos (Real.exp_pos _), abs_of_nonneg hprod]
  calc z.1 ^ (lam + p - 1) * exp (-(β * z.1) + β * √z.1 * ξ₀ z.2) * (∏ i, z.2 i ^ μ i) *
        |φ₀ z.2|
      ≤ z.1 ^ (lam + p - 1) * exp (-(β * z.1) + β * √z.1 * M) * (∏ i, z.2 i ^ μ i) * P := by
        gcongr
        exact hφP _ hw
    _ = _ := by ring

/-- The challenge's `Y^p(n, ξ, φ)` is `(log n)^r / n^{λ+p}` times the library's frozen limit of the
shifted block data, evaluated at the traces `w ↦ ξ(e(0, w))`, `w ↦ φ(e(0, w))`. -/
private theorem normalCrossingCentralPart_eq_block (hm : monomialMultiplicity k h hk = r + 1)
    (hb : 0 < b) (β p : ℝ)
    (hβ : 0 < β) (hp : 0 ≤ p) (n : ℝ) (ξ φ : (Fin d → ℝ) → ℝ) (hξ : ContinuousOn ξ (cube d b))
    (hφ : ContinuousOn φ (cube d b)) :
    normalCrossingCentralPart k h hk b β p n hb.le ⟨fun x ↦ ξ x, hξ.domRestrict⟩
        ⟨fun x ↦ φ x, hφ.domRestrict⟩
      = log n ^ r / n ^ (monomialRlct k h hk + p) *
        frozenLimit (fun i ↦ k (eP i)) (fun i ↦ (h (eP i) : ℝ) + 2 * k (eP i) * p)
          (fun i ↦ k (eS i)) (fun i ↦ (h (eS i) : ℝ) + 2 * k (eS i) * p)
          (monomialRlct k h hk + p) b β
          (fun w ↦ ext (⟨fun x ↦ ξ x, hξ.domRestrict⟩ : C(cube d b, ℝ))
            (MeasurableEquiv.blockEquiv eP eS (0, w)))
          (fun w ↦ ext (⟨fun x ↦ φ x, hφ.domRestrict⟩ : C(cube d b, ℝ))
            (MeasurableEquiv.blockEquiv eP eS (0, w))) := by
  set lam := monomialRlct k h hk with hlam_def
  set ξD : C(cube d b, ℝ) := ⟨fun x ↦ ξ x, hξ.domRestrict⟩ with hξD
  set φD : C(cube d b, ℝ) := ⟨fun x ↦ φ x, hφ.domRestrict⟩ with hφD
  have hlam0 : 0 < lam := monomialRlct_pos hk
  have hμ : ∀ i, -1 < (h (eS i) : ℝ) - 2 * k (eS i) * lam := fun i ↦ by
    linarith [secondary_lt_of_notMem_primary (eS i).2]
  have hF : MeasurableSet (Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b)) :=
    measurableSet_Icc
  have hcube : MeasurableSet (cube s b) :=
    measurableSet_Icc
  -- the traces on the secondary block
  set ξ₀ : (Fin s → ℝ) → ℝ := fun w ↦ ext ξD (MeasurableEquiv.blockEquiv eP eS (0, w)) with hξ₀
  set φ₀ : (Fin s → ℝ) → ℝ := fun w ↦ ext φD (MeasurableEquiv.blockEquiv eP eS (0, w)) with hφ₀
  have hξ₀m : Measurable ξ₀ :=
    (measurable_ext hξ).comp ((MeasurableEquiv.blockEquiv eP eS).measurable.comp
        (measurable_const.prodMk
      measurable_id))
  have hφ₀m : Measurable φ₀ :=
    (measurable_ext hφ).comp ((MeasurableEquiv.blockEquiv eP eS).measurable.comp
        (measurable_const.prodMk
      measurable_id))
  have hzero : ∀ w ∈ cube s b,
      ((0 : Fin (r + 1) → ℝ), w) ∈ cube (r + 1) b ×ˢ cube s b :=
    fun w hw ↦ ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, hw⟩
  have hξ₀M : ∀ w ∈ cube s b, |ξ₀ w| ≤ ‖ξD‖ := fun w hw ↦
    abs_ext_le ξD (blockEquiv_mem_cube eP eS (hzero w hw))
  have hφ₀P : ∀ w ∈ cube s b, |φ₀ w| ≤ ‖φD‖ := fun w hw ↦
    abs_ext_le φD (blockEquiv_mem_cube eP eS (hzero w hw))
  -- the ambient integrand of the inner integral
  set G : ℝ → ({j // j ∉ criticalCoords k h hk} → ℝ) → ℝ := fun t v ↦
    t ^ (lam + p - 1) * exp (-(β * t) + β * √t * ext ξD (toCriticalFaceFn k h hk v)) *
      (∏ j, v j ^ ((h j : ℝ) - 2 * k j * lam)) * ext φD (toCriticalFaceFn k h hk v) with hG
  -- the inner integral on the subtype is the set integral of `G`, reindexed to the block cube
  have hinner : ∀ t : ℝ, ∫ v : Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b),
      t ^ (lam + p - 1) * exp (-(β * t) + β * √t * ξD (toCriticalFace k h hk hb.le v)) *
        (∏ j, v.val j ^ ((h j : ℝ) - 2 * k j * lam)) * φD (toCriticalFace k h hk hb.le v)
        ∂(volume.comap Subtype.val)
      = ∫ w in cube s b, t ^ (lam + p - 1) * exp (-(β * t) + β * √t * ξ₀ w) *
          NormalCrossing.secondaryWeight (fun i ↦ k (eS i)) (fun i ↦ (h (eS i) : ℝ)) lam w * φ₀ w :=
              by
    intro t
    have h1 : ∀ v : Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b),
        t ^ (lam + p - 1) * exp (-(β * t) + β * √t * ξD (toCriticalFace k h hk hb.le v)) *
          (∏ j, v.val j ^ ((h j : ℝ) - 2 * k j * lam)) * φD (toCriticalFace k h hk hb.le v)
        = G t v := by
      intro v
      simp only [hG]
      rw [← ext_coe ξD (toCriticalFace k h hk hb.le v),
        ← ext_coe φD (toCriticalFace k h hk hb.le v), toCriticalFace_val]
    simp only [h1]
    rw [integral_subtype_comap hF (G t),
      ← (volume_measurePreserving_piCongrLeft (fun _ ↦ ℝ) eS).setIntegral_preimage_emb
        (MeasurableEquiv.measurableEmbedding _) (G t), secEquiv_preimage_Icc]
    refine setIntegral_congr_fun hcube fun w _ ↦ ?_
    simp only [hG, hξ₀, hφ₀]
    rw [toCriticalFaceFn_secEquiv eP eS, prod_secEquiv eS]
  -- assemble: Fubini, then pull out the constants
  have hint := integrable_ypIntegrand_block (s := s) (lam := lam) (p := p) (by positivity) hb hβ hμ
    hξ₀m hφ₀m (norm_nonneg ξD) hξ₀M hφ₀P
  simp only [normalCrossingCentralPart, hm, Nat.add_sub_cancel, Function.comp_apply]
  rw [← hlam_def]
  simp only [hinner]
  rw [frozenLimit_shift, gammaConst_eq_block eP hm, hlam_def]
  rw [integral_integral_swap (f := fun (t : ℝ) (w : Fin s → ℝ) ↦
    t ^ (monomialRlct k h hk + p - 1) * exp (-(β * t) + β * √t * ξ₀ w) *
      NormalCrossing.secondaryWeight (fun i ↦ k (eS i)) (fun i ↦ (h (eS i) : ℝ))
          (monomialRlct k h hk) w * φ₀ w)
    hint]
  have hin : ∀ w, ∫ t in Ioi (0 : ℝ),
      t ^ (monomialRlct k h hk + p - 1) * exp (-(β * t) + β * √t * ξ₀ w) *
        NormalCrossing.secondaryWeight (fun i ↦ k (eS i)) (fun i ↦ (h (eS i) : ℝ))
            (monomialRlct k h hk) w * φ₀ w
      = NormalCrossing.secondaryWeight (fun i ↦ k (eS i)) (fun i ↦ (h (eS i) : ℝ))
          (monomialRlct k h hk) w *
        φ₀ w * ∫ t in Ioi (0 : ℝ),
          t ^ (monomialRlct k h hk + p - 1) * exp (-(β * t) + β * √t * ξ₀ w) := by
    intro w
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ ↦ ?_
    ring
  simp only [hin]
  ring


/-! ### The `C¹` data: the gradient norm and the Lipschitz bound towards the primary face -/

/-- The operator norm of `L : ℝ^d →L ℝ` is at most `d · max_j |L e_j|`. -/
private theorem opNorm_le_card_mul {L : (Fin d → ℝ) →L[ℝ] ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hL : ∀ j, ‖L (Pi.single j 1)‖ ≤ C) : ‖L‖ ≤ d * C := by
  refine ContinuousLinearMap.opNorm_le_bound L (by positivity) fun x ↦ ?_
  have hx : L x = ∑ j, x j • L (Pi.single j 1) := by
    have := (L : (Fin d → ℝ) →ₗ[ℝ] ℝ).pi_apply_eq_sum_univ x
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  rw [hx]
  calc ‖∑ j, x j • L (Pi.single j 1)‖ ≤ ∑ j, ‖x j • L (Pi.single j 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _j : Fin d, ‖x‖ * C := Finset.sum_le_sum fun j _ ↦ by
        rw [norm_smul]
        exact mul_le_mul (norm_le_pi_norm x j) (hL j) (norm_nonneg _) (norm_nonneg _)
    _ = d * C * ‖x‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The mean value step in the proof of [Wat09, Theorem 4.9]: for `ξ` of class `C¹`
on the cube with `|∂_j ξ| ≤ Cg`, `|ξ(e z) − ξ(e(0, z.2))| ≤ d Cg Σ_i z.1_i` on the block cube
(`e = blockEquiv eP eS`; the two points differ in the primary coordinates only). -/
private theorem abs_sub_face_le (hb : 0 < b) {ξ : (Fin d → ℝ) → ℝ}
    (hξ : ContDiffOn ℝ 1 ξ (cube d b)) {Cg : ℝ} (hCg : 0 ≤ Cg)
    (hgrad : ∀ x ∈ cube d b, ∀ j, |fderivWithin ℝ ξ (cube d b) x (Pi.single j 1)| ≤ Cg)
    {z : (Fin (r + 1) → ℝ) × (Fin s → ℝ)}
    (hz : z ∈ cube (r + 1) b ×ˢ cube s b) :
    |ext (⟨fun x ↦ ξ x, hξ.continuousOn.domRestrict⟩ : C(cube d b, ℝ))
        (MeasurableEquiv.blockEquiv eP eS z) -
        ext (⟨fun x ↦ ξ x, hξ.continuousOn.domRestrict⟩ : C(cube d b, ℝ))
          (MeasurableEquiv.blockEquiv eP eS (0, z.2))|
      ≤ d * Cg * ∑ i, z.1 i := by
  have hz0 : ((0 : Fin (r + 1) → ℝ), z.2)
      ∈ cube (r + 1) b ×ˢ cube s b :=
    ⟨⟨fun _ ↦ le_rfl, fun _ ↦ hb.le⟩, hz.2⟩
  have hy : MeasurableEquiv.blockEquiv eP eS z ∈ cube d b := blockEquiv_mem_cube eP eS hz
  have hx : MeasurableEquiv.blockEquiv eP eS (0, z.2) ∈ cube d b := blockEquiv_mem_cube eP eS hz0
  rw [ext_apply_of_mem hξ.continuousOn hy, ext_apply_of_mem hξ.continuousOn hx]
  have hD : Convex ℝ (cube d b) := convex_Icc _ _
  have hdiff : DifferentiableOn ℝ ξ (cube d b) := hξ.differentiableOn one_ne_zero
  have hbound : ∀ x ∈ cube d b, ‖fderivWithin ℝ ξ (cube d b) x‖ ≤ d * Cg := fun x hx ↦
    opNorm_le_card_mul hCg fun j ↦ by rw [Real.norm_eq_abs]; exact hgrad x hx j
  have hmv := hD.norm_image_sub_le_of_norm_fderivWithin_le hdiff hbound hx hy
  have hsum0 : 0 ≤ ∑ i, z.1 i := Finset.sum_nonneg fun i _ ↦ hz.1.1 i
  have hnorm : ‖MeasurableEquiv.blockEquiv eP eS z - MeasurableEquiv.blockEquiv eP eS (0, z.2)‖ ≤ ∑
      i, z.1 i := by
    refine (pi_norm_le_iff_of_nonneg hsum0).mpr fun j ↦ ?_
    obtain ⟨t, rfl⟩ := (Equiv.blockIndex eP eS).surjective j
    rcases t with i | i
    · simp only [Pi.sub_apply, Equiv.blockIndex_inl, MeasurableEquiv.blockEquiv_apply_inl,
        Pi.zero_apply, sub_zero,
        Real.norm_eq_abs, abs_of_nonneg (hz.1.1 i)]
      exact Finset.single_le_sum (f := z.1) (fun i _ ↦ hz.1.1 i) (Finset.mem_univ i)
    · simp only [Pi.sub_apply, Equiv.blockIndex_inr, MeasurableEquiv.blockEquiv_apply_inr, sub_self,
        norm_zero]
      exact hsum0
  rw [Real.norm_eq_abs] at hmv
  calc |ξ (MeasurableEquiv.blockEquiv eP eS z) - ξ (MeasurableEquiv.blockEquiv eP eS (0, z.2))|
      ≤ d * Cg * ‖MeasurableEquiv.blockEquiv eP eS z - MeasurableEquiv.blockEquiv eP eS (0, z.2)‖ :=
          hmv
    _ ≤ d * Cg * ∑ i, z.1 i := by gcongr

end GB49

/-- **The central part approximates the monomial partition function.** `‖∇ξ‖` is the maximum over
all coordinates, and `n` is real with `n ≥ 2`.

Relation to the source.
* **Gap.** The book's $\|\nabla \xi\|$ is the maximum over the critical coordinates; here it is over
  all coordinates, a weaker bound.
* **Formalisation note.** The constant $C$ may depend on $p$, and $(\log n)^{m-2}$ is a real power,
  so $m = 1$ gives $1/\log n$.

Source statement: [Wat09, Theorem 4.9] -/
theorem abs_normalCrossingIntegral_sub_normalCrossingCentralPart_le {d : ℕ} (k h : Fin d → ℕ)
    (hk : ∃ j, 0 < k j) (b β p : ℝ)
    (hb : 0 < b) (hβ : 0 < β) (hp : 0 ≤ p) :
    let D := cube d b
    let lam := monomialRlct k h hk
    let m := monomialMultiplicity k h hk
    let Zp := normalCrossingIntegral k h b β p
    let Yp := fun n ↦ normalCrossingCentralPart k h hk b β p n hb.le
    ∃ C > 0, ∀ (ξ φ : (Fin d → ℝ) → ℝ)
      (hξ : ContDiffOn ℝ 1 ξ D) (hφ : ContDiffOn ℝ 1 φ D),
      -- restriction of ξ and φ to D
      let ξD : C(D, ℝ) := ⟨fun x ↦ ξ x, hξ.continuousOn.domRestrict⟩
      let φD : C(D, ℝ) := ⟨fun x ↦ φ x, hφ.continuousOn.domRestrict⟩
      -- ‖∇f‖ = max_j sup_{x ∈ D} |∂_j f(x)| over all coordinates j
      let gradξ : C(D, Fin d → ℝ) :=
        ⟨fun x j ↦ fderivWithin ℝ ξ D x (Pi.single j 1),
          continuous_fderivWithin_cube hb ξ hξ⟩
      let gradφ : C(D, Fin d → ℝ) :=
        ⟨fun x j ↦ fderivWithin ℝ φ D x (Pi.single j 1),
          continuous_fderivWithin_cube hb φ hφ⟩
      ∀ (n : ℝ) (hn : 2 ≤ n),
        |Zp n ξD φD - Yp n ξD φD|
          ≤ C * log n ^ ((m : ℝ) - 2) / n ^ (lam + p) * exp (β * ‖ξD‖ ^ 2 / 2) *
            (β * ‖gradξ‖ * ‖φD‖ + ‖gradφ‖ + ‖φD‖) := by
  intro D lam m Zp Yp
  -- Permute the `m` primary coordinates first; then `Z^p` and `Y^p` are the library's block
  -- integrals for the weights shifted by `2kp`, and `quantitative_approx` gives the rate with the
  -- Lipschitz constants `d ‖∇ξ‖`, `d ‖∇φ‖` from the mean value theorem.
  have hmpos : 0 < monomialMultiplicity k h hk := by
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_inf' (s := Finset.univ.filter fun j ↦ 0 < k j)
      (by obtain ⟨j, hj⟩ := hk; exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩)
      (fun j ↦ ((h j : ℝ) + 1) / (2 * k j))
    exact Finset.card_pos.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, (Finset.mem_filter.mp hj).2, by rw [monomialRlct, hjeq]⟩⟩
  obtain ⟨r, hr⟩ : ∃ r, monomialMultiplicity k h hk = r + 1 :=
    ⟨monomialMultiplicity k h hk - 1, (Nat.sub_add_cancel hmpos).symm⟩
  have hcardP : Fintype.card {j // j ∈ criticalCoords k h hk} = r + 1 := by
    rw [Fintype.card_coe]; exact hr
  have hcardS : Fintype.card {j // j ∉ criticalCoords k h hk} = d - (r + 1) := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, hcardP]
  let eP : Fin (r + 1) ≃ {j // j ∈ criticalCoords k h hk} := (Fintype.equivFinOfCardEq hcardP).symm
  let eS : Fin (d - (r + 1)) ≃ {j // j ∉ criticalCoords k h hk} :=
    (Fintype.equivFinOfCardEq hcardS).symm
  have hlam0 : 0 < lam := monomialRlct_pos hk
  have hkP : ∀ i, 0 < k (eP i) := fun i ↦ k_pos_of_mem_primary (eP i).2
  have hlamP : ∀ i, ((h (eP i) : ℝ) + 1) / (2 * k (eP i)) = lam := fun i ↦
    ratio_eq_of_mem_primary (eP i).2
  have hsecS : ∀ i, 2 * (k (eS i) : ℝ) * lam < (h (eS i) : ℝ) + 1 := fun i ↦
    secondary_lt_of_notMem_primary (eS i).2
  obtain ⟨-, -, hlamP', -⟩ := NormalCrossing.exponents_aux (k := fun i ↦ k (eP i))
      (h := fun i ↦ (h (eP i) : ℝ))
    (k' := fun i ↦ k (eS i)) (h' := fun i ↦ (h (eS i) : ℝ)) hkP hlamP hlam0 hsecS hp
  have hsecS' : ∀ i, 2 * (k (eS i) : ℝ) * (lam + p) < (h (eS i) : ℝ) + 2 * k (eS i) * p + 1 :=
    fun i ↦ by linarith [hsecS i]
  -- the library's constant, for the block data shifted by `2kp`
  obtain ⟨C₀, hC₀, HQ⟩ := quantitative_approx (k := fun i ↦ k (eP i))
    (h := fun i ↦ (h (eP i) : ℝ) + 2 * k (eP i) * p) (k' := fun i ↦ k (eS i))
    (h' := fun i ↦ (h (eS i) : ℝ) + 2 * k (eS i) * p) (lam := lam + p) hkP hlamP'
    (by positivity) hsecS' hb hβ
  have hd1 : (1 : ℝ) ≤ d := by
    have : d ≠ 0 := by
      rintro rfl
      obtain ⟨j, -⟩ := hk
      exact j.elim0
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr this
  refine ⟨C₀ * d + 1, by positivity, fun ξ φ hξ hφ ↦ ?_⟩
  intro ξD φD gradξ gradφ n hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hl0 : 0 < log n := Real.log_pos (by linarith)
  have hnl : 0 < n ^ (lam + p) := Real.rpow_pos_of_pos hn0 _
  -- the transported data on the block cube
  have hξ'm : Measurable (ext ξD ∘ MeasurableEquiv.blockEquiv eP eS) :=
    (measurable_ext hξ.continuousOn).comp (MeasurableEquiv.blockEquiv eP eS).measurable
  have hφ'm : Measurable (ext φD ∘ MeasurableEquiv.blockEquiv eP eS) :=
    (measurable_ext hφ.continuousOn).comp (MeasurableEquiv.blockEquiv eP eS).measurable
  have hξ'M : ∀ z ∈ cube (r + 1) b ×ˢ cube (d - (r + 1)) b,
      |(ext ξD ∘ MeasurableEquiv.blockEquiv eP eS) z| ≤ ‖ξD‖ := fun z hz ↦
    abs_ext_le ξD (blockEquiv_mem_cube eP eS hz)
  have hφ'M : ∀ z ∈ cube (r + 1) b ×ˢ cube (d - (r + 1)) b,
      |(ext φD ∘ MeasurableEquiv.blockEquiv eP eS) z| ≤ ‖φD‖ := fun z hz ↦
    abs_ext_le φD (blockEquiv_mem_cube eP eS hz)
  have hgradξ : ∀ x ∈ D, ∀ j, |fderivWithin ℝ ξ D x (Pi.single j 1)| ≤ ‖gradξ‖ := fun x hx j ↦ by
    have h1 : ‖gradξ ⟨x, hx⟩ j‖ ≤ ‖gradξ ⟨x, hx⟩‖ := norm_le_pi_norm _ j
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (ContinuousMap.norm_coe_le_norm gradξ ⟨x, hx⟩)
  have hgradφ : ∀ x ∈ D, ∀ j, |fderivWithin ℝ φ D x (Pi.single j 1)| ≤ ‖gradφ‖ := fun x hx j ↦ by
    have h1 : ‖gradφ ⟨x, hx⟩ j‖ ≤ ‖gradφ ⟨x, hx⟩‖ := norm_le_pi_norm _ j
    rw [Real.norm_eq_abs] at h1
    exact h1.trans (ContinuousMap.norm_coe_le_norm gradφ ⟨x, hx⟩)
  have hξ'L : ∀ z ∈ cube (r + 1) b ×ˢ cube (d - (r + 1)) b,
      |(ext ξD ∘ MeasurableEquiv.blockEquiv eP eS) z - (ext ξD ∘ MeasurableEquiv.blockEquiv eP eS)
          (0, z.2)|
        ≤ d * ‖gradξ‖ * ∑ i, z.1 i := fun z hz ↦
    abs_sub_face_le eP eS hb hξ (norm_nonneg _) hgradξ hz
  have hφ'L : ∀ z ∈ cube (r + 1) b ×ˢ cube (d - (r + 1)) b,
      |(ext φD ∘ MeasurableEquiv.blockEquiv eP eS) z - (ext φD ∘ MeasurableEquiv.blockEquiv eP eS)
          (0, z.2)|
        ≤ d * ‖gradφ‖ * ∑ i, z.1 i := fun z hz ↦
    abs_sub_face_le eP eS hb hφ (norm_nonneg _) hgradφ hz
  -- the block estimate
  have hmain := HQ (ext ξD ∘ MeasurableEquiv.blockEquiv eP eS)
      (ext φD ∘ MeasurableEquiv.blockEquiv eP eS) ‖ξD‖ ‖φD‖
    (d * ‖gradξ‖) (d * ‖gradφ‖) hξ'm hφ'm (by positivity) (by positivity) hξ'M hφ'M hξ'L hφ'L
    n hn
  rw [← NormalCrossing.blockIntegral_shift, ← normalCrossingIntegral_eq_block eP eS] at hmain
  have hY := normalCrossingCentralPart_eq_block eP eS hr hb β p hβ hp n ξ φ hξ.continuousOn
      hφ.continuousOn
  -- the rate `(log n)^{m−2} = (log n)^r / log n`
  have hlog : log n ^ ((m : ℝ) - 2) = log n ^ r / log n := by
    have hm : (m : ℝ) = r + 1 := by simp only [m, hr]; push_cast; ring
    rw [hm, show (r : ℝ) + 1 - 2 = (r : ℝ) - 1 by ring, Real.rpow_sub hl0, Real.rpow_natCast,
      Real.rpow_one]
  -- the constants
  have hG0 : 0 ≤ ‖gradξ‖ := norm_nonneg _
  have hG0' : 0 ≤ ‖gradφ‖ := norm_nonneg _
  have hP0 : 0 ≤ ‖φD‖ := norm_nonneg _
  have hkey : C₀ * (β * (d * ‖gradξ‖) * ‖φD‖ + d * ‖gradφ‖ + ‖φD‖)
      ≤ (C₀ * d + 1) * (β * ‖gradξ‖ * ‖φD‖ + ‖gradφ‖ + ‖φD‖) := by
    nlinarith [mul_nonneg (mul_nonneg hC₀ hP0) (sub_nonneg.mpr hd1),
      mul_nonneg (mul_nonneg hβ.le hG0) hP0, mul_nonneg hC₀ hP0]
  calc |Zp n ξD φD - Yp n ξD φD|
      ≤ C₀ * log n ^ r / (n ^ (lam + p) * log n) * exp (β * ‖ξD‖ ^ 2 / 2) *
        (β * (d * ‖gradξ‖) * ‖φD‖ + d * ‖gradφ‖ + ‖φD‖) := by
        simp only [Zp, Yp]
        rw [hY]
        exact hmain
    _ = log n ^ r / (n ^ (lam + p) * log n) * exp (β * ‖ξD‖ ^ 2 / 2) *
        (C₀ * (β * (d * ‖gradξ‖) * ‖φD‖ + d * ‖gradφ‖ + ‖φD‖)) := by ring
    _ ≤ log n ^ r / (n ^ (lam + p) * log n) * exp (β * ‖ξD‖ ^ 2 / 2) *
        ((C₀ * d + 1) * (β * ‖gradξ‖ * ‖φD‖ + ‖gradφ‖ + ‖φD‖)) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = _ := by rw [hlog]; ring

/-! ## Resolution atlases

The singularity type of a nondegenerate atlas whose potential and prior are continuous on a
compact `W`. -/

section AtlasBridges

open MeasureTheory Filter Topology

variable {K φ : (Fin d → ℝ) → ℝ} {W : Set (Fin d → ℝ)}

/-- The type of a nondegenerate atlas, for `K` and `φ ≥ 0` continuous on the compact `W`
(`NondegenerateResolutionAtlas.isSingularityType` asks for a measurable potential; `K` is
replaced by `W.piecewise K 0`, which the atlas and the type only see on `W`). -/
theorem NondegenerateResolutionAtlas.isSingularityType_of_continuousOn {K φ : (Fin d → ℝ) → ℝ}
    {W : Set (Fin d → ℝ)}
    (hW : IsCompact W) (hKc : ContinuousOn K W) (hφ : ∀ w ∈ W, 0 ≤ φ w) (hφc : ContinuousOn φ W)
    (R : NondegenerateResolutionAtlas K φ W) : IsSingularityType K φ W R.rlct R.mult := by
  classical
  have hWm : MeasurableSet W := hW.isClosed.measurableSet
  have hagree : ∀ w ∈ W, K w = W.piecewise K 0 w := fun w hw ↦
    (Set.piecewise_eq_of_mem W _ _ hw).symm
  have hKm : Measurable (W.piecewise K 0) :=
    ContinuousOn.measurable_piecewise hKc continuousOn_const hWm
  exact ((R.congr hagree).isSingularityType hWm hKm hφ (hφc.aemeasurable hWm)).congr
    fun w hw ↦ (hagree w hw).symm

end AtlasBridges


end SingularLearningTheory
