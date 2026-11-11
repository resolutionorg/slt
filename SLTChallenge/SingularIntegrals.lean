/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.TangentCone.Real
public import Mathlib.MeasureTheory.Measure.Comap
public import Mathlib.Topology.ContinuousMap.Compact
public import SLTChallenge.Setting
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

/-!
# Singular integrals: challenge statements

Statements of the bounds on the partition functions of normal-crossing potentials,
[Wat09, Theorems 4.7–4.9], and of the four characterizations of the singularity type
$(\lambda, m)$ in [Wat09, Theorem 7.1]. The theorem bodies are `sorry` by design.
`SLT/SingularIntegrals/Defs.lean` has the definitions word for word, and
`SLT/SingularIntegrals.lean` proves the theorems.

For Chapter 4 the file fixes, for exponents $k, h \in \mathbb N^d$ with some $k_j > 0$, the
potential $x^{2k}$ and the weight $x^h$ on the cube $[0, b]^d$, the threshold
$\lambda = \min_{k_j > 0} (h_j + 1)/(2k_j)$, the critical coordinates that attain it and their
number $m$, the partition function $Z^p(n, \xi, \varphi)$ of [Wat09, Definition 4.10] and its case
$Z^p(n)$, the constant $\gamma_b$ and the central part $Y^p(n, \xi, \varphi)$. Theorems 4.7 and 4.8
bound $Z^p(n)$ and $Z^p(n, \xi, \varphi)$ above and below by multiples of
$(\log n)^{m-1}/n^{\lambda + p}$. Theorem 4.9 bounds $|Z^p - Y^p|$ by
$(\log n)^{m-2}/n^{\lambda + p}$ times norms of $\xi$, $\varphi$ and their gradients.

For Chapter 7 the file fixes the singular integral $Z_0(n) = \int_W e^{-n\beta K}\varphi$, the
volume `SingularLearningTheory.sublevelVolume` $V(t)$ of $\{K \le t\}$, the state density $v = V'$
and the predicate `SingularLearningTheory.IsSingularityType`, two-sided bounds
$V(\varepsilon) \asymp \varepsilon^\lambda (-\log\varepsilon)^{m-1}$ as $\varepsilon \to 0^+$, which
`SingularLearningTheory.singularity_type_unique` states determine $(\lambda, m)$. For an analytic
$K \ge 0$ on a compact $W$, the four parts of Theorem 7.1 state
$Z_0(n) \sim c_1 (\log n)^{m-1}/n^\lambda$, $\lambda = -\lim_n \log Z_0(n)/\log n$,
$v(t) \sim c_2 t^{\lambda-1}(-\log t)^{m-1}$ and
$\lambda = \lim_{t \to 0^+} \log(V(at)/V(t))/\log a$. Each statement's docstring records where it
differs from the book.
-/

@[expose] public section

namespace SingularLearningTheory

open MeasureTheory Set

variable {E : Type*} [MeasureSpace E]

/-- The volume function `V(t) = ∫_W 𝟙(K(w) ≤ t) φ(w) dw` of [Wat09, eq. (4.9)]. Stated under its
name in `SLT/SingularIntegrals/StateDensity.lean`, so comparator checks that the two definitions
agree.

Relation to the source.
* **Interpretation.** The volume uses $K \le t$ where [Wat09, eq. (4.9)] has $K < t$. -/
noncomputable def sublevelVolume (K φ : E → ℝ) (W : Set E) (t : ℝ) : ℝ :=
  ∫ w in W, {w | K w ≤ t}.indicator φ w

end SingularLearningTheory

namespace SingularLearningTheory

open MeasureTheory (IntegrableOn volume)
open Set (Icc Ioi)
open Real (exp log)

variable {d : ℕ}

/-! ## Normal-crossing singular integrals ([Wat09, Section 4.4]) -/

section NormalCrossing

/-- The closed cube $[0, b]^d$, the domain of the normal-crossing integrals. -/
abbrev cube (d : ℕ) (b : ℝ) : Set (Fin d → ℝ) :=
  Icc 0 (fun _ ↦ b)

/-- The normal-crossing potential `x ↦ x^{2k}`, the book's `K(x, y)²` in [Wat09, eq. (4.18)]. -/
def normalCrossing (k : Fin d → ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ j, x j ^ (2 * k j)

/-- The monomial weight `x ↦ x^h`. -/
noncomputable def monomialWeight (h : Fin d → ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ j, x j ^ (h j : ℝ)

/-- The positive exponents form a nonempty set of coordinates. -/
lemma active_coords_nonempty {d : ℕ} (k : Fin d → ℕ) (hk : ∃ j, 0 < k j) :
    (Finset.univ.filter fun j ↦ 0 < k j).Nonempty :=
  sorry

/-- The threshold `λ` of [Wat09, Theorem 4.7]: the minimum of `(h_j + 1) / (2 k_j)` over the
coordinates with `k_j > 0`, of which there must be at least one. -/
noncomputable def monomialRlct (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j) : ℝ :=
  Finset.inf' (Finset.univ.filter fun j ↦ 0 < k j)
    (active_coords_nonempty k hk)
    (fun j ↦ ((h j : ℝ) + 1) / (2 * k j))

/-- The active coordinates attaining the minimum ratio. -/
noncomputable def criticalCoords (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j) : Finset (Fin d) :=
  Finset.univ.filter fun j ↦ 0 < k j ∧ ((h j : ℝ) + 1) / (2 * k j) = monomialRlct k h hk

/-- The number `m` of critical coordinates, the book's `r` in [Wat09, Theorem 4.7]. -/
noncomputable def monomialMultiplicity (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j) : ℕ :=
  (criticalCoords k h hk).card

/-- Inserting zeros at the critical coordinates produces a point in the cube. -/
lemma toCriticalFace_mem_cube {d : ℕ} (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j)
    {b : ℝ} (hb : 0 ≤ b)
    (v : Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b)) :
    (fun j ↦ if hj : j ∈ criticalCoords k h hk then 0 else v.val ⟨j, hj⟩) ∈ cube d b :=
  sorry

/-- The point of the face of `[0, b]^d` obtained from `v ∈ [0, b]^(d−m)` by inserting zeros at
the critical coordinates; when these are the first `m`, `v ↦ (0, …, 0, v₁, …, v_(d−m))`. -/
noncomputable def toCriticalFace (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j) {b : ℝ} (hb : 0 ≤ b)
    (v : Icc (0 : {j // j ∉ criticalCoords k h hk} → ℝ) (fun _ ↦ b)) : cube d b :=
  ⟨fun j ↦ if hj : j ∈ criticalCoords k h hk then 0 else v.val ⟨j, hj⟩,
    toCriticalFace_mem_cube k h hk hb v⟩

/-- The partition function `Z^p(n, ξ, φ)` of [Wat09, Definition 4.10].

Relation to the source.
* **Interpretation.** `normalCrossing k` $= x^{2k}$ is the book's $K(x, y)^2$, so the factor $K^p$
  is the book's $K(x, y)^{2p}$: the reading under which the book's proofs give the rate
  $n^{\lambda + p}$. -/
noncomputable def normalCrossingIntegral (k h : Fin d → ℕ) (b β p n : ℝ) (ξ φ : C(cube d b, ℝ)) :
    ℝ :=
  let D := cube d b
  let K := normalCrossing k
  ∫ x : D,
    (K x) ^ p *
      exp (-(n * β * K x) + √n * β * √(K x) * ξ x) *
      (monomialWeight h x) * φ x ∂(volume.comap Subtype.val)

/-- The singular integral `Z^p(n)` of [Wat09, eq. (4.18)], the case `ξ = 0`, `φ = 1` of
`normalCrossingIntegral`. -/
noncomputable abbrev normalCrossingIntegral₀ (k h : Fin d → ℕ) (b β p n : ℝ) : ℝ :=
  normalCrossingIntegral k h b β p n 0 1

/-- The constant `γ_b` of [Wat09, eq. (4.16)].

Relation to the source.
* **Restatement.** The factor $b^{|h| + r - 2|k|\lambda}$ of [Wat09, eq. (4.16)] is omitted: its
  exponent vanishes on the critical coordinates, where $h_j + 1 = 2k_j\lambda$. -/
noncomputable def gammaConst (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j) : ℝ :=
  let m := monomialMultiplicity k h hk
  let I := criticalCoords k h hk
  1 / (2 ^ m * (m - 1).factorial * ∏ j ∈ I, (k j : ℝ))

/-- The central part `Y^p(n, ξ, φ)` of the partition function, [Wat09, eq. (4.19)]. The inner
integral is over the non-critical coordinates, including those with `k_j = 0`. -/
noncomputable def normalCrossingCentralPart (k h : Fin d → ℕ) (hk : ∃ j, 0 < k j) (b β p n : ℝ)
    (hb : 0 ≤ b)
    (ξ φ : C(cube d b, ℝ)) : ℝ :=
  let lam := monomialRlct k h hk -- `λ` is a Lean keyword
  let m := monomialMultiplicity k h hk
  let γ := gammaConst k h hk
  let I := criticalCoords k h hk
  -- ξ and φ with the critical coordinates set to zero: the book's ξ(0, y) and φ(0, y)
  let ξ₀ := ξ ∘ toCriticalFace k h hk hb
  let φ₀ := φ ∘ toCriticalFace k h hk hb
  -- [0, b]^(d−m), indexed by the non-critical coordinates rather than Fin (d−m)
  let F := Icc (0 : {j // j ∉ I} → ℝ) (fun _ ↦ b)
  γ * (log n) ^ (m - 1) / n ^ (lam + p) *
    ∫ t in Ioi (0 : ℝ),
      ∫ v : F,
        t ^ (lam + p - 1) *
          exp (-(β * t) + β * √t * ξ₀ v) *
          (∏ j, v.val j ^ ((h j : ℝ) - 2 * k j * lam)) * φ₀ v
        ∂(volume.comap Subtype.val)

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
        Zp n ≤ a₂ * log n ^ (m - 1) / n ^ (lam + p) :=
  sorry

/-- The origin belongs to a cube with nonnegative side length. -/
lemma zero_mem_cube {d : ℕ} {b : ℝ} (hb : 0 ≤ b) :
    (0 : Fin d → ℝ) ∈ cube d b :=
  sorry

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
          ≤ a₂ * log n ^ (m - 1) / n ^ (lam + p) * exp (β * ‖ξ‖ ^ 2 / 2) * ‖φ‖ :=
  sorry

/-- A C¹ function on a cube of positive side has a continuous gradient. -/
lemma continuous_fderivWithin_cube {d : ℕ} {b : ℝ} (hb : 0 < b)
    (f : (Fin d → ℝ) → ℝ) (hf : ContDiffOn ℝ 1 f (cube d b)) :
    Continuous (fun (x : cube d b) (j : Fin d) ↦
      fderivWithin ℝ f (cube d b) x (Pi.single j 1)) :=
  sorry

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
            (β * ‖gradξ‖ * ‖φD‖ + ‖gradφ‖ + ‖φD‖) :=
  sorry

end NormalCrossing

/-- The singular integral `Z₀(n) = ∫_W exp(−nβK(w)) φ(w) dw` of [Wat09, eq. (4.1)], with an inverse
temperature `β`.

Relation to the source.
* **Translation.** `laplaceIntegral K φ W 1 n` is the book's $Z_0(n)$ [Wat09, eq. (4.1)]; the
  inverse temperature $\beta$ is added. -/
noncomputable def laplaceIntegral (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) (β n : ℝ) : ℝ :=
  ∫ w in W, exp (-(n * β * K w)) * φ w

/-- The state density function `v(t)` of [Wat09, eq. (4.8)], the derivative of the volume `V(t)`.

Relation to the source.
* **Interpretation.** $v$ is the derivative of the volume, not the book's
  $\int \delta(t - K(w))\,\varphi(w)\,dw$; the book shows the two agree. Where $V$ is not
  differentiable the derivative is $0$, so the statements about $v$ assert differentiability. -/
noncomputable def stateDensity (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) (t : ℝ) : ℝ :=
  deriv (SingularLearningTheory.sublevelVolume K φ W) t

open Filter Topology

section SingularityType

open MeasureTheory

/-- `(λ, m)` is the singularity type of `K` and `φ` on `W`: the prior volume
`V(ε) = ∫_{W ∩ {K ≤ ε}} φ` satisfies `c₁ ε^λ (−log ε)^{m−1} ≤ V(ε) ≤ c₂ ε^λ (−log ε)^{m−1}` for
small `ε > 0`. This is the volume scaling of [Wat09, Theorem 7.1(4)], whose proof gives
`V(t) ∼ c t^λ (−log t)^{m−1}` as `t → 0`. By `zetaFunction_meromorphic_continuation`, `λ` is
rational. The definition itself takes `λ` real and the exponent `m − 1` in `ℝ`.

Relation to the source.
* **Restatement.** [Wat09, Definition 2.7] defines the real log canonical threshold through a
  resolution, and [Wat09, Definition 6.4] defines $\lambda$ and $m$ as the largest pole of the zeta
  function and its order. Here the pair is defined by volume scaling;
  `SLTResolution.isSingularityType` identifies it with the pair read off a resolution, and
  `zetaFunction_meromorphic_continuation` with the largest pole and its order. -/
def IsSingularityType (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (lam : ℝ) (m : ℕ) : Prop :=
  ∃ c₁ > (0 : ℝ), ∃ c₂ > (0 : ℝ), ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    c₁ * (ε ^ lam * (-Real.log ε) ^ ((m : ℝ) - 1)) ≤ ∫ w in W ∩ {w | K w ≤ ε}, φ w ∧
    ∫ w in W ∩ {w | K w ≤ ε}, φ w ≤ c₂ * (ε ^ lam * (-Real.log ε) ^ ((m : ℝ) - 1))

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
  sorry

end SingularityType

/-! ## [Wat09, Theorem 7.1]

The four characterisations of the singularity type `(λ, m)`. The hypotheses are those of
`zetaFunction_meromorphic_continuation`: `K` analytic near the compact set `W` and nonnegative
on it, the prior condition of `FundamentalConditionII`, and `ZeroSetConditions`: nonzero germs of
`K` and `φ` at the zeros of `K`, and positive prior mass on every positive sublevel. The last is the
book's assumption that `{w ∈ supp φ | K(w) = 0}` is nonempty, read for the measure `φ dw` on `W`.
The pair `(λ, m)` is the volume-scaling invariant `IsSingularityType`, which
`singularity_type_unique` and the zeta theorems identify with the book's largest pole and its
order. -/

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
      Tendsto (fun n : ℝ ↦ n ^ lam / log n ^ (m - 1) * laplaceIntegral K φ W β n) atTop (𝓝 c₁) :=
  sorry

/-- **The learning coefficient from the partition function.** `λ = −lim log Z₀(n) / log n`, at `β =
1` as in the book.

Source statement: [Wat09, Theorem 7.1(2)] -/
theorem tendsto_neg_log_laplaceIntegral_div_log {d : ℕ}
    (K φ : (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ))
    (hW : IsCompact W) (hKa : AnalyticOnNhd ℝ K W)
    (hK : ∀ w ∈ W, 0 ≤ K w) (II : FundamentalConditionII φ W)
    (hZ : ZeroSetConditions K φ W)
    (lam : ℝ) (m : ℕ) (hlam : 0 < lam) (hm : 1 ≤ m)
    (htype : IsSingularityType K φ W lam m) :
    Tendsto (fun n : ℝ ↦ -log (laplaceIntegral K φ W 1 n) / log n) atTop (𝓝 lam) :=
  sorry

/-- **Asymptotics of the state density.** The state density has the exact asymptotic `v(t) ~ c₂
t^(λ−1) (−log t)^(m−1)` as `t → 0⁺`. Here `v` is `stateDensity`, the derivative of the volume, so
the statement also asserts that `V` is differentiable on some interval `(0, ε)`.

Source statement: [Wat09, Theorem 7.1(3)] -/
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
        (𝓝[>] 0) (𝓝 c₂) :=
  sorry

/-- **The learning coefficient from the volume function.** `λ = lim log(V(at) / V(t)) / log a` as `t
→ 0⁺`, for every `a > 0` with `a ≠ 1`. The book's volume uses `K < t`; `sublevelVolume` uses `K ≤
t`.

Source statement: [Wat09, Theorem 7.1(4)] -/
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
  sorry

end SingularLearningTheory
