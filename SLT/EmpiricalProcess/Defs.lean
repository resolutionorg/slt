/-
Copyright (c) 2026 Resolution. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Hitchcock
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Tight
public import Mathlib.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.Independence.Basic
public import SLT.Setting
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
# The empirical process and its limit: definitions

[Wat09, Chapter 5]: `L^s(q)`-valued analyticity (Definition 5.3), the empirical process `ψ_n`
(Definition 5.6), its moment bound (Theorem 5.8) and its convergence in law (Theorem 5.9), whose
conclusion is the structure `EmpiricalProcessLimit`. The process keeps the book's sign,
`ψ_n = n^{-1/2} Σ (f(X_i, ·) − E f)`. Later files use `EmpiricalProcessLimit` for the process of
`a(x, u)` on a resolution, whose limit is `Ψlim` in code; chapter 6's `ξ` is `−Ψlim`.

The definitions are those of `SLTChallenge/EmpiricalProcess.lean`, word for word, and
`SLT/EmpiricalProcess.lean` proves its theorems.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal

namespace SingularLearningTheory

/-- The Borel σ-algebra on `C(X, ℝ)` ([Wat09, Definition 5.5]), which Mathlib does not provide. -/
instance instMeasurableSpaceContinuousMapReal (X : Type*) [TopologicalSpace X] :
    MeasurableSpace C(X, ℝ) := borel C(X, ℝ)

/-- The σ-algebra above is the Borel σ-algebra. -/
instance instBorelSpaceContinuousMapReal (X : Type*) [TopologicalSpace X] :
    BorelSpace C(X, ℝ) := ⟨rfl⟩

variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

/-- [Wat09, Definition 5.6, eq. (5.21)]. The empirical process of `f : X → U → ℝ` for the
sample `X₀, X₁, …` drawn from `q`, `ψ_n(u) = n^{-1/2} Σ_{i<n} (f(X_i, u) − E[f(X, u)])`, as a
real function of `u` for each sample; `EmpiricalProcessLimit` makes it a `C(U, ℝ)`-valued
random variable.

Relation to the source.
* **Translation.** `empiricalProcess q f Xs n ω` is the $\psi_n$ of [Wat09, eq. (5.21)] as a real
  function on the parameters for each sample, the pre-empirical process of [Wat09, Definition 5.4,
  eq. (5.12)]; `EmpiricalProcessLimit` makes it the $C(K)$-valued random variable of [Wat09,
  Definition 5.6]. -/
noncomputable def empiricalProcess {U : Type*} (q : Measure X) (f : X → U → ℝ) (Xs : ℕ → Ω → X)
    (n : ℕ) (ω : Ω) (u : U) : ℝ :=
  (√n)⁻¹ * ∑ i ∈ Finset.range n, (f (Xs i ω) u - ∫ x, f x u ∂q)

/-- [Wat09, Definition 5.3]. `f` is `L^s(q)`-valued real analytic on `W`: on an open set `U ⊇ W`,
`w ↦ f(·, w)` agrees with a map `U → L^s(q)` that is analytic in the Banach-space sense.

Relation to the source.
* **Restatement.** Analyticity of a map into the Banach space $L^s(q)$ is the book's absolutely
  convergent power series with coefficients in $L^s(q)$. -/
def LsValuedAnalytic {d : ℕ} (s : ℝ≥0∞) [Fact (1 ≤ s)] (q : Measure X)
    (f : X → (Fin d → ℝ) → ℝ) (W : Set (Fin d → ℝ)) : Prop :=
  ∃ U : Set (Fin d → ℝ), IsOpen U ∧ W ⊆ U ∧
    ∃ F : (Fin d → ℝ) → Lp ℝ s q, AnalyticOnNhd ℝ F U ∧
      ∀ w ∈ U, (F w : X → ℝ) =ᵐ[q] fun x ↦ f x w

/-- **The conclusion of [Wat09, Theorem 5.9]** for the empirical process `ψ_n` of `f` on a
topological space `U` (the book's compact `K`, or the disjoint union of the chart cubes of a
resolution): `ψ_n` is a random element of `C(U, ℝ)` with the Borel σ-algebra; (1) the sequence
is tight; (2) it converges in law to a random continuous function `ψ`; (3) the
finite-dimensional distributions of `ψ` are centred Gaussian with covariance
`cov(f(X, u_i), f(X, u_j))`, `X ∼ q`.

Relation to the source.
* **Interpretation.** The book treats $\psi_n$ as continuous for every sample [Wat09, Remark 5.7];
  the structure needs a continuous version only almost surely. -/
structure EmpiricalProcessLimit {Ω' : Type*} [MeasurableSpace Ω']
    {U : Type*} [TopologicalSpace U] (q : Measure X)
    (f : X → U → ℝ) (Xs : ℕ → Ω → X) (P : Measure Ω) (P' : Measure Ω')
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] where
  /-- `ψ_n` as a random continuous function: a measurable `C(U, ℝ)`-valued map agreeing with
  `empiricalProcess` almost surely. The book treats `ψ_n` as continuous for every sample
  (Remark 5.7); here continuity is needed only almost surely. -/
  Ψ : ℕ → Ω → C(U, ℝ)
  Ψ_measurable : ∀ n, Measurable (Ψ n)
  Ψ_ae_eq : ∀ n, ∀ᵐ ω ∂P, ∀ u, Ψ n ω u = empiricalProcess q f Xs n ω u
  /-- (1) `{ψ_n}` is tight on `(C(U, ℝ), 𝓑)`. -/
  tight : IsTightMeasureSet (Set.range fun n ↦ P.map (Ψ n))
  /-- (2) The limit `ψ`, a random continuous function on a probability space `Ω'`. -/
  Ψlim : Ω' → C(U, ℝ)
  tendsto : TendstoInDistribution Ψ atTop Ψlim (fun _ ↦ P) P'
  /-- (3) For any `u₁, …, u_M`, `(ψ(u₁), …, ψ(u_M))` is Gaussian … -/
  gaussian : ∀ (M : ℕ) (u : Fin M → U), IsGaussian (P'.map fun ω' j ↦ Ψlim ω' (u j))
  /-- … with mean zero … -/
  mean_zero : ∀ u, ∫ ω', Ψlim ω' u ∂P' = 0
  /-- … and covariance `Σ_{ij} = cov(f(X, u_i), f(X, u_j))`. -/
  cov : ∀ u u', cov[fun ω' ↦ Ψlim ω' u, fun ω' ↦ Ψlim ω' u'; P']
    = cov[fun x ↦ f x u, fun x ↦ f x u'; q]

end SingularLearningTheory

