import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import SLT.EmpiricalProcess
import SLT.FreeEnergy.StochasticAsymptotics

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SingularLearningTheory MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option verso.blueprint.autoDeps true

#doc (Manual) "Empirical processes (Chapter 5)" =>

Chapter 5 supplies the probabilistic vocabulary of the main theorems: convergence in law, the
function-valued analytic model, the empirical process and its limit, and the fluctuation
function $`S_\lambda` and the singular fluctuation $`\nu(\beta)`.

# Convergence in law (§5.1)

::::definition "def:5_1" (lean := "MeasureTheory.TendstoInDistribution")
%%%
paperIdentity := some { label := "[Wat09, Definition 5.1]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
A sequence of probability distributions $`\mu_n` on a metric space converges *in law* to $`\mu` if
$`\int f\,d\mu_n \to \int f\,d\mu` for every bounded continuous $`f`; random variables $`X_n`
converge in law to $`Z` if their distributions do.

The library uses Mathlib's `TendstoInDistribution` throughout, for real statistics, vectors of
them, and random continuous functions; each random variable may live on its own probability
space.

`TendstoInDistribution Xn atTop Z (fun _ ↦ P) P'` is the book's "$`X_n` converges in law to
$`Z`", with $`X_n` defined on $`(\Omega, P)` and $`Z` on $`(\Omega', P')`.
::::

# Function-valued analytic functions (§5.2)

::::definition "def:5_3" (lean := "SingularLearningTheory.LsValuedAnalytic")
%%%
paperIdentity := some { label := "[Wat09, Definition 5.3]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For $`s \ge 1` and a probability measure $`q`, a function $`f(x, w)` is *$`L^s(q)`-valued real
analytic* on $`W` if $`w \mapsto f(\cdot, w)` is given near each point by an absolutely convergent
power series with coefficients in $`L^s(q)`.

`LsValuedAnalytic s q f W`: on an open set $`U \supseteq W`, $`w \mapsto f(\cdot, w)` agrees
$`q`-almost everywhere with a map $`U \to L^s(q)` that is analytic in the Banach-space sense
(Mathlib's `AnalyticOnNhd`).

::::

# The empirical process (§5.3)

::::definition "def:5_5" (lean := "SingularLearningTheory.instMeasurableSpaceContinuousMapReal, SingularLearningTheory.instBorelSpaceContinuousMapReal")
%%%
paperIdentity := some { label := "[Wat09, Definition 5.5]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The space $`C(K, \mathbb{R})` of continuous functions carries the Borel σ-algebra of its uniform
topology, which makes a random continuous function a random variable. Mathlib does not provide
this instance; the library declares it.
::::

::::definition "def:empirical_process" (lean := "SingularLearningTheory.empiricalProcess")
%%%
paperIdentity := some { label := "[Wat09, Definition 5.6, eq. (5.21)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The *empirical process* of $`f(x, u)` for the sample $`X_1, X_2, \dots` drawn from $`q` is
$$`\psi_n(u) = \frac{1}{\sqrt n} \sum_{i=1}^{n} \bigl(f(X_i, u) - \mathbb{E}_q[f(X, u)]\bigr).`

`empiricalProcess q f Xs n ω u` is this function of $`u`, for each sample; the limit theorems
treat it as a random continuous function through `EmpiricalProcessLimit`
({bpref "def:epl"}[]). It has the centring $`f - \mathbb{E}f` of eq. (6.11); the processes of
Chapter 6 in the sign of eq. (6.10) are its negatives ({ref "conv-sign"}[the sign of ξ]).

::::

::::definition "def:epl" (lean := "SingularLearningTheory.EmpiricalProcessLimit")
%%%
paperIdentity := some { label := "[Wat09, Theorem 5.9 (the conclusion)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
`EmpiricalProcessLimit q f Xs P P'` packages the conclusion of Theorem 5.9 for the empirical
process $`\psi_n` of $`f : X \to U \to \mathbb{R}` on a topological space $`U`: a measurable
$`C(U, \mathbb{R})`-valued $`\Psi_n` equal to $`\psi_n` almost surely (`Ψ`, `Ψ_ae_eq`); (1) the
laws of the $`\Psi_n` are tight (`tight`); (2) $`\Psi_n` converges in law to a random continuous
function $`\psi` on $`(\Omega', P')` (`Ψlim`, `tendsto`); (3) the finite-dimensional distributions
of $`\psi` are centred Gaussian with covariance $`\operatorname{cov}(f(X, u), f(X, u'))`,
$`X \sim q` (`gaussian`, `mean_zero`, `cov`).

::::

::::theorem "thm:5_8" (lean := "SingularLearningTheory.exists_lintegral_iSup_empiricalProcess_pow_le")
%%%
paperIdentity := some { label := "[Wat09, Theorem 5.8]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For $`W` compact, $`s \ge 2` an even integer and $`f` $`L^s(q)`-valued real analytic on a
neighbourhood of $`W` ({bpref "def:5_3"}[]), the empirical process of an i.i.d. sample satisfies
$`\mathbb{E}[\sup_{w \in W} |\psi_n(w)|^s] \le C` with $`C` independent of $`n`.

::::

::::theorem "thm:5_9" (lean := "SingularLearningTheory.convergence_of_empirical_process")
%%%
paperIdentity := some { label := "[Wat09, Theorem 5.9]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For $`W` compact, $`s \ge 2` an even integer and $`f` $`L^s(q)`-valued real analytic on a
neighbourhood of $`W`, the empirical process $`\psi_n` on $`W` of an i.i.d. sample is tight and
converges in law to a centred Gaussian process with the covariance of $`f`.

`convergence_of_empirical_process` asserts `EmpiricalProcessLimit` ({bpref "def:epl"}[]) on
$`C(W, \mathbb{R})`, on some probability space $`(\Omega', P')`.

::::

::::theorem "thm:5_10"
%%%
paperIdentity := some { label := "[Wat09, Theorem 5.10]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
If $`f` is $`L^{s+2}(q)`-valued real analytic, for $`s` a positive even integer, then
$`\lim_n \mathbb{E}[\sup_{w \in K} |\psi_n(w)|^s] = \mathbb{E}[\sup_{w \in K} |\psi(w)|^s]`.

:::unformalised (missing := statement)
The convergence of the moments of the supremum is not stated. With the uniform bound of
{bpref "thm:5_8"}[Theorem 5.8] at index $`s + 2` and the convergence in law of
{bpref "thm:5_9"}[Theorem 5.9], it follows by uniform integrability.
:::
::::

# Fluctuation of Gaussian processes (§5.4)

::::definition "def:5_8" (lean := "SingularLearningTheory.frozenInner")
%%%
paperIdentity := some { label := "[Wat09, Definition 5.8]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The *fluctuation function* of inverse temperature $`\beta` and $`\lambda > 0` is
$$`S_\lambda(a) = \int_0^\infty t^{\lambda - 1} e^{-\beta t + \beta a \sqrt t}\,dt .`

`frozenInner lam β a` is this integral; the library uses it inside its proofs of §6.2 and §6.3.

:::translation
`frozenInner lam β a` is the book's fluctuation function $`S_\lambda(a)` (Definition 5.8).
:::
::::

::::definition "def:5_9"
%%%
paperIdentity := some { label := "[Wat09, Definition 5.9]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For a measure $`\mu` on $`\mathcal{M}` and a Gaussian process $`\xi` on $`\mathcal{M}` with
$`\rho(u, u) = 2`, the *singular fluctuation* is
$$`\nu(\beta) = \frac{1}{2\beta}\, \mathbb{E}\Bigl[\frac{1}{Z(\xi)} \int_{\mathcal{M}} \xi(u)\,
  S'_\lambda(\xi(u))\,d\mu(u)\Bigr], \qquad Z(\xi) = \int_{\mathcal{M}} S_\lambda(\xi(u))\,d\mu(u).`

:::outOfScope
The definition assumes $`\rho(u, u) = 2`, the variance that Theorem 6.3 derives from
realizability; under relatively finite variance it fails in general ({bpref "thm:6_3"}[]). The
library defines $`\nu` instead through the limit of the functional variance,
$`\mathbb{E}[V] \to 2\nu/\beta` ({bpref "thm:6_10"}[Theorem 6.10]).
:::
::::

::::theorem "thm:5_11"
%%%
paperIdentity := some { label := "[Wat09, Theorem 5.11, eqs. (5.23), (5.24)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For the singular fluctuation of Definition 5.9,
$`\mathbb{E}\bigl[\int \mu(du)\, S''_\lambda(\xi(u)) / Z(\xi)\bigr] = \lambda\beta + \beta^2\nu(\beta)`
and
$`\frac12 \mathbb{E}\,\mathbb{E}_X\bigl[\bigl(\int \mu(du)\, a(X, u) S'_\lambda(\xi(u)) / Z(\xi)\bigr)^2\bigr]
= \lambda\beta + (\beta^2 - \beta)\nu(\beta)`.

:::outOfScope
Stated for the singular fluctuation of {bpref "def:5_9"}[Definition 5.9], which assumes
realizability.
:::
::::
