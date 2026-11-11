import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import SLT.StandardForm
import SLT.Resolution
import SLT.SingularIntegrals.Zeta
import SLT.FreeEnergy
import SLT.FreeEnergy.Main
import SLT.BayesGibbs
import SLT.MaximumLikelihood

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SingularLearningTheory MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option verso.blueprint.autoDeps true
-- Dependency inference for the declarations of Theorem 6.2 walks their unregistered helpers
-- through Mathlib's measure theory and exceeds the default 200000 heartbeats.
set_option maxHeartbeats 400000

#doc (Manual) "Singular learning theory (Chapter 6)" =>

Chapter 6 is the core of the book and of the library. Its theorems are stated for a true
distribution `q`, a model `p` on a parameter set `W ⊆ ℝ^d`, a reference parameter `w₀`, a prior
density `φ` and an i.i.d. sample `Xs` from `q` ({bpref "def:setup"}[], {bpref "def:sample"}[]),
under hypotheses that most of them share:

- `hA : StandingAssumptions s q p W w₀` ({bpref "def:6_1"}[]): $`W` compact, the model jointly
  measurable and positive on $`W`, $`w_0 \in W`, relatively finite variance at $`w_0`
  ({bpref "def:rfv"}[]), Fundamental Condition (I) with index $`s`, and the continuity of
  $`f(x, \cdot)` on $`W` for $`q`-almost every $`x`. The index is $`s = 2` for the free energy
  formula, $`s = 4` for its expectation and for §6.4, and $`s = 6` for §6.3;
- `II : FundamentalConditionII φ W` ({bpref "def:6_3"}[]) and
  `hZ : ZeroSetConditions (excessLoss q p w₀) φ W` ({bpref "def:zero_set"}[]), for the theorems
  with a prior.

Every theorem is stated under relatively finite variance in place of realizability, with the
losses measured from $`w_0`; how this compares with the book is explained in
{ref "conv-rfv"}[relatively finite variance], and the annotations shared by the theorems are at the
hypotheses they concern: `StandingAssumptions`, `RelativelyFiniteVariance` and
`ZeroSetConditions`. Where a
theorem needs the resolution, it either takes one (an `SLTResolution`, a chart family and a
partition of unity, {bpref "thm:6_5"}[]) or obtains one inside the proof from
{bpref "thm:2_8"}[Theorem 2.8], and the pair $`(\lambda, m)` is the singularity type of $`K`
({bpref "def:2_7"}[]).

Items the library does not state carry an *Unformalised* box at their node, and items that
assume realizability in a way relatively finite variance does not support an *Out of scope* box.

# Standard form of the likelihood ratio function (§6.1)

::::definition "def:6_1" (lean := "SingularLearningTheory.FundamentalConditionI, SingularLearningTheory.StandingAssumptions")
%%%
paperIdentity := some { label := "[Wat09, Fundamental Condition (I), Definition 6.1]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Fundamental Condition (I) with index $`s`: the set of all parameters $`W` is compact,
$`W_0 = \{w \in W : K(w) = 0\}` is not empty, and there is an open $`W^{(C)} \supseteq W` on which
(1-a) $`p(x \mid w)` is analytic in $`w`, (1-b) $`w \mapsto f(\cdot, w)` is an $`L^s(q)`-valued
analytic function ({bpref "def:5_3"}[Definition 5.3]), (1-c) there is $`M(x)` with
$`|f(x, w)| \le M(x)` and $`\int M^s q\,dx < \infty`; and (2) $`\int M(x)^2 Q(x)\,dx < \infty`
for $`Q(x) = \sup_w p(x \mid w)`.

`FundamentalConditionI s q f K W` keeps items (1-a), (1-b) in real form: $`2 \le s`,
$`K(w) = \int f(x, w)\,q(dx)` for every $`w`, and $`f` is $`L^s(q)`-valued real analytic on an
open neighbourhood of $`W` (`ls_analytic`). The rest of the book's condition, and what replaces
realizability, are fields of `StandingAssumptions s q p W w₀`: $`W` compact (`compact`),
$`w_0 \in W` (`mem`), $`p` jointly measurable (`measurable`), $`p(x \mid w) > 0` for every
$`w \in W` and $`q`-almost every $`x` (`pos`), relatively finite variance at $`w_0` (`rfv`),
Fundamental Condition (I) for the log density ratio and the excess loss measured from $`w_0`
(`conditionI`), and continuity of $`f(x, \cdot)` on $`W` for $`q`-almost every $`x`
(`continuousOn`).

::::

::::theorem "thm:essential_uniqueness" (lean := "SingularLearningTheory.StandingAssumptions.isMinOn_excessLoss, SingularLearningTheory.StandingAssumptions.isMinOn_expectedNegativeLogLikelihood, SingularLearningTheory.StandingAssumptions.ae_eq_of_excessLoss_eq_zero, SingularLearningTheory.StandingAssumptions.of_excessLoss_eq_zero, SingularLearningTheory.StandingAssumptions.analyticOnNhd_excessLoss")
%%%
paperIdentity := some { label := "[Wat18, Definition 6, Lemma 3]", href := "https://doi.org/10.1201/9781315373010" }
%%%
Under the standing assumptions ({bpref "def:6_1"}[]):

- the reference parameter minimises the excess loss on $`W`: $`K(w_0) = 0 \le K(w)`
  (`isMinOn_excessLoss`), and the average log loss $`L` when $`\log p(\cdot \mid w_0)` is
  integrable (`isMinOn_expectedNegativeLogLikelihood`);
- every other minimiser $`w_0'` of $`K` in $`W` has the same model up to a $`q`-null set
  (`ae_eq_of_excessLoss_eq_zero`, essential uniqueness, {cite Wat18}[Definition 6 and Lemma 3]), gives
  the same $`K` and satisfies the standing assumptions itself (`of_excessLoss_eq_zero`); so
  nothing depends on which minimiser is the reference parameter, and relatively finite variance
  holds at every minimiser, as {cite Wat18}[Definition 7] requires;
- $`K` is real analytic on an open neighbourhood of $`W` (`analyticOnNhd_excessLoss`).

These are what singular learning theory usually assumes of the true parameter, derived here from
the standing assumptions.
::::

::::definition "def:6_3" (lean := "SingularLearningTheory.FundamentalConditionII, SingularLearningTheory.Semianalytic")
%%%
paperIdentity := some { label := "[Wat09, Fundamental Condition (II), Definition 6.3]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Fundamental Condition (II): the parameter set $`W = \{ \pi_1 \ge 0, \dots, \pi_k \ge 0 \}`
(compact, by Fundamental Condition (I)) has real analytic $`\pi_j`, and the prior is
$`\varphi_1 \varphi_2` with $`\varphi_1 > 0` of class $`C^\infty` and $`\varphi_2 \ge 0` real
analytic.

`FundamentalConditionII φ W`: $`W` is semianalytic (`Semianalytic W`: inside an open
neighbourhood $`U` of $`W`, $`W` is cut out by finitely many inequalities $`H_i \ge 0` with $`H_i`
real analytic on $`U`), and on an open neighbourhood of $`W` the prior factors as
$`\varphi = \varphi_1 \varphi_2` with $`\varphi_1 > 0` smooth and $`\varphi_2` real analytic and
nonnegative on $`W`. The compactness of $`W` is assumed separately.

::::

::::definition "def:zero_set" (lean := "SingularLearningTheory.ZeroSetConditions")
%%%
paperIdentity := some { label := "[Wat09, Theorem 7.1 (the true parameter)]; [Wat09, Theorem 2.3 (non-constancy)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
`ZeroSetConditions K φ W`: at every zero of $`K` in $`W`, neither $`K` nor $`\varphi` is
identically zero on a neighbourhood (`loss_germ`, `prior_germ`), and every sublevel set
$`\{w \in W : K(w) < \varepsilon\}` has positive prior mass (`sublevel_mass`).

::::

::::theorem "thm:6_1" (lean := "SingularLearningTheory.exists_resolvedLogDensityRatio, SingularLearningTheory.ResolvedLogDensityRatio")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.1]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Condition (I), in the local coordinates of the resolution there is an
$`L^s(q)`-valued real analytic $`a(x, u)` with $`f(x, g(u)) = a(x, u)\, u^k` (6.5) and
$`\mathbb{E}_X[a(X, u)] = u^k` (6.6).

`ResolvedLogDensityRatio s F q f` is the conclusion on a chart family `F` of a resolution
({bpref "def:chart_family"}[]): for every piece $`\alpha` a coefficient `a α x u`, measurable in
$`x`, continuous in $`u` on the cube, $`L^s(q)`-valued real analytic on a neighbourhood of the
cube, with $`f(x, g_\alpha(u)) = u^{k_\alpha}\, a_\alpha(x, u)` for $`q`-almost every $`x`
simultaneously for every $`u` (`factor`) and $`\int a_\alpha(x, u)\,q(dx) = u^{k_\alpha}`
(`mean`). `exists_resolvedLogDensityRatio`: for $`W` closed, Fundamental Condition (I) at any
index $`s`, relatively finite variance at $`w_0` and $`f(x, \cdot)` continuous on $`W` for
$`q`-almost every $`x`, every chart family of every resolution of $`K` has resolved coefficients.

::::

::::theorem "mainthm:6_1" (lean := "SingularLearningTheory.empiricalExcessLoss_standardForm")
%%%
paperIdentity := some { label := "[Wat09, Main Theorem 6.1, eqs. (6.10), (6.11)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Condition (I) the log likelihood ratio function has the *standard form*
$$`K_n(g_\alpha(u)) = u^{2k_\alpha} - \frac{1}{\sqrt n}\, u^{k_\alpha}\, \xi_n(u), \qquad
  \xi_n(u) = \frac{1}{\sqrt n} \sum_{i=1}^{n} \bigl(u^{k_\alpha} - a_\alpha(X_i, u)\bigr)`
in every local coordinate of the resolution of Theorem 6.1.

`empiricalExcessLoss_standardForm`: for resolved coefficients `L` on the pieces of a chart family
({bpref "thm:6_1"}[]) and an i.i.d. sample, almost surely, for every $`n \ge 1`, every piece
$`\alpha` and every $`u` in its cube, `empiricalExcessLoss p w₀ Xs n ω (α.map u)` equals
$`(u^{k_\alpha})^2 - n^{-1/2} u^{k_\alpha} \xi_n(u)`, with $`\xi_n` the negative of
`empiricalProcess` of the coefficients ({ref "conv-sign"}[the sign of ξ]).

:::restatement
The book's Main Theorem 6.1 is the existence of the resolution and of the coefficients,
`exists_resolvedLogDensityRatio` ({bpref "thm:6_1"}[Theorem 6.1]), together with the standard form
(6.10), which `empiricalExcessLoss_standardForm` states for any such coefficients.
:::

:::strengthening
The identity holds almost surely simultaneously for every $`n`, every piece and every point of its
cube; the book's (6.5) is an identity in $`L^s(q)` at each point.
:::
::::

::::theorem "mf:I" (lean := "SingularLearningTheory.empiricalExcessLoss_standardForm, SingularLearningTheory.exists_empiricalProcessLimit")
%%%
paperIdentity := some { label := "[Wat09, Main Formula I, eqs. (1.19)–(1.21)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The standard form of {bpref "mainthm:6_1"}[Main Theorem 6.1] holds with a single empirical process
$`\xi_n` on the disjoint union $`\mathcal{M}` of the charts, $`\xi_n` converges in law to a
Gaussian process $`\xi` on $`\mathcal{M}`, and the prior pulls back to
$`\varphi^*_\alpha(u)\, u^{h_\alpha}` on the charts (eq. (1.21)).

The standard form is `empiricalExcessLoss_standardForm` and the convergence in law of $`\xi_n`
is `exists_empiricalProcessLimit` ({bpref "thm:6_2"}[]), on the disjoint union of the pieces of a
chart family. The pull-back of the prior (1.20) is the field `density_eq` of each chart of the
resolution ({bpref "def:sltresolution"}[]); its integrated form (1.21) is not stated
({bpref "thm:6_5"}[Theorem 6.5]).
::::

::::theorem "thm:6_2" (lean := "SingularLearningTheory.exists_empiricalProcessLimit")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.2]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(1) Under Fundamental Condition (I) with $`s = 2`, the empirical processes $`\psi_n(w)` on
$`\{K > \varepsilon\}` and $`\xi_n(u)` on $`\mathcal{M}` converge in law to Gaussian processes
$`\psi(w)` and $`\xi(u)`. (2) With $`s = 4`,
$`\lim_n \mathbb{E}[\sup_{K > \varepsilon} |\psi_n|^{s-2}] = \mathbb{E}[\sup |\psi|^{s-2}] < \infty`
and $`\lim_n \mathbb{E}[\sup_{\mathcal{M}} |\xi_n|^{s-2}]
= \mathbb{E}[\sup_{\mathcal{M}} |\xi|^{s-2}] < \infty`.

The chart process, in the library. `exists_empiricalProcessLimit`: for resolved coefficients $`a`
on a chart family ({bpref "thm:6_1"}[]) at index $`s \ge 2` and an i.i.d. sample, the centred
empirical process $`\Psi_n(u) = n^{-1/2} \sum_i (a(X_i, u) - \mathbb{E}[a(X, u)])` on the disjoint
union of the pieces satisfies `EmpiricalProcessLimit` ({bpref "def:epl"}[]): it is tight and
converges in law to a centred Gaussian process $`\Psi` with the covariance of $`a`. The book's
$`\xi_n` of (6.10) is $`-\Psi_n` ({ref "conv-sign"}[the sign of ξ]).

The relative process $`\psi_n` and part (2) are not stated. The relative process is an instance
of {bpref "thm:5_9"}[Theorem 5.9] for $`(K(w) - f(x, w))/\sqrt{K(w)}` on $`\{K \ge \varepsilon\}
\cap W`, and part (2) follows from the convergence in law with uniform integrability
({bpref "thm:5_10"}[Theorem 5.10]).

::::

::::theorem "thm:6_3"
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.3]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Condition (I) with $`s = 4`, if $`K(g(u)) = 0` then
$`\mathbb{E}_X[a(X, u)^2] = \mathbb{E}[|\xi_n(u)|^2] = \mathbb{E}[|\xi(u)|^2] = 2`.

:::outOfScope
The proof expands $`\mathbb{E}_q[e^{-f(X, w)}] = 1`, which holds when $`q = p(\cdot \mid w_0)`. Under
relatively finite variance $`\mathbb{E}_q[p(X \mid w)/p(X \mid w_0)]` need not be $`1`, and the
variance of the coefficients on the zero set is not $`2` in general.
:::
::::

# Evidence and stochastic complexity (§6.2)

::::theorem "thm:6_4"
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.4]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For every $`n`,
$`\mathbb{E}[F_n^0] \le -\log \int \exp(-n\beta K(w))\,\varphi(w)\,dw`.

:::unformalised (missing := statement)
Not stated. It follows from Jensen's inequality and $`\mathbb{E}[K_n(w)] = K(w)`, for
`normalizedEvidence` and `laplaceIntegral` ({bpref "def:volume"}[]).
:::
::::

::::theorem "thm:6_5" (lean := "SingularLearningTheory.SLTResolution.exists_chartFamily, SingularLearningTheory.SLTResolution.ChartFamily.exists_partitionOfUnity")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.5]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(Partition of the parameter space). Assume Fundamental Conditions (I) and (II) and let
$`\varepsilon > 0` be a constant. Resolving $`K(\varepsilon - K)\varphi_2 \prod_j \pi_j` gives a
real analytic manifold and a proper real analytic map $`g` onto $`W_\varepsilon^{(R)}` such that (1)
$`\mathcal{M} = g^{-1}(W_\varepsilon)`, $`W_\varepsilon = \{w \in W : K(w) \le \varepsilon\}`, is
covered by finitely many local coordinates $`\mathcal{M}_\alpha = [0, b]^d`; (2) $`K(g(u)) = u^{2k}`
on each $`\mathcal{M}_\alpha`; (3) $`\varphi(g(u))\,|g'(u)| = \phi(u)\, u^h` with $`\phi` of class
$`C^\infty` and $`\phi > c > 0` on $`[0, b]^d`; (4) there is a partition of unity
$`\sigma_\alpha \ge 0`, $`\sum_\alpha \sigma_\alpha = 1`, $`\sigma_\alpha > 0` on $`[0, b)^d`,
$`\operatorname{supp} \sigma_\alpha = [0, b]^d`, with $`\int_W H\varphi\,dw = \sum_\alpha
\int_{\mathcal{M}_\alpha} H(g(u))\,\varphi^*(u)\,u^h\,du` for $`\varphi^* = \sigma_\alpha \phi`, and
a constant $`C_1 > 0` with $`C_1 \sum_\alpha \int_{\mathcal{M}_\alpha} H(g)\,\phi\,u^h \le
\int_{W_\varepsilon} H\varphi \le \sum_\alpha \int_{\mathcal{M}_\alpha} H(g)\,\phi\,u^h` (6.14).

The library starts from a resolution `R` of $`K` with prior $`\varphi` on $`W`
({bpref "thm:2_8"}[Theorem 2.8]). `SLTResolution.exists_chartFamily`: for $`W` compact and $`K`
continuous and nonnegative on $`W`, `R` has a chart family ({bpref "def:chart_family"}[]):
finitely many charts whose open cubes cover the part of the resolved parameter set where
$`K \le \delta`, for some $`\delta > 0`; its pieces are the $`\mathcal{M}_\alpha` of (1), with
(2) and (3) from the charts ({bpref "def:sltresolution"}[]).
`SLTResolution.ChartFamily.exists_partitionOfUnity`: every chart family has a smooth partition of
unity on the resolving manifold, subordinate to the open cubes and summing to $`1` on the
sublevel it covers, the partition of unity of (4).

::::

::::definition "def:6_4" (lean := "SingularLearningTheory.SLTResolution.rlct, SingularLearningTheory.SLTResolution.mult, SingularLearningTheory.SLTResolution.ChartFamily.Piece.IsEssential, SingularLearningTheory.SLTResolution.isSingularityType")
%%%
paperIdentity := some { label := "[Wat09, Definition 6.4, eqs. (6.16), (6.17)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The zeta function of the pair $`(K, \varphi)` is $`\zeta(z) = \int K(w)^z \varphi(w)\,dw`; its
largest pole is $`-\lambda` and $`m` is the order of that pole. On the local coordinates of
Theorem 6.5,
$$`\lambda = \min_\alpha \min_{k_{\alpha i} > 0} \frac{h_{\alpha i} + 1}{2 k_{\alpha i}}, \qquad
  m = \max_{\alpha : \lambda_\alpha = \lambda} \#\{ i : \tfrac{h_{\alpha i} + 1}{2 k_{\alpha i}} = \lambda \},`
and the coordinates attaining both are *essential*.

`SLTResolution.rlct` and `SLTResolution.mult` are (6.16) and (6.17) read off a resolution: the
minimum of the chart learning coefficients over all charts centred at points of the resolved
parameter set over zeros of $`K`, and the largest multiplicity among the charts attaining it. A
piece is essential (`Piece.IsEssential`) when its chart attains both.
`SLTResolution.isSingularityType`: for $`W` compact, $`K` continuous and nonnegative on $`W`,
$`\varphi` continuous and nonnegative on $`W`, and every sublevel $`\{K < \varepsilon\}` of
positive prior mass, the pair read off any resolution is the singularity type of $`K` and
$`\varphi` ({bpref "def:2_7"}[]).

::::

::::theorem "thm:6_6" (lean := "SingularLearningTheory.zetaFunction_meromorphic_continuation, SingularLearningTheory.zetaFunction_continuation_unique")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.6]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The zeta function $`\zeta(z) = \int K^z \varphi\,dw` is holomorphic on $`\operatorname{Re} z > 0`
and continues meromorphically to $`\mathbb{C}`; its poles are real, negative and rational; its
largest pole is $`-\lambda` with order $`m`, for the pair of {bpref "def:6_4"}[Definition 6.4].

`zetaFunction_meromorphic_continuation`: for $`W` compact, $`K` real analytic near $`W` and
nonnegative on it, Fundamental Condition (II) ({bpref "def:6_3"}[]) and the zero-set conditions
({bpref "def:zero_set"}[]), `zetaFunction K φ W` is holomorphic on $`\operatorname{Re} z > 0`,
and there are a meromorphic continuation $`\zeta_{\mathrm{ext}}` to $`\mathbb{C}` and a pair
$`(\lambda, m)` with $`\lambda > 0` rational and $`m \ge 1`, the singularity type of $`K` and
$`\varphi` ({bpref "def:2_7"}[]), such that every pole of $`\zeta_{\mathrm{ext}}` is a negative
rational, $`\zeta_{\mathrm{ext}}` is holomorphic on $`\operatorname{Re} z > -\lambda`, and its
order at $`-\lambda` is $`-m`. `zetaFunction_continuation_unique`: two meromorphic continuations
agree on a punctured neighbourhood of every point.

::::

::::theorem "thm:6_7" (lean := "SingularLearningTheory.tendstoInDistribution_normalizedEvidence, SingularLearningTheory.SLTResolution.ChartFamily.limitFunctional")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.7]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(Convergence in law of evidence). Under Fundamental Conditions (I) and (II) with $`s = 2`, with
$`(\lambda, m)` the learning coefficient and its order,
$$`\frac{n^\lambda Z_n^0}{(\log n)^{m-1}} \to \sum_{\alpha^*} \gamma_b \int_0^\infty dt
  \int_{M_{\alpha^*}} t^{\lambda-1} e^{-\beta t + \sqrt t \beta \xi_0(y)} \varphi^*_0(y)\,dy`
in law, the sum over the essential charts.

`ChartFamily.limitFunctional β ρ χ` is the right-hand side as a function $`Y(\chi)` of a
continuous $`\chi` on the pieces of a chart family `F`: the sum over the essential pieces of
$`\gamma_b` times the integral over $`t > 0` and the critical face of
$`t^{\lambda - 1} \prod_j v_j^{h_j - 2k_j\lambda} e^{-\beta t + \beta \sqrt t\, \chi}` times the
partition of unity `ρ` and the unit of the prior density.
`tendstoInDistribution_normalizedEvidence`: for $`W` compact, $`w_0 \in W`, relatively finite
variance, Fundamental Conditions (I) with $`s = 2` and (II), $`f(x, \cdot)` continuous on $`W`
for $`q`-almost every $`x`, a resolution `R`, a chart family `F` and a subordinate partition of
unity `ρ`, there are resolved coefficients ({bpref "thm:6_1"}[]) such that for every
$`\beta > 0` and every i.i.d. sample their empirical process has a limit $`\Psi`
({bpref "thm:6_2"}[]) and $`n^\lambda (\log n)^{-(m-1)} Z_n^0 \to Y(\xi)` in law, with
$`\xi = -\Psi` and $`(\lambda, m) = ` `(R.rlct, R.mult)` ({bpref "def:6_4"}[]).

::::

::::theorem "mainthm:6_2" (lean := "SingularLearningTheory.NondegenerateResolutionAtlas.free_energy_formula, SingularLearningTheory.NondegenerateResolutionAtlas.tendsto_integral_Rn, SingularLearningTheory.NondegenerateResolutionAtlas.eventually_integral_normalizedFreeEnergy_eq, SingularLearningTheory.NondegenerateResolutionAtlas.limitFunctional_pos")
%%%
paperIdentity := some { label := "[Wat09, Main Theorem 6.2]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(Convergence of stochastic complexity.) (1) Under Fundamental Conditions (I) and (II) with
$`s = 2`, $`F_n^0 - \lambda \log n + (m - 1) \log\log n \to -\log Y(\xi)` in law, where
$`Y(\xi)` is the limit of {bpref "thm:6_7"}[Theorem 6.7]. (2) With $`s = 4`,
$`\mathbb{E}[F_n^0] - \lambda \log n + (m - 1) \log\log n \to -\mathbb{E}[\log Y(\xi)]`.

The library proves both for its internal resolution atlas `R` (a `NondegenerateResolutionAtlas`)
and the random inputs `I` built on it, the objects from which the proofs of the free
energy formula ({bpref "cor:6_1"}[Corollary 6.1]) start. `free_energy_formula` is (1), for the
remainder `I.Rn` $`= F_n^0 - \lambda \log n + (m - 1) \log\log n` ({bpref "def:FR"}[]);
`limitFunctional_pos` gives $`Y > 0`. `tendsto_integral_Rn` with
`eventually_integral_normalizedFreeEnergy_eq` is (2).

:::restatement
Stated for the library's resolution atlas `R` and its empirical process input `I` rather than for
a resolution, a chart family and a partition of unity: `I.Rn` is
$`F_n^0 - \lambda \log n + (m - 1) \log\log n` (`normalizedFreeEnergy_eq`) and
`R.limitFunctional β` is the limit functional $`Y` of Theorem 6.7, whose $`-\log` is the limit.
:::

:::meta
`hLip`, the Lipschitz continuity of the weights of the essential charts, is a hypothesis of the
library's atlas that the statements of Theorem 6.7 and Corollary 6.1 discharge.
:::
::::

::::theorem "mf:II" (lean := "SingularLearningTheory.free_energy_formula")
%%%
paperIdentity := some { label := "[Wat09, Main Formula II]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
$`F_n^0 = \lambda \log n - (m - 1) \log\log n + F^R(\xi) + o_p(1)`, hence
$`F_n = n\beta S_n + \lambda \log n - (m - 1) \log\log n + F^R(\xi) + o_p(1)`, for $`(-\lambda, m)`
the largest pole of the zeta function and its order, a random variable $`F^R(\xi)` and the
empirical entropy $`S_n`.

The library's form is the free energy formula of {bpref "cor:6_1"}[Corollary 6.1 (1)]:
$`F_n = n\beta L_n(w_0) + \lambda \log n - (m - 1) \log\log n + R_n` with $`R_n` convergent in
law. The first display, with the limit of the remainder named as $`-\log Y(\xi)`, is
{bpref "mainthm:6_2"}[Main Theorem 6.2].

::::

::::theorem "cor:6_1" (lean := "SingularLearningTheory.free_energy_formula, SingularLearningTheory.free_energy_formula_expectation")
%%%
paperIdentity := some { label := "[Wat09, Corollary 6.1]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(1) Under Fundamental Conditions (I) and (II) with $`s = 2`,
$`F_n = n\beta S_n + \lambda \log n - (m - 1) \log\log n + F^R_n`, where $`F^R_n` converges in law;
(2) with $`s = 4`, $`\mathbb{E}[F_n] = n\beta S + \lambda \log n - (m - 1) \log\log n +
\mathbb{E}[F^R_n]`, where $`\mathbb{E}[F^R_n]` converges.

`free_energy_formula`: under the standing assumptions with $`s = 2`, Fundamental Condition (II)
and the zero-set conditions, there are $`\lambda > 0` and $`m \ge 1`, the singularity type of
$`K` and $`\varphi` ({bpref "def:2_7"}[]), such that for every $`\beta > 0` and every i.i.d.
sample there is $`R_n` with, almost surely for every $`n \ge 2`,
$$`F_n = n\beta L_n(w_0) + \lambda \log n - (m - 1) \log\log n + R_n,`
and $`R_n` converges in law. `free_energy_formula_expectation`: with $`s = 4` and
$`\log p(\cdot \mid w_0)` integrable, moreover
$`\mathbb{E}[F_n] = n\beta L + \lambda \log n - (m - 1) \log\log n + \mathbb{E}[R_n]` for all
large $`n`, with $`L = L(w_0)`, and $`\mathbb{E}[R_n]` converges.

::::

::::definition "def:FR" (lean := "SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.normalizedFreeEnergy, SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.Rn, SingularLearningTheory.ResolutionAtlas.EmpiricalProcessInput.normalizedFreeEnergy_eq")
%%%
paperIdentity := some { label := "[Wat09, Main Formula II, Corollary 6.1]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The normalized stochastic complexity $`F_n^0 = -\log Z_n^0` and the remainder
$`F^R_n = F_n^0 - \lambda \log n + (m - 1) \log\log n`.

In the library, for its internal resolution atlas, `normalizedFreeEnergy` is $`F_n^0` and `Rn` is
$`F^R_n`, written as $`-\log\bigl(n^\lambda Z_n^0 / (\log n)^{m-1}\bigr)`;
`normalizedFreeEnergy_eq` is the identity between them for $`n \ge 2` wherever $`Z_n^0 > 0`. The
statement of {bpref "cor:6_1"}[Corollary 6.1] asserts the existence of such a remainder.
::::

# Bayes and Gibbs estimation (§6.3)

::::definition "def:6_5" (lean := "SingularLearningTheory.posteriorMeasure, SingularLearningTheory.bayesGeneralizationError, SingularLearningTheory.bayesTrainingError, SingularLearningTheory.gibbsGeneralizationError, SingularLearningTheory.gibbsTrainingError")
%%%
paperIdentity := some { label := "[Wat09, Definition 6.5]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The Bayes and Gibbs generalization and training errors, relative to the log density ratio:
$`B_g = -\mathbb{E}_X[\log \mathbb{E}_w[e^{-f(X, w)}]]`,
$`B_t = -\frac1n \sum_i \log \mathbb{E}_w[e^{-f(X_i, w)}]`, $`G_g = \mathbb{E}_w[K(w)]` and
$`G_t = \mathbb{E}_w[K_n(w)]`, with $`\mathbb{E}_w` the expectation over the tempered posterior.

`bayesGeneralizationError`, `bayesTrainingError`, `gibbsGeneralizationError` and
`gibbsTrainingError` are these, with $`f`, $`K`, $`K_n` measured from $`w_0`
({bpref "def:1_1"}[]) and $`\mathbb{E}_w` the expectation over `posteriorMeasure`, the tempered
posterior $`e^{-n\beta K_n(w)} \varphi(w)\,dw / Z_n^0` on $`W` ({bpref "def:evidence"}[]).

::::

::::definition "def:6_6" (lean := "SingularLearningTheory.functionalVariance")
%%%
paperIdentity := some { label := "[Wat09, Definition 6.6, eq. (6.24)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The *functional variance* $`V = \sum_{i=1}^{n} \bigl( \mathbb{E}_w[f(X_i, w)^2] - \mathbb{E}_w[f(X_i, w)]^2 \bigr)`,
the expectations over the posterior.

::::

::::definition "def:6_8"
%%%
paperIdentity := some { label := "[Wat09, Definition 6.8]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The expectation over the essential local coordinates for a given field $`\xi`: on each essential
chart $`\alpha^*` write $`u = (x, y)` with $`x` the coordinates attaining $`\lambda`, and
integrate against $`t^{\lambda - 1} e^{-\beta t + \beta\sqrt t\, \xi_0(y)}\, y^\mu\, \varphi^*_0(y)`
on $`(0, \infty) \times [0, b]^{d - m}`, normalized.

:::unformalised (missing := statement)
Not defined. It is a device of the book's proofs in §6.3; the limits of the library's Theorems
6.8–6.10 are stated without it.
:::
::::

::::definition "def:6_9"
%%%
paperIdentity := some { label := "[Wat09, Definition 6.9, eqs. (6.44)–(6.47)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The explicit representation of the Bayes quartet: functionals $`B_g^*(\xi)`, $`B_t^*(\xi)`,
$`G_g^*(\xi)`, $`G_t^*(\xi)` of a field $`\xi`, defined through the expectation of
{bpref "def:6_8"}[Definition 6.8].

:::unformalised (missing := statement)
Not defined. The library's {bpref "thm:6_8"}[Theorem 6.8] states the limits of the scaled errors
existentially, as the book's Theorem 6.8 (1) does.
:::
::::

::::theorem "thm:6_8" (lean := "SingularLearningTheory.bayes_gibbs_convergence")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.8]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Conditions (I) and (II) with $`s = 6`: (1) there are random variables
$`B_g^*, B_t^*, G_g^*, G_t^*` with $`nB_g \to B_g^*`, $`nB_t \to B_t^*`, $`nG_g \to G_g^*`,
$`nG_t \to G_t^*` in law; (2) $`n(B_g - B_t - G_g + G_t) \to 0` in probability; (3)
$`\mathbb{E}[nB_g] \to \mathbb{E}[B_g^*]`, and likewise for the other three.

`bayes_gibbs_convergence`: under the standing assumptions with $`s = 6`, Fundamental Condition
(II) and the zero-set conditions, for every $`\beta > 0` and every i.i.d. sample, there are limits
$`B_g^*, B_t^*, G_g^*, G_t^*` on some probability space such that
$`(nB_g, nB_t, nG_g, nG_t)` converges jointly in law to them (1); each limit is integrable, each
scaled error is integrable for all large $`n` and its expectation converges to that of its limit
(3); and $`n(B_g - B_t - G_g + G_t) \to 0` in probability (2). The errors are those of
{bpref "def:6_5"}[Definition 6.5].

::::

::::theorem "mainthm:6_3" (lean := "SingularLearningTheory.equations_of_state")
%%%
paperIdentity := some { label := "[Wat09, Main Theorem 6.3]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(Equations of states in statistical estimation). Under Fundamental Conditions (I) and (II) with
$`s = 6`, for arbitrary $`q`, $`p(x \mid w)` and $`\varphi`,
$$`\mathbb{E}[B_g^*] - \mathbb{E}[B_t^*]
    = 2\beta\bigl(\mathbb{E}[G_t^*] - \mathbb{E}[B_t^*]\bigr), \qquad
  \mathbb{E}[G_g^*] - \mathbb{E}[G_t^*] = 2\beta\bigl(\mathbb{E}[G_t^*] - \mathbb{E}[B_t^*]\bigr)`
(6.19), (6.20); Corollary 6.2 is their matrix form (6.21).

`equations_of_state`: in the setting of {bpref "thm:6_8"}[Theorem 6.8],
$`n\bigl(\mathbb{E}[B_g] - \mathbb{E}[B_t] - 2\beta(\mathbb{E}[G_t] - \mathbb{E}[B_t])\bigr) \to 0`
and $`n\bigl(\mathbb{E}[G_g] - \mathbb{E}[G_t] - 2\beta(\mathbb{E}[G_t] - \mathbb{E}[B_t])\bigr)
\to 0`.

::::

::::theorem "thm:6_9" (lean := "SingularLearningTheory.gibbs_errors_learning_coefficient")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.9, eq. (6.22)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Conditions (I) and (II) with $`s = 6`, $`nG_g + nG_t - 2\lambda/\beta \to 0` in
probability, and $`\mathbb{E}[G_g^*] + \mathbb{E}[G_t^*] = 2\lambda/\beta` (6.22).

`gibbs_errors_learning_coefficient`: in the setting of {bpref "thm:6_8"}[Theorem 6.8], for the
singularity type $`(\lambda, m)` of $`K` and $`\varphi` ({bpref "def:2_7"}[]),
$`nG_g + nG_t - 2\lambda/\beta \to 0` in probability and
$`n\mathbb{E}[G_g] + n\mathbb{E}[G_t] \to 2\lambda/\beta`.

::::

::::theorem "cor:6_2" (lean := "SingularLearningTheory.generalization_errors_of_training_errors")
%%%
paperIdentity := some { label := "[Wat09, Corollary 6.2, eq. (6.21)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The two generalization errors can be estimated by the two training errors,
$$`\begin{pmatrix} E[B_g^*] \\ E[G_g^*] \end{pmatrix} =
  \begin{pmatrix} 1 - 2\beta & 2\beta \\ -2\beta & 1 + 2\beta \end{pmatrix}
  \begin{pmatrix} E[B_t^*] \\ E[G_t^*] \end{pmatrix}.`

`generalization_errors_of_training_errors`: in the setting of {bpref "thm:6_8"}[Theorem 6.8],
$`n\bigl(E[B_g] - ((1 - 2\beta) E[B_t] + 2\beta E[G_t])\bigr) \to 0` and
$`n\bigl(E[G_g] - (-2\beta E[B_t] + (1 + 2\beta) E[G_t])\bigr) \to 0`.

:::restatement
As in {bpref "mainthm:6_3"}[Main Theorem 6.3], the identities are stated for the scaled expectations
at finite $`n`, which by Theorem 6.8 (3) converge to the expectations of the limits.
:::
::::

::::theorem "cor:6_3" (lean := "SingularLearningTheory.bayes_errors_learning_coefficient")
%%%
paperIdentity := some { label := "[Wat09, Corollary 6.3]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Conditions (I) and (II) with $`s = 6`, $`nB_g - nB_t + 2nG_t - 2\lambda/\beta
\to 0` in probability,
$`\mathbb{E}[B_g^*] - \mathbb{E}[B_t^*] + 2\mathbb{E}[G_t^*] = 2\lambda/\beta`, and in particular
$`\mathbb{E}[B_g^*] = \lambda` if $`\beta = 1`.

`bayes_errors_learning_coefficient`: in the setting of {bpref "thm:6_8"}[Theorem 6.8], for the
singularity type $`(\lambda, m)` ({bpref "def:2_7"}[]), the convergence in probability; the
convergence of $`n E[B_g] - n E[B_t] + 2n E[G_t]` to $`2\lambda/\beta`; and at $`\beta = 1`,
$`n E[B_g] \to \lambda`.

:::restatement
The identity of the expectations of the limits is stated for the limit of the scaled expectations,
which by Theorem 6.8 (3) is $`E[B_g^*] - E[B_t^*] + 2E[G_t^*]`.
:::
::::

::::theorem "thm:6_10" (lean := "SingularLearningTheory.bayes_gibbs_learning_coefficients")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.10, eqs. (6.25)–(6.30)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
$`V - 2(nG_t - nB_t) \to 0` and $`V - 2(nG_g - nB_g) \to 0` in probability (6.25), (6.26); there is
$`\nu = \nu(\beta) > 0` with $`\lim_n \mathbb{E}[V] = 2\nu/\beta` and
$$`\mathbb{E}[B_g^*] = \frac{\lambda}{\beta} + \Bigl(1 - \frac{1}{\beta}\Bigr)\nu, \quad
  \mathbb{E}[B_t^*] = \frac{\lambda}{\beta} - \Bigl(1 + \frac{1}{\beta}\Bigr)\nu, \quad
  \mathbb{E}[G_g^*] = \frac{\lambda}{\beta} + \nu, \quad
  \mathbb{E}[G_t^*] = \frac{\lambda}{\beta} - \nu`
(6.27)–(6.30), where $`\nu(\beta)` is the singular fluctuation of eq. (6.48) and
$`0 \le \nu(\beta) \le \mathbb{E}[\|\xi\|^2]/8 + (\mathbb{E}[\|\xi\|^2]^{1/2}/8)
\sqrt{\mathbb{E}[\|\xi\|^2] + 16\lambda/\beta}`, $`\|\xi\|` the maximum of $`\xi`.

`bayes_gibbs_learning_coefficients`: in the setting of {bpref "thm:6_8"}[Theorem 6.8], for the
singularity type $`(\lambda, m)` and the functional variance $`V` ({bpref "def:6_6"}[]), there is
$`\nu \ge 0` such that (6.25) and (6.26) hold in probability, $`V` is integrable for all large
$`n` and $`\mathbb{E}[V] \to 2\nu/\beta`, and $`n\mathbb{E}[B_g]`, $`n\mathbb{E}[B_t]`,
$`n\mathbb{E}[G_g]`, $`n\mathbb{E}[G_t]` converge to the right-hand sides of (6.27)–(6.30).

::::

::::theorem "rem:6_10" (lean := "SingularLearningTheory.singular_fluctuation_of_bayes_quartet")
%%%
paperIdentity := some { label := "[Wat09, Remark 6.10, eqs. (6.31)–(6.32)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The singular fluctuation has the representations
$`\nu = \tfrac12(E[B_g^*] - E[B_t^*]) = \tfrac12(E[G_g^*] - E[G_t^*]) = \beta(E[G_g^*] - E[B_g^*])
= \beta(E[G_t^*] - E[B_t^*]) = \lim_n \tfrac{\beta}{2} E[V]`, and from the equations of state
$`E[B_g] = E[B_t] + \tfrac{\beta}{n} E[V] + o(1/n)` and
$`E[G_g] = E[G_t] + \tfrac{\beta}{n} E[V] + o(1/n)` (6.31), (6.32); these relations estimate
$`\nu(\beta)` from numerical experiments.

`singular_fluctuation_of_bayes_quartet`: in the setting of {bpref "thm:6_10"}[Theorem 6.10], with
its $`\nu \ge 0`, the five representations as limits of scaled expectations, and (6.31), (6.32)
multiplied by $`n`.

:::restatement
The representations of $`\nu` and the relations (6.31), (6.32) are stated as limits of scaled
expectations at finite $`n`; (6.31) and (6.32) are the book's $`o(1/n)` statements multiplied by
$`n`.
:::
::::

# Maximum likelihood and a posteriori (§6.4)

::::definition "def:1_9"
%%%
paperIdentity := some { label := "[Wat09, Definition 1.9, §6.4]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The maximum likelihood estimator $`\hat w_n` minimises $`n K_n(w) = \sum_i f(X_i, w)`; the
maximum a posteriori estimator minimises $`n K_n(w) + a_n\, \sigma(w)` for a penalty $`\sigma`
and weights $`a_n \ge 0`, with $`a_n = 1`, $`\sigma = -\log \varphi` for the a posteriori
estimator.

The library defines no estimator. The theorems of §6.4 quantify over every sequence of measurable
estimators `ŵ : ℕ → Ω → Fin d → ℝ` lying in $`W` almost surely and almost surely minimising the
objective over $`W` (hypotheses `hŵ`, `hŵW`, `hmin`), for the empirical excess loss
`empiricalExcessLoss` ({bpref "def:1_1"}[]); their existence is not asserted.
::::

::::theorem "thm:6_12"
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.12]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Conditions (I) and (II) with $`s \ge 6` and $`a_n/n \to 0`, for the
estimator $`\hat w` and the empirical process $`\psi_n` on $`\{K > \varepsilon\}`:
(1) $`P(\|\psi_n\|^2 > n\varepsilon) \le C/n^{s/2}` and $`P(K(\hat w) > \varepsilon) \le C/n^{s/2}`;
(2) the expectations of $`\|\psi_n\|^2` and $`nK(\hat w)` on those events are at most
$`C'/n^{s/2 - 1}`. By Remark 6.15 the maximum likelihood and a posteriori estimators converge to
the set of true parameters.

:::unformalised (missing := statement)
Not stated; the library proves the consistency it needs inside its proofs of Main Theorem 6.4.
:::
::::

::::theorem "thm:6_13"
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.13]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Under Fundamental Conditions (I) and (II) with $`s \ge 6` and $`a_n/n^p \to 0` for every
$`p > 0`, for $`0 < \delta < 1`: (1) $`P(\|\xi_n\|^2 > n^\delta) \le C/n^{s\delta/2}` and
$`P(nK(g(\hat u)) > n^\delta) \le C/n^{s\delta/2}`; (2) the expectations of $`\|\xi_n\|^2` and
$`nK(g(\hat u))` on those events are at most $`C'/n^{\delta(s/2 - 1)}`.

:::unformalised (missing := statement)
Not stated; the library proves the bounds it needs inside its proofs of Main Theorem 6.4.
:::
::::

::::theorem "mainthm:6_4:1" (lean := "SingularLearningTheory.maximumLikelihood_asymptotics")
%%%
paperIdentity := some { label := "[Wat09, Main Theorem 6.4 (1)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
For the maximum likelihood estimator, $`\mathbb{E}[n K(\hat w_n)] \to \tfrac14
\mathbb{E}[M(\xi)^2]` and $`\mathbb{E}[n K_n(\hat w_n)] \to -\tfrac14 \mathbb{E}[M(\xi)^2]`, where
$`M(\xi) = \max_\alpha \max_{u \in \mathcal{M}_{\alpha 0}} \max\{0, \xi(u)\}`.

`maximumLikelihood_asymptotics`: under the standing assumptions with $`s = 4` and
$`W = \overline{\operatorname{int} W}`, for a resolution `R`, a chart family `F`, resolved
coefficients `L` ({bpref "thm:6_1"}[]) with an empirical process limit `E`
({bpref "thm:6_2"}[]), and every measurable maximum likelihood estimator, with
$`\mathcal{Z}` the zeros of $`K` on the pieces and
$`M = \sup_{v \in \mathcal{Z}} \max\{0, \xi(v)\}^2/4` at $`\xi = -\Psi`: $`M` is integrable,
$`nK(\hat w_n)` and $`nK_n(\hat w_n)` are integrable for all large $`n`, the pair
$`(nK(\hat w_n), nK_n(\hat w_n))` converges in law to $`(M, -M)`, and the expectations converge
to $`\pm\mathbb{E}[M]`.

::::

::::theorem "mainthm:6_4:2" (lean := "SingularLearningTheory.finitePenalty_asymptotics")
%%%
paperIdentity := some { label := "[Wat09, Main Theorem 6.4 (2)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
If $`a_n \to a^*`, the maximum a posteriori estimator satisfies
$`n K(\hat w_n) \to \tfrac14 \max\{0, \xi(u^*)\}^2` and $`n K_n(\hat w_n) \to -\tfrac14 \max\{0, \xi(u^*)\}^2`
in law, where $`u^*` maximises $`\tfrac14 \max\{0, \xi(u)\}^2 - a^* \sigma(g(u))` over the zero
slice; and $`\mathbb{E}[n K(\hat w_n)] + \mathbb{E}[n K_n(\hat w_n)] \to 0` (Main Formula IV).

`finitePenalty_asymptotics`: in the setting of {bpref "mainthm:6_4:1"}[Main Theorem 6.4 (1)], for
a penalty $`\sigma` of class $`C^1` on an open neighbourhood of $`W`, weights $`a_n \ge 0` with
$`a_n \to a`, and every measurable minimiser of $`nK_n + a_n\sigma`, with
$`M = \sup_{v \in \mathcal{Z}} \bigl(\max\{0, \xi(v)\}^2/4 - a\,\sigma(g(v))\bigr)`: the pair
$`(nK(\hat w_n) - a\sigma(\hat w_n),\ nK_n(\hat w_n) + a\sigma(\hat w_n))` converges in law to
$`(M, -M)`, and both expectations converge, with the integrability of $`M` and of both errors.

::::

::::theorem "mainthm:6_4:3" (lean := "SingularLearningTheory.divergingPenalty_asymptotics")
%%%
paperIdentity := some { label := "[Wat09, Main Theorem 6.4 (3)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
If $`a_n \to \infty` slower than every power of $`n`, then $`n K(\hat w_n) \to \tfrac14 M_{00}(\xi)^2`
and $`n K_n(\hat w_n) \to -\tfrac14 M_{00}(\xi)^2` in law and in mean, with
$`M_{00}(\xi) = \max_\alpha \max_{u \in \mathcal{M}_{\alpha 00}} \max\{0, \xi(u)\}` the maximum over
the penalty minimisers of the zero slice.

`divergingPenalty_asymptotics`: in the setting of {bpref "mainthm:6_4:2"}[Main Theorem 6.4 (2)],
for weights $`a_n \ge 0` with $`a_n \to \infty` and $`a_n / n^r \to 0` for every $`r > 0`, the
conclusion of part (1) holds with the supremum restricted to $`\mathcal{Z}_{00}`, the zeros of
$`K` on the pieces at which $`\sigma \circ g` is smallest over all pieces.

::::

::::theorem "cor:6_4" (lean := "SingularLearningTheory.freeEnergy_centered_at_maximumLikelihood")
%%%
paperIdentity := some { label := "[Wat09, Corollary 6.4]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
$`F^{MR}_n = F^R_n - n K_n(\hat w_n)` converges in law to $`-\log Z(\xi) + \tfrac14 M(\xi)^2`,
for the maximum likelihood or a posteriori estimator.

`freeEnergy_centered_at_maximumLikelihood`: under the standing assumptions with $`s = 4`,
Fundamental Condition (II) and the zero-set conditions, for every i.i.d. sample and measurable
maximum likelihood estimator, at $`\beta = 1`, with $`(\lambda, m)` the singularity type, the
remainder
$$`R_n = F_n - n L_n(\hat w_n) - \lambda \log n + (m - 1) \log\log n`
converges in law and in expectation to an integrable limit.

::::
