# Singular learning theory in Lean

[![Build](https://github.com/resolutionorg/slt/actions/workflows/build.yml/badge.svg)](https://github.com/resolutionorg/slt/actions/workflows/build.yml)
[![Comparator](https://github.com/resolutionorg/slt/actions/workflows/comparator.yml/badge.svg)](https://github.com/resolutionorg/slt/actions/workflows/comparator.yml)

**[API documentation](https://resolutionorg.github.io/slt/docs/)** · **[Blueprint](https://resolutionorg.github.io/slt/blueprint/)** ·
[Statements](SLTChallenge) · [Sources](references.bib)

A Lean 4 formalization, over Mathlib, of the main results of Sumio Watanabe's *Algebraic Geometry
and Statistical Learning Theory* [Wat09], with the weaker *relatively finite variance* from Watanabe's 
*Mathematical Theory of Bayesian Statistics* [Wat18, Definition 7] replacing the realizability assumption 
of [Wat09]. Every theorem is proved: the library contains no `sorry`.

## Overview

The statements of the theorems live in [`SLTChallenge/`](SLTChallenge), separately from their
proofs. These files are short (about 2,200 lines in total), import only Mathlib, and contain every
definition that the statements use. The theorem statements and definitions in these files have been 
manually checked against the source material.
A reader can check what has been formalized by reading only the files in [`SLTChallenge/`](SLTChallenge). 

The proofs live in the library [`SLT/`](SLT). For each file of `SLTChallenge/`, the
library has a `Defs` module that repeats its definitions word for word and a module that proves its
theorems under the same names:

| Statements | Definitions | Proofs |
| --- | --- | --- |
| [`Setting`](SLTChallenge/Setting.lean) | [`SLT/Setting.lean`](SLT/Setting.lean) | |
| [`StandardForm`](SLTChallenge/StandardForm.lean) | [`SLT/StandardForm/Defs.lean`](SLT/StandardForm/Defs.lean) | [`SLT/StandardForm.lean`](SLT/StandardForm.lean) |
| [`FreeEnergy`](SLTChallenge/FreeEnergy.lean) | [`SLT/FreeEnergy/Defs.lean`](SLT/FreeEnergy/Defs.lean) | [`SLT/FreeEnergy.lean`](SLT/FreeEnergy.lean) |
| [`SingularIntegrals`](SLTChallenge/SingularIntegrals.lean) | [`SLT/SingularIntegrals/Defs.lean`](SLT/SingularIntegrals/Defs.lean) | [`SLT/SingularIntegrals.lean`](SLT/SingularIntegrals.lean) |
| [`Zeta`](SLTChallenge/Zeta.lean) | [`SLT/SingularIntegrals/Zeta/Defs.lean`](SLT/SingularIntegrals/Zeta/Defs.lean) | [`SLT/SingularIntegrals/Zeta.lean`](SLT/SingularIntegrals/Zeta.lean) |
| [`Mellin`](SLTChallenge/Mellin.lean) | [`SLT/Analysis/Mellin/Defs.lean`](SLT/Analysis/Mellin/Defs.lean) | [`SLT/Analysis/Mellin.lean`](SLT/Analysis/Mellin.lean) |
| [`Resolution`](SLTChallenge/Resolution.lean) | [`SLT/Resolution/Defs.lean`](SLT/Resolution/Defs.lean) | [`SLT/Resolution.lean`](SLT/Resolution.lean) |
| [`EmpiricalProcess`](SLTChallenge/EmpiricalProcess.lean) | [`SLT/EmpiricalProcess/Defs.lean`](SLT/EmpiricalProcess/Defs.lean) | [`SLT/EmpiricalProcess.lean`](SLT/EmpiricalProcess.lean) |
| [`MaximumLikelihood`](SLTChallenge/MaximumLikelihood.lean) | | [`SLT/MaximumLikelihood.lean`](SLT/MaximumLikelihood.lean) |
| [`BayesGibbs`](SLTChallenge/BayesGibbs.lean) | [`SLT/BayesGibbs/Defs.lean`](SLT/BayesGibbs/Defs.lean) | [`SLT/BayesGibbs.lean`](SLT/BayesGibbs.lean) |

A tool, the comparator, checks that the theorems proved in `SLT/` are exactly those stated in
`SLTChallenge/` ([Building and verifying](#building-and-verifying)).

[`SLT/Witnesses.lean`](SLT/Witnesses.lean) shows that the hypotheses of the free energy
formula can all be met. It takes the Bernoulli model $p(1 \mid w) = w$ on $W = [1/4, 3/4]$ with a
uniform prior and true parameter $1/2$, proves every hypothesis of `free_energy_formula` for it and
applies the theorem.

## Building and verifying

The Lean toolchain is pinned in [`lean-toolchain`](lean-toolchain) (Lean 4.35.0) and Mathlib in
[`lake-manifest.json`](lake-manifest.json). With [elan](https://github.com/leanprover/elan)
installed, in the root of the repository:

```sh
lake exe cache get                          # download prebuilt Mathlib
lake build                                  # the library SLT, with all proofs
lake build SLTChallenge                     # the statements
```

A successful `lake build` checks every proof in `SLT/`; the only `sorry` warnings come from
`SLTChallenge/`, where they are intended.

[leanprover/comparator](https://github.com/leanprover/comparator) checks, for each name in
[`comparator.json`](comparator.json), that the declaration in `SLT` has the same statement as
the one in `SLTChallenge`, and that its proof uses no axiom beyond `propext`, `Quot.sound` and
`Classical.choice`. A reader who trusts the comparator therefore needs to read only
`SLTChallenge/` to know what has been proved. With `landrun` and a `lean4export` built for this
toolchain on the `PATH`:

```sh
lake build SLT SLTChallenge
lake env path/to/comparator comparator.json   # expect: Your solution is okay!
```

The repository's CI runs the comparator on every push and pull request
([`.github/workflows/comparator.yml`](.github/workflows/comparator.yml)), building both libraries
from scratch in its sandbox.

The library requires [hironaka](https://github.com/resolutionorg/hironaka), a Lean formalization of
resolution of singularities, at its release for the same Lean toolchain; Lake fetches it with the
other dependencies. Only the proofs use it: Watanabe's resolution theorem [Wat09, Theorem 2.8]
(`exists_sltResolution`) and the analytic machinery around it are derived from hironaka's
resolution theorems. `SLTChallenge/` imports only Mathlib, and the `Defs` modules that repeat its
definitions do not import hironaka, so the statements do not depend on it.

## The statements

This section describes each file of `SLTChallenge/`: what it defines, what it proves and which
items of [Wat09] the theorems formalize. The files are listed in reading order, starting with
the setting and the headline results. Each table links a theorem's statement and its proof.

Some departures from [Wat09] recur across the files, and are worth knowing before reading any
statement.

- **Relatively finite variance in place of realizability.** Results are proved under the weaker
  relatively finite variance condition [Wat18, Definition 7] rather than realizability. 
- **The learning coefficient by volume scaling.** [Wat09] defines the learning coefficient
  $\lambda$ and its multiplicity $m$ as the largest pole of the zeta function and its order. Here
  `IsSingularityType K φ W λ m` defines them by two-sided bounds on the prior volume of the
  sublevel sets $\{K \le \varepsilon\}$, of order $\varepsilon^\lambda (-\log\varepsilon)^{m-1}$.
  The zeta function theorems prove that the two definitions agree.

### Setting

[`SLTChallenge/Setting.lean`](SLTChallenge/Setting.lean) fixes the objects every other file
uses, for a model $p(x \mid w)$ with parameters $w$ in a set $W \subseteq \mathbb{R}^d$: the log
density ratio $f$, the excess loss $K$ and its empirical version $K_n$ [Wat09, Definition 1.3], the
average and empirical log losses $L$ and $L_n$ [Wat18, eqs. (3.6) and (3.7)], relatively finite
variance (`RelativelyFiniteVariance`) [Wat18, Definition 7], an i.i.d. sample (`IsIIDSample`), the
prior measure, fundamental condition II (`FundamentalConditionII`) [Wat09, Definition 6.3], with
the semianalyticity of $W$ that it requires, and `ZeroSetConditions`. The file contains no theorems.

### The standard form of the log likelihood ratio

[`SLTChallenge/StandardForm.lean`](SLTChallenge/StandardForm.lean) states [Wat09, Main Theorem
6.1]: after a resolution of singularities, the empirical excess loss takes the standard form
$K_n(g(u)) = u^{2k} - n^{-1/2} u^k \xi_n(u)$ in local coordinates $u$. It defines fundamental
condition I [Wat09, Definition 6.1] and bundles the hypotheses shared by the main theorems into
`StandingAssumptions`: $W$ compact, $p$ measurable and positive on $W$, relatively finite variance
at $w_0 \in W$, fundamental condition I, and continuity of $f(x, \cdot)$. Several consequences 
of `StandingAssumptions` are also proved, which demonstrate that these bundled hypotheses correspond to 
the usual setting of singular learning theory. 

| Theorem | Source | Proof |
| --- | --- | --- |
| [`StandingAssumptions.isMinOn_excessLoss`](SLTChallenge/StandardForm.lean#L113) | | [Proof](SLT/StandardForm.lean#L90) | <!-- StandingAssumptions.isMinOn_excessLoss -->
| [`StandingAssumptions.isMinOn_expectedNegativeLogLikelihood`](SLTChallenge/StandardForm.lean#L122) | | [Proof](SLT/StandardForm.lean#L101) | <!-- StandingAssumptions.isMinOn_expectedNegativeLogLikelihood -->
| [`StandingAssumptions.ae_eq_of_excessLoss_eq_zero`](SLTChallenge/StandardForm.lean#L132) | [Wat18, Definition 6 and Lemma 3] | [Proof](SLT/StandardForm.lean#L122) | <!-- StandingAssumptions.ae_eq_of_excessLoss_eq_zero -->
| [`StandingAssumptions.of_excessLoss_eq_zero`](SLTChallenge/StandardForm.lean#L143) | [Wat18, after Lemma 3] | [Proof](SLT/StandardForm.lean#L144) | <!-- StandingAssumptions.of_excessLoss_eq_zero -->
| [`StandingAssumptions.analyticOnNhd_excessLoss`](SLTChallenge/StandardForm.lean#L153) | | [Proof](SLT/StandardForm.lean#L174) | <!-- StandingAssumptions.analyticOnNhd_excessLoss -->
| [`exists_resolvedLogDensityRatio`](SLTChallenge/StandardForm.lean#L204) | [Wat09, Theorem 6.1] | [Proof](SLT/StandardForm.lean#L203) | <!-- exists_resolvedLogDensityRatio -->
| [`exists_empiricalProcessLimit`](SLTChallenge/StandardForm.lean#L236) | [Wat09, Theorem 6.2(1)] | [Proof](SLT/StandardForm.lean#L279) | <!-- exists_empiricalProcessLimit -->

### The free energy formula

[`SLTChallenge/FreeEnergy.lean`](SLTChallenge/FreeEnergy.lean) concerns the evidence $Z_n$, the 
free energy $F_n = -\log Z_n$ and the normalized evidence
$Z_n^0$ [Wat09, Definition 6.2 and eq. (6.12)]. `free_energy_formula` states that, under the
standing assumptions, fundamental condition II and the zero-set conditions, there are $\lambda > 0$
and $m \ge 1$, the singularity type of $K$, such that for every inverse temperature $\beta > 0$ and
every i.i.d. sample

$$F_n = n\beta L_n(w_0) + \lambda \log n - (m - 1) \log\log n + R_n$$

almost surely for $n \ge 2$, where $R_n$ converges in law. This is [Wat09, Main Theorem 6.2] in the
form of Corollary 6.1. `free_energy_formula_expectation` is the same statement in expectation, and
`tendstoInDistribution_normalizedEvidence` is the convergence in law of the normalized evidence on which both rest.

| Theorem | Source | Proof |
| --- | --- | --- |
| [`tendstoInDistribution_normalizedEvidence`](SLTChallenge/FreeEnergy.lean#L115) | [Wat09, Theorem 6.7] | [Proof](SLT/FreeEnergy.lean#L790) | <!-- tendstoInDistribution_normalizedEvidence -->
| [`free_energy_formula`](SLTChallenge/FreeEnergy.lean#L174) | [Wat09, Corollary 6.1(1)] | [Proof](SLT/FreeEnergy.lean#L936) | <!-- free_energy_formula -->
| [`free_energy_formula_expectation`](SLTChallenge/FreeEnergy.lean#L211) | [Wat09, Corollary 6.1(2)] | [Proof](SLT/FreeEnergy.lean#L1009) | <!-- free_energy_formula_expectation -->

### Bayes and Gibbs estimation

[`SLTChallenge/BayesGibbs.lean`](SLTChallenge/BayesGibbs.lean) states [Wat09, §6.3]. It
defines the tempered posterior, the Bayes and Gibbs generalization and training errors [Wat09,
Definition 6.5] and the functional variance [Wat09, Definition 6.6], all relative to $w_0$. The
theorems give the joint convergence of the four scaled errors, the equations of state [Wat09, Main
Theorem 6.3], and the expressions of the errors through the learning coefficient $\lambda$ and the
singular fluctuation $\nu$. 

| Theorem | Source | Proof |
| --- | --- | --- |
| [`bayes_gibbs_convergence`](SLTChallenge/BayesGibbs.lean#L107) | [Wat09, Theorem 6.8] | [Proof](SLT/BayesGibbs.lean#L224) | <!-- bayes_gibbs_convergence -->
| [`equations_of_state`](SLTChallenge/BayesGibbs.lean#L149) | [Wat09, Main Theorem 6.3] | [Proof](SLT/BayesGibbs.lean#L285) | <!-- equations_of_state -->
| [`gibbs_errors_learning_coefficient`](SLTChallenge/BayesGibbs.lean#L181) | [Wat09, Theorem 6.9] | [Proof](SLT/BayesGibbs.lean#L344) | <!-- gibbs_errors_learning_coefficient -->
| [`bayes_gibbs_learning_coefficients`](SLTChallenge/BayesGibbs.lean#L212) | [Wat09, Theorem 6.10] | [Proof](SLT/BayesGibbs.lean#L394) | <!-- bayes_gibbs_learning_coefficients -->

### Maximum likelihood and maximum a posteriori estimation

[`SLTChallenge/MaximumLikelihood.lean`](SLTChallenge/MaximumLikelihood.lean) states [Wat09,
§6.4]: the limiting laws of the generalization and training errors of the maximum likelihood
estimator and of penalized estimators with a fixed or a slowly diverging penalty (the maximum a
posteriori estimator is a special case), and the free energy centered at the maximum likelihood
estimator.

| Theorem | Source | Proof |
| --- | --- | --- |
| [`maximumLikelihood_asymptotics`](SLTChallenge/MaximumLikelihood.lean#L43) | [Wat09, Main Theorem 6.4(1)] | [Proof](SLT/MaximumLikelihood.lean#L120) | <!-- maximumLikelihood_asymptotics -->
| [`finitePenalty_asymptotics`](SLTChallenge/MaximumLikelihood.lean#L91) | [Wat09, Main Theorem 6.4(2)] | [Proof](SLT/MaximumLikelihood.lean#L195) | <!-- finitePenalty_asymptotics -->
| [`divergingPenalty_asymptotics`](SLTChallenge/MaximumLikelihood.lean#L142) | [Wat09, Main Theorem 6.4(3)] | [Proof](SLT/MaximumLikelihood.lean#L279) | <!-- divergingPenalty_asymptotics -->
| [`freeEnergy_centered_at_maximumLikelihood`](SLTChallenge/MaximumLikelihood.lean#L199) | [Wat09, Corollary 6.4] | [Proof](SLT/MaximumLikelihood.lean#L401) | <!-- freeEnergy_centered_at_maximumLikelihood -->

### Singular integrals

[`SLTChallenge/SingularIntegrals.lean`](SLTChallenge/SingularIntegrals.lean) has two parts.
The first concerns integrals over a cube $[0, b]^d$ with the normal-crossing potential $x^{2k}$ and
weight $x^h$. It defines the threshold $\lambda = \min_{k_j > 0} (h_j + 1)/(2k_j)$, the number $m$
of coordinates that attain it, the partition function $Z^p(n, \xi, \varphi)$ [Wat09, Definition
4.10] and its central part $Y^p$, and states the bounds of [Wat09, Theorems 4.7–4.9]: $Z^p$ is of
order $(\log n)^{m-1}/n^{\lambda + p}$, and $Y^p$ approximates it to within
$(\log n)^{m-2}/n^{\lambda+p}$. The second part defines the integral
$Z_0(n) = \int_W e^{-n\beta K}\varphi$, the volume $V(t)$ of $\{K \le t\}$, the state density
$v = V'$ and `IsSingularityType`, and states the four characterizations of $(\lambda, m)$ in [Wat09,
Theorem 7.1], for analytic $K \ge 0$ on a compact $W$.

| Theorem | Source | Proof |
| --- | --- | --- |
| [`normalCrossingIntegral₀_bounds`](SLTChallenge/SingularIntegrals.lean#L224) | [Wat09, Theorem 4.7] | [Proof](SLT/SingularIntegrals.lean#L290) | <!-- normalCrossingIntegral₀_bounds -->
| [`normalCrossingIntegral_bounds_of_nonneg`](SLTChallenge/SingularIntegrals.lean#L250) | [Wat09, Theorem 4.8] | [Proof](SLT/SingularIntegrals.lean#L440) | <!-- normalCrossingIntegral_bounds_of_nonneg -->
| [`abs_normalCrossingIntegral_sub_normalCrossingCentralPart_le`](SLTChallenge/SingularIntegrals.lean#L285) | [Wat09, Theorem 4.9] | [Proof](SLT/SingularIntegrals.lean#L948) | <!-- abs_normalCrossingIntegral_sub_normalCrossingCentralPart_le -->
| [`singularity_type_unique`](SLTChallenge/SingularIntegrals.lean#L366) | | [Proof](SLT/SingularIntegrals.lean#L103) | <!-- singularity_type_unique -->
| [`tendsto_rpow_div_log_pow_mul_laplaceIntegral`](SLTChallenge/SingularIntegrals.lean#L394) | [Wat09, Theorem 7.1(1)] | [Proof](SLT/SingularIntegrals.lean#L152) | <!-- tendsto_rpow_div_log_pow_mul_laplaceIntegral -->
| [`tendsto_neg_log_laplaceIntegral_div_log`](SLTChallenge/SingularIntegrals.lean#L409) | [Wat09, Theorem 7.1(2)] | [Proof](SLT/SingularIntegrals.lean#L173) | <!-- tendsto_neg_log_laplaceIntegral_div_log -->
| [`tendsto_stateDensity_div_rpow_mul_neg_log_pow`](SLTChallenge/SingularIntegrals.lean#L424) | [Wat09, Theorem 7.1(3)] | [Proof](SLT/SingularIntegrals.lean#L191) | <!-- tendsto_stateDensity_div_rpow_mul_neg_log_pow -->
| [`tendsto_log_sublevelVolume_ratio_div_log`](SLTChallenge/SingularIntegrals.lean#L442) | [Wat09, Theorem 7.1(4)] | [Proof](SLT/SingularIntegrals.lean#L214) | <!-- tendsto_log_sublevelVolume_ratio_div_log -->

### Zeta functions

[`SLTChallenge/Zeta.lean`](SLTChallenge/Zeta.lean) defines the zeta function
$\zeta(z) = \int_W K(w)^z \varphi(w)\,dw$ [Wat09, eq. (6.15)] and states that it is holomorphic on
$\mathrm{Re}\, z > 0$ and continues to a meromorphic function on $\mathbb{C}$ whose poles are
negative rationals, the largest being $-\lambda$ with order $m$, where $(\lambda, m)$ is the
singularity type. This identifies the volume-scaling definition of $(\lambda, m)$ with that of [Wat09].

| Theorem | Source | Proof |
| --- | --- | --- |
| [`zetaFunction_meromorphic_continuation`](SLTChallenge/Zeta.lean#L60) | [Wat09, Theorem 6.6 and Definition 6.4] | [Proof](SLT/SingularIntegrals/Zeta.lean#L42) | <!-- zetaFunction_meromorphic_continuation -->
| [`zetaFunction_continuation_unique`](SLTChallenge/Zeta.lean#L85) | [Wat09, Theorem 6.6] | [Proof](SLT/SingularIntegrals/Zeta.lean#L79) | <!-- zetaFunction_continuation_unique -->

### Mellin transforms

[`SLTChallenge/Mellin.lean`](SLTChallenge/Mellin.lean) states the results on Mellin transforms
in [Wat09, §4.3], which connect the zeta function to the state density. It defines the Mellin
transform following the convention of [Wat09]: $(\mathcal{M}f)(z) = \int_0^\infty f(t)\,t^z\,dt$, which is
Mathlib's `mellin` shifted by one.

| Theorem | Source | Proof |
| --- | --- | --- |
| [`mellinTransform_differentiableOn_strip`](SLTChallenge/Mellin.lean#L85) | [Wat09, §4.3] | [Proof](SLT/Analysis/Mellin.lean#L46) | <!-- mellinTransform_differentiableOn_strip -->
| [`inverseMellin_tendsto_of_boundedVariation`](SLTChallenge/Mellin.lean#L110) | [Wat09, Theorem 4.5] | [Proof](SLT/Analysis/Mellin.lean#L31) | <!-- inverseMellin_tendsto_of_boundedVariation -->
| [`mellinTransform_power_log`](SLTChallenge/Mellin.lean#L129) | [Wat09, Example 4.7] | [Proof](SLT/Analysis/Mellin.lean#L61) | <!-- mellinTransform_power_log -->

### Resolution of singularities

[`SLTChallenge/Resolution.lean`](SLTChallenge/Resolution.lean) defines the form of resolution
of singularities that singular learning theory uses. An `SLTResolution K φ W` is a proper analytic
map $\pi : M \to U$ onto an open neighbourhood $U$ of $W$, an isomorphism away from a null set, with
a chart around every point over a zero of $K$ in which $K \circ \pi = u^{2k}$ and the pulled-back
prior density is a positive smooth function times $|u^h|$. This is [Wat09, Theorem 2.8] in a global
form. A `ChartFamily` is a finite set of such charts
covering a sublevel set of $K$, cut into the orthant pieces that are the book's local coordinates
in [Wat09, Theorem 6.5]. The learning coefficient and multiplicity of a resolution are read off its
charts as in [Wat09, eqs. (6.16) and (6.17)], and `SLTResolution.isSingularityType` proves they are
the singularity type of $K$. The existence of a resolution rests on the formalization of Hironaka's
theorem in the [hironaka](https://github.com/resolutionorg/hironaka) library.

| Theorem | Source | Proof |
| --- | --- | --- |
| [`exists_sltResolution`](SLTChallenge/Resolution.lean#L367) | [Wat09, Theorem 2.8] | [Proof](SLT/Resolution.lean#L260) | <!-- exists_sltResolution -->
| [`SLTResolution.exists_chartFamily`](SLTChallenge/Resolution.lean#L397) | [Wat09, Theorem 6.5] | [Proof](SLT/Resolution.lean#L461) | <!-- SLTResolution.exists_chartFamily -->
| [`SLTResolution.ChartFamily.exists_partitionOfUnity`](SLTChallenge/Resolution.lean#L410) | [Wat09, Theorem 6.5(4)] | [Proof](SLT/Resolution.lean#L474) | <!-- SLTResolution.ChartFamily.exists_partitionOfUnity -->
| [`SLTResolution.isSingularityType`](SLTChallenge/Resolution.lean#L428) | [Wat09, Definition 6.4] | [Proof](SLT/Resolution.lean#L492) | <!-- SLTResolution.isSingularityType -->

### Empirical processes

[`SLTChallenge/EmpiricalProcess.lean`](SLTChallenge/EmpiricalProcess.lean) states the results
of [Wat09, Chapter 5]. It defines $L^s(q)$-valued real analyticity [Wat09, Definition 5.3], the
empirical process $\psi_n(w) = n^{-1/2} \sum_{i<n} (f(X_i, w) - E f(X, w))$ [Wat09, Definition
5.6], and `EmpiricalProcessLimit`, which packages the conclusion of [Wat09, Theorem 5.9]: $\psi_n$
is a tight sequence of random continuous functions converging in law to a centered Gaussian process
with the covariance of $f$.

| Theorem | Source | Proof |
| --- | --- | --- |
| [`convergence_of_empirical_process`](SLTChallenge/EmpiricalProcess.lean#L124) | [Wat09, Theorem 5.9] | [Proof](SLT/EmpiricalProcess.lean#L96) | <!-- convergence_of_empirical_process -->
| [`exists_lintegral_iSup_empiricalProcess_pow_le`](SLTChallenge/EmpiricalProcess.lean#L150) | [Wat09, Theorem 5.8] | [Proof](SLT/EmpiricalProcess.lean#L127) | <!-- exists_lintegral_iSup_empiricalProcess_pow_le -->

## Blueprint

[`blueprint/`](blueprint/) is a Verso Blueprint document that follows [Wat09] chapter by chapter:
a node per definition and main theorem, linked by name to its declaration, with every difference
from the book recorded as an annotation at the node ([`blueprint/README.md`](blueprint/README.md)).
Items of [Wat09] that this library does not state are marked unformalised at their node. It is
published at https://resolutionorg.github.io/slt/blueprint/, beside the [API documentation](https://resolutionorg.github.io/slt/docs/). To
build the site (writes `blueprint/_out/site/html-multi/`):

```sh
cd blueprint
lake exe vbp build    # add --serve to preview
```

## Using the library

Add the package to your `lakefile.toml`:

```toml
[[require]]
name = "slt"
git = "https://github.com/resolutionorg/slt"
rev = "v4.35.0"
```

A release is tagged with its Lean toolchain, so pick the tag that matches your project's
`lean-toolchain`.

and import `SLT` or one of its modules. Import from `SLT`, never from `SLTChallenge`:
the two declare the same names, and the theorems of `SLTChallenge` are unproved.

All declarations are in the namespace `SingularLearningTheory`. The definitions to build on are
those of the `Defs` modules listed above, which are the definitions of `SLTChallenge`; the rest of the library
contains the machinery of the proofs, including the block-coordinate forms of the normal-crossing
integrals in the namespace `SingularLearningTheory.NormalCrossing`.

Lake also fetches the package's dependencies, Mathlib and hironaka, at the revisions in
[`lake-manifest.json`](lake-manifest.json); your project's Mathlib must be the same revision.

## Methodology

AI agents run through Claude Code (Claude Fable 5.1 and Claude Opus 5.5; Anthropic) and Codex (GPT 6 Astra; OpenAI) 
were directed to formalize the main results of [Wat09] under the relatively finite variance condition 
of [Wat18]. The agents were given access to the source material [Wat09,Wat18] and additionally
[Hit26] (Chapters 2-5 give an exposition of the proof of the free energy formula), and were instructed to 
follow the approach presented in the source material. 

Once the agents claimed to have completed the task, the main statements and supporting definitions 
were extracted, forming the first draft of `SLTChallenge/`. These statements and definitions underwent 
extensive refactoring to make them more useful, readable, and to make them better correspond to the 
source material. Refactoring was often needed to address situations such as the following:
- The source material was ambiguous or left certain assumptions implicit. Agents introduced assumptions 
that allowed the proof to be completed but did not match our intent. 
- Definitions were made which did not read naturally to a human mathematician. For 
example, several loosely related hypotheses may have been bundled into a single definition. Even if all 
of these hypotheses are 'correct' (in the sense of being required for our intended formalization), such 
definitions make the formalized statements difficult to interpret and reuse.
- Relatedly, definitions were introduced to improve readability or reusability.


## Sources

The sources are listed in [`references.bib`](references.bib):

- [Wat09] Sumio Watanabe, *Algebraic Geometry and Statistical Learning Theory*, Cambridge
  University Press, 2009.
- [Wat18] Sumio Watanabe, *Mathematical Theory of Bayesian Statistics*, CRC Press, 2018.
- [Hit26] Rohan Hitchcock, *Singular learning theory for deep learning interpretability: stochastic
  sampling methods and applications to learning from physical systems*, PhD thesis, University of
  Melbourne, 2026. <https://hdl.handle.net/11343/371115>.

## License

Apache License 2.0; see `LICENSE`. Copyright (c) 2026 Resolution.
