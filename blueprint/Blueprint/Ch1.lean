import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import SLT.Setting
import SLT.FreeEnergy.Defs
import SLT.BayesGibbs.Defs

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SingularLearningTheory MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option verso.blueprint.autoDeps true

#doc (Manual) "Introduction (Chapter 1)" =>

Chapter 1 fixes the vocabulary of the book: a true distribution, a parametric model, a prior, and
the objects built from them. The library does not bundle them into a structure: every statement
takes the true distribution `q`, the model `p`, the parameter set `W`, a reference parameter `w₀`
and the prior density `φ` as separate arguments, and the hypotheses on them as separate
hypotheses. The losses are measured from the reference parameter $`w_0` rather than from the true
distribution, which is what lets the theorems assume relatively finite variance
({bpref "def:rfv"}[]) in place of realizability.

# Basic concepts in statistical learning (§1.1)

::::definition "def:setup" (lean := "SingularLearningTheory.priorMeasure, SingularLearningTheory.StandingAssumptions")
%%%
paperIdentity := some { label := "[Wat09, §1.1.1]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
A *statistical learning setup* consists of a true probability density $`q(x)`, a parametric model
of densities $`p(x \mid w)`, and a prior $`\varphi(w)\,dw` on the parameter space $`W`.

In the library the true distribution is a probability measure `q : Measure X` on the sample space,
the model is a function `p : (Fin d → ℝ) → X → ℝ`, $`p(x \mid w) = ` `p w x`, the parameter set
is a subset `W` of $`\mathbb{R}^d`, and the prior is a density `φ` on `W`, whose measure is
`priorMeasure φ W`, Lebesgue measure on `W` with density `φ`. A reference parameter
`w₀ : Fin d → ℝ` fixes the origin of the losses ({bpref "def:1_1"}[]). The hypotheses that the
main theorems share are bundled in `StandingAssumptions s q p W w₀` ({bpref "def:6_1"}[]).

::::

::::definition "def:1_1" (lean := "SingularLearningTheory.logDensityRatio, SingularLearningTheory.excessLoss, SingularLearningTheory.empiricalExcessLoss, SingularLearningTheory.expectedNegativeLogLikelihood, SingularLearningTheory.empiricalNegativeLogLikelihood")
%%%
paperIdentity := some { label := "[Wat09, Definition 1.1, eqs. (1.1)–(1.3)]; [Wat18, eqs. (3.6), (3.7)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The *log density ratio* is $`f(x, w) = \log \frac{q(x)}{p(x \mid w)}` (eq. (1.1)), the
*Kullback–Leibler distance as a function of the parameter* is $`K(w) = \int q(x) f(x, w)\,dx`
(eq. (1.2)), and the *empirical Kullback–Leibler distance*, or log likelihood ratio, of a sample
$`X_1, \dots, X_n` is $`K_n(w) = \frac{1}{n} \sum_{i=1}^{n} f(X_i, w)` (eq. (1.3)).

The library measures the same quantities from the reference parameter: `logDensityRatio p w₀ x w`
is $`f(x, w) = \log \frac{p(x \mid w_0)}{p(x \mid w)}`, `excessLoss q p w₀ w` is
$`K(w) = \mathbb{E}_q[f(X, w)]` and `empiricalExcessLoss p w₀ Xs n ω w` is $`K_n(w)` for the
first $`n` points of the sample `Xs`. With the average and empirical log losses of {cite Wat18}[eqs.
(3.6), (3.7)], $`L(w) = -\mathbb{E}_q[\log p(X \mid w)]` (`expectedNegativeLogLikelihood`) and
$`L_n(w) = -\frac1n \sum_i \log p(X_i \mid w)` (`empiricalNegativeLogLikelihood`), these are
$`K = L - L(w_0)` and $`K_n = L_n - L_n(w_0)`.

::::

::::definition "def:rfv" (lean := "SingularLearningTheory.RelativelyFiniteVariance")
%%%
paperIdentity := some { label := "[Wat18, Definition 7]", href := "https://doi.org/10.1201/9781315373010" }
%%%
The pair $`(q, p)` has *relatively finite variance* if there is $`c > 0` such that, for every
optimal parameter $`w_0` and every $`w \in W`,
$$`\mathbb{E}_q\bigl[f(X, w)^2\bigr] \le c\, \mathbb{E}_q\bigl[f(X, w)\bigr], \qquad
  f(x, w) = \log \frac{p(x \mid w_0)}{p(x \mid w)}.`

`RelativelyFiniteVariance q p w₀ W` asks this at the one reference parameter `w₀`, in the form
$`C\, \mathbb{E}_q[f(X, w)^2] \le K(w)` with $`C > 0`, together with $`f(\cdot, w) \in L^2(q)`
for every $`w \in W`. This is the hypothesis that replaces realizability in every theorem of the
library ({ref "conv-rfv"}[]).

::::

# Statistical estimation methods (§1.3)

::::definition "def:evidence" (lean := "SingularLearningTheory.evidence, SingularLearningTheory.freeEnergy, SingularLearningTheory.normalizedEvidence, SingularLearningTheory.posteriorMeasure")
%%%
paperIdentity := some { label := "[Wat09, §1.3.1, eqs. (1.10), (1.11)]; [Wat09, Definition 6.2, eq. (6.12)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
At inverse temperature $`\beta > 0` the *evidence* (marginal likelihood) is
$$`Z_n = \int \prod_{i=1}^{n} p(X_i \mid w)^{\beta}\, \varphi(w)\,dw`
(eq. (1.10)), the *normalized evidence* is
$$`Z_n^0 = \int \exp\bigl(-n\beta K_n(w)\bigr)\, \varphi(w)\,dw`
(eq. (1.11)), and the *stochastic complexities* (free energies) are $`F_n = -\log Z_n` and
$`F_n^0 = -\log Z_n^0`. The *a posteriori distribution* is the prior reweighted by
$`\exp(-n\beta K_n(w))` and normalized, and the *predictive density* is
$`p^*(x) = \int p(x \mid w)\, p(w \mid D_n)\,dw`.

The library has `evidence p W φ β Xs n ω` $`= \int_W e^{-n\beta L_n(w)} \varphi(w)\,dw = Z_n`,
`freeEnergy` $`= F_n`, `normalizedEvidence p w₀ W φ β Xs n ω` $`= Z_n^0` with $`K_n` measured
from $`w_0`, and the tempered posterior `posteriorMeasure`, the measure
$`e^{-n\beta K_n(w)} \varphi(w)\,dw / Z_n^0` on $`W`. $`F_n^0` is the
library's `normalizedFreeEnergy` ({bpref "def:FR"}[]).

:::unformalised (missing := statement)
The predictive density $`p^*(x)` is not defined.
:::

::::

::::definition "def:1_8"
%%%
paperIdentity := some { label := "[Wat09, Definition 1.8]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The *Bayes quartet*: the Bayes generalization error $`B_g = K(q \,\|\, p^*)`, the Bayes training
error $`B_t = \frac{1}{n}\sum_i \log \frac{q(X_i)}{p^*(X_i)}`, the Gibbs generalization error
$`G_g = \mathbb{E}_w[K(w)]` and the Gibbs training error $`G_t = \mathbb{E}_w[K_n(w)]`, the last
two expectations over the a posteriori distribution.

:::unformalised (missing := statement)
The quartet through the predictive density is not defined. The library's quartet is that of
{bpref "def:6_5"}[Definition 6.5], measured from the reference parameter $`w_0`; the theorems of
§6.3 are stated for it.
:::
::::

# The sample (§1.7)

::::definition "def:sample" (lean := "SingularLearningTheory.IsIIDSample")
%%%
paperIdentity := some { label := "[Wat09, §1.1.1, §1.7]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The sample $`D_n = (X_1, \dots, X_n)` is drawn independently from the true distribution
$`q(x)\,dx`. The limit theorems take the sample as an infinite sequence of random variables
`Xs : ℕ → Ω → X` on a probability space `(Ω, P)`, of which the statistics at size $`n` use the
first $`n`: `IsIIDSample q Xs P` says each $`X_i` has law $`q` (`measurePreserving`) and the
$`X_i` are independent (`indep`).

::::

# The four main formulas (§1.4, §1.5)

The book states its four main results informally in §1.4 and restates them in §1.5 under
"natural conditions"; the rigorous versions are Main Theorems 6.1–6.4 of Chapter 6.

- Main Formula I (standard form of the log likelihood ratio): {bpref "mf:I"}[].
- Main Formula II (asymptotics of the stochastic complexity): {bpref "mf:II"}[].
- Main Formula III (equations of state of the Bayes quartet): {bpref "mainthm:6_3"}[].
- Main Formula IV (maximum likelihood and a posteriori): {bpref "mainthm:6_4:2"}[].
