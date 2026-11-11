import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import SLT.Setting
import SLT.StandardForm

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SingularLearningTheory MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

#doc (Manual) "Conventions and general remarks" =>

Every difference between what the library states and what the book states is recorded as an
annotation inside the node it concerns, one annotation per item. This appendix explains the
annotation kinds and collects the matters that are general: conventions of the whole
formalisation and readings that every statement shares. Nothing here is specific to one
theorem, and no annotation anywhere is evidence that a statement corresponds to the book; the
annotations are the list of what a reader must weigh.

# Reading the annotations
%%%
tag := "conv-annotations"
%%%

The boxes under a node record how the Lean statement relates to the book. For the statements of
`SLTChallenge` they are written in the docstrings of the declarations the node presents, in a
section headed "Relation to the source.", one item per difference; the same text is what a reader
of the library's source sees. For a declaration of the library outside `SLTChallenge`, and for an
item of the book with no declaration, they are written at the node.

A *Translation* matches Lean notation with the book's. *Unformalised* marks an item of the book
with no Lean counterpart yet, *Out of scope* one left out by decision. A *Correction* repairs a
claim false as printed; an *Interpretation* fixes one reading of underspecified wording. A
*Restatement* is an equivalent form, a *Strengthening* implies the book's statement, and a *Gap*
is weaker or incomparable. A *Formalisation note* is a remark that fits none of these. Hovering a
label shows its explanation.

# Relatively finite variance
%%%
tag := "conv-rfv"
%%%

Book reference: every theorem of Chapter 6; {cite Wat18}[Definition 7].

The book assumes realizability: the true distribution is $`q = p(\cdot \mid w_0)` for some
parameter $`w_0`. The library assumes instead relatively finite variance at a reference parameter
$`w_0 \in W` ({bpref "def:rfv"}[]): $`C\, \mathbb{E}_q[f(X, w)^2] \le K(w)` on $`W` for some
$`C > 0`, where $`f(x, w) = \log(p(x \mid w_0)/p(x \mid w))` and $`K = \mathbb{E}_q f` are measured
from $`w_0` ({bpref "def:1_1"}[]). In the realizable case $`q = p(\cdot \mid w_0)` the library's
$`f`, $`K`, $`K_n` are the book's.

Measured from $`w_0`, every statement of the book keeps its form, with the empirical entropy
$`S_n` and the entropy $`S` replaced by the empirical and average log losses at the reference
parameter, $`L_n(w_0)` and $`L(w_0)`, and the Bayes and Gibbs errors measured relative to the
best model $`p(\cdot \mid w_0)` instead of $`q`. Relatively finite variance makes $`w_0` a
minimiser of $`K` and every other minimiser equivalent to it
({bpref "thm:essential_uniqueness"}[]), which is the role of the book's set of true parameters.

How relatively finite variance compares with realizability, and when it follows from it, is
the first item of the docstring of `StandingAssumptions` ({bpref "def:6_1"}[]).

# Real analyticity
%%%
tag := "conv-real_analytic"
%%%

Book reference: Definition 6.1 (1-a,b); Remark 5.5; Remark 6.1 (1).

Definition 6.1 (1) asks for an open $`W^{(C)} \subseteq \mathbb{C}^d` containing $`W` on which the
model is $`L^s(q)`-valued complex analytic. The library assumes the real form: $`L^s`-valued real
analyticity on an open real neighbourhood of $`W` (`LsValuedAnalytic`, {bpref "def:5_3"}[]). The
two are equivalent: Remark 6.1 (1) takes the real slice of the complex clause, and Remark 5.5
states the converse, that a real analytic $`L^s(q)`-valued function on an open real set is complex
analytic on some complex open set covering a given compact subset. The complex extension does work
in the book only in Remark 5.5 itself, where Cauchy's integral formula gives the Taylor
coefficient bounds used for the tightness of the empirical process; in Lean those bounds come from
the radius of convergence of the Banach-valued power series. The only complex variable of the
statements is the argument $`z` of the zeta function and of the Mellin transform.

# Pointwise continuity of the model
%%%
tag := "conv-continuity"
%%%

Book reference: Remark 5.7; Theorems 5.8, 5.9, 6.1, 6.7; Corollary 6.1; §6.3; §6.4.

Fundamental Condition (I) gives $`L^s(q)`-valued analyticity of $`w \mapsto f(\cdot, w)` and
nothing pointwise: changing $`f(\cdot, w)` on a $`q`-null set depending on $`w` leaves every
$`L^s` class unchanged and can destroy the continuity of $`f(x, \cdot)`. The book takes the
empirical process to be continuous for every sample (Remark 5.7). The library assumes instead
that $`f(x, \cdot)` is continuous on $`W` for $`q`-almost every $`x` (the field `continuousOn`
of `StandingAssumptions`, {bpref "def:6_1"}[], and the hypotheses `hf_cont`, `hcont`), which
makes the empirical process continuous almost surely. As far as is known the book's claims hold
without it, so each occurrence is a gap at its node.

# The sign of ξ
%%%
tag := "conv-sign"
%%%

Book reference: eqs. (1.18), (6.10), (6.11); Definition 5.6.

The book prints the standard form (6.10), $`K_n(g(u)) = u^{2k} - n^{-1/2} u^k \xi_n(u)`, with
$`\xi_n(u) = n^{-1/2} \sum_i (u^k - a(X_i, u))` as in eq. (1.18), and eq. (6.11) with the
opposite sign; one of the two is a misprint, recorded at {bpref "thm:6_2"}[Theorem 6.2]. The library's empirical
process (`empiricalProcess`, {bpref "def:empirical_process"}[]) and its limit $`\Psi` have the
centring $`a - \mathbb{E}[a]` of (6.11); the statements of Chapter 6 evaluate their limits at
$`\xi = -\Psi`, the sign of (6.10).

`-E.Ψlim ω'` for an `E : EmpiricalProcessLimit q a Xs P P'` is the book's limit process
$`\xi` of (6.10), and `empiricalProcess q a Xs n ω` is $`-\xi_n`.

# Integrals and integrability
%%%
tag := "conv-integrals"
%%%

Book reference: every expectation of §6.2–§6.4; {cite Wat18}[Definition 7].

Mathlib's Bochner integral is totalized: $`\int f\,d\mu` is $`0` when $`f` is not integrable, so
an equation or inequality between integrals says nothing about $`f` until `Integrable f μ` is
stated. The statements therefore carry `Integrable` conjuncts for the expectations they assert
to converge, and the hypotheses that compare integrals carry the integrability they need
(`MemLp` in relatively finite variance). These conjuncts are content the book leaves implicit.

`Integrable (fun ω ↦ …) P` next to a limit of integrals is the book's $`\mathbb{E}[\cdot]`
presupposing that the expectation exists; `∫ ω, … ∂P` is $`\mathbb{E}[\cdot]` itself.

# Names
%%%
tag := "conv-names"
%%%

The library's declarations are in the namespace `SingularLearningTheory`, with descriptive names
(`free_energy_formula`, `bayes_gibbs_convergence`); the book's numbering is in each theorem's
docstring, as its source statement, and on the nodes of this document. Names on the pages are
shown relative to the namespaces each page opens, as its legend says; links and hover keys keep
the canonical name.
