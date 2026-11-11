import Verso
import VersoManual
import VersoBlueprint
import Blueprint.References
import SLT.Resolution
import SLT.SingularIntegrals
import SLT.SingularIntegrals.Zeta

open Verso.Genre
open Verso.Genre.Manual
open Informal
open SingularLearningTheory MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

set_option verso.blueprint.autoDeps true

#doc (Manual) "Singularity theory (Chapter 2)" =>

Chapter 2 supplies the resolution of singularities on which Chapter 6 rests. The library uses it
in one form, a global resolution of the loss over a neighbourhood of the parameter set
(`SLTResolution`, Theorem 2.8), from which Chapter 6 cuts the finitely many cube coordinates of
Theorem 6.5 (a chart family and its pieces). The learning coefficient of Definition 2.7 is
defined by the scaling of the prior volume of the sublevel sets of the loss, and identified with
the book's largest pole of the zeta function by Theorem 6.6.

# Resolution of singularities (§2.4)

::::theorem "thm:2_3"
%%%
paperIdentity := some { label := "[Wat09, Theorem 2.3]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(Hironaka). Let $`f` be a real analytic function on a neighbourhood of a compact set of
$`\mathbb{R}^d`, not identically zero, with $`f(w) = 0` somewhere. There are a real analytic
manifold $`M` and a proper real analytic map $`g : M \to \mathbb{R}^d`, an isomorphism off the
zero set of $`f`, such that around every point of $`M` there are local coordinates in which
$`f(g(u)) = \pm u_1^{k_1} \cdots u_d^{k_d}` and the Jacobian determinant of $`g` is
$`b(u)\, u_1^{h_1} \cdots u_d^{h_d}` with $`b` nonvanishing.

The library has no statement of Theorem 2.3 itself. Its resolution theorem is Theorem 2.8
({bpref "thm:2_8"}[]), whose proof uses the formalisation of Hironaka's theorem in the hironaka
package as a proved theorem, never as an axiom or as a hypothesis of a theorem of the library.
::::

::::definition "def:sltresolution" (lean := "SingularLearningTheory.SLTResolution, SingularLearningTheory.SLTChart, SingularLearningTheory.SLTChart.rlct, SingularLearningTheory.SLTChart.mult, SingularLearningTheory.SLTChart.openCube, SingularLearningTheory.SLTChart.IsAdmissible, SingularLearningTheory.openOrthant, SingularLearningTheory.reflectOrthant")
%%%
paperIdentity := some { label := "[Wat09, Theorem 2.8 (the resolution map)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
An `SLTResolution K φ W` is a resolution of the loss $`K` with prior density $`\varphi` over an
open neighbourhood $`U` of the parameter set $`W` (the field `U`): a real analytic manifold `M`
and a proper real analytic map $`\pi : M \to \mathbb{R}^d` onto $`U`, an analytic isomorphism off
a null set containing the zeros of $`K` (`exceptional`), with an `SLTChart` around every point
$`z` of $`M` over a zero of $`K` in $`W`. A chart is a member of the analytic atlas of $`M`
centred at $`z`, containing the closed cube $`[-r, r]^d` in its target, in which

- $`K(\pi(u)) = u^{2k}` exactly, with some $`k_j > 0` (`loss_eq`, `active`);
- over $`W`, the pulled-back prior density is a positive smooth unit times a monomial,
  $`\varphi(\pi(u))\,|\det \pi'(u)| = c(u)\,|u^h|` (`density_eq`);
- on each open orthant of the cube, $`\pi` lands entirely in the interior of $`W` or entirely
  outside $`W` (`orthant_dichotomy`); the orthants of the first kind are *admissible*.

The chart's learning coefficient and multiplicity are those of its monomial,
$`\lambda = \min_{k_j > 0} (h_j + 1)/(2k_j)` and the number of coordinates attaining it
(`SLTChart.rlct`, `SLTChart.mult`).

::::

::::theorem "thm:2_8" (lean := "SingularLearningTheory.exists_sltResolution")
%%%
paperIdentity := some { label := "[Wat09, Theorem 2.8]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
(Simultaneous resolution of singularities.) Let $`f_0, \dots, f_k` be real analytic functions
near the origin of $`\mathbb{R}^d`, each vanishing at the origin and not constant. There are an
open $`W \ni 0`, a real analytic manifold $`U` and a proper real analytic map $`g : U \to W`, an
analytic isomorphism off the zeros of the $`f_i`, such that around every point over a zero there
are local coordinates in which $`f_0(g(u)) = u^{k_0}`, $`f_i(g(u)) = a_i(u)\,u^{k_i}` and
$`g'(u) = b(u)\,u^h` with nonvanishing analytic $`a_i`, $`b`.

`exists_sltResolution`: if $`W` is semianalytic, $`K` is real analytic and nonnegative on an open
$`U \supseteq W` and not identically zero near any point of $`U`, and on $`U` the prior factors as
$`\varphi = \varphi_1 \varphi_2` with $`\varphi_1 > 0` smooth and $`\varphi_2` real analytic,
nonnegative on $`W` and not identically zero near any point of $`U`, then there is an
`SLTResolution K φ W` ({bpref "def:sltresolution"}[]) over an open subset of $`U`.

::::

::::definition "def:2_7" (lean := "SingularLearningTheory.IsSingularityType, SingularLearningTheory.zetaFunction")
%%%
paperIdentity := some { label := "[Wat09, Definition 2.7, Definition 6.4]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The *real log canonical threshold* of a real analytic $`f` on a compact set $`C` is read off the
resolutions of Theorem 2.3 at the zeros $`P \in C` of $`f`, with $`f(g(u)) = \pm u^k` and
$`g'(u) = b(u)\,u^h`:
$$`\Lambda(C) = \inf_{P \in C} \min_{1 \le j \le d} \frac{h_j + 1}{k_j}.`
Definition 6.4 defines the pair $`(\lambda, m)` of a loss $`K` and a prior $`\varphi` as the
largest pole of $`\zeta(z) = \int K(w)^z \varphi(w)\,dw` and its order.

`IsSingularityType K φ W λ m` defines the pair by volume scaling instead: there are
$`c_1, c_2 > 0` with
$$`c_1\, \varepsilon^\lambda (-\log \varepsilon)^{m-1} \le \int_{W \cap \{K \le \varepsilon\}} \varphi
  \le c_2\, \varepsilon^\lambda (-\log \varepsilon)^{m-1}`
for all small $`\varepsilon > 0`. The zeta function is `zetaFunction K φ W`
$`= \int_W K(w)^z \varphi(w)\,dw`. It agrees with both of the book's: `SLTResolution.isSingularityType` identifies it with the pair
read off a resolution ({bpref "def:6_4"}[]), and under the hypotheses of
{bpref "thm:6_6"}[Theorem 6.6] the singularity type exists and $`-\lambda` is the largest pole of
the continuation of `zetaFunction K φ W`, of order $`m`, and by {bpref "thm:2_4"}[Theorem 2.4] the
singularity type is unique.

::::

::::theorem "thm:2_4" (lean := "SingularLearningTheory.singularity_type_unique, SingularLearningTheory.SLTResolution.isSingularityType")
%%%
paperIdentity := some { label := "[Wat09, Theorem 2.4]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
The real log canonical threshold does not depend on the resolution used to compute it.

`singularity_type_unique`: two pairs $`(\lambda, m)`, $`(\lambda', m')` that are both the
singularity type of $`(K, \varphi)` on $`W` ({bpref "def:2_7"}[]) are equal. Since
`SLTResolution.isSingularityType` shows that the pair read off any resolution is the singularity
type ({bpref "def:6_4"}[]), the pairs read off any two resolutions agree.

::::

# The local coordinates of Theorem 6.5

::::definition "def:chart_family" (lean := "SingularLearningTheory.SLTResolution.resolvedParameterSet, SingularLearningTheory.SLTResolution.ChartFamily, SingularLearningTheory.SLTResolution.ChartFamily.sublevel, SingularLearningTheory.SLTResolution.ChartFamily.Piece, SingularLearningTheory.SLTResolution.ChartFamily.Piece.map, SingularLearningTheory.SLTResolution.ChartFamily.Piece.point, SingularLearningTheory.SLTResolution.ChartFamily.Piece.densityUnit, SingularLearningTheory.cube")
%%%
paperIdentity := some { label := "[Wat09, Theorem 6.5 (1), (2)]", href := "https://doi.org/10.1017/CBO9780511800474" }
%%%
Theorem 6.5 covers $`g^{-1}(W_\varepsilon)`, $`W_\varepsilon = \{w \in W : K(w) \le \varepsilon\}`,
by finitely many local coordinates $`\mathcal{M}_\alpha = [0, b]^d` with
$`K(g(u)) = u^{2k}` on each.

The library cuts these from a resolution `R` ({bpref "def:sltresolution"}[]) in two steps. The
*resolved parameter set* is $`\widetilde W = \overline{\pi^{-1}(\operatorname{int} W)}`
(`resolvedParameterSet`). A `ChartFamily` of `R` is a finite family of charts of `R` whose open
cubes cover $`\widetilde W \cap \pi^{-1}\{K \le \delta\}` for some $`\delta > 0` (`sublevel`).
A *piece* of the family is a chart together with an admissible orthant, reflected onto the cube
$`[0, r]^d` (`cube d r`); its map `Piece.map` $`= g_\alpha : [0, r]^d \to \mathbb{R}^d` is the
book's chart map, with $`K(g_\alpha(u)) = u^{2k_\alpha}` and the prior density
$`c_\alpha(u)\,u^{h_\alpha}` (`Piece.densityUnit`) on it. The pieces are the book's
$`\mathcal{M}_\alpha`.

::::
