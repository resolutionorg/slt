# Blueprint: *Algebraic Geometry and Statistical Learning Theory*

A Verso Blueprint document over the library `slt`, following Watanabe, *Algebraic Geometry and
Statistical Learning Theory* (2009): one page per book chapter, a node per definition and main
theorem linked by name to the library's declaration, with the book's numbering on every node. It
is reference-only: it describes the declarations as they are and never restates them.

The library states the book's theorems under relatively finite variance (Watanabe 2018,
Definition 7) in place of realizability. An item of the book that the library does not state
has a node without a declaration, marked *Unformalised*, or *Out of scope* when it assumes
realizability in a way relatively finite variance does not support.

## Building

```sh
lake build Blueprint      # elaborates the chapters against slt
lake exe vbp build        # writes _out/site/html-multi; add --serve to preview
```

`packagesDir = "../.lake/packages"` shares slt's dependency checkouts. The package, named
`Blueprint`, requires slt (`..`) and the Timaeus fork of verso-blueprint.

## Annotations

For the statements of `SLTChallenge`, how a statement relates to the book is written once, in the
docstring of the declaration (in `SLTChallenge/` and in its counterpart in `SLT/`, word for word): a
section headed by the line `Relation to the source.`, followed by Markdown bullets, each beginning
with a bold label. The labels are the fork's editorial kinds, chosen by three questions in order:

- Does the book's item have a formal counterpart? If not: `**Unformalised.**` (a statement or
  proof is missing) or `**Out of scope.**` (none is owed, by decision).
- Is the book's claim true as printed? If false: `**Correction.**` (the hypothesis it needs is
  added, and the corrected version stated). If underspecified: `**Interpretation.**` (the library
  fixes one reading).
- For a true claim, how do the statements compare? `**Restatement.**` (logically equivalent),
  `**Strengthening.**` (the formal statement implies the book's) or `**Gap.**` (weaker or
  incomparable).

`**Translation.**` is a dictionary entry (this Lean expression is the book's such-and-such),
whatever the answers, and `**Formalisation note.**` the fallback for a remark that is none of
these. An item may continue on indented lines and may use inline code, inline LaTeX `$...$` and
citations `[Wat09, Theorem 6.7]` with the keys of `../references.bib`. An item shared by many
theorems is written once, at the definition it concerns (`StandingAssumptions`,
`RelativelyFiniteVariance`, `ZeroSetConditions`), not repeated at each theorem.

The fork renders the items of every declaration embedded at a node as annotation boxes after the
node's text. Two kinds of node carry hand-written directives (`:::restatement`, `:::unformalised`,
and so on) instead: a node whose declarations are in the library but not in `SLTChallenge`, whose
docstrings carry no relation section, and a node with no declaration. The appendix
`Blueprint/Conventions.lean` explains the kinds to the reader, and so does the label of each box:
hovering it shows its kind's one-sentence explanation, from `annotation-labels.js` (styled by
`annotation-labels.css`), which `Main.lean` inlines in every page.

Citations in the chapters use `{cite Wat09}[Theorem 6.7]`, registered from `../references.bib` by
`Blueprint/References.lean`; `{blueprint_bibliography}` lists the cited entries.

Placement: node-to-node references use `{bpref "label"}`. General matters are sections of the
appendix, referenced with `{ref "conv-…"}`.