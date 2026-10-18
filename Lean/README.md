
# Finite Bit Formalism (FBF)

Author: Manouchehr Amiri  
Affiliation: Independent Researcher

[![DOI](https://zenodo.org/badge/990585452.svg)](https://doi.org/10.5281/zenodo.23448233)
**Archived release:** v1.0.1  
**Version DOI:** https://doi.org/10.5281/zenodo.23448233 
Introduction

Finite Bit Formalism (FBF) is an axiomatic, information-based framework
for mathematical reasoning. Its geometric realization is called
**Finite Bit Geometry (FBG)**.

The central idea is that a mathematical entity can be represented by a
finite minimal set of information bits. Mathematical constructions 
produce equivalent representations without introducing new independent
information.

The present development focuses on two principal axioms.

## Axiom 1 — Information Invariance

A mathematical entity admits a minimal information representation.
Equivalent minimal representations preserve information content, and a
null operation cannot introduce a new independent bit.

Schematically,

\[
B \longrightarrow B'
\]

under an information-preserving null operation implies

\[
\operatorname{BitContent}(B)
=
\operatorname{BitContent}(B').
\]

## Axiom 3 — Emergence and Uniqueness

When independent information is adjoined to an existing mathematical
entity, the enlarged information structure determines a unique emergent
equivalent-bit class.

Schematically,

\[
B + A_{\mathrm{adjoined}}
\longrightarrow
E,
\]

where \(E\) is the unique emergent equivalent class associated with the
existing and independently adjoined information.

## FBF Reasoning

FBF distinguishes between:

- existing information bits,
- independent adjoined bits,
- dependent or equivalent bits,
- null operations,
- emergent equivalent-bit classes,
- and excess independent information.

A typical FBF proof has the form

\[
\text{assumed configuration}
\longrightarrow
\text{new feature}
\longrightarrow
\begin{cases}
\text{dependent origin},\\
\text{independent excess bit}.
\end{cases}
\]

Axiom 3 may exclude an inconsistent dependent origin, while Axiom 1
excludes the remaining possibility of an independent bit being generated
by a null construction.

## Finite Bit Geometry (FBG)

FBG applies the FBF axioms to straightedge-and-compass geometry.

The current development includes formal or manuscript-level treatments of:

- basic \(1:1\) constructions,
- triangle congruence,
- equality of opposed angles,
- construction of right angles,
- parallel-line constructions,
- Playfair's postulate,
- the Euclidean fifth postulate,
- concurrency of the medians,
- parallel proportionality,
- and information-based theorem-feasibility reasoning.

The median-concurrency proof illustrates the characteristic FBG method:

\[
\text{nonconcurrency}
\Rightarrow
\sigma,
\]

where \(\sigma\) is a hypothetical sideness bit.

Axiom 3 excludes a consistent dependent origin of \(\sigma\), so
\(\sigma\) must be independent. Axiom 1 then excludes its production by
the null median construction. Hence the medians must be concurrent.

## Formal Verification

The current formal development is primarily being carried out in
**Lean 4 / Mathlib**.

The Lean formalization includes:

- the FBF information structures,
- refined Axiom 1,
- Axiom 3 with emergence and uniqueness,
- geometric primitives,
- observer/sideness structures,
- Playfair uniqueness,
- median concurrency,
- and the parallel proportionality development.

For important theorems, Lean dependency audits are performed using

```lean
#check theorem_name
#print axioms theorem_name
```

For example, the median-concurrency and parallel-proportionality
developments compile without `sorryAx` in the current working
formalization.

Formal verification here means that the stated conclusions follow from
the explicitly encoded FBF axioms and domain-specific bridge facts. It
does not by itself assert that the FBF axioms are absolutely true.

## Repository Structure

```text
Finite-Bit-Formalism/
├── README.md
├── LICENSE
├── Coq/
│   └── historical Coq formalization
├── Lean/
│   └── current Lean formalization of FBF/FBG
├── docs/
│   └── explanatory documentation
└── manuscript/
    └── manuscript-related material
```

## Coq Formalization

The `Coq/` directory preserves an earlier formalization of FBF.

It is retained as part of the historical development of the framework.
The present axioms and geometric formalization have subsequently been
refined substantially.

## Lean Formalization

The `Lean/` directory is intended to contain the current formal
implementation.

The present development distinguishes carefully between:

1. definitions,
2. FBF axioms,
3. general reasoning principles,
4. geometric bridge facts,
5. and derived theorems.

This separation is intended to make the logical dependencies of each
FBG result explicit.

## No-Theorem Criterion

FBF also suggests a theorem-feasibility principle.

If the same existing and adjoined information permits two or more
inequivalent admissible emergent classes, then the supplied information
does not determine a unique theorem of the proposed form.

Additional information or structural conditions are then required to
restore uniqueness.

This is intended as a possible basis for theorem discovery and
feasibility analysis within FBF.

## Status

FBF/FBG is an active research program.

Some results have already been formalized in Lean, while others remain
at the manuscript or formalization-in-progress stage. The repository is
being developed so that every major claim can be associated with an
explicit dependency chain and, where possible, a machine-checked proof.

## Citation

A permanent citation and DOI for the current FBF/FBG release will be
added here after the corresponding archival release is deposited.

## License

See the `LICENSE` file for the repository license.



