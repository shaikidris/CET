# Quantitative Collatz Descent to Stretched-Logarithmic Scale in Natural Density 
CollatzEndpointTransport

**Author:** Idris Ali Shaik

**ORCID:** [0009-0009-9699-9712](https://orcid.org/0009-0009-9699-9712)

**Software DOI:** [10.5281/zenodo.21797535](https://doi.org/10.5281/zenodo.21797535)

This repository is the journal-neutral Lean 4 and Mathlib artifact accompanying
*Quantitative Collatz Descent to Stretched-Logarithmic Scale in Natural
Density*. It formalizes the half-Collatz map

```text
T(n) = n / 2       if n is even,
T(n) = (3n + 1)/2  if n is odd,
```

and the article's quantitative natural-density descent theorem. For every
exponent below the explicit nonattained endpoint

```text
log (1 / a0) / log (2 / a0),   a0 = (log2 3) / 2,
```

the formalized result gives

```text
min_k T^k(n) <= exp ((log n)^(1 - delta))
```

on a set of natural density one, together with quantitative exceptional-count,
timed-descent, fixed-power, full-envelope, and first-passage consequences. This
is an almost-all result. It does not prove the Collatz conjecture for every
initial value and does not exclude exceptional cycles or divergent trajectories.

## Artifact layout

- `lean/CollatzEndpointTransport/Common/`: shared Collatz, density, parity,
  affine-correction, and initial-window infrastructure.
- `lean/CollatzEndpointTransport/Linear/`: the article's fixed-total endpoint
  analysis, pullback, endpoint-only bootstrap, main API, and first-passage laws.
- `lean/CollatzEndpointTransport/Linear/PaperDependencyAudit.lean`: the
  declaration-level theorem-dependency and article-to-source audit.
- `lean/CollatzEndpointTransport/Linear/PaperAudit.lean`: the separate
  `#print axioms` audit for the article-facing declarations.
- `lean/CollatzEndpointTransport/QuadraticAppendix/`: an optional independently
  verified quadratic baseline, not imported by the principal article audit.

Exploratory branches, manuscript-format files, generated documents, raw
diagnostics, and internal research ledgers are deliberately excluded.

## Replay

The artifact is pinned to Lean `v4.15.0` and the Mathlib revision recorded in
`lean/lake-manifest.json`.

```bash
cd lean
lake exe cache get
lake build
lake build CollatzEndpointTransport.Linear.PaperAudit
lake build QuadraticAppendix
```

The default build reconstructs every retained `Common` and `Linear` module.
`PaperAudit` prints the axiom base for the article-facing declarations; it does
not replace the independent dependency audit. The optional `QuadraticAppendix`
target is intentionally outside the principal theorem chain.

The exact theorem map, dependency-audit interpretation, and direct replay
commands are documented in `lean/CollatzEndpointTransport/README.md`.

## Packaging

From a clean tagged commit, create the standalone software archive with:

```bash
python3 scripts/package_software.py --version 2.0.1 --ref v2.0.1
```

The script archives only this public formal artifact and prints its SHA-256 and
MD5 checksums. It does not publish, push, or modify a Git tag.
