# Lean supplementary development

**Author:** Idris Ali Shaik

This directory contains the `CollatzEndpointTransport` Lean 4 formalization
accompanying the natural-density Collatz descent manuscript.

The default build recompiles the retained paper modules, constructs the
paper dependency report, and replays the public axiom report:

```bash
lake build
```

To print the dependency report directly:

```bash
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -DmaxHeartbeats=20000000 \
  CollatzEndpointTransport/Linear/PaperDependencyAudit.lean
```

To print the public axiom report directly:

```bash
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -DmaxHeartbeats=20000000 \
  CollatzEndpointTransport/Linear/PaperAudit.lean
```

The independently verified quadratic package is optional and is not imported
by the paper audit:

```bash
lake build QuadraticAppendix
```

The development is pinned to Lean `v4.15.0`; the exact Mathlib revision is
recorded in `lake-manifest.json`. Kernel dependencies, source-elaboration
references, imports, and trusted axioms are reported separately; see
`CollatzEndpointTransport/README.md`.

See `CollatzEndpointTransport/README.md` for the public theorem names and package
layout.

## License

The Lean source under `CollatzEndpointTransport/` is released under the Apache License 2.0; see
`LICENSE`. This license does not apply to manuscript text outside `lean/`.
