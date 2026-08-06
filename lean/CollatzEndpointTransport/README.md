# CollatzEndpointTransport Lean packages

**Author:** Idris Ali Shaik

The verified development is split by mathematical role.

- `Linear/Main.lean`: referee-facing theorem API for the central higher-Renyi
  endpoint-only theorem with exact nonattained endpoint
  `log (1 / a0) / log (2 / a0)`, re-exporting Corollary 1.5.
- `Linear/FirstPassageLaws.lean`: dedicated implementation of the uniform
  quantitative first-passage profile and its two limit laws in Corollary 1.5,
  re-exported by `Linear/Main.lean`.
- `Linear/PaperDependencyAudit.lean`: transitive compiled-declaration graph,
  `.ilean` source-reference graph, and manuscript-to-source map.
- `Linear/PaperAudit.lean`: public `#print axioms` report. This is a separate
  logical-trust check, not evidence of declaration reachability.
- `Linear/`: the main fixed-total endpoint-only proof, together with the
  stronger full-envelope companion theorem in its smaller exponent range.
- `Common/`: route-independent Collatz definitions, envelope and endpoint
  lemmas, parity/correction infrastructure, maximal-barrier initial-window
  estimates, and dyadic summation.
- `QuadraticAppendix/`: the independently verified maximal-barrier
  quadratic baseline (Theorem B and Corollaries B.1--B.3).

Build every retained `Common` and `Linear` module, including the main theorem
and the two audit modules:

```text
lake build
```

Build only the narrower referee-facing public axiom-audit target:

```text
lake build CollatzEndpointTransport.Linear.PaperAudit
```

These commands are not scope-equivalent. The full build is the source
reconstruction gate for the retained library; `PaperAudit` is the public
paper-declaration and axiom-report surface.

Print the dependency report directly:

```text
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -DmaxHeartbeats=20000000 \
  CollatzEndpointTransport/Linear/PaperDependencyAudit.lean
```

Print the separate axiom report directly:

```text
lake env lean -DautoImplicit=false -DrelaxedAutoImplicit=false \
  -DmaxHeartbeats=20000000 \
  CollatzEndpointTransport/Linear/PaperAudit.lean
```

The exact referee-facing Main Theorem declaration is
`CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_natural_density_descent`.
Its full-range timed and exceptional-count corollaries are
`collatz_central_renyi_endpoint_natural_density_descent_timed` and
`collatz_central_renyi_endpoint_exceptional_count`.
The quantitative fixed-power consequence is
`collatz_central_renyi_fixed_power_density`; it gives a density exponent
`c * alpha ^ beta` for every `beta` above the reciprocal headline endpoint,
with `c` and the orbit-power constant uniform in `alpha`.
The critical-moment baseline remains available as
`collatz_endpoint_only_natural_density_descent`, with endpoint
`log (1 / a0) / log (3 / a0)`.

## Paper-to-Lean theorem map

| Paper result | Lean declaration | Module |
|---|---|---|
| Theorem 3.8, fixed-total core | `CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_le` | `Linear/CentralRenyiReverse.lean` |
| Theorem 3.8, endpoint aggregate | `CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le` | `Linear/CentralRenyiShell.lean` |
| Proposition 6.3, centered-kernel identity | `CollatzEndpointTransport.FixedTotal.centralRenyiRatio_one_half_eq_unrestrictedReverseSpendRatio` | `Linear/CentralRenyiCore.lean` |
| Theorem 3.9 | `CollatzEndpointTransport.FixedTotal.collatzPullback_dense_centralRenyi` | `Linear/CentralRenyiPullback.lean` |
| Proposition 6.1 socket | `CollatzEndpointTransport.OptimizedLinearPullback.centralRenyiEndpointOnlyTheorem_of_transport` | `Linear/CentralRenyiEndpointOnly.lean` |
| Theorem 1.1 | `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_natural_density_descent` | `Linear/Main.lean` |
| Corollary 1.2 | `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_exceptional_count_at_exponent` | `Linear/Main.lean` |
| Corollary 1.3, timed descent | `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_natural_density_descent_timed` | `Linear/Main.lean` |
| Corollary 1.3, orbit-ceiling input | `CollatzEndpointTransport.OptimizedLinearPullback.iterate_le_endpointChain_ceiling` | `Linear/EndpointOnlyOrbit.lean` |
| Theorem 1.4, density and envelope data | `CollatzEndpointTransport.OptimizedLinearPullback.powerDescentSet_hasNaturalDensityOne`; `CollatzEndpointTransport.OptimizedLinearPullback.mem_powerDescentSet_data` | `Linear/OptimizedLinearDescentAssembly.lean` |
| Theorem 1.4, public orbit-minimum consequence | `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_stretched_log_natural_density_descent` | `Linear/Main.lean` |
| Explicit subpower form following Theorem 1.1 | `CollatzEndpointTransport.QuantitativeCollatzMain.explicitSubpowerExponent_pos`; `explicitSubpowerExponent_antitone`; `explicitSubpowerExponent_tendsto_zero`; `explicitSubpowerExponent_eventually_eq`; `collatz_explicit_subpower_natural_density_descent` | `Linear/Main.lean` |
| Corollary 1.5, uniform profile bound | `CollatzEndpointTransport.QuantitativeCollatzMain.powerDescentSet_firstPassage_profile_bound` | `Linear/FirstPassageLaws.lean` |
| Corollary 1.5, profile exceptional count | `CollatzEndpointTransport.OptimizedLinearPullback.powerDescentSet_badPrefix_eventually_le_stretched_log` | `Linear/OptimizedLinearExceptionalCount.lean` |
| Corollary 1.5, density-one limit laws | `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_almost_all_first_passage_laws` | `Linear/FirstPassageLaws.lean` |
| Corollary 1.6 | `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_fixed_power_density` | `Linear/Main.lean` |
| Critical baseline | `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_endpoint_only_natural_density_descent` | `Linear/Main.lean` |

Paper counters are intentionally confined to this table and
`Linear/PaperDependencyAudit.lean`. Ordinary Lean module and declaration
documentation uses semantic names so manuscript renumbering cannot make source
comments stale.

Corollary 1.3's combined timed-and-ceiling statement uses the two mapped
declarations in its row rather than one wrapper theorem. This distinction
prevents the theorem map from overstating the formal API.

The exact nonattained Theorem 1.1 endpoint is encoded as
`log (1 / a0) / log (2 / a0)`.

## What the dependency audit proves

`PaperDependencyAudit.lean` starts from the mapped declarations above and
constructs two closures. The kernel closure uses
`Name.transitivelyUsedConstants` on the compiled declaration types and proof
terms. The combined closure adds identifier references from Lean's `.ilean`
elaboration metadata. For each root it reports:

- the Lean declaration name;
- its defining module and source line;
- the number of reachable project declarations and modules in both closures;
- every transitive edge between mapped paper milestones.

It also reports the full transitive import closure and labels modules that
occur only at source-build time. This last category is legitimate: a helper
may be needed to elaborate an imported source module yet disappear from the
finished kernel term. Accordingly, the audit does not call import-only
modules mathematically reachable, and it does not call them unused. The
clean `lake build` is the gate for source reconstruction; the kernel closure
is the gate for theorem provenance; `.ilean` references connect source-level
uses to their parent declarations.

The report prints the current number of paper roots, compiled project
declarations, source/kernel declarations, and imported project modules. It
also identifies any elaboration-only or import-only project modules, so these
figures are replayed evidence rather than manually maintained documentation.

The report also performs the converse audit. It treats every theorem constant
exported by `Linear/Main.lean`, together with the mapped internal manuscript
milestones, as terminal roots. It then enumerates source-authored theorems in
the retained linear import closure and reports every theorem outside their
combined reverse closure individually by module and line.

That complement is intentional and is not described as part of the linear
proof closure. It contains shared declarations used by the separately built
quadratic package, exact phase-transition and affine-collision results worth
retaining as standalone mathematics, and small public simplification or
base-case lemmas that keep the definitions usable. Superseded proof branches
and a weaker generic fiber-refinement chain were removed during the cleanup.
The complement remains a reviewable maintenance inventory, not a logical or
axiomatic defect and not evidence that each retained theorem supports Theorem
1.1.

The milestone graph has two principal branches:

```text
fixed-total central moment
  -> endpoint aggregate
  -> central-Renyi pullback
  -> endpoint transport socket
  -> Theorem 1.1 and Corollaries 1.2, 1.3, 1.6

full-envelope parameter certificate + density core + envelope data
  -> Theorem 1.4 consequences and Corollary 1.5 profile/limits
```

`PaperAudit.lean` then runs `#print axioms` on the public declarations. Each
currently reports only `propext`, `Classical.choice`, and `Quot.sound`; that
report concerns the trusted axiom base, not the dependency graph.

Build the optional independent quadratic baseline:

```text
lake build QuadraticAppendix
```

Historical and open research modules are deliberately excluded from this
public artifact.
