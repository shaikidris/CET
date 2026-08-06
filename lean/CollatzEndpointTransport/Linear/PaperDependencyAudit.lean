/-
Copyright (c) 2026 Idris Ali Shaik. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik
-/
import CollatzEndpointTransport.Linear.Main
import ImportGraph.RequiredModules
import Lean.DeclarationRange
import Lean.Server.References

/-!
# Manuscript dependency audit

Declaration-level dependency audit for the accompanying manuscript.

An import graph and `#print axioms` answer different questions from this file:

* imports show what was available while a module compiled;
* axioms show the trusted logical principles in a finished declaration;
* the kernel graph follows constants retained in compiled declaration types and
  proof terms;
* the source graph follows identifier uses retained in Lean's `.ilean`
  elaboration metadata, including helpers that disappear from the final proof
  term.

For every referee-facing root below, the audit reports its source module and
line, the sizes of its kernel and combined source/kernel closures, and their
project-module counts. It also prints the transitive dependency relation
between the mapped roots.

The final reverse-reachability pass treats every theorem declared in
`Linear.Main`, together with the mapped internal manuscript milestones, as a
public root. It then enumerates every theorem in the retained imported project
modules and reports whether that theorem occurs in the combined dependency
closure of at least one public root. This is the declaration-level check that
distinguishes a genuinely supporting theorem from a theorem that merely
happens to live in an imported file.

The audit requires `.ilean` metadata for every imported project module. Imports
used only by syntax or tactic elaboration may still be absent from both
declaration closures, so the ordinary clean build remains a separate required
gate. Such modules are reported, not rejected.
-/

open Lean Elab Command

private structure PaperRoot where
  paperLabel : String
  decl : Name

private def paperRoots : Array PaperRoot := #[
  ⟨"Theorem 3.8 (fixed-total core)",
    `CollatzEndpointTransport.FixedTotal.fixedRenyiMoment_central_le⟩,
  ⟨"Theorem 3.8 (endpoint aggregate)",
    `CollatzEndpointTransport.FixedTotal.centralEndpointInformation_le⟩,
  ⟨"Proposition 6.3 (critical-kernel identity)",
    `CollatzEndpointTransport.FixedTotal.centralRenyiRatio_one_half_eq_unrestrictedReverseSpendRatio⟩,
  ⟨"Theorem 3.9 (central Renyi pullback)",
    `CollatzEndpointTransport.FixedTotal.collatzPullback_dense_centralRenyi⟩,
  ⟨"Proposition 6.1 (endpoint transport socket)",
    `CollatzEndpointTransport.OptimizedLinearPullback.centralRenyiEndpointOnlyTheorem_of_transport⟩,
  ⟨"Theorem 1.1 (exact endpoint identity)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.centralRenyiEndpointAdmissibleExponent_eq_paper⟩,
  ⟨"Theorem 1.1 (natural-density descent)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_natural_density_descent⟩,
  ⟨"Explicit subpower form (descent)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_explicit_subpower_natural_density_descent⟩,
  ⟨"Explicit subpower form (positive exponent)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.explicitSubpowerExponent_pos⟩,
  ⟨"Explicit subpower form (antitone exponent)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.explicitSubpowerExponent_antitone⟩,
  ⟨"Explicit subpower form (exponent tends to zero)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.explicitSubpowerExponent_tendsto_zero⟩,
  ⟨"Explicit subpower form (eventual explicit formula)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.explicitSubpowerExponent_eventually_eq⟩,
  ⟨"Corollary 1.5 (uniform first-passage profile)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.powerDescentSet_firstPassage_profile_bound⟩,
  ⟨"Corollary 1.5 (profile exceptional count)",
    `CollatzEndpointTransport.OptimizedLinearPullback.powerDescentSet_badPrefix_eventually_le_stretched_log⟩,
  ⟨"Corollary 1.5 (first-passage limits)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_almost_all_first_passage_laws⟩,
  ⟨"Theorem 1.1 (certified decimal range)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_decimal_natural_density_descent⟩,
  ⟨"Corollary 1.2 (optimized exceptional count)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_exceptional_count_at_exponent⟩,
  ⟨"Corollary 1.3 (timed descent)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_natural_density_descent_timed⟩,
  ⟨"Corollary 1.3 (timed exceptional count)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_endpoint_timed_exceptional_count⟩,
  ⟨"Corollary 1.6 (fixed-power density)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_central_renyi_fixed_power_density⟩,
  ⟨"Critical-moment endpoint baseline",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_endpoint_only_natural_density_descent⟩,
  ⟨"Orbit-ceiling estimate (6.10)",
    `CollatzEndpointTransport.OptimizedLinearPullback.iterate_le_endpointChain_ceiling⟩,
  ⟨"Full-envelope parameter certificate",
    `CollatzEndpointTransport.OptimizedLinearPullback.exists_optimized_linear_parameters⟩,
  ⟨"Theorem 1.4 (density core)",
    `CollatzEndpointTransport.OptimizedLinearPullback.powerDescentSet_hasNaturalDensityOne⟩,
  ⟨"Theorem 1.4 (full-envelope data)",
    `CollatzEndpointTransport.OptimizedLinearPullback.mem_powerDescentSet_data⟩,
  ⟨"Theorem 1.4 (orbit-minimum consequence)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_stretched_log_natural_density_descent⟩,
  ⟨"Theorem 1.4 (timed consequence)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_stretched_log_natural_density_descent_timed⟩,
  ⟨"Theorem 1.4 (exceptional count)",
    `CollatzEndpointTransport.QuantitativeCollatzMain.collatz_stretched_log_exceptional_count⟩
]

private def isProjectDecl (n : Name) : Bool :=
  `CollatzEndpointTransport |>.isPrefixOf n

private def isProjectModule (n : Name) : Bool :=
  `CollatzEndpointTransport |>.isPrefixOf n

private def mainModule : Name :=
  `CollatzEndpointTransport.Linear.Main

private def declarationLine (decl : Name) : CommandElabM Nat := do
  match ← findDeclarationRanges? decl with
  | some ranges => pure ranges.range.pos.line
  | none => pure 0

private def projectClosure (root : Name) : CommandElabM NameSet := do
  let used ← liftCoreM <| root.transitivelyUsedConstants
  pure <| used.fold (init := {}) fun acc decl =>
    if isProjectDecl decl then acc.insert decl else acc

private def sourceReferenceEdges
    (modules : List Name) : CommandElabM (Array (Name × Name)) := do
  let searchPath ← liftIO searchPathRef.get
  let mut edges : Array (Name × Name) := #[]
  for moduleName in modules do
    let some path ← liftIO <| searchPath.findModuleWithExt "ilean" moduleName
      | throwError m!"Missing .ilean metadata for imported project module {moduleName}"
    let ilean ← liftIO <| Server.Ilean.load path
    for (ident, info) in ilean.references.toArray do
      let dependency ← match ident with
        | .const _ identName => pure identName.toName
        | .fvar .. => continue
      if isProjectDecl dependency then
        for usage in info.usages do
          if let some parent := usage.parentDecl? then
            let source := parent.name.toName
            if isProjectDecl source then
              edges := edges.push (source, dependency)
  pure edges

private partial def combinedClosureFrom
    (env : Environment) (sourceEdges : Array (Name × Name))
    (roots : List Name) : NameSet :=
  go roots {}
where
  go (pending : List Name) (seen : NameSet) : NameSet :=
    match pending with
    | [] => seen
    | current :: rest =>
        if seen.contains current then
          go rest seen
        else
          let seen := seen.insert current
          let kernelDependencies := match env.find? current with
            | some info => info.getUsedConstantsAsSet
            | none => {}
          let pending := kernelDependencies.fold (init := rest) fun todo dependency =>
            if isProjectDecl dependency && !seen.contains dependency then
              dependency :: todo
            else
              todo
          let pending := sourceEdges.foldl (init := pending) fun todo edge =>
            if edge.1 == current && !seen.contains edge.2 then edge.2 :: todo else todo
          go pending seen

private def combinedClosure
    (env : Environment) (sourceEdges : Array (Name × Name))
    (root : Name) : NameSet :=
  combinedClosureFrom env sourceEdges [root]

private def projectModulesFor
    (env : Environment) (decls : NameSet) : NameSet :=
  decls.fold (init := {}) fun modules decl =>
    match env.getModuleFor? decl with
    | some moduleName => modules.insert moduleName
    | none => modules

private def theoremDeclarationsIn
    (env : Environment) (modules : NameSet) : Array Name :=
  env.constants.toList.foldl (init := #[]) fun declarations entry =>
    let (decl, info) := entry
    match info with
    | .thmInfo _ =>
        match env.getModuleFor? decl with
        | some moduleName =>
            if isProjectDecl decl && modules.contains moduleName then
              declarations.push decl
            else
              declarations
        | none => declarations
    | _ => declarations

private def theoremDeclarationsInModule
    (env : Environment) (moduleName : Name) : Array Name :=
  theoremDeclarationsIn env (({} : NameSet).insert moduleName)

elab "#paper_dependency_audit" : command => do
  let env ← getEnv
  let importedProjectModules := env.header.moduleNames.toList
    |>.filter isProjectModule
    |>.mergeSort Name.lt
  let sourceEdges ← sourceReferenceEdges importedProjectModules
  let mut closures : Array (PaperRoot × NameSet × NameSet) := #[]
  let mut unionKernelDecls : NameSet := {}
  let mut unionCombinedDecls : NameSet := {}

  for root in paperRoots do
    discard <| getConstInfo root.decl
    let kernelClosure ← projectClosure root.decl
    let combined := combinedClosure env sourceEdges root.decl
    closures := closures.push (root, kernelClosure, combined)
    unionKernelDecls := kernelClosure.fold (init := unionKernelDecls) fun acc decl =>
      acc.insert decl
    unionCombinedDecls := combined.fold (init := unionCombinedDecls) fun acc decl => acc.insert decl

    let kernelModules := projectModulesFor env kernelClosure
    let combinedModules := projectModulesFor env combined
    let moduleName := (env.getModuleFor? root.decl).getD `unknown
    let line ← declarationLine root.decl
    logInfo m!"PAPER_ROOT\t{root.paperLabel}\t{root.decl}\t{moduleName}:{line}\t\
      KERNEL_DECLS={kernelClosure.size}\tKERNEL_MODULES={kernelModules.size}\t\
      COMBINED_DECLS={combined.size}\tCOMBINED_MODULES={combinedModules.size}"

  logInfo m!"PAPER_GRAPH_ROOTS\t{paperRoots.size}"
  for (root, _, closure) in closures do
    for dependency in paperRoots do
      if root.decl != dependency.decl && closure.contains dependency.decl then
        logInfo m!"PAPER_COMBINED_TRANSITIVE_EDGE\t{root.paperLabel}\t{dependency.paperLabel}"

  let kernelModules := projectModulesFor env unionKernelDecls
  let combinedModules := projectModulesFor env unionCombinedDecls
  let elaborationOnlyModules := combinedModules.toList
    |>.filter (!kernelModules.contains ·)
    |>.mergeSort Name.lt
  let importOnlyModules := importedProjectModules
    |>.filter (!combinedModules.contains ·)
    |>.mergeSort Name.lt

  logInfo m!"PAPER_KERNEL_PROJECT_DECLARATIONS\t{unionKernelDecls.size}"
  logInfo m!"PAPER_KERNEL_PROJECT_MODULES\t{kernelModules.size}"
  logInfo m!"PAPER_COMBINED_PROJECT_DECLARATIONS\t{unionCombinedDecls.size}"
  logInfo m!"PAPER_COMBINED_PROJECT_MODULES\t{combinedModules.size}"
  logInfo m!"PAPER_GRAPH_IMPORTED_MODULES\t{importedProjectModules.length}"
  logInfo m!"PAPER_SOURCE_REFERENCE_EDGES\t{sourceEdges.size}"
  for moduleName in elaborationOnlyModules do
    logInfo m!"PAPER_ELABORATION_ONLY_MODULE\t{moduleName}"
  for moduleName in importOnlyModules do
    logInfo m!"PAPER_IMPORT_ONLY_MODULE\t{moduleName}"

  /-
  Reverse reachability from every theorem exported by `Linear.Main` and every
  mapped internal manuscript milestone. This is intentionally broader than
  either root class alone: terminal public corollaries and manuscript-level
  internal results are roots in their own right and must not be classified as
  unused merely because no other mapped theorem depends on them.
  -/
  let mainTheorems := theoremDeclarationsInModule env mainModule
  let publicRootSet := paperRoots.foldl
    (init := mainTheorems.foldl (init := ({} : NameSet)) fun roots root =>
      roots.insert root) fun roots root => roots.insert root.decl
  let publicRootNames := publicRootSet.toList
  let importedModuleSet := importedProjectModules.foldl
    (init := ({} : NameSet)) fun modules moduleName => modules.insert moduleName
  let retainedTheorems := theoremDeclarationsIn env importedModuleSet
  let mainReachableDecls := combinedClosureFrom env sourceEdges publicRootNames

  let unreachableTheorems := retainedTheorems.filter fun theoremName =>
    !mainReachableDecls.contains theoremName
  let mut sourceTheorems : Array Name := #[]
  let mut sourceUnreachableTheorems : Array Name := #[]
  for theoremName in retainedTheorems do
    let line ← declarationLine theoremName
    if line > 0 then
      sourceTheorems := sourceTheorems.push theoremName
      if !mainReachableDecls.contains theoremName then
        sourceUnreachableTheorems := sourceUnreachableTheorems.push theoremName
  logInfo m!"MAIN_FILE_THEOREMS\t{mainTheorems.size}"
  logInfo m!"PUBLIC_TERMINAL_ROOTS\t{publicRootNames.length}"
  logInfo m!"RETAINED_PROJECT_THEOREMS\t{retainedTheorems.size}"
  logInfo m!"RETAINED_SOURCE_THEOREMS\t{sourceTheorems.size}"
  logInfo m!"MAIN_REACHABLE_PROJECT_DECLARATIONS\t{mainReachableDecls.size}"
  logInfo m!"MAIN_UNREACHABLE_PROJECT_THEOREMS\t{unreachableTheorems.size}"
  logInfo m!"MAIN_UNREACHABLE_SOURCE_THEOREMS\t{sourceUnreachableTheorems.size}"

  for moduleName in importedProjectModules do
    let moduleTheorems := theoremDeclarationsInModule env moduleName
    let mut moduleSourceTheorems : Array Name := #[]
    let mut sourceUnreachableInModule : Array Name := #[]
    for theoremName in moduleTheorems do
      let line ← declarationLine theoremName
      if line > 0 then
        moduleSourceTheorems := moduleSourceTheorems.push theoremName
        if !mainReachableDecls.contains theoremName then
          sourceUnreachableInModule := sourceUnreachableInModule.push theoremName
    if !moduleSourceTheorems.isEmpty then
      logInfo m!"MAIN_REACHABILITY_MODULE\t{moduleName}\t\
        SOURCE_THEOREMS={moduleSourceTheorems.size}\t\
        REACHABLE={moduleSourceTheorems.size - sourceUnreachableInModule.size}\t\
        UNREACHABLE={sourceUnreachableInModule.size}"
    for theoremName in sourceUnreachableInModule do
      let line ← declarationLine theoremName
      logInfo m!"MAIN_UNREACHABLE_SOURCE_THEOREM\t{moduleName}:{line}\t{theoremName}"

#paper_dependency_audit
