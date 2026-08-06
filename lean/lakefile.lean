import Lake
open Lake DSL

package CollatzEndpointTransport where
  leanOptions := #[
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.15.0"

@[default_target]
lean_lib CollatzEndpointTransport where
  -- Increase heartbeats only for project modules. Keeping this option off the
  -- package prevents a clean replay from invalidating Mathlib's build cache.
  moreLeanArgs := #["-DmaxHeartbeats=20000000"]
  globs := #[
    .submodules `CollatzEndpointTransport.Common,
    .submodules `CollatzEndpointTransport.Linear
  ]

/-- Optional fully verified quadratic baseline, retained as an appendix
package but excluded from the default endpoint-only build. -/
lean_lib QuadraticAppendix where
  moreLeanArgs := #["-DmaxHeartbeats=20000000"]
  globs := #[.submodules `CollatzEndpointTransport.QuadraticAppendix]
