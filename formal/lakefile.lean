import Lake
open Lake DSL

package PcsOpenGolf where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩
  ]

require VCVio from git
  "https://github.com/Verified-zkEVM/VCVio" @ "25f26bfee60d6700644eb1a69f091091948f15da"

require «riscv-zkvm» from git
  "https://github.com/Verified-zkEVM/riscv-zkvm" @ "4634e41b229da4256e4a1f1688b94133fffa4af0"

/-- Contract definitions and the rendered challenge stubs. -/
@[default_target] lean_lib PcsOpenGolf where
  globs := #[.submodules `PcsOpenGolf]

/-- A submission may add or edit only the root assigned to its track in `challenges.json`. -/
lean_lib Submissions where
  globs := #[.submodules `Submissions]

/-- Regression checks on the executable parts of the contract. -/
lean_lib PcsOpenGolfTests
