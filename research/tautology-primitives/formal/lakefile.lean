import Lake
open Lake DSL
package «fig22-proofs» where
  version := v!"0.1.0"
@[default_target]
lean_lib FIG22 where
  roots := #[`TreeProofs, `DagProofs, `BasisCertificates, `BasisDag, `Interface]
