# FIG-22 Lean verification plan

User-authorized scope: formalize the existing minimum TRUE circuit-cost results
with Lean's kernel; retain all prior evidence and its original status.

1. Install the pinned official Lean 4.35.0 release and record binary/archive identity.
2. Define ordered Boolean semantics, arbitrary finite-variable formula trees,
   gate occurrence size and depth. Prove universal lower bounds and witnesses.
3. Define source-aware ordered acyclic shared circuits and reachable gate cost.
   Prove singleton lower bounds despite dead gates; construct exact witnesses.
4. Check the 136 singleton/pair formula/depth costs via kernel-checked certificates
   with a generic unbounded induction and closure invariant; retain exact scope.
5. Compile in an isolated output directory. Reject placeholders and extra axioms;
   use proof-producing decide, not native_decide. Print theorem axiom dependencies.
6. Review theorem statements against the prior mathematical model, retain logs,
   hashes, exact toolchain/version, and checked/not-checked distinction. Update PR6
   and FIG-22 only after observed successful compilation and review.

No unrelated private proofs, external runtime integrations, P-versus-NP claims,
repository merges, or historical evidence rewrites are in scope. If formalization
exposes a mismatch, repair the smallest definition/proof and preserve the gap
until it is resolved. Compilation failures are not recorded as proof success.
