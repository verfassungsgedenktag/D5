# Lean formalization of `[D₅(G), G] = γ₆(G)` for finite groups

This project formalizes the finite-group part of `proof_D5_G_gamma6.md` in
Lean 4 with Mathlib.

The source document and the synced files under the parent project's
`sources/` directory are reference material and are not modified.

## Verification target

The final theorem `D5.finite_group_theorem` states the subgroup equality
`[D₅(G), G] = γ₆(G)` for every finite group `G`, where `D₅` is defined from
the fifth power of the augmentation ideal in `ℤ[G]`.

Tahara's description may be assumed as an explicitly named axiom. Any other
background result not already supplied by Mathlib must also be isolated and
listed in `AXIOMS.md`. The document-specific commutator and arithmetic
calculations are to be proved in Lean.

The complete formal interface to Tahara's Theorem 4.3.3 is in
`D5/Tahara.lean`. It contains the three cyclic-coordinate systems, structural
coefficients, the word (4.3.1), every condition (4.3.2)--(4.3.15), the
Tahara axiom `D5.Tahara.description`, and the separately listed standard
coordinate-existence axiom `D5.Tahara.context_exists`.

The source-to-Lean transcription checklist is recorded in
`TAHARA_INTERFACE.md`.

## Build

```text
./scripts/lake-local build
```

The project pins both Lean and Mathlib. `D5/Audit.lean` prints the exact
axioms of the main theorem during the build.

Lean is currently installed locally under `.tooling/elan`; no shell profile
or system-wide `PATH` was changed.
