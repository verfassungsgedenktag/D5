# Formalization progress

## Phase 0 — reproducible environment

- [x] Create a separate project without changing source material.
- [x] Pin Lean and Mathlib versions in project files.
- [x] Install the pinned toolchain locally.
- [x] Download Mathlib and its compiled cache.
- [x] Run the first successful `lake build`.

## Phase 1 — foundations

- [x] Define the left-normed element commutator notation used by the paper.
- [x] Align `γₙ(G)` with Mathlib's lower central series indexing.
- [x] Define the integral augmentation ideal and `Dₙ(G)`.
- [ ] Prove or isolate functoriality and `γₙ(G) ≤ Dₙ(G)`.
  - [x] Isolate `γₙ(G) ≤ Dₙ(G)` as one named background axiom.
  - [ ] Formalize functoriality under quotient maps.
- [ ] Establish quotient and weight bookkeeping modulo `γ₆(G)`.

## Phase 2 — Tahara interface

- [ ] Transcribe Theorem 4.3.3 exactly from the cited source.
- [ ] Represent its finite cyclic coordinates and arithmetic conditions.
- [ ] Declare the reviewed statement as the named Tahara axiom.

## Phase 3 — document calculations

- [ ] Formalize Sections 3–4 (integer divisibility).
  - [x] Pair equations (12), (13) and divisibilities (14)–(17), in
    denominator-free integer form.
  - [x] Binomial identities multiplying `C(n,2)` by 2 and `C(n,3)` by 3.
  - [ ] Package the pair lemmas against the exact Tahara parameter record.
- [ ] Formalize Sections 5–14 (`[w, ξ] ≡ κ mod γ₆`).
- [ ] Formalize Sections 15–25 (`κ ≡ 1 mod γ₆`).

## Phase 4 — finite-group theorem and audit

- [ ] Prove the finite nilpotent case.
- [ ] Pass from a finite group to `G / γ₆(G)`.
- [ ] Prove both subgroup inclusions.
  - [x] Prove `γ₆(G) ≤ [D₅(G),G]` from the recorded background axiom.
  - [ ] Prove `[D₅(G),G] ≤ γ₆(G)` using the Tahara calculation.
- [ ] Run `lake build` and audit the final theorem with `#print axioms`.
