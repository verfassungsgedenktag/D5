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
  - [x] Prove functoriality under every group homomorphism.
- [x] Establish quotient congruence and the basic weight bookkeeping modulo
  `γ₆(G)`.
- [x] Prove exact product, inverse, swap, conjugation, and square identities
  for the paper's commutator convention.
- [x] Prove the two product-bilinearity rules in formula (56) modulo `γ₆`.
- [x] Prove weight-parametrized collection at an arbitrary truncation level,
  including the nested power extraction needed at weights five and six.

## Phase 2 — Tahara interface

- [x] Transcribe Theorem 4.3.3 exactly from the cited source.
- [x] Represent its finite cyclic coordinates and arithmetic conditions.
- [x] Declare the reviewed statement as the named Tahara axiom.

## Phase 3 — document calculations

- [ ] Formalize Sections 3–4 (integer divisibility).
  - [x] Prove the multiplicative consequence (6) of condition (4.3.6) in
    `γ₂/γ₃`, including collection of all finite cyclic coordinates.
  - [x] Pair equations (12), (13) and divisibilities (14)–(17), in
    denominator-free integer form.
  - [x] Binomial identities multiplying `C(n,2)` by 2 and `C(n,3)` by 3.
  - [x] Package the pair lemmas against the exact Tahara parameter record.
- [ ] Formalize Sections 5–14 (`[w, ξ] ≡ κ mod γ₆`).
  - [x] Prove formula (18), including ordered product collection and all
    three integer-power extractions.
  - [x] Prove the exact Hall--Witt identity and full rotation formula (19),
    including its four explicit weight-five corrections modulo `γ₆`.
  - [x] Prove both truncated Hall--Petresco formulas needed for the transfer,
    the full six-factor identity (20), and its arbitrary outer power `u`.
  - [x] Use divisibilities (16)--(17) to eliminate the last three
    weight-five factors in (20), obtaining the reduced Tahara-pair formula.
  - [x] Prove the weight `(1,2,1)` transfer formula (22), including its
    weight-five correction, and specialize it to the ordered Tahara
    second-weight word.
  - [x] Prove formula (23), including substitution of relation (1), removal
    of its third-layer tail by weight, and collection of the three finite
    indices into the displayed double product.
  - [x] Prove formulas (24)--(26): eliminate the diagonal by condition (14)
    and combine each strict pair by condition (15) and a weight-controlled
    Hall--Witt rotation.
  - [x] Formalize formula (27): rearrange condition (13), prove that its
    modulus `gcd(d(i), f(l))` kills the indicated weight-five commutator,
    and apply the replacement to the global third-coordinate product.
  - [x] Prove the local relation-(3) alpha-coordinate expansion used in
    formula (28), including an arbitrary integer outer exponent.
  - [x] Split formula (27) into its four alpha-coordinate streams and expand
    the full `u`-stream through relation (3), with finite reindexing and
    coefficient multiplication checked in Lean.
  - [ ] Complete the other three streams of formula (28), then rotate the
    resulting commutators into the exact displayed order and signs.
  - [x] Prove the structural expansion (21).
    - [x] Verify its local substitution of relation (1) through two
      commutators and split the second- and third-weight coordinate blocks.
    - [x] Expand both blocks into their individual ordered coordinates and
      extract all coefficients `b(j,p)` and `c(j,l)`.
    - [x] Prove powered coordinate expansion and the reusable finite-product
      Fubini/pointwise collection rules in the abelian layer `γ₃/γ₆`.
    - [x] Isolate condition (4.3.6) as the exact grouped exponent identity
      for the second-weight coordinates in (21).
    - [x] Collect the ordered coordinate products and their global exponent
      sums, apply condition (4.3.6), and expand the `e(p)v'` contribution
      with relation (2).
- [ ] Formalize Sections 15–25 (`κ ≡ 1 mod γ₆`).

## Phase 4 — finite-group theorem and audit

- [ ] Prove the finite nilpotent case.
- [x] Formalize the reduction from a finite group to `G / γ₆(G)`; its use
  is conditional only on the remaining finite nilpotent calculation.
- [ ] Prove both subgroup inclusions.
  - [x] Prove `γ₆(G) ≤ [D₅(G),G]` from the recorded background axiom.
  - [ ] Prove `[D₅(G),G] ≤ γ₆(G)` using the Tahara calculation.
- [ ] Run `lake build` and audit the final theorem with `#print axioms`.
