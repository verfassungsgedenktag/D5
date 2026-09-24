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
  - [x] Expand the left `w`-stream through relation (3), including its
    diagonal-zero case and both finite reindexings.
  - [x] Expand the right `w`-stream through relation (3), including its
    diagonal-zero case and both finite reindexings.
  - [x] Expand the final `w'`-stream through relation (3), including its
    diagonal-zero case, and combine all four streams.
  - [x] Rotate the resulting commutators into the exact displayed order and
    signs of formula (28), including the conversion of the ratio power in
    the `u`-stream.
    - [x] Prove the common local inner-commutator rotation at weights
      `(3,1,1)`, with its sign and arbitrary integer exponent.
    - [x] Prove threefold extraction of a first-entry power modulo `γ₆` and
      absorb `d(i)/d(h)` into `x₁ₕ^{d(i)}` in the `u`-stream.
    - [x] Remove all diagonal conditionals and match the four exact finite
      products, index domains, signs, and powers displayed in formula (28).
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
  - [x] Formalize Section 10 (formula (29)).
    - [x] For each `i < j`, derive all six formula-(19) factors, distribute
      the outer integer power, normalize the first main factor by the
      cyclic-order ratio, and apply reduced formula (20) to the second.
    - [x] Lift that calculation to the full triangular product and use a
      checked eight-factor permutation in `γ₃/γ₆` to separate its six
      correction factors from the two main streams of formula (21).
    - [x] Insert the verified formula (21), so the transformed first block
      is now connected to all three original blocks of formula (18).
    - [x] Reverse and collect the original second product of (18), then
      prove its exact cancellation with the correction produced by (26).
    - [x] Split the six local pair corrections into the first six global
      triangular streams by checked finite-product collection.
    - [x] Collect formulas (21)--(28) into all twelve displayed products,
      preserving every index domain, sign, exponent, and product order.
  - [x] Formalize Section 11 (formulas (30)--(36)).
    - [x] Derive the coordinate congruences (30)--(31) from conditions
      (11)--(12), with their exact filtered sums.
    - [x] Prove the Bezout coordinate lemma for
      `gcd(d(j),e(p))` and use it to verify the group statements (32)--(33)
      as membership in `γ₂(G)^{d(j)}γ₃(G)`.
    - [x] Prove the weight-transfer lemma behind (35) and eliminate its
      entire strict-pair product using (33).
    - [x] Eliminate the diagonal additional product by (32), including both
      displayed congruences and the binomial exponent calculation in (36).
    - [x] Transform lines 7 and 9--12 of (29) into (34).
      - [x] Prove the local Jacobi transformation printed for every
        `w' i j k` term.
      - [x] Prove the five-factor local Jacobi transformation for every
        `w i j k` term, including its arbitrary integer power.
      - [x] Transform and collect the complete finite `w'` stream into its
        additional stream and the second principal product of (34).
      - [x] Collect the powered `w` identity over the canonical triangle
        `i ≤ j ≤ k`, separating its additional and principal products.
      - [x] Reindex lines 9, 10 and 12 into the canonical `w` triangle and
        combine all three source streams pointwise.
      - [x] Combine the additional `w` and `w'` streams with (35)--(36),
        producing the third principal `w''` product.
        - [x] Expand every factor of (35) into its three finite blocks,
          verify the two required strict/weak triple reindexings, and derive
          the off-diagonal `w''` principal product with the printed negative
          exponent.
        - [x] Split the complete additional `w` stream into its diagonal and
          off-diagonal parts by an explicit finite-list permutation.
        - [x] Identify line 7 with the diagonal word from (32) and finish the
          diagonal cancellation using (36).
  - [x] Formalize Section 12 (strict triples).
    - [x] Derive formulas (37)--(38) directly from conditions (5) and (10).
    - [x] Transfer all three cyclic powers in formula (39), retaining and
      identifying the three weight-five binomial corrections.
    - [x] Eliminate the principal exponent by (37) and all corrections by
      the divisibilities in (38).
    - [x] Collect the local calculation over every strict triple and connect
      it to the three separate principal streams of formula (34).
    - [x] Remove the completely diagonal factor using condition (2).
  - [x] Formalize Section 13 (repeated-index pairs).
    - [x] Prove formulas (40)--(41), including both power transfers and the
      disappearance of their weight-five corrections by (14).
    - [x] Prove formula (42), with its correction divisibility derived from
      condition (15).
    - [x] Prove formulas (43)--(44) from the appropriate weight-controlled
      multiplicative Jacobi identities.
    - [x] Collect the seven transformed factors into formula (45), including
      both printed integer exponent identities.
    - [x] Kill the first two factors of (45), obtain the three local factors
      retained in (46), and collect them over every pair `i < j`.
    - [x] Identify the Section 13 source product with the exact remainder of
      formulas (29) and (34) after the strict and diagonal terms from Section
      12 have been removed.
    - [x] Split the three principal products of (34) into diagonal,
      repeated-index, and strict-index parts; remove the first and last parts
      by conditions (2), (5), and (10).
    - [x] Reorder the complete formula-(29) product, identify its remaining
      pair factors with the source of (45), and derive the finite-group
      theorem `section13_finite` ending at formula (46).
  - [ ] Formalize Sections 14–25 (`κ ≡ 1 mod γ₆`).

## Phase 4 — finite-group theorem and audit

- [ ] Prove the finite nilpotent case.
- [x] Formalize the reduction from a finite group to `G / γ₆(G)`; its use
  is conditional only on the remaining finite nilpotent calculation.
- [ ] Prove both subgroup inclusions.
  - [x] Prove `γ₆(G) ≤ [D₅(G),G]` from the recorded background axiom.
  - [ ] Prove `[D₅(G),G] ≤ γ₆(G)` using the Tahara calculation.
- [ ] Run `lake build` and audit the final theorem with `#print axioms`.
