# Build log

## 2026-09-16

- Lean: `v4.24.0`
- Lake: `5.0.0-src+797c613`
- Mathlib tag: `v4.24.0`
- Mathlib revision: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`
- Dependency cache: 7335 artifacts downloaded and unpacked successfully.
- First smoke build: successful.
- Foundations build: successful, including the noncommutative group-ring
  definition using two-sided ideals.
- Tahara pair arithmetic build: successful, with no `sorry`.
- Axiom audit build: successful. Completed arithmetic lemmas use only Lean's
  standard logical axioms (`propext`, `Classical.choice`, `Quot.sound`).
- The proved inclusion `γ₆(G) ≤ [D₅(G),G]` additionally reports exactly the
  declared background axiom `lowerCentralSeries_le_dimensionSubgroup`.

Run the current verification with:

```text
./scripts/lake-local build
```

## 2026-09-17

- Full build: successful (`3103` jobs).
- Added quotient congruence modulo `γ₆`, lower-central-series weight
  bookkeeping, and exact commutator identities in the paper's convention.
- Verified both product-bilinearity rules from formula (56) modulo `γ₆`.
- Axiom audit: these collection rules use only Lean's standard logical axioms
  and the explicitly listed background axiom
  `commutator_gamma_le_gamma_add`.
- Source scan: no `sorry` or `sorryAx` occurs in any Lean file.
- Tahara interface build: successful. The formal statement includes all
  cyclic-coordinate data, the ordered noncommutative word (4.3.1), and all
  conditions (4.3.2)--(4.3.15). Its only new mathematical assumption is the
  named axiom `D5.Tahara.description`.
- Full formula (20) build: successful (`3119` jobs). Both truncated
  Hall--Petresco expansions, all six factors, the arbitrary exponent `u`,
  and the reduction by divisibilities (16)--(17) are checked by Lean.
- Axiom audit for formula (20): only Lean's standard logical axioms and the
  declared background axiom `commutator_gamma_le_gamma_add`; no additional
  mathematical axiom was introduced.
- Source scan after formula (20): no `sorry`, `sorryAx`, or `admit` occurs in
  any Lean file.
- Formula (22): the universal weight `(1,2,1)` transfer and its specialization
  to the ordered Tahara second-weight word compile successfully.
- Formula (21), local structural stage: relation (1) is transported through
  two commutators and both coordinate blocks are expanded term by term with
  their `b(j,p)` and `c(j,l)` exponents.
- Added checked finite-product collection in the abelian layer `γ₃/γ₆`,
  including pointwise multiplication, distribution of integer powers, and
  exchange of two finite ordered-product loops.

## 2026-09-18

- Formula (21): full build successful (`3123` jobs). Lean checks the global
  triangular-product reindexing, collection by `x₂` and `x₃` coordinates,
  the exponent identity from condition (4.3.6), and the expansion of the
  `e(p)v'` contribution through relation (2).
- Axiom audit for formula (21): only Lean's standard logical axioms and the
  declared background axiom `commutator_gamma_le_gamma_add`; no new
  mathematical axiom was introduced.
- Source scan: no `sorry`, `sorryAx`, or `admit` occurs in any Lean file.
- Formula (23): full build successful (`3124` jobs). Relation (1), the
  weight-six disappearance of its third-layer tail, and the global
  three-index collection are checked by Lean.
- Formula (26): local and global collection of the weight-two block compile;
  conditions (14)--(15) are used only through their stated congruences.
- Formula (27): the condition-(13) exponent comparison and its transport to
  the weight-five third-coordinate commutator compile successfully.
- Formula (28), first collection stage: successful full build (`3127` jobs).
  Lean separates all four alpha-coordinate streams in (27), then reindexes
  and expands the complete `u`-stream using relation (3).  The result is the
  raw first-layer commutator stream before the displayed rotations.
- Formula (28), second stream: relation (3) now expands the full left
  `w(g,i,h)` triangular stream.  Lean checks the diagonal separately from
  `alpha(i,i,l)=0` and recollects both nested finite index products.
- Formula (28), third stream: the same checked expansion now covers the
  right `w(g,h,i)` triangle, including its independent diagonal case.
- Formula (28), all coordinate expansions: the final `w'` stream is checked
  and all four streams are combined into a single raw commutator product.
- Formula (28), final form: all inner commutators are rotated with the
  correct negative exponents; the `u`-stream ratio is absorbed into
  `x₁ᵢ^{d(j)}` by a checked threefold power-extraction lemma; diagonal terms
  are restored and proved trivial.  The result matches all four displayed
  finite products exactly.
- Section 10 local formula-(19)--(20) calculation: full build successful
  (`3128` jobs).  The audit of `formula19_pair`, `formula19_low_main`, and
  `formula19_and_20_pair` uses only the existing commutator-weight
  background axiom.
- Section 10 triangular collection: the local result is lifted to every
  pair `i < j`, and Lean checks the eight-factor reordering and its finite
  product collection into the correction product and `formula21MainPairProduct`.
- Section 10 assembly: formula (21) is now inserted into the transformed
  first block while the original weight-two and weight-four blocks of (18)
  remain explicit; this is checked by `formula18_after_formula19_to_21`.
- Section 10, formula (29): full build successful (`3128` jobs).  Lean
  reverses and collects the second product of (18), cancels it against the
  formula-(26) correction, separates the six pairwise corrections into six
  global streams, and inserts formulas (27)--(28).  The theorem `formula29`
  has exactly the twelve displayed products and all their printed index
  restrictions, signs, and exponents.
- Formula-(29) axiom audit: `#print axioms D5.Tahara.formula29` reports only
  Lean's standard logical axioms and the explicitly accepted background
  theorem `D5.Background.commutator_gamma_le_gamma_add`; no new project
  axiom enters the calculation.
- Section 11, formulas (30)--(33): full build successful (`3129` jobs).
  Conditions (11)--(12) are converted to their exact coordinate sums, and
  an explicit Bezout construction proves membership of both displayed
  words in `γ₂(G)^{d(j)}γ₃(G)` without adding an axiom.
- Formula (35): the strict-pair product is proved trivial modulo `γ₆` by a
  checked fourfold commutator power-transfer lemma applied to formula (33).
- Formula (36): both displayed congruences compile.  Lean checks the
  multilinear replacement supplied by (32), the identity
  `2 * binom(d(j),2) = d(j) * (d(j)-1)`, and the final power transfer.
- Formula (34), local `w'` step: the printed Jacobi transformation is proved
  from the existing Hall--Witt rotation and weight-controlled collection.
- Full build after formulas (35)--(36) and the local formula-(34) step:
  successful (`3129` jobs).  The axiom audit reports only Lean's standard
  logical axioms and `D5.Background.commutator_gamma_le_gamma_add` for every
  new theorem; the source scan remains free of `sorry`, `admit`, and
  `sorryAx`.

## 2026-09-24

- Formula (34), local `w` step: the complete five-factor Jacobi identity is
  proved from three weight-controlled Hall--Witt rotations.  Its arbitrary
  integer-powered specialization compiles with all signs explicit.
- Formula (34), global `w'` stream: the full finite triangular product from
  line 11 of (29) is transformed and separated into the additional stream
  and the second principal product of (34).
- Formula (34), canonical `w` stream: all powered local identities are
  collected over `i ≤ j ≤ k` and separated into their additional and first
  principal products.  Reindexing lines 9, 10 and 12 to this common triangle
  remains the next step.
- Full build at this checkpoint: successful (`3130` jobs).  The new local,
  powered, and finite-product theorems depend only on Lean's standard
  logical axioms and `D5.Background.commutator_gamma_le_gamma_add`.
- Formula (34), finite reindexing: explicit permutations identify the
  `(j,i,k)` and `(k,i,j)` loop orders of lines 9 and 10 with the canonical
  triangle `(i,j,k)`.  Lines 9, 10 and 12 are then combined pointwise and
  transformed into the additional `w` stream and the first principal
  product of (34).
- Full build after the reindexing stage: successful (`3130` jobs); the
  axiom audit again contains no mathematical assumption beyond the accepted
  commutator-weight background theorem.
- Formula (35) is now expanded back into the three explicit words of (33).
  Two checked finite permutations identify its first two blocks with the
  off-diagonal additional `w` stream and the complete additional `w'`
  stream.  Solving the resulting product identity and distributing the
  inverse through the finite product gives the third principal `w''` stream
  for all `i ≤ j < k`, with its negative exponent exactly as in (34).
- The complete additional `w` product is split into diagonal `j = k` and
  off-diagonal `j < k` pieces.  The remaining Section 11 obligation is now
  only the diagonal identity involving line 7 and formula (36).
- Section 11 and formula (34) are complete.  Line 7 is identified with the
  unsquared first-layer word from (32), including the negative-coordinate
  inversion and commutator swap.  Formula (36) kills its square together
  with the diagonal `w` and `w''` blocks.  The diagonal and strict `w''`
  products are then joined into the exact domain `i ≤ j < k`, and theorem
  `formula34` transforms lines 7 and 9--12 of (29) into all three displayed
  principal products.
- Full build after completing formula (34): successful (`3130` jobs).
  `#print axioms D5.Tahara.formula34` reports only Lean's standard logical
  axioms and the accepted commutator-weight background theorem; no new
  mathematical axiom, `sorry`, or `admit` is used.
- Section 12, formulas (37)--(39): Lean derives the strict-triple exponent
  identity and three divisibilities from Tahara conditions (5) and (10),
  expands all three cyclic powers with their weight-five corrections, and
  proves every local strict-triple contribution trivial modulo `γ₆`.
- The local calculation is collected over `i < j < k` and identified with
  the product of the three strict principal streams from formula (34).
  Condition (2) separately removes the fully diagonal factor.
- Full build after completing Section 12: successful (`3131` jobs).  The
  axiom audit for all new public theorems contains only Lean's standard
  logical axioms and the accepted background theorem
  `D5.Background.commutator_gamma_le_gamma_add`.
- Section 13 pair calculation: formulas (40)--(44) compile with every
  cyclic-power transfer and weight-five correction explicit.  Formula (43)
  is derived from the five-factor Jacobi theorem used in (34), while (44)
  uses its weight `(2,1,2)` specialization.
- The seven transformed pair factors are collected into formula (45).
  Lean verifies both printed integer exponent identities, the order-power
  vanishing of the first two factors, and the resulting local and global
  three-product form (46).
- Section 13 global bridge completed.  Lean splits the weak index domains in
  the three principal products of (34), removes the diagonal and strict
  parts using Section 12, and identifies the two repeated-index faces.
- The first six streams of (29), the repeated first stream of (28), and the
  two surviving faces are collected pointwise into the exact source of
  formula (45).  The resulting theorem `section13_finite` derives formula
  (46) directly from `[word C P, ξ]` for finite groups.
- Full build after completing Section 13: successful (`3132` jobs).  The
  axiom audit for the new global bridge and `section13_finite` contains only
  Lean's standard logical axioms and the accepted background theorem
  `D5.Background.commutator_gamma_le_gamma_add`; no new project axiom was
  introduced.
- Section 14 started in `D5/Section14.lean`.  Formulas (47)--(49) expand
  condition (6) through all finite products.  Formula (52) retains and then
  removes both weight-five corrections using the two divisibilities in
  (17).  A direct pairwise power-transfer proof of (53) yields the global
  cancellation of the first two products in (46) and formula (54).
- Formula (51) is recorded with its printed three-factor right side and
  checked against formulas (52)--(53).
- Formula (50) is proved modulo `γ₄`.  Lean checks the two-term
  Hall--Petresco expansion for a power in the first commutator entry, moves
  the `d(i)`-power through each triple commutator, applies both divisibilities
  in (17), and verifies the final exponent cancellation from
  `d(j) = d(i) * (d(j) / d(i))`.  This completes Section 14.
- Full build after completing Section 14: successful (`3133` jobs).  The
  audit for formulas (47)--(54), the Hall--Petresco helper for (50), and the
  global cancellation contains only Lean's standard logical axioms and the
  accepted commutator-weight background theorem.
- Section 15 is formalized in `D5/Section15.lean`.  Formula (55) names the
  exact remaining product from (54), and every local factor is proved to
  lie in `γ₅`.  Formula (56) is represented by checked multiplication,
  integer-power, modulo-`γ₄` replacement, and `γ₄` reordering lemmas.
- Full build after Section 15: successful (`3134` jobs).  The axiom audit
  reports only Lean's standard logical axioms and the accepted
  commutator-weight background theorem; no proof placeholders occur.
- Section 16 is formalized in `D5/Section16.lean`.  Formula (57) is the
  checked first-entry Hall--Petresco expansion modulo `γ₄`; formula (58)
  transfers the order power into the last entry.  Formula (59) is collected
  over all strict pairs, and its second product is eliminated factor by
  factor using the first divisibility in (17), yielding formula (60).
- Full build after Section 16: successful (`3135` jobs), with the new
  theorems included in the axiom audit.
- Section 17 is formalized in `D5/Section17.lean`.  Formula (61) is derived
  directly from the weight-three condition-(6) word by finite-product
  collection modulo `γ₄`.  Formula (63) records every principal and
  correction stream from expanding (62); Lean verifies the two correction
  exponent identities from conditions (7) and (8), then formula (58) makes
  both streams trivial and yields formula (62).
- Full build after Section 17: successful (`3136` jobs).  The complete
  Section 17 chain is included in the axiom audit.
- Section 18 is formalized in `D5/Section18.lean`.  The definitions of
  `lambda` and `eta` use the unique normal form of the original `x3` cyclic
  basis.  Lean verifies formulas (64)--(65), proves the two divisibilities
  in (66) by reducing arbitrary integer coordinates modulo their orders,
  and checks the complete exponent sums in formulas (67)--(69).
- Formula (68) is derived from the rearranged formula (57), formula (67),
  and the coordinate form (65).  Its left side is then proved to lie in
  `gamma G 3`.  Formula (69) separately expands and collects the ordinary,
  upper-triangular, and lower-triangular products in formula (62).
- Full build after Section 18: successful (`3137` jobs).  The axiom audit
  for formulas (64)--(69) contains only Lean's standard logical axioms and
  the accepted commutator-weight background theorem; no new mathematical
  axiom was introduced.
- Section 19 is formalized in `D5/Section19.lean`.  Lean proves the generic
  finite double-sum reindexing and square partition needed to expand (70)
  and (71).  Conditions (14)--(15), formula (66), and the cyclic-order
  divisibility `f(l) ∣ f(m)` then prove both displayed sums divisible by
  `f(l)`.
- Full build after Section 19: successful (`3138` jobs).  The new sum
  identities require no project axiom, while formulas (70)--(71) use only
  the already accepted commutator-weight background theorem.
- Section 20 has begun in `D5/Section20.lean`.  Formula (72) is derived from
  condition (11) after an explicit finite-sum split removes the diagonal
  term by condition (2).  Formula (73) is proved for the printed three-part
  word by expanding it coordinatewise in `γ₂/γ₃` and applying the existing
  Bezout calculation to every cyclic coordinate.
- Full build after formulas (72)--(73): successful (`3139` jobs).  Their
  axiom audit contains only standard logical axioms and the accepted
  commutator-weight theorem.
- Section 20 is complete.  Formula (74) is obtained by commuting all three
  factors of (73), collecting modulo `γ₄`, and transferring the `d(i)`
  power from `γ₂` to `γ₃`.  Formula (75) uses the actual normal-form
  coordinates in `γ₃/γ₄`; coordinate uniqueness supplies explicit integer
  witnesses `q(i,l)`.
- The proofs of (76)--(77) multiply (75) by the stated `eta` coordinates,
  eliminate every witness using (66), and formally reindex the lower
  triangular sums as upper triangular sums.  All displayed exponents use
  the full sums in `b`, `lambda`, `v`, `w`, and `w''`.
- Full build after completing Section 20: successful (`3139` jobs).  The
  audit of formulas (74)--(77) reports only Lean's standard logical axioms
  and the accepted commutator-weight background theorem.
- Section 21 is formalized in `D5/Section21.lean`.  Lean verifies the exact
  polynomial expansions (78)--(79), all lower-to-upper triangular sum
  reindexings, and the final strict-pair coefficient divisibility from
  condition (14).  The mixed case also checks the required transfer along
  `f(l) ∣ f(m)`.
- Full build after Section 21: successful (`3140` jobs).  The axiom audit
  reports only Lean's standard logical axioms and the previously accepted
  commutator-weight background theorem; Section 21 introduces no new axiom.
- Section 22 is formalized in `D5/Section22.lean`.  Formula (80) is isolated
  as the explicit standard invariant-factor axiom for the finite abelian
  quotient `γ₂(G)/γ₄(G)`.  Lean then constructs the coordinates in (81),
  derives (82) from the cyclic order relation, and verifies the complete
  coordinate expansions and congruences (83)--(84) from formulas (68),
  (69), and (62).
- Full build after Section 22: successful (`3141` jobs).  The audit records
  exactly one new accepted background axiom,
  `D5.Background.gammaTwoFourBasis_exists`; formulas (81)--(84) themselves
  are derived from the selected basis and the earlier checked calculation.
