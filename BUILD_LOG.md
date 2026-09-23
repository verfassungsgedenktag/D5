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
