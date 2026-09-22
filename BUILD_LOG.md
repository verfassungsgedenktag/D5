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
