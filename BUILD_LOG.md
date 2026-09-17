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
