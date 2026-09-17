# Axiom ledger

This file records every non-Mathlib mathematical assumption used by the
formalization. The goal is that `#print axioms` for the final theorem agrees
with this ledger and does not contain `sorryAx`.

## Approved in principle

1. **Tahara's description of the fifth integral dimension subgroup.**
   The exact Lean signature is not fixed yet. It must match Theorem 4.3.3 in
   `sources/нормальные ряды.pdf` and expose the representative together with
   all arithmetic conditions used by the source proof.
2. **Missing standard background theorems**, only when Mathlib does not
   already provide a usable theorem. Each such assumption must be separately
   named and stated here before it is used.

## Currently declared

1. `D5.Background.lowerCentralSeries_le_dimensionSubgroup`:
   `γₙ(G) ≤ Dₙ(G)` for every group and every positive `n`. The project defines
   `Dₙ` directly from the two-sided augmentation ideal; Mathlib currently has
   no integral dimension-subgroup development providing this theorem.
2. `D5.Background.commutator_gamma_le_gamma_add`:
   `[γᵣ(G),γₛ(G)] ≤ γᵣ₊ₛ(G)` for positive weights. Mathlib defines the
   lower central series and proves the one-step descending-series property,
   but does not currently expose the two-weight estimate needed here.

Tahara's axiom has not yet been declared: its full parameter record and exact
hypotheses are still being transcribed from Theorem 4.3.3.

## Forbidden

- `sorry` or `by_contra` gaps closed by `sorryAx`;
- an axiom equivalent to the target theorem;
- assumptions of the document-specific reductions (54) or (92);
- hidden assumptions bundled into Tahara's axiom beyond the cited theorem.
