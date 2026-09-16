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

## Forbidden

- `sorry` or `by_contra` gaps closed by `sorryAx`;
- an axiom equivalent to the target theorem;
- assumptions of the document-specific reductions (54) or (92);
- hidden assumptions bundled into Tahara's axiom beyond the cited theorem.
