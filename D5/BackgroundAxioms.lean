import D5.Foundations

/-!
# Explicit background assumptions

Only standard results absent from the current Mathlib development belong in
this file. Every declaration here must also appear in `AXIOMS.md`.
-/

namespace D5.Background

universe u

noncomputable section

/-- The classical inclusion of the lower central series in the integral
dimension series: `γₙ(G) ≤ Dₙ(G)` for positive `n`.

This is an approved standard background assumption. It is separate from the
Tahara axiom and from every document-specific commutator calculation. -/
axiom lowerCentralSeries_le_dimensionSubgroup
    (G : Type u) [Group G] (n : ℕ) (hn : 1 ≤ n) :
    D5.gamma G n ≤ D5.dimensionSubgroup G n

end

end D5.Background
