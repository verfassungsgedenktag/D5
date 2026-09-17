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

/-- The standard weight estimate for the lower central series. Mathlib's
current group-theory development defines the series but does not expose this
two-weight estimate in the form needed by the collection argument. -/
axiom commutator_gamma_le_gamma_add
    (G : Type u) [Group G] (r s : ℕ) (hr : 1 ≤ r) (hs : 1 ≤ s) :
    ⁅D5.gamma G r, D5.gamma G s⁆ ≤ D5.gamma G (r + s)

end

end D5.Background
