import D5.Functoriality
import D5.Congruence
import Mathlib.GroupTheory.Nilpotent

/-!
# Reduction through `G / gamma G 6`

This is the finite project's quotient infrastructure.  It does not use
residual finiteness or finitely generated subgroups.
-/

namespace D5

universe u v

noncomputable section

section CentralSeriesMap

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- A surjective homomorphism maps every lower-central-series term onto the
corresponding term. -/
theorem lowerCentralSeries_map_eq_of_surjective (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    Subgroup.map f (lowerCentralSeries G n) = lowerCentralSeries H n := by
  induction n with
  | zero =>
      change Subgroup.map f (⊤ : Subgroup G) = (⊤ : Subgroup H)
      rw [← MonoidHom.range_eq_map]
      exact f.range_eq_top_of_surjective hf
  | succ n ih =>
      change Subgroup.map f ⁅lowerCentralSeries G n, (⊤ : Subgroup G)⁆ =
        ⁅lowerCentralSeries H n, (⊤ : Subgroup H)⁆
      rw [Subgroup.map_commutator, ih]
      rw [← MonoidHom.range_eq_map]
      exact congrArg (fun K : Subgroup H => ⁅lowerCentralSeries H n, K⁆)
        (f.range_eq_top_of_surjective hf)

/-- Paper-indexed version of `lowerCentralSeries_map_eq_of_surjective`. -/
theorem gamma_map_eq_of_surjective (f : G →* H)
    (hf : Function.Surjective f) (n : ℕ) :
    Subgroup.map f (gamma G n) = gamma H n := by
  exact lowerCentralSeries_map_eq_of_surjective f hf (n - 1)

end CentralSeriesMap

section SixthQuotient

variable (G : Type u) [Group G]

/-- The quotient used to reduce the theorem for an arbitrary finite group to
a finite nilpotent group. -/
abbrev SixthQuotient := G ⧸ gamma G 6

/-- Canonical quotient map to `G / gamma G 6`. -/
abbrev sixthQuotientMap : G →* SixthQuotient G :=
  QuotientGroup.mk' (gamma G 6)

/-- The sixth paper-indexed lower-central-series term vanishes in the
quotient by `gamma G 6`. -/
theorem gamma_six_sixthQuotient_eq_bot :
    gamma (SixthQuotient G) 6 = ⊥ := by
  rw [← gamma_map_eq_of_surjective (sixthQuotientMap G)
    QuotientGroup.mk_surjective 6]
  exact (Subgroup.map_eq_bot_iff (gamma G 6)).2 <| by
    rw [QuotientGroup.ker_mk']

/-- `G / gamma G 6` is nilpotent, with no nilpotency assumption on `G`. -/
instance sixthQuotient_isNilpotent : Group.IsNilpotent (SixthQuotient G) := by
  rw [nilpotent_iff_lowerCentralSeries]
  refine ⟨5, ?_⟩
  simpa [gamma] using gamma_six_sixthQuotient_eq_bot G

/-- Membership in `Dₙ` descends to the sixth quotient. -/
theorem mem_dimensionSubgroup_sixthQuotient (n : ℕ) {g : G}
    (hg : g ∈ dimensionSubgroup G n) :
    sixthQuotientMap G g ∈ dimensionSubgroup (SixthQuotient G) n :=
  map_mem_dimensionSubgroup (sixthQuotientMap G) n hg

/-- A commutator dies in the sixth quotient exactly when it belongs to
`gamma G 6`. -/
theorem paperComm_mem_gamma_six_iff {a b : G} :
    paperComm a b ∈ gamma G 6 ↔
      paperComm (sixthQuotientMap G a) (sixthQuotientMap G b) = 1 := by
  rw [← map_paperComm]
  change paperComm a b ∈ gamma G 6 ↔ paperComm a b ∈ (sixthQuotientMap G).ker
  rw [QuotientGroup.ker_mk']

/-- Vertical reduction step: an elementwise commutator theorem for the finite
nilpotent quotient implies the corresponding statement in `G`. -/
theorem paperComm_dimension_five_mem_gamma_six_of_quotient
    (hQ : ∀ w ∈ dimensionSubgroup (SixthQuotient G) 5,
      ∀ ξ, paperComm w ξ ∈ gamma (SixthQuotient G) 6)
    {w ξ : G} (hw : w ∈ dimensionSubgroup G 5) :
    paperComm w ξ ∈ gamma G 6 := by
  rw [paperComm_mem_gamma_six_iff G]
  have hmem := hQ (sixthQuotientMap G w)
    (mem_dimensionSubgroup_sixthQuotient G 5 hw) (sixthQuotientMap G ξ)
  simpa [gamma_six_sixthQuotient_eq_bot G] using hmem

end SixthQuotient

end

end D5
