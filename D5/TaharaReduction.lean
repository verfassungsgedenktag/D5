import D5.Tahara
import D5.CommutatorIdentities
import D5.Weight

/-!
# From Tahara generators to an elementwise commutator theorem

The elements whose commutators lie in a fixed normal subgroup form a
subgroup: the inverse image of the center of the quotient.  Consequently it
is enough to verify the document's calculation on each Tahara generator,
even though Theorem 4.3.3 describes `D₅` as a subgroup closure.
-/

namespace D5

universe u

noncomputable section

variable {G : Type u} [Group G]

theorem paperComm_eq_one_iff_mul_comm {a b : G} :
    paperComm a b = 1 ↔ a * b = b * a := by
  rw [paperComm, commutatorElement_eq_one_iff_mul_comm]
  constructor <;> intro h
  · simpa [eq_comm] using congrArg Inv.inv h
  · simpa [eq_comm] using congrArg Inv.inv h

/-- Elements central modulo `N`. -/
def centralModulo (N : Subgroup G) [N.Normal] : Subgroup G :=
  Subgroup.comap (QuotientGroup.mk' N) (Subgroup.center (G ⧸ N))

theorem mem_centralModulo_iff (N : Subgroup G) [N.Normal] {a : G} :
    a ∈ centralModulo N ↔ ∀ b : G, paperComm a b ∈ N := by
  rw [centralModulo, Subgroup.mem_comap, Subgroup.mem_center_iff]
  constructor
  · intro ha b
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' N (paperComm a b) = 1
    rw [map_paperComm, paperComm_eq_one_iff_mul_comm]
    exact (ha (QuotientGroup.mk' N b)).symm
  · intro ha q
    rcases QuotientGroup.mk_surjective q with ⟨b, rfl⟩
    have hcomm : paperComm (QuotientGroup.mk' N a)
        (QuotientGroup.mk' N b) = 1 := by
      rw [← map_paperComm]
      change ((paperComm a b : G) : G ⧸ N) = 1
      rw [QuotientGroup.eq_one_iff]
      exact ha b
    exact (paperComm_eq_one_iff_mul_comm.mp hcomm).symm

namespace Tahara

/-- It is enough to check the commutator calculation on each admissible word
in (4.3.1); subgroup closure then gives the result for every element of
`D₅`. -/
theorem dimensionSubgroup_le_centralModulo_of_words
    (C : Context G) [Finite G]
    (hword : ∀ (P : Parameters C.s C.t), P.Satisfies →
      ∀ ξ : G, paperComm (word C P) ξ ∈ gamma G 6) :
    dimensionSubgroup G 5 ≤ centralModulo (gamma G 6) := by
  rw [description C]
  apply sup_le
  · apply (Subgroup.closure_le (centralModulo (gamma G 6))).2
    rintro g ⟨P, hP, rfl⟩
    change word C P ∈ centralModulo (gamma G 6)
    exact (mem_centralModulo_iff (gamma G 6)).2 (hword P hP)
  · intro g hg
    exact (mem_centralModulo_iff (gamma G 6)).2 fun ξ =>
      modEq_one_iff_mem.mp (gamma_five_central_mod_gamma_six hg)

/-- Elementwise form of the preceding reduction. -/
theorem dimensionSubgroup_paperComm_mem_of_words
    (C : Context G) [Finite G]
    (hword : ∀ (P : Parameters C.s C.t), P.Satisfies →
      ∀ ξ : G, paperComm (word C P) ξ ∈ gamma G 6)
    {w : G} (hw : w ∈ dimensionSubgroup G 5) (ξ : G) :
    paperComm w ξ ∈ gamma G 6 := by
  have hc : w ∈ centralModulo (gamma G 6) :=
    dimensionSubgroup_le_centralModulo_of_words C hword hw
  exact (mem_centralModulo_iff (gamma G 6)).1 hc ξ

end Tahara

end

end D5
