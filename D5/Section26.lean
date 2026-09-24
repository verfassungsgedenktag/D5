import D5.Section25
import D5.TaharaReduction

/-!
# Section 26: completion of the finite elementwise calculation

Formula (54) identifies the commutator of an admissible Tahara word with
`κ(P,ξ)` modulo `γ₆`; formula (92) makes `κ(P,ξ)` trivial modulo
`γ₆`.  Tahara's lifted description and centrality of `γ₅` modulo
`γ₆` then extend the calculation from the admissible words to every
element of `D₅`.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Formulas (54) and (92) together: every admissible Tahara word commutes
with every element modulo `γ₆`. -/
theorem formula54_formula92_finite [Finite G]
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.paperComm (word C P) ξ ∈ D5.gamma G 6 := by
  apply D5.modEq_one_iff_mem.mp
  exact (formula54_kappa C P hP ξ).trans
    (formula92_finite C P hP ξ)

/-- The difficult elementwise statement for finite groups. -/
theorem finite_elementwise (G : Type u) [Group G] [Finite G] :
    ∀ w ∈ D5.dimensionSubgroup G 5, ∀ ξ : G,
      D5.paperComm w ξ ∈ D5.gamma G 6 := by
  let C := Context.chosen G
  intro w hw ξ
  exact dimensionSubgroup_paperComm_mem_of_words C
    (formula54_formula92_finite C) hw ξ

end

end D5.Tahara
