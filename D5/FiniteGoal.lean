import D5.BackgroundAxioms
import D5.Functoriality
import D5.FiniteQuotient
import D5.TaharaArithmetic
import D5.Tahara
import D5.TaharaPair
import D5.TaharaReduction
import D5.TaharaWeights
import D5.TaharaExpand
import D5.TaharaCondition6
import D5.TaharaTransferConsequences
import D5.Rotation
import D5.RotationSix
import D5.Weight
import D5.CommutatorIdentities
import D5.CollectionModSix

/-!
# The finite-group target and the easy inclusion
-/

namespace D5

universe u

noncomputable section

/-- The exact proposition that the project aims to prove. -/
def FiniteD5Statement : Prop :=
  ∀ (G : Type u), ∀ [Group G] [Finite G],
    ⁅dimensionSubgroup G 5, (⊤ : Subgroup G)⁆ = gamma G 6

/-- The inclusion `γ₆(G) ≤ [D₅(G),G]`. It uses only the standard background
inclusion `γ₅(G) ≤ D₅(G)` and Mathlib's monotonicity of subgroup
commutators. No finiteness assumption is needed. -/
theorem gamma_six_le_commutator_dimension_five
    (G : Type u) [Group G] :
    gamma G 6 ≤ ⁅dimensionSubgroup G 5, (⊤ : Subgroup G)⁆ := by
  rw [show (6 : ℕ) = 5 + 1 by norm_num, gamma_succ G 5 (by norm_num)]
  exact Subgroup.commutator_mono
    (Background.lowerCentralSeries_le_dimensionSubgroup G 5 (by norm_num))
    le_rfl

/-- Turn an elementwise theorem in the paper's commutator convention into an
inclusion between Mathlib's commutator subgroups. -/
theorem commutator_le_of_paperComm
    {G : Type u} [Group G] {A B N : Subgroup G}
    (h : ∀ a ∈ A, ∀ b ∈ B, paperComm a b ∈ N) :
    ⁅A, B⁆ ≤ N := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_eq_paperComm_inv]
  exact h a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)

/-- The precise intermediate result still required from the Tahara
calculation: an elementwise theorem for finite nilpotent groups. -/
def FiniteNilpotentElementwiseStatement : Prop :=
  ∀ (H : Type u), ∀ [Group H] [Finite H] [Group.IsNilpotent H],
    ∀ w ∈ dimensionSubgroup H 5, ∀ ξ : H,
      paperComm w ξ ∈ gamma H 6

/-- The quotient reduction of the verification plan. Once the elementwise
finite nilpotent result is proved, the difficult subgroup inclusion follows
for every finite group, without assuming that the original group is
nilpotent. -/
theorem finite_group_difficult_inclusion_of_nilpotent_elementwise
    (hNil : ∀ (H : Type u), ∀ [Group H] [Finite H] [Group.IsNilpotent H],
      ∀ w ∈ dimensionSubgroup H 5, ∀ ξ : H,
        paperComm w ξ ∈ gamma H 6)
    (G : Type u) [Group G] [Finite G] :
    ⁅dimensionSubgroup G 5, (⊤ : Subgroup G)⁆ ≤ gamma G 6 := by
  apply commutator_le_of_paperComm
  intro w hw ξ hξ
  apply paperComm_dimension_five_mem_gamma_six_of_quotient G
    (w := w) (ξ := ξ) ?_ hw
  intro qw hqw qξ
  exact hNil (SixthQuotient G) qw hqw qξ

/-- Final finite-group equality reduced to the still-explicit finite
nilpotent computational statement. -/
theorem finite_group_theorem_of_nilpotent_elementwise
    (hNil : ∀ (H : Type u), ∀ [Group H] [Finite H] [Group.IsNilpotent H],
      ∀ w ∈ dimensionSubgroup H 5, ∀ ξ : H,
        paperComm w ξ ∈ gamma H 6)
    (G : Type u) [Group G] [Finite G] :
    ⁅dimensionSubgroup G 5, (⊤ : Subgroup G)⁆ = gamma G 6 :=
  le_antisymm
    (finite_group_difficult_inclusion_of_nilpotent_elementwise hNil G)
    (gamma_six_le_commutator_dimension_five G)

end

end D5
