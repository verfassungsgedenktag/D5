import D5.BackgroundAxioms
import D5.TaharaArithmetic

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

end

end D5
