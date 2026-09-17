import D5.Foundations
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Congruence modulo a normal subgroup

The source proof performs all calculations in Sections 5–25 modulo
`γ₆(G)`. We encode this as equality in a quotient group, so multiplication,
inverse, powers, and commutators preserve congruence automatically.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

/-- Multiplicative congruence modulo a normal subgroup. -/
def ModEq (N : Subgroup G) [N.Normal] (a b : G) : Prop :=
  (a : G ⧸ N) = b

@[refl]
theorem ModEq.refl (N : Subgroup G) [N.Normal] (a : G) : ModEq N a a :=
  rfl

@[symm]
theorem ModEq.symm {N : Subgroup G} [N.Normal] {a b : G}
    (h : ModEq N a b) : ModEq N b a :=
  Eq.symm h

@[trans]
theorem ModEq.trans {N : Subgroup G} [N.Normal] {a b c : G}
    (hab : ModEq N a b) (hbc : ModEq N b c) : ModEq N a c :=
  Eq.trans hab hbc

theorem modEq_iff_div_mem {N : Subgroup G} [N.Normal] {a b : G} :
    ModEq N a b ↔ a / b ∈ N :=
  QuotientGroup.eq_iff_div_mem

theorem modEq_one_iff_mem {N : Subgroup G} [N.Normal] {a : G} :
    ModEq N a 1 ↔ a ∈ N := by
  simp [ModEq, QuotientGroup.eq_one_iff]

theorem ModEq.mul {N : Subgroup G} [N.Normal] {a b c d : G}
    (hab : ModEq N a b) (hcd : ModEq N c d) :
    ModEq N (a * c) (b * d) := by
  change (a : G ⧸ N) * c = b * d
  rw [hab, hcd]

theorem ModEq.inv {N : Subgroup G} [N.Normal] {a b : G}
    (h : ModEq N a b) : ModEq N a⁻¹ b⁻¹ := by
  change (a : G ⧸ N)⁻¹ = (b : G ⧸ N)⁻¹
  rw [h]

theorem ModEq.zpow {N : Subgroup G} [N.Normal] {a b : G}
    (h : ModEq N a b) (z : ℤ) : ModEq N (a ^ z) (b ^ z) := by
  change (a : G ⧸ N) ^ z = (b : G ⧸ N) ^ z
  rw [h]

theorem map_paperComm {H : Type*} [Group H] (f : G →* H) (a b : G) :
    f (paperComm a b) = paperComm (f a) (f b) := by
  simp [paperComm, map_commutatorElement]

theorem ModEq.paperComm {N : Subgroup G} [N.Normal]
    {a b c d : G} (hac : ModEq N a c) (hbd : ModEq N b d) :
    ModEq N (D5.paperComm a b) (D5.paperComm c d) := by
  change D5.paperComm (a : G ⧸ N) b = D5.paperComm (c : G ⧸ N) d
  rw [hac, hbd]

/-- Congruence modulo the sixth term of the paper-indexed lower central
series. -/
abbrev ModGammaSix (a b : G) : Prop :=
  @ModEq G _ (gamma G 6) (gamma_normal G 6) a b

end

end D5
