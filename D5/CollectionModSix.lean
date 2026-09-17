import D5.Weight

/-!
# First collection rules modulo `γ₆`

This file verifies the bilinearity rules used in formula (56) of the source
document. The proofs expand exact commutator identities and then discard only
terms whose membership in `γ₆` follows from the explicit weight estimate.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

theorem conjugateBy_mod_gamma_six
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : 6 ≤ r + s)
    {x y : G} (hx : x ∈ gamma G r) (hy : y ∈ gamma G s) :
    ModGammaSix (conjugateBy x y) x := by
  rw [conjugateBy_eq_mul_paperComm]
  change ModEq (gamma G 6) (x * paperComm x y) x
  simpa using (ModEq.refl (gamma G 6) x).mul
    (paperComm_mod_gamma_six_eq_one hr hs hrs hx hy)

theorem mul_comm_mod_gamma_six
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : 6 ≤ r + s)
    {x y : G} (hx : x ∈ gamma G r) (hy : y ∈ gamma G s) :
    ModGammaSix (x * y) (y * x) := by
  have heq : x * y = y * x * paperComm x y := by
    simp only [paperComm_eq]
    group
  rw [heq]
  change ModEq (gamma G 6) (y * x * paperComm x y) (y * x)
  simpa using (ModEq.refl (gamma G 6) (y * x)).mul
    (paperComm_mod_gamma_six_eq_one hr hs hrs hx hy)

/-- First identity in (56): collection in the first argument for three
elements of `γ₂`. -/
theorem paperComm_mul_left_mod_gamma_six
    {a b c : G}
    (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 2) (hc : c ∈ gamma G 2) :
    ModGammaSix (paperComm (a * b) c)
      (paperComm a c * paperComm b c) := by
  rw [paperComm_mul_left]
  have hac : paperComm a c ∈ gamma G 4 := by
    simpa using paperComm_mem_gamma_add (r := 2) (s := 2)
      (by norm_num) (by norm_num) ha hc
  have hconj : ModGammaSix (conjugateBy (paperComm a c) b) (paperComm a c) :=
    conjugateBy_mod_gamma_six (r := 4) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hac hb
  exact hconj.mul (ModEq.refl (gamma G 6) (paperComm b c))

/-- Second identity in (56): collection in the second argument for three
elements of `γ₂`. -/
theorem paperComm_mul_right_mod_gamma_six
    {a b c : G}
    (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 2) (hc : c ∈ gamma G 2) :
    ModGammaSix (paperComm a (b * c))
      (paperComm a b * paperComm a c) := by
  rw [paperComm_mul_right]
  have hab : paperComm a b ∈ gamma G 4 := by
    simpa using paperComm_mem_gamma_add (r := 2) (s := 2)
      (by norm_num) (by norm_num) ha hb
  have hac : paperComm a c ∈ gamma G 4 := by
    simpa using paperComm_mem_gamma_add (r := 2) (s := 2)
      (by norm_num) (by norm_num) ha hc
  have hconj : ModGammaSix (conjugateBy (paperComm a b) c) (paperComm a b) :=
    conjugateBy_mod_gamma_six (r := 4) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hab hc
  have hcollect : ModGammaSix
      (paperComm a c * conjugateBy (paperComm a b) c)
      (paperComm a c * paperComm a b) :=
    (ModEq.refl (gamma G 6) (paperComm a c)).mul hconj
  exact hcollect.trans <| mul_comm_mod_gamma_six
    (r := 4) (s := 4) (by norm_num) (by norm_num) (by norm_num) hac hab

end

end D5
