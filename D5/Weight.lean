import D5.BackgroundAxioms
import D5.Congruence
import D5.CommutatorIdentities

/-!
# Weight bookkeeping

These lemmas turn the standard subgroup estimate
`[γᵣ,γₛ] ≤ γᵣ₊ₛ` into element-level rules using the commutator convention of
the source document.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

theorem paperComm_mem_gamma_add
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) :
    paperComm a b ∈ gamma G (r + s) := by
  apply Background.commutator_gamma_le_gamma_add G r s hr hs
  exact Subgroup.commutator_mem_commutator
    ((gamma G r).inv_mem ha) ((gamma G s).inv_mem hb)

theorem paperComm_mod_gamma_six_eq_one
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : 6 ≤ r + s)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) :
    ModGammaSix (paperComm a b) 1 := by
  change ModEq (gamma G 6) (paperComm a b) 1
  rw [modEq_one_iff_mem]
  exact lowerCentralSeries_antitone (by
    simpa [gamma] using Nat.sub_le_sub_right hrs 1)
    (paperComm_mem_gamma_add hr hs ha hb)

theorem gamma_five_central_mod_gamma_six
    {a b : G} (ha : a ∈ gamma G 5) :
    ModGammaSix (paperComm a b) 1 := by
  apply paperComm_mod_gamma_six_eq_one (r := 5) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) ha
  simp [gamma]

/-- A left-normed commutator whose first entry has weight `r` and whose
remaining entries have weight one has weight `r + length`. -/
theorem leftComm_mem_gamma_of_first
    {r : ℕ} (hr : 1 ≤ r) {a : G} (ha : a ∈ gamma G r) (xs : List G) :
    leftComm a xs ∈ gamma G (r + xs.length) := by
  induction xs generalizing r a with
  | nil => simpa using ha
  | cons x xs ih =>
      rw [leftComm_cons]
      have hx : x ∈ gamma G 1 := by simp [gamma]
      have hfirst : paperComm a x ∈ gamma G (r + 1) :=
        paperComm_mem_gamma_add hr (by norm_num) ha hx
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (Nat.le_add_right_of_le hr) hfirst

/-- An unrestricted left-normed commutator on `1 + length` entries has that
weight in the lower central series. -/
theorem leftComm_mem_gamma (a : G) (xs : List G) :
    leftComm a xs ∈ gamma G (1 + xs.length) :=
  leftComm_mem_gamma_of_first (by norm_num) (by simp [gamma]) xs

end

end D5
