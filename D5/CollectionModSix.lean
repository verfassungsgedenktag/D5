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

/-- Weight-parametrized collection in the first argument.  The discarded
conjugation correction has weight `(r + t) + s`. -/
theorem paperComm_mul_left_mod_gamma_six_of_weights
    {r s t : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hsum : 6 ≤ r + t + s) {a b c : G}
    (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) (hc : c ∈ gamma G t) :
    ModGammaSix (paperComm (a * b) c)
      (paperComm a c * paperComm b c) := by
  rw [paperComm_mul_left]
  have hac : paperComm a c ∈ gamma G (r + t) :=
    paperComm_mem_gamma_add hr ht ha hc
  have hconj : ModGammaSix (conjugateBy (paperComm a c) b) (paperComm a c) :=
    conjugateBy_mod_gamma_six (r := r + t) (s := s)
      (Nat.le_add_right_of_le hr) hs (by simpa [Nat.add_assoc] using hsum) hac hb
  exact hconj.mul (ModEq.refl (gamma G 6) (paperComm b c))

/-- Weight-parametrized inversion in the first argument. -/
theorem paperComm_inv_left_mod_gamma_six_of_weights
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hsum : 6 ≤ s + r + r)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) :
    ModGammaSix (paperComm a⁻¹ b) (paperComm a b)⁻¹ := by
  rw [paperComm_inv_left, paperComm_swap]
  have hba : paperComm b a ∈ gamma G (s + r) :=
    paperComm_mem_gamma_add hs hr hb ha
  have hinv : (paperComm a b)⁻¹ ∈ gamma G (s + r) := by
    rw [← paperComm_swap]
    exact hba
  exact conjugateBy_mod_gamma_six (r := s + r) (s := r)
    (Nat.le_add_right_of_le hs) hr hsum hinv ((gamma G r).inv_mem ha)

/-- Integer-power collection in the first argument, under the exact weight
bound for the correction terms. -/
theorem paperComm_zpow_left_mod_gamma_six_of_weights
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hsum : 6 ≤ r + s + r)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) (v : ℤ) :
    ModGammaSix (paperComm (a ^ v) b) (paperComm a b ^ v) := by
  induction v using Int.induction_on with
  | zero => simpa [paperComm_eq] using ModEq.refl (gamma G 6) (1 : G)
  | succ n ih =>
      rw [zpow_add_one, zpow_add_one]
      exact (paperComm_mul_left_mod_gamma_six_of_weights hr hr hs hsum
        ((gamma G r).zpow_mem ha n) ha hb).trans
          (ih.mul (ModEq.refl (gamma G 6) (paperComm a b)))
  | pred n ih =>
      rw [zpow_sub_one, zpow_sub_one]
      exact (paperComm_mul_left_mod_gamma_six_of_weights hr hr hs hsum
        ((gamma G r).zpow_mem ha (-n)) ((gamma G r).inv_mem ha) hb).trans
          (ih.mul (paperComm_inv_left_mod_gamma_six_of_weights hr hs
            (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hsum) ha hb))

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

theorem paperComm_inv_left_mod_gamma_six
    {a b : G} (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 2) :
    ModGammaSix (paperComm a⁻¹ b) (paperComm a b)⁻¹ := by
  rw [paperComm_inv_left, paperComm_swap]
  have hba : paperComm b a ∈ gamma G 4 := by
    simpa using paperComm_mem_gamma_add (r := 2) (s := 2)
      (by norm_num) (by norm_num) hb ha
  have hinv : (paperComm a b)⁻¹ ∈ gamma G 4 := by
    rw [← paperComm_swap]
    exact hba
  exact conjugateBy_mod_gamma_six (r := 4) (s := 2)
    (by norm_num) (by norm_num) (by norm_num) hinv ((gamma G 2).inv_mem ha)

theorem paperComm_inv_right_mod_gamma_six
    {a b : G} (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 2) :
    ModGammaSix (paperComm a b⁻¹) (paperComm a b)⁻¹ := by
  rw [paperComm_inv_right, paperComm_swap]
  have hba : paperComm b a ∈ gamma G 4 := by
    simpa using paperComm_mem_gamma_add (r := 2) (s := 2)
      (by norm_num) (by norm_num) hb ha
  have hinv : (paperComm a b)⁻¹ ∈ gamma G 4 := by
    rw [← paperComm_swap]
    exact hba
  exact conjugateBy_mod_gamma_six (r := 4) (s := 2)
    (by norm_num) (by norm_num) (by norm_num) hinv ((gamma G 2).inv_mem hb)

/-- Integer-power version of the first bilinearity identity in (56). -/
theorem paperComm_zpow_left_mod_gamma_six
    {a b : G} (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 2) (v : ℤ) :
    ModGammaSix (paperComm (a ^ v) b) (paperComm a b ^ v) := by
  induction v using Int.induction_on with
  | zero => simpa [paperComm_eq] using ModEq.refl (gamma G 6) (1 : G)
  | succ n ih =>
      rw [zpow_add_one, zpow_add_one]
      exact (paperComm_mul_left_mod_gamma_six
        ((gamma G 2).zpow_mem ha n) ha hb).trans
          (ih.mul (ModEq.refl (gamma G 6) (paperComm a b)))
  | pred n ih =>
      rw [zpow_sub_one, zpow_sub_one]
      exact (paperComm_mul_left_mod_gamma_six
        ((gamma G 2).zpow_mem ha (-n)) ((gamma G 2).inv_mem ha) hb).trans
          (ih.mul (paperComm_inv_left_mod_gamma_six ha hb))

/-- Integer-power version of the second bilinearity identity in (56). -/
theorem paperComm_zpow_right_mod_gamma_six
    {a b : G} (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 2) (z : ℤ) :
    ModGammaSix (paperComm a (b ^ z)) (paperComm a b ^ z) := by
  induction z using Int.induction_on with
  | zero => simpa [paperComm_eq] using ModEq.refl (gamma G 6) (1 : G)
  | succ n ih =>
      rw [zpow_add_one, zpow_add_one]
      exact (paperComm_mul_right_mod_gamma_six
        ha ((gamma G 2).zpow_mem hb n) hb).trans
          (ih.mul (ModEq.refl (gamma G 6) (paperComm a b)))
  | pred n ih =>
      rw [zpow_sub_one, zpow_sub_one]
      exact (paperComm_mul_right_mod_gamma_six
        ha ((gamma G 2).zpow_mem hb (-n)) ((gamma G 2).inv_mem hb)).trans
          (ih.mul (paperComm_inv_right_mod_gamma_six ha hb))

/-- Full integer bilinearity from formula (56). -/
theorem paperComm_zpow_zpow_mod_gamma_six
    {a b : G} (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 2) (v z : ℤ) :
    ModGammaSix (paperComm (a ^ v) (b ^ z))
      (paperComm a b ^ (v * z)) := by
  have hbz : b ^ z ∈ gamma G 2 := (gamma G 2).zpow_mem hb z
  have hleft := paperComm_zpow_left_mod_gamma_six ha hbz v
  have hright := paperComm_zpow_right_mod_gamma_six ha hb z
  have hpowers := hright.zpow v
  exact hleft.trans <| hpowers.trans <| by
    change ModEq (gamma G 6) ((paperComm a b ^ z) ^ v)
      (paperComm a b ^ (v * z))
    rw [← zpow_mul]
    simpa [mul_comm] using
      ModEq.refl (gamma G 6) (paperComm a b ^ (v * z))

end

end D5
