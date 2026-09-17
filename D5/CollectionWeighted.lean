import D5.CollectionModSix

/-!
# Weight-parametrized commutator collection

These are the collection lemmas with an arbitrary truncation weight.  They
are used below at weight five and then transported through one more
commutator to the calculations modulo `γ₆`.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

theorem paperComm_mod_gamma_eq_one
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : n ≤ r + s)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) :
    ModEq (gamma G n) (paperComm a b) 1 := by
  rw [modEq_one_iff_mem]
  exact gamma_antitone G hn (paperComm_mem_gamma_add hr hs ha hb)

theorem conjugateBy_mod_gamma
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : n ≤ r + s)
    {x y : G} (hx : x ∈ gamma G r) (hy : y ∈ gamma G s) :
    ModEq (gamma G n) (conjugateBy x y) x := by
  rw [conjugateBy_eq_mul_paperComm]
  simpa using (ModEq.refl (gamma G n) x).mul
    (paperComm_mod_gamma_eq_one hr hs hn hx hy)

theorem paperComm_mul_left_mod_gamma
    {n r s t : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hn : n ≤ r + t + s) {a b c : G}
    (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) (hc : c ∈ gamma G t) :
    ModEq (gamma G n) (paperComm (a * b) c)
      (paperComm a c * paperComm b c) := by
  rw [paperComm_mul_left]
  have hac : paperComm a c ∈ gamma G (r + t) :=
    paperComm_mem_gamma_add hr ht ha hc
  have hconj : ModEq (gamma G n) (conjugateBy (paperComm a c) b)
      (paperComm a c) :=
    conjugateBy_mod_gamma (r := r + t) (s := s)
      (Nat.le_add_right_of_le hr) hs
      (by simpa [Nat.add_assoc] using hn) hac hb
  exact hconj.mul (ModEq.refl (gamma G n) (paperComm b c))

theorem paperComm_inv_left_mod_gamma
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : n ≤ s + r + r)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) :
    ModEq (gamma G n) (paperComm a⁻¹ b) (paperComm a b)⁻¹ := by
  rw [paperComm_inv_left, paperComm_swap]
  have hba : paperComm b a ∈ gamma G (s + r) :=
    paperComm_mem_gamma_add hs hr hb ha
  have hinv : (paperComm a b)⁻¹ ∈ gamma G (s + r) := by
    rw [← paperComm_swap]
    exact hba
  exact conjugateBy_mod_gamma (r := s + r) (s := r)
    (Nat.le_add_right_of_le hs) hr hn hinv ((gamma G r).inv_mem ha)

theorem paperComm_inv_right_mod_gamma
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : n ≤ s + r + s)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) :
    ModEq (gamma G n) (paperComm a b⁻¹) (paperComm a b)⁻¹ := by
  rw [paperComm_inv_right, paperComm_swap]
  have hba : paperComm b a ∈ gamma G (s + r) :=
    paperComm_mem_gamma_add hs hr hb ha
  have hinv : (paperComm a b)⁻¹ ∈ gamma G (s + r) := by
    rw [← paperComm_swap]
    exact hba
  exact conjugateBy_mod_gamma (r := s + r) (s := s)
    (Nat.le_add_right_of_le hs) hs hn hinv ((gamma G s).inv_mem hb)

theorem paperComm_zpow_left_mod_gamma
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : n ≤ r + s + r)
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) (v : ℤ) :
    ModEq (gamma G n) (paperComm (a ^ v) b) (paperComm a b ^ v) := by
  induction v using Int.induction_on with
  | zero => simpa [paperComm_eq] using ModEq.refl (gamma G n) (1 : G)
  | succ z ih =>
      rw [zpow_add_one, zpow_add_one]
      exact (paperComm_mul_left_mod_gamma hr hr hs hn
        ((gamma G r).zpow_mem ha z) ha hb).trans
          (ih.mul (ModEq.refl (gamma G n) (paperComm a b)))
  | pred z ih =>
      rw [zpow_sub_one, zpow_sub_one]
      exact (paperComm_mul_left_mod_gamma hr hr hs hn
        ((gamma G r).zpow_mem ha (-z)) ((gamma G r).inv_mem ha) hb).trans
          (ih.mul (paperComm_inv_left_mod_gamma hr hs
            (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hn) ha hb))

theorem mul_comm_mod_gamma
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hn : n ≤ r + s)
    {x y : G} (hx : x ∈ gamma G r) (hy : y ∈ gamma G s) :
    ModEq (gamma G n) (x * y) (y * x) := by
  have heq : x * y = y * x * paperComm x y := by
    simp only [paperComm_eq]
    group
  rw [heq]
  simpa using (ModEq.refl (gamma G n) (y * x)).mul
    (paperComm_mod_gamma_eq_one hr hs hn hx hy)

theorem paperComm_mul_right_mod_gamma
    {n r s t : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (ht : 1 ≤ t)
    (hnConj : n ≤ r + s + t) (hnComm : n ≤ (r + t) + (r + s))
    {a b c : G} (ha : a ∈ gamma G r)
    (hb : b ∈ gamma G s) (hc : c ∈ gamma G t) :
    ModEq (gamma G n) (paperComm a (b * c))
      (paperComm a b * paperComm a c) := by
  rw [paperComm_mul_right]
  have hab : paperComm a b ∈ gamma G (r + s) :=
    paperComm_mem_gamma_add hr hs ha hb
  have hac : paperComm a c ∈ gamma G (r + t) :=
    paperComm_mem_gamma_add hr ht ha hc
  have hconj : ModEq (gamma G n) (conjugateBy (paperComm a b) c)
      (paperComm a b) :=
    conjugateBy_mod_gamma (r := r + s) (s := t)
      (Nat.le_add_right_of_le hr) ht
      (by simpa [Nat.add_assoc] using hnConj) hab hc
  have hfirst : ModEq (gamma G n)
      (paperComm a c * conjugateBy (paperComm a b) c)
      (paperComm a c * paperComm a b) :=
    (ModEq.refl (gamma G n) (paperComm a c)).mul hconj
  exact hfirst.trans <| mul_comm_mod_gamma
    (n := n) (r := r + t) (s := r + s)
      (Nat.le_add_right_of_le hr) (Nat.le_add_right_of_le hr)
      hnComm hac hab

theorem paperComm_zpow_right_mod_gamma
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hnConj : n ≤ r + s + s) (hnComm : n ≤ (r + s) + (r + s))
    {a b : G} (ha : a ∈ gamma G r) (hb : b ∈ gamma G s) (z : ℤ) :
    ModEq (gamma G n) (paperComm a (b ^ z)) (paperComm a b ^ z) := by
  induction z using Int.induction_on with
  | zero => simpa [paperComm_eq] using ModEq.refl (gamma G n) (1 : G)
  | succ v ih =>
      rw [zpow_add_one, zpow_add_one]
      exact (paperComm_mul_right_mod_gamma hr hs hs hnConj hnComm
        ha ((gamma G s).zpow_mem hb v) hb).trans
          (ih.mul (ModEq.refl (gamma G n) (paperComm a b)))
  | pred v ih =>
      rw [zpow_sub_one, zpow_sub_one]
      exact (paperComm_mul_right_mod_gamma hr hs hs hnConj hnComm
        ha ((gamma G s).zpow_mem hb (-v)) ((gamma G s).inv_mem hb)).trans
          (ih.mul (paperComm_inv_right_mod_gamma hr hs
            (by simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hnConj) ha hb))

/-- If the first argument changes modulo `γᵣ`, one further commutator with
an element of weight `s` changes only modulo `γᵣ₊ₛ`. -/
theorem paperComm_left_of_modEq_gamma
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {a b c : G} (hab : ModEq (gamma G r) a b)
    (hc : c ∈ gamma G s) :
    ModEq (gamma G (r + s)) (paperComm a c) (paperComm b c) := by
  have hquot : a / b ∈ gamma G r := modEq_iff_div_mem.mp hab
  have hb : b ∈ gamma G 1 := by simp [gamma]
  have hsplit := paperComm_mul_left_mod_gamma
    (n := r + s) (r := r) (s := 1) (t := s) hr (by norm_num) hs
    (by omega) hquot hb hc
  have hvanish : ModEq (gamma G (r + s)) (paperComm (a / b) c) 1 :=
    paperComm_mod_gamma_eq_one hr hs le_rfl hquot hc
  have hprod : ModEq (gamma G (r + s))
      (paperComm (a / b) c * paperComm b c) (paperComm b c) := by
    simpa using hvanish.mul (ModEq.refl (gamma G (r + s)) (paperComm b c))
  rw [show a = (a / b) * b by simp [div_eq_mul_inv]]
  exact hsplit.trans hprod

/-- The symmetric transport rule for a change in the second argument. -/
theorem paperComm_right_of_modEq_gamma
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    {a b c : G} (hbc : ModEq (gamma G s) b c)
    (ha : a ∈ gamma G r) :
    ModEq (gamma G (r + s)) (paperComm a b) (paperComm a c) := by
  have h := (paperComm_left_of_modEq_gamma hs hr hbc ha).inv
  rw [← paperComm_swap b a, ← paperComm_swap c a] at h
  simpa [Nat.add_comm] using h

/-- The nested power extraction used in the first block of formula (18). -/
theorem paperComm_paperComm_zpow_left_mod_gamma_six
    {a b c : G} (ha : a ∈ gamma G 2)
    (hb : b ∈ gamma G 1) (hc : c ∈ gamma G 1) (v : ℤ) :
    ModGammaSix (paperComm (paperComm (a ^ v) b) c)
      (paperComm (paperComm a b) c ^ v) := by
  have hinner : ModEq (gamma G 5) (paperComm (a ^ v) b)
      (paperComm a b ^ v) :=
    paperComm_zpow_left_mod_gamma (n := 5) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) ha hb v
  have hlift := paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hc
  have hab : paperComm a b ∈ gamma G 3 :=
    paperComm_mem_gamma_add (r := 2) (s := 1)
      (by norm_num) (by norm_num) ha hb
  exact hlift.trans
    (paperComm_zpow_left_mod_gamma_six_of_weights
      (r := 3) (s := 1) (by norm_num) (by norm_num) (by norm_num) hab hc v)

end

end D5
