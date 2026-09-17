import D5.CollectionWeighted

/-!
# Hall--Witt rotation with weight control

This file proves the leading (weight-four) part of formula (19).  The full
formula modulo `γ₆` retains the weight-five conjugation corrections; here
they are deliberately killed modulo `γ₅` to verify the Hall--Witt core
before those corrections are expanded.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

/-- The multiplicative Jacobi rotation in the weights occurring in (19),
one level below the final truncation. -/
theorem rotation_main_mod_gamma_five
    {a b c : G} (ha : a ∈ gamma G 2)
    (hb : b ∈ gamma G 1) (hc : c ∈ gamma G 1) :
    ModEq (gamma G 5) (paperComm (paperComm a b) c)
      ((paperComm (paperComm c a) b)⁻¹ * paperComm (paperComm c b) a) := by
  let A := paperComm (paperComm a b) c
  let B := paperComm (paperComm c b) a
  let C := paperComm (paperComm c a) b
  have hab : paperComm a b ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb
  have hcb : paperComm c b ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hc hb
  have hca : paperComm c a ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hc ha
  have hA : A ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hab hc
  have hB : B ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hcb ha
  have hC : C ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hca hb

  have hinner1 : ModEq (gamma G 4) (paperComm a b⁻¹) (paperComm a b)⁻¹ :=
    paperComm_inv_right_mod_gamma (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) ha hb
  have hlift1 := paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hinner1 hc
  have hinv1 : ModEq (gamma G 5)
      (paperComm (paperComm a b)⁻¹ c) A⁻¹ := by
    exact paperComm_inv_left_mod_gamma (n := 5) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hab hc
  have hbase1 : ModEq (gamma G 5)
      (paperComm (paperComm a b⁻¹) c) A⁻¹ := hlift1.trans hinv1
  have hraw1 : paperComm (paperComm a b⁻¹) c ∈ gamma G 4 := by
    have hi : paperComm a b⁻¹ ∈ gamma G 3 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) ha
        ((gamma G 1).inv_mem hb)
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hi hc
  have hterm1 : ModEq (gamma G 5)
      (conjugateBy (paperComm (paperComm a b⁻¹) c) b) A⁻¹ :=
    (conjugateBy_mod_gamma (n := 5) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hraw1 hb).trans hbase1

  have hinner2 : ModEq (gamma G 3) (paperComm b c⁻¹) (paperComm c b) := by
    have h := paperComm_inv_right_mod_gamma (n := 3) (r := 1) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hb hc
    rw [← paperComm_swap b c] at h
    exact h
  have hbase2 : ModEq (gamma G 5)
      (paperComm (paperComm b c⁻¹) a) B :=
    paperComm_left_of_modEq_gamma
      (r := 3) (s := 2) (by norm_num) (by norm_num) hinner2 ha
  have hraw2 : paperComm (paperComm b c⁻¹) a ∈ gamma G 4 := by
    have hi : paperComm b c⁻¹ ∈ gamma G 2 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hb
        ((gamma G 1).inv_mem hc)
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hi ha
  have hterm2 : ModEq (gamma G 5)
      (conjugateBy (paperComm (paperComm b c⁻¹) a) c) B :=
    (conjugateBy_mod_gamma (n := 5) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hraw2 hc).trans hbase2

  have hinner3 : ModEq (gamma G 4) (paperComm c a⁻¹) (paperComm c a)⁻¹ :=
    paperComm_inv_right_mod_gamma (n := 4) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hc ha
  have hlift3 := paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hinner3 hb
  have hinv3 : ModEq (gamma G 5)
      (paperComm (paperComm c a)⁻¹ b) C⁻¹ :=
    paperComm_inv_left_mod_gamma (n := 5) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hca hb
  have hbase3 : ModEq (gamma G 5)
      (paperComm (paperComm c a⁻¹) b) C⁻¹ := hlift3.trans hinv3
  have hraw3 : paperComm (paperComm c a⁻¹) b ∈ gamma G 4 := by
    have hi : paperComm c a⁻¹ ∈ gamma G 3 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hc
        ((gamma G 2).inv_mem ha)
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hi hb
  have hterm3 : ModEq (gamma G 5)
      (conjugateBy (paperComm (paperComm c a⁻¹) b) a) C⁻¹ :=
    (conjugateBy_mod_gamma (n := 5) (r := 4) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hraw3 ha).trans hbase3

  have hHall : ModEq (gamma G 5)
      (conjugateBy (paperComm (paperComm a b⁻¹) c) b *
        conjugateBy (paperComm (paperComm b c⁻¹) a) c *
        conjugateBy (paperComm (paperComm c a⁻¹) b) a) 1 := by
    rw [hallWitt]
  have happrox : ModEq (gamma G 5) (A⁻¹ * B * C⁻¹) 1 :=
    ((hterm1.mul hterm2).mul hterm3).symm.trans hHall
  have hsolve : ModEq (gamma G 5) A (B * C⁻¹) := by
    change (A : G ⧸ gamma G 5) = (B : G ⧸ gamma G 5) * (C : G ⧸ gamma G 5)⁻¹
    have hq : ((A⁻¹ * B * C⁻¹ : G) : G ⧸ gamma G 5) = 1 := happrox
    calc
      (A : G ⧸ gamma G 5) = A * 1 := by simp
      _ = (A : G ⧸ gamma G 5) * ((A⁻¹ * B * C⁻¹ : G) : G ⧸ gamma G 5) := by rw [hq]
      _ = (B : G ⧸ gamma G 5) * (C : G ⧸ gamma G 5)⁻¹ := by
        change (A : G ⧸ gamma G 5) *
          ((A : G ⧸ gamma G 5)⁻¹ * (B : G ⧸ gamma G 5) *
            (C : G ⧸ gamma G 5)⁻¹) = _
        group
  have hcomm : ModEq (gamma G 5) (B * C⁻¹) (C⁻¹ * B) :=
    mul_comm_mod_gamma (n := 5) (r := 4) (s := 4)
      (by norm_num) (by norm_num) (by norm_num) hB ((gamma G 4).inv_mem hC)
  exact hsolve.trans hcomm

end

end D5
