import D5.TaharaPair
import D5.Weight

/-!
# Weights of the blocks in Tahara's representative

This verifies the first bookkeeping assertion of Section 5: the first block
of (4.3.1) lies in `γ₃`, the other two blocks lie in `γ₄`, and hence the full
representative lies in `γ₃`.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

namespace Context

theorem x2_mem_gamma2 (C : Context G) (p : Fin C.t) :
    C.x2 p ∈ D5.gamma G 2 :=
  C.basis2.1 p

theorem x3_mem_gamma3 (C : Context G) (l : Fin C.r) :
    C.x3 l ∈ D5.gamma G 3 :=
  C.basis3.1 l

theorem x1_order_power_mem_gamma2 (C : Context G) (i : Fin C.s) :
    C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 := by
  have hx2prod : orderedProduct (fun p => C.x2 p ^ C.b i p) ∈ D5.gamma G 2 :=
    orderedProduct_mem (D5.gamma G 2) _ fun p =>
      (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _
  have hx3prod : orderedProduct (fun l => C.x3 l ^ C.c i l) ∈ D5.gamma G 2 :=
    orderedProduct_mem (D5.gamma G 2) _ fun l =>
      (D5.gamma_antitone G (by norm_num : 2 ≤ 3))
        ((D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _)
  apply D5.mem_of_modEq_of_le (D5.gamma_antitone G (by norm_num : 2 ≤ 4))
    (C.x1_power i)
  exact (D5.gamma G 2).mul_mem hx2prod hx3prod

theorem x1_later_order_power_mem_gamma2 (C : Context G)
    {i j : Fin C.s} (hij : i ≤ j) :
    C.x1 i ^ orderInt C.d j ∈ D5.gamma G 2 := by
  have hdvd := C.d_dvd i j hij
  have heNat : C.d j = C.d i * (C.d j / C.d i) := by
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdvd).symm
  have heZ : orderInt C.d j =
      orderInt C.d i * orderRatio C.d i j := by
    have h : (C.d j : ℤ) = (C.d i : ℤ) * ((C.d j / C.d i : ℕ) : ℤ) := by
      exact_mod_cast heNat
    simpa [orderInt, orderRatio] using h
  rw [heZ, zpow_mul]
  exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 i) _

theorem x1_parameter_power_mem_gamma2 (C : Context G)
    {i j : Fin C.s} (hij : i ≤ j) (u : ℤ) :
    C.x1 i ^ (u * orderInt C.d j) ∈ D5.gamma G 2 := by
  rw [mul_comm, zpow_mul]
  exact (D5.gamma G 2).zpow_mem (C.x1_later_order_power_mem_gamma2 hij) u

end Context

/-- First block of (4.3.1). -/
def firstBlock (C : Context G) (P : Parameters C.s C.t) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    D5.paperComm (C.x1 i ^ (P.u i j * orderInt C.d j)) (C.x1 j)

/-- Second block of (4.3.1). -/
def secondBlock (C : Context G) (P : Parameters C.s C.t) : G :=
  orderedProduct fun i => orderedProduct fun p =>
    orderedProductWhere (p < ·) fun q =>
      D5.paperComm (C.x2 q) (C.x2 p) ^ (C.b i q * P.v i p)

/-- Third block of (4.3.1). -/
def thirdBlock (C : Context G) (P : Parameters C.s C.t) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k] ^ P.w i j k

theorem word_eq_blocks (C : Context G) (P : Parameters C.s C.t) :
    word C P = firstBlock C P * secondBlock C P * thirdBlock C P :=
  rfl

theorem firstBlock_mem_gamma3 (C : Context G) (P : Parameters C.s C.t) :
    firstBlock C P ∈ D5.gamma G 3 := by
  apply orderedProduct_mem
  intro i
  apply orderedProductWhere_mem
  intro j hij
  exact D5.paperComm_mem_gamma_add (r := 2) (s := 1)
    (by norm_num) (by norm_num)
    (C.x1_parameter_power_mem_gamma2 (le_of_lt hij) (P.u i j))
    (by simp [D5.gamma])

theorem secondBlock_mem_gamma4 (C : Context G) (P : Parameters C.s C.t) :
    secondBlock C P ∈ D5.gamma G 4 := by
  apply orderedProduct_mem
  intro i
  apply orderedProduct_mem
  intro p
  apply orderedProductWhere_mem
  intro q hpq
  apply (D5.gamma G 4).zpow_mem
  exact D5.paperComm_mem_gamma_add (r := 2) (s := 2)
    (by norm_num) (by norm_num) (C.x2_mem_gamma2 q) (C.x2_mem_gamma2 p)

theorem thirdBlock_mem_gamma4 (C : Context G) (P : Parameters C.s C.t) :
    thirdBlock C P ∈ D5.gamma G 4 := by
  apply orderedProduct_mem
  intro i
  apply orderedProductWhere_mem
  intro j hij
  apply orderedProductWhere_mem
  intro k hjk
  apply (D5.gamma G 4).zpow_mem
  simpa using D5.leftComm_mem_gamma_of_first (r := 2) (by norm_num)
    (C.x1_order_power_mem_gamma2 i) [C.x1 j, C.x1 k]

theorem word_mem_gamma3 (C : Context G) (P : Parameters C.s C.t) :
    word C P ∈ D5.gamma G 3 := by
  rw [word_eq_blocks]
  have h43 : D5.gamma G 4 ≤ D5.gamma G 3 :=
    D5.gamma_antitone G (by norm_num)
  exact (D5.gamma G 3).mul_mem
    ((D5.gamma G 3).mul_mem (firstBlock_mem_gamma3 C P)
      (h43 (secondBlock_mem_gamma4 C P)))
    (h43 (thirdBlock_mem_gamma4 C P))

end

end D5.Tahara
