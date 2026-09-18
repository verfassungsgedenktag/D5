import D5.TaharaWeights
import D5.Transfer22

/-!
# Formula (22) for the Tahara coordinates
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The product of second-weight generators appearing in formulas
(21)--(23). -/
def formula22WeightTwoWord (C : Context G) (P : Parameters C.s C.t)
    (j : Fin C.s) : G :=
  orderedProduct fun p => C.x2 p ^ (-P.v j p)

theorem formula22WeightTwoWord_mem_gamma2
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) :
    formula22WeightTwoWord C P j ∈ D5.gamma G 2 := by
  apply orderedProduct_mem
  intro p
  exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _

/-- The paper's formula (22), with its ordered product written exactly in
Tahara coordinates. -/
theorem transfer_formula22
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (formula22WeightTwoWord C P j ^ orderInt C.d j))
        (C.x1 j))
      (D5.paperComm
          (D5.paperComm ξ (formula22WeightTwoWord C P j))
          (C.x1 j ^ orderInt C.d j) *
        D5.paperComm
          (D5.paperComm
            (D5.paperComm (formula22WeightTwoWord C P j) ξ) (C.x1 j))
          (C.x1 j) ^ TaharaArithmetic.binom2 (C.d j)) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  simpa [orderInt] using D5.transfer_formula22 hξ
    (formula22WeightTwoWord_mem_gamma2 C P j) hx (C.d j)

end

end D5.Tahara
