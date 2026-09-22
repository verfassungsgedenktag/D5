import D5.TaharaCondition13

/-!
# The local alpha-coordinate expansion for formula (28)

Relation (3) expresses a power commutator of first-layer generators in the
`x₃` coordinates.  Here it is transported through the two commutators used
in formula (28).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

def alphaCoordinateBlock
    (C : Context G) (ξ : G) (i g h : Fin C.s) : G :=
  orderedProduct fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^ C.alpha g h l

theorem alpha_coordinate_expansion
    (C : Context G) (ξ : G) (i g h : Fin C.s) (hgh : g < h) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
        (C.x1 i))
      (alphaCoordinateBlock C ξ i g h) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hreplace := nested_middle_of_modEq_gamma4 hξ hxi
    (C.x1_power_comm g h hgh)
  have hcollect := nested_weight_three_orderedProduct_right hξ hxi
    (fun l => C.x3 l ^ C.alpha g h l)
    (fun l => (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _)
  refine (show D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
        (C.x1 i))
      (orderedProduct fun l =>
        D5.paperComm
          (D5.paperComm ξ (C.x3 l ^ C.alpha g h l)) (C.x1 i)) by
    exact hreplace.trans <| hcollect).trans ?_
  unfold alphaCoordinateBlock
  apply modEq_orderedProduct
  intro l
  exact nested_weight_three_zpow_right hξ (C.x3_mem_gamma3 l) hxi _

theorem alpha_coordinate_expansion_zpow
    (C : Context G) (ξ : G) (i g h : Fin C.s) (hgh : g < h)
    (z : ℤ) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
        (C.x1 i) ^ z)
      (orderedProduct fun l =>
        D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
          (z * C.alpha g h l)) := by
  let A : Fin C.r → G := fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hbase := (alpha_coordinate_expansion C ξ i g h hgh).zpow z
  have hA : ∀ l, A l ^ C.alpha g h l ∈ D5.gamma G 3 := by
    intro l
    apply (D5.gamma G 3).zpow_mem
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x3_mem_gamma3 l)) hxi
  have hdistribute := D5.orderedProduct_zpow_gammaThree
    (fun l => A l ^ C.alpha g h l) hA z
  refine hbase.trans <| hdistribute.trans ?_
  apply modEq_orderedProduct
  intro l
  change D5.ModGammaSix ((A l ^ C.alpha g h l) ^ z)
    (A l ^ (z * C.alpha g h l))
  rw [← zpow_mul]
  congr 1
  ring

end

end D5.Tahara
