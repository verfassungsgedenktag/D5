import D5.TaharaExpand
import D5.CollectionWeighted
import D5.AbelianCollectionSix
import D5.TaharaCondition6
import D5.TaharaTransfer22

/-!
# Structural replacement used in formula (21)

This file verifies the local use of relation (1): after two commutators,
the `γ₄` congruence for `x₁ⱼ ^ d(j)` may be substituted modulo `γ₆`, and
its second- and third-weight coordinate blocks split without extra terms.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

def x1PowerSecondBlock (C : Context G) (j : Fin C.s) : G :=
  orderedProduct fun p => C.x2 p ^ C.b j p

def x1PowerThirdBlock (C : Context G) (j : Fin C.s) : G :=
  orderedProduct fun l => C.x3 l ^ C.c j l

theorem x1PowerSecondBlock_mem_gamma2 (C : Context G) (j : Fin C.s) :
    x1PowerSecondBlock C j ∈ D5.gamma G 2 := by
  apply orderedProduct_mem
  intro p
  exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _

theorem x1PowerThirdBlock_mem_gamma3 (C : Context G) (j : Fin C.s) :
    x1PowerThirdBlock C j ∈ D5.gamma G 3 := by
  apply orderedProduct_mem
  intro l
  exact (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _

/-- The local structural expansion underlying formula (21). -/
theorem structural_expansion21_local
    (C : Context G) (ξ : G) (i j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i))
      (D5.paperComm
          (D5.paperComm ξ (x1PowerSecondBlock C j)) (C.x1 i) *
        D5.paperComm
          (D5.paperComm ξ (x1PowerThirdBlock C j)) (C.x1 i)) := by
  let X2 := x1PowerSecondBlock C j
  let X3 := x1PowerThirdBlock C j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX2 : X2 ∈ D5.gamma G 2 := x1PowerSecondBlock_mem_gamma2 C j
  have hX3 : X3 ∈ D5.gamma G 3 := x1PowerThirdBlock_mem_gamma3 C j
  have hrelation : D5.ModEq (D5.gamma G 4)
      (C.x1 j ^ orderInt C.d j) (X2 * X3) := by
    simpa [X2, X3, x1PowerSecondBlock, x1PowerThirdBlock] using
      C.x1_power j
  have hfirst : D5.ModEq (D5.gamma G 5)
      (D5.paperComm ξ (C.x1 j ^ orderInt C.d j))
      (D5.paperComm ξ (X2 * X3)) :=
    D5.paperComm_right_of_modEq_gamma
      (r := 1) (s := 4) (by norm_num) (by norm_num) hrelation hξ
  have hreplace : D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i))
      (D5.paperComm (D5.paperComm ξ (X2 * X3)) (C.x1 i)) :=
    D5.paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hfirst hxi
  have hinnerSplit : D5.ModEq (D5.gamma G 5)
      (D5.paperComm ξ (X2 * X3))
      (D5.paperComm ξ X2 * D5.paperComm ξ X3) :=
    D5.paperComm_mul_right_mod_gamma
      (n := 5) (r := 1) (s := 2) (t := 3)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hξ hX2 hX3
  have hliftSplit : D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (X2 * X3)) (C.x1 i))
      (D5.paperComm
        (D5.paperComm ξ X2 * D5.paperComm ξ X3) (C.x1 i)) :=
    D5.paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hinnerSplit hxi
  have hξX2 : D5.paperComm ξ X2 ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hX2
  have hξX3 : D5.paperComm ξ X3 ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hX3
  have houterSplit : D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ X2 * D5.paperComm ξ X3) (C.x1 i))
      (D5.paperComm (D5.paperComm ξ X2) (C.x1 i) *
        D5.paperComm (D5.paperComm ξ X3) (C.x1 i)) :=
    D5.paperComm_mul_left_mod_gamma
      (n := 6) (r := 3) (s := 4) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hξX2 hξX3 hxi
  simpa [X2, X3] using hreplace.trans (hliftSplit.trans houterSplit)

/-- A power in a weight-three second argument can be extracted through the
two nested commutators used in (21). -/
theorem nested_weight_three_zpow_right
    {ξ y x : G} (hξ : ξ ∈ D5.gamma G 1) (hy : y ∈ D5.gamma G 3)
    (hx : x ∈ D5.gamma G 1) (v : ℤ) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (y ^ v)) x)
      (D5.paperComm (D5.paperComm ξ y) x ^ v) := by
  have hinner : D5.ModEq (D5.gamma G 5)
      (D5.paperComm ξ (y ^ v)) (D5.paperComm ξ y ^ v) :=
    D5.paperComm_zpow_right_mod_gamma
      (n := 5) (r := 1) (s := 3)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hξ hy v
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hx
  have hξy : D5.paperComm ξ y ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hy
  exact hlift.trans <| D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 4) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hξy hx v

/-- Nested commutators distribute over a list of weight-three elements. -/
theorem nested_weight_three_listProd_right
    {ξ x : G} (hξ : ξ ∈ D5.gamma G 1) (hx : x ∈ D5.gamma G 1)
    (ys : List G) (hys : ∀ y ∈ ys, y ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ ys.prod) x)
      ((ys.map fun y => D5.paperComm (D5.paperComm ξ y) x).prod) := by
  induction ys with
  | nil =>
      simpa [D5.paperComm_eq] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)
  | cons y ys ih =>
      have hy : y ∈ D5.gamma G 3 := hys y (by simp)
      have htail : ys.prod ∈ D5.gamma G 3 :=
        listProd_mem (D5.gamma G 3) ys fun z hz => hys z (by simp [hz])
      have hinner : D5.ModEq (D5.gamma G 5)
          (D5.paperComm ξ (y * ys.prod))
          (D5.paperComm ξ y * D5.paperComm ξ ys.prod) :=
        D5.paperComm_mul_right_mod_gamma
          (n := 5) (r := 1) (s := 3) (t := 3)
          (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) hξ hy htail
      have hlift := D5.paperComm_left_of_modEq_gamma
        (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hx
      have hhead : D5.paperComm ξ y ∈ D5.gamma G 4 :=
        D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hy
      have hrest : D5.paperComm ξ ys.prod ∈ D5.gamma G 4 :=
        D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ htail
      have hsplit : D5.ModGammaSix
          (D5.paperComm
            (D5.paperComm ξ y * D5.paperComm ξ ys.prod) x)
          (D5.paperComm (D5.paperComm ξ y) x *
            D5.paperComm (D5.paperComm ξ ys.prod) x) :=
        D5.paperComm_mul_left_mod_gamma
          (n := 6) (r := 4) (s := 4) (t := 1)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hhead hrest hx
      simp only [List.prod_cons, List.map_cons]
      exact (hlift.trans hsplit).trans <|
        (D5.ModEq.refl (D5.gamma G 6)
          (D5.paperComm (D5.paperComm ξ y) x)).mul
          (ih fun z hz => hys z (by simp [hz]))

theorem nested_weight_three_orderedProduct_right
    {ξ x : G} (hξ : ξ ∈ D5.gamma G 1) (hx : x ∈ D5.gamma G 1)
    {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (orderedProduct f)) x)
      (orderedProduct fun i => D5.paperComm (D5.paperComm ξ (f i)) x) := by
  unfold orderedProduct
  simpa [List.map_map] using nested_weight_three_listProd_right hξ hx
    ((List.finRange n).map f) (fun y hy => by
      rcases List.mem_map.mp hy with ⟨i, hi, rfl⟩
      exact hf i)

/-- Coordinate collection of the third-weight block in formula (21). -/
theorem structural_expansion21_third_block
    (C : Context G) (ξ : G) (i j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (x1PowerThirdBlock C j)) (C.x1 i))
      (orderedProduct fun l =>
        D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^ C.c j l) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hcollect := nested_weight_three_orderedProduct_right hξ hxi
    (fun l => C.x3 l ^ C.c j l)
    (fun l => (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _)
  refine (show D5.ModGammaSix
    (D5.paperComm
      (D5.paperComm ξ (x1PowerThirdBlock C j)) (C.x1 i))
    (orderedProduct fun l =>
      D5.paperComm (D5.paperComm ξ (C.x3 l ^ C.c j l)) (C.x1 i)) by
      simpa [x1PowerThirdBlock] using hcollect).trans ?_
  apply modEq_orderedProduct
  intro l
  exact nested_weight_three_zpow_right hξ (C.x3_mem_gamma3 l) hxi _

/-- The corresponding power extraction for a weight-two coordinate.  The
potential inner correction has weight five and disappears after the final
commutator. -/
theorem nested_weight_two_zpow_right
    {ξ y x : G} (hξ : ξ ∈ D5.gamma G 1) (hy : y ∈ D5.gamma G 2)
    (hx : x ∈ D5.gamma G 1) (v : ℤ) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (y ^ v)) x)
      (D5.paperComm (D5.paperComm ξ y) x ^ v) := by
  have hinner : D5.ModEq (D5.gamma G 5)
      (D5.paperComm ξ (y ^ v)) (D5.paperComm ξ y ^ v) :=
    D5.paperComm_zpow_right_mod_gamma
      (n := 5) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hξ hy v
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hx
  have hξy : D5.paperComm ξ y ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hy
  exact hlift.trans <| D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 3) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hξy hx v

theorem nested_weight_two_listProd_right
    {ξ x : G} (hξ : ξ ∈ D5.gamma G 1) (hx : x ∈ D5.gamma G 1)
    (ys : List G) (hys : ∀ y ∈ ys, y ∈ D5.gamma G 2) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ ys.prod) x)
      ((ys.map fun y => D5.paperComm (D5.paperComm ξ y) x).prod) := by
  induction ys with
  | nil =>
      simpa [D5.paperComm_eq] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)
  | cons y ys ih =>
      have hy : y ∈ D5.gamma G 2 := hys y (by simp)
      have htail : ys.prod ∈ D5.gamma G 2 :=
        listProd_mem (D5.gamma G 2) ys fun z hz => hys z (by simp [hz])
      have hinner : D5.ModEq (D5.gamma G 5)
          (D5.paperComm ξ (y * ys.prod))
          (D5.paperComm ξ y * D5.paperComm ξ ys.prod) :=
        D5.paperComm_mul_right_mod_gamma
          (n := 5) (r := 1) (s := 2) (t := 2)
          (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num) hξ hy htail
      have hlift := D5.paperComm_left_of_modEq_gamma
        (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hx
      have hhead : D5.paperComm ξ y ∈ D5.gamma G 3 :=
        D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hy
      have hrest : D5.paperComm ξ ys.prod ∈ D5.gamma G 3 :=
        D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ htail
      have hsplit : D5.ModGammaSix
          (D5.paperComm
            (D5.paperComm ξ y * D5.paperComm ξ ys.prod) x)
          (D5.paperComm (D5.paperComm ξ y) x *
            D5.paperComm (D5.paperComm ξ ys.prod) x) :=
        D5.paperComm_mul_left_mod_gamma
          (n := 6) (r := 3) (s := 3) (t := 1)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hhead hrest hx
      simp only [List.prod_cons, List.map_cons]
      exact (hlift.trans hsplit).trans <|
        (D5.ModEq.refl (D5.gamma G 6)
          (D5.paperComm (D5.paperComm ξ y) x)).mul
          (ih fun z hz => hys z (by simp [hz]))

theorem nested_weight_two_orderedProduct_right
    {ξ x : G} (hξ : ξ ∈ D5.gamma G 1) (hx : x ∈ D5.gamma G 1)
    {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ D5.gamma G 2) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (orderedProduct f)) x)
      (orderedProduct fun i => D5.paperComm (D5.paperComm ξ (f i)) x) := by
  unfold orderedProduct
  simpa [List.map_map] using nested_weight_two_listProd_right hξ hx
    ((List.finRange n).map f) (fun y hy => by
      rcases List.mem_map.mp hy with ⟨i, hi, rfl⟩
      exact hf i)

/-- Coordinate collection of the second-weight block in formula (21). -/
theorem structural_expansion21_second_block
    (C : Context G) (ξ : G) (i j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (x1PowerSecondBlock C j)) (C.x1 i))
      (orderedProduct fun p =>
        D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^ C.b j p) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hcollect := nested_weight_two_orderedProduct_right hξ hxi
    (fun p => C.x2 p ^ C.b j p)
    (fun p => (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _)
  refine (show D5.ModGammaSix
    (D5.paperComm
      (D5.paperComm ξ (x1PowerSecondBlock C j)) (C.x1 i))
    (orderedProduct fun p =>
      D5.paperComm (D5.paperComm ξ (C.x2 p ^ C.b j p)) (C.x1 i)) by
      simpa [x1PowerSecondBlock] using hcollect).trans ?_
  apply modEq_orderedProduct
  intro p
  exact nested_weight_two_zpow_right hξ (C.x2_mem_gamma2 p) hxi _

/-- Relation (1) fully expanded into its individual second- and third-layer
coordinates.  The remaining part of global formula (21) is finite-product
reindexing and collection of the integer exponents. -/
theorem structural_expansion21_coordinates
    (C : Context G) (ξ : G) (i j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i))
      ((orderedProduct fun p =>
          D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^ C.b j p) *
        (orderedProduct fun l =>
          D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^ C.c j l)) := by
  exact (structural_expansion21_local C ξ i j).trans <|
    (structural_expansion21_second_block C ξ i j).mul
      (structural_expansion21_third_block C ξ i j)

/-- Powered coordinate form of the local structural expansion.  This is the
form used when the two pairwise factors of (21) are multiplied globally. -/
theorem structural_expansion21_coordinates_zpow
    (C : Context G) (ξ : G) (i j : Fin C.s) (u : ℤ) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^ u)
      ((orderedProduct fun p =>
          D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^
            (u * C.b j p)) *
        (orderedProduct fun l =>
          D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
            (u * C.c j l))) := by
  let F2 : Fin C.t → G := fun p =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i)
  let F3 : Fin C.r → G := fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hF2 : ∀ p, F2 p ∈ D5.gamma G 3 := by
    intro p
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x2_mem_gamma2 p)) hxi
  have hF3 : ∀ l, F3 l ∈ D5.gamma G 3 := by
    intro l
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x3_mem_gamma3 l)) hxi
  have hB2 : orderedProduct (fun p => F2 p ^ C.b j p) ∈ D5.gamma G 3 :=
    orderedProduct_mem (D5.gamma G 3) _ fun p =>
      (D5.gamma G 3).zpow_mem (hF2 p) _
  have hB3 : orderedProduct (fun l => F3 l ^ C.c j l) ∈ D5.gamma G 3 :=
    orderedProduct_mem (D5.gamma G 3) _ fun l =>
      (D5.gamma G 3).zpow_mem (hF3 l) _
  have hbase := (structural_expansion21_coordinates C ξ i j).zpow u
  have hsplit := D5.gammaThree_mul_zpow hB2 hB3 u
  have hpow2 := D5.orderedProduct_zpow_gammaThree
    (fun p => F2 p ^ C.b j p)
    (fun p => (D5.gamma G 3).zpow_mem (hF2 p) _) u
  have hpow3 := D5.orderedProduct_zpow_gammaThree
    (fun l => F3 l ^ C.c j l)
    (fun l => (D5.gamma G 3).zpow_mem (hF3 l) _) u
  refine hbase.trans <| hsplit.trans <| (hpow2.mul hpow3).trans ?_
  apply (modEq_orderedProduct (N := D5.gamma G 6) (fun p => by
    simp only [F2, ← zpow_mul]
    congr 1
    ring_nf)).mul
  apply modEq_orderedProduct
  intro l
  simp only [F3, ← zpow_mul]
  congr 1
  ring_nf

/-- The two powered structural factors belonging to one pair `i < j` in
formula (21), expanded into second- and third-layer coordinates. -/
theorem structural_expansion21_pair
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
          (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j) ^
            (-P.u i j * orderRatio C.d i j) *
        D5.paperComm
          (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^
            P.u i j)
      (((orderedProduct fun p =>
          D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 j) ^
            ((-P.u i j * orderRatio C.d i j) * C.b i p)) *
        (orderedProduct fun l =>
          D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 j) ^
            ((-P.u i j * orderRatio C.d i j) * C.c i l))) *
        ((orderedProduct fun p =>
          D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^
            (P.u i j * C.b j p)) *
        (orderedProduct fun l =>
          D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
            (P.u i j * C.c j l)))) := by
  exact (structural_expansion21_coordinates_zpow C ξ j i
    (-P.u i j * orderRatio C.d i j)).mul
      (structural_expansion21_coordinates_zpow C ξ i j (P.u i j))

/-- The product of the two main terms left after formulas (19)--(20). -/
def formula21MainPairProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    D5.paperComm
        (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j) ^
          (-P.u i j * orderRatio C.d i j) *
      D5.paperComm
        (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^
          P.u i j

/-- Pairwise coordinate expansion before exchanging the finite product
loops and adding equal-base exponents. -/
def formula21RawCoordinateProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    ((orderedProduct fun p =>
        D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 j) ^
          ((-P.u i j * orderRatio C.d i j) * C.b i p)) *
      (orderedProduct fun l =>
        D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 j) ^
          ((-P.u i j * orderRatio C.d i j) * C.c i l))) *
      ((orderedProduct fun p =>
        D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^
          (P.u i j * C.b j p)) *
      (orderedProduct fun l =>
        D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
          (P.u i j * C.c j l)))

def formula21SecondCoordinateBlock
    (C : Context G) (ξ : G) (k : Fin C.s) (e : Fin C.t → ℤ) : G :=
  orderedProduct fun p =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 k) ^ e p

def formula21ThirdCoordinateBlock
    (C : Context G) (ξ : G) (k : Fin C.s) (e : Fin C.r → ℤ) : G :=
  orderedProduct fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 k) ^ e l

theorem formula21SecondCoordinateBlock_mem_gamma3
    (C : Context G) (ξ : G) (k : Fin C.s) (e : Fin C.t → ℤ) :
    formula21SecondCoordinateBlock C ξ k e ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  apply orderedProduct_mem
  intro p
  apply (D5.gamma G 3).zpow_mem
  exact D5.gamma_antitone G (by norm_num) <|
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        hξ (C.x2_mem_gamma2 p)) hx

theorem formula21ThirdCoordinateBlock_mem_gamma3
    (C : Context G) (ξ : G) (k : Fin C.s) (e : Fin C.r → ℤ) :
    formula21ThirdCoordinateBlock C ξ k e ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  apply orderedProduct_mem
  intro l
  apply (D5.gamma G 3).zpow_mem
  exact D5.gamma_antitone G (by norm_num) <|
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        hξ (C.x3_mem_gamma3 l)) hx

def formula21LowSecondPairBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  formula21SecondCoordinateBlock C ξ j fun p =>
    (-P.u i j * orderRatio C.d i j) * C.b i p

def formula21LowThirdPairBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  formula21ThirdCoordinateBlock C ξ j fun l =>
    (-P.u i j * orderRatio C.d i j) * C.c i l

def formula21HighSecondPairBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  formula21SecondCoordinateBlock C ξ i fun p => P.u i j * C.b j p

def formula21HighThirdPairBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  formula21ThirdCoordinateBlock C ξ i fun l => P.u i j * C.c j l

def strictPairProduct {s : ℕ} (f : Fin s → Fin s → G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) (f i)

/-- Exchange the two loops over the strict upper triangle. -/
theorem strictPairProduct_swap
    {s : ℕ} (f : Fin s → Fin s → G)
    (hf : ∀ i j, i < j → f i j ∈ D5.gamma G 3) :
    D5.ModGammaSix (strictPairProduct f)
      (orderedProduct fun j => orderedProductWhere (· < j) fun i => f i j) := by
  classical
  let all := List.finRange s
  let rows := (all ×ˢ all).filter fun ij => ij.1 < ij.2
  let cols := ((all ×ˢ all).map fun ij => (ij.2, ij.1)).filter
    fun ij => ij.1 < ij.2
  have hall : all.Nodup := by simpa [all] using List.nodup_finRange s
  have hswapInj : Function.Injective (fun ij : Fin s × Fin s => (ij.2, ij.1)) := by
    intro a b h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hrows : rows.Nodup := (hall.product hall).filter _
  have hcols : cols.Nodup := ((hall.product hall).map hswapInj).filter _
  have hpairs : rows.Perm cols := by
    apply (List.perm_ext_iff_of_nodup hrows hcols).2
    intro ij
    have hrmem : ij ∈ all ×ˢ all := List.mem_product.mpr ⟨by simp [all], by simp [all]⟩
    have hcmem : ij ∈ (all ×ˢ all).map (fun ab => (ab.2, ab.1)) := by
      apply List.mem_map.mpr
      exact ⟨(ij.2, ij.1),
        List.mem_product.mpr ⟨by simp [all], by simp [all]⟩, by simp⟩
    simp [rows, cols, hrmem, hcmem]
  have flattenFiltered : ∀ {α β : Type} (is : List α) (js : List β)
      (p : α → β → Prop) [DecidableRel p] (g : α → β → G),
      (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
        (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
          fun ij => g ij.1 ij.2).prod := by
    intro α β is js p inst g
    induction is with
    | nil => simp
    | cons i is ih =>
        rw [List.map_cons, List.prod_cons, List.product_cons,
          List.filter_append, List.map_append, List.prod_append, ih]
        congr 1
        have hlist :
            (js.filter (p i)).map (g i) =
              ((js.map fun b => (i, b)).filter fun ij => p ij.1 ij.2).map
                fun ij => g ij.1 ij.2 := by
          simp only [List.filter_map, List.map_map]
          rfl
        exact congrArg List.prod hlist
  have hrowEq : strictPairProduct f =
      (rows.map fun ij => f ij.1 ij.2).prod := by
    unfold strictPairProduct orderedProduct orderedProductWhere
    simpa [rows, all] using
      flattenFiltered (List.finRange s) (List.finRange s)
        (fun i j => i < j) f
  have hcolEq :
      (orderedProduct fun j => orderedProductWhere (· < j) fun i => f i j) =
      (cols.map fun ij => f ij.1 ij.2).prod := by
    unfold orderedProduct orderedProductWhere
    have hflat := flattenFiltered (List.finRange s) (List.finRange s)
      (fun j i => i < j) (fun j i => f i j)
    simpa [cols, all, List.filter_map] using hflat
  rw [hrowEq, hcolEq]
  apply D5.listProd_perm_gammaThree (hpairs.map _)
  intro x hx
  rcases List.mem_map.mp hx with ⟨ij, hij, rfl⟩
  have hp := of_decide_eq_true (List.mem_filter.mp hij).2
  exact hf ij.1 ij.2 hp

/-- The raw expansion split into its four independent triangular streams. -/
theorem structural_expansion21_split_streams
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula21RawCoordinateProduct C P ξ)
      ((strictPairProduct (formula21LowSecondPairBlock C P ξ) *
          strictPairProduct (formula21LowThirdPairBlock C P ξ)) *
        (strictPairProduct (formula21HighSecondPairBlock C P ξ) *
          strictPairProduct (formula21HighThirdPairBlock C P ξ))) := by
  let L2 := formula21LowSecondPairBlock C P ξ
  let L3 := formula21LowThirdPairBlock C P ξ
  let H2 := formula21HighSecondPairBlock C P ξ
  let H3 := formula21HighThirdPairBlock C P ξ
  have hL2 : ∀ i j, L2 i j ∈ D5.gamma G 3 := fun i j =>
    formula21SecondCoordinateBlock_mem_gamma3 C ξ j _
  have hL3 : ∀ i j, L3 i j ∈ D5.gamma G 3 := fun i j =>
    formula21ThirdCoordinateBlock_mem_gamma3 C ξ j _
  have hH2 : ∀ i j, H2 i j ∈ D5.gamma G 3 := fun i j =>
    formula21SecondCoordinateBlock_mem_gamma3 C ξ i _
  have hH3 : ∀ i j, H3 i j ∈ D5.gamma G 3 := fun i j =>
    formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _
  have hinner : D5.ModGammaSix (formula21RawCoordinateProduct C P ξ)
      (orderedProduct fun i =>
        ((orderedProductWhere (i < ·) (L2 i) *
          orderedProductWhere (i < ·) (L3 i)) *
        (orderedProductWhere (i < ·) (H2 i) *
          orderedProductWhere (i < ·) (H3 i)))) := by
    unfold formula21RawCoordinateProduct
    apply modEq_orderedProduct
    intro i
    simpa [L2, L3, H2, H3, formula21LowSecondPairBlock,
      formula21LowThirdPairBlock, formula21HighSecondPairBlock,
      formula21HighThirdPairBlock, formula21SecondCoordinateBlock,
      formula21ThirdCoordinateBlock] using
        D5.orderedProductWhere_four_gammaThree (i < ·)
          (L2 i) (L3 i) (H2 i) (H3 i)
          (fun j hij => hL2 i j) (fun j hij => hL3 i j)
          (fun j hij => hH2 i j) (fun j hij => hH3 i j)
  have hstream (F : Fin C.s → Fin C.s → G)
      (hF : ∀ i j, F i j ∈ D5.gamma G 3) :
      ∀ i, orderedProductWhere (i < ·) (F i) ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hF i j
  have houter := D5.orderedProduct_four_gammaThree
    (fun i => orderedProductWhere (i < ·) (L2 i))
    (fun i => orderedProductWhere (i < ·) (L3 i))
    (fun i => orderedProductWhere (i < ·) (H2 i))
    (fun i => orderedProductWhere (i < ·) (H3 i))
    (hstream L2 hL2) (hstream L3 hL3) (hstream H2 hH2) (hstream H3 hH3)
  exact hinner.trans <| by
    simpa [strictPairProduct, L2, L3, H2, H3] using houter

private theorem formula21_second_base_mem_gamma3
    (C : Context G) (ξ : G) (k : Fin C.s) (p : Fin C.t) :
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 k) ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact D5.gamma_antitone G (by norm_num) <|
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        hξ (C.x2_mem_gamma2 p)) hx

private theorem formula21_third_base_mem_gamma3
    (C : Context G) (ξ : G) (k : Fin C.s) (l : Fin C.r) :
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 k) ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact D5.gamma_antitone G (by norm_num) <|
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        hξ (C.x3_mem_gamma3 l)) hx

def formula21LowSecondGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => formula21SecondCoordinateBlock C ξ j fun p =>
    ∑ i ∈ Finset.univ.filter (· < j),
      (-P.u i j * orderRatio C.d i j) * C.b i p

def formula21HighSecondGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21SecondCoordinateBlock C ξ i fun p =>
    ∑ j ∈ Finset.univ.filter (i < ·), P.u i j * C.b j p

def formula21LowThirdGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => formula21ThirdCoordinateBlock C ξ j fun l =>
    ∑ i ∈ Finset.univ.filter (· < j),
      (-P.u i j * orderRatio C.d i j) * C.c i l

def formula21HighThirdGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    ∑ j ∈ Finset.univ.filter (i < ·), P.u i j * C.c j l

theorem formula21_low_second_grouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (strictPairProduct (formula21LowSecondPairBlock C P ξ))
      (formula21LowSecondGrouped C P ξ) := by
  have hswap := strictPairProduct_swap
    (formula21LowSecondPairBlock C P ξ)
    (fun i j hij => formula21SecondCoordinateBlock_mem_gamma3 C ξ j _)
  refine hswap.trans ?_
  unfold formula21LowSecondGrouped
  apply modEq_orderedProduct
  intro j
  simpa [formula21LowSecondPairBlock, formula21SecondCoordinateBlock] using
    D5.orderedProductWhere_coordinateBlocks_gammaThree (· < j)
      (fun p => D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 j))
      (formula21_second_base_mem_gamma3 C ξ j)
      (fun i p => (-P.u i j * orderRatio C.d i j) * C.b i p)

theorem formula21_high_second_grouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (strictPairProduct (formula21HighSecondPairBlock C P ξ))
      (formula21HighSecondGrouped C P ξ) := by
  unfold strictPairProduct formula21HighSecondGrouped
  apply modEq_orderedProduct
  intro i
  unfold formula21HighSecondPairBlock
  simpa [formula21SecondCoordinateBlock] using
    D5.orderedProductWhere_coordinateBlocks_gammaThree (i < ·)
      (fun p => D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i))
      (formula21_second_base_mem_gamma3 C ξ i)
      (fun j p => P.u i j * C.b j p)

theorem formula21_low_third_grouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (strictPairProduct (formula21LowThirdPairBlock C P ξ))
      (formula21LowThirdGrouped C P ξ) := by
  have hswap := strictPairProduct_swap
    (formula21LowThirdPairBlock C P ξ)
    (fun i j hij => formula21ThirdCoordinateBlock_mem_gamma3 C ξ j _)
  refine hswap.trans ?_
  unfold formula21LowThirdGrouped
  apply modEq_orderedProduct
  intro j
  simpa [formula21LowThirdPairBlock, formula21ThirdCoordinateBlock] using
    D5.orderedProductWhere_coordinateBlocks_gammaThree (· < j)
      (fun l => D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 j))
      (formula21_third_base_mem_gamma3 C ξ j)
      (fun i l => (-P.u i j * orderRatio C.d i j) * C.c i l)

theorem formula21_high_third_grouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (strictPairProduct (formula21HighThirdPairBlock C P ξ))
      (formula21HighThirdGrouped C P ξ) := by
  unfold strictPairProduct formula21HighThirdGrouped
  apply modEq_orderedProduct
  intro i
  unfold formula21HighThirdPairBlock
  simpa [formula21ThirdCoordinateBlock] using
    D5.orderedProductWhere_coordinateBlocks_gammaThree (i < ·)
      (fun l => D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i))
      (formula21_third_base_mem_gamma3 C ξ i)
      (fun j l => P.u i j * C.c j l)

/-- All four triangular streams collected by their outer generator. -/
theorem structural_expansion21_grouped_streams
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula21RawCoordinateProduct C P ξ)
      ((formula21LowSecondGrouped C P ξ *
          formula21LowThirdGrouped C P ξ) *
        (formula21HighSecondGrouped C P ξ *
          formula21HighThirdGrouped C P ξ)) := by
  exact (structural_expansion21_split_streams C P ξ).trans <|
    ((formula21_low_second_grouped C P ξ).mul
      (formula21_low_third_grouped C P ξ)).mul
    ((formula21_high_second_grouped C P ξ).mul
      (formula21_high_third_grouped C P ξ))

theorem formula21SecondCoordinateBlock_add
    (C : Context G) (ξ : G) (i : Fin C.s)
    (a b : Fin C.t → ℤ) :
    D5.ModGammaSix
      (formula21SecondCoordinateBlock C ξ i a *
        formula21SecondCoordinateBlock C ξ i b)
      (formula21SecondCoordinateBlock C ξ i fun p => a p + b p) := by
  let F : Fin C.t → G := fun p =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i)
  have hF : ∀ p, F p ∈ D5.gamma G 3 :=
    formula21_second_base_mem_gamma3 C ξ i
  have hsplit := D5.orderedProduct_pointwise_mul_gammaThree
    (fun p => F p ^ a p) (fun p => F p ^ b p)
    (fun p => (D5.gamma G 3).zpow_mem (hF p) _)
    (fun p => (D5.gamma G 3).zpow_mem (hF p) _)
  refine hsplit.symm.trans ?_
  unfold formula21SecondCoordinateBlock
  apply modEq_orderedProduct
  intro p
  change D5.ModGammaSix (F p ^ a p * F p ^ b p) (F p ^ (a p + b p))
  rw [zpow_add]

theorem formula21ThirdCoordinateBlock_add
    (C : Context G) (ξ : G) (i : Fin C.s)
    (a b : Fin C.r → ℤ) :
    D5.ModGammaSix
      (formula21ThirdCoordinateBlock C ξ i a *
        formula21ThirdCoordinateBlock C ξ i b)
      (formula21ThirdCoordinateBlock C ξ i fun l => a l + b l) := by
  let F : Fin C.r → G := fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hF : ∀ l, F l ∈ D5.gamma G 3 :=
    formula21_third_base_mem_gamma3 C ξ i
  have hsplit := D5.orderedProduct_pointwise_mul_gammaThree
    (fun l => F l ^ a l) (fun l => F l ^ b l)
    (fun l => (D5.gamma G 3).zpow_mem (hF l) _)
    (fun l => (D5.gamma G 3).zpow_mem (hF l) _)
  refine hsplit.symm.trans ?_
  unfold formula21ThirdCoordinateBlock
  apply modEq_orderedProduct
  intro l
  change D5.ModGammaSix (F l ^ a l * F l ^ b l) (F l ^ (a l + b l))
  rw [zpow_add]

def formula21SecondGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21SecondCoordinateBlock C ξ i fun p =>
    (∑ h ∈ Finset.univ.filter (· < i),
      (-P.u h i * orderRatio C.d h i) * C.b h p) +
    (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.b h p)

def formula21ThirdGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    (∑ h ∈ Finset.univ.filter (· < i),
      (-P.u h i * orderRatio C.d h i) * C.c h l) +
    (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l)

/-- The second-coordinate block after applying the integer identity in
Tahara condition (4.3.6). -/
def formula21SecondCondition6Grouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21SecondCoordinateBlock C ξ i fun p =>
    -P.v i p * orderInt C.d i - P.v' i p * orderInt C.e p

theorem formula21_second_grouped_condition6
    (C : Context G) (P : Parameters C.s C.t) (h6 : P.Condition6)
    (ξ : G) :
    D5.ModGammaSix
      (formula21SecondGrouped C P ξ)
      (formula21SecondCondition6Grouped C P ξ) := by
  unfold formula21SecondGrouped formula21SecondCondition6Grouped
  apply modEq_orderedProduct
  intro i
  unfold formula21SecondCoordinateBlock
  apply modEq_orderedProduct
  intro p
  have hlow :
      (∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderRatio C.d h i) * C.b h p) =
      -(∑ h ∈ Finset.univ.filter (· < i),
        P.u h i * orderRatio C.d h i * C.b h p) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  have hc := structuralSecondCoefficient_eq C P h6 i p
  unfold structuralSecondCoefficient at hc
  have hexp :
      (∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderRatio C.d h i) * C.b h p) +
      (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.b h p) =
      -P.v i p * orderInt C.d i - P.v' i p * orderInt C.e p := by
    rw [hlow]
    linarith
  change D5.ModGammaSix
    (D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^
      ((∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderRatio C.d h i) * C.b h p) +
       (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.b h p)))
    (D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^
      (-P.v i p * orderInt C.d i - P.v' i p * orderInt C.e p))
  rw [hexp]

/-- The first product on the right of formula (21). -/
def formula21WeightTwoPowerProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i =>
    D5.paperComm
      (D5.paperComm ξ
        (formula22WeightTwoWord C P i ^ orderInt C.d i))
      (C.x1 i)

/-- Expanding the powered weight-two word gives exactly the
`-vᵢₚ d(i)` part of the condition-(6) exponent. -/
theorem formula21_weight_two_power_coordinates
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (formula22WeightTwoWord C P i ^ orderInt C.d i))
        (C.x1 i))
      (formula21SecondCoordinateBlock C ξ i fun p =>
        -P.v i p * orderInt C.d i) := by
  let W := formula22WeightTwoWord C P i
  let A : Fin C.t → G := fun p =>
    D5.paperComm
      (D5.paperComm ξ (C.x2 p ^ (-P.v i p))) (C.x1 i)
  let B : Fin C.t → G := fun p =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hW : W ∈ D5.gamma G 2 := by
    simpa [W] using formula22WeightTwoWord_mem_gamma2 C P i
  have hA : ∀ p, A p ∈ D5.gamma G 3 := by
    intro p
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ ((D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _)) hx
  have hpower := nested_weight_two_zpow_right hξ hW hx (orderInt C.d i)
  have hcollect := nested_weight_two_orderedProduct_right hξ hx
    (fun p => C.x2 p ^ (-P.v i p))
    (fun p => (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _)
  have hcollectPower := hcollect.zpow (orderInt C.d i)
  have hdistribute := D5.orderedProduct_zpow_gammaThree A hA
    (orderInt C.d i)
  refine hpower.trans <| hcollectPower.trans <| hdistribute.trans ?_
  unfold formula21SecondCoordinateBlock
  apply modEq_orderedProduct
  intro p
  have hp := (nested_weight_two_zpow_right hξ
    (C.x2_mem_gamma2 p) hx (-P.v i p)).zpow (orderInt C.d i)
  simpa [A, B, ← zpow_mul] using hp

theorem formula21_weight_two_power_product_coordinates
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula21WeightTwoPowerProduct C P ξ)
      (orderedProduct fun i =>
        formula21SecondCoordinateBlock C ξ i fun p =>
          -P.v i p * orderInt C.d i) := by
  unfold formula21WeightTwoPowerProduct
  apply modEq_orderedProduct
  intro i
  exact formula21_weight_two_power_coordinates C P ξ i

/-- A congruence modulo `γ₄` in the middle argument may be transported
through the two commutators occurring in formula (21). -/
theorem nested_middle_of_modEq_gamma4
    {ξ y z x : G} (hξ : ξ ∈ D5.gamma G 1)
    (hx : x ∈ D5.gamma G 1)
    (hyz : D5.ModEq (D5.gamma G 4) y z) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ y) x)
      (D5.paperComm (D5.paperComm ξ z) x) := by
  have hinner : D5.ModEq (D5.gamma G 5)
      (D5.paperComm ξ y) (D5.paperComm ξ z) :=
    D5.paperComm_right_of_modEq_gamma
      (r := 1) (s := 4) (by norm_num) (by norm_num)
      hyz hξ
  exact D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num)
    hinner hx

/-- Relation (2), after applying the two commutators in (21), expanded
into the third-layer coordinates. -/
theorem formula21_x2_order_nested_coordinates
    (C : Context G) (ξ : G) (i : Fin C.s) (p : Fin C.t) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (C.x2 p ^ orderInt C.e p)) (C.x1 i))
      (formula21ThirdCoordinateBlock C ξ i fun l => C.delta p l) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hreplace := nested_middle_of_modEq_gamma4 hξ hx (C.x2_power p)
  have hcollect := nested_weight_three_orderedProduct_right hξ hx
    (fun l => C.x3 l ^ C.delta p l)
    (fun l => (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _)
  refine hreplace.trans <| hcollect.trans ?_
  unfold formula21ThirdCoordinateBlock
  apply modEq_orderedProduct
  intro l
  exact nested_weight_three_zpow_right hξ (C.x3_mem_gamma3 l) hx _

/-- The `-v'ᵢₚ e(p)` power in the second layer becomes the corresponding
row of the `δ` matrix in the third layer. -/
theorem formula21_x2_correction_coordinates
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) (p : Fin C.t) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i) ^
        (-P.v' i p * orderInt C.e p))
      (formula21ThirdCoordinateBlock C ξ i fun l =>
        -P.v' i p * C.delta p l) := by
  let B := D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x1 i)
  let T : Fin C.r → G := fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  let k := -P.v' i p
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hBpower := (nested_weight_two_zpow_right hξ
    (C.x2_mem_gamma2 p) hx (orderInt C.e p)).zpow k
  have hreplace := (formula21_x2_order_nested_coordinates C ξ i p).zpow k
  have hT : ∀ l, T l ^ C.delta p l ∈ D5.gamma G 3 := by
    intro l
    apply (D5.gamma G 3).zpow_mem
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x3_mem_gamma3 l)) hx
  have hdistribute := D5.orderedProduct_zpow_gammaThree
    (fun l => T l ^ C.delta p l) hT k
  have hstart : D5.ModGammaSix
      (B ^ (-P.v' i p * orderInt C.e p))
      ((D5.paperComm
        (D5.paperComm ξ (C.x2 p ^ orderInt C.e p)) (C.x1 i)) ^ k) := by
    have hs := hBpower.symm
    simpa [B, k, ← zpow_mul, mul_comm] using hs
  refine hstart.trans <| hreplace.trans <| hdistribute.trans ?_
  unfold formula21ThirdCoordinateBlock
  apply modEq_orderedProduct
  intro l
  change D5.ModGammaSix
    ((T l ^ C.delta p l) ^ k)
    (T l ^ (-P.v' i p * C.delta p l))
  have he : C.delta p l * k = -P.v' i p * C.delta p l := by
    dsimp [k]
    ring
  rw [← zpow_mul, he]

/-- The entire `v'` correction after collecting first by `p` and then by
the third-layer coordinate `l`. -/
def formula21DeltaCorrectionGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    -(∑ p, P.v' i p * C.delta p l)

theorem formula21_x2_corrections_collect
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) :
    D5.ModGammaSix
      (formula21SecondCoordinateBlock C ξ i fun p =>
        -P.v' i p * orderInt C.e p)
      (formula21ThirdCoordinateBlock C ξ i fun l =>
        -(∑ p, P.v' i p * C.delta p l)) := by
  let T : Fin C.r → G := fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hfirst : D5.ModGammaSix
      (formula21SecondCoordinateBlock C ξ i fun p =>
        -P.v' i p * orderInt C.e p)
      (orderedProduct fun p => formula21ThirdCoordinateBlock C ξ i fun l =>
        -P.v' i p * C.delta p l) := by
    unfold formula21SecondCoordinateBlock
    apply modEq_orderedProduct
    intro p
    exact formula21_x2_correction_coordinates C P ξ i p
  have hT : ∀ l, T l ∈ D5.gamma G 3 := by
    intro l
    exact formula21_third_base_mem_gamma3 C ξ i l
  have hswap := D5.orderedProduct_orderedProduct_swap_gammaThree
    (fun p l => T l ^ (-P.v' i p * C.delta p l))
    (fun p l => (D5.gamma G 3).zpow_mem (hT l) _)
  refine hfirst.trans <| (show D5.ModGammaSix
      (orderedProduct fun p => orderedProduct fun l =>
        T l ^ (-P.v' i p * C.delta p l))
      (formula21ThirdCoordinateBlock C ξ i fun l =>
        -(∑ p, P.v' i p * C.delta p l)) from
    hswap.trans ?_)
  unfold formula21ThirdCoordinateBlock
  apply modEq_orderedProduct
  intro l
  rw [D5.orderedProduct_zpow_same_base]
  have he : (∑ p, -P.v' i p * C.delta p l) =
      -(∑ p, P.v' i p * C.delta p l) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  change D5.ModGammaSix
    (T l ^ (∑ p, -P.v' i p * C.delta p l))
    (T l ^ (-(∑ p, P.v' i p * C.delta p l)))
  rw [he]

theorem formula21_second_condition6_split
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula21SecondCondition6Grouped C P ξ)
      (formula21WeightTwoPowerProduct C P ξ *
        formula21DeltaCorrectionGrouped C P ξ) := by
  let A : Fin C.s → G := fun i =>
    formula21SecondCoordinateBlock C ξ i fun p =>
      -P.v i p * orderInt C.d i
  let B : Fin C.s → G := fun i =>
    formula21SecondCoordinateBlock C ξ i fun p =>
      -P.v' i p * orderInt C.e p
  have hpoint : D5.ModGammaSix
      (formula21SecondCondition6Grouped C P ξ)
      (orderedProduct fun i => A i * B i) := by
    unfold formula21SecondCondition6Grouped
    apply modEq_orderedProduct
    intro i
    have hadd := (formula21SecondCoordinateBlock_add C ξ i
      (fun p => -P.v i p * orderInt C.d i)
      (fun p => -P.v' i p * orderInt C.e p)).symm
    simpa [A, B, sub_eq_add_neg, neg_mul] using hadd
  have hsplit := D5.orderedProduct_pointwise_mul_gammaThree A B
    (fun i => formula21SecondCoordinateBlock_mem_gamma3 C ξ i _)
    (fun i => formula21SecondCoordinateBlock_mem_gamma3 C ξ i _)
  have hweight :=
    (formula21_weight_two_power_product_coordinates C P ξ).symm
  have hdelta : D5.ModGammaSix
      (orderedProduct B) (formula21DeltaCorrectionGrouped C P ξ) := by
    unfold formula21DeltaCorrectionGrouped
    apply modEq_orderedProduct
    intro i
    simpa [B] using formula21_x2_corrections_collect C P ξ i
  exact hpoint.trans <| hsplit.trans <| by
    simpa [A] using hweight.mul hdelta

/-- The third-layer exponent displayed on the right of formula (21). -/
def formula21ThirdCoefficient
    (C : Context G) (P : Parameters C.s C.t)
    (i : Fin C.s) (l : Fin C.r) : ℤ :=
  (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l) -
    (∑ h ∈ Finset.univ.filter (· < i),
      P.u h i * orderRatio C.d h i * C.c h l) -
    (∑ p, P.v' i p * C.delta p l)

def formula21FinalThirdGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    formula21ThirdCoefficient C P i l

theorem formula21_delta_and_third_combine
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula21DeltaCorrectionGrouped C P ξ *
        formula21ThirdGrouped C P ξ)
      (formula21FinalThirdGrouped C P ξ) := by
  let A : Fin C.s → G := fun i =>
    formula21ThirdCoordinateBlock C ξ i fun l =>
      -(∑ p, P.v' i p * C.delta p l)
  let B : Fin C.s → G := fun i =>
    formula21ThirdCoordinateBlock C ξ i fun l =>
      (∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderRatio C.d h i) * C.c h l) +
      (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l)
  have hsplit := (D5.orderedProduct_pointwise_mul_gammaThree A B
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)).symm
  have hstart : D5.ModGammaSix
      (formula21DeltaCorrectionGrouped C P ξ *
        formula21ThirdGrouped C P ξ)
      (orderedProduct fun i => A i * B i) := by
    simpa [formula21DeltaCorrectionGrouped, formula21ThirdGrouped, A, B]
      using hsplit
  refine hstart.trans ?_
  unfold formula21FinalThirdGrouped
  apply modEq_orderedProduct
  intro i
  refine (formula21ThirdCoordinateBlock_add C ξ i _ _).trans ?_
  unfold formula21ThirdCoordinateBlock
  apply modEq_orderedProduct
  intro l
  have hlow :
      (∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderRatio C.d h i) * C.c h l) =
      -(∑ h ∈ Finset.univ.filter (· < i),
        P.u h i * orderRatio C.d h i * C.c h l) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  have he :
      -(∑ p, P.v' i p * C.delta p l) +
        ((∑ h ∈ Finset.univ.filter (· < i),
          (-P.u h i * orderRatio C.d h i) * C.c h l) +
         (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l)) =
      formula21ThirdCoefficient C P i l := by
    unfold formula21ThirdCoefficient
    rw [hlow]
    ring
  change D5.ModGammaSix
    (D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
      (-(∑ p, P.v' i p * C.delta p l) +
        ((∑ h ∈ Finset.univ.filter (· < i),
          (-P.u h i * orderRatio C.d h i) * C.c h l) +
         (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l))))
    (D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
      formula21ThirdCoefficient C P i l)
  rw [he]

theorem formula21_second_streams_combine
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula21LowSecondGrouped C P ξ *
        formula21HighSecondGrouped C P ξ)
      (formula21SecondGrouped C P ξ) := by
  unfold formula21LowSecondGrouped formula21HighSecondGrouped
    formula21SecondGrouped
  have houter := D5.orderedProduct_pointwise_mul_gammaThree
    (fun i => formula21SecondCoordinateBlock C ξ i fun p =>
      ∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderRatio C.d h i) * C.b h p)
    (fun i => formula21SecondCoordinateBlock C ξ i fun p =>
      ∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.b h p)
    (fun i => formula21SecondCoordinateBlock_mem_gamma3 C ξ i _)
    (fun i => formula21SecondCoordinateBlock_mem_gamma3 C ξ i _)
  refine houter.symm.trans ?_
  apply modEq_orderedProduct
  intro i
  exact formula21SecondCoordinateBlock_add C ξ i _ _

theorem formula21_third_streams_combine
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula21LowThirdGrouped C P ξ *
        formula21HighThirdGrouped C P ξ)
      (formula21ThirdGrouped C P ξ) := by
  unfold formula21LowThirdGrouped formula21HighThirdGrouped
    formula21ThirdGrouped
  have houter := D5.orderedProduct_pointwise_mul_gammaThree
    (fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
      ∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderRatio C.d h i) * C.c h l)
    (fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
      ∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l)
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)
  refine houter.symm.trans ?_
  apply modEq_orderedProduct
  intro i
  exact formula21ThirdCoordinateBlock_add C ξ i _ _

/-- The global pair product collected into one second-layer and one
third-layer block for each outer generator. -/
theorem structural_expansion21_grouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula21RawCoordinateProduct C P ξ)
      (formula21SecondGrouped C P ξ * formula21ThirdGrouped C P ξ) := by
  have hL3 : formula21LowThirdGrouped C P ξ ∈ D5.gamma G 3 := by
    apply orderedProduct_mem
    intro i
    exact formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _
  have hH2 : formula21HighSecondGrouped C P ξ ∈ D5.gamma G 3 := by
    apply orderedProduct_mem
    intro i
    exact formula21SecondCoordinateBlock_mem_gamma3 C ξ i _
  have hinterchange := D5.gammaThree_interchange
    (a := formula21LowSecondGrouped C P ξ)
    (b := formula21LowThirdGrouped C P ξ)
    (c := formula21HighSecondGrouped C P ξ)
    (d := formula21HighThirdGrouped C P ξ) hL3 hH2
  exact (structural_expansion21_grouped_streams C P ξ).trans <|
    hinterchange.trans <|
      (formula21_second_streams_combine C P ξ).mul
        (formula21_third_streams_combine C P ξ)

/-- Formula (21) through pairwise coordinate expansion. -/
theorem structural_expansion21_pairwise
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula21MainPairProduct C P ξ)
      (formula21RawCoordinateProduct C P ξ) := by
  unfold formula21MainPairProduct formula21RawCoordinateProduct
  apply modEq_orderedProduct
  intro i
  apply modEq_orderedProductWhere
  intro j hij
  exact structural_expansion21_pair C P ξ i j

/-- Formula (21), with all finite products and all three displayed
integer sums made explicit.  The only Tahara hypothesis used here is
condition (4.3.6); relation (2) is part of the accepted coordinate
description in `Context`. -/
theorem structural_expansion21
    (C : Context G) (P : Parameters C.s C.t) (h6 : P.Condition6)
    (ξ : G) :
    D5.ModGammaSix
      (formula21MainPairProduct C P ξ)
      (formula21WeightTwoPowerProduct C P ξ *
        formula21FinalThirdGrouped C P ξ) := by
  have hpairs := structural_expansion21_pairwise C P ξ
  have hgroup := structural_expansion21_grouped C P ξ
  have hcondition :=
    (formula21_second_grouped_condition6 C P h6 ξ).mul
      (D5.ModEq.refl (D5.gamma G 6) (formula21ThirdGrouped C P ξ))
  have hsplit := (formula21_second_condition6_split C P ξ).mul
    (D5.ModEq.refl (D5.gamma G 6) (formula21ThirdGrouped C P ξ))
  have hassoc : D5.ModGammaSix
      ((formula21WeightTwoPowerProduct C P ξ *
          formula21DeltaCorrectionGrouped C P ξ) *
        formula21ThirdGrouped C P ξ)
      (formula21WeightTwoPowerProduct C P ξ *
        (formula21DeltaCorrectionGrouped C P ξ *
          formula21ThirdGrouped C P ξ)) := by
    rw [mul_assoc]
  exact hpairs.trans <| hgroup.trans <| hcondition.trans <|
    hsplit.trans <| hassoc.trans <|
      (D5.ModEq.refl (D5.gamma G 6)
        (formula21WeightTwoPowerProduct C P ξ)).mul
        (formula21_delta_and_third_combine C P ξ)

end

end D5.Tahara
