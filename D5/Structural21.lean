import D5.TaharaExpand
import D5.CollectionWeighted
import D5.AbelianCollectionSix

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

end

end D5.Tahara
