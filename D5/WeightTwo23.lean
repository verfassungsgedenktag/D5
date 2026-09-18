import D5.Structural21

/-!
# The weight-two block in formula (23)

This file expands the first factor produced by formula (22).  Relation (1)
replaces `x₁ⱼ ^ d(j)` by its second-layer coordinates; the third-layer tail
has weight six after the final commutator and disappears.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

theorem paperComm_listProd_right_weight_three_two
    {a : G} (ha : a ∈ D5.gamma G 3)
    (ys : List G) (hys : ∀ y ∈ ys, y ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm a ys.prod)
      ((ys.map fun y => D5.paperComm a y).prod) := by
  induction ys with
  | nil =>
      simpa [D5.paperComm_eq] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)
  | cons y ys ih =>
      have hy : y ∈ D5.gamma G 2 := hys y (by simp)
      have htail : ys.prod ∈ D5.gamma G 2 :=
        listProd_mem (D5.gamma G 2) ys fun z hz => hys z (by simp [hz])
      simp only [List.prod_cons, List.map_cons]
      exact (D5.paperComm_mul_right_mod_gamma
        (n := 6) (r := 3) (s := 2) (t := 2)
        (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) ha hy htail).trans
          ((D5.ModEq.refl (D5.gamma G 6) (D5.paperComm a y)).mul
            (ih fun z hz => hys z (by simp [hz])))

theorem paperComm_orderedProduct_right_weight_three_two
    {a : G} (ha : a ∈ D5.gamma G 3)
    {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm a (orderedProduct f))
      (orderedProduct fun i => D5.paperComm a (f i)) := by
  unfold orderedProduct
  simpa [List.map_map] using
    paperComm_listProd_right_weight_three_two ha
      ((List.finRange n).map f) (fun y hy => by
        rcases List.mem_map.mp hy with ⟨i, hi, rfl⟩
        exact hf i)

/-- The first factor on the right of formula (22), before multiplication
over `j`. -/
def formula23LocalSource
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm ξ (formula22WeightTwoWord C P j))
    (C.x1 j ^ orderInt C.d j)

/-- Its fully expanded weight-five coordinate form. -/
def formula23LocalCoordinates
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j : Fin C.s) : G :=
  orderedProduct fun q => orderedProduct fun p =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
      (-P.v j p * C.b j q)

theorem formula23_local
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j : Fin C.s) :
    D5.ModGammaSix
      (formula23LocalSource C P ξ j)
      (formula23LocalCoordinates C P ξ j) := by
  let W := formula22WeightTwoWord C P j
  let Q := D5.paperComm ξ W
  let X2 := x1PowerSecondBlock C j
  let X3 := x1PowerThirdBlock C j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hW : W ∈ D5.gamma G 2 := by
    simpa [W] using formula22WeightTwoWord_mem_gamma2 C P j
  have hQ : Q ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hW
  have hX2 : X2 ∈ D5.gamma G 2 := by
    simpa [X2] using x1PowerSecondBlock_mem_gamma2 C j
  have hX3 : X3 ∈ D5.gamma G 3 := by
    simpa [X3] using x1PowerThirdBlock_mem_gamma3 C j
  have hreplace7 := D5.paperComm_right_of_modEq_gamma
    (r := 3) (s := 4) (by norm_num) (by norm_num)
    (C.x1_power j) hQ
  have hreplace : D5.ModGammaSix
      (D5.paperComm Q (C.x1 j ^ orderInt C.d j))
      (D5.paperComm Q (X2 * X3)) := by
    exact hreplace7.mono (D5.gamma_antitone G (by norm_num : 6 ≤ 7))
  have hsplit := D5.paperComm_mul_right_mod_gamma
    (n := 6) (r := 3) (s := 2) (t := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hQ hX2 hX3
  have htail : D5.ModGammaSix (D5.paperComm Q X3) 1 :=
    D5.paperComm_mod_gamma_eq_one
      (r := 3) (s := 3) (by norm_num) (by norm_num)
      (by norm_num) hQ hX3
  have hsecond : D5.ModGammaSix
      (D5.paperComm Q X2)
      (orderedProduct fun q => D5.paperComm Q (C.x2 q) ^ C.b j q) := by
    have hc := paperComm_orderedProduct_right_weight_three_two hQ
      (fun q => C.x2 q ^ C.b j q)
      (fun q => (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 q) _)
    refine (show D5.ModGammaSix
      (D5.paperComm Q X2)
      (orderedProduct fun q => D5.paperComm Q (C.x2 q ^ C.b j q)) by
        simpa [X2, x1PowerSecondBlock] using hc).trans ?_
    apply modEq_orderedProduct
    intro q
    exact D5.paperComm_zpow_right_mod_gamma
      (n := 6) (r := 3) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hQ (C.x2_mem_gamma2 q) _
  have hdrop : D5.ModGammaSix
      (D5.paperComm Q (X2 * X3))
      (orderedProduct fun q => D5.paperComm Q (C.x2 q) ^ C.b j q) := by
    exact hsplit.trans <| by
      simpa only [mul_one] using hsecond.mul htail
  refine (show D5.ModGammaSix (formula23LocalSource C P ξ j)
      (orderedProduct fun q => D5.paperComm Q (C.x2 q) ^ C.b j q) by
    simpa [formula23LocalSource, Q] using hreplace.trans hdrop).trans ?_
  unfold formula23LocalCoordinates
  have hxq : ∀ q, C.x2 q ∈ D5.gamma G 1 := fun q =>
    D5.gamma_antitone G (by norm_num) (C.x2_mem_gamma2 q)
  apply modEq_orderedProduct
  intro q
  have hinner := nested_weight_two_orderedProduct_right hξ (hxq q)
    (fun p => C.x2 p ^ (-P.v j p))
    (fun p => (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _)
  have hpow := hinner.zpow (C.b j q)
  have hbase : ∀ p,
      D5.paperComm
        (D5.paperComm ξ (C.x2 p ^ (-P.v j p))) (C.x2 q) ∈
        D5.gamma G 3 := by
    intro p
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ ((D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _)) (hxq q)
  have hdist := D5.orderedProduct_zpow_gammaThree
    (fun p => D5.paperComm
      (D5.paperComm ξ (C.x2 p ^ (-P.v j p))) (C.x2 q))
    hbase (C.b j q)
  refine (show D5.ModGammaSix
      (D5.paperComm Q (C.x2 q) ^ C.b j q)
      ((orderedProduct fun p =>
        D5.paperComm
          (D5.paperComm ξ (C.x2 p ^ (-P.v j p))) (C.x2 q)) ^
        C.b j q) by
      simpa [Q, W, formula22WeightTwoWord] using hpow).trans <|
    hdist.trans ?_
  apply modEq_orderedProduct
  intro p
  have hp := (nested_weight_two_zpow_right hξ
    (C.x2_mem_gamma2 p) (hxq q) (-P.v j p)).zpow (C.b j q)
  simpa [← zpow_mul] using hp

def formula23Source
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => formula23LocalSource C P ξ j

def formula23Uncollected
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => formula23LocalCoordinates C P ξ j

/-- The right hand side displayed in formula (23). -/
def formula23Collected
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun p => orderedProduct fun q =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
      (-(∑ j, P.v j p * C.b j q))

private theorem formula23_base_mem_gamma3
    (C : Context G) (ξ : G) (p q : Fin C.t) :
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ∈
      D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact D5.gamma_antitone G (by norm_num) <|
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        hξ (C.x2_mem_gamma2 p)) (C.x2_mem_gamma2 q)

theorem formula23_uncollected
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula23Source C P ξ)
      (formula23Uncollected C P ξ) := by
  unfold formula23Source formula23Uncollected
  apply modEq_orderedProduct
  intro j
  exact formula23_local C P ξ j

theorem formula23_collect
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula23Uncollected C P ξ)
      (formula23Collected C P ξ) := by
  let F : Fin C.s → Fin C.t → Fin C.t → G := fun j q p =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
      (-P.v j p * C.b j q)
  have hF : ∀ j q p, F j q p ∈ D5.gamma G 3 := by
    intro j q p
    exact (D5.gamma G 3).zpow_mem
      (formula23_base_mem_gamma3 C ξ p q) _
  have hswapJQ := D5.orderedProduct_orderedProduct_swap_gammaThree
    (fun j q => orderedProduct fun p => F j q p)
    (fun j q => orderedProduct_mem (D5.gamma G 3) _ fun p => hF j q p)
  have hswapJP : D5.ModGammaSix
      (orderedProduct fun q => orderedProduct fun j => orderedProduct fun p =>
        F j q p)
      (orderedProduct fun q => orderedProduct fun p => orderedProduct fun j =>
        F j q p) := by
    apply modEq_orderedProduct
    intro q
    exact D5.orderedProduct_orderedProduct_swap_gammaThree
      (fun j p => F j q p) (fun j p => hF j q p)
  have hcollect : D5.ModGammaSix
      (orderedProduct fun q => orderedProduct fun p => orderedProduct fun j =>
        F j q p)
      (orderedProduct fun q => orderedProduct fun p =>
        D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
          (-(∑ j, P.v j p * C.b j q))) := by
    apply modEq_orderedProduct
    intro q
    apply modEq_orderedProduct
    intro p
    unfold F
    rw [D5.orderedProduct_zpow_same_base]
    have he : (∑ j, -P.v j p * C.b j q) =
        -(∑ j, P.v j p * C.b j q) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [he]
  have hswapQP := D5.orderedProduct_orderedProduct_swap_gammaThree
    (fun q p =>
      D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
        (-(∑ j, P.v j p * C.b j q)))
    (fun q p => (D5.gamma G 3).zpow_mem
      (formula23_base_mem_gamma3 C ξ p q) _)
  unfold formula23Uncollected formula23LocalCoordinates formula23Collected
  exact (show D5.ModGammaSix
      (orderedProduct fun j => orderedProduct fun q => orderedProduct fun p =>
        F j q p)
      (orderedProduct fun p => orderedProduct fun q =>
        D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
          (-(∑ j, P.v j p * C.b j q))) from
    hswapJQ.trans <| hswapJP.trans <| hcollect.trans hswapQP)

/-- Formula (23). -/
theorem transfer_formula23
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula23Source C P ξ)
      (formula23Collected C P ξ) :=
  (formula23_uncollected C P ξ).trans (formula23_collect C P ξ)

end

end D5.Tahara
