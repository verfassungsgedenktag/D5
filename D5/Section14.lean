import D5.Section13

/-!
# Section 14: cancellation of the first two products

This file starts the formalization of formulas (47)--(54).  The first part
commutes the multiplicative form of condition (6), expands its three finite
blocks, and proves formula (49).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

set_option maxHeartbeats 800000

def formula47Word
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (condition6Word C P i)) (C.x1 i)) (C.x1 i)

/-- Formula (47): commuting the multiplicative consequence of condition
(6) with `ξ,x₁ᵢ,x₁ᵢ` gives an element of `γ₆`. -/
theorem formula47
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    D5.ModGammaSix (formula47Word C P ξ i) 1 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hW : condition6Word C P i ∈ D5.gamma G 3 :=
    condition6_multiplicative_of_satisfies C P hP i
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  apply D5.modEq_one_iff_mem.mpr
  exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
    (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hW) hi) hi

def formula48HighRow
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (i < ·) fun j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i)) (C.x1 i) ^
        P.u i j

def formula48LowRow
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) : G :=
  orderedProductWhere (· < j) fun i =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
        (-P.u i j * orderRatio C.d i j)

def formula48SecondLayerWord
    (C : Context G) (P : Parameters C.s C.t) (i : Fin C.s) : G :=
  orderedProduct fun p => C.x2 p ^ P.v i p

def formula48ThirdFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (formula48SecondLayerWord C P i)) (C.x1 i)) (C.x1 i) ^
      orderInt C.d i

def formula48Row
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  (formula48HighRow C P ξ i * formula48LowRow C P ξ i) *
    formula48ThirdFactor C P ξ i

theorem formula48SecondLayerWord_mem_gamma2
    (C : Context G) (P : Parameters C.s C.t) (i : Fin C.s) :
    formula48SecondLayerWord C P i ∈ D5.gamma G 2 := by
  unfold formula48SecondLayerWord
  apply orderedProduct_mem
  intro p
  exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _

private theorem formula48_high_base_mem_gamma2
    (C : Context G) (P : Parameters C.s C.t)
    {i j : Fin C.s} (_hij : i < j) :
    C.x1 j ^ (P.u i j * orderInt C.d j) ∈ D5.gamma G 2 := by
  have heq : P.u i j * orderInt C.d j = orderInt C.d j * P.u i j := by ring
  rw [heq, zpow_mul]
  exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 j) _

private theorem formula48_low_base_mem_gamma2
    (C : Context G) (P : Parameters C.s C.t)
    {h i : Fin C.s} (hhi : h < i) :
    C.x1 h ^ (-P.u h i * orderInt C.d i) ∈ D5.gamma G 2 := by
  rw [C.orderInt_eq_mul_ratio hhi.le]
  have heq : -P.u h i * (orderInt C.d h * orderRatio C.d h i) =
      orderInt C.d h * (-P.u h i * orderRatio C.d h i) := by ring
  rw [heq, zpow_mul]
  exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _

private theorem formula48_high_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (orderedProductWhere (i < ·) fun j =>
          C.x1 j ^ (P.u i j * orderInt C.d j))) (C.x1 i)) (C.x1 i))
      (formula48HighRow C P ξ i) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hraw := fourfold_second_orderedProductWhere_mod_gamma_six
    (i < ·) (fun j => C.x1 j ^ (P.u i j * orderInt C.d j))
    hξ (fun j hij => formula48_high_base_mem_gamma2 C P hij) hi hi
  refine hraw.trans ?_
  unfold formula48HighRow
  apply modEq_orderedProductWhere
  intro j hij
  have heq : C.x1 j ^ (P.u i j * orderInt C.d j) =
      (C.x1 j ^ orderInt C.d j) ^ P.u i j := by
    rw [show P.u i j * orderInt C.d j =
      orderInt C.d j * P.u i j by ring, zpow_mul]
  change D5.ModGammaSix
    (D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 j ^ (P.u i j * orderInt C.d j)))
        (C.x1 i)) (C.x1 i)) _
  rw [heq]
  exact fourfold_second_zpow_mod_gamma_six hξ
    (C.x1_order_power_mem_gamma2 j) hi hi (P.u i j)

private theorem formula48_low_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (orderedProductWhere (· < j) fun i =>
          C.x1 i ^ (-P.u i j * orderInt C.d j))) (C.x1 j)) (C.x1 j))
      (formula48LowRow C P ξ j) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hraw := fourfold_second_orderedProductWhere_mod_gamma_six
    (· < j) (fun i => C.x1 i ^ (-P.u i j * orderInt C.d j))
    hξ (fun i hij => formula48_low_base_mem_gamma2 C P hij) hj hj
  refine hraw.trans ?_
  unfold formula48LowRow
  apply modEq_orderedProductWhere
  intro i hij
  have hd := C.orderInt_eq_mul_ratio hij.le
  have heq : C.x1 i ^ (-P.u i j * orderInt C.d j) =
      (C.x1 i ^ orderInt C.d i) ^
        (-P.u i j * orderRatio C.d i j) := by
    rw [hd, show -P.u i j *
      (orderInt C.d i * orderRatio C.d i j) =
        orderInt C.d i * (-P.u i j * orderRatio C.d i j) by ring,
      zpow_mul]
  change D5.ModGammaSix
    (D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ (-P.u i j * orderInt C.d j)))
        (C.x1 j)) (C.x1 j)) _
  rw [heq]
  exact fourfold_second_zpow_mod_gamma_six hξ
    (C.x1_order_power_mem_gamma2 i) hj hj
      (-P.u i j * orderRatio C.d i j)

private theorem formula48_third_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ
          (formula48SecondLayerWord C P i ^ orderInt C.d i))
          (C.x1 i)) (C.x1 i))
      (formula48ThirdFactor C P ξ i) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  simpa [formula48ThirdFactor] using
    fourfold_second_zpow_mod_gamma_six hξ
      (formula48SecondLayerWord_mem_gamma2 C P i) hi hi (orderInt C.d i)

private theorem formula47_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModGammaSix (formula47Word C P ξ i) (formula48Row C P ξ i) := by
  let H := orderedProductWhere (i < ·) fun h =>
    C.x1 h ^ (P.u i h * orderInt C.d h)
  let L := orderedProductWhere (· < i) fun h =>
    C.x1 h ^ (-P.u h i * orderInt C.d i)
  let V := formula48SecondLayerWord C P i
  let X := C.x1 i
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hH : H ∈ D5.gamma G 2 := by
    dsimp [H]
    apply orderedProductWhere_mem
    intro h hih
    exact formula48_high_base_mem_gamma2 C P hih
  have hL : L ∈ D5.gamma G 2 := by
    dsimp [L]
    apply orderedProductWhere_mem
    intro h hhi
    exact formula48_low_base_mem_gamma2 C P hhi
  have hV : V ∈ D5.gamma G 2 := formula48SecondLayerWord_mem_gamma2 C P i
  have hVd : V ^ orderInt C.d i ∈ D5.gamma G 2 :=
    (D5.gamma G 2).zpow_mem hV _
  have hsplit1 := fourfold_second_mul_mod_gamma_six hξ hH
    ((D5.gamma G 2).mul_mem hL hVd) hX hX
  have hsplit2 := fourfold_second_mul_mod_gamma_six hξ hL hVd hX hX
  have hsplit : D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (H * (L * V ^ orderInt C.d i))) X) X)
      ((D5.paperComm (D5.paperComm (D5.paperComm ξ H) X) X *
        D5.paperComm (D5.paperComm (D5.paperComm ξ L) X) X) *
        D5.paperComm (D5.paperComm
          (D5.paperComm ξ (V ^ orderInt C.d i)) X) X) := by
    simpa [mul_assoc] using hsplit1.trans
      ((D5.ModEq.refl (D5.gamma G 6)
        (D5.paperComm (D5.paperComm (D5.paperComm ξ H) X) X)).mul hsplit2)
  have hexpand := ((formula48_high_expand C P ξ i).mul
    (formula48_low_expand C P ξ i)).mul
      (formula48_third_expand C P ξ i)
  simpa [formula47Word, condition6Word, formula48Row,
    formula48SecondLayerWord, H, L, V, X, mul_assoc] using
      hsplit.trans hexpand

theorem formula48_row_vanish
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    D5.ModGammaSix (formula48Row C P ξ i) 1 :=
  (formula47_expand C P ξ i).symm.trans (formula47 C P hP ξ i)

def formula48FirstProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i)) (C.x1 i) ^
        P.u i j

def formula48SecondProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
        (-P.u i j * orderRatio C.d i j)

def formula48ThirdProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct (formula48ThirdFactor C P ξ)

private theorem formula48_row_components_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    formula48HighRow C P ξ i ∈ D5.gamma G 3 ∧
    formula48LowRow C P ξ i ∈ D5.gamma G 3 ∧
    formula48ThirdFactor C P ξ i ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  constructor
  · unfold formula48HighRow
    apply orderedProductWhere_mem
    intro j hij
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ
            (C.x1_order_power_mem_gamma2 j)) hi) hi) _
  constructor
  · unfold formula48LowRow
    apply orderedProductWhere_mem
    intro h hhi
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ
            (C.x1_order_power_mem_gamma2 h)) hi) hi) _
  · unfold formula48ThirdFactor
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ
            (formula48SecondLayerWord_mem_gamma2 C P i)) hi) hi) _

/-- Formula (48), with all three displayed products and their finite index
domains. -/
theorem formula48
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix 1
      ((formula48FirstProduct C P ξ * formula48SecondProduct C P ξ) *
        formula48ThirdProduct C P ξ) := by
  have hrows : D5.ModGammaSix
      (orderedProduct (formula48Row C P ξ)) 1 := by
    have h : D5.ModGammaSix
        (orderedProduct (formula48Row C P ξ))
        (orderedProduct fun _i : Fin C.s => (1 : G)) := by
      apply modEq_orderedProduct
      intro i
      exact formula48_row_vanish C P hP ξ i
    simpa [orderedProduct] using h
  let H := formula48HighRow C P ξ
  let L := formula48LowRow C P ξ
  let T := formula48ThirdFactor C P ξ
  have hm : ∀ i, H i ∈ D5.gamma G 3 ∧ L i ∈ D5.gamma G 3 ∧
      T i ∈ D5.gamma G 3 := formula48_row_components_mem_gamma3 C P ξ
  have hHL := D5.orderedProduct_pointwise_mul_gammaThree H L
    (fun i => (hm i).1) (fun i => (hm i).2.1)
  have hHLT := D5.orderedProduct_pointwise_mul_gammaThree
    (fun i => H i * L i) T
    (fun i => (D5.gamma G 3).mul_mem (hm i).1 (hm i).2.1)
    (fun i => (hm i).2.2)
  have hcollect : D5.ModGammaSix
      (orderedProduct (formula48Row C P ξ))
      ((orderedProduct H * orderedProduct L) * orderedProduct T) := by
    simpa [formula48Row, H, L, T] using hHLT.trans <|
      hHL.mul (D5.ModEq.refl (D5.gamma G 6) (orderedProduct T))
  have hlow := strictPairProduct_swap
    (fun i j => D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
        (-P.u i j * orderRatio C.d i j))
    (fun i j hij => by
      have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
      have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
      exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
            (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ
              (C.x1_order_power_mem_gamma2 i)) hj) hj) _)
  have hlow' : D5.ModGammaSix (orderedProduct L)
      (formula48SecondProduct C P ξ) := by
    change D5.ModGammaSix
      (orderedProduct fun j => orderedProductWhere (· < j) fun i =>
        D5.paperComm (D5.paperComm
          (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
            (-P.u i j * orderRatio C.d i j))
      (strictPairProduct fun i j =>
        D5.paperComm (D5.paperComm
          (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
            (-P.u i j * orderRatio C.d i j))
    exact hlow.symm
  have hid : D5.ModGammaSix
      ((orderedProduct H * orderedProduct L) * orderedProduct T)
      ((formula48FirstProduct C P ξ * formula48SecondProduct C P ξ) *
        formula48ThirdProduct C P ξ) := by
    have hhigh : orderedProduct H = formula48FirstProduct C P ξ := rfl
    have hthirdEq : orderedProduct T = formula48ThirdProduct C P ξ := rfl
    rw [hhigh, hthirdEq]
    exact ((D5.ModEq.refl (D5.gamma G 6) (formula48FirstProduct C P ξ)).mul
      hlow').mul (D5.ModEq.refl (D5.gamma G 6) (formula48ThirdProduct C P ξ))
  exact hrows.symm.trans (hcollect.trans hid)

theorem formula48_third_product_vanish
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula48ThirdProduct C P ξ) 1 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h : D5.ModGammaSix (formula48ThirdProduct C P ξ)
      (orderedProduct fun _i : Fin C.s => (1 : G)) := by
    unfold formula48ThirdProduct
    apply modEq_orderedProduct
    intro i
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact fourfold_last_entry_power_vanish hξ
      (formula48SecondLayerWord_mem_gamma2 C P i) hi hi
        (C.x1_order_power_mem_gamma2 i)
  simpa [orderedProduct] using h

/-- Inversion of a strict pair product in the abelian layer `γ₃/γ₆`. -/
theorem strictPairProduct_pointwise_inv_gammaThree
    {n : ℕ} (f : Fin n → Fin n → G)
    (hf : ∀ i j, i < j → f i j ∈ D5.gamma G 3) :
    D5.ModGammaSix (strictPairProduct f)⁻¹
      (strictPairProduct fun i j => (f i j)⁻¹) := by
  let R : Fin n → G := fun i => orderedProductWhere (i < ·) (f i)
  have hR : ∀ i, R i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hf i j hij
  have hrow : ∀ i, D5.ModGammaSix (R i)⁻¹
      (orderedProductWhere (i < ·) fun j => (f i j)⁻¹) := by
    intro i
    simpa [R, zpow_neg] using orderedProductWhere_zpow_gammaThree
      (i < ·) (f i) (hf i) (-1)
  have hout := D5.orderedProduct_zpow_gammaThree R hR (-1)
  have hreplace : D5.ModGammaSix
      (orderedProduct fun i => R i ^ (-1 : ℤ))
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        (f i j)⁻¹) := by
    apply modEq_orderedProduct
    intro i
    simpa [zpow_neg] using hrow i
  simpa [strictPairProduct, R, zpow_neg] using hout.trans hreplace

/-- Formula (49): the first product of (46) is replaced by the first
product of (48). -/
theorem formula49
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (formula46FirstProduct C P ξ)
      (formula48FirstProduct C P ξ) := by
  have h48 := formula48 C P hP ξ
  have hthird := formula48_third_product_vanish C P ξ
  have hshort : D5.ModGammaSix 1
      (formula48FirstProduct C P ξ * formula48SecondProduct C P ξ) := by
    have hr := h48.trans <|
      ((D5.ModEq.refl (D5.gamma G 6)
        (formula48FirstProduct C P ξ * formula48SecondProduct C P ξ)).mul
          hthird)
    simpa using hr
  let F : Fin C.s → Fin C.s → G := fun i j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
        (P.u i j * orderRatio C.d i j)
  have hF : ∀ i j, i < j → F i j ∈ D5.gamma G 3 := by
    intro i j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ
            (C.x1_order_power_mem_gamma2 i)) hj) hj) _
  have hinv := strictPairProduct_pointwise_inv_gammaThree F hF
  have hneg : D5.ModGammaSix (formula48SecondProduct C P ξ)
      (formula46FirstProduct C P ξ)⁻¹ := by
    have hlocal : D5.ModGammaSix
        (strictPairProduct fun i j =>
          D5.paperComm (D5.paperComm
            (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
              (-P.u i j * orderRatio C.d i j))
        (strictPairProduct fun i j => (F i j)⁻¹) := by
      apply modEq_orderedProduct
      intro i
      apply modEq_orderedProductWhere
      intro j hij
      simpa [F, zpow_neg] using
        D5.ModEq.refl (D5.gamma G 6) ((F i j)⁻¹)
    simpa [formula48SecondProduct, formula46FirstProduct, F] using
      hlocal.trans hinv.symm
  have hmul := hshort.mul
    (D5.ModEq.refl (D5.gamma G 6) (formula46FirstProduct C P ξ))
  have hreplace := ((D5.ModEq.refl (D5.gamma G 6)
    (formula48FirstProduct C P ξ)).mul hneg).mul
      (D5.ModEq.refl (D5.gamma G 6) (formula46FirstProduct C P ξ))
  have hfinal := hmul.trans hreplace
  simpa [mul_assoc] using hfinal

/-! ## The correction calculation in formula (52) -/

/-- A weight-four commutator followed by an entry whose `d`th power has
weight two is killed by the `d`th power modulo `γ₆`. -/
theorem weightFour_last_entry_power_vanish
    {r z : G} {d : ℤ} (hr : r ∈ D5.gamma G 4)
    (hz : z ∈ D5.gamma G 1) (hzd : z ^ d ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm r z ^ d) 1 := by
  have htransfer := D5.paperComm_zpow_right_mod_gamma
    (n := 6) (r := 4) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr hz d
  have hzero : D5.ModGammaSix (D5.paperComm r (z ^ d)) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hr hzd
  exact htransfer.symm.trans hzero

def formula52Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i)) (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^
      P.u i j *
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 i) ^
      (-P.u i j * orderRatio C.d i j)

def formula52FirstCorrection
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i)) (C.x1 j)) (C.x1 j)) (C.x1 i) ^
      (P.u i j * TaharaArithmetic.binom2 (C.d j))

def formula52SecondCorrection
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i)) (C.x1 i)) (C.x1 j)) (C.x1 i) ^
      (-P.u i j * orderRatio C.d i j *
        TaharaArithmetic.binom2 (C.d i))

/-- The first congruence in (52): after transferring both powers, the
common weight-four terms cancel and only the two binomial corrections
remain. -/
theorem formula52_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula52Left C P ξ i j)
      (formula52FirstCorrection C P ξ i j *
        formula52SecondCorrection C P ξ i j) := by
  let X := C.x1 i
  let Y := C.x1 j
  let d := orderInt C.d i
  let e := orderInt C.d j
  let q := orderRatio C.d i j
  let u := P.u i j
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ X) Y) X
  let I := D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ X) Y) Y) X
  let J := D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ X) X) Y) X
  let b2d := TaharaArithmetic.binom2 (C.d i)
  let b2e := TaharaArithmetic.binom2 (C.d j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hA : A ∈ D5.gamma G 4 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hX) hY) hX
  have hI : I ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hX) hY) hY) hX
  have hJ : J ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hX) hX) hY) hX
  have ht1 := fourfold_zpow_third_entry hξ hX hY hX (C.d j)
  have ht2 := fourfold_zpow_second_entry hξ hX hY hX (C.d i)
  have hp1 := (ht1.zpow u).trans <| D5.gammaThree_mul_zpow
    ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA) e)
    ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hI) b2e) u
  have hp2 := (ht2.zpow (-u * q)).trans <| D5.gammaThree_mul_zpow
    ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA) d)
    ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hJ) b2d)
      (-u * q)
  let AE := (A ^ e) ^ u
  let IE := (I ^ b2e) ^ u
  let AD := (A ^ d) ^ (-u * q)
  let JD := (J ^ b2d) ^ (-u * q)
  have hAE : AE ∈ D5.gamma G 3 :=
    (D5.gamma G 3).zpow_mem
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA) e) u
  have hIE : IE ∈ D5.gamma G 3 :=
    (D5.gamma G 3).zpow_mem
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hI) b2e) u
  have hAD : AD ∈ D5.gamma G 3 :=
    (D5.gamma G 3).zpow_mem
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA) d) (-u * q)
  have hJD : JD ∈ D5.gamma G 3 :=
    (D5.gamma G 3).zpow_mem
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hJ) b2d) (-u * q)
  have hsource : D5.ModGammaSix (formula52Left C P ξ i j)
      ((AE * IE) * (AD * JD)) := by
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ X) (Y ^ e)) X ^ u *
        D5.paperComm (D5.paperComm (D5.paperComm ξ (X ^ d)) Y) X ^
          (-u * q))
      ((AE * IE) * (AD * JD))
    exact hp1.mul hp2
  have hswap := D5.gammaThree_interchange (a := AE) (b := IE)
    (c := AD) (d := JD) hIE hAD
  have he : e = d * q := C.orderInt_eq_mul_ratio hij.le
  have hlead : AE * AD = 1 := by
    dsimp [AE, AD]
    rw [← zpow_mul, ← zpow_mul, ← zpow_add]
    have hz : e * u + d * (-u * q) = 0 := by rw [he]; ring
    rw [hz, zpow_zero]
  have hcorr : IE * JD =
      formula52FirstCorrection C P ξ i j *
        formula52SecondCorrection C P ξ i j := by
    dsimp [IE, JD]
    rw [← zpow_mul, ← zpow_mul]
    simp only [formula52FirstCorrection, formula52SecondCorrection,
      I, J, X, Y, u, q, b2d, b2e]
    congr 2 <;> ring
  have hfinish : D5.ModGammaSix ((AE * AD) * (IE * JD))
      (formula52FirstCorrection C P ξ i j *
        formula52SecondCorrection C P ξ i j) := by
    rw [hlead, one_mul, hcorr]
  exact hsource.trans (hswap.trans hfinish)

/-- The second congruence in (52): both binomial corrections vanish by
the two divisibilities collected in formula (17). -/
theorem formula52_corrections_vanish
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix
      (formula52FirstCorrection C P ξ i j *
        formula52SecondCorrection C P ξ i j) 1 := by
  let X := C.x1 i
  let Y := C.x1 j
  let d := orderInt C.d i
  let I0 := D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ X) Y) Y) X
  let J0 := D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ X) X) Y) X
  let RI := D5.paperComm (D5.paperComm (D5.paperComm ξ X) Y) Y
  let RJ := D5.paperComm (D5.paperComm (D5.paperComm ξ X) X) Y
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hRI : RI ∈ D5.gamma G 4 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hX) hY) hY
  have hRJ : RJ ∈ D5.gamma G 4 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hX) hX) hY
  have hIord : D5.ModGammaSix (I0 ^ d) 1 := by
    simpa [I0, RI] using weightFour_last_entry_power_vanish hRI hX
      (C.x1_order_power_mem_gamma2 i)
  have hJord : D5.ModGammaSix (J0 ^ d) 1 := by
    simpa [J0, RJ] using weightFour_last_entry_power_vanish hRJ hX
      (C.x1_order_power_mem_gamma2 i)
  have hpairs := pairConsequences C P hP hij
  have hdivI : d ∣ P.u i j * TaharaArithmetic.binom2 (C.d j) :=
    hpairs.dvd17_right
  have hdivJ : d ∣ -P.u i j * orderRatio C.d i j *
      TaharaArithmetic.binom2 (C.d i) := by
    have hneg := dvd_neg.mpr hpairs.dvd17_left
    simpa only [neg_mul] using hneg
  have hIv := D5.modGammaSix_zpow_eq_one_of_dvd hIord hdivI
  have hJv := D5.modGammaSix_zpow_eq_one_of_dvd hJord hdivJ
  simpa [formula52FirstCorrection, formula52SecondCorrection,
    I0, J0, X, Y] using hIv.mul hJv

/-- Formula (52) in its final form. -/
theorem formula52
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula52Left C P ξ i j) 1 :=
  (formula52_expand C P ξ hij).trans
    (formula52_corrections_vanish C P hP ξ hij)

/-! ## Formula (53) and the global cancellation -/

def formula53Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 j)) (C.x1 i))
      (C.x1 i ^ orderInt C.d i) ^
        (P.u i j * orderRatio C.d i j)

def formula53Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i))
      (C.x1 i) ^ P.u i j

/-- Formula (53).  Both sides are transferred directly to the same
weight-four basic commutator; the two weight-five corrections vanish by
the divisibilities in (17). -/
theorem formula53
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula53Left C P ξ i j)
      (formula53Right C P ξ i j) := by
  let X := C.x1 i
  let Y := C.x1 j
  let d := orderInt C.d i
  let e := orderInt C.d j
  let q := orderRatio C.d i j
  let u := P.u i j
  let S := D5.paperComm (D5.paperComm ξ Y) X
  let A := D5.paperComm S X
  let I := D5.paperComm A X
  let J := D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) X) X
  let RJ := D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) X
  let b2d := TaharaArithmetic.binom2 (C.d i)
  let b2e := TaharaArithmetic.binom2 (C.d j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hS : S ∈ D5.gamma G 3 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY) hX
  have hA : A ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hS hX
  have hI : I ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hX
  have hRJ : RJ ∈ D5.gamma G 4 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY) hY) hX
  have hJ : J ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hRJ hX
  have hIord : D5.ModGammaSix (I ^ d) 1 := by
    simpa [I, A] using weightFour_last_entry_power_vanish hA hX
      (C.x1_order_power_mem_gamma2 i)
  have hJord : D5.ModGammaSix (J ^ d) 1 := by
    simpa [J, RJ] using weightFour_last_entry_power_vanish hRJ hX
      (C.x1_order_power_mem_gamma2 i)
  have hpairs := pairConsequences C P hP hij
  have hdivI : d ∣ b2d * (u * q) := by
    simpa [d, b2d, u, q, mul_assoc, mul_left_comm, mul_comm] using
      hpairs.dvd17_left
  have hdivJ : d ∣ b2e * u := by
    simpa [d, b2e, u, mul_comm] using hpairs.dvd17_right
  have hIv := D5.modGammaSix_zpow_eq_one_of_dvd hIord hdivI
  have hJv := D5.modGammaSix_zpow_eq_one_of_dvd hJord hdivJ
  have hleft0 := weightThree_comm_zpow_right_hallPetresco hS hX (C.d i)
  have hleft1 := (hleft0.zpow (u * q)).trans <|
    D5.gammaThree_mul_zpow
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA) d)
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hI) b2d)
      (u * q)
  have hleft2 : D5.ModGammaSix (formula53Left C P ξ i j)
      (A ^ (d * (u * q))) := by
    have hIv' : D5.ModGammaSix ((I ^ b2d) ^ (u * q)) 1 := by
      simpa [zpow_mul] using hIv
    have hkill := (D5.ModEq.refl (D5.gamma G 6) ((A ^ d) ^ (u * q))).mul hIv'
    have hc := hleft1.trans hkill
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) X) (X ^ d) ^
        (u * q)) (A ^ (d * (u * q)))
    have hpowe : (A ^ d) ^ (u * q) = A ^ (d * (u * q)) := by
      rw [← zpow_mul]
    rw [← hpowe]
    simpa only [mul_one] using hc
  have hright0 := fourfold_zpow_second_entry hξ hY hX hX (C.d j)
  have hright1 := (hright0.zpow u).trans <|
    D5.gammaThree_mul_zpow
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA) e)
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hJ) b2e) u
  have hright2 : D5.ModGammaSix (formula53Right C P ξ i j)
      (A ^ (e * u)) := by
    have hJv' : D5.ModGammaSix ((J ^ b2e) ^ u) 1 := by
      simpa [zpow_mul] using hJv
    have hkill := (D5.ModEq.refl (D5.gamma G 6) ((A ^ e) ^ u)).mul hJv'
    have hc := hright1.trans hkill
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ (Y ^ e)) X) X ^ u)
      (A ^ (e * u))
    have hpowe : (A ^ e) ^ u = A ^ (e * u) := by rw [← zpow_mul]
    rw [← hpowe]
    simpa only [mul_one] using hc
  have he : e = d * q := C.orderInt_eq_mul_ratio hij.le
  have hexp : d * (u * q) = e * u := by rw [he]; ring
  rw [hexp] at hleft2
  exact hleft2.trans hright2.symm

def formula51First
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 i) ^
      (P.u i j * orderRatio C.d i j)

def formula51Third
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i)) (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^
      (-P.u i j)

def formula51Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  (formula51First C P ξ i j * formula53Right C P ξ i j) *
    formula51Third C P ξ i j

/-- Formula (51).  Its three-factor right side is checked against (52),
while the remaining middle factor is identified by the direct transfer
calculation (53). -/
theorem formula51
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula53Left C P ξ i j)
      (formula51Right C P ξ i j) := by
  let A := formula51First C P ξ i j
  let B := formula53Right C P ξ i j
  let C' := formula51Third C P ξ i j
  have hA : A ∈ D5.gamma G 3 := by
    dsimp [A, formula51First]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ
            (C.x1_order_power_mem_gamma2 i)) hj) hi) _
  have hB : B ∈ D5.gamma G 3 := by
    dsimp [B, formula53Right]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ
            (C.x1_order_power_mem_gamma2 j)) hi) hi) _
  have hC : C' ∈ D5.gamma G 3 := by
    dsimp [C', formula51Third]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hi)
            (C.x1_order_power_mem_gamma2 j)) hi) _
  have h52 := formula52 C P hP ξ hij
  have hcancel : D5.ModGammaSix (A * C') 1 := by
    have hi := h52.inv
    simpa [formula52Left, formula51First, formula51Third, A, C',
      inv_zpow, zpow_neg] using hi
  have hperm : D5.ModGammaSix ((A * B) * C') ((A * C') * B) := by
    simpa only [mul_one] using
      D5.gammaThree_interchange (a := A) (b := B) (c := C') (d := (1 : G)) hB hC
  have hright : D5.ModGammaSix (formula51Right C P ξ i j) B := by
    simpa [formula51Right, A, B, C'] using hperm.trans <|
      hcancel.mul (D5.ModEq.refl (D5.gamma G 6) B)
  exact (formula53 C P hP ξ hij).trans hright.symm

def formula53LeftProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula53Left C P ξ)

/-- Formula (53) multiplied over all pairs. -/
theorem formula53_product
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (formula53LeftProduct C P ξ)
      (formula48FirstProduct C P ξ) := by
  unfold formula53LeftProduct formula48FirstProduct strictPairProduct
  apply modEq_orderedProduct
  intro i
  apply modEq_orderedProductWhere
  intro j hij
  exact formula53 C P hP ξ hij

/-- The first two global products in (46) cancel. -/
theorem formula46_first_two_vanish
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix
      (formula46FirstProduct C P ξ * formula46SecondProduct C P ξ) 1 := by
  have h49 := formula49 C P hP ξ
  have h53 := formula53_product C P hP ξ
  let Q : Fin C.s → Fin C.s → G := formula53Left C P ξ
  have hQ : ∀ i j, i < j → Q i j ∈ D5.gamma G 3 := by
    intro i j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <| (D5.gamma G 5).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hj) hi)
        (C.x1_order_power_mem_gamma2 i)) _
  have hinv := strictPairProduct_pointwise_inv_gammaThree Q hQ
  have hsecond : D5.ModGammaSix (formula46SecondProduct C P ξ)
      (formula53LeftProduct C P ξ)⁻¹ := by
    have hlocal : D5.ModGammaSix (formula46SecondProduct C P ξ)
        (strictPairProduct fun i j => (Q i j)⁻¹) := by
      unfold formula46SecondProduct strictPairProduct
      apply modEq_orderedProduct
      intro i
      apply modEq_orderedProductWhere
      intro j hij
      simpa [Q, formula53Left, zpow_neg] using
        D5.ModEq.refl (D5.gamma G 6) ((Q i j)⁻¹)
    exact hlocal.trans hinv.symm
  have hreplace := h49.mul hsecond
  have hsame := h53.symm.mul
    (D5.ModEq.refl (D5.gamma G 6) (formula53LeftProduct C P ξ)⁻¹)
  exact hreplace.trans <| hsame.trans <| by
    simpa using D5.ModEq.refl (D5.gamma G 6) (1 : G)

/-- Formula (54): after Section 14 only the third product of (46) remains. -/
theorem formula54
    [Finite G] (C : Context G) (P : Parameters C.s C.t)
    (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (D5.paperComm (word C P) ξ)
      (formula46ThirdProduct C P ξ) := by
  have h46 := section13_finite (G := G) C P hP ξ
  have hv := formula46_first_two_vanish C P hP ξ
  exact h46.trans <| by
    simpa using hv.mul
      (D5.ModEq.refl (D5.gamma G 6) (formula46ThirdProduct C P ξ))

end

end D5.Tahara
