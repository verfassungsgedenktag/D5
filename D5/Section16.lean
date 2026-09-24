import D5.Section15

/-!
# Section 16: the first expansion of `κ`

This file verifies formulas (57)--(60).  In particular, the binomial
correction in (59) is retained explicitly before condition (17) kills it.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Formula (57), the first-entry Hall--Petresco expansion modulo `γ₄`. -/
theorem formula57
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
      (D5.paperComm (C.x1 i) ξ ^ orderInt C.d i *
        D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i) ^
          TaharaArithmetic.binom2 (C.d i)) := by
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  simpa [orderInt] using
    paperComm_zpow_left_hallPetresco_mod_gamma_four hi hξ (C.d i)

/-- Formula (58): the `d(i)`th power of the weight-three correction in
(57) lies in `γ₄`. -/
theorem formula58
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i) ^
      orderInt C.d i ∈ D5.gamma G 4 := by
  let X := C.x1 i
  let A := D5.paperComm X ξ
  let d := orderInt C.d i
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : A ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hX hξ
  have htransfer := D5.paperComm_zpow_right_mod_gamma
    (n := 4) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hA hX d
  have hzero : D5.ModEq (D5.gamma G 4)
      (D5.paperComm A (X ^ d)) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA
        (C.x1_order_power_mem_gamma2 i)
  have h := D5.modEq_one_iff_mem.mp (htransfer.symm.trans hzero)
  simpa [A, X, d] using h

def formula59FirstFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (C.x1 i) ξ)
    (D5.paperComm (C.x1 j) ξ) ^
      (P.u i j * orderInt C.d j)

def formula59SecondFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i))
    (D5.paperComm (C.x1 j) ξ) ^
      (P.u i j * orderRatio C.d i j *
        TaharaArithmetic.binom2 (C.d i))

def formula59FirstProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula59FirstFactor C P ξ)

def formula59SecondProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula59SecondFactor C P ξ)

/-- The local expansion used in (59). -/
theorem formula59_pair
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
        (D5.paperComm (C.x1 j) ξ) ^
          (P.u i j * orderRatio C.d i j))
      (formula59FirstFactor C P ξ i j *
        formula59SecondFactor C P ξ i j) := by
  let X := C.x1 i
  let Y := C.x1 j
  let A := D5.paperComm X ξ
  let B := D5.paperComm Y ξ
  let I := D5.paperComm A X
  let d := orderInt C.d i
  let e := orderInt C.d j
  let q := orderRatio C.d i j
  let u := P.u i j
  let b2d := TaharaArithmetic.binom2 (C.d i)
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : A ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hX hξ
  have hB : B ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hY hξ
  have hI : I ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hX
  have h57 := formula57 C ξ i
  have hreplace := formula56_replace_left h57 hB
  have hsplit := formula56_mul_left
    ((D5.gamma G 2).zpow_mem hA d)
    ((D5.gamma G 2).zpow_mem (D5.gamma_antitone G (by norm_num) hI) b2d) hB
  have hfirst := D5.paperComm_zpow_left_mod_gamma_six
    hA hB d
  have hsecond := D5.paperComm_zpow_left_mod_gamma_six
    (D5.gamma_antitone G (by norm_num) hI) hB b2d
  have hbase : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (X ^ d) ξ) B)
      (D5.paperComm A B ^ d * D5.paperComm I B ^ b2d) := by
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm (X ^ d) ξ) B)
      (D5.paperComm A B ^ d * D5.paperComm I B ^ b2d)
    exact hreplace.trans <| hsplit.trans (hfirst.mul hsecond)
  have hAB : D5.paperComm A B ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hB
  have hIB : D5.paperComm I B ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hI hB
  have hpow := (hbase.zpow (u * q)).trans <|
    D5.gammaThree_mul_zpow
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hAB) d)
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hIB) b2d)
      (u * q)
  have he : e = d * q := C.orderInt_eq_mul_ratio hij.le
  have hexp1 : d * (u * q) = u * e := by rw [he]; ring
  have hexp2 : b2d * (u * q) = u * q * b2d := by ring
  change D5.ModGammaSix
    (D5.paperComm (D5.paperComm (X ^ d) ξ) B ^ (u * q))
    (D5.paperComm A B ^ (u * e) * D5.paperComm I B ^ (u * q * b2d))
  exact hpow.trans <| by
    rw [← zpow_mul, ← zpow_mul, hexp1, hexp2]

/-- Formula (59), collected over every strict pair. -/
theorem formula59
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (kappa C P ξ)
      (formula59FirstProduct C P ξ * formula59SecondProduct C P ξ) := by
  let F := formula59FirstFactor C P ξ
  let S := formula59SecondFactor C P ξ
  have hlocal : D5.ModGammaSix (kappa C P ξ)
      (strictPairProduct fun i j => F i j * S i j) := by
    unfold kappa strictPairProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    exact formula59_pair C P ξ hij
  have hF : ∀ i j, i < j → F i j ∈ D5.gamma G 3 := by
    intro i j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hi hξ)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ)) _
  have hS : ∀ i j, i < j → S i j ∈ D5.gamma G 3 := by
    intro i j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hA := D5.paperComm_mem_gamma_add
      (r := 1) (s := 1) (by norm_num) (by norm_num) hi hξ
    have hI := D5.paperComm_mem_gamma_add
      (r := 2) (s := 1) (by norm_num) (by norm_num) hA hi
    have hB := D5.paperComm_mem_gamma_add
      (r := 1) (s := 1) (by norm_num) (by norm_num) hj hξ
    exact (D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hI hB) _
  exact hlocal.trans <| by
    simpa [formula59FirstProduct, formula59SecondProduct, F, S] using
      (strictPairProduct_pointwise_gammaThree F S hF hS).symm

/-- Every local factor in the second product of (59) vanishes. -/
theorem formula59_second_factor_vanish
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula59SecondFactor C P ξ i j) 1 := by
  let X := C.x1 i
  let Y := C.x1 j
  let I := D5.paperComm (D5.paperComm X ξ) X
  let B := D5.paperComm Y ξ
  let K := D5.paperComm I B
  let d := orderInt C.d i
  let q := orderRatio C.d i j
  let u := P.u i j
  let b2d := TaharaArithmetic.binom2 (C.d i)
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : D5.paperComm X ξ ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hX hξ
  have hI : I ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hX
  have hB : B ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hY hξ
  have hIpow : I ^ d ∈ D5.gamma G 4 := by
    simpa [I, X, d] using formula58 C ξ i
  have htransfer := D5.paperComm_zpow_left_mod_gamma_six
    (D5.gamma_antitone G (by norm_num) hI) hB d
  have hzero : D5.ModGammaSix (D5.paperComm (I ^ d) B) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hIpow hB
  have hKord : D5.ModGammaSix (K ^ d) 1 := by
    simpa [K] using htransfer.symm.trans hzero
  have hpairs := pairConsequences C P hP hij
  have hdiv : d ∣ u * q * b2d := by
    simpa [d, u, q, b2d] using hpairs.dvd17_left
  have hv := D5.modGammaSix_zpow_eq_one_of_dvd hKord hdiv
  simpa [formula59SecondFactor, K, I, B, X, Y, d, u, q, b2d] using hv

theorem formula59_second_product_vanish
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (formula59SecondProduct C P ξ) 1 := by
  unfold formula59SecondProduct strictPairProduct
  have h : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        formula59SecondFactor C P ξ i j)
      (orderedProduct fun _i : Fin C.s => (1 : G)) := by
    apply modEq_orderedProduct
    intro i
    have hi : D5.ModGammaSix
        (orderedProductWhere (i < ·) fun j => formula59SecondFactor C P ξ i j)
        (orderedProductWhere (i < ·) fun _j => (1 : G)) := by
      apply modEq_orderedProductWhere
      intro j hij
      exact formula59_second_factor_vanish C P hP ξ hij
    simpa [orderedProductWhere] using hi
  simpa [orderedProduct] using h

/-- Formula (60): only the first product in (59) remains. -/
theorem formula60
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (kappa C P ξ) (formula59FirstProduct C P ξ) := by
  have h59 := formula59 C P ξ
  have hv := formula59_second_product_vanish C P hP ξ
  exact h59.trans <| by
    simpa using (D5.ModEq.refl (D5.gamma G 6)
      (formula59FirstProduct C P ξ)).mul hv

end

end D5.Tahara
