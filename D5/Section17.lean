import D5.Section16

/-!
# Section 17: the multiplicative consequence of condition (6)

This file formalizes formulas (61)--(63) and the resulting relation (62).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- A product of weight-two entries may be collected in the first argument
of a commutator modulo `γ₄`. -/
theorem paperComm_orderedProduct_left_gammaTwo_mod_gamma_four
    {n : ℕ} (f : Fin n → G) (b : G)
    (hf : ∀ i, f i ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 1) :
    D5.ModEq (D5.gamma G 4) (D5.paperComm (orderedProduct f) b)
      (orderedProduct fun i => D5.paperComm (f i) b) := by
  unfold orderedProduct
  induction List.finRange n with
  | nil => simpa [D5.paperComm_eq] using
      D5.ModEq.refl (D5.gamma G 4) (1 : G)
  | cons i is ih =>
      simp only [List.map_cons, List.prod_cons]
      have hi : f i ∈ D5.gamma G 2 := hf i
      have his : (is.map f).prod ∈ D5.gamma G 2 :=
        listProd_mem (D5.gamma G 2) (is.map f) fun x hx => by
          rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
          exact hf j
      exact (D5.paperComm_mul_left_mod_gamma
        (n := 4) (r := 2) (s := 2) (t := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        hi his hb).trans <|
          (D5.ModEq.refl (D5.gamma G 4) (D5.paperComm (f i) b)).mul ih

theorem paperComm_orderedProductWhere_left_gammaTwo_mod_gamma_four
    {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → G) (b : G)
    (hf : ∀ i, p i → f i ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 1) :
    D5.ModEq (D5.gamma G 4) (D5.paperComm (orderedProductWhere p f) b)
      (orderedProductWhere p fun i => D5.paperComm (f i) b) := by
  unfold orderedProductWhere
  have aux : ∀ xs : List (Fin n),
      (∀ i ∈ xs, f i ∈ D5.gamma G 2) →
      D5.ModEq (D5.gamma G 4) (D5.paperComm (xs.map f).prod b)
        (xs.map (fun i => D5.paperComm (f i) b)).prod := by
    intro xs hxs
    induction xs with
    | nil => simpa [D5.paperComm_eq] using
        D5.ModEq.refl (D5.gamma G 4) (1 : G)
    | cons i is ih =>
        simp only [List.map_cons, List.prod_cons]
        have hi : f i ∈ D5.gamma G 2 := hxs i (by simp)
        have htail : (is.map f).prod ∈ D5.gamma G 2 :=
          listProd_mem (D5.gamma G 2) (is.map f) fun x hx => by
            rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
            exact hxs j (by simp [hj])
        exact (D5.paperComm_mul_left_mod_gamma
          (n := 4) (r := 2) (s := 2) (t := 1)
          (by norm_num) (by norm_num) (by norm_num) (by norm_num)
          hi htail hb).trans <|
            (D5.ModEq.refl (D5.gamma G 4) (D5.paperComm (f i) b)).mul
              (ih fun j hj => hxs j (by simp [hj]))
  apply aux
  intro i hi
  exact hf i (of_decide_eq_true (List.mem_filter.mp hi).2)

def formula61High
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (i < ·) fun j =>
    D5.paperComm (C.x1 j ^ orderInt C.d j) ξ ^ P.u i j

def formula61Low
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (· < i) fun h =>
    D5.paperComm (C.x1 h ^ orderInt C.d h) ξ ^
      (-P.u h i * orderRatio C.d h i)

def formula61Second
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProduct fun p => D5.paperComm (C.x2 p) ξ ^ P.v i p

def formula61Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  (formula61High C P ξ i * formula61Low C P ξ i) *
    formula61Second C P ξ i ^ orderInt C.d i

/-- Formula (61), obtained by commuting the multiplicative form of
condition (6) with `ξ` and collecting modulo `γ₄`. -/
theorem formula61
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula61Left C P ξ i) 1 := by
  let H := orderedProductWhere (i < ·) fun j =>
    C.x1 j ^ (P.u i j * orderInt C.d j)
  let L := orderedProductWhere (· < i) fun h =>
    C.x1 h ^ (-P.u h i * orderInt C.d i)
  let W := orderedProduct fun p => C.x2 p ^ P.v i p
  let T := W ^ orderInt C.d i
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hH : H ∈ D5.gamma G 2 := by
    dsimp [H]
    apply orderedProductWhere_mem
    intro j hij
    have heq : P.u i j * orderInt C.d j =
        orderInt C.d j * P.u i j := by ring
    rw [heq, zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 j) _
  have hL : L ∈ D5.gamma G 2 := by
    dsimp [L]
    apply orderedProductWhere_mem
    intro h hhi
    change C.x1 h ^ (-P.u h i * orderInt C.d i) ∈ D5.gamma G 2
    have hd := C.orderInt_eq_mul_ratio hhi.le
    have hexp : -P.u h i * orderInt C.d i =
        orderInt C.d h * (-P.u h i * orderRatio C.d h i) := by
      rw [hd]
      ring
    rw [hexp, zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  have hW : W ∈ D5.gamma G 2 := by
    dsimp [W]
    apply orderedProduct_mem
    intro p
    exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _
  have hT : T ∈ D5.gamma G 2 := (D5.gamma G 2).zpow_mem hW _
  have hword : (H * L) * T = condition6Word C P i := by
    rfl
  have hcondition : condition6Word C P i ∈ D5.gamma G 3 :=
    condition6_multiplicative_of_satisfies C P hP i
  have hzero : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ((H * L) * T) ξ) 1 := by
    rw [hword]
    exact D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hcondition hξ
  have houter := D5.paperComm_mul_left_mod_gamma
    (n := 4) (r := 2) (s := 2) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ((D5.gamma G 2).mul_mem hH hL) hT hξ
  have hinner := D5.paperComm_mul_left_mod_gamma
    (n := 4) (r := 2) (s := 2) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hH hL hξ
  have hsplit : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ((H * L) * T) ξ)
      ((D5.paperComm H ξ * D5.paperComm L ξ) * D5.paperComm T ξ) :=
    houter.trans <| hinner.mul
      (D5.ModEq.refl (D5.gamma G 4) (D5.paperComm T ξ))
  have hHex := paperComm_orderedProductWhere_left_gammaTwo_mod_gamma_four
    (i < ·) (fun j => C.x1 j ^ (P.u i j * orderInt C.d j)) ξ
    (fun j hij => by
      change C.x1 j ^ (P.u i j * orderInt C.d j) ∈ D5.gamma G 2
      have heq : P.u i j * orderInt C.d j =
          orderInt C.d j * P.u i j := by ring
      rw [heq, zpow_mul]
      exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 j) _)
    hξ
  have hHpow : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (i < ·) fun j =>
        D5.paperComm (C.x1 j ^ (P.u i j * orderInt C.d j)) ξ)
      (formula61High C P ξ i) := by
    unfold formula61High
    apply modEq_orderedProductWhere
    intro j hij
    have heq : P.u i j * orderInt C.d j =
        orderInt C.d j * P.u i j := by ring
    rw [heq, zpow_mul]
    exact D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (C.x1_order_power_mem_gamma2 j) hξ (P.u i j)
  have hLex := paperComm_orderedProductWhere_left_gammaTwo_mod_gamma_four
    (· < i) (fun h => C.x1 h ^ (-P.u h i * orderInt C.d i)) ξ
    (fun h hhi => by
      change C.x1 h ^ (-P.u h i * orderInt C.d i) ∈ D5.gamma G 2
      have hd := C.orderInt_eq_mul_ratio hhi.le
      have hexp : -P.u h i * orderInt C.d i =
          orderInt C.d h * (-P.u h i * orderRatio C.d h i) := by
        rw [hd]
        ring
      rw [hexp, zpow_mul]
      exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _)
    hξ
  have hLpow : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (· < i) fun h =>
        D5.paperComm (C.x1 h ^ (-P.u h i * orderInt C.d i)) ξ)
      (formula61Low C P ξ i) := by
    unfold formula61Low
    apply modEq_orderedProductWhere
    intro h hhi
    have hd := C.orderInt_eq_mul_ratio hhi.le
    have hexp : -P.u h i * orderInt C.d i =
        orderInt C.d h * (-P.u h i * orderRatio C.d h i) := by
      rw [hd]
      ring
    rw [hexp, zpow_mul]
    exact D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (C.x1_order_power_mem_gamma2 h) hξ
      (-P.u h i * orderRatio C.d h i)
  have hWex := paperComm_orderedProduct_left_gammaTwo_mod_gamma_four
    (fun p => C.x2 p ^ P.v i p) ξ
    (fun p => (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _) hξ
  have hWpow : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun p => D5.paperComm (C.x2 p ^ P.v i p) ξ)
      (formula61Second C P ξ i) := by
    unfold formula61Second
    apply modEq_orderedProduct
    intro p
    exact D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (C.x2_mem_gamma2 p) hξ (P.v i p)
  have hTpow := D5.paperComm_zpow_left_mod_gamma
    (n := 4) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hW hξ (orderInt C.d i)
  have hreplace : D5.ModEq (D5.gamma G 4)
      ((D5.paperComm H ξ * D5.paperComm L ξ) * D5.paperComm T ξ)
      (formula61Left C P ξ i) := by
    have hHfinal : D5.ModEq (D5.gamma G 4)
        (D5.paperComm H ξ) (formula61High C P ξ i) := hHex.trans hHpow
    have hLfinal : D5.ModEq (D5.gamma G 4)
        (D5.paperComm L ξ) (formula61Low C P ξ i) := hLex.trans hLpow
    have hWfinal : D5.ModEq (D5.gamma G 4)
        (D5.paperComm W ξ) (formula61Second C P ξ i) := hWex.trans hWpow
    have hTfinal : D5.ModEq (D5.gamma G 4)
        (D5.paperComm T ξ)
        (formula61Second C P ξ i ^ orderInt C.d i) :=
      hTpow.trans (hWfinal.zpow (orderInt C.d i))
    exact (hHfinal.mul hLfinal).mul hTfinal
  exact (hsplit.trans hreplace).symm.trans hzero

/-! ## The correction exponents in formula (63) -/

def formula63HighExponent
    (C : Context G) (P : Parameters C.s C.t)
    (i j : Fin C.s) : ℤ :=
  -P.u i j * TaharaArithmetic.binom2 (C.d j) +
    orderInt C.d i * P.w i j j

def formula63LowExponent
    (C : Context G) (P : Parameters C.s C.t)
    (h i : Fin C.s) : ℤ :=
  P.u h i * orderRatio C.d h i * TaharaArithmetic.binom2 (C.d h) +
    orderInt C.d i * P.w'' h h i

/-- Condition (8), in the exact exponent form used in the second line of
(63). -/
theorem formula63_high_exponent
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    {i j : Fin C.s} (hij : i < j) :
    formula63HighExponent C P i j =
      -orderInt C.d j * P.w' i j j := by
  have hpairs := pairConsequences C P hP hij
  have he : orderInt C.d j =
      orderInt C.d i * orderRatio C.d i j :=
    C.orderInt_eq_mul_ratio hij.le
  unfold formula63HighExponent
  calc
    -P.u i j * TaharaArithmetic.binom2 (C.d j) +
        orderInt C.d i * P.w i j j =
      -(P.u i j * TaharaArithmetic.binom2 (C.d j)) +
        orderInt C.d i * P.w i j j := by ring
    _ = -(orderInt C.d i *
          (P.w i j j + orderRatio C.d i j * P.w' i j j)) +
        orderInt C.d i * P.w i j j := by rw [hpairs.equation12]
    _ = -orderInt C.d j * P.w' i j j := by rw [he]; ring

/-- Condition (7), applied to `h < i`, in the exact exponent form used in
the third line of (63). -/
theorem formula63_low_exponent
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    {h i : Fin C.s} (hhi : h < i) :
    formula63LowExponent C P h i =
      -orderInt C.d h * P.w h h i := by
  have hpairs := pairConsequences C P hP hhi
  have he : orderInt C.d i =
      orderInt C.d h * orderRatio C.d h i :=
    C.orderInt_eq_mul_ratio hhi.le
  unfold formula63LowExponent
  rw [hpairs.equation13, he]
  ring

def formula63HighCorrection
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) : G :=
  orderedProductWhere (i < ·) fun j =>
    D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j) ^
      formula63HighExponent C P i j

def formula63LowCorrection
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) : G :=
  orderedProductWhere (· < i) fun h =>
    D5.paperComm (D5.paperComm (C.x1 h) ξ) (C.x1 h) ^
      formula63LowExponent C P h i

theorem formula63_high_correction_mem_gamma4
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    formula63HighCorrection C P ξ i ∈ D5.gamma G 4 := by
  unfold formula63HighCorrection
  apply orderedProductWhere_mem
  intro j hij
  rw [formula63_high_exponent C P hP hij]
  have hexp : -orderInt C.d j * P.w' i j j =
      orderInt C.d j * (-P.w' i j j) := by ring
  rw [hexp, zpow_mul]
  exact (D5.gamma G 4).zpow_mem (formula58 C ξ j) _

theorem formula63_low_correction_mem_gamma4
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    formula63LowCorrection C P ξ i ∈ D5.gamma G 4 := by
  unfold formula63LowCorrection
  apply orderedProductWhere_mem
  intro h hhi
  rw [formula63_low_exponent C P hP hhi]
  have hexp : -orderInt C.d h * P.w h h i =
      orderInt C.d h * (-P.w h h i) := by ring
  rw [hexp, zpow_mul]
  exact (D5.gamma G 4).zpow_mem (formula58 C ξ h) _

theorem formula63_corrections_vanish
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (formula63HighCorrection C P ξ i *
        formula63LowCorrection C P ξ i) 1 := by
  apply D5.modEq_one_iff_mem.mpr
  exact (D5.gamma G 4).mul_mem
    (formula63_high_correction_mem_gamma4 C P hP ξ i)
    (formula63_low_correction_mem_gamma4 C P hP ξ i)

/-! ## Expansion of the left side of (62) -/

/-- Rearranged and powered form of (57), used for both index ranges in
(63). -/
theorem formula57_rearranged_zpow
    (C : Context G) (ξ : G) (k : Fin C.s) (z : ℤ) :
    D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 k) ξ ^ (orderInt C.d k * z))
      (D5.paperComm (C.x1 k ^ orderInt C.d k) ξ ^ z *
        D5.paperComm (D5.paperComm (C.x1 k) ξ) (C.x1 k) ^
          (-TaharaArithmetic.binom2 (C.d k) * z)) := by
  let A := D5.paperComm (C.x1 k) ξ
  let I := D5.paperComm A (C.x1 k)
  let Q := D5.paperComm (C.x1 k ^ orderInt C.d k) ξ
  let d := orderInt C.d k
  let b2 := TaharaArithmetic.binom2 (C.d k)
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : A ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hk hξ
  have hI : I ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hk
  have hQ : Q ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (C.x1_order_power_mem_gamma2 k) hξ
  have h57 : D5.ModEq (D5.gamma G 4) Q (A ^ d * I ^ b2) := by
    simpa [Q, A, I, d, b2] using formula57 C ξ k
  have hrearr : D5.ModEq (D5.gamma G 4) (A ^ d)
      (Q * I ^ (-b2)) := by
    have h := h57.symm.mul
      (D5.ModEq.refl (D5.gamma G 4) (I ^ (-b2)))
    simpa [← zpow_add] using h
  have hpow := hrearr.zpow z
  have hsplit := gammaTwoThree_mul_zpow_mod_gamma_four
    (D5.gamma_antitone G (by norm_num) hQ)
    ((D5.gamma G 3).zpow_mem hI (-b2)) z
  have h := hpow.trans hsplit
  simpa [A, I, Q, d, b2, zpow_mul] using h

def formula62High
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (i < ·) fun j =>
    D5.paperComm (C.x1 j) ξ ^ (P.u i j * orderInt C.d j)

def formula62Low
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (· < i) fun h =>
    D5.paperComm (C.x1 h) ξ ^ (-P.u h i * orderInt C.d i)

def formula62HighWeightThree
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (i < ·) fun j =>
    D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j) ^ P.w i j j

def formula62LowWeightThree
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (· < i) fun h =>
    D5.paperComm (D5.paperComm (C.x1 h) ξ) (C.x1 h) ^ P.w'' h h i

def formula62Inner
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  (formula61Second C P ξ i * formula62HighWeightThree C P ξ i) *
    formula62LowWeightThree C P ξ i

def formula62Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  (formula62High C P ξ i * formula62Low C P ξ i) *
    formula62Inner C P ξ i ^ orderInt C.d i

def formula63HighNegative
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (i < ·) fun j =>
    D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j) ^
      (-P.u i j * TaharaArithmetic.binom2 (C.d j))

def formula63LowPositive
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (· < i) fun h =>
    D5.paperComm (D5.paperComm (C.x1 h) ξ) (C.x1 h) ^
      (P.u h i * orderRatio C.d h i *
        TaharaArithmetic.binom2 (C.d h))

theorem formula62_high_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula62High C P ξ i)
      (formula61High C P ξ i * formula63HighNegative C P ξ i) := by
  let F : Fin C.s → G := fun j =>
    D5.paperComm (C.x1 j ^ orderInt C.d j) ξ ^ P.u i j
  let E : Fin C.s → G := fun j =>
    D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j) ^
      (-P.u i j * TaharaArithmetic.binom2 (C.d j))
  have hlocal : D5.ModEq (D5.gamma G 4) (formula62High C P ξ i)
      (orderedProductWhere (i < ·) fun j => F j * E j) := by
    unfold formula62High
    apply modEq_orderedProductWhere
    intro j hij
    have hexp : P.u i j * orderInt C.d j =
        orderInt C.d j * P.u i j := by ring
    rw [hexp]
    simpa [F, E, mul_comm, mul_left_comm, mul_assoc] using
      formula57_rearranged_zpow C ξ j (P.u i j)
  have hF : ∀ j, i < j → F j ∈ D5.gamma G 3 := by
    intro j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x1_order_power_mem_gamma2 j) hξ) _
  have hE : ∀ j, i < j → E j ∈ D5.gamma G 3 := by
    intro j hij
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ) hj) _
  have hsplit := (D5.orderedProductWhere_pointwise_mul_gammaThree
    (i < ·) F E hF hE).mono
      (D5.gamma_antitone G (by norm_num : 4 ≤ 6))
  simpa [formula61High, formula63HighNegative, F, E] using
    hlocal.trans hsplit

theorem formula62_low_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula62Low C P ξ i)
      (formula61Low C P ξ i * formula63LowPositive C P ξ i) := by
  let F : Fin C.s → G := fun h =>
    D5.paperComm (C.x1 h ^ orderInt C.d h) ξ ^
      (-P.u h i * orderRatio C.d h i)
  let E : Fin C.s → G := fun h =>
    D5.paperComm (D5.paperComm (C.x1 h) ξ) (C.x1 h) ^
      (P.u h i * orderRatio C.d h i * TaharaArithmetic.binom2 (C.d h))
  have hlocal : D5.ModEq (D5.gamma G 4) (formula62Low C P ξ i)
      (orderedProductWhere (· < i) fun h => F h * E h) := by
    unfold formula62Low
    apply modEq_orderedProductWhere
    intro h hhi
    have hd := C.orderInt_eq_mul_ratio hhi.le
    have hexp : -P.u h i * orderInt C.d i =
        orderInt C.d h * (-P.u h i * orderRatio C.d h i) := by
      rw [hd]
      ring
    rw [hexp]
    simpa [F, E, mul_comm, mul_left_comm, mul_assoc] using
      formula57_rearranged_zpow C ξ h (-P.u h i * orderRatio C.d h i)
  have hF : ∀ h, h < i → F h ∈ D5.gamma G 3 := by
    intro h hhi
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x1_order_power_mem_gamma2 h) hξ) _
  have hE : ∀ h, h < i → E h ∈ D5.gamma G 3 := by
    intro h hhi
    have hh : C.x1 h ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hh hξ) hh) _
  have hsplit := (D5.orderedProductWhere_pointwise_mul_gammaThree
    (· < i) F E hF hE).mono
      (D5.gamma_antitone G (by norm_num : 4 ≤ 6))
  simpa [formula61Low, formula63LowPositive, F, E] using
    hlocal.trans hsplit

def formula63HighFromInner
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (i < ·) fun j =>
    D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j) ^
      (P.w i j j * orderInt C.d i)

def formula63LowFromInner
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) : G :=
  orderedProductWhere (· < i) fun h =>
    D5.paperComm (D5.paperComm (C.x1 h) ξ) (C.x1 h) ^
      (P.w'' h h i * orderInt C.d i)

theorem formula62_inner_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (formula62Inner C P ξ i ^ orderInt C.d i)
      ((formula61Second C P ξ i ^ orderInt C.d i *
          formula63HighFromInner C P ξ i) *
        formula63LowFromInner C P ξ i) := by
  let R := formula61Second C P ξ i
  let H := formula62HighWeightThree C P ξ i
  let L := formula62LowWeightThree C P ξ i
  let d := orderInt C.d i
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hR : R ∈ D5.gamma G 3 := by
    dsimp [R, formula61Second]
    apply orderedProduct_mem
    intro p
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x2_mem_gamma2 p) hξ) _
  have hH : H ∈ D5.gamma G 3 := by
    dsimp [H, formula62HighWeightThree]
    apply orderedProductWhere_mem
    intro j hij
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ) hj) _
  have hL : L ∈ D5.gamma G 3 := by
    dsimp [L, formula62LowWeightThree]
    apply orderedProductWhere_mem
    intro h hhi
    have hh : C.x1 h ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hh hξ) hh) _
  have houter := D5.gammaThree_mul_zpow
    ((D5.gamma G 3).mul_mem hR hH) hL d
  have hinner := D5.gammaThree_mul_zpow hR hH d
  have hsplit : D5.ModGammaSix (((R * H) * L) ^ d)
      ((R ^ d * H ^ d) * L ^ d) :=
    houter.trans <| hinner.mul (D5.ModEq.refl (D5.gamma G 6) (L ^ d))
  have hHz := orderedProductWhere_zpow_gammaThree
    (i < ·)
    (fun j => D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j) ^ P.w i j j)
    (fun j hij => by
      have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
      exact (D5.gamma G 3).zpow_mem
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ) hj) _)
    d
  have hHfinal : D5.ModGammaSix (H ^ d) (formula63HighFromInner C P ξ i) := by
    simpa [H, d, formula62HighWeightThree, formula63HighFromInner,
      zpow_mul] using hHz
  have hLz := orderedProductWhere_zpow_gammaThree
    (· < i)
    (fun h => D5.paperComm (D5.paperComm (C.x1 h) ξ) (C.x1 h) ^ P.w'' h h i)
    (fun h hhi => by
      have hh : C.x1 h ∈ D5.gamma G 1 := by simp [D5.gamma]
      exact (D5.gamma G 3).zpow_mem
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hh hξ) hh) _)
    d
  have hLfinal : D5.ModGammaSix (L ^ d) (formula63LowFromInner C P ξ i) := by
    simpa [L, d, formula62LowWeightThree, formula63LowFromInner,
      zpow_mul] using hLz
  have h := hsplit.trans <|
    ((D5.ModEq.refl (D5.gamma G 6) (R ^ d)).mul hHfinal).mul hLfinal
  simpa [formula62Inner, R, H, L, d] using
    h.mono (D5.gamma_antitone G (by norm_num : 4 ≤ 6))

theorem formula63_high_combine
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (formula63HighNegative C P ξ i * formula63HighFromInner C P ξ i)
      (formula63HighCorrection C P ξ i) := by
  let I : Fin C.s → G := fun j =>
    D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j)
  let A : Fin C.s → G := fun j =>
    I j ^ (-P.u i j * TaharaArithmetic.binom2 (C.d j))
  let B : Fin C.s → G := fun j => I j ^ (P.w i j j * orderInt C.d i)
  have hI : ∀ j, i < j → I j ∈ D5.gamma G 3 := by
    intro j hij
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ) hj
  have hsplit := (D5.orderedProductWhere_pointwise_mul_gammaThree
    (i < ·) A B
    (fun j hij => (D5.gamma G 3).zpow_mem (hI j hij) _)
    (fun j hij => (D5.gamma G 3).zpow_mem (hI j hij) _)).symm.mono
      (D5.gamma_antitone G (by norm_num : 4 ≤ 6))
  have hpoint : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (i < ·) fun j => A j * B j)
      (formula63HighCorrection C P ξ i) := by
    unfold formula63HighCorrection
    apply modEq_orderedProductWhere
    intro j hij
    dsimp [A, B]
    have hexp : -P.u i j * TaharaArithmetic.binom2 (C.d j) +
        P.w i j j * orderInt C.d i = formula63HighExponent C P i j := by
      unfold formula63HighExponent
      ring
    rw [← zpow_add, hexp]
  simpa [formula63HighNegative, formula63HighFromInner, A, B, I] using
    hsplit.trans hpoint

theorem formula63_low_combine
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (formula63LowPositive C P ξ i * formula63LowFromInner C P ξ i)
      (formula63LowCorrection C P ξ i) := by
  let I : Fin C.s → G := fun h =>
    D5.paperComm (D5.paperComm (C.x1 h) ξ) (C.x1 h)
  let A : Fin C.s → G := fun h =>
    I h ^ (P.u h i * orderRatio C.d h i * TaharaArithmetic.binom2 (C.d h))
  let B : Fin C.s → G := fun h => I h ^ (P.w'' h h i * orderInt C.d i)
  have hI : ∀ h, h < i → I h ∈ D5.gamma G 3 := by
    intro h hhi
    have hh : C.x1 h ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hh hξ) hh
  have hsplit := (D5.orderedProductWhere_pointwise_mul_gammaThree
    (· < i) A B
    (fun h hhi => (D5.gamma G 3).zpow_mem (hI h hhi) _)
    (fun h hhi => (D5.gamma G 3).zpow_mem (hI h hhi) _)).symm.mono
      (D5.gamma_antitone G (by norm_num : 4 ≤ 6))
  have hpoint : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (· < i) fun h => A h * B h)
      (formula63LowCorrection C P ξ i) := by
    unfold formula63LowCorrection
    apply modEq_orderedProductWhere
    intro h hhi
    dsimp [A, B]
    have hexp :
        P.u h i * orderRatio C.d h i * TaharaArithmetic.binom2 (C.d h) +
          P.w'' h h i * orderInt C.d i = formula63LowExponent C P h i := by
      unfold formula63LowExponent
      ring
    rw [← zpow_add, hexp]
  simpa [formula63LowPositive, formula63LowFromInner, A, B, I] using
    hsplit.trans hpoint

/-- Formula (63): after expanding (57) throughout (62), the first line is
exactly (61) and the remaining two streams have the displayed correction
exponents. -/
theorem formula63
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula62Left C P ξ i)
      ((formula61Left C P ξ i * formula63HighCorrection C P ξ i) *
        formula63LowCorrection C P ξ i) := by
  let PH := formula61High C P ξ i
  let HN := formula63HighNegative C P ξ i
  let PL := formula61Low C P ξ i
  let LP := formula63LowPositive C P ξ i
  let RD := formula61Second C P ξ i ^ orderInt C.d i
  let HI := formula63HighFromInner C P ξ i
  let LI := formula63LowFromInner C P ξ i
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hPH : PH ∈ D5.gamma G 3 := by
    dsimp [PH, formula61High]
    apply orderedProductWhere_mem
    intro j hij
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x1_order_power_mem_gamma2 j) hξ) _
  have hHN : HN ∈ D5.gamma G 3 := by
    dsimp [HN, formula63HighNegative]
    apply orderedProductWhere_mem
    intro j hij
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ) hj) _
  have hPL : PL ∈ D5.gamma G 3 := by
    dsimp [PL, formula61Low]
    apply orderedProductWhere_mem
    intro h hhi
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x1_order_power_mem_gamma2 h) hξ) _
  have hLP : LP ∈ D5.gamma G 3 := by
    dsimp [LP, formula63LowPositive]
    apply orderedProductWhere_mem
    intro h hhi
    have hh : C.x1 h ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hh hξ) hh) _
  have hRD : RD ∈ D5.gamma G 3 := by
    apply (D5.gamma G 3).zpow_mem
    dsimp [RD, formula61Second]
    apply orderedProduct_mem
    intro p
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x2_mem_gamma2 p) hξ) _
  have hHI : HI ∈ D5.gamma G 3 := by
    dsimp [HI, formula63HighFromInner]
    apply orderedProductWhere_mem
    intro j hij
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ) hj) _
  have hLI : LI ∈ D5.gamma G 3 := by
    dsimp [LI, formula63LowFromInner]
    apply orderedProductWhere_mem
    intro h hhi
    have hh : C.x1 h ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hh hξ) hh) _
  have hbase : D5.ModEq (D5.gamma G 4) (formula62Left C P ξ i)
      (((PH * HN) * (PL * LP)) * ((RD * HI) * LI)) := by
    have h := ((formula62_high_expand C P ξ i).mul
      (formula62_low_expand C P ξ i)).mul
        (formula62_inner_expand C P ξ i)
    simpa [formula62Left, PH, HN, PL, LP, RD, HI, LI] using h
  have hswap1 : D5.ModGammaSix
      (((PH * HN) * (PL * LP)) * ((RD * HI) * LI))
      (((PH * PL) * (HN * LP)) * ((RD * HI) * LI)) :=
    (D5.gammaThree_interchange (a := PH) (b := HN) (c := PL) (d := LP)
      hHN hPL).mul (D5.ModEq.refl (D5.gamma G 6) ((RD * HI) * LI))
  have hswap2 : D5.ModGammaSix
      (((PH * PL) * (HN * LP)) * ((RD * HI) * LI))
      (((PH * PL) * RD) * ((HN * LP) * (HI * LI))) := by
    simpa [mul_assoc] using D5.gammaThree_interchange
      (a := PH * PL) (b := HN * LP) (c := RD) (d := HI * LI)
      ((D5.gamma G 3).mul_mem hHN hLP) hRD
  have hswap3 : D5.ModGammaSix
      (((PH * PL) * RD) * ((HN * LP) * (HI * LI)))
      (((PH * PL) * RD) * ((HN * HI) * (LP * LI))) :=
    (D5.ModEq.refl (D5.gamma G 6) ((PH * PL) * RD)).mul <|
      D5.gammaThree_interchange (a := HN) (b := LP) (c := HI) (d := LI)
        hLP hHI
  have hreorder := (hswap1.trans (hswap2.trans hswap3)).mono
    (D5.gamma_antitone G (by norm_num : 4 ≤ 6))
  have hcombine : D5.ModEq (D5.gamma G 4)
      (((PH * PL) * RD) * ((HN * HI) * (LP * LI)))
      ((formula61Left C P ξ i * formula63HighCorrection C P ξ i) *
        formula63LowCorrection C P ξ i) := by
    have hh := formula63_high_combine C P ξ i
    have hl := formula63_low_combine C P ξ i
    simpa [formula61Left, PH, PL, RD, HN, HI, LP, LI, mul_assoc] using
      ((D5.ModEq.refl (D5.gamma G 4) ((PH * PL) * RD)).mul hh).mul hl
  exact hbase.trans (hreorder.trans hcombine)

/-- Formula (62).  Formula (61) removes the principal line of (63), while
conditions (7), (8) and formula (58) remove both correction streams. -/
theorem formula62
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula62Left C P ξ i) 1 := by
  have h63 := formula63 C P ξ i
  have h61 := formula61 C P hP ξ i
  have hc := formula63_corrections_vanish C P hP ξ i
  have hfinish := h61.mul hc
  exact h63.trans <| by
    simpa [mul_assoc] using hfinish

end

end D5.Tahara
