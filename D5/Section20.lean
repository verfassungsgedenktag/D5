import D5.Section19

/-!
# Section 20: the mixed corrections from Tahara condition (11)

The first step is formula (72), where the diagonal term in condition (11)
is removed using condition (2).  The remaining group and coordinate
consequences are developed after this exact arithmetic normalization.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The coefficient printed in formula (72), with the diagonal
`w i i i` term already removed. -/
def formula72Coefficient
    (C : Context G) (P : Parameters C.s C.t)
    (i : Fin C.s) (p : Fin C.t) : ℤ :=
  TaharaArithmetic.binom2 (C.d i) * P.v i p -
    (∑ h ∈ Finset.univ.filter (· < i), P.w h i i * C.b h p) -
    (∑ j ∈ Finset.univ.filter (i < ·), P.w'' i i j * C.b j p)

/-- A weak lower triangular sum splits into the strict lower part and its
diagonal entry. -/
theorem sum_filter_le_eq_sum_filter_lt_add
    {n : ℕ} (i : Fin n) (a : Fin n → ℤ) :
    (∑ h ∈ Finset.univ.filter (· ≤ i), a h) =
      (∑ h ∈ Finset.univ.filter (· < i), a h) + a i := by
  have hset : Finset.univ.filter (· ≤ i) =
      insert i (Finset.univ.filter (· < i)) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  rw [add_comm]

/-- Formula (72), derived from condition (11) after Lean checks that the
only removed summand is zero by condition (2). -/
theorem formula72
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (i : Fin C.s) (p : Fin C.t) :
    Int.ModEq (orderGCD C.d C.e i p) (formula72Coefficient C P i p) 0 := by
  rcases hP with
    ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hsplit := sum_filter_le_eq_sum_filter_lt_add i
    (fun h => P.w h i i * C.b h p)
  have hdiag : P.w i i i * C.b i p = 0 := by rw [h2 i, zero_mul]
  have hsum :
      (∑ h ∈ Finset.univ.filter (· ≤ i), P.w h i i * C.b h p) =
        ∑ h ∈ Finset.univ.filter (· < i), P.w h i i * C.b h p := by
    rw [hsplit, hdiag, add_zero]
  have h := condition11_formula30 C P h11 i p
  simpa [condition11Coefficient, formula72Coefficient, hsum, mul_comm] using h

/-- The group word displayed in formula (73).  The two last products use
flattened integer powers, definitionally equivalent to powers of
`x₁h ^ d(h)`. -/
def formula73Word
    (C : Context G) (P : Parameters C.s C.t) (i : Fin C.s) : G :=
  ((orderedProduct (fun p => C.x2 p ^ P.v i p) ^
      TaharaArithmetic.binom2 (C.d i)) *
    orderedProductWhere (· < i) (fun h =>
      C.x1 h ^ (orderInt C.d h * (-P.w h i i)))) *
    orderedProductWhere (i < ·) (fun j =>
      C.x1 j ^ (orderInt C.d j * (-P.w'' i i j)))

/-- Formula (73): condition (11), after removal of the zero diagonal term,
places the printed word in `γ₂(G)^{d(i)} γ₃(G)`. -/
theorem formula73
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (i : Fin C.s) :
    IsGammaTwoPowerModGammaThree (orderInt C.d i)
      (formula73Word C P i) := by
  let V : Fin C.t → ℤ := fun p =>
    TaharaArithmetic.binom2 (C.d i) * P.v i p
  let A : Fin C.t → ℤ := fun p =>
    ∑ h ∈ Finset.univ.filter (· < i), (-P.w h i i) * C.b h p
  let B : Fin C.t → ℤ := fun p =>
    ∑ j ∈ Finset.univ.filter (i < ·), (-P.w'' i i j) * C.b j p
  let M : Fin C.t → ℤ := fun p => V p + A p + B p
  have hv : D5.ModEq (D5.gamma G 3)
      (orderedProduct (fun p => C.x2 p ^ P.v i p) ^
        TaharaArithmetic.binom2 (C.d i))
      (orderedProduct fun p => C.x2 p ^ V p) := by
    simpa [V, mul_comm] using coordinateProduct_zpow_mod_gamma3 C
      (P.v i) (TaharaArithmetic.binom2 (C.d i))
  have hA : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (· < i) fun h =>
        C.x1 h ^ (orderInt C.d h * (-P.w h i i)))
      (orderedProduct fun p => C.x2 p ^ A p) := by
    refine (modEq_orderedProductWhere (· < i)
      (f := fun h => C.x1 h ^ (orderInt C.d h * (-P.w h i i)))
      (g := fun h => orderedProduct fun p =>
        C.x2 p ^ ((-P.w h i i) * C.b h p)) ?_).trans ?_
    · intro h hhi
      exact x1_order_multiple_mod_gamma3 C h (-P.w h i i)
    · exact coordinateProductWhere_mod_gamma3 C (· < i)
        (fun h p => (-P.w h i i) * C.b h p)
  have hB : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (i < ·) fun j =>
        C.x1 j ^ (orderInt C.d j * (-P.w'' i i j)))
      (orderedProduct fun p => C.x2 p ^ B p) := by
    refine (modEq_orderedProductWhere (i < ·)
      (f := fun j => C.x1 j ^ (orderInt C.d j * (-P.w'' i i j)))
      (g := fun j => orderedProduct fun p =>
        C.x2 p ^ ((-P.w'' i i j) * C.b j p)) ?_).trans ?_
    · intro j hij
      exact x1_order_multiple_mod_gamma3 C j (-P.w'' i i j)
    · exact coordinateProductWhere_mod_gamma3 C (i < ·)
        (fun j p => (-P.w'' i i j) * C.b j p)
  have hcollectVA := coordinateProduct_mul_mod_gamma3 C V A
  have hcollectM := coordinateProduct_mul_mod_gamma3 C
    (fun p => V p + A p) B
  have hword : D5.ModEq (D5.gamma G 3) (formula73Word C P i)
      (orderedProduct fun p => C.x2 p ^ M p) := by
    have h := (hv.mul hA).mul hB
    exact h.trans <| by
      simpa [M] using
        (hcollectVA.mul (D5.ModEq.refl (D5.gamma G 3) _)).trans hcollectM
  have hm : ∀ p, ((Nat.gcd (C.d i) (C.e p) : ℕ) : ℤ) ∣ M p := by
    intro p
    have hc := Int.modEq_zero_iff_dvd.mp (formula72 C P hP i p)
    change ((Nat.gcd (C.d i) (C.e p) : ℕ) : ℤ) ∣
      formula72Coefficient C P i p at hc
    convert hc using 1
    dsimp [M, V, A, B, formula72Coefficient]
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    ring
  rcases coordinateProduct_is_gammaTwoPower_mod_gammaThree C (C.d i) M hm with
    ⟨y, hy, hcoord⟩
  exact ⟨y, hy, hword.trans hcoord⟩

/-- Elementwise form of membership in `γ₃(G)^d γ₄(G)`. -/
def IsGammaThreePowerModGammaFour (d : ℤ) (g : G) : Prop :=
  ∃ y ∈ D5.gamma G 3, D5.ModEq (D5.gamma G 4) g (y ^ d)

/-- The commutator word printed in formula (74). -/
def formula74Word
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) : G :=
  ((formula61Second C P ξ i ^ TaharaArithmetic.binom2 (C.d i)) *
    orderedProductWhere (· < i) (fun h =>
      D5.paperComm (C.x1 h ^ orderInt C.d h) ξ ^ (-P.w h i i))) *
    orderedProductWhere (i < ·) (fun j =>
      D5.paperComm (C.x1 j ^ orderInt C.d j) ξ ^ (-P.w'' i i j))

/-- Commuting the three factors of (73) with `ξ` produces exactly the
three factors printed in (74), modulo `γ₄`. -/
theorem formula74_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (D5.paperComm (formula73Word C P i) ξ)
      (formula74Word C P ξ i) := by
  let R := orderedProduct fun p => C.x2 p ^ P.v i p
  let L := orderedProductWhere (· < i) fun h =>
    C.x1 h ^ (orderInt C.d h * (-P.w h i i))
  let H := orderedProductWhere (i < ·) fun j =>
    C.x1 j ^ (orderInt C.d j * (-P.w'' i i j))
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hR : R ∈ D5.gamma G 2 := by
    dsimp [R]
    apply orderedProduct_mem
    intro p
    exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _
  have hL : L ∈ D5.gamma G 2 := by
    dsimp [L]
    apply orderedProductWhere_mem
    intro h hhi
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  have hH : H ∈ D5.gamma G 2 := by
    dsimp [H]
    apply orderedProductWhere_mem
    intro j hij
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 j) _
  have hRpow : R ^ TaharaArithmetic.binom2 (C.d i) ∈ D5.gamma G 2 :=
    (D5.gamma G 2).zpow_mem hR _
  have houter := D5.paperComm_mul_left_mod_gamma
    (n := 4) (r := 2) (s := 2) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    ((D5.gamma G 2).mul_mem hRpow hL) hH hξ
  have hinner := D5.paperComm_mul_left_mod_gamma
    (n := 4) (r := 2) (s := 2) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hRpow hL hξ
  have hsplit : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ((R ^ TaharaArithmetic.binom2 (C.d i) * L) * H) ξ)
      ((D5.paperComm (R ^ TaharaArithmetic.binom2 (C.d i)) ξ *
        D5.paperComm L ξ) * D5.paperComm H ξ) :=
    houter.trans <| hinner.mul
      (D5.ModEq.refl (D5.gamma G 4) (D5.paperComm H ξ))
  have hRtransfer := D5.paperComm_zpow_left_mod_gamma
    (n := 4) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num)
    hR hξ (TaharaArithmetic.binom2 (C.d i))
  have hRexpand := paperComm_orderedProduct_left_gammaTwo_mod_gamma_four
    (fun p => C.x2 p ^ P.v i p) ξ
    (fun p => (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _) hξ
  have hRlocal : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun p => D5.paperComm (C.x2 p ^ P.v i p) ξ)
      (formula61Second C P ξ i) := by
    unfold formula61Second
    apply modEq_orderedProduct
    intro p
    exact D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (C.x2_mem_gamma2 p) hξ (P.v i p)
  have hRfinal : D5.ModEq (D5.gamma G 4)
      (D5.paperComm (R ^ TaharaArithmetic.binom2 (C.d i)) ξ)
      (formula61Second C P ξ i ^ TaharaArithmetic.binom2 (C.d i)) :=
    hRtransfer.trans <|
      (hRexpand.trans hRlocal).zpow (TaharaArithmetic.binom2 (C.d i))
  have hLexpand := paperComm_orderedProductWhere_left_gammaTwo_mod_gamma_four
    (· < i) (fun h => C.x1 h ^ (orderInt C.d h * (-P.w h i i))) ξ
    (fun h hhi => by
      change C.x1 h ^ (orderInt C.d h * (-P.w h i i)) ∈ D5.gamma G 2
      rw [zpow_mul]
      exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _)
    hξ
  have hLlocal : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (· < i) fun h =>
        D5.paperComm (C.x1 h ^ (orderInt C.d h * (-P.w h i i))) ξ)
      (orderedProductWhere (· < i) fun h =>
        D5.paperComm (C.x1 h ^ orderInt C.d h) ξ ^ (-P.w h i i)) := by
    apply modEq_orderedProductWhere
    intro h hhi
    rw [zpow_mul]
    exact D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (C.x1_order_power_mem_gamma2 h) hξ (-P.w h i i)
  have hHexpand := paperComm_orderedProductWhere_left_gammaTwo_mod_gamma_four
    (i < ·) (fun j => C.x1 j ^ (orderInt C.d j * (-P.w'' i i j))) ξ
    (fun j hij => by
      change C.x1 j ^ (orderInt C.d j * (-P.w'' i i j)) ∈ D5.gamma G 2
      rw [zpow_mul]
      exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 j) _)
    hξ
  have hHlocal : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (i < ·) fun j =>
        D5.paperComm (C.x1 j ^ (orderInt C.d j * (-P.w'' i i j))) ξ)
      (orderedProductWhere (i < ·) fun j =>
        D5.paperComm (C.x1 j ^ orderInt C.d j) ξ ^ (-P.w'' i i j)) := by
    apply modEq_orderedProductWhere
    intro j hij
    rw [zpow_mul]
    exact D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (C.x1_order_power_mem_gamma2 j) hξ (-P.w'' i i j)
  have hreplace := (hRfinal.mul (hLexpand.trans hLlocal)).mul
    (hHexpand.trans hHlocal)
  simpa [formula73Word, formula74Word, R, L, H] using hsplit.trans hreplace

/-- Formula (74): the printed commutator word is a `d(i)`-th power from
`γ₃`, modulo `γ₄`. -/
theorem formula74
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    IsGammaThreePowerModGammaFour (orderInt C.d i)
      (formula74Word C P ξ i) := by
  rcases formula73 C P hP i with ⟨y, hy, h73⟩
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 3) (s := 1) (by norm_num) (by norm_num) h73 hξ
  have htransfer := D5.paperComm_zpow_left_mod_gamma
    (n := 4) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num)
    hy hξ (orderInt C.d i)
  let z := D5.paperComm y ξ
  have hz : z ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hy hξ
  refine ⟨z, hz, ?_⟩
  exact (formula74_expansion C P ξ i).symm.trans <|
    hlift.trans <| by simpa [z] using htransfer

/-- The full exponent on the left side of formula (75). -/
def formula75Coefficient
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) (l : Fin C.r) : ℤ :=
  TaharaArithmetic.binom2 (C.d i) *
      (∑ p, P.v i p * lambda C ξ p l) -
    (∑ h ∈ Finset.univ.filter (· < i),
      P.w h i i * (∑ p, C.b h p * lambda C ξ p l)) -
    (∑ j ∈ Finset.univ.filter (i < ·),
      P.w'' i i j * (∑ p, C.b j p * lambda C ξ p l))

/-- Coordinate expansion of the complete word in formula (74). -/
theorem formula74_coordinates
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula74Word C P ξ i)
      (orderedProduct fun l => C.x3 l ^ formula75Coefficient C P ξ i l) := by
  let S : Fin C.r → ℤ := fun l => ∑ p, P.v i p * lambda C ξ p l
  let A : Fin C.r → ℤ := fun l =>
    ∑ h ∈ Finset.univ.filter (· < i),
      (-P.w h i i) * formula67Coefficient C ξ h l
  let B : Fin C.r → ℤ := fun l =>
    ∑ j ∈ Finset.univ.filter (i < ·),
      (-P.w'' i i j) * formula67Coefficient C ξ j l
  have hsecondLocal : D5.ModEq (D5.gamma G 4)
      (formula61Second C P ξ i)
      (orderedProduct fun p =>
        orderedProduct fun l => C.x3 l ^ (P.v i p * lambda C ξ p l)) := by
    unfold formula61Second
    apply modEq_orderedProduct
    intro p
    exact (formula64 C ξ p).zpow (P.v i p) |>.trans
      (x3CoordinateProduct_zpow C (lambda C ξ p) (P.v i p))
  have hsecondBase : D5.ModEq (D5.gamma G 4)
      (formula61Second C P ξ i)
      (orderedProduct fun l => C.x3 l ^ S l) :=
    hsecondLocal.trans <| by
      simpa [S] using x3CoordinateProducts_collect C
        (fun p l => P.v i p * lambda C ξ p l)
  have hsecond : D5.ModEq (D5.gamma G 4)
      (formula61Second C P ξ i ^ TaharaArithmetic.binom2 (C.d i))
      (orderedProduct fun l => C.x3 l ^
        (TaharaArithmetic.binom2 (C.d i) * S l)) :=
    (hsecondBase.zpow (TaharaArithmetic.binom2 (C.d i))).trans
      (x3CoordinateProduct_zpow C S (TaharaArithmetic.binom2 (C.d i)))
  have hlowLocal : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (· < i) fun h =>
        D5.paperComm (C.x1 h ^ orderInt C.d h) ξ ^ (-P.w h i i))
      (orderedProductWhere (· < i) fun h =>
        orderedProduct fun l => C.x3 l ^
          ((-P.w h i i) * formula67Coefficient C ξ h l)) := by
    apply modEq_orderedProductWhere
    intro h hhi
    exact (formula67 C ξ h).zpow (-P.w h i i) |>.trans
      (x3CoordinateProduct_zpow C (formula67Coefficient C ξ h) (-P.w h i i))
  have hlow : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (· < i) fun h =>
        D5.paperComm (C.x1 h ^ orderInt C.d h) ξ ^ (-P.w h i i))
      (orderedProduct fun l => C.x3 l ^ A l) :=
    hlowLocal.trans <| by
      simpa [A] using x3CoordinateProductsWhere_collect C (· < i)
        (fun h l => (-P.w h i i) * formula67Coefficient C ξ h l)
  have hhighLocal : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (i < ·) fun j =>
        D5.paperComm (C.x1 j ^ orderInt C.d j) ξ ^ (-P.w'' i i j))
      (orderedProductWhere (i < ·) fun j =>
        orderedProduct fun l => C.x3 l ^
          ((-P.w'' i i j) * formula67Coefficient C ξ j l)) := by
    apply modEq_orderedProductWhere
    intro j hij
    exact (formula67 C ξ j).zpow (-P.w'' i i j) |>.trans
      (x3CoordinateProduct_zpow C (formula67Coefficient C ξ j) (-P.w'' i i j))
  have hhigh : D5.ModEq (D5.gamma G 4)
      (orderedProductWhere (i < ·) fun j =>
        D5.paperComm (C.x1 j ^ orderInt C.d j) ξ ^ (-P.w'' i i j))
      (orderedProduct fun l => C.x3 l ^ B l) :=
    hhighLocal.trans <| by
      simpa [B] using x3CoordinateProductsWhere_collect C (i < ·)
        (fun j l => (-P.w'' i i j) * formula67Coefficient C ξ j l)
  have hcollectSA := x3CoordinateProduct_mul C
    (fun l => TaharaArithmetic.binom2 (C.d i) * S l) A
  have hcollectB := x3CoordinateProduct_mul C
    (fun l => TaharaArithmetic.binom2 (C.d i) * S l + A l) B
  have h := ((hsecond.mul hlow).mul hhigh).trans
    ((hcollectSA.mul (D5.ModEq.refl (D5.gamma G 4) _)).trans hcollectB)
  have hcoeff : ∀ l,
      TaharaArithmetic.binom2 (C.d i) * S l + A l + B l =
        formula75Coefficient C P ξ i l := by
    intro l
    dsimp [S, A, B, formula75Coefficient]
    simp_rw [formula67Coefficient]
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    ring
  simpa [formula74Word, hcoeff] using h

/-- Equality of two arbitrary integer coordinate words modulo `γ₄` implies
coordinatewise congruence modulo the cyclic orders. -/
theorem x3Coordinate_modEq_dvd
    (C : Context G) (a b : Fin C.r → ℤ)
    (hab : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun l => C.x3 l ^ a l)
      (orderedProduct fun l => C.x3 l ^ b l))
    (l : Fin C.r) : orderInt C.f l ∣ b l - a l := by
  have hdiv : (orderedProduct (fun k => C.x3 k ^ a k) /
      orderedProduct (fun k => C.x3 k ^ b k)) ∈ D5.gamma G 4 :=
    D5.modEq_iff_div_mem.mp hab
  have hinv : D5.ModEq (D5.gamma G 4)
      (orderedProduct (fun k => C.x3 k ^ b k))⁻¹
      (orderedProduct fun k => C.x3 k ^ (-b k)) := by
    simpa using x3CoordinateProduct_zpow C b (-1)
  have hdiff : D5.ModEq (D5.gamma G 4)
      (orderedProduct (fun k => C.x3 k ^ a k) /
        orderedProduct (fun k => C.x3 k ^ b k))
      (orderedProduct fun k => C.x3 k ^ (a k - b k)) := by
    rw [div_eq_mul_inv]
    exact ((D5.ModEq.refl (D5.gamma G 4)
      (orderedProduct fun k => C.x3 k ^ a k)).mul hinv).trans <| by
        simpa [sub_eq_add_neg] using x3CoordinateProduct_mul C a (fun k => -b k)
  have hmem : (orderedProduct fun k => C.x3 k ^ (a k - b k)) ∈
      D5.gamma G 4 :=
    D5.mem_of_modEq_of_le le_rfl hdiff.symm hdiv
  have hd := C.x3_coordinate_dvd_of_product_mem (fun k => a k - b k) hmem l
  have hneg := dvd_neg.mpr hd
  simpa [sub_eq_add_neg, add_comm] using hneg

/-- Formula (75), with explicit integer witnesses `qᵢₗ`. -/
theorem formula75
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) :
    ∃ q : Fin C.r → ℤ, ∀ l,
      Int.ModEq (orderInt C.f l) (formula75Coefficient C P ξ i l)
        (orderInt C.d i * q l) := by
  rcases formula74 C P hP ξ i with ⟨y, hy, h74⟩
  let q : Fin C.r → ℤ := fun l => (C.gammaThreeCoordinates y hy l).val
  have hycoord := C.gammaThreeCoordinates_spec y hy
  have hypow : D5.ModEq (D5.gamma G 4) (y ^ orderInt C.d i)
      (orderedProduct fun l => C.x3 l ^ (orderInt C.d i * q l)) :=
    (hycoord.zpow (orderInt C.d i)).trans <| by
      simpa [q] using x3CoordinateProduct_zpow C
        (fun l => (C.gammaThreeCoordinates y hy l).val) (orderInt C.d i)
  have hcoords := (formula74_coordinates C P ξ i).symm.trans
    (h74.trans hypow)
  refine ⟨q, fun l => ?_⟩
  rw [Int.modEq_iff_dvd]
  exact x3Coordinate_modEq_dvd C
    (formula75Coefficient C P ξ i)
    (fun l => orderInt C.d i * q l) hcoords l

/-- Reindex a lower-triangular double sum as an upper-triangular one. -/
theorem sum_lower_reindex
    {n : ℕ} (F : Fin n → Fin n → ℤ) :
    (∑ i, ∑ h ∈ Finset.univ.filter (· < i), F h i) =
      ∑ h, ∑ i ∈ Finset.univ.filter (h < ·), F h i := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]

/-- A weighted form of (75).  The unknown `q` disappears whenever the
weight absorbs the factor `d(i)` modulo `f(l)`. -/
theorem formula75_weighted_dvd
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (l : Fin C.r) (a : Fin C.s → ℤ)
    (ha : ∀ i, orderInt C.f l ∣ orderInt C.d i * a i) :
    orderInt C.f l ∣
      ∑ i, formula75Coefficient C P ξ i l * a i := by
  apply Finset.dvd_sum
  intro i hi
  rcases formula75 C P hP ξ i with ⟨q, hq⟩
  have hdiff := (hq l).dvd
  have hleft : orderInt C.f l ∣
      (orderInt C.d i * q l) * a i := by
    have := dvd_mul_of_dvd_left (ha i) (q l)
    convert this using 1 <;> ring
  have hright : orderInt C.f l ∣
      ((orderInt C.d i * q l) - formula75Coefficient C P ξ i l) * a i :=
    dvd_mul_of_dvd_left hdiff (a i)
  have hsub := Int.dvd_sub hleft hright
  convert hsub using 1 <;> ring

/-- The preceding weighted cancellation after weakening the coordinate
modulus to any divisor of `f(k)`. -/
theorem formula75_weighted_dvd_of_dvd
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (k : Fin C.r) (n : ℤ) (hn : n ∣ orderInt C.f k)
    (a : Fin C.s → ℤ) (ha : ∀ i, n ∣ orderInt C.d i * a i) :
    n ∣ ∑ i, formula75Coefficient C P ξ i k * a i := by
  apply Finset.dvd_sum
  intro i hi
  rcases formula75 C P hP ξ i with ⟨q, hq⟩
  have hdiff : n ∣
      (orderInt C.d i * q k) - formula75Coefficient C P ξ i k :=
    dvd_trans hn (hq k).dvd
  have hleft : n ∣ (orderInt C.d i * q k) * a i := by
    have := dvd_mul_of_dvd_left (ha i) (q k)
    convert this using 1 <;> ring
  have hright : n ∣
      ((orderInt C.d i * q k) - formula75Coefficient C P ξ i k) * a i :=
    dvd_mul_of_dvd_left hdiff (a i)
  have hsub := Int.dvd_sub hleft hright
  convert hsub using 1 <;> ring

/-- Expansion of a weighted sum of formula-(75) coefficients. -/
theorem formula75_weighted_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (k : Fin C.r) (a : Fin C.s → ℤ) :
    (∑ i, formula75Coefficient C P ξ i k * a i) =
      (∑ i, TaharaArithmetic.binom2 (C.d i) *
        (∑ p, P.v i p * lambda C ξ p k) * a i) -
      (∑ i : Fin C.s, ∑ j ∈ Finset.univ.filter (i < ·),
        (P.w i j j * (∑ p, C.b i p * lambda C ξ p k) * a j +
          P.w'' i i j * (∑ p, C.b j p * lambda C ξ p k) * a i)) := by
  let V : Fin C.s → ℤ := fun i => ∑ p, P.v i p * lambda C ξ p k
  let B : Fin C.s → ℤ := fun i => formula67Coefficient C ξ i k
  have hreindex := sum_lower_reindex
    (fun h i => P.w h i i * B h * a i)
  simp_rw [formula75Coefficient, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  change
    (∑ i, TaharaArithmetic.binom2 (C.d i) * V i * a i) -
        (∑ i, ∑ h ∈ Finset.univ.filter (· < i),
          P.w h i i * B h * a i) -
        (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
          P.w'' i i j * B j * a i) = _
  rw [hreindex]
  simp_rw [Finset.sum_add_distrib]
  dsimp [V, B]
  simp_rw [formula67Coefficient]
  ring

def formula76Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l : Fin C.r) : ℤ :=
  ∑ i, TaharaArithmetic.binom2 (C.d i) * eta C ξ i l *
    (∑ p, P.v i p * lambda C ξ p l)

def formula76Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l : Fin C.r) : ℤ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    (P.w i j j * (∑ p, C.b i p * lambda C ξ p l) * eta C ξ j l +
      P.w'' i i j * (∑ p, C.b j p * lambda C ξ p l) * eta C ξ i l)

/-- The exact finite-sum reindexing underlying formula (76). -/
theorem formula76_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l : Fin C.r) :
    (∑ i, formula75Coefficient C P ξ i l * eta C ξ i l) =
      formula76Left C P ξ l - formula76Right C P ξ l := by
  let V : Fin C.s → ℤ := fun i => ∑ p, P.v i p * lambda C ξ p l
  let B : Fin C.s → ℤ := fun i => formula67Coefficient C ξ i l
  have hreindex := sum_lower_reindex
    (fun h i => P.w h i i * B h * eta C ξ i l)
  rw [formula76Left, formula76Right]
  simp_rw [formula75Coefficient, sub_mul, Finset.sum_sub_distrib,
    Finset.sum_mul]
  change
    (∑ i, TaharaArithmetic.binom2 (C.d i) * V i * eta C ξ i l) -
        (∑ i, ∑ h ∈ Finset.univ.filter (· < i),
          P.w h i i * B h * eta C ξ i l) -
        (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
          P.w'' i i j * B j * eta C ξ i l) = _
  rw [hreindex]
  simp_rw [Finset.sum_add_distrib]
  have hmain :
      (∑ i, TaharaArithmetic.binom2 (C.d i) * V i * eta C ξ i l) =
        ∑ i, TaharaArithmetic.binom2 (C.d i) * eta C ξ i l *
          (∑ p, P.v i p * lambda C ξ p l) := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp [V]
    ring
  have hlow :
      (∑ h, ∑ j ∈ Finset.univ.filter (h < ·),
        P.w h j j * B h * eta C ξ j l) =
      ∑ h, ∑ j ∈ Finset.univ.filter (h < ·),
        P.w h j j * formula67Coefficient C ξ h l * eta C ξ j l := by
    simp [B]
  have hhigh :
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        P.w'' i i j * B j * eta C ξ i l) =
      ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        P.w'' i i j * formula67Coefficient C ξ j l * eta C ξ i l := by
    simp [B]
  rw [hmain, hlow, hhigh]
  simp_rw [formula67Coefficient]
  ring

/-- Formula (76). -/
theorem formula76
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (l : Fin C.r) :
    Int.ModEq (orderInt C.f l)
      (formula76Left C P ξ l) (formula76Right C P ξ l) := by
  have hdvd := formula75_weighted_dvd C P hP ξ l
    (fun i => eta C ξ i l) (fun i => formula66_eta C ξ i l)
  rw [formula76_expansion C P ξ l] at hdvd
  rw [Int.modEq_iff_dvd]
  have hneg := dvd_neg.mpr hdvd
  convert hneg using 1 <;> ring

def formula77Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) : ℤ :=
  ∑ i, TaharaArithmetic.binom2 (C.d i) *
    (eta C ξ i l * (∑ p, P.v i p * lambda C ξ p m) +
      eta C ξ i m * (∑ p, P.v i p * lambda C ξ p l))

def formula77Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) : ℤ :=
  (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    P.w i j j *
      ((∑ p, C.b i p * lambda C ξ p l) * eta C ξ j m +
        (∑ p, C.b i p * lambda C ξ p m) * eta C ξ j l)) +
  (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    P.w'' i i j *
      ((∑ p, C.b j p * lambda C ξ p l) * eta C ξ i m +
        (∑ p, C.b j p * lambda C ξ p m) * eta C ξ i l))

/-- The exact two-coordinate expansion used in formula (77). -/
theorem formula77_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) :
    (∑ i, (formula75Coefficient C P ξ i l * eta C ξ i m +
      formula75Coefficient C P ξ i m * eta C ξ i l)) =
      formula77Left C P ξ l m - formula77Right C P ξ l m := by
  have hl := formula75_weighted_expansion C P ξ l (fun i => eta C ξ i m)
  have hm := formula75_weighted_expansion C P ξ m (fun i => eta C ξ i l)
  have hmain :
      (∑ i, TaharaArithmetic.binom2 (C.d i) *
          (∑ p, P.v i p * lambda C ξ p l) * eta C ξ i m) +
        (∑ i, TaharaArithmetic.binom2 (C.d i) *
          (∑ p, P.v i p * lambda C ξ p m) * eta C ξ i l) =
      formula77Left C P ξ l m := by
    rw [formula77Left, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hright :
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        (P.w i j j * formula67Coefficient C ξ i l * eta C ξ j m +
          P.w'' i i j * formula67Coefficient C ξ j l * eta C ξ i m)) +
      (∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
        (P.w i j j * formula67Coefficient C ξ i m * eta C ξ j l +
          P.w'' i i j * formula67Coefficient C ξ j m * eta C ξ i l)) =
      formula77Right C P ξ l m := by
    have hsplit : ∀ F H : Fin C.s → Fin C.s → ℤ,
        (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), (F i j + H i j)) =
          (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), F i j) +
            ∑ i, ∑ j ∈ Finset.univ.filter (i < ·), H i j := by
      intro F H
      simp_rw [Finset.sum_add_distrib]
    rw [formula77Right]
    rw [hsplit, hsplit]
    simp_rw [mul_add]
    rw [hsplit, hsplit]
    simp_rw [formula67Coefficient]
    ring
  rw [Finset.sum_add_distrib, hl, hm]
  rw [← hmain, ← hright]
  simp_rw [formula67Coefficient]
  ring

/-- Formula (77). -/
theorem formula77
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {l m : Fin C.r} (hlm : l < m) :
    Int.ModEq (orderInt C.f l)
      (formula77Left C P ξ l m) (formula77Right C P ξ l m) := by
  have hfm : orderInt C.f l ∣ orderInt C.f m := by
    rcases C.f_dvd l m hlm.le with ⟨z, hz⟩
    refine ⟨(z : ℤ), ?_⟩
    change (C.f m : ℤ) = (C.f l : ℤ) * (z : ℤ)
    exact_mod_cast hz
  have hl : orderInt C.f l ∣
      ∑ i, formula75Coefficient C P ξ i l * eta C ξ i m :=
    formula75_weighted_dvd_of_dvd C P hP ξ l (orderInt C.f l)
      dvd_rfl (fun i => eta C ξ i m) (fun i =>
        dvd_trans hfm (formula66_eta C ξ i m))
  have hm : orderInt C.f l ∣
      ∑ i, formula75Coefficient C P ξ i m * eta C ξ i l :=
    formula75_weighted_dvd_of_dvd C P hP ξ m (orderInt C.f l)
      hfm (fun i => eta C ξ i l) (fun i => formula66_eta C ξ i l)
  have hsum : orderInt C.f l ∣
      ∑ i, (formula75Coefficient C P ξ i l * eta C ξ i m +
        formula75Coefficient C P ξ i m * eta C ξ i l) := by
    rw [Finset.sum_add_distrib]
    exact dvd_add hl hm
  rw [formula77_expansion C P ξ l m] at hsum
  rw [Int.modEq_iff_dvd]
  have hneg := dvd_neg.mpr hsum
  convert hneg using 1 <;> ring

end

end D5.Tahara
