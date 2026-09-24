import D5.Section22

/-!
# Section 23: expansion of `κ` in the commutators `[yₐ,y_b]`

This file proves formulas (85)--(87).  All products remain finite and all
reindexing and exponent collection is performed explicitly.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Bilinearity in the second argument for a finite product of weight-two
elements, modulo `γ₆`. -/
theorem paperComm_orderedProduct_right_gammaTwo_mod_gamma_six
    {a : G} (ha : a ∈ D5.gamma G 2)
    {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm a (orderedProduct f))
      (orderedProduct fun i => D5.paperComm a (f i)) := by
  unfold orderedProduct
  induction List.finRange n with
  | nil => simpa [D5.paperComm_eq] using
      D5.ModEq.refl (D5.gamma G 6) (1 : G)
  | cons i is ih =>
      simp only [List.map_cons, List.prod_cons]
      have hi : f i ∈ D5.gamma G 2 := hf i
      have htail : (is.map f).prod ∈ D5.gamma G 2 :=
        listProd_mem (D5.gamma G 2) (is.map f) fun x hx => by
          rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
          exact hf j
      exact (formula56_mul_right ha hi htail).trans <|
        (D5.ModEq.refl (D5.gamma G 6) (D5.paperComm a (f i))).mul ih

/-- Expand the commutator of two coordinate words into the full square of
coordinate commutators. -/
theorem paperComm_coordinateProducts
    (B : GammaTwoFourBasis G) (A E : Fin B.n → ℤ) :
    D5.ModGammaSix
      (D5.paperComm
        (orderedProduct fun a => B.y a ^ A a)
        (orderedProduct fun b => B.y b ^ E b))
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (B.y a) (B.y b) ^ (A a * E b)) := by
  let X : Fin B.n → G := fun a => B.y a ^ A a
  let Y : Fin B.n → G := fun b => B.y b ^ E b
  have hX : ∀ a, X a ∈ D5.gamma G 2 := fun a =>
    (D5.gamma G 2).zpow_mem (B.basis.1 a) _
  have hY : ∀ b, Y b ∈ D5.gamma G 2 := fun b =>
    (D5.gamma G 2).zpow_mem (B.basis.1 b) _
  have hYprod : orderedProduct Y ∈ D5.gamma G 2 := by
    apply orderedProduct_mem
    exact hY
  have hleft := paperComm_orderedProduct_mod_gamma_six
    (r := 2) (s := 2) (by norm_num) (by norm_num) (by norm_num)
    X hX hYprod
  have hright : D5.ModGammaSix
      (orderedProduct fun a => D5.paperComm (X a) (orderedProduct Y))
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (X a) (Y b)) := by
    apply modEq_orderedProduct
    intro a
    exact paperComm_orderedProduct_right_gammaTwo_mod_gamma_six
      (hX a) Y hY
  have hpowers : D5.ModGammaSix
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (X a) (Y b))
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (B.y a) (B.y b) ^ (A a * E b)) := by
    apply modEq_orderedProduct
    intro a
    apply modEq_orderedProduct
    intro b
    exact formula56_zpow (B.basis.1 a) (B.basis.1 b) (A a) (E b)
  simpa [X, Y] using hleft.trans (hright.trans hpowers)

/-- Distribute one more integer power through the coordinate expansion. -/
theorem paperComm_coordinateProducts_zpow
    (B : GammaTwoFourBasis G) (A E : Fin B.n → ℤ) (z : ℤ) :
    D5.ModGammaSix
      (D5.paperComm
        (orderedProduct fun a => B.y a ^ A a)
        (orderedProduct fun b => B.y b ^ E b) ^ z)
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (B.y a) (B.y b) ^ (z * (A a * E b))) := by
  let K : Fin B.n → Fin B.n → G := fun a b =>
    D5.paperComm (B.y a) (B.y b)
  let F : Fin B.n → Fin B.n → G := fun a b => K a b ^ (A a * E b)
  have hK : ∀ a b, K a b ∈ D5.gamma G 4 := by
    intro a b
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (B.basis.1 a) (B.basis.1 b)
  have hF : ∀ a b, F a b ∈ D5.gamma G 3 := by
    intro a b
    exact (D5.gamma G 3).zpow_mem
      (D5.gamma_antitone G (by norm_num) (hK a b)) _
  have hbase := (paperComm_coordinateProducts B A E).zpow z
  have houter := D5.orderedProduct_zpow_gammaThree
    (fun a => orderedProduct fun b => F a b)
    (fun a => by
      apply orderedProduct_mem
      intro b
      exact hF a b) z
  have hinner : D5.ModGammaSix
      (orderedProduct fun a => (orderedProduct fun b => F a b) ^ z)
      (orderedProduct fun a => orderedProduct fun b => (F a b) ^ z) := by
    apply modEq_orderedProduct
    intro a
    exact D5.orderedProduct_zpow_gammaThree (F a) (hF a) z
  have hnormalize : D5.ModGammaSix
      (orderedProduct fun a => orderedProduct fun b => (F a b) ^ z)
      (orderedProduct fun a => orderedProduct fun b =>
        K a b ^ (z * (A a * E b))) := by
    apply modEq_orderedProduct
    intro a
    apply modEq_orderedProduct
    intro b
    have heq : (F a b) ^ z = K a b ^ (z * (A a * E b)) := by
      calc
        (F a b) ^ z = K a b ^ ((A a * E b) * z) := by
          exact (zpow_mul (K a b) (A a * E b) z).symm
        _ = K a b ^ (z * (A a * E b)) := by
          congr 1
          ring
    rw [heq]
  simpa [F, K] using hbase.trans (houter.trans (hinner.trans hnormalize))

/-- Reorder and collect a family of square coordinate blocks indexed by a
strict pair. -/
theorem strictPairProduct_coordinateSquares_collect
    {s n : ℕ} (z : Fin n → Fin n → G)
    (hz : ∀ a b, z a b ∈ D5.gamma G 3)
    (e : Fin s → Fin s → Fin n → Fin n → ℤ) :
    D5.ModGammaSix
      (strictPairProduct fun i j =>
        orderedProduct fun a => orderedProduct fun b => z a b ^ e i j a b)
      (orderedProduct fun a => orderedProduct fun b => z a b ^
        (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), e i j a b)) := by
  let F : Fin s → Fin s → Fin n → Fin n → G := fun i j a b =>
    z a b ^ e i j a b
  have hF : ∀ i j a b, F i j a b ∈ D5.gamma G 3 := fun i j a b =>
    (D5.gamma G 3).zpow_mem (hz a b) _
  have hrow : ∀ i, D5.ModGammaSix
      (orderedProductWhere (i < ·) fun j =>
        orderedProduct fun a => orderedProduct fun b => F i j a b)
      (orderedProduct fun a => orderedProduct fun b =>
        orderedProductWhere (i < ·) fun j => F i j a b) := by
    intro i
    have hJA := D5.orderedProductWhere_orderedProduct_swap_gammaThree
      (i < ·) (fun j a => orderedProduct fun b => F i j a b)
      (fun j hij a => by
        apply orderedProduct_mem
        intro b
        exact hF i j a b)
    refine hJA.trans ?_
    apply modEq_orderedProduct
    intro a
    exact D5.orderedProductWhere_orderedProduct_swap_gammaThree
      (i < ·) (fun j b => F i j a b)
      (fun j hij b => hF i j a b)
  have hrows : D5.ModGammaSix
      (strictPairProduct fun i j =>
        orderedProduct fun a => orderedProduct fun b => F i j a b)
      (orderedProduct fun i => orderedProduct fun a => orderedProduct fun b =>
        orderedProductWhere (i < ·) fun j => F i j a b) := by
    unfold strictPairProduct
    apply modEq_orderedProduct
    exact hrow
  have hIA := D5.orderedProduct_orderedProduct_swap_gammaThree
    (fun i a => orderedProduct fun b =>
      orderedProductWhere (i < ·) fun j => F i j a b)
    (fun i a => by
      apply orderedProduct_mem
      intro b
      apply orderedProductWhere_mem
      intro j hij
      exact hF i j a b)
  have hIB : D5.ModGammaSix
      (orderedProduct fun a => orderedProduct fun i => orderedProduct fun b =>
        orderedProductWhere (i < ·) fun j => F i j a b)
      (orderedProduct fun a => orderedProduct fun b => orderedProduct fun i =>
        orderedProductWhere (i < ·) fun j => F i j a b) := by
    apply modEq_orderedProduct
    intro a
    exact D5.orderedProduct_orderedProduct_swap_gammaThree
      (fun i b => orderedProductWhere (i < ·) fun j => F i j a b)
      (fun i b => by
        apply orderedProductWhere_mem
        intro j hij
        exact hF i j a b)
  have hcollect :
      (orderedProduct fun a => orderedProduct fun b => orderedProduct fun i =>
        orderedProductWhere (i < ·) fun j => F i j a b) =
      (orderedProduct fun a => orderedProduct fun b => z a b ^
        (∑ i, ∑ j ∈ Finset.univ.filter (i < ·), e i j a b)) := by
    apply congrArg orderedProduct
    funext a
    apply congrArg orderedProduct
    funext b
    simp_rw [F, D5.orderedProductWhere_zpow_same_base]
    exact D5.orderedProduct_zpow_same_base (z a b)
      (fun i => ∑ j ∈ Finset.univ.filter (i < ·), e i j a b)
  simpa [F, hcollect] using hrows.trans (hIA.trans hIB)

/-- The coordinate word representing `[x₁ᵢ,ξ]` in formula (81). -/
def formula85CoordinateWord
    (C : Context G) (B : GammaTwoFourBasis G) (ξ : G)
    (i : Fin C.s) : G :=
  orderedProduct fun a => B.y a ^ rCoord C B ξ i a

def formula85FirstProduct
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    D5.paperComm (formula85CoordinateWord C B ξ i)
      (formula85CoordinateWord C B ξ j) ^
        (P.u i j * orderInt C.d j)

def formula85RawExponent
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    (P.u i j * orderInt C.d j) *
      (rCoord C B ξ i a * rCoord C B ξ j b)

def formula85Exponent
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    P.u i j * orderInt C.d j *
      (rCoord C B ξ i a * rCoord C B ξ j b -
        rCoord C B ξ i b * rCoord C B ξ j a)

def formula85Right
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun a b =>
    D5.paperComm (B.y a) (B.y b) ^ formula85Exponent C B P ξ a b

theorem formula85_raw_sub
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) (a b : Fin B.n) :
    formula85RawExponent C B P ξ a b -
      formula85RawExponent C B P ξ b a =
        formula85Exponent C B P ξ a b := by
  unfold formula85RawExponent formula85Exponent
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem formula85_first
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (kappa C P ξ) (formula85FirstProduct C B P ξ) := by
  have hword : ∀ i, formula85CoordinateWord C B ξ i ∈ D5.gamma G 2 := by
    intro i
    unfold formula85CoordinateWord
    apply orderedProduct_mem
    intro a
    exact (D5.gamma G 2).zpow_mem (B.basis.1 a) _
  have hreplace : D5.ModGammaSix
      (formula59FirstProduct C P ξ) (formula85FirstProduct C B P ξ) := by
    unfold formula59FirstProduct formula85FirstProduct strictPairProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    have hAj := formula81_first_mem_gamma2 C ξ j
    have hl := formula56_replace_left (formula81_first C B ξ i) hAj
    have hr := formula56_replace_right (formula81_first C B ξ j)
      (hword i)
    exact (hl.trans hr).zpow (P.u i j * orderInt C.d j)
  exact (formula60 C P hP ξ).trans hreplace

theorem formula85_second
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula85FirstProduct C B P ξ)
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (B.y a) (B.y b) ^
          formula85RawExponent C B P ξ a b) := by
  let K : Fin B.n → Fin B.n → G := fun a b =>
    D5.paperComm (B.y a) (B.y b)
  let e : Fin C.s → Fin C.s → Fin B.n → Fin B.n → ℤ :=
    fun i j a b => (P.u i j * orderInt C.d j) *
      (rCoord C B ξ i a * rCoord C B ξ j b)
  have hlocal : D5.ModGammaSix (formula85FirstProduct C B P ξ)
      (strictPairProduct fun i j =>
        orderedProduct fun a => orderedProduct fun b => K a b ^ e i j a b) := by
    unfold formula85FirstProduct strictPairProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    simpa [formula85CoordinateWord, K, e] using
      paperComm_coordinateProducts_zpow B
        (rCoord C B ξ i) (rCoord C B ξ j)
        (P.u i j * orderInt C.d j)
  have hK : ∀ a b, K a b ∈ D5.gamma G 3 := by
    intro a b
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (B.basis.1 a) (B.basis.1 b)
  have hcollect := strictPairProduct_coordinateSquares_collect K hK e
  simpa [K, e, formula85RawExponent] using hlocal.trans hcollect

theorem formula85_square_to_pairs
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (B.y a) (B.y b) ^
          formula85RawExponent C B P ξ a b)
      (formula85Right C B P ξ) := by
  let K : Fin B.n → Fin B.n → G := fun a b =>
    D5.paperComm (B.y a) (B.y b)
  let F : Fin B.n → Fin B.n → G := fun a b =>
    K a b ^ formula85RawExponent C B P ξ a b
  have hF : ∀ a b, F a b ∈ D5.gamma G 3 := by
    intro a b
    apply (D5.gamma G 3).zpow_mem
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (B.basis.1 a) (B.basis.1 b)
  have hpartition := orderedProduct_square_partition_gammaThree F hF
  have hdiag : D5.ModGammaSix (orderedProduct fun a => F a a) 1 := by
    have hpoint : D5.ModGammaSix (orderedProduct fun a => F a a)
        (orderedProduct fun _a : Fin B.n => (1 : G)) := by
      apply modEq_orderedProduct
      intro a
      simpa [F, K, D5.paperComm_eq] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)
    exact hpoint.trans <| by
      simpa [orderedProduct] using D5.ModEq.refl (D5.gamma G 6) (1 : G)
  have hpairs : D5.ModGammaSix
      (strictPairProduct F * strictPairProduct fun a b => F b a)
      (formula85Right C B P ξ) := by
    have hcombine := strictPairProduct_pointwise_gammaThree F
      (fun a b => F b a) (fun a b hab => hF a b)
      (fun a b hab => hF b a)
    refine hcombine.trans ?_
    unfold strictPairProduct formula85Right
    apply modEq_orderedProduct
    intro a
    apply modEq_orderedProductWhere
    intro b hab
    have heq : F a b * F b a =
        D5.paperComm (B.y a) (B.y b) ^
          formula85Exponent C B P ξ a b := by
      dsimp [F, K]
      rw [D5.paperComm_swap (B.y a) (B.y b), inv_zpow,
        ← zpow_neg, ← zpow_add, ← sub_eq_add_neg,
        formula85_raw_sub]
    change D5.ModGammaSix (F a b * F b a)
      (D5.paperComm (B.y a) (B.y b) ^
        formula85Exponent C B P ξ a b)
    rw [heq]
  simpa [F, K, formula85Right] using hpartition.trans (hdiag.mul hpairs)

/-- Formula (85). -/
theorem formula85
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (kappa C P ξ) (formula85Right C B P ξ) :=
  (formula85_first C B P hP ξ).trans <|
    (formula85_second C B P ξ).trans
      (formula85_square_to_pairs C B P ξ)

/-- Formula (86). -/
theorem formula86
    (B : GammaTwoFourBasis G) (a b : Fin B.n) :
    D5.ModGammaSix
      (D5.paperComm (B.y a) (B.y b) ^ orderInt B.order a) 1 := by
  have htransfer := D5.paperComm_zpow_left_mod_gamma_six
    (B.basis.1 a) (B.basis.1 b) (orderInt B.order a)
  have hzero : D5.ModGammaSix
      (D5.paperComm (B.y a ^ orderInt B.order a) (B.y b)) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (B.y_order_power a) (B.basis.1 b)
  exact htransfer.symm.trans hzero

/-- The second line of formula (87), after collecting the coefficient of
`r(i,a)`. -/
def formula87First
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ i, rCoord C B ξ i a *
    ((∑ j ∈ Finset.univ.filter (i < ·),
        P.u i j * orderInt C.d j * rCoord C B ξ j b) -
      (∑ h ∈ Finset.univ.filter (· < i),
        P.u h i * orderInt C.d i * rCoord C B ξ h b))

/-- The third line of formula (87). -/
def formula87Second
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  -∑ i, orderInt C.d i * rCoord C B ξ i a *
    (∑ m, formula69Coefficient C P ξ i m * sCoord C B m b)

/-- The last line of formula (87). -/
def formula87Third
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  -∑ l, ∑ m,
    sCoord C B l a * sCoord C B m b *
      (∑ i, formula68Coefficient C ξ i l *
        formula69Coefficient C P ξ i m)

/-- The first passage in (87) is an exact equality of integers. -/
theorem formula87_start
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) :
    formula85Exponent C B P ξ a b = formula87First C B P ξ a b := by
  have hreindex := sum_lower_reindex
    (fun h i => rCoord C B ξ i a *
      (P.u h i * orderInt C.d i * rCoord C B ξ h b))
  rw [formula85Exponent, formula87First]
  simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [hreindex]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- Algebraic form of the first congruence in (87): its difference is a
linear combination of the coefficients in (84). -/
theorem formula87_first_difference
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) :
    formula87Second C B P ξ a b - formula87First C B P ξ a b =
      -∑ i, rCoord C B ξ i a * formula84Coefficient C B P ξ i b := by
  rw [formula87Second, formula87First]
  unfold formula84Coefficient formula69Coefficient
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ring

/-- First congruence in (87), weakened from modulus `n(b)` to `n(a)` by
the invariant-factor divisibility `n(a) ∣ n(b)`. -/
theorem formula87_first_congruence
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G)
    {a b : Fin B.n} (hab : a < b) :
    Int.ModEq (orderInt B.order a)
      (formula87First C B P ξ a b) (formula87Second C B P ξ a b) := by
  rw [Int.modEq_iff_dvd, formula87_first_difference]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro i hi
  have hnab : orderInt B.order a ∣ orderInt B.order b := by
    rcases B.order_dvd a b hab.le with ⟨q, hq⟩
    refine ⟨(q : ℤ), ?_⟩
    change (B.order b : ℤ) = (B.order a : ℤ) * (q : ℤ)
    exact_mod_cast hq
  have hcoeff : orderInt B.order a ∣
      formula84Coefficient C B P ξ i b := by
    have hb := (formula84 C B P hP ξ i b).dvd
    have hb' : orderInt B.order b ∣
        -formula84Coefficient C B P ξ i b := by
      simpa only [zero_sub] using hb
    exact dvd_trans hnab (dvd_neg.mp hb')
  exact dvd_mul_of_dvd_right hcoeff (rCoord C B ξ i a)

/-- Algebraic form of the second congruence in (87).  The reindexing is
the finite distributive law used earlier in formula (70). -/
theorem formula87_second_difference
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) :
    formula87Third C B P ξ a b - formula87Second C B P ξ a b =
      -∑ i,
        (∑ m, formula69Coefficient C P ξ i m * sCoord C B m b) *
          ((∑ l, formula68Coefficient C ξ i l * sCoord C B l a) -
            orderInt C.d i * rCoord C B ξ i a) := by
  have hreindex := sum_product_reindex
    (fun i l => formula68Coefficient C ξ i l)
    (fun i m => formula69Coefficient C P ξ i m)
    (fun l => sCoord C B l a) (fun m => sCoord C B m b)
  have hdouble :
      (∑ l, ∑ m,
        sCoord C B l a * sCoord C B m b *
          (∑ i, formula68Coefficient C ξ i l *
            formula69Coefficient C P ξ i m)) =
      ∑ i,
        (∑ l, formula68Coefficient C ξ i l * sCoord C B l a) *
          (∑ m, formula69Coefficient C P ξ i m * sCoord C B m b) := by
    calc
      _ = ∑ l, ∑ m,
          (∑ i, formula68Coefficient C ξ i l *
            formula69Coefficient C P ξ i m) *
              (sCoord C B l a * sCoord C B m b) := by
            apply Finset.sum_congr rfl
            intro l hl
            apply Finset.sum_congr rfl
            intro m hm
            ring
      _ = _ := hreindex.symm
  rw [formula87Third, formula87Second]
  rw [hdouble]
  simp only [mul_sub, Finset.sum_sub_distrib]
  simp only [mul_assoc, mul_comm]
  ring

/-- Second congruence in (87), obtained coordinatewise from formula (83). -/
theorem formula87_second_congruence
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) :
    Int.ModEq (orderInt B.order a)
      (formula87Second C B P ξ a b) (formula87Third C B P ξ a b) := by
  rw [Int.modEq_iff_dvd, formula87_second_difference]
  apply dvd_neg.mpr
  apply Finset.dvd_sum
  intro i hi
  have hcoord := (formula83 C B ξ i a).dvd
  exact dvd_mul_of_dvd_right hcoord
    (∑ m, formula69Coefficient C P ξ i m * sCoord C B m b)

/-- Formula (87), retaining the exact first equality and both modular
comparisons as separate components. -/
theorem formula87
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G)
    {a b : Fin B.n} (hab : a < b) :
    formula85Exponent C B P ξ a b = formula87First C B P ξ a b ∧
      Int.ModEq (orderInt B.order a)
        (formula87First C B P ξ a b) (formula87Second C B P ξ a b) ∧
      Int.ModEq (orderInt B.order a)
        (formula87Second C B P ξ a b) (formula87Third C B P ξ a b) :=
  ⟨formula87_start C B P ξ a b,
    formula87_first_congruence C B P hP ξ hab,
    formula87_second_congruence C B P ξ a b⟩

end

end D5.Tahara
