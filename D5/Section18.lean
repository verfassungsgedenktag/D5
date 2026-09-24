import D5.Section17

/-!
# Section 18: coordinates in `γ₃ / γ₄`

The coordinates `λ` and `η` are chosen from the cyclic basis already stored
in `Context`.  They are therefore actual coordinates relative to the
original generators `x₃`, as required in formulas (64)--(69).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

namespace Context

/-- Canonical coordinates supplied by the unique normal form in
`γ₃ / γ₄`. -/
noncomputable def gammaThreeCoordinates
    (C : Context G) (y : G) (hy : y ∈ D5.gamma G 3) :
    ∀ l, Fin (C.f l) :=
  Classical.choose (C.basis3.2.2.2 y hy)

theorem gammaThreeCoordinates_spec
    (C : Context G) (y : G) (hy : y ∈ D5.gamma G 3) :
    D5.ModEq (D5.gamma G 4) y
      (orderedProduct fun l =>
        C.x3 l ^ (C.gammaThreeCoordinates y hy l).val) :=
  (Classical.choose_spec (C.basis3.2.2.2 y hy)).1

/-- If an integer-coordinate word in the chosen `x₃` generators lies in
`γ₄`, each coordinate is divisible by its cyclic order. -/
theorem x3_coordinate_dvd_of_product_mem
    (C : Context G) (a : Fin C.r → ℤ)
    (ha : orderedProduct (fun l => C.x3 l ^ a l) ∈ D5.gamma G 4)
    (l : Fin C.r) : orderInt C.f l ∣ a l := by
  let rem : ∀ k, Fin (C.f k) := fun k =>
    ⟨Int.natMod (a k) (orderInt C.f k),
      Int.natMod_lt (Nat.ne_of_gt (lt_trans Nat.zero_lt_one (C.f_gt_one k)))⟩
  let zero : ∀ k, Fin (C.f k) := fun k =>
    ⟨0, lt_trans Nat.zero_lt_one (C.f_gt_one k)⟩
  have hreduce : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun k => C.x3 k ^ a k)
      (orderedProduct fun k => C.x3 k ^ (rem k).val) := by
    apply modEq_orderedProduct
    intro k
    let f : ℤ := orderInt C.f k
    let q : ℤ := a k / f
    have hf : f ≠ 0 := by
      dsimp [f, orderInt]
      exact_mod_cast Nat.ne_of_gt (lt_trans Nat.zero_lt_one (C.f_gt_one k))
    have haeq : a k = f * q + a k % f := by
      simpa [q] using (Int.mul_ediv_add_emod (a k) f).symm
    have hrem : ((rem k).val : ℤ) = a k % f := by
      dsimp [rem, Int.natMod]
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ hf)
    have hperiod : D5.ModEq (D5.gamma G 4)
        ((C.x3 k ^ f) ^ q) 1 := by
      apply D5.modEq_one_iff_mem.mpr
      exact (D5.gamma G 4).zpow_mem (by simpa [f] using C.x3_order_power k) q
    rw [haeq, zpow_add, zpow_mul]
    rw [← zpow_natCast, hrem]
    simpa using hperiod.mul
      (D5.ModEq.refl (D5.gamma G 4) (C.x3 k ^ (a k % f)))
  have hres : D5.ModEq (D5.gamma G 4) 1
      (orderedProduct fun k => C.x3 k ^ (rem k).val) :=
    (D5.modEq_one_iff_mem.mpr ha).symm.trans hreduce
  have hzero : D5.ModEq (D5.gamma G 4) 1
      (orderedProduct fun k => C.x3 k ^ (zero k).val) := by
    simpa [orderedProduct, zero] using
      D5.ModEq.refl (D5.gamma G 4) (1 : G)
  obtain ⟨normal, hnormal, hunique⟩ :=
    C.basis3.2.2.2 (1 : G) (by simp)
  have hremEq : rem = normal := hunique rem hres
  have hzeroEq : zero = normal := hunique zero hzero
  have hcoord : rem l = zero l := by rw [hremEq, hzeroEq]
  have hmod : a l % orderInt C.f l = 0 := by
    have hv := congrArg (fun z => (z.val : ℤ)) hcoord
    dsimp [rem, zero, Int.natMod] at hv
    have hf : orderInt C.f l ≠ 0 := by
      dsimp [orderInt]
      exact_mod_cast Nat.ne_of_gt (lt_trans Nat.zero_lt_one (C.f_gt_one l))
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hf)] at hv
    exact hv
  exact Int.dvd_iff_emod_eq_zero.mpr hmod

end Context

theorem lambdaArgument_mem_gamma3
    (C : Context G) (ξ : G) (p : Fin C.t) :
    D5.paperComm (C.x2 p) ξ ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact D5.paperComm_mem_gamma_add (r := 2) (s := 1)
    (by norm_num) (by norm_num) (C.x2_mem_gamma2 p) hξ

theorem etaArgument_mem_gamma3
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i) ∈
      D5.gamma G 3 := by
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact D5.paperComm_mem_gamma_add (r := 2) (s := 1)
    (by norm_num) (by norm_num)
    (D5.paperComm_mem_gamma_add (r := 1) (s := 1)
      (by norm_num) (by norm_num) hi hξ) hi

def lambda
    (C : Context G) (ξ : G) (p : Fin C.t) (l : Fin C.r) : ℤ :=
  (C.gammaThreeCoordinates
    (D5.paperComm (C.x2 p) ξ)
    (lambdaArgument_mem_gamma3 C ξ p) l).val

def eta
    (C : Context G) (ξ : G) (i : Fin C.s) (l : Fin C.r) : ℤ :=
  (C.gammaThreeCoordinates
    (D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i))
    (etaArgument_mem_gamma3 C ξ i) l).val

/-- Formula (64). -/
theorem formula64
    (C : Context G) (ξ : G) (p : Fin C.t) :
    D5.ModEq (D5.gamma G 4) (D5.paperComm (C.x2 p) ξ)
      (orderedProduct fun l => C.x3 l ^ lambda C ξ p l) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hmem : D5.paperComm (C.x2 p) ξ ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (C.x2_mem_gamma2 p) hξ
  simpa [lambda] using C.gammaThreeCoordinates_spec
    (D5.paperComm (C.x2 p) ξ) hmem

/-- Formula (65). -/
theorem formula65
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i))
      (orderedProduct fun l => C.x3 l ^ eta C ξ i l) := by
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hmem : D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i) ∈
      D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hi hξ) hi
  simpa [eta] using C.gammaThreeCoordinates_spec
    (D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i)) hmem

/-- Integer powers of an `x₃` coordinate word are taken coordinatewise
modulo `γ₄`. -/
theorem x3CoordinateProduct_zpow
    (C : Context G) (a : Fin C.r → ℤ) (z : ℤ) :
    D5.ModEq (D5.gamma G 4)
      ((orderedProduct fun l => C.x3 l ^ a l) ^ z)
      (orderedProduct fun l => C.x3 l ^ (z * a l)) := by
  have h := D5.orderedProduct_zpow_gammaThree
    (fun l => C.x3 l ^ a l)
    (fun l => (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _) z
  have h4 := h.mono (D5.gamma_antitone G (by norm_num : 4 ≤ 6))
  exact h4.trans <| by
    apply modEq_orderedProduct
    intro l
    have heq : (C.x3 l ^ a l) ^ z = C.x3 l ^ (z * a l) := by
      rw [← zpow_mul]
      congr 1
      ring
    rw [heq]

/-- First divisibility in (66). -/
theorem formula66_lambda
    (C : Context G) (ξ : G) (p : Fin C.t) (l : Fin C.r) :
    orderInt C.f l ∣ orderInt C.e p * lambda C ξ p l := by
  let Q := D5.paperComm (C.x2 p) ξ
  let e := orderInt C.e p
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hQ : Q ∈ D5.gamma G 3 := lambdaArgument_mem_gamma3 C ξ p
  have htransfer := D5.paperComm_zpow_left_mod_gamma
    (n := 4) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num)
    (C.x2_mem_gamma2 p) hξ e
  have hzero : D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x2 p ^ e) ξ) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x2_order_power_mem_gamma3 p) hξ
  have hQpow : Q ^ e ∈ D5.gamma G 4 :=
    D5.modEq_one_iff_mem.mp (htransfer.symm.trans hzero)
  have hcoordPow :
      (orderedProduct fun k => C.x3 k ^ (e * lambda C ξ p k)) ∈
        D5.gamma G 4 := by
    have h64pow := (formula64 C ξ p).zpow e
    have hprodPow :
        (orderedProduct fun k => C.x3 k ^ lambda C ξ p k) ^ e ∈
          D5.gamma G 4 :=
      D5.mem_of_modEq_of_le le_rfl h64pow.symm hQpow
    exact D5.mem_of_modEq_of_le le_rfl
      (x3CoordinateProduct_zpow C (lambda C ξ p) e).symm hprodPow
  exact C.x3_coordinate_dvd_of_product_mem
    (fun k => e * lambda C ξ p k) hcoordPow l

/-- Second divisibility in (66). -/
theorem formula66_eta
    (C : Context G) (ξ : G) (i : Fin C.s) (l : Fin C.r) :
    orderInt C.f l ∣ orderInt C.d i * eta C ξ i l := by
  let I := D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i)
  let d := orderInt C.d i
  have hIpow : I ^ d ∈ D5.gamma G 4 := by
    simpa [I, d] using formula58 C ξ i
  have hcoordPow :
      (orderedProduct fun k => C.x3 k ^ (d * eta C ξ i k)) ∈
        D5.gamma G 4 := by
    have h65pow := (formula65 C ξ i).zpow d
    have hprodPow :
        (orderedProduct fun k => C.x3 k ^ eta C ξ i k) ^ d ∈
          D5.gamma G 4 :=
      D5.mem_of_modEq_of_le le_rfl h65pow.symm hIpow
    exact D5.mem_of_modEq_of_le le_rfl
      (x3CoordinateProduct_zpow C (eta C ξ i) d).symm hprodPow
  exact C.x3_coordinate_dvd_of_product_mem
    (fun k => d * eta C ξ i k) hcoordPow l

private theorem quotient_coe_orderedProduct_gamma4
    {n : ℕ} (a : Fin n → G) :
    ((orderedProduct a : G) : G ⧸ D5.gamma G 4) =
      orderedProduct (fun i => (a i : G ⧸ D5.gamma G 4)) := by
  unfold orderedProduct
  induction List.finRange n with
  | nil => simp
  | cons i is ih => simp [ih]

private theorem quotient_coe_orderedProductWhere_gamma4
    {n : ℕ} (q : Fin n → Prop) [DecidablePred q] (a : Fin n → G) :
    ((orderedProductWhere q a : G) : G ⧸ D5.gamma G 4) =
      orderedProductWhere q (fun i => (a i : G ⧸ D5.gamma G 4)) := by
  unfold orderedProductWhere
  induction (List.finRange n).filter q with
  | nil => simp
  | cons i is ih => simp [ih]

private theorem x3_quotient_pairwise_commute
    (C : Context G) (l m : Fin C.r) :
    Commute ((C.x3 l : G ⧸ D5.gamma G 4)) (C.x3 m) := by
  show (C.x3 l : G ⧸ D5.gamma G 4) * C.x3 m =
    C.x3 m * C.x3 l
  exact D5.mul_comm_mod_gamma (n := 4) (r := 3) (s := 3)
    (by norm_num) (by norm_num) (by norm_num)
    (C.x3_mem_gamma3 l) (C.x3_mem_gamma3 m)

/-- Collect a two-dimensional family of `x₃` coordinate words by its
second coordinate modulo `γ₄`. -/
theorem x3CoordinateProducts_collect
    (C : Context G) {n : ℕ} (a : Fin n → Fin C.r → ℤ) :
    D5.ModEq (D5.gamma G 4)
      (orderedProduct fun i => orderedProduct fun l => C.x3 l ^ a i l)
      (orderedProduct fun l => C.x3 l ^ (∑ i, a i l)) := by
  change
    ((orderedProduct (fun i => orderedProduct fun l => C.x3 l ^ a i l) : G) :
        G ⧸ D5.gamma G 4) =
      ((orderedProduct (fun l => C.x3 l ^ (∑ i, a i l)) : G) :
        G ⧸ D5.gamma G 4)
  rw [quotient_coe_orderedProduct_gamma4,
    quotient_coe_orderedProduct_gamma4]
  simp_rw [quotient_coe_orderedProduct_gamma4, QuotientGroup.mk_zpow]
  exact orderedProduct_coordinates_of_pairwise_commute
    (fun l => (C.x3 l : G ⧸ D5.gamma G 4))
    (x3_quotient_pairwise_commute C) a

/-- Two `x₃` coordinate words add their exponents modulo `γ₄`. -/
theorem x3CoordinateProduct_mul
    (C : Context G) (a b : Fin C.r → ℤ) :
    D5.ModEq (D5.gamma G 4)
      (orderedProduct (fun l => C.x3 l ^ a l) *
        orderedProduct (fun l => C.x3 l ^ b l))
      (orderedProduct fun l => C.x3 l ^ (a l + b l)) := by
  change
    (((orderedProduct (fun l => C.x3 l ^ a l) *
      orderedProduct (fun l => C.x3 l ^ b l) : G) :
        G ⧸ D5.gamma G 4)) = _
  rw [QuotientGroup.mk_mul, quotient_coe_orderedProduct_gamma4,
    quotient_coe_orderedProduct_gamma4,
    quotient_coe_orderedProduct_gamma4]
  exact orderedProduct_mul_of_pairwise_commute
    (fun l => (C.x3 l : G ⧸ D5.gamma G 4))
    (x3_quotient_pairwise_commute C) a b

/-- Collect a filtered family of `x₃` coordinate words modulo `γ₄`. -/
theorem x3CoordinateProductsWhere_collect
    (C : Context G) {n : ℕ} (q : Fin n → Prop) [DecidablePred q]
    (a : Fin n → Fin C.r → ℤ) :
    D5.ModEq (D5.gamma G 4)
      (orderedProductWhere q fun i =>
        orderedProduct fun l => C.x3 l ^ a i l)
      (orderedProduct fun l => C.x3 l ^
        (∑ i ∈ Finset.univ.filter q, a i l)) := by
  change
    ((orderedProductWhere q (fun i =>
      orderedProduct fun l => C.x3 l ^ a i l) : G) :
        G ⧸ D5.gamma G 4) = _
  rw [quotient_coe_orderedProductWhere_gamma4,
    quotient_coe_orderedProduct_gamma4]
  simp_rw [quotient_coe_orderedProduct_gamma4, QuotientGroup.mk_zpow]
  exact orderedProductWhere_coordinates_of_pairwise_commute
    (fun l => (C.x3 l : G ⧸ D5.gamma G 4))
    (x3_quotient_pairwise_commute C) q a

/-- Coordinate coefficient appearing in formula (67). -/
def formula67Coefficient
    (C : Context G) (ξ : G) (i : Fin C.s) (l : Fin C.r) : ℤ :=
  ∑ p, C.b i p * lambda C ξ p l

/-- Formula (67). -/
theorem formula67
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
      (orderedProduct fun l => C.x3 l ^ formula67Coefficient C ξ i l) := by
  let A := orderedProduct fun p => C.x2 p ^ C.b i p
  let B := orderedProduct fun l => C.x3 l ^ C.c i l
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : A ∈ D5.gamma G 2 := by
    dsimp [A]
    apply orderedProduct_mem
    intro p
    exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _
  have hB3 : B ∈ D5.gamma G 3 := by
    dsimp [B]
    apply orderedProduct_mem
    intro l
    exact (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _
  have hrel5 := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) (C.x1_power i) hξ
  have hrel4 := hrel5.mono (D5.gamma_antitone G (by norm_num : 4 ≤ 5))
  have hsplit := D5.paperComm_mul_left_mod_gamma
    (n := 4) (r := 2) (s := 2) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hA (D5.gamma_antitone G (by norm_num) hB3) hξ
  have hBzero : D5.ModEq (D5.gamma G 4) (D5.paperComm B ξ) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hB3 hξ
  have htoA : D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
      (D5.paperComm A ξ) := by
    have h := hrel4.trans <| hsplit.trans <|
      (D5.ModEq.refl (D5.gamma G 4) (D5.paperComm A ξ)).mul hBzero
    simpa [A, B] using h
  have hAexpand := paperComm_orderedProduct_left_gammaTwo_mod_gamma_four
    (fun p => C.x2 p ^ C.b i p) ξ
    (fun p => (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _) hξ
  have hlocal : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun p => D5.paperComm (C.x2 p ^ C.b i p) ξ)
      (orderedProduct fun p =>
        orderedProduct fun l => C.x3 l ^ (C.b i p * lambda C ξ p l)) := by
    apply modEq_orderedProduct
    intro p
    have hp := D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num)
      (C.x2_mem_gamma2 p) hξ (C.b i p)
    have hc := (formula64 C ξ p).zpow (C.b i p)
    exact hp.trans <| hc.trans <|
      x3CoordinateProduct_zpow C (lambda C ξ p) (C.b i p)
  have hcollect := x3CoordinateProducts_collect C
    (fun p l => C.b i p * lambda C ξ p l)
  simpa [A, formula67Coefficient] using
    htoA.trans (hAexpand.trans (hlocal.trans hcollect))

/-- Coordinate coefficient in formula (68). -/
def formula68Coefficient
    (C : Context G) (ξ : G) (i : Fin C.s) (l : Fin C.r) : ℤ :=
  formula67Coefficient C ξ i l -
    TaharaArithmetic.binom2 (C.d i) * eta C ξ i l

/-- Formula (68). -/
theorem formula68
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 i) ξ ^ orderInt C.d i)
      (orderedProduct fun l => C.x3 l ^ formula68Coefficient C ξ i l) := by
  let b2 := TaharaArithmetic.binom2 (C.d i)
  have hrearr := formula57_rearranged_zpow C ξ i 1
  have hrearr' : D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 i) ξ ^ orderInt C.d i)
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ *
        D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i) ^ (-b2)) := by
    simpa [b2] using hrearr
  have hQ := formula67 C ξ i
  have hI : D5.ModEq (D5.gamma G 4)
      (D5.paperComm (D5.paperComm (C.x1 i) ξ) (C.x1 i) ^ (-b2))
      (orderedProduct fun l => C.x3 l ^ ((-b2) * eta C ξ i l)) :=
    (formula65 C ξ i).zpow (-b2) |>.trans
      (x3CoordinateProduct_zpow C (eta C ξ i) (-b2))
  have hreplace := hQ.mul hI
  have hcollect := x3CoordinateProduct_mul C
    (formula67Coefficient C ξ i)
    (fun l => (-b2) * eta C ξ i l)
  have h := hrearr'.trans (hreplace.trans hcollect)
  simpa [b2, formula68Coefficient] using h

/-- The explicit consequence recorded immediately after (68). -/
theorem formula68_mem_gamma3
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.paperComm (C.x1 i) ξ ^ orderInt C.d i ∈ D5.gamma G 3 := by
  apply D5.mem_of_modEq_of_le
    (D5.gamma_antitone G (by norm_num : 3 ≤ 4)) (formula68 C ξ i)
  apply orderedProduct_mem
  intro l
  exact (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _

/-- Coordinate coefficient on the right side of formula (69). -/
def formula69Coefficient
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) (l : Fin C.r) : ℤ :=
  (∑ p, P.v i p * lambda C ξ p l) +
    (∑ j ∈ Finset.univ.filter (i < ·), P.w i j j * eta C ξ j l) +
    (∑ h ∈ Finset.univ.filter (· < i), P.w'' h h i * eta C ξ h l)

/-- Formula (69), with every exponent displayed as an actual coordinate
sum in the original `x₃` basis. -/
theorem formula69
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula62Inner C P ξ i)
      (orderedProduct fun l => C.x3 l ^ formula69Coefficient C P ξ i l) := by
  have hsecondLocal : D5.ModEq (D5.gamma G 4)
      (formula61Second C P ξ i)
      (orderedProduct fun p =>
        orderedProduct fun l => C.x3 l ^ (P.v i p * lambda C ξ p l)) := by
    unfold formula61Second
    apply modEq_orderedProduct
    intro p
    exact (formula64 C ξ p).zpow (P.v i p) |>.trans
      (x3CoordinateProduct_zpow C (lambda C ξ p) (P.v i p))
  have hsecond := hsecondLocal.trans <| x3CoordinateProducts_collect C
    (fun p l => P.v i p * lambda C ξ p l)
  have hhighLocal : D5.ModEq (D5.gamma G 4)
      (formula62HighWeightThree C P ξ i)
      (orderedProductWhere (i < ·) fun j =>
        orderedProduct fun l => C.x3 l ^ (P.w i j j * eta C ξ j l)) := by
    unfold formula62HighWeightThree
    apply modEq_orderedProductWhere
    intro j hij
    exact (formula65 C ξ j).zpow (P.w i j j) |>.trans
      (x3CoordinateProduct_zpow C (eta C ξ j) (P.w i j j))
  have hhigh := hhighLocal.trans <| x3CoordinateProductsWhere_collect C
    (i < ·) (fun j l => P.w i j j * eta C ξ j l)
  have hlowLocal : D5.ModEq (D5.gamma G 4)
      (formula62LowWeightThree C P ξ i)
      (orderedProductWhere (· < i) fun h =>
        orderedProduct fun l => C.x3 l ^ (P.w'' h h i * eta C ξ h l)) := by
    unfold formula62LowWeightThree
    apply modEq_orderedProductWhere
    intro h hhi
    exact (formula65 C ξ h).zpow (P.w'' h h i) |>.trans
      (x3CoordinateProduct_zpow C (eta C ξ h) (P.w'' h h i))
  have hlow := hlowLocal.trans <| x3CoordinateProductsWhere_collect C
    (· < i) (fun h l => P.w'' h h i * eta C ξ h l)
  have hfirstCollect := x3CoordinateProduct_mul C
    (fun l => ∑ p, P.v i p * lambda C ξ p l)
    (fun l => ∑ j ∈ Finset.univ.filter (i < ·),
      P.w i j j * eta C ξ j l)
  have hsecondCollect := x3CoordinateProduct_mul C
    (fun l => (∑ p, P.v i p * lambda C ξ p l) +
      ∑ j ∈ Finset.univ.filter (i < ·), P.w i j j * eta C ξ j l)
    (fun l => ∑ h ∈ Finset.univ.filter (· < i),
      P.w'' h h i * eta C ξ h l)
  exact ((hsecond.mul hhigh).mul hlow).trans
    ((hfirstCollect.mul (D5.ModEq.refl (D5.gamma G 4) _)).trans
      hsecondCollect)

end

end D5.Tahara
