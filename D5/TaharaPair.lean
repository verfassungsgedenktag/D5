import D5.Tahara

/-!
# Pairwise arithmetic consequences of Tahara's conditions

This file connects the abstract integer lemmas in `TaharaArithmetic` to the
actual parameter record and conditions (4.3.3), (4.3.4), and
(4.3.7)--(4.3.9).  Its main theorem packages formulas (12)--(17) for every
pair `i < j`.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

namespace Context

theorem d_gt_one (C : Context G) (i : Fin C.s) : 1 < C.d i :=
  C.basis1.2.2.1 i

theorem e_gt_one (C : Context G) (i : Fin C.t) : 1 < C.e i :=
  C.basis2.2.2.1 i

theorem f_gt_one (C : Context G) (i : Fin C.r) : 1 < C.f i :=
  C.basis3.2.2.1 i

end Context

/-- Formulas (12)--(17), with (15) expressed without division by using
divisibility by `d(i)^2`. -/
structure PairConsequences (C : Context G) (P : Parameters C.s C.t)
    (i j : Fin C.s) : Prop where
  equation12 :
    P.u i j * TaharaArithmetic.binom2 (C.d j) =
      orderInt C.d i *
        (P.w i j j + orderRatio C.d i j * P.w' i j j)
  equation13 :
    P.u i j * orderRatio C.d i j * TaharaArithmetic.binom2 (C.d i) =
      orderInt C.d i *
        (-P.w i i j - orderRatio C.d i j * P.w'' i i j)
  dvd17_left : orderInt C.d i ∣
    P.u i j * orderRatio C.d i j * TaharaArithmetic.binom2 (C.d i)
  dvd17_right : orderInt C.d i ∣
    P.u i j * TaharaArithmetic.binom2 (C.d j)
  dvd14_wiij : orderInt C.d i ∣
    P.w i i j * TaharaArithmetic.binom2 (C.d i)
  dvd14_wppiij : orderInt C.d i ∣
    P.w'' i i j * TaharaArithmetic.binom2 (C.d j)
  dvd14_wpijj : orderInt C.d i ∣
    P.w' i j j * TaharaArithmetic.binom2 (C.d j)
  dvd14_wijj : orderInt C.d i ∣
    P.w i j j * TaharaArithmetic.binom2 (C.d i)
  /-- The transferred `w'` correction used in formula (40). -/
  dvd_q_wpijj_B2d : orderInt C.d i ∣
    orderRatio C.d i j * P.w' i j j *
      TaharaArithmetic.binom2 (C.d i)
  /-- The transferred `w''` correction used in formula (41). -/
  dvd_q_wppiij_B2d : orderInt C.d i ∣
    orderRatio C.d i j * P.w'' i i j *
      TaharaArithmetic.binom2 (C.d i)
  dvd15_left : orderInt C.d i * orderInt C.d i ∣
    P.u i j * TaharaArithmetic.binom2 (C.d j) *
      TaharaArithmetic.binom2 (C.d i)
  dvd15_right : orderInt C.d i * orderInt C.d i ∣
    P.u i j * orderRatio C.d i j * TaharaArithmetic.binom2 (C.d i) *
      TaharaArithmetic.binom2 (C.d i)
  dvd16_left : orderInt C.d i ∣
    P.u i j * orderRatio C.d i j * TaharaArithmetic.binom3 (C.d i)
  dvd16_right : orderInt C.d i ∣
    P.u i j * TaharaArithmetic.binom3 (C.d j)

/-- Every admissible parameter package satisfies all pairwise consequences
(12)--(17). -/
theorem pairConsequences (C : Context G) (P : Parameters C.s C.t)
    (hP : P.Satisfies) {i j : Fin C.s} (hij : i < j) :
    PairConsequences C P i j := by
  rcases hP with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hdvdNat : C.d i ∣ C.d j := C.d_dvd i j (le_of_lt hij)
  have heNat : C.d j = C.d i * (C.d j / C.d i) := by
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdvdNat).symm
  have he : orderInt C.d j =
      orderInt C.d i * orderRatio C.d i j := by
    have heZ : (C.d j : ℤ) = (C.d i : ℤ) * (C.d j / C.d i : ℕ) := by
      exact_mod_cast heNat
    simpa [orderInt, orderRatio] using heZ
  have hdpos : 0 < C.d i := lt_trans Nat.zero_lt_one (C.d_gt_one i)
  have hepos : 0 < C.d j := lt_trans Nat.zero_lt_one (C.d_gt_one j)
  have hqpos : 0 < C.d j / C.d i :=
    Nat.div_pos (Nat.le_of_dvd hepos hdvdNat) hdpos
  have hdne : orderInt C.d i ≠ 0 := by
    simpa [orderInt] using (show (C.d i : ℤ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hdpos))
  have h3eq :
      P.u i j * orderRatio C.d i j * TaharaArithmetic.binom2 (C.d i) +
        orderInt C.d i * P.w i i j + orderInt C.d j * P.w'' i i j = 0 := by
    simpa [mul_comm] using h3 i j hij
  have h4eq :
      -P.u i j * TaharaArithmetic.binom2 (C.d j) +
        orderInt C.d i * P.w i j j + orderInt C.d j * P.w' i j j = 0 := by
    simpa [mul_comm] using h4 i j hij
  have hB2d : 2 * TaharaArithmetic.binom2 (C.d i) =
      orderInt C.d i * (orderInt C.d i - 1) := by
    have h := TaharaArithmetic.two_mul_binom2 (C.d i)
    rw [Nat.cast_sub (Nat.le_of_lt (C.d_gt_one i))] at h
    simpa [orderInt] using h
  have hB3d : 3 * TaharaArithmetic.binom3 (C.d i) =
      TaharaArithmetic.binom2 (C.d i) * (orderInt C.d i - 2) := by
    have h := TaharaArithmetic.three_mul_binom3 (C.d i)
    rw [Nat.cast_sub (C.d_gt_one i)] at h
    simpa [orderInt] using h
  have hB2e : 2 * TaharaArithmetic.binom2 (C.d j) =
      orderInt C.d j * (orderInt C.d j - 1) := by
    have h := TaharaArithmetic.two_mul_binom2 (C.d j)
    rw [Nat.cast_sub (Nat.le_of_lt (C.d_gt_one j))] at h
    simpa [orderInt] using h
  have hB3e : 3 * TaharaArithmetic.binom3 (C.d j) =
      TaharaArithmetic.binom2 (C.d j) * (orderInt C.d j - 2) := by
    have h := TaharaArithmetic.three_mul_binom3 (C.d j)
    rw [Nat.cast_sub (C.d_gt_one j)] at h
    simpa [orderInt] using h
  have h7dvd : orderInt C.d i ∣
      P.u i j * orderRatio C.d i j * TaharaArithmetic.binom3 (C.d i) +
        P.w i i j * TaharaArithmetic.binom2 (C.d i) :=
    Int.modEq_zero_iff_dvd.mp (h7 i j hij)
  have h8dvd : orderInt C.d i ∣
      P.w i i j * TaharaArithmetic.binom2 (C.d i) +
        P.w'' i i j * TaharaArithmetic.binom2 (C.d j) :=
    Int.modEq_zero_iff_dvd.mp (h8 i j hij)
  have h9dvd : orderInt C.d i ∣
      -P.u i j * TaharaArithmetic.binom3 (C.d j) +
        P.w' i j j * TaharaArithmetic.binom2 (C.d j) :=
    Int.modEq_zero_iff_dvd.mp (h9 i j hij)
  have h17 := TaharaArithmetic.divisibility17 he h3eq h4eq
  have hwi := TaharaArithmetic.dvd_wiij_mul_B2d h17.1 h7dvd hB2d hB3d
  have hwp := TaharaArithmetic.dvd_wpijj_mul_B2e he h17.2 h9dvd hB2e hB3e
  have hwpp := TaharaArithmetic.dvd_wppiij_mul_B2e hwi h8dvd
  have huB3d := TaharaArithmetic.dvd_uq_mul_B3d hwi h7dvd
  have huB3e := TaharaArithmetic.dvd_u_mul_B3e hwp h9dvd
  have hdiff0 := TaharaArithmetic.binom2_mul_sub_ratio
    (C.d i) (C.d j / C.d i) hdpos hqpos
  have hdiff : TaharaArithmetic.binom2 (C.d j) -
      orderRatio C.d i j * TaharaArithmetic.binom2 (C.d i) =
      orderInt C.d i * orderInt C.d i *
        TaharaArithmetic.binom2 (C.d j / C.d i) := by
    change TaharaArithmetic.binom2 (C.d j) -
      ((C.d j / C.d i : ℕ) : ℤ) * TaharaArithmetic.binom2 (C.d i) =
      (C.d i : ℤ) * (C.d i : ℤ) *
        TaharaArithmetic.binom2 (C.d j / C.d i)
    nth_rewrite 1 [heNat]
    exact hdiff0
  have hqwpp := TaharaArithmetic.dvd_q_mul_B2d_of_dvd_mul_B2e hdiff hwpp
  have hqwp := TaharaArithmetic.dvd_q_mul_B2d_of_dvd_mul_B2e hdiff hwp
  have h15right := TaharaArithmetic.dvd_sq_mul_uq_B2d_sq
    he h3eq hwi hqwpp
  have h15left := TaharaArithmetic.dvd_sq_mul_u_B2e_B2d hdiff h15right
  have hwijj := TaharaArithmetic.dvd_wijj_mul_B2d hdne he h4eq
    h15left hqwp
  exact
    { equation12 := TaharaArithmetic.equation12 he h4eq
      equation13 := TaharaArithmetic.equation13 he h3eq
      dvd17_left := h17.1
      dvd17_right := h17.2
      dvd14_wiij := hwi
      dvd14_wppiij := hwpp
      dvd14_wpijj := hwp
      dvd14_wijj := hwijj
      dvd_q_wpijj_B2d := hqwp
      dvd_q_wppiij_B2d := hqwpp
      dvd15_left := h15left
      dvd15_right := h15right
      dvd16_left := huB3d
      dvd16_right := huB3e }

end

end D5.Tahara
