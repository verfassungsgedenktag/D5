import D5.TaharaExpand28
import D5.TaharaTransferConsequences

/-!
# The local calculation in Section 10

The first product in formula (18) is transformed one pair of indices at a
time.  This file records the full six-factor Hall--Witt rotation before the
subsequent finite-product collection.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

set_option maxHeartbeats 800000

/-- The six factors supplied by formula (19) for the pair `i < j`, after
the outer exponent `u(i,j)` has been distributed.  The first two factors
are the two main terms used in formula (21); the last four are the first
four correction lines of formula (29). -/
def formula19PairFactors
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d j)) (C.x1 j) ^ (-P.u i j) *
    D5.paperComm
      (D5.paperComm ξ (C.x1 j)) (C.x1 i ^ orderInt C.d j) ^ P.u i j) *
  ((D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j))
        (C.x1 j)) ξ ^ P.u i j *
    D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ)
        (C.x1 j) ^ (-P.u i j)) *
    (D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ) ξ)
        (C.x1 i ^ orderInt C.d j) ^ P.u i j *
    D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ)
        (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j)))

/-- Formula (19) for one pair in the exact commutator orientation used by
the proof.  No Tahara condition is used: this is the Hall--Witt computation
and the fact that the six resulting factors commute modulo `γ₆`. -/
theorem formula19_pair
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ ^ P.u i j)
      (formula19PairFactors C P ξ i j) := by
  let a := C.x1 i ^ orderInt C.d j
  let b := C.x1 j
  let c := ξ
  let v := P.u i j
  have ha : a ∈ D5.gamma G 2 := by
    simpa [a] using C.x1_later_order_power_mem_gamma2 (show i ≤ j from hij.le)
  have hb : b ∈ D5.gamma G 1 := by simp [b, D5.gamma]
  have hc : c ∈ D5.gamma G 1 := by simp [c, D5.gamma]
  have hrot := (D5.rotation_formula19 ha hb hc).zpow v
  have hC : D5.paperComm (D5.paperComm c a) b ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hc ha) hb
  have hB : D5.paperComm (D5.paperComm c b) a ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hc hb) ha
  have hab : D5.paperComm a b ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb
  have hD : D5.paperComm (D5.paperComm (D5.paperComm a b) b) c ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hab hb) hc
  have hE : D5.paperComm (D5.paperComm (D5.paperComm a b) c) b ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hab hc) hb
  have hbc : D5.paperComm b c ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hc
  have hF : D5.paperComm (D5.paperComm (D5.paperComm b c) c) a ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hbc hc) ha
  have hH : D5.paperComm (D5.paperComm (D5.paperComm b c) a) c ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hbc ha) hc
  let C0 := (D5.paperComm (D5.paperComm c a) b)⁻¹
  let B0 := D5.paperComm (D5.paperComm c b) a
  let D0 := D5.paperComm (D5.paperComm (D5.paperComm a b) b) c
  let E0 := (D5.paperComm (D5.paperComm (D5.paperComm a b) c) b)⁻¹
  let F0 := D5.paperComm (D5.paperComm (D5.paperComm b c) c) a
  let H0 := (D5.paperComm (D5.paperComm (D5.paperComm b c) a) c)⁻¹
  have hC0 : C0 ∈ D5.gamma G 3 :=
    D5.gamma_antitone G (by norm_num : 3 ≤ 4) ((D5.gamma G 4).inv_mem hC)
  have hB0 : B0 ∈ D5.gamma G 3 := D5.gamma_antitone G (by norm_num : 3 ≤ 4) hB
  have hD0 : D0 ∈ D5.gamma G 3 := D5.gamma_antitone G (by norm_num : 3 ≤ 5) hD
  have hE0 : E0 ∈ D5.gamma G 3 :=
    D5.gamma_antitone G (by norm_num : 3 ≤ 5) ((D5.gamma G 5).inv_mem hE)
  have hF0 : F0 ∈ D5.gamma G 3 := D5.gamma_antitone G (by norm_num : 3 ≤ 5) hF
  have hH0 : H0 ∈ D5.gamma G 3 :=
    D5.gamma_antitone G (by norm_num : 3 ≤ 5) ((D5.gamma G 5).inv_mem hH)
  have hCB : C0 * B0 ∈ D5.gamma G 3 := (D5.gamma G 3).mul_mem hC0 hB0
  have hCBD : C0 * B0 * D0 ∈ D5.gamma G 3 := (D5.gamma G 3).mul_mem hCB hD0
  have hCBDE : C0 * B0 * D0 * E0 ∈ D5.gamma G 3 :=
    (D5.gamma G 3).mul_mem hCBD hE0
  have hCBDEF : C0 * B0 * D0 * E0 * F0 ∈ D5.gamma G 3 :=
    (D5.gamma G 3).mul_mem hCBDE hF0
  have h1 := D5.gammaThree_mul_zpow hC0 hB0 v
  have h2 := D5.gammaThree_mul_zpow hCB hD0 v
  have h3 := D5.gammaThree_mul_zpow hCBD hE0 v
  have h4 := D5.gammaThree_mul_zpow hCBDE hF0 v
  have h5 := D5.gammaThree_mul_zpow hCBDEF hH0 v
  have hdistribute : D5.ModGammaSix
      (((D5.paperComm (D5.paperComm c a) b)⁻¹ *
          D5.paperComm (D5.paperComm c b) a *
          D5.paperComm (D5.paperComm (D5.paperComm a b) b) c *
          (D5.paperComm (D5.paperComm (D5.paperComm a b) c) b)⁻¹ *
          D5.paperComm (D5.paperComm (D5.paperComm b c) c) a *
          (D5.paperComm (D5.paperComm (D5.paperComm b c) a) c)⁻¹) ^ v)
      ((D5.paperComm (D5.paperComm c a) b)⁻¹ ^ v *
          D5.paperComm (D5.paperComm c b) a ^ v *
          D5.paperComm (D5.paperComm (D5.paperComm a b) b) c ^ v *
          (D5.paperComm (D5.paperComm (D5.paperComm a b) c) b)⁻¹ ^ v *
          D5.paperComm (D5.paperComm (D5.paperComm b c) c) a ^ v *
          (D5.paperComm (D5.paperComm (D5.paperComm b c) a) c)⁻¹ ^ v) := by
    have h123 := h2.trans <|
      h1.mul (D5.ModEq.refl (D5.gamma G 6) (D0 ^ v))
    have h1234 := h3.trans <|
      h123.mul (D5.ModEq.refl (D5.gamma G 6) (E0 ^ v))
    have h12345 := h4.trans <|
      h1234.mul (D5.ModEq.refl (D5.gamma G 6) (F0 ^ v))
    exact h5.trans <|
      h12345.mul (D5.ModEq.refl (D5.gamma G 6) (H0 ^ v))
  have hCpow : C0 ^ v = D5.paperComm (D5.paperComm c a) b ^ (-v) := by
    simp only [C0, inv_zpow, zpow_neg]
  have hEpow : E0 ^ v = D5.paperComm (D5.paperComm (D5.paperComm a b) c) b ^ (-v) := by
    simp only [E0, inv_zpow, zpow_neg]
  have hHpow : H0 ^ v = D5.paperComm (D5.paperComm (D5.paperComm b c) a) c ^ (-v) := by
    simp only [H0, inv_zpow, zpow_neg]
  simpa only [formula19PairFactors, C0, B0, D0, E0, F0, H0, hCpow, hEpow,
    hHpow, neg_mul, mul_assoc] using hrot.trans hdistribute

/-- The first main factor of formula (19) has the order-normalized form
used in formula (21). -/
theorem formula19_low_main
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ (C.x1 i ^ orderInt C.d j)) (C.x1 j) ^ (-P.u i j))
      (D5.paperComm
        (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j) ^
          (-P.u i j * orderRatio C.d i j)) := by
  let y := C.x1 i ^ orderInt C.d i
  let q := orderRatio C.d i j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hy : y ∈ D5.gamma G 2 := by
    simpa [y] using C.x1_order_power_mem_gamma2 i
  have hx : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hpower := (nested_weight_two_zpow_right hξ hy hx q).zpow (-P.u i j)
  have horder : orderInt C.d j = orderInt C.d i * q :=
    Context.orderInt_eq_mul_ratio C hij.le
  simpa [y, q, horder, zpow_neg, zpow_mul, mul_comm] using hpower

/-- The local output after applying both formula (19) and the reduced
formula (20).  The order in this definition is the order produced by the
two calculations; the later finite-product collection will rearrange these
weight-at-least-four factors into the twelve displayed streams of (29). -/
def formula19And20PairFactors
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j) ^
        (-P.u i j * orderRatio C.d i j) *
    (D5.paperComm
        (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^ P.u i j *
      D5.paperComm
        (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j)) (C.x1 i) ^
          (P.u i j * TaharaArithmetic.binom2 (C.d j)) *
      D5.paperComm
        (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 i)) (C.x1 i) ^
          (-P.u i j * TaharaArithmetic.binom2 (C.d j)))) *
  ((D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j))
        (C.x1 j)) ξ ^ P.u i j *
    D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ)
        (C.x1 j) ^ (-P.u i j)) *
    (D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ) ξ)
        (C.x1 i ^ orderInt C.d j) ^ P.u i j *
    D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ)
        (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j)))

theorem formula19_and_20_pair
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ ^ P.u i j)
      (formula19And20PairFactors C P ξ i j) := by
  have h19 := formula19_pair C P ξ hij
  have hlow := formula19_low_main C P ξ hij
  have h20 := transfer_formula20_reduced C P hP ξ hij
  exact h19.trans <| by
    simpa [formula19PairFactors, formula19And20PairFactors, mul_assoc] using
      ((hlow.mul h20).mul
        (D5.ModEq.refl (D5.gamma G 6)
          ((D5.paperComm
            (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j))
              (C.x1 j)) ξ ^ P.u i j *
          D5.paperComm
            (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ)
              (C.x1 j) ^ (-P.u i j)) *
          (D5.paperComm
            (D5.paperComm (D5.paperComm (C.x1 j) ξ) ξ)
              (C.x1 i ^ orderInt C.d j) ^ P.u i j *
          D5.paperComm
            (D5.paperComm (D5.paperComm (C.x1 j) ξ)
              (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j)))))

end

end D5.Tahara
