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

/-- A fixed finite permutation used when collecting one `i < j` factor in
Section 10.  It moves the four Hall--Witt corrections to the front and
leaves the two transfer corrections immediately before the two main terms. -/
private theorem gammaThree_permute_eight
    {a b c d e f g h : G}
    (ha : a ∈ D5.gamma G 3) (hb : b ∈ D5.gamma G 3)
    (hc : c ∈ D5.gamma G 3) (hd : d ∈ D5.gamma G 3)
    (he : e ∈ D5.gamma G 3) (hf : f ∈ D5.gamma G 3)
    (hg : g ∈ D5.gamma G 3) (hh : h ∈ D5.gamma G 3) :
    D5.ModGammaSix ([a, b, c, d, e, f, g, h].prod)
      ([e, f, g, h, c, d, a, b].prod) := by
  have hleft : ([a, b] ++ [c, d]).Perm ([c, d] ++ [a, b]) :=
    List.perm_append_comm
  have hperm : ([a, b, c, d] ++ [e, f, g, h]).Perm
      ([e, f, g, h] ++ [c, d, a, b]) := by
    exact List.perm_append_comm.trans <| by
      simpa only [List.append_assoc] using hleft.append_left [e, f, g, h]
  apply D5.listProd_perm_gammaThree (by simpa using hperm)
  intro x hx
  simp only [List.mem_cons] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he
  · exact hf
  · exact hg
  rcases hx with rfl | hx
  · exact hh
  simpa using hx

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

/-- The six correction factors of formula (29) attached to one pair
`i < j`, in their displayed order. -/
def formula29PairCorrections
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
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
        (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j))) *
  (D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j)) (C.x1 i) ^
        (P.u i j * TaharaArithmetic.binom2 (C.d j)) *
    D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 i)) (C.x1 i) ^
        (-P.u i j * TaharaArithmetic.binom2 (C.d j)))

/-- The two terms passed on to formula (21). -/
def formula29PairMain
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j) ^
        (-P.u i j * orderRatio C.d i j) *
    D5.paperComm
      (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^ P.u i j

/-- The only reordering in the local step of Section 10.  All eight factors
are in `γ₃`, so the checked finite permutation is valid modulo `γ₆`. -/
theorem formula19_and_20_pair_collected
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula19And20PairFactors C P ξ i j)
      (formula29PairCorrections C P ξ i j * formula29PairMain C P ξ i j) := by
  let A := D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j) ^
      (-P.u i j * orderRatio C.d i j)
  let B := D5.paperComm
    (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i) ^ P.u i j
  let C0 := D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j)) (C.x1 i) ^
      (P.u i j * TaharaArithmetic.binom2 (C.d j))
  let D0 := D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 i)) (C.x1 i) ^
      (-P.u i j * TaharaArithmetic.binom2 (C.d j))
  let E := D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j))
      (C.x1 j)) ξ ^ P.u i j
  let F := D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ)
      (C.x1 j) ^ (-P.u i j)
  let H := D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ) ξ)
      (C.x1 i ^ orderInt C.d j) ^ P.u i j
  let K := D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ)
      (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hipow : C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 i
  have hijpow : C.x1 i ^ orderInt C.d j ∈ D5.gamma G 2 :=
    C.x1_later_order_power_mem_gamma2 hij.le
  have hjpow : C.x1 j ^ orderInt C.d j ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 j
  have hA : A ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hipow) hxj
  have hB : B ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hjpow) hxi
  have hxjξ : D5.paperComm (C.x1 j) ξ ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxj hξ
  have hC : C0 ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hxj) hxi
  have hD : D0 ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hxi) hxi
  have hipowj : D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j) ∈
      D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hijpow hxj
  have hE : E ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hipowj hxj) hξ
  have hF : F ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hipowj hξ) hxj
  have hH : H ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hξ) hijpow
  have hK : K ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hijpow) hξ
  have hperm := gammaThree_permute_eight hA hB hC hD hE hF hH hK
  simpa [formula19And20PairFactors, formula29PairCorrections,
    formula29PairMain, A, B, C0, D0, E, F, H, K, List.prod_cons,
    List.prod_nil, mul_assoc] using hperm

theorem formula29_pair_main_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : formula29PairMain C P ξ i j ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hipow : C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 i
  have hjpow : C.x1 j ^ orderInt C.d j ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 j
  apply (D5.gamma G 3).mul_mem
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hipow) hxj
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hjpow) hxi

theorem formula29_pair_corrections_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    formula29PairCorrections C P ξ i j ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hijpow : C.x1 i ^ orderInt C.d j ∈ D5.gamma G 2 :=
    C.x1_later_order_power_mem_gamma2 hij.le
  have hxjξ : D5.paperComm (C.x1 j) ξ ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxj hξ
  have hipowj : D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j) ∈
      D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hijpow hxj
  have hE : D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j))
        (C.x1 j)) ξ ^ P.u i j ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hipowj hxj) hξ
  have hF : D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ)
        (C.x1 j) ^ (-P.u i j) ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hipowj hξ) hxj
  have hH : D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ) ξ)
        (C.x1 i ^ orderInt C.d j) ^ P.u i j ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hξ) hijpow
  have hK : D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ)
        (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j) ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hijpow) hξ
  have hC : D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j)) (C.x1 i) ^
        (P.u i j * TaharaArithmetic.binom2 (C.d j)) ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hxj) hxi
  have hD : D5.paperComm
      (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 i)) (C.x1 i) ^
        (-P.u i j * TaharaArithmetic.binom2 (C.d j)) ∈ D5.gamma G 3 := by
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hxi) hxi
  simpa [formula29PairCorrections] using
    (D5.gamma G 3).mul_mem
      ((D5.gamma G 3).mul_mem ((D5.gamma G 3).mul_mem hE hF)
        ((D5.gamma G 3).mul_mem hH hK))
      ((D5.gamma G 3).mul_mem hC hD)

/-- Finite collection of all pairwise formula-(19)--(20) outputs.  The two
resulting products are exactly the first six correction streams and the
two main streams which feed formula (21). -/
theorem formula19_and_20_first_product_collected
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        formula19And20PairFactors C P ξ i j)
      ((orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
          formula29PairCorrections C P ξ i j) *
        (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
          formula29PairMain C P ξ i j)) := by
  let R : Fin C.s → G := fun i => orderedProductWhere (i < ·) fun j =>
    formula29PairCorrections C P ξ i j
  let M : Fin C.s → G := fun i => orderedProductWhere (i < ·) fun j =>
    formula29PairMain C P ξ i j
  have hR : ∀ i, R i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact formula29_pair_corrections_mem_gamma3 C P ξ hij
  have hM : ∀ i, M i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact formula29_pair_main_mem_gamma3 C P ξ i j
  have hlocal : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        formula19And20PairFactors C P ξ i j)
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        formula29PairCorrections C P ξ i j * formula29PairMain C P ξ i j) := by
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    exact formula19_and_20_pair_collected C P ξ hij
  have hrows : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        formula29PairCorrections C P ξ i j * formula29PairMain C P ξ i j)
      (orderedProduct fun i => R i * M i) := by
    apply modEq_orderedProduct
    intro i
    simpa [R, M] using D5.orderedProductWhere_pointwise_mul_gammaThree
      (i < ·) (formula29PairCorrections C P ξ i)
        (formula29PairMain C P ξ i)
        (fun j hij => formula29_pair_corrections_mem_gamma3 C P ξ hij)
        (fun j _hij => formula29_pair_main_mem_gamma3 C P ξ i j)
  have houter := D5.orderedProduct_pointwise_mul_gammaThree R M hR hM
  exact hlocal.trans <| hrows.trans <| by
    simpa [R, M] using houter

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

/-- The first product in formula (18), isolated so that the pairwise
formula-(19)--(20) calculation can be lifted through its exact ordered
indexing. -/
def formula18FirstPairProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ ^ P.u i j

/-- The simultaneous formula-(19)--(20) replacement of every factor in
the first product of (18).  This preserves the paper's noncommutative
lexicographic product order; the reordering into the displayed streams of
formula (29) is a separate finite collection step. -/
theorem formula19_and_20_first_product
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (formula18FirstPairProduct C P ξ)
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        formula19And20PairFactors C P ξ i j) := by
  unfold formula18FirstPairProduct
  apply modEq_orderedProduct
  intro i
  apply modEq_orderedProductWhere
  intro j hij
  exact formula19_and_20_pair C P hP ξ hij

/-- The surviving main pair product is definitionally the left side of the
already verified structural expansion (21). -/
theorem formula29_main_product_eq_formula21
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        formula29PairMain C P ξ i j) = formula21MainPairProduct C P ξ := by
  rfl

/-- Formulas (19)--(20) applied to the whole first factor of (18), with the
two main streams identified as the input to formula (21). -/
theorem formula19_and_20_first_product_to_formula21
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (formula18FirstPairProduct C P ξ)
      ((orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
          formula29PairCorrections C P ξ i j) *
        formula21MainPairProduct C P ξ) := by
  exact (formula19_and_20_first_product C P hP ξ).trans <|
    (formula19_and_20_first_product_collected C P hP ξ).trans <| by
      rw [formula29_main_product_eq_formula21]

/-- The first completed assembly step of Section 10.  It applies formulas
(19)--(21) to the first block of formula (18), retaining the untouched
second- and third-weight blocks in their original order. -/
theorem formula18_after_formula19_to_21
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (formula18Expansion C P ξ)
      ((orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
          formula29PairCorrections C P ξ i j) *
        (formula21WeightTwoPowerProduct C P ξ *
          formula21FinalThirdGrouped C P ξ) *
        (orderedProduct fun i => orderedProduct fun p =>
          orderedProductWhere (p < ·) fun q =>
            D5.paperComm (D5.paperComm (C.x2 q) (C.x2 p)) ξ ^
              (C.b i q * P.v i p)) *
        orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
          orderedProductWhere (j ≤ ·) fun k =>
            D5.paperComm
              (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ^
                P.w i j k) := by
  have hfirst := formula19_and_20_first_product_to_formula21 C P hP ξ
  have h21 := structural_expansion21 C P hP.2.2.2.2.1 ξ
  let Q := orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    formula29PairCorrections C P ξ i j
  let S := orderedProduct fun i => orderedProduct fun p =>
    orderedProductWhere (p < ·) fun q =>
      D5.paperComm (D5.paperComm (C.x2 q) (C.x2 p)) ξ ^
        (C.b i q * P.v i p)
  let T := orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      D5.paperComm
        (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ^ P.w i j k
  have hfirst' : D5.ModGammaSix (formula18Expansion C P ξ)
      ((Q * formula21MainPairProduct C P ξ) * (S * T)) := by
    simpa [formula18Expansion, formula18FirstPairProduct, Q, S, T] using
      hfirst.mul (D5.ModEq.refl (D5.gamma G 6) (S * T))
  simpa only [mul_assoc] using hfirst'.trans <|
    ((D5.ModEq.refl (D5.gamma G 6) Q).mul h21).mul
      (D5.ModEq.refl (D5.gamma G 6) (S * T))

/-- The seventh displayed stream of formula (29), obtained as the correction
term in formula (22). -/
def formula29LineSeven
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j =>
    D5.paperComm
      (D5.paperComm (D5.paperComm (formula22WeightTwoWord C P j) ξ)
        (C.x1 j)) (C.x1 j) ^ TaharaArithmetic.binom2 (C.d j)

theorem formula22_correction_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) :
    D5.paperComm
      (D5.paperComm (D5.paperComm (formula22WeightTwoWord C P j) ξ)
        (C.x1 j)) (C.x1 j) ^ TaharaArithmetic.binom2 (C.d j) ∈
      D5.gamma G 3 := by
  have hW := formula22WeightTwoWord_mem_gamma2 C P j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
  apply (D5.gamma G 5).zpow_mem
  exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
    (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hW hξ) hx) hx

/-- Formula (22) collected over all first-layer indices. -/
theorem formula21_weight_two_to_formula23_and_line_seven
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula21WeightTwoPowerProduct C P ξ)
      (formula23Source C P ξ * formula29LineSeven C P ξ) := by
  let A : Fin C.s → G := fun j => formula23LocalSource C P ξ j
  let B : Fin C.s → G := fun j =>
    D5.paperComm
      (D5.paperComm (D5.paperComm (formula22WeightTwoWord C P j) ξ)
        (C.x1 j)) (C.x1 j) ^ TaharaArithmetic.binom2 (C.d j)
  have hA : ∀ j, A j ∈ D5.gamma G 3 := by
    intro j
    have hW := formula22WeightTwoWord_mem_gamma2 C P j
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hx : C.x1 j ^ orderInt C.d j ∈ D5.gamma G 2 :=
      C.x1_order_power_mem_gamma2 j
    simpa [A, formula23LocalSource] using D5.gamma_antitone G
      (by norm_num : 3 ≤ 5)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hW) hx)
  have hB : ∀ j, B j ∈ D5.gamma G 3 := by
    intro j
    simpa [B] using formula22_correction_mem_gamma3 C P ξ j
  have hlocal : D5.ModGammaSix (formula21WeightTwoPowerProduct C P ξ)
      (orderedProduct fun j => A j * B j) := by
    unfold formula21WeightTwoPowerProduct
    apply modEq_orderedProduct
    intro j
    simpa [A, B, formula23LocalSource] using transfer_formula22 C P ξ j
  exact hlocal.trans <| by
    simpa [formula23Source, formula29LineSeven, A, B] using
      D5.orderedProduct_pointwise_mul_gammaThree A B hA hB

/-- The second product in formula (18), retained with its printed order of
indices.  It cancels the correction produced by formula (26). -/
def formula18SecondProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProduct fun p =>
    orderedProductWhere (p < ·) fun q =>
      D5.paperComm (D5.paperComm (C.x2 q) (C.x2 p)) ξ ^
        (C.b i q * P.v i p)

/-- The same second product after reversing its inner commutator, applying
finite Fubini, and collecting the exponent at every pair `p < q`. -/
theorem formula18_second_collected
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula18SecondProduct C P ξ)
      (strictPairProduct fun p q =>
        D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ ^
          (-formula23Coefficient C P p q)) := by
  let A : Fin C.t → Fin C.t → G := fun p q =>
    D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ
  let F : Fin C.s → Fin C.t → Fin C.t → G := fun i p q =>
    A p q ^ (-(C.b i q * P.v i p))
  have hA : ∀ p q, A p q ∈ D5.gamma G 3 := by
    intro p q
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (C.x2_mem_gamma2 p) (C.x2_mem_gamma2 q)) hξ
  have hF : ∀ i p q, F i p q ∈ D5.gamma G 3 := by
    intro i p q
    exact (D5.gamma G 3).zpow_mem (hA p q) _
  have hreverse : D5.ModGammaSix (formula18SecondProduct C P ξ)
      (orderedProduct fun i => orderedProduct fun p =>
        orderedProductWhere (p < ·) fun q => F i p q) := by
    unfold formula18SecondProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProduct
    intro p
    apply modEq_orderedProductWhere
    intro q hpq
    have hinner : D5.paperComm (C.x2 p) (C.x2 q) ∈ D5.gamma G 4 :=
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (C.x2_mem_gamma2 p) (C.x2_mem_gamma2 q)
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hinv := D5.paperComm_inv_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hinner hξ
    rw [D5.paperComm_swap (C.x2 p) (C.x2 q)]
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q))⁻¹ ξ ^
        (C.b i q * P.v i p))
      (A p q ^ (-(C.b i q * P.v i p)))
    have hp := hinv.zpow (C.b i q * P.v i p)
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q))⁻¹ ξ ^
        (C.b i q * P.v i p))
      ((A p q)⁻¹ ^ (C.b i q * P.v i p)) at hp
    exact hp.trans <| by
      rw [inv_zpow, zpow_neg]
  have hswapIP : D5.ModGammaSix
      (orderedProduct fun i => orderedProduct fun p =>
        orderedProductWhere (p < ·) fun q => F i p q)
      (orderedProduct fun p => orderedProduct fun i =>
        orderedProductWhere (p < ·) fun q => F i p q) := by
    exact D5.orderedProduct_orderedProduct_swap_gammaThree
      (fun i p => orderedProductWhere (p < ·) fun q => F i p q)
      (fun i p => by
        apply orderedProductWhere_mem
        intro q hpq
        exact hF i p q)
  have hswapIQ : D5.ModGammaSix
      (orderedProduct fun p => orderedProduct fun i =>
        orderedProductWhere (p < ·) fun q => F i p q)
      (orderedProduct fun p => orderedProductWhere (p < ·) fun q =>
        orderedProduct fun i => F i p q) := by
    apply modEq_orderedProduct
    intro p
    exact (D5.orderedProductWhere_orderedProduct_swap_gammaThree
      (p < ·) (fun q i => F i p q)
      (fun q hpq i => hF i p q)).symm
  have hcollect : D5.ModGammaSix
      (orderedProduct fun p => orderedProductWhere (p < ·) fun q =>
        orderedProduct fun i => F i p q)
      (strictPairProduct fun p q =>
        A p q ^ (-formula23Coefficient C P p q)) := by
    unfold strictPairProduct
    apply modEq_orderedProduct
    intro p
    apply modEq_orderedProductWhere
    intro q hpq
    unfold F
    rw [D5.orderedProduct_zpow_same_base]
    have he : (∑ i, -(C.b i q * P.v i p)) =
        -formula23Coefficient C P p q := by
      simp only [formula23Coefficient, Finset.sum_neg_distrib]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he]
  exact hreverse.trans <| hswapIP.trans <| hswapIQ.trans <| by
    simpa [A] using hcollect

/-- Formula (26) cancels the second product of formula (18), including the
sign coming from `[x₂q,x₂p] = [x₂p,x₂q]⁻¹`. -/
theorem formula26_cancels_formula18_second
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula26Correction C P ξ * formula18SecondProduct C P ξ) 1 := by
  let A : Fin C.t → Fin C.t → G := fun p q =>
    D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ
  let F : Fin C.t → Fin C.t → G := fun p q =>
    A p q ^ formula23Coefficient C P p q
  let H : Fin C.t → Fin C.t → G := fun p q =>
    A p q ^ (-formula23Coefficient C P p q)
  have hA : ∀ p q, A p q ∈ D5.gamma G 3 := by
    intro p q
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (C.x2_mem_gamma2 p) (C.x2_mem_gamma2 q)) hξ
  have hF : ∀ p q, p < q → F p q ∈ D5.gamma G 3 := by
    intro p q hpq
    exact (D5.gamma G 3).zpow_mem (hA p q) _
  have hH : ∀ p q, p < q → H p q ∈ D5.gamma G 3 := by
    intro p q hpq
    exact (D5.gamma G 3).zpow_mem (hA p q) _
  have hsecond := formula18_second_collected C P ξ
  refine ((D5.ModEq.refl (D5.gamma G 6) (formula26Correction C P ξ)).mul
    hsecond).trans ?_
  have hcombine := strictPairProduct_pointwise_gammaThree F H hF hH
  have hone : strictPairProduct (fun p q => F p q * H p q) = (1 : G) := by
    unfold strictPairProduct orderedProduct orderedProductWhere
    simp [F, H]
  have hcombine' : D5.ModGammaSix
      (formula26Correction C P ξ * strictPairProduct H)
      (strictPairProduct fun p q => F p q * H p q) := by
    simpa [formula26Correction, A, F] using hcombine
  rw [hone] at hcombine'
  simpa [A, H] using hcombine'

def formula29PairLineOne
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j))
      (C.x1 j)) ξ ^ P.u i j

def formula29PairLineTwo
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ)
      (C.x1 j) ^ (-P.u i j)

def formula29PairLineThree
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ) ξ)
      (C.x1 i ^ orderInt C.d j) ^ P.u i j

def formula29PairLineFour
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ)
      (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j)

def formula29PairLineFive
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 j)) (C.x1 i) ^
      (P.u i j * TaharaArithmetic.binom2 (C.d j))

def formula29PairLineSix
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (C.x1 j) ξ) (C.x1 i)) (C.x1 i) ^
      (-P.u i j * TaharaArithmetic.binom2 (C.d j))

theorem formula29_pair_lines_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    formula29PairLineOne C P ξ i j ∈ D5.gamma G 3 ∧
    formula29PairLineTwo C P ξ i j ∈ D5.gamma G 3 ∧
    formula29PairLineThree C P ξ i j ∈ D5.gamma G 3 ∧
    formula29PairLineFour C P ξ i j ∈ D5.gamma G 3 ∧
    formula29PairLineFive C P ξ i j ∈ D5.gamma G 3 ∧
    formula29PairLineSix C P ξ i j ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hijpow : C.x1 i ^ orderInt C.d j ∈ D5.gamma G 2 :=
    C.x1_later_order_power_mem_gamma2 hij.le
  have hxjξ : D5.paperComm (C.x1 j) ξ ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxj hξ
  have hipowj : D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j) ∈
      D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hijpow hxj
  constructor
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hipowj hxj) hξ
  constructor
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hipowj hξ) hxj
  constructor
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hξ) hijpow
  constructor
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hijpow) hξ
  constructor
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hxj) hxi
  · apply D5.gamma_antitone G (by norm_num : 3 ≤ 4)
    apply (D5.gamma G 4).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hxjξ hxi) hxi

def formula29LineOne (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula29PairLineOne C P ξ)

def formula29LineTwo (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula29PairLineTwo C P ξ)

def formula29LineThree (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula29PairLineThree C P ξ)

def formula29LineFour (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula29PairLineFour C P ξ)

def formula29LineFive (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula29PairLineFive C P ξ)

def formula29LineSix (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula29PairLineSix C P ξ)

/-- The first six displayed products of formula (29), in their printed
order rather than grouped one pair at a time. -/
def formula29FirstSixDisplayed
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  ((formula29LineOne C P ξ * formula29LineTwo C P ξ) *
    (formula29LineThree C P ξ * formula29LineFour C P ξ)) *
  (formula29LineFive C P ξ * formula29LineSix C P ξ)

theorem formula29_first_six_collected
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (strictPairProduct (formula29PairCorrections C P ξ))
      (formula29FirstSixDisplayed C P ξ) := by
  let L1 := formula29PairLineOne C P ξ
  let L2 := formula29PairLineTwo C P ξ
  let L3 := formula29PairLineThree C P ξ
  let L4 := formula29PairLineFour C P ξ
  let L5 := formula29PairLineFive C P ξ
  let L6 := formula29PairLineSix C P ξ
  have hm : ∀ i j, i < j →
      L1 i j ∈ D5.gamma G 3 ∧ L2 i j ∈ D5.gamma G 3 ∧
      L3 i j ∈ D5.gamma G 3 ∧ L4 i j ∈ D5.gamma G 3 ∧
      L5 i j ∈ D5.gamma G 3 ∧ L6 i j ∈ D5.gamma G 3 := by
    intro i j hij
    simpa [L1, L2, L3, L4, L5, L6] using
      formula29_pair_lines_mem_gamma3 C P ξ hij
  have h12 := strictPairProduct_pointwise_gammaThree L1 L2
    (fun i j hij => (hm i j hij).1)
    (fun i j hij => (hm i j hij).2.1)
  have h34 := strictPairProduct_pointwise_gammaThree L3 L4
    (fun i j hij => (hm i j hij).2.2.1)
    (fun i j hij => (hm i j hij).2.2.2.1)
  have h56 := strictPairProduct_pointwise_gammaThree L5 L6
    (fun i j hij => (hm i j hij).2.2.2.2.1)
    (fun i j hij => (hm i j hij).2.2.2.2.2)
  have h1234 := strictPairProduct_pointwise_gammaThree
    (fun i j => L1 i j * L2 i j) (fun i j => L3 i j * L4 i j)
    (fun i j hij => (D5.gamma G 3).mul_mem (hm i j hij).1 (hm i j hij).2.1)
    (fun i j hij => (D5.gamma G 3).mul_mem
      (hm i j hij).2.2.1 (hm i j hij).2.2.2.1)
  have hall := strictPairProduct_pointwise_gammaThree
    (fun i j => (L1 i j * L2 i j) * (L3 i j * L4 i j))
    (fun i j => L5 i j * L6 i j)
    (fun i j hij => (D5.gamma G 3).mul_mem
      ((D5.gamma G 3).mul_mem (hm i j hij).1 (hm i j hij).2.1)
      ((D5.gamma G 3).mul_mem (hm i j hij).2.2.1
        (hm i j hij).2.2.2.1))
    (fun i j hij => (D5.gamma G 3).mul_mem
      (hm i j hij).2.2.2.2.1 (hm i j hij).2.2.2.2.2)
  have hsplit := hall.symm.trans <|
    h1234.symm.mul h56.symm |>.trans <| (h12.symm.mul h34.symm).mul
      (D5.ModEq.refl (D5.gamma G 6)
        (strictPairProduct L5 * strictPairProduct L6))
  simpa [formula29PairCorrections, formula29FirstSixDisplayed,
    formula29LineOne, formula29LineTwo, formula29LineThree,
    formula29LineFour, formula29LineFive, formula29LineSix,
    L1, L2, L3, L4, L5, L6] using hsplit

/-- The twelfth and final displayed product of formula (29). -/
def formula29LineTwelve
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      D5.paperComm
        (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ^
          P.w i j k

/-- All twelve products on the right hand side of formula (29), with the
parentheses made explicit. -/
def formula29DisplayedProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  ((formula29FirstSixDisplayed C P ξ * formula29LineSeven C P ξ) *
    formula28DisplayedProduct C P ξ) * formula29LineTwelve C P ξ

/-- Formulas (22)--(28) inserted into formula (18).  The formula-(26)
correction is moved next to the second product of (18) by one checked
finite permutation and then cancelled. -/
theorem formula18_to_formula29_grouped
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (formula18Expansion C P ξ)
      (((strictPairProduct (formula29PairCorrections C P ξ) *
          formula29LineSeven C P ξ) *
        formula21FinalThirdGrouped C P ξ) * formula29LineTwelve C P ξ) := by
  rcases hP with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15⟩
  have hSat : P.Satisfies :=
    ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  let Q := strictPairProduct (formula29PairCorrections C P ξ)
  let W := formula21WeightTwoPowerProduct C P ξ
  let R := formula21FinalThirdGrouped C P ξ
  let K := formula26Correction C P ξ
  let L := formula29LineSeven C P ξ
  let S := formula18SecondProduct C P ξ
  let T := formula29LineTwelve C P ξ
  have hstart : D5.ModGammaSix (formula18Expansion C P ξ)
      ((Q * (W * R)) * S * T) := by
    simpa [Q, W, R, S, T, strictPairProduct, formula18SecondProduct,
      formula29LineTwelve, mul_assoc] using
        formula18_after_formula19_to_21 C P hSat ξ
  have hW : D5.ModGammaSix W (K * L) := by
    exact (formula21_weight_two_to_formula23_and_line_seven C P ξ).trans <|
      ((transfer_formula23 C P ξ).trans
        (weight_two_block_cancels26 C P h14 h15 ξ)).mul
          (D5.ModEq.refl (D5.gamma G 6) (formula29LineSeven C P ξ))
  have hreplaced : D5.ModGammaSix (formula18Expansion C P ξ)
      ((Q * ((K * L) * R)) * S * T) :=
    hstart.trans <| (((D5.ModEq.refl (D5.gamma G 6) Q).mul
      (hW.mul (D5.ModEq.refl (D5.gamma G 6) R))).mul
        (D5.ModEq.refl (D5.gamma G 6) S)).mul
          (D5.ModEq.refl (D5.gamma G 6) T)
  have hQ : Q ∈ D5.gamma G 3 := by
    dsimp [Q]
    unfold strictPairProduct
    apply orderedProduct_mem
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact formula29_pair_corrections_mem_gamma3 C P ξ hij
  have hK : K ∈ D5.gamma G 3 := by
    dsimp [K]
    unfold formula26Correction strictPairProduct
    apply orderedProduct_mem
    intro p
    apply orderedProductWhere_mem
    intro q hpq
    apply (D5.gamma G 3).zpow_mem
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (C.x2_mem_gamma2 p) (C.x2_mem_gamma2 q)) hξ
  have hL : L ∈ D5.gamma G 3 := by
    dsimp [L]
    unfold formula29LineSeven
    apply orderedProduct_mem
    intro j
    exact formula22_correction_mem_gamma3 C P ξ j
  have hR : R ∈ D5.gamma G 3 := by
    dsimp [R]
    unfold formula21FinalThirdGrouped
    apply orderedProduct_mem
    intro i
    exact formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _
  have hS : S ∈ D5.gamma G 3 := by
    dsimp [S]
    unfold formula18SecondProduct
    apply orderedProduct_mem
    intro i
    apply orderedProduct_mem
    intro p
    apply orderedProductWhere_mem
    intro q hpq
    apply (D5.gamma G 3).zpow_mem
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (C.x2_mem_gamma2 q) (C.x2_mem_gamma2 p)) hξ
  have hT : T ∈ D5.gamma G 3 := by
    dsimp [T]
    unfold formula29LineTwelve
    apply orderedProduct_mem
    intro i
    apply orderedProductWhere_mem
    intro j hij
    apply orderedProductWhere_mem
    intro k hjk
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    have hinner : D5.leftComm (C.x1 i ^ orderInt C.d i)
        [C.x1 j, C.x1 k] ∈ D5.gamma G 4 := by
      simpa using D5.leftComm_mem_gamma_of_first (r := 2) (by norm_num)
        (C.x1_order_power_mem_gamma2 i) [C.x1 j, C.x1 k]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hinner hξ
  have hp : [Q, K, L, R, S, T].Perm [Q, L, R, K, S, T] := by
    apply List.Perm.cons Q
    have hswap : ([K] ++ [L, R]).Perm ([L, R] ++ [K]) :=
      List.perm_append_comm
    simpa only [List.append_assoc] using hswap.append_right [S, T]
  have hperm := D5.listProd_perm_gammaThree hp (fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | hx
    · exact hQ
    · exact hK
    · exact hL
    · exact hR
    · exact hS
    · rcases hx with rfl | hx
      · exact hT
      · simpa using hx)
  have hcancel := formula26_cancels_formula18_second C P ξ
  have hfinish : D5.ModGammaSix ([Q, L, R, K, S, T].prod)
      ([Q, L, R, T].prod) := by
    simpa [List.prod_cons, List.prod_nil, mul_assoc] using
      (((D5.ModEq.refl (D5.gamma G 6) ((Q * L) * R)).mul hcancel).mul
        (D5.ModEq.refl (D5.gamma G 6) T))
  exact hreplaced.trans <| by
    simpa [List.prod_cons, List.prod_nil, mul_assoc, Q, K, L, R, S, T] using
      hperm.trans hfinish

/-- Formula (29) exactly as twelve finite products.  Every exponent, sign,
index restriction and reordering in Section 10 is included in the checked
term. -/
theorem formula29
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (D5.paperComm (word C P) ξ)
      (formula29DisplayedProduct C P ξ) := by
  rcases hP with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15⟩
  have hSat : P.Satisfies :=
    ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hgrouped := (commutator_representative_formula18 C P ξ).trans
    (formula18_to_formula29_grouped C P hSat ξ)
  have hthird := (formula27 C P h13 ξ).trans (formula28 C P ξ)
  have hreplace : D5.ModGammaSix
      (((strictPairProduct (formula29PairCorrections C P ξ) *
          formula29LineSeven C P ξ) * formula21FinalThirdGrouped C P ξ) *
        formula29LineTwelve C P ξ)
      (((strictPairProduct (formula29PairCorrections C P ξ) *
          formula29LineSeven C P ξ) * formula28DisplayedProduct C P ξ) *
        formula29LineTwelve C P ξ) :=
    (((D5.ModEq.refl (D5.gamma G 6)
      (strictPairProduct (formula29PairCorrections C P ξ) *
        formula29LineSeven C P ξ)).mul hthird).mul
          (D5.ModEq.refl (D5.gamma G 6) (formula29LineTwelve C P ξ)))
  exact hgrouped.trans <| hreplace.trans <| by
    simpa [formula29DisplayedProduct] using
      ((formula29_first_six_collected C P ξ).mul
        (D5.ModEq.refl (D5.gamma G 6) (formula29LineSeven C P ξ))).mul
          (D5.ModEq.refl (D5.gamma G 6) (formula28DisplayedProduct C P ξ)) |>.mul
            (D5.ModEq.refl (D5.gamma G 6) (formula29LineTwelve C P ξ))

end

end D5.Tahara
