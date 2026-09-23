import D5.Section11

/-!
# Section 11: the Jacobi collection in formula (34)

This file proves the remaining local five-factor Jacobi calculation used for
the `w i j k` stream.  The four correction terms in the general
Hall--Witt rotation are discarded only after their weight has been checked
to be at least six.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- If the four weight-five corrections in formula (19) already lie in
`γ₆`, the formula reduces to its two leading Jacobi terms modulo `γ₆`. -/
theorem rotation_main_mod_gamma_six_of_corrections
    {a b c : G}
    (ha : a ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 1)
    (hc : c ∈ D5.gamma G 1)
    (hD : D5.paperComm (D5.paperComm (D5.paperComm a b) b) c ∈
      D5.gamma G 6)
    (hE : D5.paperComm (D5.paperComm (D5.paperComm a b) c) b ∈
      D5.gamma G 6)
    (hF : D5.paperComm (D5.paperComm (D5.paperComm b c) c) a ∈
      D5.gamma G 6)
    (hH : D5.paperComm (D5.paperComm (D5.paperComm b c) a) c ∈
      D5.gamma G 6) :
    D5.ModGammaSix (D5.paperComm (D5.paperComm a b) c)
      ((D5.paperComm (D5.paperComm c a) b)⁻¹ *
        D5.paperComm (D5.paperComm c b) a) := by
  let C := D5.paperComm (D5.paperComm c a) b
  let B := D5.paperComm (D5.paperComm c b) a
  let D := D5.paperComm (D5.paperComm (D5.paperComm a b) b) c
  let E := D5.paperComm (D5.paperComm (D5.paperComm a b) c) b
  let F := D5.paperComm (D5.paperComm (D5.paperComm b c) c) a
  let H := D5.paperComm (D5.paperComm (D5.paperComm b c) a) c
  have hrot := D5.rotation_formula19 ha hb hc
  have htail : D5.ModGammaSix
      (C⁻¹ * B * D * E⁻¹ * F * H⁻¹) (C⁻¹ * B) := by
    have hD1 : D5.ModGammaSix D 1 :=
      D5.modEq_one_iff_mem.mpr (by simpa [D] using hD)
    have hE1 : D5.ModGammaSix E⁻¹ 1 :=
      D5.modEq_one_iff_mem.mpr ((D5.gamma G 6).inv_mem (by simpa [E] using hE))
    have hF1 : D5.ModGammaSix F 1 :=
      D5.modEq_one_iff_mem.mpr (by simpa [F] using hF)
    have hH1 : D5.ModGammaSix H⁻¹ 1 :=
      D5.modEq_one_iff_mem.mpr ((D5.gamma G 6).inv_mem (by simpa [H] using hH))
    simpa only [mul_assoc, mul_one] using
      ((((D5.ModEq.refl (D5.gamma G 6) (C⁻¹ * B)).mul hD1).mul hE1).mul hF1).mul hH1
  simpa [C, B, D, E, F, H] using hrot.trans htail

/-- Weight pattern `(3,1,1)`: all four formula-(19) corrections have
weight at least six. -/
theorem rotation_main_mod_gamma_six_311
    {a b c : G} (ha : a ∈ D5.gamma G 3)
    (hb : b ∈ D5.gamma G 1) (hc : c ∈ D5.gamma G 1) :
    D5.ModGammaSix (D5.paperComm (D5.paperComm a b) c)
      ((D5.paperComm (D5.paperComm c a) b)⁻¹ *
        D5.paperComm (D5.paperComm c b) a) := by
  apply rotation_main_mod_gamma_six_of_corrections
    (D5.gamma_antitone G (by norm_num) ha) hb hc
  · exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb) hb) hc
  · exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb) hc) hb
  · exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hc) hc) ha
  · exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hc) ha) hc

/-- Weight pattern `(2,1,2)`: again all formula-(19) corrections vanish
modulo `γ₆`. -/
theorem rotation_main_mod_gamma_six_212
    {a b c : G} (ha : a ∈ D5.gamma G 2)
    (hb : b ∈ D5.gamma G 1) (hc : c ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm (D5.paperComm a b) c)
      ((D5.paperComm (D5.paperComm c a) b)⁻¹ *
        D5.paperComm (D5.paperComm c b) a) := by
  apply rotation_main_mod_gamma_six_of_corrections ha hb
    (D5.gamma_antitone G (by norm_num) hc)
  · exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb) hb) hc
  · exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb) hc) hb
  · exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hc) hc) ha
  · exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hc) ha) hc

/-- Derivation form of Jacobi in weights `(1,2,1)`, one level before the
final truncation. -/
theorem right_nested_jacobi_mod_gamma_five
    {x a c : G} (hx : x ∈ D5.gamma G 1)
    (ha : a ∈ D5.gamma G 2) (hc : c ∈ D5.gamma G 1) :
    D5.ModEq (D5.gamma G 5) (D5.paperComm x (D5.paperComm a c))
      (D5.paperComm (D5.paperComm x a) c *
        (D5.paperComm (D5.paperComm x c) a)⁻¹) := by
  let A := D5.paperComm (D5.paperComm x a) c
  let B := D5.paperComm (D5.paperComm x c) a
  have hA : A ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hx ha) hc
  have hB : B ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hx hc) ha
  have hrot := D5.rotation_main_mod_gamma_five ha hc hx
  rw [D5.paperComm_swap x (D5.paperComm a c)] at hrot
  have hinv : D5.ModEq (D5.gamma G 5)
      (D5.paperComm x (D5.paperComm a c)) (B⁻¹ * A) := by
    simpa [A, B] using hrot.inv
  have hcomm : D5.ModEq (D5.gamma G 5) (B⁻¹ * A) (A * B⁻¹) :=
    D5.mul_comm_mod_gamma (n := 5) (r := 4) (s := 4)
      (by norm_num) (by norm_num) (by norm_num)
      ((D5.gamma G 4).inv_mem hB) hA
  simpa [A, B] using hinv.trans hcomm

/-- The same derivation identity in total weight five. -/
theorem right_nested_jacobi_mod_gamma_six
    {x a c : G} (hx : x ∈ D5.gamma G 2)
    (ha : a ∈ D5.gamma G 2) (hc : c ∈ D5.gamma G 1) :
    D5.ModGammaSix (D5.paperComm x (D5.paperComm a c))
      (D5.paperComm (D5.paperComm x a) c *
        (D5.paperComm (D5.paperComm x c) a)⁻¹) := by
  let A := D5.paperComm (D5.paperComm x a) c
  let B := D5.paperComm (D5.paperComm x c) a
  have hA : A ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hx ha) hc
  have hB : B ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hx hc) ha
  have hrot := rotation_main_mod_gamma_six_212 ha hc hx
  rw [D5.paperComm_swap x (D5.paperComm a c)] at hrot
  have hinv : D5.ModGammaSix
      (D5.paperComm x (D5.paperComm a c)) (B⁻¹ * A) := by
    simpa [A, B] using hrot.inv
  have hcomm : D5.ModGammaSix (B⁻¹ * A) (A * B⁻¹) :=
    D5.mul_comm_mod_gamma (n := 6) (r := 5) (s := 5)
      (by norm_num) (by norm_num) (by norm_num)
      ((D5.gamma G 5).inv_mem hB) hA
  simpa [A, B] using hinv.trans hcomm

/-- The five-factor Jacobi identity printed after formula (36).  It is the
local transformation applied to every coefficient `w i j k`. -/
theorem formula34_w_jacobi
    {a b ξ c : G}
    (ha : a ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 1)
    (hξ : ξ ∈ D5.gamma G 1) (hc : c ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (((D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c)⁻¹ *
          (D5.paperComm (D5.paperComm (D5.paperComm a c) ξ) b)⁻¹) *
        D5.paperComm (D5.paperComm (D5.paperComm a c) b) ξ)
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a) b) c *
        (D5.paperComm (D5.paperComm (D5.paperComm ξ b) c) a)⁻¹) := by
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ a) b) c
  let B := D5.paperComm (D5.paperComm (D5.paperComm ξ b) a) c
  let C := D5.paperComm (D5.paperComm (D5.paperComm ξ a) c) b
  let D := D5.paperComm (D5.paperComm (D5.paperComm ξ c) a) b
  let Z := D5.paperComm (D5.paperComm (D5.paperComm ξ b) c) a
  let E := D5.paperComm (D5.paperComm (D5.paperComm a c) b) ξ
  have h1 : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c)⁻¹
      (A * B⁻¹) := by
    simpa [A, B] using formula34_wprime_jacobi ha hb hξ hc
  have h2 : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm a c) ξ) b)⁻¹
      (C * D⁻¹) := by
    simpa [C, D] using formula34_wprime_jacobi ha hc hξ hb
  have hac : D5.paperComm a c ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hc
  have hrotE := rotation_main_mod_gamma_six_311 hac hb hξ
  have hU0 := right_nested_jacobi_mod_gamma_five hξ ha hc
  have hU1 := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hU0 hb
  have hξa_c : D5.paperComm (D5.paperComm ξ a) c ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha) hc
  have hξc_a : D5.paperComm (D5.paperComm ξ c) a ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hc) ha
  have hUsplit : D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm (D5.paperComm ξ a) c *
          (D5.paperComm (D5.paperComm ξ c) a)⁻¹) b)
      (C * D⁻¹) := by
    have hs := D5.paperComm_mul_left_mod_gamma
      (n := 6) (r := 4) (s := 4) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hξa_c ((D5.gamma G 4).inv_mem hξc_a) hb
    have hi := D5.paperComm_inv_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hξc_a hb
    simpa [C, D] using hs.trans
      ((D5.ModEq.refl (D5.gamma G 6)
        (D5.paperComm (D5.paperComm (D5.paperComm ξ a) c) b)).mul hi)
  have hU : D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (D5.paperComm a c)) b)
      (C * D⁻¹) := hU1.trans hUsplit
  have hxb : D5.paperComm ξ b ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hb
  have hV : D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ b) (D5.paperComm a c))
      (B * Z⁻¹) := by
    simpa [B, Z] using right_nested_jacobi_mod_gamma_six hxb ha hc
  have hE : D5.ModGammaSix E ((D * C⁻¹) * (B * Z⁻¹)) := by
    have hUi : D5.ModGammaSix
        (D5.paperComm (D5.paperComm ξ (D5.paperComm a c)) b)⁻¹
        (D * C⁻¹) := by
      simpa using hU.inv
    simpa [E] using hrotE.trans (hUi.mul hV)
  have hall : D5.ModGammaSix
      (((D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c)⁻¹ *
          (D5.paperComm (D5.paperComm (D5.paperComm a c) ξ) b)⁻¹) * E)
      (((A * B⁻¹) * (C * D⁻¹)) * ((D * C⁻¹) * (B * Z⁻¹))) :=
    (h1.mul h2).mul hE
  refine hall.trans ?_
  have heq : ((A * B⁻¹) * (C * D⁻¹)) *
      ((D * C⁻¹) * (B * Z⁻¹)) = A * Z⁻¹ := by
    group
  rw [heq]

/-! ## Exact powered factors used in the finite products -/

def formula34WSourceFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  ((D5.paperComm (D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) (C.x1 k)) ξ)
        (C.x1 j) ^ (-P.w i j k)) *
    (D5.paperComm (D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) (C.x1 j)) ξ)
        (C.x1 k) ^ (-P.w i j k))) *
    D5.paperComm
      (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ^
        P.w i j k

def formula34WExtraFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 k))
      (C.x1 j) ^ P.w i j k

def formula34WMainFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 k)) (C.x1 j))
      (C.x1 i ^ orderInt C.d i) ^ (-P.w i j k)

/-- The powered `w i j k` factor: all three source factors are combined
before the local Jacobi identity is applied. -/
theorem formula34_w_powered
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    D5.ModGammaSix (formula34WSourceFactor C P ξ i j k)
      (formula34WExtraFactor C P ξ i j k *
        formula34WMainFactor C P ξ i j k) := by
  let a := C.x1 i ^ orderInt C.d i
  let b := C.x1 k
  let c := C.x1 j
  let X := D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c
  let Y := D5.paperComm (D5.paperComm (D5.paperComm a c) ξ) b
  let E := D5.paperComm (D5.paperComm (D5.paperComm a c) b) ξ
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ a) b) c
  let Z := D5.paperComm (D5.paperComm (D5.paperComm ξ b) c) a
  let m := P.w i j k
  have ha : a ∈ D5.gamma G 2 := C.x1_order_power_mem_gamma2 i
  have hb : b ∈ D5.gamma G 1 := by simp [b, D5.gamma]
  have hc : c ∈ D5.gamma G 1 := by simp [c, D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb) hξ) hc
  have hY : Y ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hc) hξ) hb
  have hE : E ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hc) hb) hξ
  have hA : A ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha) hb) hc
  have hZ : Z ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hb) hc) ha
  have hjac : D5.ModGammaSix ((X⁻¹ * Y⁻¹) * E) (A * Z⁻¹) := by
    simpa [X, Y, E, A, Z] using formula34_w_jacobi ha hb hξ hc
  have hXY := D5.gammaThree_mul_zpow
    (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hX))
    (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hY)) m
  have hsource0 := D5.gammaThree_mul_zpow
    ((D5.gamma G 3).mul_mem
      (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hX))
      (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hY)))
    (D5.gamma_antitone G (by norm_num) hE) m
  have hsource : D5.ModGammaSix (((X⁻¹ * Y⁻¹) * E) ^ m)
      ((X ^ (-m) * Y ^ (-m)) * E ^ m) := by
    exact hsource0.trans <| by
      simpa [inv_zpow, zpow_neg] using
        hXY.mul (D5.ModEq.refl (D5.gamma G 6) (E ^ m))
  have htarget := D5.gammaThree_mul_zpow
    (D5.gamma_antitone G (by norm_num) hA)
    (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hZ)) m
  have htarget' : D5.ModGammaSix ((A * Z⁻¹) ^ m)
      (A ^ m * Z ^ (-m)) := by
    simpa [inv_zpow, zpow_neg] using htarget
  simpa [formula34WSourceFactor, formula34WExtraFactor,
    formula34WMainFactor, a, b, c, X, Y, E, A, Z, m] using
      hsource.symm.trans ((hjac.zpow m).trans htarget')

def formula34WPrimeSourceFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 j ^ orderInt C.d j) (C.x1 k)) ξ)
      (C.x1 i) ^ (-P.w' i j k)

def formula34WPrimeExtraFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 k))
      (C.x1 i) ^ P.w' i j k

def formula34WPrimeMainFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 k)) (C.x1 j ^ orderInt C.d j))
      (C.x1 i) ^ (-P.w' i j k)

/-- Powered specialization of the printed `w' i j k` Jacobi identity. -/
theorem formula34_wprime_powered
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    D5.ModGammaSix (formula34WPrimeSourceFactor C P ξ i j k)
      (formula34WPrimeExtraFactor C P ξ i j k *
        formula34WPrimeMainFactor C P ξ i j k) := by
  let a := C.x1 j ^ orderInt C.d j
  let b := C.x1 k
  let c := C.x1 i
  let X := D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ a) b) c
  let B := D5.paperComm (D5.paperComm (D5.paperComm ξ b) a) c
  let m := P.w' i j k
  have ha : a ∈ D5.gamma G 2 := C.x1_order_power_mem_gamma2 j
  have hb : b ∈ D5.gamma G 1 := by simp [b, D5.gamma]
  have hc : c ∈ D5.gamma G 1 := by simp [c, D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : A ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha) hb) hc
  have hB : B ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hb) ha) hc
  have hjac : D5.ModGammaSix X⁻¹ (A * B⁻¹) := by
    simpa [X, A, B] using formula34_wprime_jacobi ha hb hξ hc
  have htarget := D5.gammaThree_mul_zpow
    (D5.gamma_antitone G (by norm_num) hA)
    (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hB)) m
  have htarget' : D5.ModGammaSix ((A * B⁻¹) ^ m)
      (A ^ m * B ^ (-m)) := by
    simpa [inv_zpow, zpow_neg] using htarget
  have hp := (hjac.zpow m).trans htarget'
  have hleft : X ^ (-m) = (X⁻¹) ^ m := by
    rw [inv_zpow, zpow_neg]
  have hp' : D5.ModGammaSix (X ^ (-m)) (A ^ m * B ^ (-m)) := by
    rw [hleft]
    exact hp
  simpa only [formula34WPrimeSourceFactor, formula34WPrimeExtraFactor,
    formula34WPrimeMainFactor, a, b, c, X, A, B, m] using hp'

def formula34WPrimeExtraProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      formula34WPrimeExtraFactor C P ξ i j k

/-- The second principal product displayed in (34). -/
def formula34WPrimeMainProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      formula34WPrimeMainFactor C P ξ i j k

theorem formula34WPrimeExtraFactor_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    formula34WPrimeExtraFactor C P ξ i j k ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ^ orderInt C.d j ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 j
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h3 : D5.paperComm ξ (C.x1 j ^ orderInt C.d j) ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (r := 1) (s := 2)
      (by norm_num) (by norm_num) hξ hj
  have h4 : D5.paperComm
      (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 k) ∈
      D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) h3 hk
  have h5 : D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 k))
      (C.x1 i) ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) h4 hi
  exact D5.gamma_antitone G (by norm_num : 3 ≤ 5) <|
    (D5.gamma G 5).zpow_mem h5 _

theorem formula34WPrimeMainFactor_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    formula34WPrimeMainFactor C P ξ i j k ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ^ orderInt C.d j ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 j
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h2 : D5.paperComm ξ (C.x1 k) ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (r := 1) (s := 1)
      (by norm_num) (by norm_num) hξ hk
  have h4 : D5.paperComm (D5.paperComm ξ (C.x1 k))
      (C.x1 j ^ orderInt C.d j) ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (r := 2) (s := 2)
      (by norm_num) (by norm_num) h2 hj
  have h5 : D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 k)) (C.x1 j ^ orderInt C.d j))
      (C.x1 i) ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) h4 hi
  exact D5.gamma_antitone G (by norm_num : 3 ≤ 5) <|
    (D5.gamma G 5).zpow_mem h5 _

/-- The complete `w'` stream from line 11 of (29), transformed and separated
into its additional stream and the second principal stream of (34). -/
theorem formula34_wprime_stream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula28WPrimeDisplayedStream C P ξ)
      (formula34WPrimeExtraProduct C P ξ *
        formula34WPrimeMainProduct C P ξ) := by
  let E : Fin C.s → Fin C.s → Fin C.s → G :=
    formula34WPrimeExtraFactor C P ξ
  let M : Fin C.s → Fin C.s → Fin C.s → G :=
    formula34WPrimeMainFactor C P ξ
  have hE : ∀ i j k, E i j k ∈ D5.gamma G 3 := by
    intro i j k
    exact formula34WPrimeExtraFactor_mem_gamma3 C P ξ i j k
  have hM : ∀ i j k, M i j k ∈ D5.gamma G 3 := by
    intro i j k
    exact formula34WPrimeMainFactor_mem_gamma3 C P ξ i j k
  have hlocal : D5.ModGammaSix (formula28WPrimeDisplayedStream C P ξ)
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => E i j k * M i j k) := by
    unfold formula28WPrimeDisplayedStream
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    apply modEq_orderedProductWhere
    intro k hjk
    simpa [formula34WPrimeSourceFactor, E, M] using
      formula34_wprime_powered C P ξ i j k
  have hsplitK : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => E i j k * M i j k)
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        (orderedProductWhere (j ≤ ·) fun k => E i j k) *
          (orderedProductWhere (j ≤ ·) fun k => M i j k)) := by
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    exact D5.orderedProductWhere_pointwise_mul_gammaThree (j ≤ ·)
      (E i j) (M i j) (fun k h => hE i j k) (fun k h => hM i j k)
  let ER : Fin C.s → Fin C.s → G := fun i j =>
    orderedProductWhere (j ≤ ·) fun k => E i j k
  let MR : Fin C.s → Fin C.s → G := fun i j =>
    orderedProductWhere (j ≤ ·) fun k => M i j k
  have hER : ∀ i j, ER i j ∈ D5.gamma G 3 := by
    intro i j
    apply orderedProductWhere_mem
    intro k hjk
    exact hE i j k
  have hMR : ∀ i j, MR i j ∈ D5.gamma G 3 := by
    intro i j
    apply orderedProductWhere_mem
    intro k hjk
    exact hM i j k
  have hsplitJ : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        ER i j * MR i j)
      (orderedProduct fun i =>
        (orderedProductWhere (i < ·) fun j => ER i j) *
          (orderedProductWhere (i < ·) fun j => MR i j)) := by
    apply modEq_orderedProduct
    intro i
    exact D5.orderedProductWhere_pointwise_mul_gammaThree (i < ·)
      (ER i) (MR i) (fun j h => hER i j) (fun j h => hMR i j)
  let EB : Fin C.s → G := fun i =>
    orderedProductWhere (i < ·) fun j => ER i j
  let MB : Fin C.s → G := fun i =>
    orderedProductWhere (i < ·) fun j => MR i j
  have hEB : ∀ i, EB i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hER i j
  have hMB : ∀ i, MB i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hMR i j
  have hsplitI : D5.ModGammaSix
      (orderedProduct fun i => EB i * MB i)
      (orderedProduct EB * orderedProduct MB) :=
    D5.orderedProduct_pointwise_mul_gammaThree EB MB hEB hMB
  exact hlocal.trans <| hsplitK.trans <| by
    simpa [ER, MR] using hsplitJ.trans <| by
      simpa [EB, MB, ER, MR, formula34WPrimeExtraProduct,
        formula34WPrimeMainProduct, E, M] using hsplitI

def formula34WCanonicalSourceProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      formula34WSourceFactor C P ξ i j k

def formula34WExtraProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      formula34WExtraFactor C P ξ i j k

/-- The first principal product displayed in (34). -/
def formula34WMainProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      formula34WMainFactor C P ξ i j k

theorem formula34WExtraFactor_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    formula34WExtraFactor C P ξ i j k ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 i
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h3 : D5.paperComm ξ (C.x1 i ^ orderInt C.d i) ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (r := 1) (s := 2)
      (by norm_num) (by norm_num) hξ hi
  have h4 : D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 k) ∈
      D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) h3 hk
  have h5 : D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 k))
      (C.x1 j) ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) h4 hj
  exact D5.gamma_antitone G (by norm_num : 3 ≤ 5) <|
    (D5.gamma G 5).zpow_mem h5 _

theorem formula34WMainFactor_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    formula34WMainFactor C P ξ i j k ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 i
  have h2 : D5.paperComm ξ (C.x1 k) ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (r := 1) (s := 1)
      (by norm_num) (by norm_num) hξ hk
  have h3 : D5.paperComm (D5.paperComm ξ (C.x1 k)) (C.x1 j) ∈
      D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (r := 2) (s := 1)
      (by norm_num) (by norm_num) h2 hj
  have h5 : D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 k)) (C.x1 j))
      (C.x1 i ^ orderInt C.d i) ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (r := 3) (s := 2)
      (by norm_num) (by norm_num) h3 hi
  exact D5.gamma_antitone G (by norm_num : 3 ≤ 5) <|
    (D5.gamma G 5).zpow_mem h5 _

/-- Formula (34) for the canonical `i ≤ j ≤ k` product.  The remaining
connection to lines 9, 10 and 12 of (29) is purely finite reindexing. -/
theorem formula34_w_canonical_product
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula34WCanonicalSourceProduct C P ξ)
      (formula34WExtraProduct C P ξ * formula34WMainProduct C P ξ) := by
  let E : Fin C.s → Fin C.s → Fin C.s → G := formula34WExtraFactor C P ξ
  let M : Fin C.s → Fin C.s → Fin C.s → G := formula34WMainFactor C P ξ
  have hE : ∀ i j k, E i j k ∈ D5.gamma G 3 := by
    intro i j k
    exact formula34WExtraFactor_mem_gamma3 C P ξ i j k
  have hM : ∀ i j k, M i j k ∈ D5.gamma G 3 := by
    intro i j k
    exact formula34WMainFactor_mem_gamma3 C P ξ i j k
  have hlocal : D5.ModGammaSix (formula34WCanonicalSourceProduct C P ξ)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => E i j k * M i j k) := by
    unfold formula34WCanonicalSourceProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    apply modEq_orderedProductWhere
    intro k hjk
    exact formula34_w_powered C P ξ i j k
  have hsplitK : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => E i j k * M i j k)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        (orderedProductWhere (j ≤ ·) fun k => E i j k) *
          (orderedProductWhere (j ≤ ·) fun k => M i j k)) := by
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    exact D5.orderedProductWhere_pointwise_mul_gammaThree (j ≤ ·)
      (E i j) (M i j) (fun k h => hE i j k) (fun k h => hM i j k)
  let ER : Fin C.s → Fin C.s → G := fun i j =>
    orderedProductWhere (j ≤ ·) fun k => E i j k
  let MR : Fin C.s → Fin C.s → G := fun i j =>
    orderedProductWhere (j ≤ ·) fun k => M i j k
  have hER : ∀ i j, ER i j ∈ D5.gamma G 3 := by
    intro i j
    apply orderedProductWhere_mem
    intro k hjk
    exact hE i j k
  have hMR : ∀ i j, MR i j ∈ D5.gamma G 3 := by
    intro i j
    apply orderedProductWhere_mem
    intro k hjk
    exact hM i j k
  have hsplitJ : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j => ER i j * MR i j)
      (orderedProduct fun i =>
        (orderedProductWhere (i ≤ ·) fun j => ER i j) *
          (orderedProductWhere (i ≤ ·) fun j => MR i j)) := by
    apply modEq_orderedProduct
    intro i
    exact D5.orderedProductWhere_pointwise_mul_gammaThree (i ≤ ·)
      (ER i) (MR i) (fun j h => hER i j) (fun j h => hMR i j)
  let EB : Fin C.s → G := fun i => orderedProductWhere (i ≤ ·) fun j => ER i j
  let MB : Fin C.s → G := fun i => orderedProductWhere (i ≤ ·) fun j => MR i j
  have hEB : ∀ i, EB i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hER i j
  have hMB : ∀ i, MB i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hMR i j
  have hsplitI : D5.ModGammaSix
      (orderedProduct fun i => EB i * MB i)
      (orderedProduct EB * orderedProduct MB) :=
    D5.orderedProduct_pointwise_mul_gammaThree EB MB hEB hMB
  exact hlocal.trans <| hsplitK.trans <| by
    simpa [ER, MR] using hsplitJ.trans <| by
      simpa [EB, MB, ER, MR, formula34WExtraProduct,
        formula34WMainProduct, E, M] using hsplitI

/-! ## Finite reindexing of the three `w` streams -/

/-- Reindex a weak upper triangle from the loop order `(j,i,k)` to
`(i,j,k)`.  This is the permutation needed for line 9 of (29). -/
theorem tripleProduct_reindex_jik
    {s : ℕ} (f : Fin s → Fin s → Fin s → G)
    (hf : ∀ i j k, i ≤ j → j ≤ k → f i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun j => orderedProductWhere (· ≤ j) fun i =>
        orderedProductWhere (j ≤ ·) fun k => f i j k)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k) := by
  classical
  let all := List.finRange s
  let triples :=
    ((((all ×ˢ all).filter fun ij => ij.1 ≤ ij.2) ×ˢ all).filter fun t =>
      t.1.2 ≤ t.2)
  let raw :=
    ((((all ×ˢ all).filter fun ji => ji.2 ≤ ji.1) ×ˢ all).filter fun t =>
      t.1.1 ≤ t.2)
  let swap : (Fin s × Fin s) × Fin s → (Fin s × Fin s) × Fin s :=
    fun t => ((t.1.2, t.1.1), t.2)
  let reordered := raw.map swap
  have hall : all.Nodup := by simpa [all] using List.nodup_finRange s
  have hbase : ((all ×ˢ all) ×ˢ all).Nodup := (hall.product hall).product hall
  have hswap : Function.Injective swap := by
    intro a b h
    apply_fun swap at h
    simpa [swap] using h
  have htriples : triples.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hraw : raw.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hreordered : reordered.Nodup := hraw.map hswap
  have hperm : triples.Perm reordered := by
    apply (List.perm_ext_iff_of_nodup htriples hreordered).2
    intro t
    constructor
    · intro ht
      have hp := List.mem_filter.mp ht
      have hpij := List.mem_product.mp hp.1
      have hij := of_decide_eq_true (List.mem_filter.mp hpij.1).2
      have hjk := of_decide_eq_true hp.2
      apply List.mem_map.mpr
      refine ⟨swap t, ?_, by simp [swap]⟩
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, hpij.2⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [swap] using hij⟩
      · simpa [swap] using hjk
    · intro ht
      rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
      have hp := List.mem_filter.mp hu
      have hpji := List.mem_product.mp hp.1
      have hji := of_decide_eq_true (List.mem_filter.mp hpji.1).2
      have hjk := of_decide_eq_true hp.2
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, hpji.2⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [swap] using hji⟩
      · simpa [swap] using hjk
  have flattenFiltered : ∀ {α β : Type} (is : List α) (js : List β)
      (p : α → β → Prop) [DecidableRel p] (g : α → β → G),
      (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
        (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
          fun ij => g ij.1 ij.2).prod := by
    intro α β is js p inst g
    induction is with
    | nil => simp
    | cons i is ih =>
        rw [List.map_cons, List.prod_cons, List.product_cons,
          List.filter_append, List.map_append, List.prod_append, ih]
        congr 1
        have hlist :
            (js.filter (p i)).map (g i) =
              ((js.map fun b => (i, b)).filter fun ij => p ij.1 ij.2).map
                fun ij => g ij.1 ij.2 := by
          simp only [List.filter_map, List.map_map]
          rfl
        exact congrArg List.prod hlist
  have hcanonical :
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k) =
      (triples.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun i j => i ≤ j)
      (fun i j => ((all.filter (j ≤ ·)).map fun k => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun ij => ij.1 ≤ ij.2) all
      (fun ij k => ij.2 ≤ k) (fun ij k => f ij.1 ij.2 k)
    simpa [triples, all] using h1.trans h2
  have hleft :
      (orderedProduct fun j => orderedProductWhere (· ≤ j) fun i =>
        orderedProductWhere (j ≤ ·) fun k => f i j k) =
      (reordered.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun j i => i ≤ j)
      (fun j i => ((all.filter (j ≤ ·)).map fun k => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun ji => ji.2 ≤ ji.1) all
      (fun ji k => ji.1 ≤ k) (fun ji k => f ji.2 ji.1 k)
    simpa [reordered, raw, swap, all, List.map_map] using h1.trans h2
  rw [hleft, hcanonical]
  apply D5.listProd_perm_gammaThree (hperm.symm.map _)
  intro x hx
  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
  have ht' : t ∈ triples := hperm.mem_iff.mpr ht
  have hp := List.mem_filter.mp ht'
  have hpij := List.mem_product.mp hp.1
  have hij := of_decide_eq_true (List.mem_filter.mp hpij.1).2
  have hjk := of_decide_eq_true hp.2
  exact hf t.1.1 t.1.2 t.2 hij hjk

/-- Reindex the same triangle from loop order `(k,i,j)` to `(i,j,k)`.
This is the permutation needed for line 10 of (29). -/
theorem tripleProduct_reindex_kij
    {s : ℕ} (f : Fin s → Fin s → Fin s → G)
    (hf : ∀ i j k, i ≤ j → j ≤ k → f i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun k => orderedProductWhere (· ≤ k) fun i =>
        orderedProductWhere (fun j => i ≤ j ∧ j ≤ k) fun j => f i j k)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k) := by
  classical
  let all := List.finRange s
  let triples :=
    ((((all ×ˢ all).filter fun ij => ij.1 ≤ ij.2) ×ˢ all).filter fun t =>
      t.1.2 ≤ t.2)
  let raw :=
    ((((all ×ˢ all).filter fun ki => ki.2 ≤ ki.1) ×ˢ all).filter fun t =>
      t.1.2 ≤ t.2 ∧ t.2 ≤ t.1.1)
  let rotate : (Fin s × Fin s) × Fin s → (Fin s × Fin s) × Fin s :=
    fun t => ((t.1.2, t.2), t.1.1)
  let unrotate : (Fin s × Fin s) × Fin s → (Fin s × Fin s) × Fin s :=
    fun t => ((t.2, t.1.1), t.1.2)
  let reordered := raw.map rotate
  have hall : all.Nodup := by simpa [all] using List.nodup_finRange s
  have hrotate : Function.Injective rotate := by
    intro a b h
    apply_fun unrotate at h
    simpa [rotate, unrotate] using h
  have htriples : triples.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hraw : raw.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hreordered : reordered.Nodup := hraw.map hrotate
  have hperm : triples.Perm reordered := by
    apply (List.perm_ext_iff_of_nodup htriples hreordered).2
    intro t
    constructor
    · intro ht
      have hp := List.mem_filter.mp ht
      have hpij := List.mem_product.mp hp.1
      have hij := of_decide_eq_true (List.mem_filter.mp hpij.1).2
      have hjk := of_decide_eq_true hp.2
      apply List.mem_map.mpr
      refine ⟨unrotate t, ?_, by simp [rotate, unrotate]⟩
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, by simp [all]⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [unrotate] using le_trans hij hjk⟩
      · simpa [unrotate] using And.intro hij hjk
    · intro ht
      rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
      have hp := List.mem_filter.mp hu
      have hpki := List.mem_product.mp hp.1
      have hik := of_decide_eq_true (List.mem_filter.mp hpki.1).2
      have hijk := of_decide_eq_true hp.2
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, by simp [all]⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [rotate] using hijk.1⟩
      · simpa [rotate] using hijk.2
  have flattenFiltered : ∀ {α β : Type} (is : List α) (js : List β)
      (p : α → β → Prop) [DecidableRel p] (g : α → β → G),
      (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
        (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
          fun ij => g ij.1 ij.2).prod := by
    intro α β is js p inst g
    induction is with
    | nil => simp
    | cons i is ih =>
        rw [List.map_cons, List.prod_cons, List.product_cons,
          List.filter_append, List.map_append, List.prod_append, ih]
        congr 1
        have hlist :
            (js.filter (p i)).map (g i) =
              ((js.map fun b => (i, b)).filter fun ij => p ij.1 ij.2).map
                fun ij => g ij.1 ij.2 := by
          simp only [List.filter_map, List.map_map]
          rfl
        exact congrArg List.prod hlist
  have hcanonical :
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k) =
      (triples.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun i j => i ≤ j)
      (fun i j => ((all.filter (j ≤ ·)).map fun k => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun ij => ij.1 ≤ ij.2) all
      (fun ij k => ij.2 ≤ k) (fun ij k => f ij.1 ij.2 k)
    simpa [triples, all] using h1.trans h2
  have hright :
      (orderedProduct fun k => orderedProductWhere (· ≤ k) fun i =>
        orderedProductWhere (fun j => i ≤ j ∧ j ≤ k) fun j => f i j k) =
      (reordered.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun k i => i ≤ k)
      (fun k i => ((all.filter fun j => i ≤ j ∧ j ≤ k).map
        fun j => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun ki => ki.2 ≤ ki.1) all
      (fun ki j => ki.2 ≤ j ∧ j ≤ ki.1) (fun ki j => f ki.2 j ki.1)
    simpa [reordered, raw, rotate, all, List.map_map] using h1.trans h2
  rw [hright, hcanonical]
  apply D5.listProd_perm_gammaThree (hperm.symm.map _)
  intro x hx
  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
  have ht' : t ∈ triples := hperm.mem_iff.mpr ht
  have hp := List.mem_filter.mp ht'
  have hpij := List.mem_product.mp hp.1
  have hij := of_decide_eq_true (List.mem_filter.mp hpij.1).2
  have hjk := of_decide_eq_true hp.2
  exact hf t.1.1 t.1.2 t.2 hij hjk

def weakTripleProduct {s : ℕ} (f : Fin s → Fin s → Fin s → G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k => f i j k

/-- Pointwise collection over the weak triangle `i ≤ j ≤ k`. -/
theorem weakTripleProduct_pointwise_gammaThree
    {s : ℕ} (f g : Fin s → Fin s → Fin s → G)
    (hf : ∀ i j k, i ≤ j → j ≤ k → f i j k ∈ D5.gamma G 3)
    (hg : ∀ i j k, i ≤ j → j ≤ k → g i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix (weakTripleProduct f * weakTripleProduct g)
      (weakTripleProduct fun i j k => f i j k * g i j k) := by
  let FR : Fin s → Fin s → G := fun i j =>
    orderedProductWhere (j ≤ ·) fun k => f i j k
  let GR : Fin s → Fin s → G := fun i j =>
    orderedProductWhere (j ≤ ·) fun k => g i j k
  have hFR : ∀ i j, i ≤ j → FR i j ∈ D5.gamma G 3 := by
    intro i j hij
    apply orderedProductWhere_mem
    intro k hjk
    exact hf i j k hij hjk
  have hGR : ∀ i j, i ≤ j → GR i j ∈ D5.gamma G 3 := by
    intro i j hij
    apply orderedProductWhere_mem
    intro k hjk
    exact hg i j k hij hjk
  have hsplitK : D5.ModGammaSix
      (weakTripleProduct fun i j k => f i j k * g i j k)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        FR i j * GR i j) := by
    unfold weakTripleProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    simpa [FR, GR] using
      D5.orderedProductWhere_pointwise_mul_gammaThree (j ≤ ·)
        (f i j) (g i j) (fun k hjk => hf i j k hij hjk)
          (fun k hjk => hg i j k hij hjk)
  let FB : Fin s → G := fun i => orderedProductWhere (i ≤ ·) fun j => FR i j
  let GB : Fin s → G := fun i => orderedProductWhere (i ≤ ·) fun j => GR i j
  have hFB : ∀ i, FB i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hFR i j hij
  have hGB : ∀ i, GB i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hGR i j hij
  have hsplitJ : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j => FR i j * GR i j)
      (orderedProduct fun i => FB i * GB i) := by
    apply modEq_orderedProduct
    intro i
    simpa [FB, GB] using
      D5.orderedProductWhere_pointwise_mul_gammaThree (i ≤ ·)
        (FR i) (GR i) (fun j hij => hFR i j hij) (fun j hij => hGR i j hij)
  have hsplitI : D5.ModGammaSix
      (orderedProduct fun i => FB i * GB i)
      (orderedProduct FB * orderedProduct GB) :=
    D5.orderedProduct_pointwise_mul_gammaThree FB GB hFB hGB
  have hsplit := hsplitK.trans (hsplitJ.trans hsplitI)
  simpa [weakTripleProduct, FB, GB, FR, GR] using hsplit.symm

def formula34WLineNineFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d i) (C.x1 k)) ξ)
      (C.x1 j) ^ (-P.w i j k)

def formula34WLineTenFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d i) (C.x1 j)) ξ)
      (C.x1 k) ^ (-P.w i j k)

def formula34WLineTwelveFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  D5.paperComm
    (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ^
      P.w i j k

theorem formula34_w_line_factors_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    formula34WLineNineFactor C P ξ i j k ∈ D5.gamma G 3 ∧
    formula34WLineTenFactor C P ξ i j k ∈ D5.gamma G 3 ∧
    formula34WLineTwelveFactor C P ξ i j k ∈ D5.gamma G 3 := by
  have ha : C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 i
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h9 : D5.paperComm (D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) (C.x1 k)) ξ)
      (C.x1 j) ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hk) hξ) hj
  have h10 : D5.paperComm (D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) (C.x1 j)) ξ)
      (C.x1 k) ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hj) hξ) hk
  have hinner : D5.leftComm (C.x1 i ^ orderInt C.d i)
      [C.x1 j, C.x1 k] ∈ D5.gamma G 4 := by
    simpa using D5.leftComm_mem_gamma_of_first (r := 2) (by norm_num) ha
      [C.x1 j, C.x1 k]
  have h12 : D5.paperComm
      (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ∈
      D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hinner hξ
  exact ⟨D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).zpow_mem h9 _),
    D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).zpow_mem h10 _),
    D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).zpow_mem h12 _)⟩

theorem formula34_line_nine_reindexed
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula28WLeftDisplayedStream C P ξ)
      (weakTripleProduct (formula34WLineNineFactor C P ξ)) := by
  simpa [formula28WLeftDisplayedStream, weakTripleProduct,
    formula34WLineNineFactor] using
    tripleProduct_reindex_jik (formula34WLineNineFactor C P ξ)
      (fun i j k hij hjk => (formula34_w_line_factors_mem_gamma3 C P ξ i j k).1)

theorem formula34_line_ten_reindexed
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula28WRightDisplayedStream C P ξ)
      (weakTripleProduct (formula34WLineTenFactor C P ξ)) := by
  simpa [formula28WRightDisplayedStream, weakTripleProduct,
    formula34WLineTenFactor] using
    tripleProduct_reindex_kij (formula34WLineTenFactor C P ξ)
      (fun i j k hij hjk =>
        (formula34_w_line_factors_mem_gamma3 C P ξ i j k).2.1)

theorem formula34_lines_nine_ten_twelve_to_canonical
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      ((formula28WLeftDisplayedStream C P ξ *
          formula28WRightDisplayedStream C P ξ) *
        formula29LineTwelve C P ξ)
      (formula34WCanonicalSourceProduct C P ξ) := by
  let L9 := formula34WLineNineFactor C P ξ
  let L10 := formula34WLineTenFactor C P ξ
  let L12 := formula34WLineTwelveFactor C P ξ
  have h9 := formula34_line_nine_reindexed C P ξ
  have h10 := formula34_line_ten_reindexed C P ξ
  have h12 : formula29LineTwelve C P ξ = weakTripleProduct L12 := by
    rfl
  have hm9 : ∀ i j k, i ≤ j → j ≤ k → L9 i j k ∈ D5.gamma G 3 := by
    intro i j k hij hjk
    exact (formula34_w_line_factors_mem_gamma3 C P ξ i j k).1
  have hm10 : ∀ i j k, i ≤ j → j ≤ k → L10 i j k ∈ D5.gamma G 3 := by
    intro i j k hij hjk
    exact (formula34_w_line_factors_mem_gamma3 C P ξ i j k).2.1
  have hm12 : ∀ i j k, i ≤ j → j ≤ k → L12 i j k ∈ D5.gamma G 3 := by
    intro i j k hij hjk
    exact (formula34_w_line_factors_mem_gamma3 C P ξ i j k).2.2
  have hcombine9_10 := weakTripleProduct_pointwise_gammaThree L9 L10 hm9 hm10
  have hcombineAll := weakTripleProduct_pointwise_gammaThree
    (fun i j k => L9 i j k * L10 i j k) L12
    (fun i j k hij hjk => (D5.gamma G 3).mul_mem
      (hm9 i j k hij hjk) (hm10 i j k hij hjk)) hm12
  have hstart : D5.ModGammaSix
      ((formula28WLeftDisplayedStream C P ξ *
          formula28WRightDisplayedStream C P ξ) *
        formula29LineTwelve C P ξ)
      ((weakTripleProduct L9 * weakTripleProduct L10) *
        weakTripleProduct L12) := by
    rw [h12]
    exact (h9.mul h10).mul
      (D5.ModEq.refl (D5.gamma G 6) (weakTripleProduct L12))
  exact hstart.trans <| by
    simpa [formula34WCanonicalSourceProduct, formula34WSourceFactor,
      formula34WLineNineFactor, formula34WLineTenFactor,
      formula34WLineTwelveFactor, weakTripleProduct, L9, L10, L12] using
        (hcombine9_10.mul
          (D5.ModEq.refl (D5.gamma G 6) (weakTripleProduct L12))).trans
            hcombineAll

/-- Lines 9, 10 and 12 of (29), after reindexing and the complete local
Jacobi calculation. -/
theorem formula34_w_streams
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      ((formula28WLeftDisplayedStream C P ξ *
          formula28WRightDisplayedStream C P ξ) *
        formula29LineTwelve C P ξ)
      (formula34WExtraProduct C P ξ * formula34WMainProduct C P ξ) :=
  (formula34_lines_nine_ten_twelve_to_canonical C P ξ).trans
    (formula34_w_canonical_product C P ξ)

/-! ## Expanding formula (35) -/

/-- Multilinearity in the second entry, collected over an arbitrary finite
list.  This is the finite form needed to expand the three words in (33). -/
theorem fourfold_second_listProd_mod_gamma_six
    {ι : Type*} (is : List ι) (a : ι → G) {ξ x z : G}
    (hξ : ξ ∈ D5.gamma G 1) (ha : ∀ i ∈ is, a i ∈ D5.gamma G 2)
    (hx : x ∈ D5.gamma G 1) (hz : z ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ ((is.map a).prod)) x) z)
      ((is.map fun i =>
        D5.paperComm (D5.paperComm (D5.paperComm ξ (a i)) x) z).prod) := by
  induction is with
  | nil =>
      simpa [D5.paperComm] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)
  | cons i is ih =>
      have hai : a i ∈ D5.gamma G 2 := ha i (by simp)
      have hatail : (is.map a).prod ∈ D5.gamma G 2 := by
        apply listProd_mem
        intro y hy
        rcases List.mem_map.mp hy with ⟨j, hj, rfl⟩
        exact ha j (by simp [hj])
      simp only [List.map_cons, List.prod_cons]
      exact (fourfold_second_mul_mod_gamma_six hξ hai hatail hx hz).trans
        ((D5.ModEq.refl (D5.gamma G 6)
          (D5.paperComm (D5.paperComm (D5.paperComm ξ (a i)) x) z)).mul
            (ih (fun j hj => ha j (by simp [hj]))))

/-- The preceding collection lemma for a filtered ordered product. -/
theorem fourfold_second_orderedProductWhere_mod_gamma_six
    {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (a : Fin n → G) {ξ x z : G}
    (hξ : ξ ∈ D5.gamma G 1)
    (ha : ∀ i, p i → a i ∈ D5.gamma G 2)
    (hx : x ∈ D5.gamma G 1) (hz : z ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (orderedProductWhere p a)) x) z)
      (orderedProductWhere p fun i =>
        D5.paperComm (D5.paperComm (D5.paperComm ξ (a i)) x) z) := by
  unfold orderedProductWhere
  apply fourfold_second_listProd_mod_gamma_six
  · exact hξ
  · intro i hi
    exact ha i (of_decide_eq_true (List.mem_filter.mp hi).2)
  · exact hx
  · exact hz

def formula35WBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) : G :=
  orderedProductWhere (· ≤ j) fun h =>
    formula34WExtraFactor C P ξ h j k

def formula35WPrimeBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) : G :=
  orderedProductWhere (fun h => j < h ∧ h ≤ k) fun h =>
    formula34WPrimeExtraFactor C P ξ j h k

def formula34WDoublePrimePositiveFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k h : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 h ^ orderInt C.d h)) (C.x1 k))
      (C.x1 j) ^ P.w'' j k h

def formula35WDoublePrimeBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) : G :=
  orderedProductWhere (k < ·) fun h =>
    formula34WDoublePrimePositiveFactor C P ξ j k h

theorem formula34WDoublePrimePositiveFactor_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k h : Fin C.s) :
    formula34WDoublePrimePositiveFactor C P ξ j k h ∈
      D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hh : C.x1 h ^ orderInt C.d h ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 h
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h3 := D5.paperComm_mem_gamma_add (r := 1) (s := 2)
    (by norm_num) (by norm_num) hξ hh
  have h4 := D5.paperComm_mem_gamma_add (r := 3) (s := 1)
    (by norm_num) (by norm_num) h3 hk
  have h5 := D5.paperComm_mem_gamma_add (r := 4) (s := 1)
    (by norm_num) (by norm_num) h4 hj
  exact D5.gamma_antitone G (by norm_num : 3 ≤ 5) <|
    (D5.gamma G 5).zpow_mem h5 _

/-- Exact expansion of one factor in (35) into the three blocks of (33).
The powers of the first-layer generators are transferred to the resulting
weight-five commutators explicitly. -/
theorem formula35_factor_expanded
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm (D5.paperComm ξ (formula33Word C P j k)) (C.x1 k))
          (C.x1 j))
      ((formula35WBlock C P ξ j k * formula35WPrimeBlock C P ξ j k) *
        formula35WDoublePrimeBlock C P ξ j k) := by
  let A : G := orderedProductWhere (· ≤ j) fun h =>
    C.x1 h ^ (orderInt C.d h * P.w h j k)
  let B : G := orderedProductWhere (fun h => j < h ∧ h ≤ k) fun h =>
    C.x1 h ^ (orderInt C.d h * P.w' j h k)
  let E : G := orderedProductWhere (k < ·) fun h =>
    C.x1 h ^ (orderInt C.d h * P.w'' j k h)
  let F : G → G := fun a =>
    D5.paperComm (D5.paperComm (D5.paperComm ξ a) (C.x1 k)) (C.x1 j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : A ∈ D5.gamma G 2 := by
    apply orderedProductWhere_mem
    intro h hh
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  have hB : B ∈ D5.gamma G 2 := by
    apply orderedProductWhere_mem
    intro h hh
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  have hE : E ∈ D5.gamma G 2 := by
    apply orderedProductWhere_mem
    intro h hh
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  have hsplit : D5.ModGammaSix (F ((A * B) * E)) ((F A * F B) * F E) := by
    exact (fourfold_second_mul_mod_gamma_six hξ
      ((D5.gamma G 2).mul_mem hA hB) hE hk hj).trans
        ((fourfold_second_mul_mod_gamma_six hξ hA hB hk hj).mul
          (D5.ModEq.refl (D5.gamma G 6) (F E)))
  have hcollectA : D5.ModGammaSix (F A) (formula35WBlock C P ξ j k) := by
    have hc := fourfold_second_orderedProductWhere_mod_gamma_six (· ≤ j)
      (fun h => C.x1 h ^ (orderInt C.d h * P.w h j k)) hξ
      (fun h hh => by
        simp only
        rw [zpow_mul]
        exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _)
      hk hj
    refine hc.trans ?_
    apply modEq_orderedProductWhere
    intro h hh
    simp only
    rw [zpow_mul]
    simpa [F, formula34WExtraFactor] using
      fourfold_second_zpow_mod_gamma_six hξ
        (C.x1_order_power_mem_gamma2 h) hk hj (P.w h j k)
  have hcollectB : D5.ModGammaSix (F B) (formula35WPrimeBlock C P ξ j k) := by
    have hc := fourfold_second_orderedProductWhere_mod_gamma_six
      (fun h => j < h ∧ h ≤ k)
      (fun h => C.x1 h ^ (orderInt C.d h * P.w' j h k)) hξ
      (fun h hh => by
        simp only
        rw [zpow_mul]
        exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _)
      hk hj
    refine hc.trans ?_
    apply modEq_orderedProductWhere
    intro h hh
    simp only
    rw [zpow_mul]
    simpa [F, formula34WPrimeExtraFactor] using
      fourfold_second_zpow_mod_gamma_six hξ
        (C.x1_order_power_mem_gamma2 h) hk hj (P.w' j h k)
  have hcollectE : D5.ModGammaSix (F E)
      (formula35WDoublePrimeBlock C P ξ j k) := by
    have hc := fourfold_second_orderedProductWhere_mod_gamma_six (k < ·)
      (fun h => C.x1 h ^ (orderInt C.d h * P.w'' j k h)) hξ
      (fun h hh => by
        simp only
        rw [zpow_mul]
        exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _)
      hk hj
    refine hc.trans ?_
    apply modEq_orderedProductWhere
    intro h hh
    simp only
    rw [zpow_mul]
    simpa [F, formula34WDoublePrimePositiveFactor] using
      fourfold_second_zpow_mod_gamma_six hξ
        (C.x1_order_power_mem_gamma2 h) hk hj (P.w'' j k h)
  simpa [formula33Word, A, B, E, F] using
    hsplit.trans ((hcollectA.mul hcollectB).mul hcollectE)

theorem orderedProductWhere_three_gammaThree
    {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (a b c : Fin n → G)
    (ha : ∀ i, p i → a i ∈ D5.gamma G 3)
    (hb : ∀ i, p i → b i ∈ D5.gamma G 3)
    (hc : ∀ i, p i → c i ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProductWhere p fun i => (a i * b i) * c i)
      ((orderedProductWhere p a * orderedProductWhere p b) *
        orderedProductWhere p c) := by
  exact (D5.orderedProductWhere_pointwise_mul_gammaThree p
    (fun i => a i * b i) c
    (fun i hi => (D5.gamma G 3).mul_mem (ha i hi) (hb i hi)) hc).trans
      ((D5.orderedProductWhere_pointwise_mul_gammaThree p a b ha hb).mul
        (D5.ModEq.refl (D5.gamma G 6) (orderedProductWhere p c)))

theorem orderedProduct_three_gammaThree
    {n : ℕ} (a b c : Fin n → G)
    (ha : ∀ i, a i ∈ D5.gamma G 3)
    (hb : ∀ i, b i ∈ D5.gamma G 3)
    (hc : ∀ i, c i ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun i => (a i * b i) * c i)
      ((orderedProduct a * orderedProduct b) * orderedProduct c) := by
  exact (D5.orderedProduct_pointwise_mul_gammaThree
    (fun i => a i * b i) c
    (fun i => (D5.gamma G 3).mul_mem (ha i) (hb i)) hc).trans
      ((D5.orderedProduct_pointwise_mul_gammaThree a b ha hb).mul
        (D5.ModEq.refl (D5.gamma G 6) (orderedProduct c)))

def formula35WProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
    formula35WBlock C P ξ j k

def formula35WPrimeProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
    formula35WPrimeBlock C P ξ j k

def formula34WDoublePrimePositiveProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
    formula35WDoublePrimeBlock C P ξ j k

theorem formula35WBlock_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) : formula35WBlock C P ξ j k ∈ D5.gamma G 3 := by
  apply orderedProductWhere_mem
  intro h hh
  exact formula34WExtraFactor_mem_gamma3 C P ξ h j k

theorem formula35WPrimeBlock_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) : formula35WPrimeBlock C P ξ j k ∈ D5.gamma G 3 := by
  apply orderedProductWhere_mem
  intro h hh
  exact formula34WPrimeExtraFactor_mem_gamma3 C P ξ j h k

theorem formula35WDoublePrimeBlock_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) :
    formula35WDoublePrimeBlock C P ξ j k ∈ D5.gamma G 3 := by
  apply orderedProductWhere_mem
  intro h hh
  exact formula34WDoublePrimePositiveFactor_mem_gamma3 C P ξ j k h

/-- Formula (35) after expanding all three first-layer words in (33) and
collecting like factors. -/
theorem formula35_expanded_product
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula35Product C P ξ)
      ((formula35WProduct C P ξ * formula35WPrimeProduct C P ξ) *
        formula34WDoublePrimePositiveProduct C P ξ) := by
  let A : Fin C.s → Fin C.s → G := formula35WBlock C P ξ
  let B : Fin C.s → Fin C.s → G := formula35WPrimeBlock C P ξ
  let E : Fin C.s → Fin C.s → G := formula35WDoublePrimeBlock C P ξ
  have hA : ∀ j k, A j k ∈ D5.gamma G 3 := fun j k =>
    formula35WBlock_mem_gamma3 C P ξ j k
  have hB : ∀ j k, B j k ∈ D5.gamma G 3 := fun j k =>
    formula35WPrimeBlock_mem_gamma3 C P ξ j k
  have hE : ∀ j k, E j k ∈ D5.gamma G 3 := fun j k =>
    formula35WDoublePrimeBlock_mem_gamma3 C P ξ j k
  have hlocal : D5.ModGammaSix (formula35Product C P ξ)
      (orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
        (A j k * B j k) * E j k) := by
    unfold formula35Product
    apply modEq_orderedProduct
    intro j
    apply modEq_orderedProductWhere
    intro k hjk
    exact formula35_factor_expanded C P ξ j k
  have hsplitK : D5.ModGammaSix
      (orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
        (A j k * B j k) * E j k)
      (orderedProduct fun j =>
        ((orderedProductWhere (j < ·) fun k => A j k) *
          (orderedProductWhere (j < ·) fun k => B j k)) *
          (orderedProductWhere (j < ·) fun k => E j k)) := by
    apply modEq_orderedProduct
    intro j
    exact orderedProductWhere_three_gammaThree (j < ·) (A j) (B j) (E j)
      (fun k hk => hA j k) (fun k hk => hB j k) (fun k hk => hE j k)
  let AR : Fin C.s → G := fun j => orderedProductWhere (j < ·) (A j)
  let BR : Fin C.s → G := fun j => orderedProductWhere (j < ·) (B j)
  let ER : Fin C.s → G := fun j => orderedProductWhere (j < ·) (E j)
  have hAR : ∀ j, AR j ∈ D5.gamma G 3 := by
    intro j; apply orderedProductWhere_mem; intro k hk; exact hA j k
  have hBR : ∀ j, BR j ∈ D5.gamma G 3 := by
    intro j; apply orderedProductWhere_mem; intro k hk; exact hB j k
  have hER : ∀ j, ER j ∈ D5.gamma G 3 := by
    intro j; apply orderedProductWhere_mem; intro k hk; exact hE j k
  have hsplitJ := orderedProduct_three_gammaThree AR BR ER hAR hBR hER
  exact hlocal.trans <| hsplitK.trans <| by
    simpa [AR, BR, ER, A, B, E, formula35WProduct,
      formula35WPrimeProduct, formula34WDoublePrimePositiveProduct] using hsplitJ

/-- The expanded three-block product is trivial modulo `γ₆`; this is the
usable cancellation consequence of (35). -/
theorem formula35_expanded_product_vanish
    (C : Context G) (P : Parameters C.s C.t) (h12 : P.Condition12)
    (ξ : G) :
    D5.ModGammaSix
      ((formula35WProduct C P ξ * formula35WPrimeProduct C P ξ) *
        formula34WDoublePrimePositiveProduct C P ξ) 1 :=
  (formula35_expanded_product C P ξ).symm.trans
    (formula35 C P h12 ξ)

/-- Reindex `i ≤ j < k` from the loop order `(j,k,i)` used by the
first block of (35) to the canonical order `(i,j,k)`. -/
theorem tripleProduct_reindex_jki_weak_strict
    {s : ℕ} (f : Fin s → Fin s → Fin s → G)
    (hf : ∀ i j k, i ≤ j → j < k → f i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
        orderedProductWhere (· ≤ j) fun i => f i j k)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j < ·) fun k => f i j k) := by
  classical
  let all := List.finRange s
  let triples :=
    ((((all ×ˢ all).filter fun ij => ij.1 ≤ ij.2) ×ˢ all).filter fun t =>
      t.1.2 < t.2)
  let raw :=
    ((((all ×ˢ all).filter fun jk => jk.1 < jk.2) ×ˢ all).filter fun t =>
      t.2 ≤ t.1.1)
  let rotate : (Fin s × Fin s) × Fin s → (Fin s × Fin s) × Fin s :=
    fun t => ((t.2, t.1.1), t.1.2)
  let unrotate : (Fin s × Fin s) × Fin s → (Fin s × Fin s) × Fin s :=
    fun t => ((t.1.2, t.2), t.1.1)
  let reordered := raw.map rotate
  have hall : all.Nodup := by simpa [all] using List.nodup_finRange s
  have hrotate : Function.Injective rotate := by
    intro a b h
    apply_fun unrotate at h
    simpa [rotate, unrotate] using h
  have htriples : triples.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hraw : raw.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hreordered : reordered.Nodup := hraw.map hrotate
  have hperm : triples.Perm reordered := by
    apply (List.perm_ext_iff_of_nodup htriples hreordered).2
    intro t
    constructor
    · intro ht
      have hp := List.mem_filter.mp ht
      have hpij := List.mem_product.mp hp.1
      have hij := of_decide_eq_true (List.mem_filter.mp hpij.1).2
      have hjk := of_decide_eq_true hp.2
      apply List.mem_map.mpr
      refine ⟨unrotate t, ?_, by simp [rotate, unrotate]⟩
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, by simp [all]⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [unrotate] using hjk⟩
      · simpa [unrotate] using hij
    · intro ht
      rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
      have hp := List.mem_filter.mp hu
      have hpjk := List.mem_product.mp hp.1
      have hjk := of_decide_eq_true (List.mem_filter.mp hpjk.1).2
      have hij := of_decide_eq_true hp.2
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, by simp [all]⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [rotate] using hij⟩
      · simpa [rotate] using hjk
  have flattenFiltered : ∀ {α β : Type} (is : List α) (js : List β)
      (p : α → β → Prop) [DecidableRel p] (g : α → β → G),
      (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
        (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
          fun ij => g ij.1 ij.2).prod := by
    intro α β is js p inst g
    induction is with
    | nil => simp
    | cons i is ih =>
        rw [List.map_cons, List.prod_cons, List.product_cons,
          List.filter_append, List.map_append, List.prod_append, ih]
        congr 1
        have hlist :
            (js.filter (p i)).map (g i) =
              ((js.map fun b => (i, b)).filter fun ij => p ij.1 ij.2).map
                fun ij => g ij.1 ij.2 := by
          simp only [List.filter_map, List.map_map]
          rfl
        exact congrArg List.prod hlist
  have hcanonical :
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j < ·) fun k => f i j k) =
      (triples.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun i j => i ≤ j)
      (fun i j => ((all.filter (j < ·)).map fun k => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun ij => ij.1 ≤ ij.2) all
      (fun ij k => ij.2 < k) (fun ij k => f ij.1 ij.2 k)
    simpa [triples, all] using h1.trans h2
  have hleft :
      (orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
        orderedProductWhere (· ≤ j) fun i => f i j k) =
      (reordered.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun j k => j < k)
      (fun j k => ((all.filter (· ≤ j)).map fun i => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun jk => jk.1 < jk.2) all
      (fun jk i => i ≤ jk.1) (fun jk i => f i jk.1 jk.2)
    simpa [reordered, raw, rotate, all, List.map_map] using h1.trans h2
  rw [hleft, hcanonical]
  apply D5.listProd_perm_gammaThree (hperm.symm.map _)
  intro x hx
  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
  have ht' : t ∈ triples := hperm.mem_iff.mpr ht
  have hp := List.mem_filter.mp ht'
  have hpij := List.mem_product.mp hp.1
  exact hf t.1.1 t.1.2 t.2
    (of_decide_eq_true (List.mem_filter.mp hpij.1).2)
    (of_decide_eq_true hp.2)

def formula34WExtraOffDiagonalProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j < ·) fun k =>
      formula34WExtraFactor C P ξ i j k

theorem formula35WProduct_reindexed
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula35WProduct C P ξ)
      (formula34WExtraOffDiagonalProduct C P ξ) := by
  simpa [formula35WProduct, formula35WBlock,
    formula34WExtraOffDiagonalProduct] using
      tripleProduct_reindex_jki_weak_strict
        (formula34WExtraFactor C P ξ)
        (fun i j k hij hjk => formula34WExtraFactor_mem_gamma3 C P ξ i j k)

/-- Reindex `i < j ≤ k` from `(i,k,j)` to `(i,j,k)`. -/
theorem tripleProduct_reindex_ikj_strict_weak
    {s : ℕ} (f : Fin s → Fin s → Fin s → G)
    (hf : ∀ i j k, i < j → j ≤ k → f i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun k =>
        orderedProductWhere (fun j => i < j ∧ j ≤ k) fun j => f i j k)
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k) := by
  classical
  let all := List.finRange s
  let triples :=
    ((((all ×ˢ all).filter fun ij => ij.1 < ij.2) ×ˢ all).filter fun t =>
      t.1.2 ≤ t.2)
  let raw :=
    ((((all ×ˢ all).filter fun ik => ik.1 < ik.2) ×ˢ all).filter fun t =>
      t.1.1 < t.2 ∧ t.2 ≤ t.1.2)
  let rotate : (Fin s × Fin s) × Fin s → (Fin s × Fin s) × Fin s :=
    fun t => ((t.1.1, t.2), t.1.2)
  let unrotate : (Fin s × Fin s) × Fin s → (Fin s × Fin s) × Fin s :=
    fun t => ((t.1.1, t.2), t.1.2)
  let reordered := raw.map rotate
  have hall : all.Nodup := by simpa [all] using List.nodup_finRange s
  have hrotate : Function.Injective rotate := by
    intro a b h
    apply_fun unrotate at h
    simpa [rotate, unrotate] using h
  have htriples : triples.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hraw : raw.Nodup :=
    (((hall.product hall).filter _).product hall).filter _
  have hreordered : reordered.Nodup := hraw.map hrotate
  have hperm : triples.Perm reordered := by
    apply (List.perm_ext_iff_of_nodup htriples hreordered).2
    intro t
    constructor
    · intro ht
      have hp := List.mem_filter.mp ht
      have hpij := List.mem_product.mp hp.1
      have hij := of_decide_eq_true (List.mem_filter.mp hpij.1).2
      have hjk := of_decide_eq_true hp.2
      apply List.mem_map.mpr
      refine ⟨unrotate t, ?_, by simp [rotate, unrotate]⟩
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, by simp [all]⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [unrotate] using lt_of_lt_of_le hij hjk⟩
      · simpa [unrotate] using And.intro hij hjk
    · intro ht
      rcases List.mem_map.mp ht with ⟨u, hu, rfl⟩
      have hp := List.mem_filter.mp hu
      have hpik := List.mem_product.mp hp.1
      have hijk := of_decide_eq_true hp.2
      apply List.mem_filter.mpr
      refine ⟨List.mem_product.mpr ⟨?_, by simp [all]⟩, ?_⟩
      · apply List.mem_filter.mpr
        exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
          by simpa [rotate] using hijk.1⟩
      · simpa [rotate] using hijk.2
  have flattenFiltered : ∀ {α β : Type} (is : List α) (js : List β)
      (p : α → β → Prop) [DecidableRel p] (g : α → β → G),
      (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
        (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
          fun ij => g ij.1 ij.2).prod := by
    intro α β is js p inst g
    induction is with
    | nil => simp
    | cons i is ih =>
        rw [List.map_cons, List.prod_cons, List.product_cons,
          List.filter_append, List.map_append, List.prod_append, ih]
        congr 1
        have hlist :
            (js.filter (p i)).map (g i) =
              ((js.map fun b => (i, b)).filter fun ij => p ij.1 ij.2).map
                fun ij => g ij.1 ij.2 := by
          simp only [List.filter_map, List.map_map]
          rfl
        exact congrArg List.prod hlist
  have hcanonical :
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k) =
      (triples.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun i j => i < j)
      (fun i j => ((all.filter (j ≤ ·)).map fun k => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun ij => ij.1 < ij.2) all
      (fun ij k => ij.2 ≤ k) (fun ij k => f ij.1 ij.2 k)
    simpa [triples, all] using h1.trans h2
  have hleft :
      (orderedProduct fun i => orderedProductWhere (i < ·) fun k =>
        orderedProductWhere (fun j => i < j ∧ j ≤ k) fun j => f i j k) =
      (reordered.map fun t => f t.1.1 t.1.2 t.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h1 := flattenFiltered all all (fun i k => i < k)
      (fun i k => ((all.filter fun j => i < j ∧ j ≤ k).map
        fun j => f i j k).prod)
    have h2 := flattenFiltered
      ((all ×ˢ all).filter fun ik => ik.1 < ik.2) all
      (fun ik j => ik.1 < j ∧ j ≤ ik.2) (fun ik j => f ik.1 j ik.2)
    simpa [reordered, raw, rotate, all, List.map_map] using h1.trans h2
  rw [hleft, hcanonical]
  apply D5.listProd_perm_gammaThree (hperm.symm.map _)
  intro x hx
  rcases List.mem_map.mp hx with ⟨t, ht, rfl⟩
  have ht' : t ∈ triples := hperm.mem_iff.mpr ht
  have hp := List.mem_filter.mp ht'
  have hpij := List.mem_product.mp hp.1
  exact hf t.1.1 t.1.2 t.2
    (of_decide_eq_true (List.mem_filter.mp hpij.1).2)
    (of_decide_eq_true hp.2)

theorem formula35WPrimeProduct_reindexed
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula35WPrimeProduct C P ξ)
      (formula34WPrimeExtraProduct C P ξ) := by
  simpa [formula35WPrimeProduct, formula35WPrimeBlock,
    formula34WPrimeExtraProduct] using
      tripleProduct_reindex_ikj_strict_weak
        (formula34WPrimeExtraFactor C P ξ)
        (fun i j k hij hjk =>
          formula34WPrimeExtraFactor_mem_gamma3 C P ξ i j k)

/-- Formula (35), now with its first two blocks in the indexing convention
of formula (34). -/
theorem formula35_reindexed_vanish
    (C : Context G) (P : Parameters C.s C.t) (h12 : P.Condition12)
    (ξ : G) :
    D5.ModGammaSix
      ((formula34WExtraOffDiagonalProduct C P ξ *
          formula34WPrimeExtraProduct C P ξ) *
        formula34WDoublePrimePositiveProduct C P ξ) 1 := by
  have hreindex : D5.ModGammaSix
      ((formula35WProduct C P ξ * formula35WPrimeProduct C P ξ) *
        formula34WDoublePrimePositiveProduct C P ξ)
      ((formula34WExtraOffDiagonalProduct C P ξ *
          formula34WPrimeExtraProduct C P ξ) *
        formula34WDoublePrimePositiveProduct C P ξ) :=
    ((formula35WProduct_reindexed C P ξ).mul
      (formula35WPrimeProduct_reindexed C P ξ)).mul
        (D5.ModEq.refl (D5.gamma G 6)
          (formula34WDoublePrimePositiveProduct C P ξ))
  exact hreindex.symm.trans (formula35_expanded_product_vanish C P h12 ξ)

theorem orderedProductWhere_zpow_gammaThree
    {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → G) (hf : ∀ i, p i → f i ∈ D5.gamma G 3)
    (v : ℤ) :
    D5.ModGammaSix (orderedProductWhere p f ^ v)
      (orderedProductWhere p fun i => f i ^ v) := by
  unfold orderedProductWhere
  simpa [List.map_map] using D5.listProd_zpow_gammaThree
    (((List.finRange n).filter p).map f)
    (fun x hx => by
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact hf i (of_decide_eq_true (List.mem_filter.mp hi).2)) v

def formula34WDoublePrimeMainFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k h : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 h ^ orderInt C.d h)) (C.x1 k))
      (C.x1 j) ^ (-P.w'' j k h)

def formula34WDoublePrimeMainBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k : Fin C.s) : G :=
  orderedProductWhere (k < ·) fun h =>
    formula34WDoublePrimeMainFactor C P ξ j k h

/-- The third principal product displayed in (34). -/
def formula34WDoublePrimeMainProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
    formula34WDoublePrimeMainBlock C P ξ j k

theorem formula34WDoublePrimeMainFactor_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (j k h : Fin C.s) :
    formula34WDoublePrimeMainFactor C P ξ j k h ∈ D5.gamma G 3 := by
  simpa [formula34WDoublePrimeMainFactor,
    formula34WDoublePrimePositiveFactor] using
      (D5.gamma G 3).inv_mem
        (formula34WDoublePrimePositiveFactor_mem_gamma3 C P ξ j k h)

/-- In the abelian weight-five layer, negating every `w''` coefficient is
the inverse of the positive product obtained from (35). -/
theorem formula34_wdoubleprime_positive_inv
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula34WDoublePrimePositiveProduct C P ξ)⁻¹
      (formula34WDoublePrimeMainProduct C P ξ) := by
  let Pos : Fin C.s → Fin C.s → Fin C.s → G :=
    formula34WDoublePrimePositiveFactor C P ξ
  let Neg : Fin C.s → Fin C.s → Fin C.s → G :=
    formula34WDoublePrimeMainFactor C P ξ
  let PB : Fin C.s → Fin C.s → G := fun j k =>
    orderedProductWhere (k < ·) (Pos j k)
  let NB : Fin C.s → Fin C.s → G := fun j k =>
    orderedProductWhere (k < ·) (Neg j k)
  let PR : Fin C.s → G := fun j => orderedProductWhere (j < ·) (PB j)
  let NR : Fin C.s → G := fun j => orderedProductWhere (j < ·) (NB j)
  have hPos : ∀ j k h, Pos j k h ∈ D5.gamma G 3 := fun j k h =>
    formula34WDoublePrimePositiveFactor_mem_gamma3 C P ξ j k h
  have hPB : ∀ j k, PB j k ∈ D5.gamma G 3 := by
    intro j k; apply orderedProductWhere_mem; intro h hkh; exact hPos j k h
  have hPR : ∀ j, PR j ∈ D5.gamma G 3 := by
    intro j; apply orderedProductWhere_mem; intro k hjk; exact hPB j k
  have hblock : ∀ j k, D5.ModGammaSix (PB j k)⁻¹ (NB j k) := by
    intro j k
    have hp := orderedProductWhere_zpow_gammaThree (k < ·) (Pos j k)
      (fun h hkh => hPos j k h) (-1)
    have hr : D5.ModGammaSix
        (orderedProductWhere (k < ·) fun h => Pos j k h ^ (-1 : ℤ))
        (orderedProductWhere (k < ·) (Neg j k)) := by
      apply modEq_orderedProductWhere
      intro h hkh
      simpa [Pos, Neg, formula34WDoublePrimePositiveFactor,
        formula34WDoublePrimeMainFactor, zpow_neg] using
          D5.ModEq.refl (D5.gamma G 6) (Neg j k h)
    simpa [PB, NB, zpow_neg] using hp.trans hr
  have hrow : ∀ j, D5.ModGammaSix (PR j)⁻¹ (NR j) := by
    intro j
    have hp := orderedProductWhere_zpow_gammaThree (j < ·) (PB j)
      (fun k hjk => hPB j k) (-1)
    have hr : D5.ModGammaSix
        (orderedProductWhere (j < ·) fun k => PB j k ^ (-1 : ℤ))
        (orderedProductWhere (j < ·) (NB j)) := by
      apply modEq_orderedProductWhere
      intro k hjk
      simpa [zpow_neg] using hblock j k
    simpa [PR, NR, zpow_neg] using hp.trans hr
  have hp := D5.orderedProduct_zpow_gammaThree PR hPR (-1)
  have hr : D5.ModGammaSix
      (orderedProduct fun j => PR j ^ (-1 : ℤ))
      (orderedProduct NR) := by
    apply modEq_orderedProduct
    intro j
    simpa [zpow_neg] using hrow j
  simpa [formula34WDoublePrimePositiveProduct,
    formula35WDoublePrimeBlock, formula34WDoublePrimeMainProduct,
    formula34WDoublePrimeMainBlock, Pos, Neg, PB, NB, PR, NR, zpow_neg] using
      hp.trans hr

/-- The off-diagonal `w` correction and the `w'` correction are exactly
the third principal product in (34). -/
theorem formula35_yields_wdoubleprime_main
    (C : Context G) (P : Parameters C.s C.t) (h12 : P.Condition12)
    (ξ : G) :
    D5.ModGammaSix
      (formula34WExtraOffDiagonalProduct C P ξ *
        formula34WPrimeExtraProduct C P ξ)
      (formula34WDoublePrimeMainProduct C P ξ) := by
  let A := formula34WExtraOffDiagonalProduct C P ξ *
    formula34WPrimeExtraProduct C P ξ
  let Q := formula34WDoublePrimePositiveProduct C P ξ
  have hv : D5.ModGammaSix (A * Q) 1 := by
    simpa [A, Q] using formula35_reindexed_vanish C P h12 ξ
  have hsolve : D5.ModGammaSix A Q⁻¹ := by
    have hm := hv.mul (D5.ModEq.refl (D5.gamma G 6) Q⁻¹)
    simpa [mul_assoc] using hm
  exact hsolve.trans (formula34_wdoubleprime_positive_inv C P ξ)

/-! ## Separating the diagonal correction -/

/-- Split a weak final interval into its initial point and the strict final
interval.  Only commutativity modulo `γ₆` is used, so the statement is
independent of the concrete enumeration of `Fin n`. -/
theorem orderedProductWhere_le_split_lt
    {n : ℕ} (j : Fin n) (f : Fin n → G)
    (hf : ∀ k, j ≤ k → f k ∈ D5.gamma G 3) :
    D5.ModGammaSix (orderedProductWhere (j ≤ ·) f)
      (f j * orderedProductWhere (j < ·) f) := by
  classical
  let all := List.finRange n
  let weak := all.filter (j ≤ ·)
  let strict := all.filter (j < ·)
  have hweak : weak.Nodup := (List.nodup_finRange n).filter _
  have hstrict : strict.Nodup := (List.nodup_finRange n).filter _
  have hjnot : j ∉ strict := by simp [strict]
  have hperm : weak.Perm (j :: strict) := by
    apply (List.perm_ext_iff_of_nodup hweak (hstrict.cons hjnot)).2
    intro k
    simp only [weak, strict, List.mem_filter, List.mem_cons]
    constructor
    · rintro ⟨hkall, hle⟩
      rcases eq_or_lt_of_le (of_decide_eq_true hle) with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hkall, by simpa using hlt⟩
    · rintro (heq | ⟨hkall, hlt⟩)
      · subst k
        exact ⟨by simp [all], by simp⟩
      · exact ⟨hkall, by
          exact decide_eq_true (le_of_lt (of_decide_eq_true hlt))⟩
  unfold orderedProductWhere
  simpa [weak, strict] using D5.listProd_perm_gammaThree (hperm.map f)
    (fun x hx => by
      rcases List.mem_map.mp hx with ⟨k, hk, rfl⟩
      exact hf k (of_decide_eq_true (List.mem_filter.mp hk).2))

def formula34WExtraDiagonalProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    formula34WExtraFactor C P ξ i j j

/-- Split the additional `w` stream into its diagonal part `j = k` and
the off-diagonal part already eliminated by (35). -/
theorem formula34WExtraProduct_split_diagonal
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula34WExtraProduct C P ξ)
      (formula34WExtraDiagonalProduct C P ξ *
        formula34WExtraOffDiagonalProduct C P ξ) := by
  let E : Fin C.s → Fin C.s → Fin C.s → G :=
    formula34WExtraFactor C P ξ
  let D : Fin C.s → Fin C.s → G := fun i j => E i j j
  let O : Fin C.s → Fin C.s → G := fun i j =>
    orderedProductWhere (j < ·) (E i j)
  have hE : ∀ i j k, E i j k ∈ D5.gamma G 3 := fun i j k =>
    formula34WExtraFactor_mem_gamma3 C P ξ i j k
  have hD : ∀ i j, D i j ∈ D5.gamma G 3 := fun i j => hE i j j
  have hO : ∀ i j, O i j ∈ D5.gamma G 3 := by
    intro i j; apply orderedProductWhere_mem; intro k hjk; exact hE i j k
  have hsplitK : D5.ModGammaSix (formula34WExtraProduct C P ξ)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        D i j * O i j) := by
    unfold formula34WExtraProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    exact orderedProductWhere_le_split_lt j (E i j)
      (fun k hjk => hE i j k)
  have hsplitJ : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        D i j * O i j)
      (orderedProduct fun i =>
        (orderedProductWhere (i ≤ ·) (D i)) *
          (orderedProductWhere (i ≤ ·) (O i))) := by
    apply modEq_orderedProduct
    intro i
    exact D5.orderedProductWhere_pointwise_mul_gammaThree (i ≤ ·)
      (D i) (O i) (fun j hij => hD i j) (fun j hij => hO i j)
  let DB : Fin C.s → G := fun i => orderedProductWhere (i ≤ ·) (D i)
  let OB : Fin C.s → G := fun i => orderedProductWhere (i ≤ ·) (O i)
  have hDB : ∀ i, DB i ∈ D5.gamma G 3 := by
    intro i; apply orderedProductWhere_mem; intro j hij; exact hD i j
  have hOB : ∀ i, OB i ∈ D5.gamma G 3 := by
    intro i; apply orderedProductWhere_mem; intro j hij; exact hO i j
  have hsplitI := D5.orderedProduct_pointwise_mul_gammaThree DB OB hDB hOB
  exact hsplitK.trans <| hsplitJ.trans <| by
    simpa [formula34WExtraDiagonalProduct,
      formula34WExtraOffDiagonalProduct, E, D, O, DB, OB] using hsplitI

/-- Reversing the first two entries and inverting the weight-two entry
cancel each other after two further commutators. -/
theorem fourfold_first_inverse_swap_mod_gamma_six
    {ξ a x z : G} (hξ : ξ ∈ D5.gamma G 1) (ha : a ∈ D5.gamma G 2)
    (hx : x ∈ D5.gamma G 1) (hz : z ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm a⁻¹ ξ) x) z)
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a) x) z) := by
  have hi : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ξ a⁻¹) (D5.paperComm ξ a)⁻¹ := by
    exact D5.paperComm_inv_right_mod_gamma
      (n := 4) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hξ ha
  have hbase : D5.ModEq (D5.gamma G 4)
      (D5.paperComm a⁻¹ ξ) (D5.paperComm ξ a) := by
    rw [D5.paperComm_swap ξ a⁻¹]
    simpa only [inv_inv] using hi.inv
  have hx' := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hbase hx
  exact D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hx' hz

theorem formula22WeightTwoWord_mod_positive_inverse
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) :
    D5.ModEq (D5.gamma G 3) (formula22WeightTwoWord C P j)
      (formula32WeightTwoWord C P j)⁻¹ := by
  have hp := coordinateProduct_zpow_mod_gamma3 C (P.v j) (-1)
  simpa [formula22WeightTwoWord, formula32WeightTwoWord, zpow_neg] using hp.symm

/-- A local factor of line 7, after replacing the negative coordinate word
by the inverse positive word and swapping the first two entries. -/
theorem formula29_line_seven_factor_to_positive
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm (D5.paperComm (formula22WeightTwoWord C P j) ξ)
          (C.x1 j)) (C.x1 j) ^ TaharaArithmetic.binom2 (C.d j))
      (D5.paperComm
        (D5.paperComm (D5.paperComm ξ (formula32WeightTwoWord C P j))
          (C.x1 j)) (C.x1 j) ^ TaharaArithmetic.binom2 (C.d j)) := by
  let A := formula22WeightTwoWord C P j
  let B := formula32WeightTwoWord C P j
  let x := C.x1 j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hB : B ∈ D5.gamma G 2 := formula32WeightTwoWord_mem_gamma2 C P j
  have hx : x ∈ D5.gamma G 1 := by simp [x, D5.gamma]
  have hAB : D5.ModEq (D5.gamma G 3) A B⁻¹ := by
    simpa [A, B] using formula22WeightTwoWord_mod_positive_inverse C P j
  have h1 := D5.paperComm_left_of_modEq_gamma
    (r := 3) (s := 1) (by norm_num) (by norm_num) hAB hξ
  have h2 := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) h1 hx
  have h3 := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) h2 hx
  have hswap := fourfold_first_inverse_swap_mod_gamma_six hξ hB hx hx
  simpa [A, B, x] using
    (h3.trans hswap).zpow (TaharaArithmetic.binom2 (C.d j))

/-- The unsquared local congruence underlying formula (36). -/
theorem formula32_fourfold_congruent
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (ξ : G) (j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (formula32FirstLayerWord C P j)) (C.x1 j))
          (C.x1 j))
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (formula32WeightTwoWord C P j)) (C.x1 j))
          (C.x1 j) ^ TaharaArithmetic.binom2 (C.d j)) := by
  let A := formula32FirstLayerWord C P j
  let B := formula32WeightTwoWord C P j
  let F : G → G := fun a =>
    D5.paperComm (D5.paperComm (D5.paperComm ξ a) (C.x1 j)) (C.x1 j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA : A ∈ D5.gamma G 2 := formula32FirstLayerWord_mem_gamma2 C P j
  have hB : B ∈ D5.gamma G 2 := formula32WeightTwoWord_mem_gamma2 C P j
  have hw : IsGammaTwoPowerModGammaThree (orderInt C.d j)
      (B ^ TaharaArithmetic.binom2 (C.d j) * A⁻¹) := by
    simpa [formula32Word, formula32WeightTwoWord, A, B] using
      formula32 C P h11 j
  have hvanish : D5.ModGammaSix
      (F (B ^ TaharaArithmetic.binom2 (C.d j) * A⁻¹)) 1 :=
    fourfold_second_gammaTwoPower_vanish hξ hx hx
      (C.x1_order_power_mem_gamma2 j) hw
  have hsplit := fourfold_second_mul_mod_gamma_six hξ
    ((D5.gamma G 2).zpow_mem hB (TaharaArithmetic.binom2 (C.d j)))
    ((D5.gamma G 2).inv_mem hA) hx hx
  have hBpow := fourfold_second_zpow_mod_gamma_six hξ hB hx hx
    (TaharaArithmetic.binom2 (C.d j))
  have hAinv := fourfold_second_inv_mod_gamma_six hξ hA hx hx
  have hprod : D5.ModGammaSix
      (F B ^ TaharaArithmetic.binom2 (C.d j) * (F A)⁻¹) 1 := by
    have hs : D5.ModGammaSix
        (F (B ^ TaharaArithmetic.binom2 (C.d j) * A⁻¹))
        (F B ^ TaharaArithmetic.binom2 (C.d j) * (F A)⁻¹) := by
      simpa [F] using hsplit.trans (hBpow.mul hAinv)
    exact hs.symm.trans hvanish
  change D5.ModGammaSix (F A)
    (F B ^ TaharaArithmetic.binom2 (C.d j))
  change (F B ^ TaharaArithmetic.binom2 (C.d j) * (F A)⁻¹ :
    G ⧸ D5.gamma G 6) = 1 at hprod
  have heq : (F B ^ TaharaArithmetic.binom2 (C.d j) :
      G ⧸ D5.gamma G 6) = (F A : G ⧸ D5.gamma G 6) := by
    have h := congrArg (fun q : G ⧸ D5.gamma G 6 =>
      q * (F A : G ⧸ D5.gamma G 6)) hprod
    simpa [mul_assoc] using h
  exact heq.symm

def formula32FirstLayerFourfoldProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (formula32FirstLayerWord C P j)) (C.x1 j))
        (C.x1 j)

/-- Line 7 is the unsquared diagonal word whose square occurs in (36). -/
theorem formula29_line_seven_to_formula32_firstLayer
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (ξ : G) :
    D5.ModGammaSix (formula29LineSeven C P ξ)
      (formula32FirstLayerFourfoldProduct C P ξ) := by
  unfold formula29LineSeven formula32FirstLayerFourfoldProduct
  apply modEq_orderedProduct
  intro j
  exact (formula29_line_seven_factor_to_positive C P ξ j).trans
    (formula32_fourfold_congruent C P h11 ξ j).symm

/-- Exchange the two loops over the weak upper triangle. -/
theorem weakPairProduct_swap
    {s : ℕ} (f : Fin s → Fin s → G)
    (hf : ∀ i j, i ≤ j → f i j ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun j => orderedProductWhere (· ≤ j) fun i => f i j)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j => f i j) := by
  classical
  let all := List.finRange s
  let rows := (all ×ˢ all).filter fun ij => ij.1 ≤ ij.2
  let cols := ((all ×ˢ all).filter fun ji => ji.2 ≤ ji.1).map
    fun ji => (ji.2, ji.1)
  have hall : all.Nodup := by simpa [all] using List.nodup_finRange s
  have hswapInj : Function.Injective (fun ij : Fin s × Fin s => (ij.2, ij.1)) := by
    intro a b h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hrows : rows.Nodup := (hall.product hall).filter _
  have hcols : cols.Nodup := ((hall.product hall).filter _).map hswapInj
  have hpairs : rows.Perm cols := by
    apply (List.perm_ext_iff_of_nodup hrows hcols).2
    intro ij
    constructor
    · intro hij
      have hp := List.mem_filter.mp hij
      have hle := of_decide_eq_true hp.2
      apply List.mem_map.mpr
      refine ⟨(ij.2, ij.1), ?_, by simp⟩
      apply List.mem_filter.mpr
      exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
        by simpa using hle⟩
    · intro hij
      rcases List.mem_map.mp hij with ⟨ji, hji, rfl⟩
      have hp := List.mem_filter.mp hji
      have hle := of_decide_eq_true hp.2
      apply List.mem_filter.mpr
      exact ⟨List.mem_product.mpr ⟨by simp [all], by simp [all]⟩,
        by simpa using hle⟩
  have flattenFiltered : ∀ {α β : Type} (is : List α) (js : List β)
      (p : α → β → Prop) [DecidableRel p] (g : α → β → G),
      (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
        (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
          fun ij => g ij.1 ij.2).prod := by
    intro α β is js p inst g
    induction is with
    | nil => simp
    | cons i is ih =>
        rw [List.map_cons, List.prod_cons, List.product_cons,
          List.filter_append, List.map_append, List.prod_append, ih]
        congr 1
        have hlist :
            (js.filter (p i)).map (g i) =
              ((js.map fun b => (i, b)).filter fun ij => p ij.1 ij.2).map
                fun ij => g ij.1 ij.2 := by
          simp only [List.filter_map, List.map_map]
          rfl
        exact congrArg List.prod hlist
  have hright :
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j => f i j) =
      (rows.map fun ij => f ij.1 ij.2).prod := by
    unfold orderedProduct orderedProductWhere
    simpa [rows, all] using
      flattenFiltered all all (fun i j => i ≤ j) f
  have hleft :
      (orderedProduct fun j => orderedProductWhere (· ≤ j) fun i => f i j) =
      (cols.map fun ij => f ij.1 ij.2).prod := by
    unfold orderedProduct orderedProductWhere
    have h := flattenFiltered all all (fun j i => i ≤ j) (fun j i => f i j)
    simpa [cols, all, List.map_map] using h
  rw [hleft, hright]
  apply D5.listProd_perm_gammaThree (hpairs.symm.map _)
  intro x hx
  rcases List.mem_map.mp hx with ⟨ij, hij, rfl⟩
  have hij' : ij ∈ rows := hpairs.mem_iff.mpr hij
  exact hf ij.1 ij.2
    (of_decide_eq_true (List.mem_filter.mp hij').2)

def formula32WDiagonalBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) : G :=
  orderedProductWhere (· ≤ j) fun h =>
    formula34WExtraFactor C P ξ h j j

def formula32WDoublePrimeDiagonalBlock
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) : G :=
  orderedProductWhere (j < ·) fun h =>
    formula34WDoublePrimePositiveFactor C P ξ j j h

def formula34WDoublePrimeDiagonalPositiveProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => formula32WDoublePrimeDiagonalBlock C P ξ j

def formula34WDoublePrimeDiagonalMainProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => orderedProductWhere (j < ·) fun h =>
    formula34WDoublePrimeMainFactor C P ξ j j h

theorem formula32_firstLayer_factor_expanded
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (formula32FirstLayerWord C P j)) (C.x1 j))
          (C.x1 j))
      (formula32WDiagonalBlock C P ξ j *
        formula32WDoublePrimeDiagonalBlock C P ξ j) := by
  let L : G := orderedProductWhere (· ≤ j) fun h =>
    C.x1 h ^ (orderInt C.d h * P.w h j j)
  let H : G := orderedProductWhere (j < ·) fun h =>
    C.x1 h ^ (orderInt C.d h * P.w'' j j h)
  let F : G → G := fun a =>
    D5.paperComm (D5.paperComm (D5.paperComm ξ a) (C.x1 j)) (C.x1 j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hL : L ∈ D5.gamma G 2 := by
    apply orderedProductWhere_mem
    intro h hh
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  have hH : H ∈ D5.gamma G 2 := by
    apply orderedProductWhere_mem
    intro h hh
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  have hsplit : D5.ModGammaSix (F (L * H)) (F L * F H) :=
    fourfold_second_mul_mod_gamma_six hξ hL hH hx hx
  have hlow : D5.ModGammaSix (F L) (formula32WDiagonalBlock C P ξ j) := by
    have hc := fourfold_second_orderedProductWhere_mod_gamma_six (· ≤ j)
      (fun h => C.x1 h ^ (orderInt C.d h * P.w h j j)) hξ
      (fun h hh => by
        simp only
        rw [zpow_mul]
        exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _)
      hx hx
    refine hc.trans ?_
    apply modEq_orderedProductWhere
    intro h hh
    simp only
    rw [zpow_mul]
    simpa [F, formula34WExtraFactor] using
      fourfold_second_zpow_mod_gamma_six hξ
        (C.x1_order_power_mem_gamma2 h) hx hx (P.w h j j)
  have hhigh : D5.ModGammaSix (F H)
      (formula32WDoublePrimeDiagonalBlock C P ξ j) := by
    have hc := fourfold_second_orderedProductWhere_mod_gamma_six (j < ·)
      (fun h => C.x1 h ^ (orderInt C.d h * P.w'' j j h)) hξ
      (fun h hh => by
        simp only
        rw [zpow_mul]
        exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _)
      hx hx
    refine hc.trans ?_
    apply modEq_orderedProductWhere
    intro h hh
    simp only
    rw [zpow_mul]
    simpa [F, formula34WDoublePrimePositiveFactor] using
      fourfold_second_zpow_mod_gamma_six hξ
        (C.x1_order_power_mem_gamma2 h) hx hx (P.w'' j j h)
  simpa [formula32FirstLayerWord, L, H, F] using
    hsplit.trans (hlow.mul hhigh)

theorem formula32_firstLayer_product_expanded
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula32FirstLayerFourfoldProduct C P ξ)
      (formula34WExtraDiagonalProduct C P ξ *
        formula34WDoublePrimeDiagonalPositiveProduct C P ξ) := by
  let L : Fin C.s → G := formula32WDiagonalBlock C P ξ
  let H : Fin C.s → G := formula32WDoublePrimeDiagonalBlock C P ξ
  have hL : ∀ j, L j ∈ D5.gamma G 3 := by
    intro j; apply orderedProductWhere_mem; intro h hh
    exact formula34WExtraFactor_mem_gamma3 C P ξ h j j
  have hH : ∀ j, H j ∈ D5.gamma G 3 := by
    intro j; apply orderedProductWhere_mem; intro h hh
    exact formula34WDoublePrimePositiveFactor_mem_gamma3 C P ξ j j h
  have hlocal : D5.ModGammaSix (formula32FirstLayerFourfoldProduct C P ξ)
      (orderedProduct fun j => L j * H j) := by
    unfold formula32FirstLayerFourfoldProduct
    apply modEq_orderedProduct
    intro j
    exact formula32_firstLayer_factor_expanded C P ξ j
  have hsplit := D5.orderedProduct_pointwise_mul_gammaThree L H hL hH
  have hreindex : D5.ModGammaSix (orderedProduct L)
      (formula34WExtraDiagonalProduct C P ξ) := by
    simpa [L, formula32WDiagonalBlock, formula34WExtraDiagonalProduct] using
      weakPairProduct_swap (fun i j => formula34WExtraFactor C P ξ i j j)
        (fun i j hij => formula34WExtraFactor_mem_gamma3 C P ξ i j j)
  exact hlocal.trans <| hsplit.trans <| by
    simpa [H, formula34WDoublePrimeDiagonalPositiveProduct] using
      hreindex.mul (D5.ModEq.refl (D5.gamma G 6) (orderedProduct H))

theorem formula32FirstLayerFourfoldFactor_mem_gamma3
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) :
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (formula32FirstLayerWord C P j)) (C.x1 j))
        (C.x1 j) ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hA := formula32FirstLayerWord_mem_gamma2 C P j
  have hx : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact D5.gamma_antitone G (by norm_num : 3 ≤ 5) <|
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hA) hx) hx

/-- Formula (36) says precisely that the square of the unsquared diagonal
word is trivial modulo `γ₆`. -/
theorem formula32_firstLayer_product_squared_vanish
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (ξ : G) :
    D5.ModGammaSix (formula32FirstLayerFourfoldProduct C P ξ ^ (2 : ℤ)) 1 := by
  let F : Fin C.s → G := fun j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (formula32FirstLayerWord C P j)) (C.x1 j))
        (C.x1 j)
  have hF : ∀ j, F j ∈ D5.gamma G 3 := fun j =>
    formula32FirstLayerFourfoldFactor_mem_gamma3 C P ξ j
  have hp := D5.orderedProduct_zpow_gammaThree F hF (2 : ℤ)
  have h36 := formula36 C P h11 ξ
  have hleft : D5.ModGammaSix
      (orderedProduct fun j => F j ^ (2 : ℤ)) 1 := by
    simpa [formula36LeftProduct, F] using h36.1.trans h36.2
  simpa [formula32FirstLayerFourfoldProduct, F] using hp.trans hleft

theorem formula34_wdoubleprime_diagonal_positive_inv
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula34WDoublePrimeDiagonalPositiveProduct C P ξ)⁻¹
      (formula34WDoublePrimeDiagonalMainProduct C P ξ) := by
  let Pos : Fin C.s → Fin C.s → G := fun j h =>
    formula34WDoublePrimePositiveFactor C P ξ j j h
  let Neg : Fin C.s → Fin C.s → G := fun j h =>
    formula34WDoublePrimeMainFactor C P ξ j j h
  let PR : Fin C.s → G := fun j => orderedProductWhere (j < ·) (Pos j)
  let NR : Fin C.s → G := fun j => orderedProductWhere (j < ·) (Neg j)
  have hPos : ∀ j h, Pos j h ∈ D5.gamma G 3 := fun j h =>
    formula34WDoublePrimePositiveFactor_mem_gamma3 C P ξ j j h
  have hPR : ∀ j, PR j ∈ D5.gamma G 3 := by
    intro j; apply orderedProductWhere_mem; intro h hjh; exact hPos j h
  have hrow : ∀ j, D5.ModGammaSix (PR j)⁻¹ (NR j) := by
    intro j
    have hp := orderedProductWhere_zpow_gammaThree (j < ·) (Pos j)
      (fun h hjh => hPos j h) (-1)
    have hr : D5.ModGammaSix
        (orderedProductWhere (j < ·) fun h => Pos j h ^ (-1 : ℤ))
        (orderedProductWhere (j < ·) (Neg j)) := by
      apply modEq_orderedProductWhere
      intro h hjh
      simpa [Pos, Neg, formula34WDoublePrimePositiveFactor,
        formula34WDoublePrimeMainFactor, zpow_neg] using
          D5.ModEq.refl (D5.gamma G 6) (Neg j h)
    simpa [PR, NR, zpow_neg] using hp.trans hr
  have hp := D5.orderedProduct_zpow_gammaThree PR hPR (-1)
  have hr : D5.ModGammaSix
      (orderedProduct fun j => PR j ^ (-1 : ℤ)) (orderedProduct NR) := by
    apply modEq_orderedProduct
    intro j
    simpa [zpow_neg] using hrow j
  simpa [formula34WDoublePrimeDiagonalPositiveProduct,
    formula32WDoublePrimeDiagonalBlock,
    formula34WDoublePrimeDiagonalMainProduct, Pos, Neg, PR, NR, zpow_neg] using
      hp.trans hr

/-- The diagonal additional `w` stream together with line 7 gives the
diagonal part of the third principal `w''` stream. -/
theorem formula36_yields_wdoubleprime_diagonal_main
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (ξ : G) :
    D5.ModGammaSix
      (formula29LineSeven C P ξ * formula34WExtraDiagonalProduct C P ξ)
      (formula34WDoublePrimeDiagonalMainProduct C P ξ) := by
  let L := formula29LineSeven C P ξ
  let D := formula34WExtraDiagonalProduct C P ξ
  let H := formula34WDoublePrimeDiagonalPositiveProduct C P ξ
  let X := formula32FirstLayerFourfoldProduct C P ξ
  have hL : D5.ModGammaSix L X := by
    simpa [L, X] using formula29_line_seven_to_formula32_firstLayer C P h11 ξ
  have hX : D5.ModGammaSix X (D * H) := by
    simpa [X, D, H] using formula32_firstLayer_product_expanded C P ξ
  have hsq : D5.ModGammaSix (X * X) 1 := by
    simpa [zpow_two] using formula32_firstLayer_product_squared_vanish C P h11 ξ
  have hv : D5.ModGammaSix ((L * D) * H) 1 := by
    have hfirst : D5.ModGammaSix ((L * D) * H) ((X * D) * H) :=
      (hL.mul (D5.ModEq.refl (D5.gamma G 6) D)).mul
        (D5.ModEq.refl (D5.gamma G 6) H)
    have hsecond : D5.ModGammaSix ((X * D) * H) (X * X) := by
      simpa only [mul_assoc] using
        ((D5.ModEq.refl (D5.gamma G 6) X).mul hX).symm
    exact hfirst.trans (hsecond.trans hsq)
  have hsolve : D5.ModGammaSix (L * D) H⁻¹ := by
    have hm := hv.mul (D5.ModEq.refl (D5.gamma G 6) H⁻¹)
    simpa [mul_assoc] using hm
  exact hsolve.trans (formula34_wdoubleprime_diagonal_positive_inv C P ξ)

/-- The full third principal product of (34), including both `i = j < k`
and `i < j < k`. -/
def formula34WDoublePrimeFullMainProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j < ·) fun k =>
      formula34WDoublePrimeMainFactor C P ξ i j k

theorem formula34_wdoubleprime_join_diagonal_strict
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      (formula34WDoublePrimeDiagonalMainProduct C P ξ *
        formula34WDoublePrimeMainProduct C P ξ)
      (formula34WDoublePrimeFullMainProduct C P ξ) := by
  let B : Fin C.s → Fin C.s → G := fun i j =>
    orderedProductWhere (j < ·) fun k =>
      formula34WDoublePrimeMainFactor C P ξ i j k
  have hB : ∀ i j, B i j ∈ D5.gamma G 3 := by
    intro i j
    apply orderedProductWhere_mem
    intro k hjk
    exact formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i j k
  have hsplitJ : D5.ModGammaSix
      (formula34WDoublePrimeFullMainProduct C P ξ)
      (orderedProduct fun i =>
        B i i * orderedProductWhere (i < ·) (B i)) := by
    unfold formula34WDoublePrimeFullMainProduct
    apply modEq_orderedProduct
    intro i
    exact orderedProductWhere_le_split_lt i (B i)
      (fun j hij => hB i j)
  let D : Fin C.s → G := fun i => B i i
  let S : Fin C.s → G := fun i => orderedProductWhere (i < ·) (B i)
  have hD : ∀ i, D i ∈ D5.gamma G 3 := fun i => hB i i
  have hS : ∀ i, S i ∈ D5.gamma G 3 := by
    intro i; apply orderedProductWhere_mem; intro j hij; exact hB i j
  have hsplitI := D5.orderedProduct_pointwise_mul_gammaThree D S hD hS
  have hcollect : D5.ModGammaSix
      (formula34WDoublePrimeDiagonalMainProduct C P ξ *
        formula34WDoublePrimeMainProduct C P ξ)
      (orderedProduct fun i => D i * S i) := by
    simpa [D, S, B, formula34WDoublePrimeDiagonalMainProduct,
      formula34WDoublePrimeMainProduct, formula34WDoublePrimeMainBlock] using
        hsplitI.symm
  exact hcollect.trans hsplitJ.symm

/-- Once the two Jacobi streams have been separated, formulas (35) and
(36) remove all additional factors and leave the three principal products
of (34). -/
theorem formula34_transformed_streams
    (C : Context G) (P : Parameters C.s C.t)
    (h11 : P.Condition11) (h12 : P.Condition12) (ξ : G) :
    D5.ModGammaSix
      ((formula29LineSeven C P ξ *
          (formula34WExtraProduct C P ξ * formula34WMainProduct C P ξ)) *
        (formula34WPrimeExtraProduct C P ξ *
          formula34WPrimeMainProduct C P ξ))
      ((formula34WMainProduct C P ξ * formula34WPrimeMainProduct C P ξ) *
        formula34WDoublePrimeFullMainProduct C P ξ) := by
  let L := formula29LineSeven C P ξ
  let D := formula34WExtraDiagonalProduct C P ξ
  let O := formula34WExtraOffDiagonalProduct C P ξ
  let M := formula34WMainProduct C P ξ
  let E := formula34WPrimeExtraProduct C P ξ
  let N := formula34WPrimeMainProduct C P ξ
  let HD := formula34WDoublePrimeDiagonalMainProduct C P ξ
  let HS := formula34WDoublePrimeMainProduct C P ξ
  have hL : L ∈ D5.gamma G 3 := by
    dsimp [L]
    apply orderedProduct_mem
    intro j
    exact formula22_correction_mem_gamma3 C P ξ j
  have hD : D ∈ D5.gamma G 3 := by
    dsimp [D, formula34WExtraDiagonalProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    exact formula34WExtraFactor_mem_gamma3 C P ξ i j j
  have hO : O ∈ D5.gamma G 3 := by
    dsimp [O, formula34WExtraOffDiagonalProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WExtraFactor_mem_gamma3 C P ξ i j k
  have hM : M ∈ D5.gamma G 3 := by
    dsimp [M, formula34WMainProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WMainFactor_mem_gamma3 C P ξ i j k
  have hE : E ∈ D5.gamma G 3 := by
    dsimp [E, formula34WPrimeExtraProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WPrimeExtraFactor_mem_gamma3 C P ξ i j k
  have hN : N ∈ D5.gamma G 3 := by
    dsimp [N, formula34WPrimeMainProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WPrimeMainFactor_mem_gamma3 C P ξ i j k
  have hHD : HD ∈ D5.gamma G 3 := by
    dsimp [HD, formula34WDoublePrimeDiagonalMainProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro k hik
    exact formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i i k
  have hHS : HS ∈ D5.gamma G 3 := by
    dsimp [HS, formula34WDoublePrimeMainProduct,
      formula34WDoublePrimeMainBlock]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i j k
  have hsplit : D5.ModGammaSix
      ((L * (formula34WExtraProduct C P ξ * M)) * (E * N))
      ((L * ((D * O) * M)) * (E * N)) :=
    ((D5.ModEq.refl (D5.gamma G 6) L).mul
      ((formula34WExtraProduct_split_diagonal C P ξ).mul
        (D5.ModEq.refl (D5.gamma G 6) M))).mul
          (D5.ModEq.refl (D5.gamma G 6) (E * N))
  have hp : [L, D, O, M, E, N].Perm [L, D, O, E, M, N] :=
    List.Perm.cons L <| List.Perm.cons D <| List.Perm.cons O <|
      (List.Perm.swap M E [N]).symm
  have hperm : D5.ModGammaSix
      ((L * ((D * O) * M)) * (E * N))
      (((L * D) * (O * E)) * (M * N)) := by
    simpa [List.prod_cons, List.prod_nil, mul_assoc] using
      D5.listProd_perm_gammaThree hp (fun x hx => by
        simp only [List.mem_cons] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl | hx
        · exact hL
        · exact hD
        · exact hO
        · exact hM
        · exact hE
        · rcases hx with rfl | hx
          · exact hN
          · simp at hx)
  have hcancel : D5.ModGammaSix
      (((L * D) * (O * E)) * (M * N))
      ((HD * HS) * (M * N)) :=
    ((formula36_yields_wdoubleprime_diagonal_main C P h11 ξ).mul
      (formula35_yields_wdoubleprime_main C P h12 ξ)).mul
        (D5.ModEq.refl (D5.gamma G 6) (M * N))
  have hcomm : D5.ModGammaSix ((HD * HS) * (M * N))
      ((M * N) * (HD * HS)) :=
    D5.mul_comm_mod_gamma (n := 6) (r := 3) (s := 3)
      (by norm_num) (by norm_num) (by norm_num)
      ((D5.gamma G 3).mul_mem hHD hHS) ((D5.gamma G 3).mul_mem hM hN)
  have hjoin := formula34_wdoubleprime_join_diagonal_strict C P ξ
  simpa [L, D, O, M, E, N, HD, HS] using
    hsplit.trans (hperm.trans (hcancel.trans (hcomm.trans
      ((D5.ModEq.refl (D5.gamma G 6) (M * N)).mul hjoin))))

/-- Lines 7 and 9--12 of formula (29), in their displayed order. -/
def formula34LastFiveDisplayedProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  ((((formula29LineSeven C P ξ * formula28WLeftDisplayedStream C P ξ) *
      formula28WRightDisplayedStream C P ξ) *
    formula28WPrimeDisplayedStream C P ξ) * formula29LineTwelve C P ξ)

/-- Formula (34): the five relevant streams of (29) are transformed into
the three displayed principal products, with all finite index domains. -/
theorem formula34
    (C : Context G) (P : Parameters C.s C.t)
    (h11 : P.Condition11) (h12 : P.Condition12) (ξ : G) :
    D5.ModGammaSix (formula34LastFiveDisplayedProduct C P ξ)
      ((formula34WMainProduct C P ξ * formula34WPrimeMainProduct C P ξ) *
        formula34WDoublePrimeFullMainProduct C P ξ) := by
  let L := formula29LineSeven C P ξ
  let A := formula28WLeftDisplayedStream C P ξ
  let B := formula28WRightDisplayedStream C P ξ
  let E := formula28WPrimeDisplayedStream C P ξ
  let T := formula29LineTwelve C P ξ
  have hE : E ∈ D5.gamma G 3 := by
    dsimp [E, formula28WPrimeDisplayedStream]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    have hj : C.x1 j ^ orderInt C.d j ∈ D5.gamma G 2 :=
      C.x1_order_power_mem_gamma2 j
    have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    apply D5.gamma_antitone G (by norm_num : 3 ≤ 5)
    apply (D5.gamma G 5).zpow_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hk) hξ) hi
  have hT : T ∈ D5.gamma G 3 := by
    dsimp [T, formula29LineTwelve]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    simpa [formula34WLineTwelveFactor] using
      (formula34_w_line_factors_mem_gamma3 C P ξ i j k).2.2
  have hreorder : D5.ModGammaSix
      ((((L * A) * B) * E) * T) ((L * ((A * B) * T)) * E) := by
    simpa only [mul_assoc, mul_one] using
      D5.gammaThree_interchange (a := (L * A) * B) (d := (1 : G)) hE hT
  have hreplace : D5.ModGammaSix ((L * ((A * B) * T)) * E)
      ((L * (formula34WExtraProduct C P ξ *
          formula34WMainProduct C P ξ)) *
        (formula34WPrimeExtraProduct C P ξ *
          formula34WPrimeMainProduct C P ξ)) :=
    ((D5.ModEq.refl (D5.gamma G 6) L).mul
      (formula34_w_streams C P ξ)).mul
        (formula34_wprime_stream C P ξ)
  simpa [formula34LastFiveDisplayedProduct, L, A, B, E, T] using
    hreorder.trans (hreplace.trans (formula34_transformed_streams C P h11 h12 ξ))

end

end D5.Tahara
