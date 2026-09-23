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

end

end D5.Tahara
