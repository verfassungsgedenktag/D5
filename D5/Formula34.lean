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

end

end D5.Tahara
