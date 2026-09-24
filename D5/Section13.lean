import D5.Section12

/-!
# Section 13: repeated indices

This file formalizes the pairwise calculations (40)--(45).  Throughout the
section `i < j`.  Integer quotients printed in the paper are represented by
`orderRatio d i j`; the corresponding divisibility is supplied by the cyclic
basis in `Context`.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-! ## Arithmetic forms of the exponents in (40)--(41) -/

def formula40Exponent
    (C : Context G) (P : Parameters C.s C.t) (i j : Fin C.s) : ℤ :=
  P.w i j j + orderRatio C.d i j * P.w' i j j

def formula41Exponent
    (C : Context G) (P : Parameters C.s C.t) (i j : Fin C.s) : ℤ :=
  P.w i i j + orderRatio C.d i j * P.w'' i i j

/-- Denominator-free form of the exponent on the right of (40). -/
theorem formula40_exponent_identity
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    {i j : Fin C.s} (hij : i < j) :
    orderInt C.d i * formula40Exponent C P i j =
      P.u i j * TaharaArithmetic.binom2 (C.d j) := by
  exact (pairConsequences C P hP hij).equation12.symm

/-- Denominator-free form of the exponent on the right of (41). -/
theorem formula41_exponent_identity
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    {i j : Fin C.s} (hij : i < j) :
    orderInt C.d i * formula41Exponent C P i j =
      -(P.u i j * orderRatio C.d i j *
        TaharaArithmetic.binom2 (C.d i)) := by
  have h := (pairConsequences C P hP hij).equation13
  unfold formula41Exponent
  linarith

/-! ## Formula (40) -/

def formula40First
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
    (C.x1 i ^ orderInt C.d i) ^ P.w i j j

def formula40Second
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 j)) (C.x1 j ^ orderInt C.d j))
      (C.x1 i) ^ P.w' i j j

def formula40Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
    (C.x1 i ^ orderInt C.d i) ^ formula40Exponent C P i j

/-- After its weight-five corrections are killed by (14), the second factor
of (40) is the first basic factor raised to `q * w'`. -/
theorem formula40_second_transfer
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula40Second C P ξ i j)
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (C.x1 j)) (C.x1 j))
          (C.x1 i ^ orderInt C.d i) ^
            (orderRatio C.d i j * P.w' i j j)) := by
  let X := C.x1 i
  let Y := C.x1 j
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) X
  let I := D5.paperComm A X
  let J := D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) Y) X
  let d := orderInt C.d i
  let e := orderInt C.d j
  let q := orderRatio C.d i j
  let m := P.w' i j j
  let B2d := TaharaArithmetic.binom2 (C.d i)
  let B2e := TaharaArithmetic.binom2 (C.d j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have h2 : D5.paperComm ξ Y ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY
  have h3 : D5.paperComm (D5.paperComm ξ Y) Y ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) h2 hY
  have hA4 : A ∈ D5.gamma G 4 := by
    simpa [A] using D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) h3 hX
  have hI5 : I ∈ D5.gamma G 5 := by
    simpa [I] using D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) hA4 hX
  have h4J : D5.paperComm
      (D5.paperComm (D5.paperComm ξ Y) Y) Y ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) h3 hY
  have hJ5 : J ∈ D5.gamma G 5 := by
    simpa [J] using D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) h4J hX
  have horder : e = d * q := by
    simpa [d, e, q] using C.orderInt_eq_mul_ratio (le_of_lt hij)
  have hlast0 := weightThree_comm_zpow_right_hallPetresco h3 hX (C.d i)
  have hthird0 := fourfold_zpow_third_entry hξ hY hY hX (C.d j)
  have hlast : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y)
        (X ^ d) ^ (q * m))
      (A ^ (d * (q * m)) * I ^ (B2d * (q * m))) := by
    have hp := (hlast0.zpow (q * m)).trans <|
      D5.gammaThree_mul_zpow
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA4) d)
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hI5) B2d)
        (q * m)
    rw [← zpow_mul, ← zpow_mul] at hp
    simpa [A, I, d, B2d, X, Y, orderInt] using hp
  have hthird : D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ Y) (Y ^ e)) X ^ m)
      (A ^ (e * m) * J ^ (B2e * m)) := by
    have hp := (hthird0.zpow m).trans <|
      D5.gammaThree_mul_zpow
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA4) e)
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hJ5) B2e)
        m
    rw [← zpow_mul, ← zpow_mul] at hp
    simpa [A, J, e, B2e, X, Y, orderInt] using hp
  have hIbase : D5.ModGammaSix (I ^ d) 1 := by
    simpa [I, d, X] using
      weightFive_last_entry_power_vanish_general hA4 hX
        (C.x1_order_power_mem_gamma2 i)
  have hJbase : D5.ModGammaSix (J ^ d) 1 := by
    simpa [J, d, X, Y] using
      weightFive_last_entry_power_vanish_general h4J hX
        (C.x1_order_power_mem_gamma2 i)
  have hpairs := pairConsequences C P hP hij
  have hIdiv : d ∣ B2d * (q * m) := by
    simpa [d, q, m, B2d, mul_comm, mul_left_comm, mul_assoc] using
      hpairs.dvd_q_wpijj_B2d
  have hJdiv : d ∣ B2e * m := by
    simpa [d, m, B2e, mul_comm] using hpairs.dvd14_wpijj
  have hIv := D5.modGammaSix_zpow_eq_one_of_dvd hIbase hIdiv
  have hJv := D5.modGammaSix_zpow_eq_one_of_dvd hJbase hJdiv
  have hlastClean : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y)
        (X ^ d) ^ (q * m)) (A ^ (d * (q * m))) :=
    hlast.trans <| by simpa using
      (D5.ModEq.refl (D5.gamma G 6) (A ^ (d * (q * m)))).mul hIv
  have hthirdClean : D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ Y) (Y ^ e)) X ^ m) (A ^ (e * m)) :=
    hthird.trans <| by simpa using
      (D5.ModEq.refl (D5.gamma G 6) (A ^ (e * m))).mul hJv
  have hexp : e * m = d * (q * m) := by rw [horder]; ring
  rw [hexp] at hthirdClean
  simpa [formula40Second, X, Y, d, e, q, m] using
    hthirdClean.trans hlastClean.symm

/-- Formula (40), including the exact exponent obtained from equation (12). -/
theorem formula40
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix
      (formula40First C P ξ i j * formula40Second C P ξ i j)
      (formula40Right C P ξ i j) := by
  have ht := formula40_second_transfer C P hP ξ hij
  let A := D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 j)) (C.x1 j))
      (C.x1 i ^ orderInt C.d i)
  have hA : A ∈ D5.gamma G 3 := by
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 :=
      C.x1_order_power_mem_gamma2 i
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hj) hj) hi
  have hmul := (D5.ModEq.refl (D5.gamma G 6)
    (formula40First C P ξ i j)).mul ht
  have hcollect : D5.ModGammaSix
      (A ^ P.w i j j * A ^ (orderRatio C.d i j * P.w' i j j))
      (A ^ formula40Exponent C P i j) := by
    rw [← zpow_add]
    rfl
  simpa [formula40First, formula40Right, A] using hmul.trans hcollect

/-! ## Formula (41) -/

def formula41First
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
    (C.x1 i ^ orderInt C.d i) ^ P.w i i j

def formula41Second
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 j ^ orderInt C.d j)) (C.x1 i))
      (C.x1 i) ^ P.w'' i i j

def formula41Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
    (C.x1 i ^ orderInt C.d i) ^ formula41Exponent C P i j

/-- After its corrections are killed by (14), the second factor of (41) is
its first basic factor raised to `q * w''`. -/
theorem formula41_second_transfer
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula41Second C P ξ i j)
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (C.x1 j)) (C.x1 i))
          (C.x1 i ^ orderInt C.d i) ^
            (orderRatio C.d i j * P.w'' i i j)) := by
  let X := C.x1 i
  let Y := C.x1 j
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ Y) X) X
  let I := D5.paperComm A X
  let J := D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) X) X
  let d := orderInt C.d i
  let e := orderInt C.d j
  let q := orderRatio C.d i j
  let m := P.w'' i i j
  let B2d := TaharaArithmetic.binom2 (C.d i)
  let B2e := TaharaArithmetic.binom2 (C.d j)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have h2 : D5.paperComm ξ Y ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY
  have h3 : D5.paperComm (D5.paperComm ξ Y) X ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) h2 hX
  have hA4 : A ∈ D5.gamma G 4 := by
    simpa [A] using D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) h3 hX
  have hI5 : I ∈ D5.gamma G 5 := by
    simpa [I] using D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) hA4 hX
  have h3J : D5.paperComm (D5.paperComm ξ Y) Y ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) h2 hY
  have h4J : D5.paperComm
      (D5.paperComm (D5.paperComm ξ Y) Y) X ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) h3J hX
  have hJ5 : J ∈ D5.gamma G 5 := by
    simpa [J] using D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) h4J hX
  have horder : e = d * q := by
    simpa [d, e, q] using C.orderInt_eq_mul_ratio (le_of_lt hij)
  have hlast0 := weightThree_comm_zpow_right_hallPetresco h3 hX (C.d i)
  have hsecond0 := fourfold_zpow_second_entry hξ hY hX hX (C.d j)
  have hlast : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) X)
        (X ^ d) ^ (q * m))
      (A ^ (d * (q * m)) * I ^ (B2d * (q * m))) := by
    have hp := (hlast0.zpow (q * m)).trans <|
      D5.gammaThree_mul_zpow
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA4) d)
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hI5) B2d)
        (q * m)
    rw [← zpow_mul, ← zpow_mul] at hp
    simpa [A, I, d, B2d, X, Y, orderInt] using hp
  have hsecond : D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (Y ^ e)) X) X ^ m)
      (A ^ (e * m) * J ^ (B2e * m)) := by
    have hp := (hsecond0.zpow m).trans <|
      D5.gammaThree_mul_zpow
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA4) e)
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hJ5) B2e)
        m
    rw [← zpow_mul, ← zpow_mul] at hp
    simpa [A, J, e, B2e, X, Y, orderInt] using hp
  have hIbase : D5.ModGammaSix (I ^ d) 1 := by
    simpa [I, d, X] using
      weightFive_last_entry_power_vanish_general hA4 hX
        (C.x1_order_power_mem_gamma2 i)
  have hJbase : D5.ModGammaSix (J ^ d) 1 := by
    simpa [J, d, X, Y] using
      weightFive_last_entry_power_vanish_general h4J hX
        (C.x1_order_power_mem_gamma2 i)
  have hpairs := pairConsequences C P hP hij
  have hIdiv : d ∣ B2d * (q * m) := by
    simpa [d, q, m, B2d, mul_comm, mul_left_comm, mul_assoc] using
      hpairs.dvd_q_wppiij_B2d
  have hJdiv : d ∣ B2e * m := by
    simpa [d, m, B2e, mul_comm] using hpairs.dvd14_wppiij
  have hIv := D5.modGammaSix_zpow_eq_one_of_dvd hIbase hIdiv
  have hJv := D5.modGammaSix_zpow_eq_one_of_dvd hJbase hJdiv
  have hlastClean : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) X)
        (X ^ d) ^ (q * m)) (A ^ (d * (q * m))) :=
    hlast.trans <| by simpa using
      (D5.ModEq.refl (D5.gamma G 6) (A ^ (d * (q * m)))).mul hIv
  have hsecondClean : D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (Y ^ e)) X) X ^ m) (A ^ (e * m)) :=
    hsecond.trans <| by simpa using
      (D5.ModEq.refl (D5.gamma G 6) (A ^ (e * m))).mul hJv
  have hexp : e * m = d * (q * m) := by rw [horder]; ring
  rw [hexp] at hsecondClean
  simpa [formula41Second, X, Y, d, e, q, m] using
    hsecondClean.trans hlastClean.symm

/-- Formula (41), including the exact exponent obtained from equation (13). -/
theorem formula41
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix
      (formula41First C P ξ i j * formula41Second C P ξ i j)
      (formula41Right C P ξ i j) := by
  have ht := formula41_second_transfer C P hP ξ hij
  let A := D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 j)) (C.x1 i))
      (C.x1 i ^ orderInt C.d i)
  have hmul := (D5.ModEq.refl (D5.gamma G 6)
    (formula41First C P ξ i j)).mul ht
  have hcollect : D5.ModGammaSix
      (A ^ P.w i i j * A ^ (orderRatio C.d i j * P.w'' i i j))
      (A ^ formula41Exponent C P i j) := by
    rw [← zpow_add]
    rfl
  simpa [formula41First, formula41Right, A] using hmul.trans hcollect

/-! ## Formula (42) -/

/-- Swapping the first two weight-one entries changes the sign after two
further commutators.  The possible inversion error has reached weight six. -/
theorem fourfold_swap_first_two
    {a b c z : G} (ha : a ∈ D5.gamma G 1) (hb : b ∈ D5.gamma G 1)
    (hc : c ∈ D5.gamma G 1) (hz : z ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm a b) c) z)
      (D5.paperComm (D5.paperComm (D5.paperComm b a) c) z)⁻¹ := by
  let q := D5.paperComm b a
  let r := D5.paperComm q c
  have hq : q ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hb ha
  have hr : r ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hc
  have hinner : D5.ModEq (D5.gamma G 5)
      (D5.paperComm q⁻¹ c) r⁻¹ := by
    simpa [r] using D5.paperComm_inv_left_mod_gamma
      (n := 5) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hc
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hz
  have hinv : D5.ModGammaSix
      (D5.paperComm r⁻¹ z) (D5.paperComm r z)⁻¹ := by
    simpa using D5.paperComm_inv_left_mod_gamma
      (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hr hz
  rw [D5.paperComm_swap b a]
  simpa [q, r] using hlift.trans hinv

/-- Cancellation of one factor of the cyclic order in the divisibility used
for the binomial correction in formula (42). -/
theorem dvd_formula42_correction
    {d r n b : ℤ} (hd : d ≠ 0) (hr : d * r = n)
    (hsq : d * d ∣ n * b) : d ∣ r * b := by
  rcases hsq with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  apply mul_left_cancel₀ hd
  calc
    d * (r * b) = n * b := by rw [← hr]; ring
    _ = d * d * k := hk
    _ = d * k * d := by ring
    _ = d * (d * k) := by ring


def formula42Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 j) ξ) (C.x1 j)) (C.x1 i) ^
      (P.u i j * TaharaArithmetic.binom2 (C.d j)) *
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 j) ξ) (C.x1 i)) (C.x1 i) ^
      (-P.u i j * TaharaArithmetic.binom2 (C.d j))

def formula42Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
    (C.x1 i ^ orderInt C.d i) ^ (-formula40Exponent C P i j) *
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
    (C.x1 i ^ orderInt C.d i) ^ formula40Exponent C P i j

/-- Formula (42).  The binomial corrections created by moving `d(i)` into
the last entry vanish by the first divisibility in (15). -/
theorem formula42
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula42Left C P ξ i j)
      (formula42Right C P ξ i j) := by
  let X := C.x1 i
  let Y := C.x1 j
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) X
  let B := D5.paperComm (D5.paperComm (D5.paperComm ξ Y) X) X
  let IA := D5.paperComm A X
  let IB := D5.paperComm B X
  let d := orderInt C.d i
  let n := P.u i j * TaharaArithmetic.binom2 (C.d j)
  let r := formula40Exponent C P i j
  let b := TaharaArithmetic.binom2 (C.d i)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hξY : D5.paperComm ξ Y ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY
  have hξYY : D5.paperComm (D5.paperComm ξ Y) Y ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξY hY
  have hξYX : D5.paperComm (D5.paperComm ξ Y) X ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξY hX
  have hA4 : A ∈ D5.gamma G 4 := by
    simpa [A] using D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) hξYY hX
  have hB4 : B ∈ D5.gamma G 4 := by
    simpa [B] using D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) hξYX hX
  have hIA5 : IA ∈ D5.gamma G 5 := by
    simpa [IA] using D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) hA4 hX
  have hIB5 : IB ∈ D5.gamma G 5 := by
    simpa [IB] using D5.paperComm_mem_gamma_add (r := 4) (s := 1)
      (by norm_num) (by norm_num) hB4 hX
  have hd : d ≠ 0 := by
    simp [d, orderInt, Nat.ne_of_gt (lt_trans Nat.zero_lt_one (C.d_gt_one i))]
  have hdr : d * r = n := by
    simpa [d, r, n] using formula40_exponent_identity C P hP hij
  have hdiv : d ∣ r * b := by
    apply dvd_formula42_correction hd hdr
    simpa [d, n, b, mul_assoc] using
      (pairConsequences C P hP hij).dvd15_left
  have hswapA : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm Y ξ) Y) X) A⁻¹ := by
    simpa [A] using fourfold_swap_first_two hY hξ hY hX
  have hswapB : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm Y ξ) X) X) B⁻¹ := by
    simpa [B] using fourfold_swap_first_two hY hξ hX hX
  have hleftA : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm Y ξ) Y) X ^ n)
      (A ^ (-n)) := by
    have hp := hswapA.zpow n
    simpa only [inv_zpow'] using hp
  have hleftB : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm Y ξ) X) X ^ (-n))
      (B ^ n) := by
    have hp := hswapB.zpow (-n)
    simpa only [inv_zpow', neg_neg] using hp
  have hlastA0 := weightThree_comm_zpow_right_hallPetresco hξYY hX (C.d i)
  have hlastB0 := weightThree_comm_zpow_right_hallPetresco hξYX hX (C.d i)
  have hrightA0 : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) (X ^ d) ^ (-r))
      (A ^ (d * (-r)) * IA ^ (b * (-r))) := by
    have hp := (hlastA0.zpow (-r)).trans <|
      D5.gammaThree_mul_zpow
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hA4) d)
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hIA5) b)
        (-r)
    rw [← zpow_mul, ← zpow_mul] at hp
    simpa [A, IA, X, Y, d, b, orderInt] using hp
  have hrightB0 : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) X) (X ^ d) ^ r)
      (B ^ (d * r) * IB ^ (b * r)) := by
    have hp := (hlastB0.zpow r).trans <|
      D5.gammaThree_mul_zpow
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hB4) d)
        ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hIB5) b)
        r
    rw [← zpow_mul, ← zpow_mul] at hp
    simpa [B, IB, X, Y, d, b, orderInt] using hp
  have hIAbase : D5.ModGammaSix (IA ^ d) 1 := by
    simpa [IA, d, X] using weightFive_last_entry_power_vanish_general
      hA4 hX (C.x1_order_power_mem_gamma2 i)
  have hIBbase : D5.ModGammaSix (IB ^ d) 1 := by
    simpa [IB, d, X] using weightFive_last_entry_power_vanish_general
      hB4 hX (C.x1_order_power_mem_gamma2 i)
  have hIAdiv : d ∣ b * (-r) := by
    simpa [mul_comm] using dvd_neg.mpr hdiv
  have hIBdiv : d ∣ b * r := by simpa [mul_comm] using hdiv
  have hIAv := D5.modGammaSix_zpow_eq_one_of_dvd hIAbase hIAdiv
  have hIBv := D5.modGammaSix_zpow_eq_one_of_dvd hIBbase hIBdiv
  have hrightA : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) (X ^ d) ^ (-r))
      (A ^ (-n)) := by
    refine hrightA0.trans ?_
    have hmain : d * (-r) = -n := by rw [← hdr]; ring
    rw [hmain]
    simpa using (D5.ModEq.refl (D5.gamma G 6) (A ^ (-n))).mul hIAv
  have hrightB : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) X) (X ^ d) ^ r)
      (B ^ n) := by
    refine hrightB0.trans ?_
    rw [hdr]
    simpa using (D5.ModEq.refl (D5.gamma G 6) (B ^ n)).mul hIBv
  simpa [formula42Left, formula42Right, X, Y, d, n, r] using
    (hleftA.trans hrightA.symm).mul (hleftB.trans hrightB.symm)

/-! ## Formula (43) -/

def formula43Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) (C.x1 j)) ξ ^
      P.u i j *
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ) (C.x1 j) ^
      (-2 * P.u i j)

def formula43Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
    (C.x1 i ^ orderInt C.d i) ^
      (-P.u i j * orderRatio C.d i j) *
  D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
      (P.u i j * orderRatio C.d i j)

set_option maxHeartbeats 800000 in
/-- Formula (43), obtained by specializing the five-factor Jacobi identity
used in formula (34) to two equal `x₁ⱼ` entries. -/
theorem formula43
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula43Left C P ξ i j)
      (formula43Right C P ξ i j) := by
  let X := C.x1 i
  let Y := C.x1 j
  let A0 := X ^ orderInt C.d i
  let a := X ^ orderInt C.d j
  let T := D5.paperComm (D5.paperComm (D5.paperComm a Y) ξ) Y
  let L := D5.paperComm (D5.paperComm (D5.paperComm a Y) Y) ξ
  let R1 := D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) a
  let R2 := D5.paperComm (D5.paperComm (D5.paperComm ξ a) Y) Y
  let S1 := D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) A0
  let S2 := D5.paperComm (D5.paperComm (D5.paperComm ξ A0) Y) Y
  let q := orderRatio C.d i j
  let u := P.u i j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hA0 : A0 ∈ D5.gamma G 2 := by
    simpa [A0, X] using C.x1_order_power_mem_gamma2 i
  have ha : a ∈ D5.gamma G 2 := by
    simpa [a, X] using C.x1_later_order_power_mem_gamma2 (le_of_lt hij)
  have hT5 : T ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hY) hξ) hY
  have hL5 : L ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hY) hY) hξ
  have hR1 : R1 ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY) hY) ha
  have hR2 : R2 ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha) hY) hY
  have hjac : D5.ModGammaSix ((T⁻¹ * T⁻¹) * L) (R2 * R1⁻¹) := by
    simpa [T, L, R1, R2] using formula34_w_jacobi ha hY hξ hY
  have hsourceDist : D5.ModGammaSix (((T⁻¹ * T⁻¹) * L) ^ u)
      ((T ^ (-u) * T ^ (-u)) * L ^ u) := by
    have hTi : T⁻¹ ∈ D5.gamma G 3 :=
      D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hT5)
    have hL3 : L ∈ D5.gamma G 3 := D5.gamma_antitone G (by norm_num) hL5
    have houter := D5.gammaThree_mul_zpow
      ((D5.gamma G 3).mul_mem hTi hTi) hL3 u
    have hinner := D5.gammaThree_mul_zpow hTi hTi u
    have hall := houter.trans <|
      hinner.mul (D5.ModEq.refl (D5.gamma G 6) (L ^ u))
    simpa only [inv_zpow'] using hall
  have hsourceCollect : D5.ModGammaSix
      ((T ^ (-u) * T ^ (-u)) * L ^ u)
      (L ^ u * T ^ (-2 * u)) := by
    have hTp : T ^ (-u) * T ^ (-u) = T ^ (-2 * u) := by
      rw [← zpow_add]
      congr 1
      ring
    rw [hTp]
    exact D5.mul_comm_mod_gamma (n := 6) (r := 3) (s := 3)
      (by norm_num) (by norm_num) (by norm_num)
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hT5) _)
      ((D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) hL5) _)
  have hleftToJacobi : D5.ModGammaSix
      (L ^ u * T ^ (-2 * u)) (((T⁻¹ * T⁻¹) * L) ^ u) :=
    hsourceCollect.symm.trans hsourceDist.symm
  have htargetDist : D5.ModGammaSix ((R2 * R1⁻¹) ^ u)
      (R2 ^ u * R1 ^ (-u)) := by
    have hp := D5.gammaThree_mul_zpow
      (D5.gamma_antitone G (by norm_num) hR2)
      (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hR1)) u
    simpa only [inv_zpow'] using hp
  have horder : orderInt C.d j = orderInt C.d i * q := by
    simpa [q] using C.orderInt_eq_mul_ratio (le_of_lt hij)
  have haeq : a = A0 ^ q := by
    simp only [a, A0, X]
    rw [horder, zpow_mul]
  have hS2transfer : D5.ModGammaSix R2 (S2 ^ q) := by
    have hp := fourfold_second_zpow_mod_gamma_six hξ hA0 hY hY q
    simpa [R2, S2, haeq] using hp
  have hbaseY : D5.paperComm (D5.paperComm ξ Y) Y ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY) hY
  have hS1transfer : D5.ModGammaSix R1 (S1 ^ q) := by
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ Y) Y) a) (S1 ^ q)
    rw [haeq]
    simpa [S1] using D5.paperComm_zpow_right_mod_gamma
      (n := 6) (r := 3) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hbaseY hA0 q
  have hR2pow := hS2transfer.zpow u
  have hR1pow := hS1transfer.zpow (-u)
  rw [← zpow_mul] at hR2pow hR1pow
  have hR2pow' : D5.ModGammaSix (R2 ^ u) (S2 ^ (u * q)) := by
    convert hR2pow using 1 <;> ring
  have hR1pow' : D5.ModGammaSix (R1 ^ (-u)) (S1 ^ (-u * q)) := by
    convert hR1pow using 1 <;> ring
  have htargetTransfer : D5.ModGammaSix
      (R2 ^ u * R1 ^ (-u))
      (S2 ^ (u * q) * S1 ^ (-u * q)) := by
    exact hR2pow'.mul hR1pow'
  have hcalc := hleftToJacobi.trans ((hjac.zpow u).trans
    (htargetDist.trans htargetTransfer))
  have hcomm : D5.ModGammaSix
      (S2 ^ (u * q) * S1 ^ (-u * q))
      (S1 ^ (-u * q) * S2 ^ (u * q)) :=
    D5.mul_comm_mod_gamma (n := 6) (r := 3) (s := 3)
      (by norm_num) (by norm_num) (by norm_num)
      ((D5.gamma G 3).zpow_mem (by
        exact D5.gamma_antitone G (by norm_num) <|
          D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
            (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
              (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
                hξ hA0) hY) hY) _)
      ((D5.gamma G 3).zpow_mem (by
        exact D5.gamma_antitone G (by norm_num) <|
          D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
            hbaseY hA0) _)
  simpa [formula43Left, formula43Right, X, Y, A0, a, T, L, R1, R2,
    S1, S2, q, u, mul_assoc] using hcalc.trans hcomm

/-! ## Formula (44) -/

def formula44Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 j) ξ) ξ) (C.x1 i ^ orderInt C.d j) ^ P.u i j *
  D5.paperComm (D5.paperComm
    (D5.paperComm (C.x1 j) ξ) (C.x1 i ^ orderInt C.d j)) ξ ^ (-P.u i j)

def formula44Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
    (D5.paperComm (C.x1 j) ξ) ^
      (P.u i j * orderRatio C.d i j)

set_option maxHeartbeats 500000 in
/-- Formula (44), from the weight pattern `(2,1,2)` of the multiplicative
Jacobi identity. -/
theorem formula44
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula44Left C P ξ i j)
      (formula44Right C P ξ i j) := by
  let X := C.x1 i
  let Y := C.x1 j
  let A0 := X ^ orderInt C.d i
  let a := X ^ orderInt C.d j
  let A := D5.paperComm Y ξ
  let U := D5.paperComm (D5.paperComm A ξ) a
  let E := D5.paperComm (D5.paperComm A a) ξ
  let V := D5.paperComm (D5.paperComm a A) ξ
  let R := D5.paperComm (D5.paperComm a ξ) A
  let Q := D5.paperComm A0 ξ
  let S := D5.paperComm Q A
  let q := orderRatio C.d i j
  let u := P.u i j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hA0 : A0 ∈ D5.gamma G 2 := by
    simpa [A0, X] using C.x1_order_power_mem_gamma2 i
  have ha : a ∈ D5.gamma G 2 := by
    simpa [a, X] using C.x1_later_order_power_mem_gamma2 (le_of_lt hij)
  have hA : A ∈ D5.gamma G 2 := by
    simpa [A] using D5.paperComm_mem_gamma_add (r := 1) (s := 1)
      (by norm_num) (by norm_num) hY hξ
  have hAa : D5.paperComm a A ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hA
  have hU5 : U ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hξ) ha
  have hE5 : E ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA ha) hξ
  have hV5 : V ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hAa hξ
  have hR5 : R ∈ D5.gamma G 5 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hξ) hA
  have hrot : D5.ModGammaSix U (V⁻¹ * R) := by
    simpa [U, V, R] using rotation_main_mod_gamma_six_212 hA hξ ha
  have hEV : D5.ModGammaSix E V⁻¹ := by
    have hi : D5.ModGammaSix
        (D5.paperComm (D5.paperComm a A)⁻¹ ξ)
        (D5.paperComm (D5.paperComm a A) ξ)⁻¹ :=
      D5.paperComm_inv_left_mod_gamma
        (n := 6) (r := 4) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) hAa hξ
    change D5.ModGammaSix
      (D5.paperComm (D5.paperComm A a) ξ)
      (D5.paperComm (D5.paperComm a A) ξ)⁻¹
    rw [D5.paperComm_swap a A]
    exact hi
  have hbase : D5.ModGammaSix (U * E⁻¹) R := by
    have hcomm : D5.ModGammaSix (R * V) (V * R) :=
      D5.mul_comm_mod_gamma (n := 6) (r := 5) (s := 5)
        (by norm_num) (by norm_num) (by norm_num) hR5 hV5
    have hcancel : D5.ModGammaSix ((V⁻¹ * R) * V) R := by
      have hp := (D5.ModEq.refl (D5.gamma G 6) V⁻¹).mul hcomm
      simpa [mul_assoc] using hp
    have hall := hrot.mul hEV.inv
    have hall' : D5.ModGammaSix (U * E⁻¹) ((V⁻¹ * R) * V) := by
      simpa using hall
    exact hall'.trans hcancel
  have hsplit := D5.gammaThree_mul_zpow
    (D5.gamma_antitone G (by norm_num) hU5)
    (D5.gamma_antitone G (by norm_num) ((D5.gamma G 5).inv_mem hE5)) u
  have hleftBase : D5.ModGammaSix (U ^ u * E ^ (-u)) (R ^ u) := by
    have hs : D5.ModGammaSix ((U * E⁻¹) ^ u) (U ^ u * E ^ (-u)) := by
      simpa only [inv_zpow'] using hsplit
    exact hs.symm.trans (hbase.zpow u)
  have horder : orderInt C.d j = orderInt C.d i * q := by
    simpa [q] using C.orderInt_eq_mul_ratio (le_of_lt hij)
  have haeq : a = A0 ^ q := by
    simp only [a, A0, X]
    rw [horder, zpow_mul]
  have hQ : Q ∈ D5.gamma G 3 := by
    simpa [Q] using D5.paperComm_mem_gamma_add (r := 2) (s := 1)
      (by norm_num) (by norm_num) hA0 hξ
  have hinner : D5.ModEq (D5.gamma G 4)
      (D5.paperComm a ξ) (Q ^ q) := by
    rw [haeq]
    simpa [Q] using D5.paperComm_zpow_left_mod_gamma
      (n := 4) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hA0 hξ q
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 2) (by norm_num) (by norm_num) hinner hA
  have hpow : D5.ModGammaSix
      (D5.paperComm (Q ^ q) A) (S ^ q) := by
    simpa [S] using D5.paperComm_zpow_left_mod_gamma
      (n := 6) (r := 3) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hQ hA q
  have htransfer : D5.ModGammaSix R (S ^ q) := by
    simpa [R] using hlift.trans hpow
  have htransferU := htransfer.zpow u
  rw [← zpow_mul] at htransferU
  have hfinal : D5.ModGammaSix (R ^ u) (S ^ (u * q)) := by
    convert htransferU using 1 <;> ring
  simpa [formula44Left, formula44Right, X, Y, A0, a, A, U, E, R, Q, S,
    q, u] using hleftBase.trans hfinal

/-! ## Assembly of formula (45) -/

def formula45Source
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  ((((formula40First C P ξ i j * formula40Second C P ξ i j)⁻¹ *
      (formula41First C P ξ i j * formula41Second C P ξ i j)⁻¹) *
    formula42Left C P ξ i j) * formula43Left C P ξ i j) *
    formula44Left C P ξ i j

def formula45Uncollected
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  ((((formula40Right C P ξ i j)⁻¹ *
      (formula41Right C P ξ i j)⁻¹) *
    formula42Right C P ξ i j) * formula43Right C P ξ i j) *
    formula44Right C P ξ i j

def formula45Pair
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  let q := orderRatio C.d i j
  let r := formula40Exponent C P i j
  let s := formula41Exponent C P i j
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
    (C.x1 i ^ orderInt C.d i)
  let B := D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
    (C.x1 i ^ orderInt C.d i)
  let D := D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j)
  let E := D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
    (D5.paperComm (C.x1 j) ξ)
  (((A ^ (-P.u i j * q - 2 * r) * B ^ (r - s)) *
      D ^ (P.u i j * q)) * E ^ (P.u i j * q))

/-- Formulas (40)--(44) transform the remaining contribution of one pair
into the seven uncollected factors preceding (45). -/
theorem formula45_source_to_uncollected
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula45Source C P ξ i j)
      (formula45Uncollected C P ξ i j) := by
  have h40 := (formula40 C P hP ξ hij).inv
  have h41 := (formula41 C P hP ξ hij).inv
  have h42 := formula42 C P hP ξ hij
  have h43 := formula43 C P ξ hij
  have h44 := formula44 C P ξ hij
  simpa [formula45Source, formula45Uncollected] using
    (((h40.mul h41).mul h42).mul h43).mul h44

set_option maxHeartbeats 600000 in
/-- Collection of the seven transformed factors into the four displayed
factors of formula (45). -/
theorem formula45_collect
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) :
    D5.ModGammaSix (formula45Uncollected C P ξ i j)
      (formula45Pair C P ξ i j) := by
  let q := orderRatio C.d i j
  let r := formula40Exponent C P i j
  let s := formula41Exponent C P i j
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
    (C.x1 i ^ orderInt C.d i)
  let B := D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
    (C.x1 i ^ orderInt C.d i)
  let D := D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j)
  let E := D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
    (D5.paperComm (C.x1 j) ξ)
  let u := P.u i j
  let a := A ^ (-r)
  let b := B ^ (-s)
  let c := A ^ (-r)
  let d := B ^ r
  let e := A ^ (-u * q)
  let f := D ^ (u * q)
  let g := E ^ (u * q)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi2 : C.x1 i ^ orderInt C.d i ∈ D5.gamma G 2 :=
    C.x1_order_power_mem_gamma2 i
  have hA : A ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hj) hj) hi2
  have hB : B ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hj) hi) hi2
  have hD : D ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hi2) hj) hj
  have hE : E ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hi2 hξ)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ)
  have ha : a ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hA _
  have hb : b ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hB _
  have hc : c ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hA _
  have hd : d ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hB _
  have he : e ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hA _
  have hf : f ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hD _
  have hg : g ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hE _
  have hp : [a, b, c, d, e, f, g].Perm [a, c, e, b, d, f, g] := by
    have hleft : ([b] ++ [c, d, e]).Perm ([c, d, e] ++ [b]) :=
      List.perm_append_comm
    have h1 : [a, b, c, d, e, f, g].Perm [a, c, d, e, b, f, g] := by
      apply List.Perm.cons a
      simpa only [List.append_assoc] using hleft.append_right [f, g]
    have hright : ([d] ++ [e]).Perm ([e] ++ [d]) := List.perm_append_comm
    have h2 : [a, c, d, e, b, f, g].Perm [a, c, e, d, b, f, g] := by
      apply List.Perm.cons a
      apply List.Perm.cons c
      simpa only [List.append_assoc] using hright.append_right [b, f, g]
    have h3 : [a, c, e, d, b, f, g].Perm [a, c, e, b, d, f, g] := by
      apply List.Perm.cons a
      apply List.Perm.cons c
      apply List.Perm.cons e
      exact (List.Perm.swap d b [f, g]).symm
    exact h1.trans (h2.trans h3)
  have hperm := D5.listProd_perm_gammaThree hp (fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | hx
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · exact hf
    · rcases hx with rfl | hx
      · exact hg
      · simp at hx)
  have hcollectA : a * c * e = A ^ (-u * q - 2 * r) := by
    simp only [a, c, e, ← zpow_add]
    congr 1
    ring
  have hcollectB : b * d = B ^ (r - s) := by
    simp only [b, d, ← zpow_add]
    congr 1
    ring
  have htarget : [a, c, e, b, d, f, g].prod =
      formula45Pair C P ξ i j := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [show a * (c * (e * (b * (d * (f * g))))) =
      (((a * c * e) * (b * d)) * f) * g by group]
    rw [hcollectA, hcollectB]
    rfl
  have hsource : formula45Uncollected C P ξ i j =
      [a, b, c, d, e, f, g].prod := by
    simp [formula45Uncollected, formula40Right, formula41Right,
      formula42Right, formula43Right, formula44Right,
      A, B, D, E, q, r, s, u, a, b, c, d, e, f, g,
      List.prod_cons, List.prod_nil, mul_assoc]
  rw [hsource]
  exact hperm.trans <| by rw [htarget]

/-- Formula (45) for one pair `i < j`. -/
theorem formula45
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula45Source C P ξ i j)
      (formula45Pair C P ξ i j) :=
  (formula45_source_to_uncollected C P hP ξ hij).trans
    (formula45_collect C P ξ i j)

/-! ## Reduction from (45) to the three products in (46) -/

/-- The first integer identity following formula (45), written with the
already integral exponent `formula40Exponent`. -/
theorem formula45_first_exponent_identity
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    {i j : Fin C.s} (hij : i < j) :
    -P.u i j * orderRatio C.d i j - 2 * formula40Exponent C P i j =
      orderInt C.d j * (-P.u i j * orderRatio C.d i j) := by
  let d := orderInt C.d i
  let e := orderInt C.d j
  let q := orderRatio C.d i j
  let u := P.u i j
  let r := formula40Exponent C P i j
  let B2e := TaharaArithmetic.binom2 (C.d j)
  have hd : d ≠ 0 := by
    simp [d, orderInt, Nat.ne_of_gt (lt_trans Nat.zero_lt_one (C.d_gt_one i))]
  have hdr : d * r = u * B2e := by
    simpa [d, r, u, B2e] using formula40_exponent_identity C P hP hij
  have he : e = d * q := by
    simpa [d, e, q] using C.orderInt_eq_mul_ratio (le_of_lt hij)
  have hB2e : 2 * B2e = e * (e - 1) := by
    have h := TaharaArithmetic.two_mul_binom2 (C.d j)
    rw [Nat.cast_sub (Nat.le_of_lt (C.d_gt_one j))] at h
    simpa [B2e, e, orderInt] using h
  apply mul_left_cancel₀ hd
  calc
    d * (-u * q - 2 * r) = -d * u * q - 2 * (d * r) := by ring
    _ = -u * e - 2 * (u * B2e) := by rw [hdr, he]; ring
    _ = -u * e - u * (e * (e - 1)) := by rw [← hB2e]; ring
    _ = d * (e * (-u * q)) := by rw [he]; ring

/-- The second integer identity following formula (45). -/
theorem formula45_second_exponent_identity
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    {i j : Fin C.s} (hij : i < j) :
    formula40Exponent C P i j - formula41Exponent C P i j +
        P.u i j * orderRatio C.d i j =
      P.u i j * orderInt C.d i *
        TaharaArithmetic.binom2 (C.d j / C.d i + 1) := by
  let d := orderInt C.d i
  let e := orderInt C.d j
  let qn := C.d j / C.d i
  let q : ℤ := orderRatio C.d i j
  let u := P.u i j
  let r := formula40Exponent C P i j
  let s := formula41Exponent C P i j
  let B2d := TaharaArithmetic.binom2 (C.d i)
  let B2e := TaharaArithmetic.binom2 (C.d j)
  let B2q1 := TaharaArithmetic.binom2 (qn + 1)
  have hd : d ≠ 0 := by
    simp [d, orderInt, Nat.ne_of_gt (lt_trans Nat.zero_lt_one (C.d_gt_one i))]
  have hdr : d * r = u * B2e := by
    simpa [d, r, u, B2e] using formula40_exponent_identity C P hP hij
  have hds : d * s = -(u * q * B2d) := by
    simpa [d, s, u, q, B2d] using formula41_exponent_identity C P hP hij
  have he : e = d * q := by
    simpa [d, e, q] using C.orderInt_eq_mul_ratio (le_of_lt hij)
  have hB2d : 2 * B2d = d * (d - 1) := by
    have h := TaharaArithmetic.two_mul_binom2 (C.d i)
    rw [Nat.cast_sub (Nat.le_of_lt (C.d_gt_one i))] at h
    simpa [B2d, d, orderInt] using h
  have hB2e : 2 * B2e = e * (e - 1) := by
    have h := TaharaArithmetic.two_mul_binom2 (C.d j)
    rw [Nat.cast_sub (Nat.le_of_lt (C.d_gt_one j))] at h
    simpa [B2e, e, orderInt] using h
  have hB2q1 : 2 * B2q1 = q * (q + 1) := by
    have h := TaharaArithmetic.two_mul_binom2 (qn + 1)
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at h
    simpa [B2q1, q, qn, orderRatio, mul_comm] using h
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2 : ℤ) ≠ 0) hd)
  calc
    (2 * d) * (r - s + u * q) =
        2 * (d * r) - 2 * (d * s) + 2 * d * u * q := by ring
    _ = 2 * (u * B2e) - 2 * (-(u * q * B2d)) + 2 * d * u * q := by
      rw [hdr, hds]
    _ = u * (2 * B2e) + u * q * (2 * B2d) + 2 * d * u * q := by ring
    _ = u * (e * (e - 1)) + u * q * (d * (d - 1)) + 2 * d * u * q := by
      rw [hB2e, hB2d]
    _ = u * d * d * (q * (q + 1)) := by rw [he]; ring
    _ = u * d * d * (2 * B2q1) := by rw [hB2q1]
    _ = (2 * d) * (u * d * B2q1) := by ring

/-- The first commutator in (45) is killed by the order of `x₁ⱼ`. -/
theorem formula45_first_base_power_vanish
    (C : Context G) (ξ : G) (i j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
        (C.x1 i ^ orderInt C.d i) ^ orderInt C.d j) 1 := by
  let X := C.x1 i
  let Y := C.x1 j
  let A0 := X ^ orderInt C.d i
  let K := D5.paperComm ξ Y
  let R := D5.paperComm K Y
  let e := orderInt C.d j
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hA0 : A0 ∈ D5.gamma G 2 := by
    simpa [A0, X] using C.x1_order_power_mem_gamma2 i
  have hYe : Y ^ e ∈ D5.gamma G 2 := by
    simpa [Y, e] using C.x1_order_power_mem_gamma2 j
  have hK : K ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY
  have hR : R ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hK hY
  have houter := D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 3) (s := 2)
    (by norm_num) (by norm_num) (by norm_num) hR hA0 e
  have hinner := D5.paperComm_zpow_right_mod_gamma
    (n := 4) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK hY e
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 2) (by norm_num) (by norm_num) hinner.symm hA0
  have hfinal : D5.ModGammaSix
      (D5.paperComm (D5.paperComm K (Y ^ e)) A0) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hK hYe) hA0
  simpa [K, R, A0, X, Y, e] using houter.symm.trans (hlift.trans hfinal)

/-- The second commutator in (45) is killed by the order of `x₁ᵢ`. -/
theorem formula45_second_base_power_vanish
    (C : Context G) (ξ : G) (i j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
        (C.x1 i ^ orderInt C.d i) ^ orderInt C.d i) 1 := by
  let X := C.x1 i
  let Y := C.x1 j
  let A0 := X ^ orderInt C.d i
  let K := D5.paperComm ξ Y
  let R := D5.paperComm K X
  let d := orderInt C.d i
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hX : X ∈ D5.gamma G 1 := by simp [X, D5.gamma]
  have hY : Y ∈ D5.gamma G 1 := by simp [Y, D5.gamma]
  have hA0 : A0 ∈ D5.gamma G 2 := by
    simpa [A0, X] using C.x1_order_power_mem_gamma2 i
  have hK : K ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hY
  have hR : R ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hK hX
  have houter := D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 3) (s := 2)
    (by norm_num) (by norm_num) (by norm_num) hR hA0 d
  have hinner := D5.paperComm_zpow_right_mod_gamma
    (n := 4) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hK hX d
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 2) (by norm_num) (by norm_num) hinner.symm hA0
  have hfinal : D5.ModGammaSix
      (D5.paperComm (D5.paperComm K A0) A0) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hK hA0) hA0
  simpa [K, R, A0, X, Y, d] using houter.symm.trans (hlift.trans hfinal)

def formula46Pair
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  let q := orderRatio C.d i j
  let B := D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
    (C.x1 i ^ orderInt C.d i)
  let D := D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j)
  let E := D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
    (D5.paperComm (C.x1 j) ξ)
  (D ^ (P.u i j * q) * B ^ (-P.u i j * q)) * E ^ (P.u i j * q)

set_option maxHeartbeats 600000 in
/-- The local reduction from (45) to the three factors retained in (46). -/
theorem formula45_to_formula46_pair
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula45Pair C P ξ i j)
      (formula46Pair C P ξ i j) := by
  let q := orderRatio C.d i j
  let r := formula40Exponent C P i j
  let s := formula41Exponent C P i j
  let A := D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
    (C.x1 i ^ orderInt C.d i)
  let B := D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
    (C.x1 i ^ orderInt C.d i)
  let D := D5.paperComm (D5.paperComm
    (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j)
  let E := D5.paperComm
    (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
    (D5.paperComm (C.x1 j) ξ)
  let u := P.u i j
  let ea := -u * q - 2 * r
  let eb := r - s
  have hAord := formula45_first_base_power_vanish C ξ i j
  have hBord := formula45_second_base_power_vanish C ξ i j
  have hea : ea = orderInt C.d j * (-u * q) := by
    simpa [ea, q, r, u] using formula45_first_exponent_identity C P hP hij
  have hAv : D5.ModGammaSix (A ^ ea) 1 := by
    rw [hea, zpow_mul]
    simpa [A] using hAord.zpow (-u * q)
  have heb : eb + u * q =
      u * orderInt C.d i * TaharaArithmetic.binom2 (C.d j / C.d i + 1) := by
    simpa [eb, q, r, s, u] using formula45_second_exponent_identity C P hP hij
  have hdiv : orderInt C.d i ∣ eb + u * q := by
    refine ⟨u * TaharaArithmetic.binom2 (C.d j / C.d i + 1), ?_⟩
    rw [heb]
    ring
  have hBextra := D5.modGammaSix_zpow_eq_one_of_dvd hBord hdiv
  have hBreplace : D5.ModGammaSix (B ^ eb) (B ^ (-u * q)) := by
    have hp := hBextra.mul
      (D5.ModEq.refl (D5.gamma G 6) (B ^ (-u * q)))
    have heq : B ^ (eb + u * q) * B ^ (-u * q) = B ^ eb := by
      rw [← zpow_add]
      congr 1
      ring
    rw [heq] at hp
    simpa using hp
  have hfirst : D5.ModGammaSix
      (((A ^ ea * B ^ eb) * D ^ (u * q)) * E ^ (u * q))
      ((B ^ (-u * q) * D ^ (u * q)) * E ^ (u * q)) := by
    simpa using (((hAv.mul hBreplace).mul
      (D5.ModEq.refl (D5.gamma G 6) (D ^ (u * q)))).mul
        (D5.ModEq.refl (D5.gamma G 6) (E ^ (u * q))))
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi2 := C.x1_order_power_mem_gamma2 i
  have hB : B ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hj) hi) hi2
  have hD : D ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hi2) hj) hj
  have hswap : D5.ModGammaSix
      (B ^ (-u * q) * D ^ (u * q))
      (D ^ (u * q) * B ^ (-u * q)) :=
    D5.mul_comm_mod_gamma (n := 6) (r := 3) (s := 3)
      (by norm_num) (by norm_num) (by norm_num)
      ((D5.gamma G 3).zpow_mem hB _) ((D5.gamma G 3).zpow_mem hD _)
  have hsecond := hswap.mul
    (D5.ModEq.refl (D5.gamma G 6) (E ^ (u * q)))
  simpa [formula45Pair, formula46Pair, A, B, D, E, q, r, s, u, ea, eb]
    using hfirst.trans hsecond

/-- Formula (46) for one pair, with the whole Section 13 source contribution
on the left. -/
theorem formula46_pair
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula45Source C P ξ i j)
      (formula46Pair C P ξ i j) :=
  (formula45 C P hP ξ hij).trans
    (formula45_to_formula46_pair C P hP ξ hij)

/-! ## Splitting the principal products of formula (34) -/

/-- Split the weak triangle `i ≤ j ≤ k` into its diagonal, the two
repeated-index faces, and the strict triangle.  This is only finite-product
bookkeeping in the abelian quotient `γ₃/γ₆`. -/
theorem weakTripleProduct_split_patterns
    {n : ℕ} (f : Fin n → Fin n → Fin n → G)
    (hf : ∀ i j k, f i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k)
      ((orderedProduct (fun i => f i i i) *
          strictPairProduct (fun i k => f i i k)) *
        (strictPairProduct (fun i j => f i j j) * strictTripleProduct f)) := by
  let B : Fin n → Fin n → G := fun i j =>
    orderedProductWhere (j ≤ ·) fun k => f i j k
  let D : Fin n → G := fun i => f i i i
  let A : Fin n → G := fun i =>
    orderedProductWhere (i < ·) fun k => f i i k
  let E : Fin n → Fin n → G := fun i j => f i j j
  let S : Fin n → Fin n → G := fun i j =>
    orderedProductWhere (j < ·) fun k => f i j k
  let ER : Fin n → G := fun i => orderedProductWhere (i < ·) (E i)
  let SR : Fin n → G := fun i => orderedProductWhere (i < ·) (S i)
  have hB : ∀ i j, B i j ∈ D5.gamma G 3 := by
    intro i j
    apply orderedProductWhere_mem
    intro k hjk
    exact hf i j k
  have hD : ∀ i, D i ∈ D5.gamma G 3 := fun i => hf i i i
  have hA : ∀ i, A i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro k hik
    exact hf i i k
  have hE : ∀ i j, i < j → E i j ∈ D5.gamma G 3 := by
    intro i j hij
    exact hf i j j
  have hS : ∀ i j, i < j → S i j ∈ D5.gamma G 3 := by
    intro i j hij
    apply orderedProductWhere_mem
    intro k hjk
    exact hf i j k
  have hER : ∀ i, ER i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hE i j hij
  have hSR : ∀ i, SR i ∈ D5.gamma G 3 := by
    intro i
    apply orderedProductWhere_mem
    intro j hij
    exact hS i j hij
  have hrow : ∀ i, D5.ModGammaSix
      (orderedProductWhere (i ≤ ·) (B i))
      ((D i * A i) * (ER i * SR i)) := by
    intro i
    have hj := orderedProductWhere_le_split_lt i (B i)
      (fun j hij => hB i j)
    have hd := orderedProductWhere_le_split_lt i (f i i)
      (fun k hik => hf i i k)
    have hoff0 : D5.ModGammaSix
        (orderedProductWhere (i < ·) (B i))
        (orderedProductWhere (i < ·) fun j => E i j * S i j) := by
      apply modEq_orderedProductWhere
      intro j hij
      simpa [B, E, S] using
        orderedProductWhere_le_split_lt j (f i j) (fun k hjk => hf i j k)
    have hoff1 := D5.orderedProductWhere_pointwise_mul_gammaThree
      (i < ·) (E i) (S i) (hE i) (hS i)
    have hreplace := hd.mul (hoff0.trans hoff1)
    simpa [B, D, A, ER, SR] using hj.trans hreplace
  have hrows : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) (B i))
      (orderedProduct fun i => (D i * A i) * (ER i * SR i)) := by
    apply modEq_orderedProduct
    exact hrow
  have hcollect := D5.orderedProduct_four_gammaThree D A ER SR
    hD hA hER hSR
  simpa [B, D, A, E, S, ER, SR, strictPairProduct,
    strictTripleProduct] using hrows.trans hcollect

/-- Split `i < j ≤ k` into the repeated-index face `i < j = k` and
the strict triangle. -/
theorem strictWeakTripleProduct_split_last
    {n : ℕ} (f : Fin n → Fin n → Fin n → G)
    (hf : ∀ i j k, f i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k)
      (strictPairProduct (fun i j => f i j j) * strictTripleProduct f) := by
  let E : Fin n → Fin n → G := fun i j => f i j j
  let S : Fin n → Fin n → G := fun i j =>
    orderedProductWhere (j < ·) fun k => f i j k
  have hE : ∀ i j, i < j → E i j ∈ D5.gamma G 3 := by
    intro i j hij
    exact hf i j j
  have hS : ∀ i j, i < j → S i j ∈ D5.gamma G 3 := by
    intro i j hij
    apply orderedProductWhere_mem
    intro k hjk
    exact hf i j k
  have hlocal : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k => f i j k)
      (strictPairProduct fun i j => E i j * S i j) := by
    unfold strictPairProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    simpa [E, S] using
      orderedProductWhere_le_split_lt j (f i j) (fun k hjk => hf i j k)
  have hsplit := strictPairProduct_pointwise_gammaThree E S hE hS
  simpa [E, S, strictTripleProduct] using hlocal.trans hsplit.symm

def formula34WMainDiagonalProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula34WMainFactor C P ξ i i i

def formula34WMainIIJProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j => formula34WMainFactor C P ξ i i j

def formula34WMainIJJProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j => formula34WMainFactor C P ξ i j j

def formula34WPrimeIJJProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j => formula34WPrimeMainFactor C P ξ i j j

theorem formula34_wmain_split_patterns
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula34WMainProduct C P ξ)
      ((formula34WMainDiagonalProduct C P ξ *
          formula34WMainIIJProduct C P ξ) *
        (formula34WMainIJJProduct C P ξ *
          formula34WMainStrictProduct C P ξ)) := by
  simpa [formula34WMainProduct, formula34WMainDiagonalProduct,
    formula34WMainIIJProduct, formula34WMainIJJProduct,
    formula34WMainStrictProduct] using
      weakTripleProduct_split_patterns (formula34WMainFactor C P ξ)
        (formula34WMainFactor_mem_gamma3 C P ξ)

theorem formula34_wprime_split_patterns
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula34WPrimeMainProduct C P ξ)
      (formula34WPrimeIJJProduct C P ξ *
        formula34WPrimeMainStrictProduct C P ξ) := by
  simpa [formula34WPrimeMainProduct, formula34WPrimeIJJProduct,
    formula34WPrimeMainStrictProduct] using
      strictWeakTripleProduct_split_last (formula34WPrimeMainFactor C P ξ)
        (formula34WPrimeMainFactor_mem_gamma3 C P ξ)

theorem formula34_wmain_diagonal_vanish
    (C : Context G) (P : Parameters C.s C.t) (h2 : P.Condition2) (ξ : G) :
    formula34WMainDiagonalProduct C P ξ = 1 := by
  unfold formula34WMainDiagonalProduct orderedProduct
  simp [formula34WMainFactor_diagonal_eq_one C P h2 ξ]

def formula40FaceProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    formula34WMainFactor C P ξ i j j *
      formula34WPrimeMainFactor C P ξ i j j

def formula41FaceProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    formula34WMainFactor C P ξ i i j *
      formula34WDoublePrimeMainFactor C P ξ i i j

/-- After Section 12 removes the diagonal and strict-triple parts, the
three principal products in (34) consist exactly of their two
repeated-index faces. -/
theorem formula34_principal_to_pair_faces
    (C : Context G) (P : Parameters C.s C.t)
    (h2 : P.Condition2) (h5 : P.Condition5) (h10 : P.Condition10) (ξ : G) :
    D5.ModGammaSix
      ((formula34WMainProduct C P ξ * formula34WPrimeMainProduct C P ξ) *
        formula34WDoublePrimeFullMainProduct C P ξ)
      (formula40FaceProduct C P ξ * formula41FaceProduct C P ξ) := by
  let A := formula34WMainIIJProduct C P ξ
  let B := formula34WMainIJJProduct C P ξ
  let S := formula34WMainStrictProduct C P ξ
  let C' := formula34WPrimeIJJProduct C P ξ
  let T := formula34WPrimeMainStrictProduct C P ξ
  let D := formula34WDoublePrimeDiagonalMainProduct C P ξ
  let U := formula34WDoublePrimeMainStrictProduct C P ξ
  have hA : A ∈ D5.gamma G 3 := by
    dsimp [A, formula34WMainIIJProduct, strictPairProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    exact formula34WMainFactor_mem_gamma3 C P ξ i i j
  have hB : B ∈ D5.gamma G 3 := by
    dsimp [B, formula34WMainIJJProduct, strictPairProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    exact formula34WMainFactor_mem_gamma3 C P ξ i j j
  have hS : S ∈ D5.gamma G 3 := by
    dsimp [S, formula34WMainStrictProduct, strictTripleProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WMainFactor_mem_gamma3 C P ξ i j k
  have hC : C' ∈ D5.gamma G 3 := by
    dsimp [C', formula34WPrimeIJJProduct, strictPairProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    exact formula34WPrimeMainFactor_mem_gamma3 C P ξ i j j
  have hT : T ∈ D5.gamma G 3 := by
    dsimp [T, formula34WPrimeMainStrictProduct, strictTripleProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WPrimeMainFactor_mem_gamma3 C P ξ i j k
  have hD : D ∈ D5.gamma G 3 := by
    dsimp [D, formula34WDoublePrimeDiagonalMainProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    exact formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i i j
  have hU : U ∈ D5.gamma G 3 := by
    dsimp [U, formula34WDoublePrimeMainStrictProduct, strictTripleProduct]
    apply orderedProduct_mem; intro i
    apply orderedProductWhere_mem; intro j hij
    apply orderedProductWhere_mem; intro k hjk
    exact formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i j k
  have hsplit := ((formula34_wmain_split_patterns C P ξ).mul
    (formula34_wprime_split_patterns C P ξ)).mul
      (formula34_wdoubleprime_join_diagonal_strict C P ξ).symm
  have hdiag := formula34_wmain_diagonal_vanish C P h2 ξ
  have hsplit' : D5.ModGammaSix
      ((formula34WMainProduct C P ξ * formula34WPrimeMainProduct C P ξ) *
        formula34WDoublePrimeFullMainProduct C P ξ)
      (((A * (B * S)) * (C' * T)) * (D * U)) := by
    simpa [A, B, S, C', T, D, U, hdiag] using hsplit
  have hp : [A, B, S, C', T, D, U].Perm [B, C', A, D, S, T, U] := by
    have h1 : [A, B, S, C', T, D, U].Perm [B, A, S, C', T, D, U] :=
      (List.Perm.swap A B [S, C', T, D, U]).symm
    have hmoveC : ([A, S] ++ [C']).Perm ([C'] ++ [A, S]) :=
      List.perm_append_comm
    have h2 : [B, A, S, C', T, D, U].Perm [B, C', A, S, T, D, U] := by
      apply List.Perm.cons B
      simpa only [List.append_assoc] using hmoveC.append_right [T, D, U]
    have hmoveD : ([S, T] ++ [D]).Perm ([D] ++ [S, T]) :=
      List.perm_append_comm
    have h3 : [B, C', A, S, T, D, U].Perm [B, C', A, D, S, T, U] := by
      apply List.Perm.cons B
      apply List.Perm.cons C'
      apply List.Perm.cons A
      simpa only [List.append_assoc] using hmoveD.append_right [U]
    exact h1.trans (h2.trans h3)
  have hperm : D5.ModGammaSix
      (((A * (B * S)) * (C' * T)) * (D * U))
      (((B * C') * (A * D)) * ((S * T) * U)) := by
    simpa [mul_assoc] using D5.listProd_perm_gammaThree hp (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | hx
      · exact hA
      · exact hB
      · exact hS
      · exact hC
      · exact hT
      · exact hD
      · rcases hx with rfl | hx
        · exact hU
        · simp at hx)
  have h40 := strictPairProduct_pointwise_gammaThree
    (fun i j => formula34WMainFactor C P ξ i j j)
    (fun i j => formula34WPrimeMainFactor C P ξ i j j)
    (fun i j hij => formula34WMainFactor_mem_gamma3 C P ξ i j j)
    (fun i j hij => formula34WPrimeMainFactor_mem_gamma3 C P ξ i j j)
  have h41 := strictPairProduct_pointwise_gammaThree
    (fun i j => formula34WMainFactor C P ξ i i j)
    (fun i j => formula34WDoublePrimeMainFactor C P ξ i i j)
    (fun i j hij => formula34WMainFactor_mem_gamma3 C P ξ i i j)
    (fun i j hij => formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i i j)
  have hstrict := formula39_strict_principal_streams_vanish C P h5 h10 ξ
  have hfinish : D5.ModGammaSix
      (((B * C') * (A * D)) * ((S * T) * U))
      (formula40FaceProduct C P ξ * formula41FaceProduct C P ξ) := by
    exact ((h40.mul h41).mul hstrict).trans (by
      simp only [mul_one]
      exact D5.ModEq.refl (D5.gamma G 6) _)
  exact hsplit'.trans (hperm.trans hfinish)

/-! ## Identifying the pair source left by formulas (29) and (34) -/

theorem formula28_u_is_formula29_line_two
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula28URotatedPairStream C P ξ)
      (formula29LineTwo C P ξ) := by
  change D5.ModGammaSix
    (orderedProduct fun j => orderedProductWhere (· < j) fun i =>
      formula29PairLineTwo C P ξ i j)
    (strictPairProduct (formula29PairLineTwo C P ξ))
  exact (strictPairProduct_swap (formula29PairLineTwo C P ξ)
    (fun i j hij => (formula29_pair_lines_mem_gamma3 C P ξ hij).2.1)).symm

def formula45RawSource
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  (formula29PairCorrections C P ξ i j *
      formula29PairLineTwo C P ξ i j) *
    ((formula34WMainFactor C P ξ i j j *
        formula34WPrimeMainFactor C P ξ i j j) *
      (formula34WMainFactor C P ξ i i j *
        formula34WDoublePrimeMainFactor C P ξ i i j))

private def formula45PermutedRawSource
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) : G :=
  let l1 := formula29PairLineOne C P ξ i j
  let l2 := formula29PairLineTwo C P ξ i j
  let l3 := formula29PairLineThree C P ξ i j
  let l4 := formula29PairLineFour C P ξ i j
  let l5 := formula29PairLineFive C P ξ i j
  let l6 := formula29PairLineSix C P ξ i j
  let w1 := formula34WMainFactor C P ξ i j j
  let w2 := formula34WPrimeMainFactor C P ξ i j j
  let w3 := formula34WMainFactor C P ξ i i j
  let w4 := formula34WDoublePrimeMainFactor C P ξ i i j
  ((((w2 * w1) * (w4 * w3)) * (l5 * l6)) * (l1 * (l2 * l2))) * (l3 * l4)

private theorem formula45_raw_permute
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula45RawSource C P ξ i j)
      (formula45PermutedRawSource C P ξ i j) := by
  let l1 := formula29PairLineOne C P ξ i j
  let l2 := formula29PairLineTwo C P ξ i j
  let l3 := formula29PairLineThree C P ξ i j
  let l4 := formula29PairLineFour C P ξ i j
  let l5 := formula29PairLineFive C P ξ i j
  let l6 := formula29PairLineSix C P ξ i j
  let w1 := formula34WMainFactor C P ξ i j j
  let w2 := formula34WPrimeMainFactor C P ξ i j j
  let w3 := formula34WMainFactor C P ξ i i j
  let w4 := formula34WDoublePrimeMainFactor C P ξ i i j
  have hl := formula29_pair_lines_mem_gamma3 C P ξ hij
  have hl1 : l1 ∈ D5.gamma G 3 := hl.1
  have hl2 : l2 ∈ D5.gamma G 3 := hl.2.1
  have hl3 : l3 ∈ D5.gamma G 3 := hl.2.2.1
  have hl4 : l4 ∈ D5.gamma G 3 := hl.2.2.2.1
  have hl5 : l5 ∈ D5.gamma G 3 := hl.2.2.2.2.1
  have hl6 : l6 ∈ D5.gamma G 3 := hl.2.2.2.2.2
  have hw1 : w1 ∈ D5.gamma G 3 :=
    formula34WMainFactor_mem_gamma3 C P ξ i j j
  have hw2 : w2 ∈ D5.gamma G 3 :=
    formula34WPrimeMainFactor_mem_gamma3 C P ξ i j j
  have hw3 : w3 ∈ D5.gamma G 3 :=
    formula34WMainFactor_mem_gamma3 C P ξ i i j
  have hw4 : w4 ∈ D5.gamma G 3 :=
    formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i i j
  have hrotate :
      ([l1, l2, l3, l4, l5, l6, l2] ++ [w1, w2, w3, w4]).Perm
        ([w1, w2, w3, w4] ++ [l1, l2, l3, l4, l5, l6, l2]) :=
    List.perm_append_comm
  have hw12 : [w1, w2].Perm [w2, w1] :=
    (List.Perm.swap w1 w2 []).symm
  have hw34 : [w3, w4].Perm [w4, w3] :=
    (List.Perm.swap w3 w4 []).symm
  have hw : [w1, w2, w3, w4].Perm [w2, w1, w4, w3] := by
    simpa only [List.append_assoc] using hw12.append hw34
  have hmove56 : ([l1, l2, l3, l4] ++ [l5, l6]).Perm
      ([l5, l6] ++ [l1, l2, l3, l4]) := List.perm_append_comm
  have hc1 : [l1, l2, l3, l4, l5, l6, l2].Perm
      [l5, l6, l1, l2, l3, l4, l2] := by
    simpa only [List.append_assoc] using hmove56.append_right [l2]
  have hmove2 : ([l3, l4] ++ [l2]).Perm ([l2] ++ [l3, l4]) :=
    List.perm_append_comm
  have hc2 : [l5, l6, l1, l2, l3, l4, l2].Perm
      [l5, l6, l1, l2, l2, l3, l4] := by
    simpa only [List.append_assoc] using hmove2.append_left [l5, l6, l1, l2]
  have hp : [l1, l2, l3, l4, l5, l6, l2, w1, w2, w3, w4].Perm
      [w2, w1, w4, w3, l5, l6, l1, l2, l2, l3, l4] := by
    have hr : [l1, l2, l3, l4, l5, l6, l2, w1, w2, w3, w4].Perm
        [w1, w2, w3, w4, l1, l2, l3, l4, l5, l6, l2] := by
      simpa only [List.append_assoc] using hrotate
    exact hr.trans <| (hw.append (hc1.trans hc2))
  change D5.ModGammaSix
    ((((l1 * l2) * (l3 * l4)) * (l5 * l6) * l2) *
      ((w1 * w2) * (w3 * w4)))
    (((((w2 * w1) * (w4 * w3)) * (l5 * l6)) *
      (l1 * (l2 * l2))) * (l3 * l4))
  simpa only [List.prod_cons, List.prod_nil, mul_one, mul_assoc] using
    D5.listProd_perm_gammaThree hp (by
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hx
      · exact hl1
      · exact hl2
      · exact hl3
      · exact hl4
      · exact hl5
      · exact hl6
      · exact hl2
      · exact hw1
      · exact hw2
      · exact hw3
      · rcases hx with rfl | hx
        · exact hw4
        · simp at hx)

private theorem formula45_permuted_raw_eq_source
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j : Fin C.s) :
    formula45PermutedRawSource C P ξ i j = formula45Source C P ξ i j := by
  have h40a : formula34WMainFactor C P ξ i j j =
      (formula40First C P ξ i j)⁻¹ := by
    simp [formula34WMainFactor, formula40First, zpow_neg]
  have h40b : formula34WPrimeMainFactor C P ξ i j j =
      (formula40Second C P ξ i j)⁻¹ := by
    simp [formula34WPrimeMainFactor, formula40Second, zpow_neg]
  have h41a : formula34WMainFactor C P ξ i i j =
      (formula41First C P ξ i j)⁻¹ := by
    simp [formula34WMainFactor, formula41First, zpow_neg]
  have h41b : formula34WDoublePrimeMainFactor C P ξ i i j =
      (formula41Second C P ξ i j)⁻¹ := by
    simp [formula34WDoublePrimeMainFactor, formula41Second, zpow_neg]
  have h43 : formula29PairLineOne C P ξ i j *
      (formula29PairLineTwo C P ξ i j * formula29PairLineTwo C P ξ i j) =
      formula43Left C P ξ i j := by
    unfold formula29PairLineOne formula29PairLineTwo formula43Left
    rw [← zpow_add]
    congr 1
    ring
  have h40 : (formula40Second C P ξ i j)⁻¹ *
      (formula40First C P ξ i j)⁻¹ =
      (formula40First C P ξ i j * formula40Second C P ξ i j)⁻¹ := by
    rw [mul_inv_rev]
  have h41 : (formula41Second C P ξ i j)⁻¹ *
      (formula41First C P ξ i j)⁻¹ =
      (formula41First C P ξ i j * formula41Second C P ξ i j)⁻¹ := by
    rw [mul_inv_rev]
  have h42 : formula29PairLineFive C P ξ i j *
      formula29PairLineSix C P ξ i j = formula42Left C P ξ i j := rfl
  have h44 : formula29PairLineThree C P ξ i j *
      formula29PairLineFour C P ξ i j = formula44Left C P ξ i j := rfl
  rw [formula45PermutedRawSource, h40a, h40b, h41a, h41b,
    h40, h41, h42, h43, h44]
  rfl

theorem formula45_raw_to_source
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    {i j : Fin C.s} (hij : i < j) :
    D5.ModGammaSix (formula45RawSource C P ξ i j)
      (formula45Source C P ξ i j) :=
  (formula45_raw_permute C P ξ hij).trans <| by
    rw [formula45_permuted_raw_eq_source]

def formula45RawSourceProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula45RawSource C P ξ)

def formula45SourceProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct (formula45Source C P ξ)

theorem formula29_pairs_and_faces_to_formula45_source
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix
      ((strictPairProduct (formula29PairCorrections C P ξ) *
          formula28URotatedPairStream C P ξ) *
        (formula40FaceProduct C P ξ * formula41FaceProduct C P ξ))
      (formula45SourceProduct C P ξ) := by
  let L2 := formula29PairLineTwo C P ξ
  let F40 : Fin C.s → Fin C.s → G := fun i j =>
    formula34WMainFactor C P ξ i j j *
      formula34WPrimeMainFactor C P ξ i j j
  let F41 : Fin C.s → Fin C.s → G := fun i j =>
    formula34WMainFactor C P ξ i i j *
      formula34WDoublePrimeMainFactor C P ξ i i j
  let CL2 : Fin C.s → Fin C.s → G := fun i j =>
    formula29PairCorrections C P ξ i j * L2 i j
  have hCorr : ∀ i j, i < j →
      formula29PairCorrections C P ξ i j ∈ D5.gamma G 3 :=
    fun i j hij => formula29_pair_corrections_mem_gamma3 C P ξ hij
  have hL2 : ∀ i j, i < j → L2 i j ∈ D5.gamma G 3 := by
    intro i j hij
    exact (formula29_pair_lines_mem_gamma3 C P ξ hij).2.1
  have hF40 : ∀ i j, i < j → F40 i j ∈ D5.gamma G 3 := by
    intro i j hij
    exact (D5.gamma G 3).mul_mem
      (formula34WMainFactor_mem_gamma3 C P ξ i j j)
      (formula34WPrimeMainFactor_mem_gamma3 C P ξ i j j)
  have hF41 : ∀ i j, i < j → F41 i j ∈ D5.gamma G 3 := by
    intro i j hij
    exact (D5.gamma G 3).mul_mem
      (formula34WMainFactor_mem_gamma3 C P ξ i i j)
      (formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i i j)
  have hCL2 : ∀ i j, i < j → CL2 i j ∈ D5.gamma G 3 := by
    intro i j hij
    exact (D5.gamma G 3).mul_mem (hCorr i j hij) (hL2 i j hij)
  have hu := formula28_u_is_formula29_line_two C P ξ
  have hreplace := ((D5.ModEq.refl (D5.gamma G 6)
    (strictPairProduct (formula29PairCorrections C P ξ))).mul hu).mul
      (D5.ModEq.refl (D5.gamma G 6)
        (formula40FaceProduct C P ξ * formula41FaceProduct C P ξ))
  have h12 := strictPairProduct_pointwise_gammaThree
    (formula29PairCorrections C P ξ) L2 hCorr hL2
  have h34 := strictPairProduct_pointwise_gammaThree F40 F41 hF40 hF41
  have hall := strictPairProduct_pointwise_gammaThree CL2
    (fun i j => F40 i j * F41 i j) hCL2
    (fun i j hij => (D5.gamma G 3).mul_mem (hF40 i j hij) (hF41 i j hij))
  have hcollect : D5.ModGammaSix
      ((strictPairProduct (formula29PairCorrections C P ξ) *
          strictPairProduct L2) *
        (strictPairProduct F40 * strictPairProduct F41))
      (formula45RawSourceProduct C P ξ) := by
    simpa [CL2, F40, F41, L2, formula45RawSourceProduct,
      formula45RawSource] using (h12.mul h34).trans hall
  have hlocal : D5.ModGammaSix (formula45RawSourceProduct C P ξ)
      (formula45SourceProduct C P ξ) := by
    unfold formula45RawSourceProduct formula45SourceProduct strictPairProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    exact formula45_raw_to_source C P ξ hij
  simpa [formula40FaceProduct, formula41FaceProduct, F40, F41, L2] using
    hreplace.trans (hcollect.trans hlocal)

theorem formula29_rearrange_section13_source
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula29DisplayedProduct C P ξ)
      ((formula29FirstSixDisplayed C P ξ *
          formula28URotatedPairStream C P ξ) *
        formula34LastFiveDisplayedProduct C P ξ) := by
  let F := formula29FirstSixDisplayed C P ξ
  let L := formula29LineSeven C P ξ
  let U := formula28URotatedPairStream C P ξ
  let A := formula28WLeftDisplayedStream C P ξ
  let B := formula28WRightDisplayedStream C P ξ
  let E := formula28WPrimeDisplayedStream C P ξ
  let T := formula29LineTwelve C P ξ
  have hL : L ∈ D5.gamma G 3 := by
    dsimp [L, formula29LineSeven]
    apply orderedProduct_mem
    intro j
    exact formula22_correction_mem_gamma3 C P ξ j
  have hU : U ∈ D5.gamma G 3 := by
    dsimp [U, formula28URotatedPairStream]
    apply orderedProduct_mem
    intro j
    apply orderedProductWhere_mem
    intro i hij
    exact (formula29_pair_lines_mem_gamma3 C P ξ hij).2.1
  have hinterchange := D5.gammaThree_interchange
    (a := F) (b := L) (c := U) (d := (A * (B * E)) * T) hL hU
  simpa [formula29DisplayedProduct, formula28DisplayedProduct,
    formula34LastFiveDisplayedProduct, F, L, U, A, B, E, T, mul_assoc] using
      hinterchange

/-- The complete global identification missing after the local formulas
(40)--(45): the remainder of formulas (29) and (34) is their pair source. -/
theorem formula29_to_formula45_source
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (formula29DisplayedProduct C P ξ)
      (formula45SourceProduct C P ξ) := by
  rcases hP with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12,
    h13, h14, h15⟩
  have hrearrange := formula29_rearrange_section13_source C P ξ
  have hfirst := formula29_first_six_collected C P ξ
  have hlast := formula34 C P h11 h12 ξ
  have hprincipal := formula34_principal_to_pair_faces C P h2 h5 h10 ξ
  have hreplace : D5.ModGammaSix
      ((formula29FirstSixDisplayed C P ξ *
          formula28URotatedPairStream C P ξ) *
        formula34LastFiveDisplayedProduct C P ξ)
      ((strictPairProduct (formula29PairCorrections C P ξ) *
          formula28URotatedPairStream C P ξ) *
        (formula40FaceProduct C P ξ * formula41FaceProduct C P ξ)) :=
    ((hfirst.symm.mul (D5.ModEq.refl (D5.gamma G 6)
      (formula28URotatedPairStream C P ξ))).mul
        (hlast.trans hprincipal))
  exact hrearrange.trans <| hreplace.trans
    (formula29_pairs_and_faces_to_formula45_source C P ξ)

/-! ## Global pair products in formula (46) -/

def formula46FirstProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
        (P.u i j * orderRatio C.d i j)

def formula46SecondProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
      (C.x1 i ^ orderInt C.d i) ^
        (-P.u i j * orderRatio C.d i j)

def formula46ThirdProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
      (D5.paperComm (C.x1 j) ξ) ^
        (P.u i j * orderRatio C.d i j)

set_option maxHeartbeats 600000 in
/-- Formula (46), obtained by multiplying the completed local Section 13
calculation over every pair `i < j`. -/
theorem formula46
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) :
    D5.ModGammaSix (formula45SourceProduct C P ξ)
      ((formula46FirstProduct C P ξ * formula46SecondProduct C P ξ) *
        formula46ThirdProduct C P ξ) := by
  let F : Fin C.s → Fin C.s → G := fun i j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (C.x1 i ^ orderInt C.d i)) (C.x1 j)) (C.x1 j) ^
        (P.u i j * orderRatio C.d i j)
  let B : Fin C.s → Fin C.s → G := fun i j =>
    D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
      (C.x1 i ^ orderInt C.d i) ^
        (-P.u i j * orderRatio C.d i j)
  let E : Fin C.s → Fin C.s → G := fun i j =>
    D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
      (D5.paperComm (C.x1 j) ξ) ^
        (P.u i j * orderRatio C.d i j)
  have hlocal : D5.ModGammaSix (formula45SourceProduct C P ξ)
      (strictPairProduct fun i j => (F i j * B i j) * E i j) := by
    unfold formula45SourceProduct strictPairProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    simpa [formula46Pair, F, B, E] using formula46_pair C P hP ξ hij
  have hF : ∀ i j, i < j → F i j ∈ D5.gamma G 3 := by
    intro i j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi2 := C.x1_order_power_mem_gamma2 i
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact (D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hi2) hj) hj) _
  have hB : ∀ i j, i < j → B i j ∈ D5.gamma G 3 := by
    intro i j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi2 := C.x1_order_power_mem_gamma2 i
    exact (D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hj) hi) hi2) _
  have hE : ∀ i j, i < j → E i j ∈ D5.gamma G 3 := by
    intro i j hij
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hi2 := C.x1_order_power_mem_gamma2 i
    exact (D5.gamma G 3).zpow_mem (D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hi2 hξ)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ)) _
  have hFB := strictPairProduct_pointwise_gammaThree F B hF hB
  have hFBE := strictPairProduct_pointwise_gammaThree
    (fun i j => F i j * B i j) E
    (fun i j hij => (D5.gamma G 3).mul_mem (hF i j hij) (hB i j hij)) hE
  have hsplit : D5.ModGammaSix
      (strictPairProduct fun i j => (F i j * B i j) * E i j)
      ((strictPairProduct F * strictPairProduct B) * strictPairProduct E) :=
    hFBE.symm.trans <|
      hFB.symm.mul (D5.ModEq.refl (D5.gamma G 6) (strictPairProduct E))
  simpa [formula46FirstProduct, formula46SecondProduct,
    formula46ThirdProduct, F, B, E] using hlocal.trans hsplit

/-- Formula (46) as a direct consequence of the complete formula-(29)
expansion. -/
theorem formula29_to_formula46
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (formula29DisplayedProduct C P ξ)
      ((formula46FirstProduct C P ξ * formula46SecondProduct C P ξ) *
        formula46ThirdProduct C P ξ) :=
  (formula29_to_formula45_source C P hP ξ).trans (formula46 C P hP ξ)

/-- Completed Section 13 for the finite-group project: every admissible
Tahara word has commutator (46) modulo `γ₆`. -/
theorem section13_finite [Finite G]
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (D5.paperComm (word C P) ξ)
      ((formula46FirstProduct C P ξ * formula46SecondProduct C P ξ) *
        formula46ThirdProduct C P ξ) :=
  (formula29 C P hP ξ).trans (formula29_to_formula46 C P hP ξ)

end

end D5.Tahara
