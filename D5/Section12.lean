import D5.Formula34

/-!
# Section 12: strict triples

This file formalizes formulas (37)--(39).  The three powers in the
principal products of (34) are transferred to a common weight-four
commutator.  The three Hall--Petresco corrections have weight five and are
killed by the divisibilities in condition (10).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Formula (37), with the factors ordered as in the common exponent in
formula (39). -/
theorem formula37
    (C : Context G) (P : Parameters C.s C.t) (h5 : P.Condition5)
    {i j k : Fin C.s} (hij : i < j) (hjk : j < k) :
    orderInt C.d i * P.w i j k + orderInt C.d j * P.w' i j k +
      orderInt C.d k * P.w'' i j k = 0 := by
  simpa [mul_comm] using h5 i j k hij hjk

/-- Formula (38), extracted from the three modular congruences in
condition (10). -/
theorem formula38
    (C : Context G) (P : Parameters C.s C.t) (h10 : P.Condition10)
    {i j k : Fin C.s} (hij : i < j) (hjk : j < k) :
    orderInt C.d i ∣ P.w i j k * TaharaArithmetic.binom2 (C.d i) ∧
    orderInt C.d i ∣ P.w' i j k * TaharaArithmetic.binom2 (C.d j) ∧
    orderInt C.d i ∣ P.w'' i j k * TaharaArithmetic.binom2 (C.d k) := by
  rcases h10 i j k hij hjk with ⟨hw, hw', hw''⟩
  exact ⟨Int.modEq_zero_iff_dvd.mp hw,
    Int.modEq_zero_iff_dvd.mp hw', Int.modEq_zero_iff_dvd.mp hw''⟩

/-- A power in the last entry of a weight-four commutator.  The only
surviving correction modulo `γ₆` is the weight-five binomial term. -/
theorem weightThree_comm_zpow_right_hallPetresco
    {a x : G} (ha : a ∈ D5.gamma G 3) (hx : x ∈ D5.gamma G 1)
    (n : ℕ) :
    D5.ModGammaSix (D5.paperComm a (x ^ (n : ℤ)))
      (D5.paperComm a x ^ (n : ℤ) *
        D5.paperComm (D5.paperComm a x) x ^
          TaharaArithmetic.binom2 n) := by
  let c := D5.paperComm a x
  let d := D5.paperComm c x
  let e := D5.paperComm d x
  have hc : c ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hx
  have hd : d ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hc hx
  have he : e ∈ D5.gamma G 6 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hx
  have hp := D5.paperComm_zpow_right_hallPetresco_of_weight
    (r := 3) (by norm_num) ha hx n
  have hp6 := hp.mono (D5.gamma_antitone G (by norm_num : 6 ≤ 7))
  have he1 : D5.ModGammaSix
      (e ^ TaharaArithmetic.binom3 n) 1 :=
    D5.modEq_one_iff_mem.mpr <| (D5.gamma G 6).zpow_mem he _
  simpa [c, d, e, mul_assoc] using
    hp6.trans (((D5.ModEq.refl (D5.gamma G 6)
      (c ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n))).mul he1)

/-- Transfer a power from the third entry of a fourfold commutator. -/
theorem fourfold_zpow_third_entry
    {ξ x y z : G} (hξ : ξ ∈ D5.gamma G 1)
    (hx : x ∈ D5.gamma G 1) (hy : y ∈ D5.gamma G 1)
    (hz : z ∈ D5.gamma G 1) (n : ℕ) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ x) (y ^ (n : ℤ))) z)
      (D5.paperComm (D5.paperComm (D5.paperComm ξ x) y) z ^ (n : ℤ) *
        D5.paperComm
          (D5.paperComm (D5.paperComm (D5.paperComm ξ x) y) y) z ^
            TaharaArithmetic.binom2 n) := by
  let q := D5.paperComm ξ x
  let c := D5.paperComm q y
  let d := D5.paperComm c y
  let e := D5.paperComm d y
  have hq : q ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hc : c ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hy
  have hd : d ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hc hy
  have he : e ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hy
  have hp := D5.paperComm_zpow_right_hallPetresco_of_weight
    (r := 2) (by norm_num) hq hy n
  have hp5 := hp.mono (D5.gamma_antitone G (by norm_num : 5 ≤ 6))
  have he1 : D5.ModEq (D5.gamma G 5)
      (e ^ TaharaArithmetic.binom3 n) 1 :=
    D5.modEq_one_iff_mem.mpr <| (D5.gamma G 5).zpow_mem he _
  have hinner : D5.ModEq (D5.gamma G 5)
      (D5.paperComm q (y ^ (n : ℤ)))
      (c ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) := by
    simpa [c, d, e, mul_assoc] using
      hp5.trans (((D5.ModEq.refl (D5.gamma G 5)
        (c ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n))).mul he1)
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hz
  have hcn : c ^ (n : ℤ) ∈ D5.gamma G 3 :=
    (D5.gamma G 3).zpow_mem hc _
  have hdn : d ^ TaharaArithmetic.binom2 n ∈ D5.gamma G 4 :=
    (D5.gamma G 4).zpow_mem hd _
  have hsplit := D5.paperComm_mul_left_mod_gamma
    (n := 6) (r := 3) (s := 4) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hcn hdn hz
  have hcPow := D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 3) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hc hz (n : ℤ)
  have hdPow := D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 4) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hd hz
      (TaharaArithmetic.binom2 n)
  simpa [q, c, d] using hlift.trans (hsplit.trans (hcPow.mul hdPow))

/-- Transfer a power from the second entry of a fourfold commutator. -/
theorem fourfold_zpow_second_entry
    {ξ x y z : G} (hξ : ξ ∈ D5.gamma G 1)
    (hx : x ∈ D5.gamma G 1) (hy : y ∈ D5.gamma G 1)
    (hz : z ∈ D5.gamma G 1) (n : ℕ) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (x ^ (n : ℤ))) y) z)
      (D5.paperComm (D5.paperComm (D5.paperComm ξ x) y) z ^ (n : ℤ) *
        D5.paperComm
          (D5.paperComm (D5.paperComm (D5.paperComm ξ x) x) y) z ^
            TaharaArithmetic.binom2 n) := by
  let q := D5.paperComm ξ x
  let d := D5.paperComm q x
  let e := D5.paperComm d x
  let a := D5.paperComm q y
  let b := D5.paperComm d y
  have hq : q ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hd : d ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have he : e ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hx
  have ha : a ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hy
  have hb : b ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hy
  have hp := D5.paperComm_zpow_right_hallPetresco_of_weight
    (r := 1) (by norm_num) hξ hx n
  have hp4 := hp.mono (D5.gamma_antitone G (by norm_num : 4 ≤ 5))
  have he1 : D5.ModEq (D5.gamma G 4)
      (e ^ TaharaArithmetic.binom3 n) 1 :=
    D5.modEq_one_iff_mem.mpr <| (D5.gamma G 4).zpow_mem he _
  have hfirst : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ξ (x ^ (n : ℤ)))
      (q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) := by
    simpa [q, d, e, mul_assoc] using
      hp4.trans (((D5.ModEq.refl (D5.gamma G 4)
        (q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n))).mul he1)
  have hfirstY := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hfirst hy
  have hqn : q ^ (n : ℤ) ∈ D5.gamma G 2 :=
    (D5.gamma G 2).zpow_mem hq _
  have hdn : d ^ TaharaArithmetic.binom2 n ∈ D5.gamma G 3 :=
    (D5.gamma G 3).zpow_mem hd _
  have hsplitY := D5.paperComm_mul_left_mod_gamma
    (n := 5) (r := 2) (s := 3) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hqn hdn hy
  have hqPow := D5.paperComm_zpow_left_mod_gamma
    (n := 5) (r := 2) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hq hy (n : ℤ)
  have hdPow := D5.paperComm_zpow_left_mod_gamma
    (n := 5) (r := 3) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hd hy
      (TaharaArithmetic.binom2 n)
  have hmiddle : D5.ModEq (D5.gamma G 5)
      (D5.paperComm (D5.paperComm ξ (x ^ (n : ℤ))) y)
      (a ^ (n : ℤ) * b ^ TaharaArithmetic.binom2 n) := by
    simpa [a, b] using hfirstY.trans (hsplitY.trans (hqPow.mul hdPow))
  have hmiddleZ := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hmiddle hz
  have han : a ^ (n : ℤ) ∈ D5.gamma G 3 :=
    (D5.gamma G 3).zpow_mem ha _
  have hbn : b ^ TaharaArithmetic.binom2 n ∈ D5.gamma G 4 :=
    (D5.gamma G 4).zpow_mem hb _
  have hsplitZ := D5.paperComm_mul_left_mod_gamma
    (n := 6) (r := 3) (s := 4) (t := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) han hbn hz
  have haPow := D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 3) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) ha hz (n : ℤ)
  have hbPow := D5.paperComm_zpow_left_mod_gamma
    (n := 6) (r := 4) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) hb hz
      (TaharaArithmetic.binom2 n)
  simpa [q, d, a, b] using
    hmiddleZ.trans (hsplitZ.trans (haPow.mul hbPow))

/-! ## The local strict-triple calculation -/

def formula39Base
    (C : Context G) (ξ : G) (i j k : Fin C.s) : G :=
  D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 k)) (C.x1 j))
    (C.x1 i)

def formula39CorrectionI
    (C : Context G) (ξ : G) (i j k : Fin C.s) : G :=
  D5.paperComm (formula39Base C ξ i j k) (C.x1 i)

def formula39CorrectionJ
    (C : Context G) (ξ : G) (i j k : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 k)) (C.x1 j))
      (C.x1 j)) (C.x1 i)

def formula39CorrectionK
    (C : Context G) (ξ : G) (i j k : Fin C.s) : G :=
  D5.paperComm
    (D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 k)) (C.x1 k))
      (C.x1 j)) (C.x1 i)

def formula39ExpandedFactor
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) : G :=
  formula39Base C ξ i j k ^
      (-orderInt C.d i * P.w i j k -
        orderInt C.d j * P.w' i j k -
        orderInt C.d k * P.w'' i j k) *
    formula39CorrectionI C ξ i j k ^
      (-P.w i j k * TaharaArithmetic.binom2 (C.d i)) *
    formula39CorrectionJ C ξ i j k ^
      (-P.w' i j k * TaharaArithmetic.binom2 (C.d j)) *
    formula39CorrectionK C ξ i j k ^
      (-P.w'' i j k * TaharaArithmetic.binom2 (C.d k))

theorem formula39_factors_mem_gamma3
    (C : Context G) (ξ : G) (i j k : Fin C.s) :
    formula39Base C ξ i j k ∈ D5.gamma G 3 ∧
    formula39CorrectionI C ξ i j k ∈ D5.gamma G 3 ∧
    formula39CorrectionJ C ξ i j k ∈ D5.gamma G 3 ∧
    formula39CorrectionK C ξ i j k ∈ D5.gamma G 3 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h2 := D5.paperComm_mem_gamma_add (r := 1) (s := 1)
    (by norm_num) (by norm_num) hξ hk
  have h3 := D5.paperComm_mem_gamma_add (r := 2) (s := 1)
    (by norm_num) (by norm_num) h2 hj
  have h4 := D5.paperComm_mem_gamma_add (r := 3) (s := 1)
    (by norm_num) (by norm_num) h3 hi
  have h5i := D5.paperComm_mem_gamma_add (r := 4) (s := 1)
    (by norm_num) (by norm_num) h4 hi
  have h4j := D5.paperComm_mem_gamma_add (r := 3) (s := 1)
    (by norm_num) (by norm_num) h3 hj
  have h5j := D5.paperComm_mem_gamma_add (r := 4) (s := 1)
    (by norm_num) (by norm_num) h4j hi
  have h3k := D5.paperComm_mem_gamma_add (r := 2) (s := 1)
    (by norm_num) (by norm_num) h2 hk
  have h4k := D5.paperComm_mem_gamma_add (r := 3) (s := 1)
    (by norm_num) (by norm_num) h3k hj
  have h5k := D5.paperComm_mem_gamma_add (r := 4) (s := 1)
    (by norm_num) (by norm_num) h4k hi
  exact ⟨D5.gamma_antitone G (by norm_num) h4,
    D5.gamma_antitone G (by norm_num) h5i,
    D5.gamma_antitone G (by norm_num) h5j,
    D5.gamma_antitone G (by norm_num) h5k⟩

/-- The three powered principal factors of (34), expanded exactly as in the
first congruence of formula (39). -/
theorem formula39_expand
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (i j k : Fin C.s) :
    D5.ModGammaSix
      ((formula34WMainFactor C P ξ i j k *
          formula34WPrimeMainFactor C P ξ i j k) *
        formula34WDoublePrimeMainFactor C P ξ i j k)
      (formula39ExpandedFactor C P ξ i j k) := by
  let A := formula39Base C ξ i j k
  let I := formula39CorrectionI C ξ i j k
  let J := formula39CorrectionJ C ξ i j k
  let K := formula39CorrectionK C ξ i j k
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  rcases formula39_factors_mem_gamma3 C ξ i j k with ⟨hA, hI, hJ, hK⟩
  have hlast0 := weightThree_comm_zpow_right_hallPetresco
    (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hk) hj)
    hi (C.d i)
  have hlastPow := hlast0.zpow (-P.w i j k)
  have hlastDist := D5.gammaThree_mul_zpow
    ((D5.gamma G 3).zpow_mem hA (orderInt C.d i))
    ((D5.gamma G 3).zpow_mem hI (TaharaArithmetic.binom2 (C.d i)))
    (-P.w i j k)
  have hlast : D5.ModGammaSix (formula34WMainFactor C P ξ i j k)
      (A ^ (-orderInt C.d i * P.w i j k) *
        I ^ (-P.w i j k * TaharaArithmetic.binom2 (C.d i))) := by
    have hp := hlastPow.trans hlastDist
    rw [← zpow_mul, ← zpow_mul] at hp
    convert hp using 1 <;>
      simp [formula34WMainFactor, A, I, formula39Base,
        formula39CorrectionI, orderInt] <;> ring
  have hthird0 := fourfold_zpow_third_entry hξ hk hj hi (C.d j)
  have hthirdPow := hthird0.zpow (-P.w' i j k)
  have hthirdDist := D5.gammaThree_mul_zpow
    ((D5.gamma G 3).zpow_mem hA (orderInt C.d j))
    ((D5.gamma G 3).zpow_mem hJ (TaharaArithmetic.binom2 (C.d j)))
    (-P.w' i j k)
  have hthird : D5.ModGammaSix
      (formula34WPrimeMainFactor C P ξ i j k)
      (A ^ (-orderInt C.d j * P.w' i j k) *
        J ^ (-P.w' i j k * TaharaArithmetic.binom2 (C.d j))) := by
    have hp := hthirdPow.trans hthirdDist
    rw [← zpow_mul, ← zpow_mul] at hp
    convert hp using 1 <;>
      simp [formula34WPrimeMainFactor, A, J, formula39Base,
        formula39CorrectionJ, orderInt] <;> ring
  have hsecond0 := fourfold_zpow_second_entry hξ hk hj hi (C.d k)
  have hsecondPow := hsecond0.zpow (-P.w'' i j k)
  have hsecondDist := D5.gammaThree_mul_zpow
    ((D5.gamma G 3).zpow_mem hA (orderInt C.d k))
    ((D5.gamma G 3).zpow_mem hK (TaharaArithmetic.binom2 (C.d k)))
    (-P.w'' i j k)
  have hsecond : D5.ModGammaSix
      (formula34WDoublePrimeMainFactor C P ξ i j k)
      (A ^ (-orderInt C.d k * P.w'' i j k) *
        K ^ (-P.w'' i j k * TaharaArithmetic.binom2 (C.d k))) := by
    have hp := hsecondPow.trans hsecondDist
    rw [← zpow_mul, ← zpow_mul] at hp
    convert hp using 1 <;>
      simp [formula34WDoublePrimeMainFactor, A, K, formula39Base,
        formula39CorrectionK, orderInt] <;> ring
  let a := A ^ (-orderInt C.d i * P.w i j k)
  let b := I ^ (-P.w i j k * TaharaArithmetic.binom2 (C.d i))
  let c := A ^ (-orderInt C.d j * P.w' i j k)
  let d := J ^ (-P.w' i j k * TaharaArithmetic.binom2 (C.d j))
  let e := A ^ (-orderInt C.d k * P.w'' i j k)
  let f := K ^ (-P.w'' i j k * TaharaArithmetic.binom2 (C.d k))
  have ha : a ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hA _
  have hb : b ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hI _
  have hc : c ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hA _
  have hd : d ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hJ _
  have he : e ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hA _
  have hf : f ∈ D5.gamma G 3 := (D5.gamma G 3).zpow_mem hK _
  have hp : [a, b, c, d, e, f].Perm [a, c, e, b, d, f] := by
    have hleft : ([b] ++ [c, d, e]).Perm ([c, d, e] ++ [b]) :=
      List.perm_append_comm
    have h1 : [a, b, c, d, e, f].Perm [a, c, d, e, b, f] := by
      apply List.Perm.cons a
      simpa only [List.append_assoc] using hleft.append_right [f]
    have hright : ([d] ++ [e]).Perm ([e] ++ [d]) := List.perm_append_comm
    have h2 : [a, c, d, e, b, f].Perm [a, c, e, d, b, f] := by
      apply List.Perm.cons a
      apply List.Perm.cons c
      simpa only [List.append_assoc] using hright.append_right [b, f]
    have h3 : [a, c, e, d, b, f].Perm [a, c, e, b, d, f] := by
      apply List.Perm.cons a
      apply List.Perm.cons c
      apply List.Perm.cons e
      exact (List.Perm.swap d b [f]).symm
    exact h1.trans (h2.trans h3)
  have hperm := D5.listProd_perm_gammaThree hp (fun x hx => by
    simp only [List.mem_cons] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | hx
    · exact ha
    · exact hb
    · exact hc
    · exact hd
    · exact he
    · rcases hx with rfl | hx
      · exact hf
      · simp at hx)
  have hcollect : a * c * e = A ^
      (-orderInt C.d i * P.w i j k -
        orderInt C.d j * P.w' i j k -
        orderInt C.d k * P.w'' i j k) := by
    simp only [a, c, e, ← zpow_add]
    congr 1
    ring
  have htarget : [a, c, e, b, d, f].prod =
      formula39ExpandedFactor C P ξ i j k := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    rw [show a * (c * (e * (b * (d * f)))) = (((a * c * e) * b) * d) * f by
      group]
    rw [hcollect]
    rfl
  have hreordered : D5.ModGammaSix [a, b, c, d, e, f].prod
      (formula39ExpandedFactor C P ξ i j k) :=
    hperm.trans <| by rw [htarget]
  have hall := (hlast.mul hthird).mul hsecond
  exact hall.trans <| by
    simpa [a, b, c, d, e, f, List.prod_cons, List.prod_nil,
      mul_assoc] using hreordered

/-- A weight-five commutator is killed by any exponent divisible by the
order exponent of its last entry. -/
theorem weightFive_last_entry_power_vanish_general
    {a x : G} {d : ℤ} (ha : a ∈ D5.gamma G 4)
    (hx : x ∈ D5.gamma G 1) (hxd : x ^ d ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm a x ^ d) 1 := by
  have hp := D5.paperComm_zpow_right_mod_gamma
    (n := 6) (r := 4) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) ha hx d
  have hfinal : D5.ModGammaSix (D5.paperComm a (x ^ d)) 1 :=
    D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hxd
  exact hp.symm.trans hfinal

/-- The expanded right side of (39) is trivial by (37)--(38). -/
theorem formula39_expanded_vanish
    (C : Context G) (P : Parameters C.s C.t)
    (h5 : P.Condition5) (h10 : P.Condition10) (ξ : G)
    {i j k : Fin C.s} (hij : i < j) (hjk : j < k) :
    D5.ModGammaSix (formula39ExpandedFactor C P ξ i j k) 1 := by
  let A := formula39Base C ξ i j k
  let I := formula39CorrectionI C ξ i j k
  let J := formula39CorrectionJ C ξ i j k
  let K := formula39CorrectionK C ξ i j k
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have h2 := D5.paperComm_mem_gamma_add (r := 1) (s := 1)
    (by norm_num) (by norm_num) hξ hk
  have h3 := D5.paperComm_mem_gamma_add (r := 2) (s := 1)
    (by norm_num) (by norm_num) h2 hj
  have hA4 : A ∈ D5.gamma G 4 := by
    simpa [A, formula39Base] using
      D5.paperComm_mem_gamma_add (r := 3) (s := 1)
        (by norm_num) (by norm_num) h3 hi
  have hJ4 : D5.paperComm
      (D5.paperComm (D5.paperComm ξ (C.x1 k)) (C.x1 j)) (C.x1 j) ∈
      D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) h3 hj
  have h3k := D5.paperComm_mem_gamma_add (r := 2) (s := 1)
    (by norm_num) (by norm_num) h2 hk
  have hK4 : D5.paperComm
      (D5.paperComm (D5.paperComm ξ (C.x1 k)) (C.x1 k)) (C.x1 j) ∈
      D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (r := 3) (s := 1)
      (by norm_num) (by norm_num) h3k hj
  have hIbase : D5.ModGammaSix (I ^ orderInt C.d i) 1 := by
    simpa [I, formula39CorrectionI] using
      weightFive_last_entry_power_vanish_general hA4 hi
        (C.x1_order_power_mem_gamma2 i)
  have hJbase : D5.ModGammaSix (J ^ orderInt C.d i) 1 := by
    simpa [J, formula39CorrectionJ] using
      weightFive_last_entry_power_vanish_general hJ4 hi
        (C.x1_order_power_mem_gamma2 i)
  have hKbase : D5.ModGammaSix (K ^ orderInt C.d i) 1 := by
    simpa [K, formula39CorrectionK] using
      weightFive_last_entry_power_vanish_general hK4 hi
        (C.x1_order_power_mem_gamma2 i)
  rcases formula38 C P h10 hij hjk with ⟨hdI, hdJ, hdK⟩
  have hdI' : orderInt C.d i ∣
      -P.w i j k * TaharaArithmetic.binom2 (C.d i) := by
    simpa only [neg_mul] using dvd_neg.mpr hdI
  have hdJ' : orderInt C.d i ∣
      -P.w' i j k * TaharaArithmetic.binom2 (C.d j) := by
    simpa only [neg_mul] using dvd_neg.mpr hdJ
  have hdK' : orderInt C.d i ∣
      -P.w'' i j k * TaharaArithmetic.binom2 (C.d k) := by
    simpa only [neg_mul] using dvd_neg.mpr hdK
  have hIv := D5.modGammaSix_zpow_eq_one_of_dvd hIbase hdI'
  have hJv := D5.modGammaSix_zpow_eq_one_of_dvd hJbase hdJ'
  have hKv := D5.modGammaSix_zpow_eq_one_of_dvd hKbase hdK'
  have h37 := formula37 C P h5 hij hjk
  have hexp : -orderInt C.d i * P.w i j k -
      orderInt C.d j * P.w' i j k -
      orderInt C.d k * P.w'' i j k = 0 := by
    linarith
  have hmain : D5.ModGammaSix
      (A ^ (-orderInt C.d i * P.w i j k -
        orderInt C.d j * P.w' i j k -
        orderInt C.d k * P.w'' i j k)) 1 := by
    rw [hexp, zpow_zero]
  simpa [formula39ExpandedFactor, A, I, J, K] using
    (((hmain.mul hIv).mul hJv).mul hKv)

/-- Formula (39) for one strict triple. -/
theorem formula39
    (C : Context G) (P : Parameters C.s C.t)
    (h5 : P.Condition5) (h10 : P.Condition10) (ξ : G)
    {i j k : Fin C.s} (hij : i < j) (hjk : j < k) :
    D5.ModGammaSix
      ((formula34WMainFactor C P ξ i j k *
          formula34WPrimeMainFactor C P ξ i j k) *
        formula34WDoublePrimeMainFactor C P ξ i j k) 1 :=
  (formula39_expand C P ξ i j k).trans
    (formula39_expanded_vanish C P h5 h10 ξ hij hjk)

def formula39StrictTripleProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    orderedProductWhere (j < ·) fun k =>
      ((formula34WMainFactor C P ξ i j k *
          formula34WPrimeMainFactor C P ξ i j k) *
        formula34WDoublePrimeMainFactor C P ξ i j k)

/-- Formula (39) collected over every `i < j < k`. -/
theorem formula39_strictTripleProduct_vanish
    (C : Context G) (P : Parameters C.s C.t)
    (h5 : P.Condition5) (h10 : P.Condition10) (ξ : G) :
    D5.ModGammaSix (formula39StrictTripleProduct C P ξ) 1 := by
  have hpoint : D5.ModGammaSix (formula39StrictTripleProduct C P ξ)
      (orderedProduct fun _i : Fin C.s => (1 : G)) := by
    unfold formula39StrictTripleProduct
    apply modEq_orderedProduct
    intro i
    have hi : D5.ModGammaSix
        (orderedProductWhere (i < ·) fun j =>
          orderedProductWhere (j < ·) fun k =>
            ((formula34WMainFactor C P ξ i j k *
                formula34WPrimeMainFactor C P ξ i j k) *
              formula34WDoublePrimeMainFactor C P ξ i j k)) 1 := by
      have hj : D5.ModGammaSix
          (orderedProductWhere (i < ·) fun j =>
            orderedProductWhere (j < ·) fun k =>
              ((formula34WMainFactor C P ξ i j k *
                  formula34WPrimeMainFactor C P ξ i j k) *
                formula34WDoublePrimeMainFactor C P ξ i j k))
          (orderedProductWhere (i < ·) fun _j : Fin C.s => (1 : G)) := by
        apply modEq_orderedProductWhere
        intro j hij
        have hk : D5.ModGammaSix
            (orderedProductWhere (j < ·) fun k =>
              ((formula34WMainFactor C P ξ i j k *
                  formula34WPrimeMainFactor C P ξ i j k) *
                formula34WDoublePrimeMainFactor C P ξ i j k))
            (orderedProductWhere (j < ·) fun _k : Fin C.s => (1 : G)) := by
          apply modEq_orderedProductWhere
          intro k hjk
          exact formula39 C P h5 h10 ξ hij hjk
        simpa [orderedProductWhere] using hk
      simpa [orderedProductWhere] using hj
    simpa using hi
  exact hpoint.trans <| by
    simpa [orderedProduct] using D5.ModEq.refl (D5.gamma G 6) (1 : G)

/-! ## The three strict principal streams -/

/-- A product over the strict triangle `i < j < k`. -/
def strictTripleProduct {s : ℕ}
    (f : Fin s → Fin s → Fin s → G) : G :=
  orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
    orderedProductWhere (j < ·) fun k => f i j k

/-- Pointwise collection of two weight-at-least-three products over the
strict triangle.  This is the strict analogue of the collection lemma used
for the weak triangle in formula (34). -/
theorem strictTripleProduct_pointwise_gammaThree
    {s : ℕ} (f g : Fin s → Fin s → Fin s → G)
    (hf : ∀ i j k, i < j → j < k → f i j k ∈ D5.gamma G 3)
    (hg : ∀ i j k, i < j → j < k → g i j k ∈ D5.gamma G 3) :
    D5.ModGammaSix (strictTripleProduct f * strictTripleProduct g)
      (strictTripleProduct fun i j k => f i j k * g i j k) := by
  let FR : Fin s → Fin s → G := fun i j =>
    orderedProductWhere (j < ·) fun k => f i j k
  let GR : Fin s → Fin s → G := fun i j =>
    orderedProductWhere (j < ·) fun k => g i j k
  have hFR : ∀ i j, i < j → FR i j ∈ D5.gamma G 3 := by
    intro i j hij
    apply orderedProductWhere_mem
    intro k hjk
    exact hf i j k hij hjk
  have hGR : ∀ i j, i < j → GR i j ∈ D5.gamma G 3 := by
    intro i j hij
    apply orderedProductWhere_mem
    intro k hjk
    exact hg i j k hij hjk
  have hsplitK : D5.ModGammaSix
      (strictTripleProduct fun i j k => f i j k * g i j k)
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        FR i j * GR i j) := by
    unfold strictTripleProduct
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    simpa [FR, GR] using
      D5.orderedProductWhere_pointwise_mul_gammaThree (j < ·)
        (f i j) (g i j) (fun k hjk => hf i j k hij hjk)
          (fun k hjk => hg i j k hij hjk)
  let FB : Fin s → G := fun i => orderedProductWhere (i < ·) fun j => FR i j
  let GB : Fin s → G := fun i => orderedProductWhere (i < ·) fun j => GR i j
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
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        FR i j * GR i j)
      (orderedProduct fun i => FB i * GB i) := by
    apply modEq_orderedProduct
    intro i
    simpa [FB, GB] using
      D5.orderedProductWhere_pointwise_mul_gammaThree (i < ·)
        (FR i) (GR i) (fun j hij => hFR i j hij)
          (fun j hij => hGR i j hij)
  have hsplitI : D5.ModGammaSix
      (orderedProduct fun i => FB i * GB i)
      (orderedProduct FB * orderedProduct GB) :=
    D5.orderedProduct_pointwise_mul_gammaThree FB GB hFB hGB
  have hsplit := hsplitK.trans (hsplitJ.trans hsplitI)
  simpa [strictTripleProduct, FB, GB, FR, GR] using hsplit.symm

/-- The strict `w` part of the first principal product in (34). -/
def formula34WMainStrictProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictTripleProduct (formula34WMainFactor C P ξ)

/-- The strict `w'` part of the second principal product in (34). -/
def formula34WPrimeMainStrictProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictTripleProduct (formula34WPrimeMainFactor C P ξ)

/-- The strict `w''` part of the third principal product in (34). -/
def formula34WDoublePrimeMainStrictProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictTripleProduct (formula34WDoublePrimeMainFactor C P ξ)

/-- The three strict principal streams of formula (34) are exactly the
global product governed by formula (39), and hence vanish modulo `γ₆`. -/
theorem formula39_strict_principal_streams_vanish
    (C : Context G) (P : Parameters C.s C.t)
    (h5 : P.Condition5) (h10 : P.Condition10) (ξ : G) :
    D5.ModGammaSix
      ((formula34WMainStrictProduct C P ξ *
          formula34WPrimeMainStrictProduct C P ξ) *
        formula34WDoublePrimeMainStrictProduct C P ξ) 1 := by
  let W : Fin C.s → Fin C.s → Fin C.s → G := formula34WMainFactor C P ξ
  let W' : Fin C.s → Fin C.s → Fin C.s → G :=
    formula34WPrimeMainFactor C P ξ
  let W'' : Fin C.s → Fin C.s → Fin C.s → G :=
    formula34WDoublePrimeMainFactor C P ξ
  have hW : ∀ i j k, i < j → j < k → W i j k ∈ D5.gamma G 3 := by
    intro i j k hij hjk
    exact formula34WMainFactor_mem_gamma3 C P ξ i j k
  have hW' : ∀ i j k, i < j → j < k → W' i j k ∈ D5.gamma G 3 := by
    intro i j k hij hjk
    exact formula34WPrimeMainFactor_mem_gamma3 C P ξ i j k
  have hW'' : ∀ i j k, i < j → j < k → W'' i j k ∈ D5.gamma G 3 := by
    intro i j k hij hjk
    exact formula34WDoublePrimeMainFactor_mem_gamma3 C P ξ i j k
  have hfirst := strictTripleProduct_pointwise_gammaThree W W' hW hW'
  have hsecond := strictTripleProduct_pointwise_gammaThree
    (fun i j k => W i j k * W' i j k) W''
    (fun i j k hij hjk => (D5.gamma G 3).mul_mem
      (hW i j k hij hjk) (hW' i j k hij hjk)) hW''
  have hcollect : D5.ModGammaSix
      ((strictTripleProduct W * strictTripleProduct W') *
        strictTripleProduct W'')
      (formula39StrictTripleProduct C P ξ) := by
    simpa [W, W', W'', formula39StrictTripleProduct,
      strictTripleProduct] using
        (hfirst.mul (D5.ModEq.refl (D5.gamma G 6)
          (strictTripleProduct W''))).trans hsecond
  have hstreams : D5.ModGammaSix
      ((formula34WMainStrictProduct C P ξ *
          formula34WPrimeMainStrictProduct C P ξ) *
        formula34WDoublePrimeMainStrictProduct C P ξ)
      (formula39StrictTripleProduct C P ξ) := by
    simpa [formula34WMainStrictProduct, formula34WPrimeMainStrictProduct,
      formula34WDoublePrimeMainStrictProduct, W, W', W''] using hcollect
  exact hstreams.trans (formula39_strictTripleProduct_vanish C P h5 h10 ξ)

/-- Condition (2) removes the completely diagonal `w` factor. -/
theorem formula34WMainFactor_diagonal_eq_one
    (C : Context G) (P : Parameters C.s C.t) (h2 : P.Condition2)
    (ξ : G) (i : Fin C.s) : formula34WMainFactor C P ξ i i i = 1 := by
  simp [formula34WMainFactor, h2 i]

end

end D5.Tahara
