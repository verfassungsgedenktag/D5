import D5.TaharaCondition6
import D5.WeightFivePowers

/-!
# Divisibility consequences after the full transfer formula

This file verifies the paragraph following formula (20): its last three
weight-five factors vanish because their exponents are divisible by `d(i)`.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

structure Formula20Vanishing (C : Context G) (P : Parameters C.s C.t)
    (ξ : G) (i j : Fin C.s) : Prop where
  commutatorSuffix : D5.ModGammaSix
    (D5.paperComm
      (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
      (D5.paperComm ξ (C.x1 j)) ^
        (-P.u i j * TaharaArithmetic.binom2 (C.d j))) 1
  threeRepeated : D5.ModGammaSix
    (D5.paperComm
      (D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 i))
        (C.x1 i)) (C.x1 i) ^
          (P.u i j * TaharaArithmetic.binom3 (C.d j))) 1
  lastEntry : D5.ModGammaSix
    (D5.paperComm
      (D5.paperComm (D5.paperComm (D5.paperComm ξ (C.x1 j)) (C.x1 j))
        (C.x1 j)) (C.x1 i) ^
          (-P.u i j * TaharaArithmetic.binom3 (C.d j))) 1

theorem formula20_last_three_vanish
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {i j : Fin C.s} (hij : i < j) :
    Formula20Vanishing C P ξ i j := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hpow := C.x1_order_power_mem_gamma2 i
  have hpairs := pairConsequences C P hP hij
  have hsuffixBase := D5.weightFive_commutator_suffix_power_vanish
    hξ hxj hxi hpow
  have hrepeatedBase := D5.weightFive_three_repeated_entry_power_vanish
    hξ hxj hxi hpow
  have hlastBase := D5.weightFive_last_entry_power_vanish
    hξ hxj hxi hpow
  have hdSuffix : orderInt C.d i ∣
      -P.u i j * TaharaArithmetic.binom2 (C.d j) := by
    have h := hpairs.dvd17_right
    simpa only [neg_mul] using (dvd_neg.mpr h)
  have hdB3 : orderInt C.d i ∣
      P.u i j * TaharaArithmetic.binom3 (C.d j) :=
    hpairs.dvd16_right
  have hdNegB3 : orderInt C.d i ∣
      -P.u i j * TaharaArithmetic.binom3 (C.d j) := by
    simpa only [neg_mul] using (dvd_neg.mpr hpairs.dvd16_right)
  exact
    { commutatorSuffix :=
        D5.modGammaSix_zpow_eq_one_of_dvd hsuffixBase hdSuffix
      threeRepeated :=
        D5.modGammaSix_zpow_eq_one_of_dvd hrepeatedBase hdB3
      lastEntry :=
        D5.modGammaSix_zpow_eq_one_of_dvd hlastBase hdNegB3 }

end

end D5.Tahara
