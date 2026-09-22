import D5.WeightTwo26

/-!
# Condition (4.3.13) and weight-five exponent replacement

The source uses condition (4.3.13) to replace the exponent of
`[ξ,x₃ₗ,x₁ᵢ]` modulo `gcd(d(i),f(l))`.  This file verifies that the two
orders indeed kill that weight-five commutator modulo `γ₆`.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The right side of the expanded form of Tahara condition (4.3.13). -/
def condition13ReplacementCoefficient
    (C : Context G) (P : Parameters C.s C.t)
    (i : Fin C.s) (l : Fin C.r) : ℤ :=
  (∑ h ∈ Finset.univ.filter (· < i),
    P.u h i * orderRatio C.d h i * C.alpha h i l) +
  (∑ g ∈ Finset.univ.filter (· ≤ i),
    ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l) +
  (∑ g ∈ Finset.univ.filter (· ≤ i),
    ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
      P.w g h i * C.alpha g h l) +
  (∑ g ∈ Finset.univ.filter (i < ·),
    ∑ h ∈ Finset.univ.filter (g ≤ ·), P.w' i g h * C.alpha g h l)

/-- Condition (4.3.13), rearranged into the form used in formula (27). -/
theorem condition13_rearranged
    (C : Context G) (P : Parameters C.s C.t) (h13 : P.Condition13)
    (i : Fin C.s) (l : Fin C.r) :
    Int.ModEq (orderGCD C.d C.f i l)
      (formula21ThirdCoefficient C P i l)
      (condition13ReplacementCoefficient C P i l) := by
  apply Int.modEq_iff_dvd.mpr
  have hdiv := Int.modEq_zero_iff_dvd.mp (h13 i l)
  have he : condition13ReplacementCoefficient C P i l -
      formula21ThirdCoefficient C P i l = -(
        -(∑ h ∈ Finset.univ.filter (· < i),
          P.u h i * orderRatio C.d h i * C.alpha h i l) +
        (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l) -
        (∑ h ∈ Finset.univ.filter (· < i),
          P.u h i * orderRatio C.d h i * C.c h l) -
        (∑ k, P.v' i k * C.delta k l) -
        (∑ g ∈ Finset.univ.filter (· ≤ i),
          ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l) -
        (∑ g ∈ Finset.univ.filter (· ≤ i),
          ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
            P.w g h i * C.alpha g h l) -
        (∑ g ∈ Finset.univ.filter (i < ·),
          ∑ h ∈ Finset.univ.filter (g ≤ ·), P.w' i g h * C.alpha g h l)) := by
    simp [formula21ThirdCoefficient, condition13ReplacementCoefficient]
    ring
  rw [he]
  exact dvd_neg.mpr hdiv

private theorem formula21_third_base_d_power_vanish
    (C : Context G) (ξ : G) (i : Fin C.s) (l : Fin C.r) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
        orderInt C.d i) 1 := by
  let A := D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hinner : D5.paperComm ξ (C.x3 l) ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      hξ (C.x3_mem_gamma3 l)
  have hpow := D5.paperComm_zpow_right_mod_gamma
    (n := 6) (r := 4) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hinner hx (orderInt C.d i)
  have hleft : D5.paperComm
      (D5.paperComm ξ (C.x3 l)) (C.x1 i ^ orderInt C.d i) ∈
      D5.gamma G 6 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      hinner (C.x1_order_power_mem_gamma2 i)
  exact hpow.symm.trans <| by
    rw [D5.modEq_one_iff_mem]
    simpa [A] using hleft

private theorem formula21_third_base_f_power_vanish
    (C : Context G) (ξ : G) (i : Fin C.s) (l : Fin C.r) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
        orderInt C.f l) 1 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hx : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hpow := nested_weight_three_zpow_right hξ
    (C.x3_mem_gamma3 l) hx (orderInt C.f l)
  have hxf : C.x3 l ^ orderInt C.f l ∈ D5.gamma G 4 :=
    C.x3_order_power l
  have hleft : D5.paperComm
      (D5.paperComm ξ (C.x3 l ^ orderInt C.f l)) (C.x1 i) ∈
      D5.gamma G 6 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hxf) hx
  exact hpow.symm.trans <| by
    rw [D5.modEq_one_iff_mem]
    exact hleft

/-- The common divisor in condition (4.3.13) kills the corresponding
weight-five commutator. -/
theorem formula21_third_base_gcd_power_vanish
    (C : Context G) (ξ : G) (i : Fin C.s) (l : Fin C.r) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
        orderGCD C.d C.f i l) 1 := by
  let A := D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hd := formula21_third_base_d_power_vanish C ξ i l
  have hf := formula21_third_base_f_power_vanish C ξ i l
  have hdq : (A : G ⧸ D5.gamma G 6) ^ C.d i = 1 := by
    change ((A ^ orderInt C.d i : G) : G ⧸ D5.gamma G 6) = 1 at hd
    rw [QuotientGroup.mk_zpow, orderInt, zpow_natCast] at hd
    exact hd
  have hfq : (A : G ⧸ D5.gamma G 6) ^ C.f l = 1 := by
    change ((A ^ orderInt C.f l : G) : G ⧸ D5.gamma G 6) = 1 at hf
    rw [QuotientGroup.mk_zpow, orderInt, zpow_natCast] at hf
    exact hf
  change ((A ^ orderGCD C.d C.f i l : G) : G ⧸ D5.gamma G 6) = 1
  rw [QuotientGroup.mk_zpow, orderGCD, zpow_natCast]
  exact pow_gcd_eq_one _ hdq hfq

/-- Formula (27): condition (4.3.13) may replace the exponent of each
weight-five third-coordinate commutator. -/
theorem formula21_third_exponent_condition13
    (C : Context G) (P : Parameters C.s C.t) (h13 : P.Condition13)
    (ξ : G) (i : Fin C.s) (l : Fin C.r) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
        formula21ThirdCoefficient C P i l)
      (D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
        condition13ReplacementCoefficient C P i l) := by
  let A := D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  let E := formula21ThirdCoefficient C P i l
  let R := condition13ReplacementCoefficient C P i l
  have hmod := condition13_rearranged C P h13 i l
  have hd : orderGCD C.d C.f i l ∣ R - E :=
    Int.modEq_iff_dvd.mp hmod
  have hdiff : D5.ModGammaSix (A ^ (R - E)) 1 :=
    D5.modGammaSix_zpow_eq_one_of_dvd
      (formula21_third_base_gcd_power_vanish C ξ i l) hd
  change ((A ^ E : G) : G ⧸ D5.gamma G 6) =
    ((A ^ R : G) : G ⧸ D5.gamma G 6)
  have hqdiff : ((A ^ (R - E) : G) : G ⧸ D5.gamma G 6) = 1 := hdiff
  rw [QuotientGroup.mk_zpow] at hqdiff
  change (A : G ⧸ D5.gamma G 6) ^ E =
    (A : G ⧸ D5.gamma G 6) ^ R
  calc
    (A : G ⧸ D5.gamma G 6) ^ E =
        (A : G ⧸ D5.gamma G 6) ^ E * 1 := by simp
    _ = (A : G ⧸ D5.gamma G 6) ^ E *
        (A : G ⧸ D5.gamma G 6) ^ (R - E) := by rw [hqdiff]
    _ = (A : G ⧸ D5.gamma G 6) ^ R := by
      rw [← zpow_add]
      congr 1
      ring

/-- The global third-coordinate product after the exponent replacement in
formula (27). -/
def formula27ReplacementGrouped
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProduct fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
      condition13ReplacementCoefficient C P i l

theorem formula27
    (C : Context G) (P : Parameters C.s C.t) (h13 : P.Condition13)
    (ξ : G) :
    D5.ModGammaSix
      (formula21FinalThirdGrouped C P ξ)
      (formula27ReplacementGrouped C P ξ) := by
  unfold formula21FinalThirdGrouped formula27ReplacementGrouped
  apply modEq_orderedProduct
  intro i
  apply modEq_orderedProduct
  intro l
  exact formula21_third_exponent_condition13 C P h13 ξ i l

end

end D5.Tahara
