import D5.Section14

/-!
# Section 15: the remainder `κ` and its collection rules

This file records formula (55), identifies it with the remainder in (54),
and packages every collection and replacement rule listed in formula (56).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Formula (55): the remainder left after Section 14. -/
def kappa
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun i j =>
    D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
      (D5.paperComm (C.x1 j) ξ) ^
        (P.u i j * orderRatio C.d i j)

theorem formula55
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    kappa C P ξ = formula46ThirdProduct C P ξ :=
  rfl

/-- Each unpowered factor in (55) has weight at least five. -/
theorem formula55_factor_mem_gamma5
    (C : Context G) (ξ : G) (i j : Fin C.s) :
    D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d i) ξ)
      (D5.paperComm (C.x1 j) ξ) ∈ D5.gamma G 5 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hleft : D5.paperComm (C.x1 i ^ orderInt C.d i) ξ ∈
      D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (C.x1_order_power_mem_gamma2 i) hξ
  have hright : D5.paperComm (C.x1 j) ξ ∈ D5.gamma G 2 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hj hξ
  exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hleft hright

theorem kappa_mem_gamma5
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    kappa C P ξ ∈ D5.gamma G 5 := by
  unfold kappa strictPairProduct
  apply orderedProduct_mem
  intro i
  apply orderedProductWhere_mem
  intro j hij
  exact (D5.gamma G 5).zpow_mem (formula55_factor_mem_gamma5 C ξ i j) _

/-- Formula (54), with the remaining product named `κ` as in (55). -/
theorem formula54_kappa
    [Finite G] (C : Context G) (P : Parameters C.s C.t)
    (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (D5.paperComm (word C P) ξ) (kappa C P ξ) := by
  simpa [formula55 C P ξ] using formula54 C P hP ξ

/-! ## Formula (56) -/

theorem formula56_mul_left
    {a b c : G}
    (ha : a ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 2)
    (hc : c ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm (a * b) c)
      (D5.paperComm a c * D5.paperComm b c) :=
  D5.paperComm_mul_left_mod_gamma_six ha hb hc

theorem formula56_mul_right
    {a b c : G}
    (ha : a ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 2)
    (hc : c ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm a (b * c))
      (D5.paperComm a b * D5.paperComm a c) :=
  D5.paperComm_mul_right_mod_gamma_six ha hb hc

theorem formula56_zpow
    {a b : G} (ha : a ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 2)
    (v z : ℤ) :
    D5.ModGammaSix (D5.paperComm (a ^ v) (b ^ z))
      (D5.paperComm a b ^ (v * z)) :=
  D5.paperComm_zpow_zpow_mod_gamma_six ha hb v z

/-- Replacing the first `γ₂` argument modulo `γ₄` does not change its
commutator with another `γ₂` element modulo `γ₆`. -/
theorem formula56_replace_left
    {a a' b : G} (haa' : D5.ModEq (D5.gamma G 4) a a')
    (hb : b ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm a b) (D5.paperComm a' b) := by
  simpa using D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 2) (by norm_num) (by norm_num) haa' hb

/-- The symmetric replacement rule for the second argument. -/
theorem formula56_replace_right
    {a b b' : G} (hbb' : D5.ModEq (D5.gamma G 4) b b')
    (ha : a ∈ D5.gamma G 2) :
    D5.ModGammaSix (D5.paperComm a b) (D5.paperComm a b') := by
  simpa using D5.paperComm_right_of_modEq_gamma
    (r := 2) (s := 4) (by norm_num) (by norm_num) hbb' ha

/-- The `γ₄` correction terms created by replacements may be reordered
modulo `γ₆`. -/
theorem formula56_gammaFour_commute
    {a b : G} (ha : a ∈ D5.gamma G 4) (hb : b ∈ D5.gamma G 4) :
    D5.ModGammaSix (a * b) (b * a) :=
  D5.mul_comm_mod_gamma (n := 6) (r := 4) (s := 4)
    (by norm_num) (by norm_num) (by norm_num) ha hb

end

end D5.Tahara
