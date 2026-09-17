import D5.CollectionWeighted
import D5.TaharaArithmetic

/-!
# Truncated Hall--Petresco formulas

This file develops the power collection needed for the six-factor transfer
in formula (20).  The first theorem collects `[a,b^n]` through weight five
when `a` has weight two and `b` has weight one.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

private theorem commute_in_gamma_quotient
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : n ≤ r + s)
    {x y : G} (hx : x ∈ gamma G r) (hy : y ∈ gamma G s) :
    Commute ((x : G ⧸ gamma G n)) (y : G ⧸ gamma G n) := by
  show (x : G ⧸ gamma G n) * y = y * x
  exact mul_comm_mod_gamma (n := n) hr hs hrs hx hy

private theorem mul_zpow_mod_gamma
    {n r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hrs : n ≤ r + s)
    {x y : G} (hx : x ∈ gamma G r) (hy : y ∈ gamma G s) (z : ℤ) :
    ModEq (gamma G n) ((x * y) ^ z) (x ^ z * y ^ z) := by
  change (((x * y) ^ z : G) : G ⧸ gamma G n) =
    ((x ^ z * y ^ z : G) : G ⧸ gamma G n)
  rw [QuotientGroup.mk_zpow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
  exact (commute_in_gamma_quotient (n := n) hr hs hrs hx hy).mul_zpow z

private theorem binom2_succ (n : ℕ) :
    TaharaArithmetic.binom2 (n + 1) =
      (n : ℤ) + TaharaArithmetic.binom2 n := by
  simp [TaharaArithmetic.binom2, Nat.choose_succ_succ]

private theorem binom3_succ (n : ℕ) :
    TaharaArithmetic.binom3 (n + 1) =
      TaharaArithmetic.binom2 n + TaharaArithmetic.binom3 n := by
  simp [TaharaArithmetic.binom2, TaharaArithmetic.binom3,
    Nat.choose_succ_succ, Nat.add_comm]

/-- Hall--Petresco collection of a power in the second argument.  Terms of
weight `r + 4` and above are discarded. -/
theorem paperComm_zpow_right_hallPetresco_of_weight
    {r : ℕ} (hr : 1 ≤ r) {a b : G} (ha : a ∈ gamma G r)
    (hb : b ∈ gamma G 1) (n : ℕ) :
    ModEq (gamma G (r + 4)) (paperComm a (b ^ (n : ℤ)))
      (paperComm a b ^ (n : ℤ) *
        paperComm (paperComm a b) b ^ TaharaArithmetic.binom2 n *
        paperComm (paperComm (paperComm a b) b) b ^
          TaharaArithmetic.binom3 n) := by
  let c := paperComm a b
  let d := paperComm c b
  let e := paperComm d b
  have hc : c ∈ gamma G (r + 1) :=
    paperComm_mem_gamma_add hr (by norm_num) ha hb
  have hd : d ∈ gamma G (r + 2) := by
    change paperComm c b ∈ gamma G (r + 2)
    simpa [Nat.add_assoc] using
      paperComm_mem_gamma_add (Nat.le_add_right_of_le hr) (by norm_num) hc hb
  have he : e ∈ gamma G (r + 3) := by
    change paperComm d b ∈ gamma G (r + 3)
    simpa [Nat.add_assoc] using
      paperComm_mem_gamma_add (Nat.le_add_right_of_le hr) (by norm_num) hd hb
  induction n with
  | zero =>
      simpa [paperComm_eq, TaharaArithmetic.binom2,
        TaharaArithmetic.binom3] using ModEq.refl (gamma G (r + 4)) (1 : G)
  | succ n ih =>
      have hpow : b ^ ((n + 1 : ℕ) : ℤ) = b ^ (n : ℤ) * b := by
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega, zpow_add_one]
      have hstart : ModEq (gamma G (r + 4))
          (paperComm a (b ^ ((n + 1 : ℕ) : ℤ)))
          (c * conjugateBy
            (c ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n *
              e ^ TaharaArithmetic.binom3 n) b) := by
        rw [hpow, paperComm_mul_right]
        exact (ModEq.refl (gamma G (r + 4)) c).mul
          (ih.conjugateBy (ModEq.refl (gamma G (r + 4)) b))
      have heConj : ModEq (gamma G (r + 4)) (conjugateBy e b) e :=
        conjugateBy_mod_gamma (n := r + 4) (r := r + 3) (s := 1)
          (Nat.le_add_right_of_le hr) (by norm_num) (by omega) he hb
      have hconj : ModEq (gamma G (r + 4))
          (conjugateBy
            (c ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n *
              e ^ TaharaArithmetic.binom3 n) b)
          ((c * d) ^ (n : ℤ) *
            (d * e) ^ TaharaArithmetic.binom2 n *
            e ^ TaharaArithmetic.binom3 n) := by
        rw [conjugateBy_mul, conjugateBy_mul,
          conjugateBy_zpow, conjugateBy_zpow, conjugateBy_zpow,
          conjugateBy_eq_mul_paperComm, conjugateBy_eq_mul_paperComm]
        exact ((ModEq.refl (gamma G (r + 4)) ((c * d) ^ (n : ℤ))).mul
          (ModEq.refl (gamma G (r + 4))
            ((d * e) ^ TaharaArithmetic.binom2 n))).mul
            (heConj.zpow (TaharaArithmetic.binom3 n))
      have hcd := mul_zpow_mod_gamma (n := r + 4) (r := r + 1) (s := r + 2)
        (Nat.le_add_right_of_le hr) (Nat.le_add_right_of_le hr)
          (by omega) hc hd (n : ℤ)
      have hde := mul_zpow_mod_gamma (n := r + 4) (r := r + 2) (s := r + 3)
        (Nat.le_add_right_of_le hr) (Nat.le_add_right_of_le hr)
          (by omega) hd he
          (TaharaArithmetic.binom2 n)
      have hexpand : ModEq (gamma G (r + 4))
          ((c * d) ^ (n : ℤ) * (d * e) ^ TaharaArithmetic.binom2 n *
            e ^ TaharaArithmetic.binom3 n)
          ((c ^ (n : ℤ) * d ^ (n : ℤ)) *
            (d ^ TaharaArithmetic.binom2 n *
              e ^ TaharaArithmetic.binom2 n) *
            e ^ TaharaArithmetic.binom3 n) :=
        (hcd.mul hde).mul
          (ModEq.refl (gamma G (r + 4)) (e ^ TaharaArithmetic.binom3 n))
      have halgebra :
          c * ((c ^ (n : ℤ) * d ^ (n : ℤ)) *
            (d ^ TaharaArithmetic.binom2 n *
              e ^ TaharaArithmetic.binom2 n) *
            e ^ TaharaArithmetic.binom3 n) =
          c ^ ((n + 1 : ℕ) : ℤ) *
            d ^ TaharaArithmetic.binom2 (n + 1) *
            e ^ TaharaArithmetic.binom3 (n + 1) := by
        rw [binom2_succ, binom3_succ]
        rw [show ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) by omega,
          zpow_add, zpow_add, zpow_add]
        simp only [zpow_one]
        group
      exact hstart.trans <|
        ((ModEq.refl (gamma G (r + 4)) c).mul (hconj.trans hexpand)).trans <| by
          rw [halgebra]

/-- The weight `(2,1)` specialization used for `[γ₂,G]` in formula (20). -/
theorem paperComm_zpow_right_hallPetresco
    {a b : G} (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 1) (n : ℕ) :
    ModGammaSix (paperComm a (b ^ (n : ℤ)))
      (paperComm a b ^ (n : ℤ) *
        paperComm (paperComm a b) b ^ TaharaArithmetic.binom2 n *
        paperComm (paperComm (paperComm a b) b) b ^
          TaharaArithmetic.binom3 n) := by
  simpa using paperComm_zpow_right_hallPetresco_of_weight
    (r := 2) (by norm_num) ha hb n

/-- The weight `(1,1)` specialization, one level earlier in formula (20). -/
theorem paperComm_zpow_right_hallPetresco_mod_gamma_five
    {a b : G} (ha : a ∈ gamma G 1) (hb : b ∈ gamma G 1) (n : ℕ) :
    ModEq (gamma G 5) (paperComm a (b ^ (n : ℤ)))
      (paperComm a b ^ (n : ℤ) *
        paperComm (paperComm a b) b ^ TaharaArithmetic.binom2 n *
        paperComm (paperComm (paperComm a b) b) b ^
          TaharaArithmetic.binom3 n) := by
  simpa using paperComm_zpow_right_hallPetresco_of_weight
    (r := 1) (by norm_num) ha hb n

/-- The two-term collection of a power in the first argument needed in
formula (20).  The omitted next commutator has weight seven. -/
theorem paperComm_zpow_left_hallPetresco_weight_two
    {a b : G} (ha : a ∈ gamma G 2) (hb : b ∈ gamma G 1) (n : ℕ) :
    ModGammaSix (paperComm (a ^ (n : ℤ)) b)
      (paperComm a b ^ (n : ℤ) *
        paperComm (paperComm a b) a ^ TaharaArithmetic.binom2 n) := by
  let c := paperComm a b
  let d := paperComm c a
  have hc : c ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb
  have hd : d ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hc ha
  induction n with
  | zero =>
      simpa [paperComm_eq, TaharaArithmetic.binom2] using
        ModEq.refl (gamma G 6) (1 : G)
  | succ n ih =>
      have hpow : a ^ ((n + 1 : ℕ) : ℤ) = a ^ (n : ℤ) * a := by
        rw [show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega, zpow_add_one]
      have hstart : ModGammaSix
          (paperComm (a ^ ((n + 1 : ℕ) : ℤ)) b)
          (conjugateBy
            (c ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) a * c) := by
        rw [hpow, paperComm_mul_left]
        exact (ih.conjugateBy (ModEq.refl (gamma G 6) a)).mul
          (ModEq.refl (gamma G 6) c)
      have hdConj : ModGammaSix (conjugateBy d a) d :=
        conjugateBy_mod_gamma (n := 6) (r := 5) (s := 2)
          (by norm_num) (by norm_num) (by norm_num) hd ha
      have hconj : ModGammaSix
          (conjugateBy (c ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) a)
          ((c * d) ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) := by
        rw [conjugateBy_mul, conjugateBy_zpow, conjugateBy_zpow,
          conjugateBy_eq_mul_paperComm]
        exact (ModEq.refl (gamma G 6) ((c * d) ^ (n : ℤ))).mul
          (hdConj.zpow (TaharaArithmetic.binom2 n))
      have hcd := mul_zpow_mod_gamma (n := 6) (r := 3) (s := 5)
        (by norm_num) (by norm_num) (by norm_num) hc hd (n : ℤ)
      have hdpow : d ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n ∈ gamma G 5 :=
        (gamma G 5).mul_mem ((gamma G 5).zpow_mem hd (n : ℤ))
          ((gamma G 5).zpow_mem hd (TaharaArithmetic.binom2 n))
      have hswap : ModGammaSix
          ((d ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) * c)
          (c * (d ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n)) :=
        mul_comm_mod_gamma (n := 6) (r := 5) (s := 3)
          (by norm_num) (by norm_num) (by norm_num) hdpow hc
      have hcollect : ModGammaSix
          (((c * d) ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) * c)
          (c ^ (n : ℤ) *
            (c * (d ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n))) := by
        exact ((hcd.mul
          (ModEq.refl (gamma G 6) (d ^ TaharaArithmetic.binom2 n))).mul
          (ModEq.refl (gamma G 6) c)).trans <| by
            simpa only [mul_assoc] using
              (ModEq.refl (gamma G 6) (c ^ (n : ℤ))).mul hswap
      have hfinish :
          c ^ (n : ℤ) *
              (c * (d ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n)) =
            c ^ ((n + 1 : ℕ) : ℤ) *
              d ^ TaharaArithmetic.binom2 (n + 1) := by
        rw [binom2_succ,
          show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 by omega,
          zpow_add, zpow_add]
        simp only [zpow_one]
        group
      exact hstart.trans <| (hconj.mul
        (ModEq.refl (gamma G 6) c)).trans <| hcollect.trans <| by
          rw [hfinish]

end

end D5
