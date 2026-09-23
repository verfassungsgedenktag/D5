import D5.Formula29
import Mathlib.Data.Int.GCD

/-!
# Section 11: the consequences of conditions (11) and (12)

This file verifies formulas (30)--(36).  The phrase
`γ₂(G)^d γ₃(G)` is represented elementwise by being congruent modulo `γ₃`
to a `d`-th power of an element of `γ₂`.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Elementwise form of membership in `γ₂(G)^d γ₃(G)`. -/
def IsGammaTwoPowerModGammaThree (d : ℤ) (g : G) : Prop :=
  ∃ y ∈ D5.gamma G 2, D5.ModEq (D5.gamma G 3) g (y ^ d)

/-- A power of a second-layer cyclic coordinate whose exponent is divisible
by `gcd(d,e)` is a `d`-th power modulo `γ₃`, provided `x^e ∈ γ₃`.
The witness is the explicit Bezout coefficient. -/
theorem coordinate_zpow_is_gammaTwoPower_mod_gammaThree
    {x : G} {d e : ℕ} {m : ℤ}
    (hxe : x ^ (e : ℤ) ∈ D5.gamma G 3)
    (hm : ((Nat.gcd d e : ℕ) : ℤ) ∣ m) :
    ∃ a : ℤ, D5.ModEq (D5.gamma G 3)
      (x ^ m) (x ^ ((d : ℤ) * a)) := by
  rcases hm with ⟨k, rfl⟩
  let a : ℤ := k * Nat.gcdA d e
  let b : ℤ := k * Nat.gcdB d e
  have hbez : ((Nat.gcd d e : ℕ) : ℤ) =
      (d : ℤ) * Nat.gcdA d e + (e : ℤ) * Nat.gcdB d e :=
    by simpa using Nat.gcd_eq_gcd_ab d e
  refine ⟨a, ?_⟩
  change (x : G ⧸ D5.gamma G 3) ^
      (((Nat.gcd d e : ℕ) : ℤ) * k) =
    (x : G ⧸ D5.gamma G 3) ^ ((d : ℤ) * a)
  have he : (x : G ⧸ D5.gamma G 3) ^ (e : ℤ) = 1 := by
    exact D5.modEq_one_iff_mem.mpr hxe
  calc
    (x : G ⧸ D5.gamma G 3) ^ (((Nat.gcd d e : ℕ) : ℤ) * k) =
        (x : G ⧸ D5.gamma G 3) ^
          (((d : ℤ) * a) + (e : ℤ) * b) := by
            congr 1
            dsimp [a, b]
            rw [hbez]
            ring
    _ = (x : G ⧸ D5.gamma G 3) ^ ((d : ℤ) * a) *
        (x : G ⧸ D5.gamma G 3) ^ ((e : ℤ) * b) := by rw [zpow_add]
    _ = (x : G ⧸ D5.gamma G 3) ^ ((d : ℤ) * a) *
        ((x : G ⧸ D5.gamma G 3) ^ (e : ℤ)) ^ b := by
          congr 1
          rw [zpow_mul]
    _ = (x : G ⧸ D5.gamma G 3) ^ ((d : ℤ) * a) := by
          rw [he, one_zpow, mul_one]

/-- Coordinatewise version of the preceding Bezout calculation. -/
theorem coordinateProduct_is_gammaTwoPower_mod_gammaThree
    (C : Context G) (d : ℕ) (m : Fin C.t → ℤ)
    (hm : ∀ p, ((Nat.gcd d (C.e p) : ℕ) : ℤ) ∣ m p) :
    IsGammaTwoPowerModGammaThree (d : ℤ)
      (orderedProduct fun p => C.x2 p ^ m p) := by
  have hpoint : ∀ p, ∃ a : ℤ, D5.ModEq (D5.gamma G 3)
      (C.x2 p ^ m p) (C.x2 p ^ ((d : ℤ) * a)) := by
    intro p
    exact coordinate_zpow_is_gammaTwoPower_mod_gammaThree
      (C.x2_order_power_mem_gamma3 p) (hm p)
  choose a ha using hpoint
  refine ⟨orderedProduct fun p => C.x2 p ^ a p, ?_, ?_⟩
  · apply orderedProduct_mem
    intro p
    exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _
  · have hall : D5.ModEq (D5.gamma G 3)
        (orderedProduct fun p => C.x2 p ^ m p)
        (orderedProduct fun p => C.x2 p ^ ((d : ℤ) * a p)) := by
      apply modEq_orderedProduct
      intro p
      exact ha p
    exact hall.trans <| by
      simpa using (coordinateProduct_zpow_mod_gamma3 C a (d : ℤ)).symm

/-- A multiple of the order of `x₁h` can be replaced by its second-layer
coordinates modulo `γ₃`. -/
theorem x1_order_multiple_mod_gamma3
    (C : Context G) (h : Fin C.s) (z : ℤ) :
    D5.ModEq (D5.gamma G 3)
      (C.x1 h ^ (orderInt C.d h * z))
      (orderedProduct fun p => C.x2 p ^ (z * C.b h p)) := by
  rw [zpow_mul]
  exact (C.x1_power_mod_gamma3 h).zpow z |>.trans
    (coordinateProduct_zpow_mod_gamma3 C (C.b h) z)

theorem x1_order_multiplesWhere_mod_gamma3
    (C : Context G) {n : ℕ} (q : Fin n → Prop) [DecidablePred q]
    (z : Fin n → ℤ) (x : Fin n → Fin C.s) :
    D5.ModEq (D5.gamma G 3)
      (orderedProductWhere q fun h =>
        C.x1 (x h) ^ (orderInt C.d (x h) * z h))
      (orderedProduct fun p => C.x2 p ^
        (∑ h ∈ Finset.univ.filter q, z h * C.b (x h) p)) := by
  refine (modEq_orderedProductWhere q
    (f := fun h => C.x1 (x h) ^ (orderInt C.d (x h) * z h))
    (g := fun h => orderedProduct fun p =>
      C.x2 p ^ (z h * C.b (x h) p)) ?_).trans ?_
  · intro h hh
    exact x1_order_multiple_mod_gamma3 C (x h) (z h)
  · exact coordinateProductWhere_mod_gamma3 C q
      (fun h p => z h * C.b (x h) p)

/-- The exponent in formula (30). -/
def condition11Coefficient
    (C : Context G) (P : Parameters C.s C.t)
    (j : Fin C.s) (p : Fin C.t) : ℤ :=
  P.v j p * TaharaArithmetic.binom2 (C.d j) -
    (∑ h ∈ Finset.univ.filter (· ≤ j), P.w h j j * C.b h p) -
    (∑ h ∈ Finset.univ.filter (j < ·), P.w'' j j h * C.b h p)

/-- Formula (30), with the paper's three summands exposed under one name. -/
theorem condition11_formula30
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (j : Fin C.s) (p : Fin C.t) :
    Int.ModEq (orderGCD C.d C.e j p)
      (condition11Coefficient C P j p) 0 := by
  simpa [condition11Coefficient] using h11 j p

/-- The exponent in formula (31). -/
def condition12Coefficient
    (C : Context G) (P : Parameters C.s C.t)
    (j k : Fin C.s) (p : Fin C.t) : ℤ :=
  (∑ h ∈ Finset.univ.filter (· ≤ j), P.w h j k * C.b h p) +
    (∑ h ∈ Finset.univ.filter (fun h => j < h ∧ h ≤ k),
      P.w' j h k * C.b h p) +
    (∑ h ∈ Finset.univ.filter (k < ·), P.w'' j k h * C.b h p)

/-- Formula (31). -/
theorem condition12_formula31
    (C : Context G) (P : Parameters C.s C.t) (h12 : P.Condition12)
    {j k : Fin C.s} (hjk : j < k) (p : Fin C.t) :
    Int.ModEq (orderGCD C.d C.e j p)
      (condition12Coefficient C P j k p) 0 := by
  simpa [condition12Coefficient] using h12 j k p hjk

/-- The first-layer word inside formula (32). -/
def formula32FirstLayerWord
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) : G :=
  (orderedProductWhere (· ≤ j) fun h =>
      C.x1 h ^ (orderInt C.d h * P.w h j j)) *
    (orderedProductWhere (j < ·) fun h =>
      C.x1 h ^ (orderInt C.d h * P.w'' j j h))

/-- The complete word displayed in formula (32). -/
def formula32Word
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) : G :=
  (orderedProduct (fun p => C.x2 p ^ P.v j p) ^
      TaharaArithmetic.binom2 (C.d j)) *
    (formula32FirstLayerWord C P j)⁻¹

theorem formula32_firstLayer_coordinates
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) :
    D5.ModEq (D5.gamma G 3) (formula32FirstLayerWord C P j)
      (orderedProduct fun p => C.x2 p ^
        ((∑ h ∈ Finset.univ.filter (· ≤ j), P.w h j j * C.b h p) +
          (∑ h ∈ Finset.univ.filter (j < ·),
            P.w'' j j h * C.b h p))) := by
  let A : Fin C.t → ℤ := fun p =>
    ∑ h ∈ Finset.univ.filter (· ≤ j), P.w h j j * C.b h p
  let B : Fin C.t → ℤ := fun p =>
    ∑ h ∈ Finset.univ.filter (j < ·), P.w'' j j h * C.b h p
  have hlow : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (· ≤ j) fun h =>
        C.x1 h ^ (orderInt C.d h * P.w h j j))
      (orderedProduct fun p => C.x2 p ^ A p) := by
    refine (modEq_orderedProductWhere (· ≤ j)
      (f := fun h => C.x1 h ^ (orderInt C.d h * P.w h j j))
      (g := fun h => orderedProduct fun p =>
        C.x2 p ^ (P.w h j j * C.b h p)) ?_).trans ?_
    · intro h hh
      exact x1_order_multiple_mod_gamma3 C h (P.w h j j)
    · exact coordinateProductWhere_mod_gamma3 C (· ≤ j)
        (fun h p => P.w h j j * C.b h p)
  have hhigh : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (j < ·) fun h =>
        C.x1 h ^ (orderInt C.d h * P.w'' j j h))
      (orderedProduct fun p => C.x2 p ^ B p) := by
    refine (modEq_orderedProductWhere (j < ·)
      (f := fun h => C.x1 h ^ (orderInt C.d h * P.w'' j j h))
      (g := fun h => orderedProduct fun p =>
        C.x2 p ^ (P.w'' j j h * C.b h p)) ?_).trans ?_
    · intro h hh
      exact x1_order_multiple_mod_gamma3 C h (P.w'' j j h)
    · exact coordinateProductWhere_mod_gamma3 C (j < ·)
        (fun h p => P.w'' j j h * C.b h p)
  exact (hlow.mul hhigh).trans <| by
    simpa [A, B] using coordinateProduct_mul_mod_gamma3 C A B

/-- Formula (32): the displayed word belongs elementwise to
`γ₂(G)^{d(j)} γ₃(G)`. -/
theorem formula32
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (j : Fin C.s) :
    IsGammaTwoPowerModGammaThree (orderInt C.d j)
      (formula32Word C P j) := by
  let V : Fin C.t → ℤ := fun p =>
    TaharaArithmetic.binom2 (C.d j) * P.v j p
  let X : Fin C.t → ℤ := fun p =>
    (∑ h ∈ Finset.univ.filter (· ≤ j), P.w h j j * C.b h p) +
    (∑ h ∈ Finset.univ.filter (j < ·), P.w'' j j h * C.b h p)
  let M : Fin C.t → ℤ := fun p => V p - X p
  have hv : D5.ModEq (D5.gamma G 3)
      (orderedProduct (fun p => C.x2 p ^ P.v j p) ^
        TaharaArithmetic.binom2 (C.d j))
      (orderedProduct fun p => C.x2 p ^ V p) := by
    simpa [V, mul_comm] using coordinateProduct_zpow_mod_gamma3 C
      (P.v j) (TaharaArithmetic.binom2 (C.d j))
  have hx := formula32_firstLayer_coordinates C P j
  have hword : D5.ModEq (D5.gamma G 3) (formula32Word C P j)
      (orderedProduct fun p => C.x2 p ^ M p) := by
    refine (hv.mul hx.inv).trans ?_
    have hneg := coordinateProduct_zpow_mod_gamma3 C X (-1)
    have hinv : D5.ModEq (D5.gamma G 3)
        (orderedProduct (fun p => C.x2 p ^ X p))⁻¹
        (orderedProduct fun p => C.x2 p ^ (-X p)) := by
      simpa using hneg
    refine ((D5.ModEq.refl (D5.gamma G 3)
      (orderedProduct fun p => C.x2 p ^ V p)).mul hinv).trans ?_
    simpa [M, sub_eq_add_neg] using
      coordinateProduct_mul_mod_gamma3 C V (fun p => -X p)
  have hm : ∀ p, ((Nat.gcd (C.d j) (C.e p) : ℕ) : ℤ) ∣ M p := by
    intro p
    have hc := Int.modEq_zero_iff_dvd.mp (condition11_formula30 C P h11 j p)
    change ((Nat.gcd (C.d j) (C.e p) : ℕ) : ℤ) ∣
      condition11Coefficient C P j p at hc
    convert hc using 1
    dsimp [M, V, X, condition11Coefficient]
    ring
  rcases coordinateProduct_is_gammaTwoPower_mod_gammaThree C (C.d j) M hm with
    ⟨y, hy, hcoord⟩
  exact ⟨y, hy, hword.trans hcoord⟩

/-- The three first-layer products displayed in formula (33). -/
def formula33Word
    (C : Context G) (P : Parameters C.s C.t)
    (j k : Fin C.s) : G :=
  ((orderedProductWhere (· ≤ j) fun h =>
      C.x1 h ^ (orderInt C.d h * P.w h j k)) *
    (orderedProductWhere (fun h => j < h ∧ h ≤ k) fun h =>
      C.x1 h ^ (orderInt C.d h * P.w' j h k))) *
    (orderedProductWhere (k < ·) fun h =>
      C.x1 h ^ (orderInt C.d h * P.w'' j k h))

theorem formula33_coordinates
    (C : Context G) (P : Parameters C.s C.t)
    (j k : Fin C.s) :
    D5.ModEq (D5.gamma G 3) (formula33Word C P j k)
      (orderedProduct fun p => C.x2 p ^ condition12Coefficient C P j k p) := by
  let A : Fin C.t → ℤ := fun p =>
    ∑ h ∈ Finset.univ.filter (· ≤ j), P.w h j k * C.b h p
  let B : Fin C.t → ℤ := fun p =>
    ∑ h ∈ Finset.univ.filter (fun h => j < h ∧ h ≤ k),
      P.w' j h k * C.b h p
  let E : Fin C.t → ℤ := fun p =>
    ∑ h ∈ Finset.univ.filter (k < ·), P.w'' j k h * C.b h p
  have hA : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (· ≤ j) fun h =>
        C.x1 h ^ (orderInt C.d h * P.w h j k))
      (orderedProduct fun p => C.x2 p ^ A p) := by
    simpa [A] using x1_order_multiplesWhere_mod_gamma3 C (· ≤ j)
      (fun h => P.w h j k) (fun h => h)
  have hB : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (fun h => j < h ∧ h ≤ k) fun h =>
        C.x1 h ^ (orderInt C.d h * P.w' j h k))
      (orderedProduct fun p => C.x2 p ^ B p) := by
    simpa [B] using x1_order_multiplesWhere_mod_gamma3 C
      (fun h => j < h ∧ h ≤ k) (fun h => P.w' j h k) (fun h => h)
  have hE : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (k < ·) fun h =>
        C.x1 h ^ (orderInt C.d h * P.w'' j k h))
      (orderedProduct fun p => C.x2 p ^ E p) := by
    simpa [E] using x1_order_multiplesWhere_mod_gamma3 C (k < ·)
      (fun h => P.w'' j k h) (fun h => h)
  have hAB := coordinateProduct_mul_mod_gamma3 C A B
  have hABE := coordinateProduct_mul_mod_gamma3 C (fun p => A p + B p) E
  exact ((hA.mul hB).mul hE).trans <| by
    simpa [formula33Word, condition12Coefficient, A, B, E] using
      (hAB.mul (D5.ModEq.refl (D5.gamma G 3)
        (orderedProduct fun p => C.x2 p ^ E p))).trans hABE

/-- Formula (33): condition (12) places the three first-layer products in
`γ₂(G)^{d(j)} γ₃(G)`. -/
theorem formula33
    (C : Context G) (P : Parameters C.s C.t) (h12 : P.Condition12)
    {j k : Fin C.s} (hjk : j < k) :
    IsGammaTwoPowerModGammaThree (orderInt C.d j)
      (formula33Word C P j k) := by
  have hm : ∀ p, ((Nat.gcd (C.d j) (C.e p) : ℕ) : ℤ) ∣
      condition12Coefficient C P j k p := by
    intro p
    have hc := Int.modEq_zero_iff_dvd.mp
      (condition12_formula31 C P h12 hjk p)
    simpa [orderGCD] using hc
  rcases coordinateProduct_is_gammaTwoPower_mod_gammaThree C (C.d j)
      (condition12Coefficient C P j k) hm with ⟨y, hy, hcoord⟩
  exact ⟨y, hy, (formula33_coordinates C P j k).trans hcoord⟩

/-- A fourfold commutator vanishes when its second entry is a `d`-th
power modulo `γ₃` and its last entry has `d`-th power in `γ₂`.  This is the
weight argument used in formula (35), with every power transfer explicit. -/
theorem fourfold_second_gammaTwoPower_vanish
    {ξ w x z : G} {d : ℤ}
    (hξ : ξ ∈ D5.gamma G 1) (hx : x ∈ D5.gamma G 1)
    (hz : z ∈ D5.gamma G 1) (hzd : z ^ d ∈ D5.gamma G 2)
    (hw : IsGammaTwoPowerModGammaThree d w) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ w) x) z) 1 := by
  rcases hw with ⟨y, hy, hwy⟩
  have hreplace1 := D5.paperComm_right_of_modEq_gamma
    (r := 1) (s := 3) (by norm_num) (by norm_num) hwy hξ
  have hreplace2 := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hreplace1 hx
  have hreplace3 := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hreplace2 hz
  let q := D5.paperComm ξ y
  let r := D5.paperComm q x
  have hq : q ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hy
  have hr : r ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have hinner : D5.ModEq (D5.gamma G 5)
      (D5.paperComm ξ (y ^ d)) (q ^ d) := by
    simpa [q] using D5.paperComm_zpow_right_mod_gamma
      (n := 5) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hξ hy d
  have hinnerX := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hx
  have hinnerXZ := D5.paperComm_left_of_modEq_gamma
    (r := 6) (s := 1) (by norm_num) (by norm_num) hinnerX hz
  have hinnerXZ6 := hinnerXZ.mono
    (D5.gamma_antitone G (by norm_num : 6 ≤ 7))
  have hmiddle : D5.ModGammaSix
      (D5.paperComm (q ^ d) x) (r ^ d) := by
    simpa [r] using D5.paperComm_zpow_left_mod_gamma
      (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hx d
  have hmiddleZ := D5.paperComm_left_of_modEq_gamma
    (r := 6) (s := 1) (by norm_num) (by norm_num) hmiddle hz
  have hmiddleZ6 := hmiddleZ.mono
    (D5.gamma_antitone G (by norm_num : 6 ≤ 7))
  have houter : D5.ModGammaSix
      (D5.paperComm (r ^ d) z) (D5.paperComm r z ^ d) :=
    D5.paperComm_zpow_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hr hz d
  have hlast : D5.ModGammaSix
      (D5.paperComm r z ^ d) (D5.paperComm r (z ^ d)) :=
    (D5.paperComm_zpow_right_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hr hz d).symm
  have hvanish : D5.ModGammaSix (D5.paperComm r (z ^ d)) 1 := by
    exact D5.modEq_one_iff_mem.mpr <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hr hzd
  exact hreplace3.trans <| hinnerXZ6.trans <| hmiddleZ6.trans <|
    houter.trans <| hlast.trans hvanish

/-- One factor of the product (35). -/
theorem formula35_factor_vanish
    (C : Context G) (P : Parameters C.s C.t) (h12 : P.Condition12)
    (ξ : G) {j k : Fin C.s} (hjk : j < k) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm (D5.paperComm ξ (formula33Word C P j k)) (C.x1 k))
          (C.x1 j)) 1 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxk : C.x1 k ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact fourfold_second_gammaTwoPower_vanish hξ hxk hxj
    (C.x1_order_power_mem_gamma2 j) (formula33 C P h12 hjk)

def formula35Product
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j => orderedProductWhere (j < ·) fun k =>
    D5.paperComm
      (D5.paperComm (D5.paperComm ξ (formula33Word C P j k)) (C.x1 k))
        (C.x1 j)

/-- Formula (35), including the whole strict-pair product. -/
theorem formula35
    (C : Context G) (P : Parameters C.s C.t) (h12 : P.Condition12)
    (ξ : G) : D5.ModGammaSix (formula35Product C P ξ) 1 := by
  have hpoint : D5.ModGammaSix (formula35Product C P ξ)
      (orderedProduct fun _j : Fin C.s => (1 : G)) := by
    unfold formula35Product
    apply modEq_orderedProduct
    intro j
    have hrow : D5.ModGammaSix
        (orderedProductWhere (j < ·) fun k =>
          D5.paperComm
            (D5.paperComm (D5.paperComm ξ (formula33Word C P j k))
              (C.x1 k)) (C.x1 j))
        (orderedProductWhere (j < ·) fun _k : Fin C.s => (1 : G)) := by
      apply modEq_orderedProductWhere
      intro k hjk
      exact formula35_factor_vanish C P h12 ξ hjk
    simpa [orderedProductWhere] using hrow
  exact hpoint.trans <| by
    simpa [orderedProduct] using
      D5.ModEq.refl (D5.gamma G 6) (1 : G)

/-! ## The diagonal correction, formula (36) -/

/-- Multilinearity in the second entry of a commutator of total weight five. -/
theorem fourfold_second_mul_mod_gamma_six
    {ξ a b x z : G}
    (hξ : ξ ∈ D5.gamma G 1) (ha : a ∈ D5.gamma G 2)
    (hb : b ∈ D5.gamma G 2) (hx : x ∈ D5.gamma G 1)
    (hz : z ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ (a * b)) x) z)
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a) x) z *
        D5.paperComm (D5.paperComm (D5.paperComm ξ b) x) z) := by
  let qa := D5.paperComm ξ a
  let qb := D5.paperComm ξ b
  let ra := D5.paperComm qa x
  let rb := D5.paperComm qb x
  have hqa : qa ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha
  have hqb : qb ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hb
  have hra : ra ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hqa hx
  have hrb : rb ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hqb hx
  have hinner : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ξ (a * b)) (qa * qb) := by
    simpa [qa, qb] using D5.paperComm_mul_right_mod_gamma
      (n := 4) (r := 1) (s := 2) (t := 2)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hξ ha hb
  have hinnerX := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hinner hx
  have hsplitX : D5.ModEq (D5.gamma G 5)
      (D5.paperComm (qa * qb) x) (ra * rb) := by
    simpa [ra, rb] using D5.paperComm_mul_left_mod_gamma
      (n := 5) (r := 3) (s := 3) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hqa hqb hx
  have htoX := hinnerX.trans hsplitX
  have htoXZ := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) htoX hz
  have hsplitZ : D5.ModGammaSix
      (D5.paperComm (ra * rb) z)
      (D5.paperComm ra z * D5.paperComm rb z) := by
    simpa using D5.paperComm_mul_left_mod_gamma
      (n := 6) (r := 4) (s := 4) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hra hrb hz
  simpa [qa, qb, ra, rb] using htoXZ.trans hsplitZ

/-- Inversion in the second entry at total weight five. -/
theorem fourfold_second_inv_mod_gamma_six
    {ξ a x z : G}
    (hξ : ξ ∈ D5.gamma G 1) (ha : a ∈ D5.gamma G 2)
    (hx : x ∈ D5.gamma G 1) (hz : z ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a⁻¹) x) z)
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a) x) z)⁻¹ := by
  let q := D5.paperComm ξ a
  let r := D5.paperComm q x
  have hq : q ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha
  have hr : r ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have hinner : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ξ a⁻¹) q⁻¹ := by
    simpa [q] using D5.paperComm_inv_right_mod_gamma
      (n := 4) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hξ ha
  have hinnerX := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hinner hx
  have hinvX : D5.ModEq (D5.gamma G 5)
      (D5.paperComm q⁻¹ x) r⁻¹ := by
    simpa [r] using D5.paperComm_inv_left_mod_gamma
      (n := 5) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hx
  have htoX := hinnerX.trans hinvX
  have htoXZ := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) htoX hz
  have hinvZ : D5.ModGammaSix
      (D5.paperComm r⁻¹ z) (D5.paperComm r z)⁻¹ := by
    simpa using D5.paperComm_inv_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hr hz
  simpa [q, r] using htoXZ.trans hinvZ

/-- Integer powers in the second entry at total weight five. -/
theorem fourfold_second_zpow_mod_gamma_six
    {ξ a x z : G}
    (hξ : ξ ∈ D5.gamma G 1) (ha : a ∈ D5.gamma G 2)
    (hx : x ∈ D5.gamma G 1) (hz : z ∈ D5.gamma G 1) (m : ℤ) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ (a ^ m)) x) z)
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a) x) z ^ m) := by
  let q := D5.paperComm ξ a
  let r := D5.paperComm q x
  have hq : q ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha
  have hr : r ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have hinner : D5.ModEq (D5.gamma G 4)
      (D5.paperComm ξ (a ^ m)) (q ^ m) := by
    simpa [q] using D5.paperComm_zpow_right_mod_gamma
      (n := 4) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hξ ha m
  have hinnerX := D5.paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hinner hx
  have hpowX : D5.ModEq (D5.gamma G 5)
      (D5.paperComm (q ^ m) x) (r ^ m) := by
    simpa [r] using D5.paperComm_zpow_left_mod_gamma
      (n := 5) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hx m
  have htoX := hinnerX.trans hpowX
  have htoXZ := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) htoX hz
  have hpowZ : D5.ModGammaSix
      (D5.paperComm (r ^ m) z) (D5.paperComm r z ^ m) := by
    simpa using D5.paperComm_zpow_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hr hz m
  simpa [q, r] using htoXZ.trans hpowZ

/-- A multiple of `d` kills the weight-five commutator when the last
entry has its `d`-th power in `γ₂`. -/
theorem fourfold_last_entry_power_vanish
    {ξ a x z : G} {d : ℤ}
    (hξ : ξ ∈ D5.gamma G 1) (ha : a ∈ D5.gamma G 2)
    (hx : x ∈ D5.gamma G 1) (hz : z ∈ D5.gamma G 1)
    (hzd : z ^ d ∈ D5.gamma G 2) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a) x) z ^ d) 1 := by
  let r := D5.paperComm (D5.paperComm ξ a) x
  have hq : D5.paperComm ξ a ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha
  have hr : r ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have htransfer := D5.paperComm_zpow_right_mod_gamma
    (n := 6) (r := 4) (s := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr hz d
  exact htransfer.symm.trans <| D5.modEq_one_iff_mem.mpr <|
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hr hzd

theorem formula32FirstLayerWord_mem_gamma2
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) :
    formula32FirstLayerWord C P j ∈ D5.gamma G 2 := by
  apply (D5.gamma G 2).mul_mem
  · apply orderedProductWhere_mem
    intro h hh
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _
  · apply orderedProductWhere_mem
    intro h hh
    rw [zpow_mul]
    exact (D5.gamma G 2).zpow_mem (C.x1_order_power_mem_gamma2 h) _

/-- The positive-exponent second-layer word occurring in (32) and (36). -/
def formula32WeightTwoWord
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) : G :=
  orderedProduct fun p => C.x2 p ^ P.v j p

theorem formula32WeightTwoWord_mem_gamma2
    (C : Context G) (P : Parameters C.s C.t) (j : Fin C.s) :
    formula32WeightTwoWord C P j ∈ D5.gamma G 2 := by
  apply orderedProduct_mem
  intro p
  exact (D5.gamma G 2).zpow_mem (C.x2_mem_gamma2 p) _

/-- The pointwise congruence in the first line of formula (36). -/
theorem formula36_factor_congruent
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (ξ : G) (j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (formula32FirstLayerWord C P j)) (C.x1 j))
          (C.x1 j) ^ (2 : ℤ))
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (formula32WeightTwoWord C P j)) (C.x1 j))
          (C.x1 j) ^ (2 * TaharaArithmetic.binom2 (C.d j))) := by
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
      (F (B ^ TaharaArithmetic.binom2 (C.d j) * A⁻¹)) 1 := by
    exact fourfold_second_gammaTwoPower_vanish hξ hx hx
      (C.x1_order_power_mem_gamma2 j) hw
  have hsplit := fourfold_second_mul_mod_gamma_six hξ
    ((D5.gamma G 2).zpow_mem hB (TaharaArithmetic.binom2 (C.d j)))
    ((D5.gamma G 2).inv_mem hA) hx hx
  have hBpow := fourfold_second_zpow_mod_gamma_six hξ hB hx hx
    (TaharaArithmetic.binom2 (C.d j))
  have hAinv := fourfold_second_inv_mod_gamma_six hξ hA hx hx
  have hprod : D5.ModGammaSix
      (F B ^ TaharaArithmetic.binom2 (C.d j) * (F A)⁻¹) 1 := by
    have hsplit' : D5.ModGammaSix
        (F (B ^ TaharaArithmetic.binom2 (C.d j) * A⁻¹))
        (F B ^ TaharaArithmetic.binom2 (C.d j) * (F A)⁻¹) := by
      simpa [F] using hsplit.trans (hBpow.mul hAinv)
    exact hsplit'.symm.trans hvanish
  have hbase : D5.ModGammaSix (F A)
      (F B ^ TaharaArithmetic.binom2 (C.d j)) := by
    change (F A : G ⧸ D5.gamma G 6) =
      (F B ^ TaharaArithmetic.binom2 (C.d j) : G ⧸ D5.gamma G 6)
    change (F B ^ TaharaArithmetic.binom2 (C.d j) * (F A)⁻¹ :
      G ⧸ D5.gamma G 6) = 1 at hprod
    have heq : (F B ^ TaharaArithmetic.binom2 (C.d j) :
        G ⧸ D5.gamma G 6) = (F A : G ⧸ D5.gamma G 6) := by
      have h := congrArg (fun q : G ⧸ D5.gamma G 6 => q * (F A : G ⧸ D5.gamma G 6)) hprod
      simpa [mul_assoc] using h
    exact heq.symm
  have hsq := hbase.zpow 2
  change D5.ModGammaSix (F A ^ (2 : ℤ))
    (F B ^ (2 * TaharaArithmetic.binom2 (C.d j)))
  have heq : (F B ^ TaharaArithmetic.binom2 (C.d j)) ^ (2 : ℤ) =
      F B ^ (2 * TaharaArithmetic.binom2 (C.d j)) := by
    rw [← zpow_mul]
    congr 1
    ring
  rw [← heq]
  exact hsq

/-- Each factor on the middle line of (36) vanishes. -/
theorem formula36_middle_factor_vanish
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (j : Fin C.s) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm
        (D5.paperComm ξ (formula32WeightTwoWord C P j)) (C.x1 j))
          (C.x1 j) ^ (2 * TaharaArithmetic.binom2 (C.d j))) 1 := by
  let F := D5.paperComm (D5.paperComm
    (D5.paperComm ξ (formula32WeightTwoWord C P j)) (C.x1 j)) (C.x1 j)
  have hd : D5.ModGammaSix (F ^ orderInt C.d j) 1 := by
    exact fourfold_last_entry_power_vanish
      (by simp [D5.gamma]) (formula32WeightTwoWord_mem_gamma2 C P j)
      (by simp [D5.gamma]) (by simp [D5.gamma])
      (C.x1_order_power_mem_gamma2 j)
  apply D5.modGammaSix_zpow_eq_one_of_dvd hd
  refine ⟨((C.d j - 1 : ℕ) : ℤ), ?_⟩
  simpa [orderInt, mul_assoc] using
    TaharaArithmetic.two_mul_binom2 (C.d j)

def formula36LeftProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (formula32FirstLayerWord C P j)) (C.x1 j))
        (C.x1 j) ^ (2 : ℤ)

def formula36MiddleProduct
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun j =>
    D5.paperComm (D5.paperComm
      (D5.paperComm ξ (formula32WeightTwoWord C P j)) (C.x1 j))
        (C.x1 j) ^ (2 * TaharaArithmetic.binom2 (C.d j))

/-- Formula (36), including both displayed congruences and all indices. -/
theorem formula36
    (C : Context G) (P : Parameters C.s C.t) (h11 : P.Condition11)
    (ξ : G) :
    D5.ModGammaSix (formula36LeftProduct C P ξ)
      (formula36MiddleProduct C P ξ) ∧
    D5.ModGammaSix (formula36MiddleProduct C P ξ) 1 := by
  constructor
  · unfold formula36LeftProduct formula36MiddleProduct
    apply modEq_orderedProduct
    intro j
    exact formula36_factor_congruent C P h11 ξ j
  · unfold formula36MiddleProduct
    have hpoint : D5.ModGammaSix
        (orderedProduct fun j =>
          D5.paperComm (D5.paperComm
            (D5.paperComm ξ (formula32WeightTwoWord C P j)) (C.x1 j))
              (C.x1 j) ^ (2 * TaharaArithmetic.binom2 (C.d j)))
        (orderedProduct fun _j : Fin C.s => (1 : G)) := by
      apply modEq_orderedProduct
      intro j
      exact formula36_middle_factor_vanish C P ξ j
    exact hpoint.trans <| by
      simpa [orderedProduct] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)

/-! ## Local Jacobi transformations for formula (34) -/

/-- The second Jacobi identity printed after formula (36).  This is the
local transformation used for every `w' i j k` in formula (34). -/
theorem formula34_wprime_jacobi
    {a b ξ c : G}
    (ha : a ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 1)
    (hξ : ξ ∈ D5.gamma G 1) (hc : c ∈ D5.gamma G 1) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c)⁻¹
      (D5.paperComm (D5.paperComm (D5.paperComm ξ a) b) c *
        (D5.paperComm (D5.paperComm (D5.paperComm ξ b) a) c)⁻¹) := by
  let A := D5.paperComm (D5.paperComm ξ a) b
  let B := D5.paperComm (D5.paperComm ξ b) a
  have hA : A ∈ D5.gamma G 4 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ ha) hb
  have hB : B ∈ D5.gamma G 4 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hb) ha
  have hAc : D5.paperComm A c ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hc
  have hBc : D5.paperComm B c ∈ D5.gamma G 5 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hB hc
  have hrot := D5.rotation_main_mod_gamma_five ha hb hξ
  have hlift := D5.paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hrot hc
  have hsplit : D5.ModGammaSix
      (D5.paperComm (A⁻¹ * B) c)
      (D5.paperComm A⁻¹ c * D5.paperComm B c) := by
    have hAi : A⁻¹ ∈ D5.gamma G 4 := (D5.gamma G 4).inv_mem hA
    simpa using D5.paperComm_mul_left_mod_gamma
      (n := 6) (r := 4) (s := 4) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hAi hB hc
  have hinv : D5.ModGammaSix
      (D5.paperComm A⁻¹ c) (D5.paperComm A c)⁻¹ := by
    exact D5.paperComm_inv_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hA hc
  have hmain : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c)
      ((D5.paperComm A c)⁻¹ * D5.paperComm B c) := by
    simpa [A, B] using hlift.trans (hsplit.trans <|
      hinv.mul (D5.ModEq.refl (D5.gamma G 6) (D5.paperComm B c)))
  have hinverted : D5.ModGammaSix
      (D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) c)⁻¹
      ((D5.paperComm B c)⁻¹ * D5.paperComm A c) := by
    simpa using hmain.inv
  have hcomm : D5.ModGammaSix
      ((D5.paperComm B c)⁻¹ * D5.paperComm A c)
      (D5.paperComm A c * (D5.paperComm B c)⁻¹) :=
    D5.mul_comm_mod_gamma (n := 6) (r := 5) (s := 5)
      (by norm_num) (by norm_num) (by norm_num)
      ((D5.gamma G 5).inv_mem hBc) hAc
  simpa [A, B] using hinverted.trans hcomm

end

end D5.Tahara
