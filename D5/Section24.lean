import D5.Section23

/-!
# Section 24: diagonal and strict-pair cancellations

This file proves formulas (88)--(90).  The square sum at the end of (87)
is partitioned exactly into its diagonal and two strict-pair orientations.
The diagonal is removed with (78), and the two orientations are combined
with (79), using only the cyclic-order divisibilities from (82).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The inner product of the two corrected coordinate coefficients occurring
in formulas (87)--(90). -/
def formula88Term
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) : ℤ :=
  ∑ i, formula68Coefficient C ξ i l *
    formula69Coefficient C P ξ i m

/-- The positive double sum whose negative is the last line of (87). -/
def formula88Positive
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ l, ∑ m, sCoord C B l a * sCoord C B m b *
    formula88Term C P ξ l m

def formula88Diagonal
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ l, sCoord C B l a * sCoord C B l b *
    formula88Term C P ξ l l

def formula88Upper
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ l, ∑ m ∈ Finset.univ.filter (l < ·),
    sCoord C B l a * sCoord C B m b * formula88Term C P ξ l m

def formula88Lower
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ l, ∑ m ∈ Finset.univ.filter (l < ·),
    sCoord C B m a * sCoord C B l b * formula88Term C P ξ m l

/-- Formula (88): exact partition of the square sum. -/
theorem formula88
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) :
    formula88Positive C B P ξ a b =
      formula88Diagonal C B P ξ a b +
        formula88Upper C B P ξ a b + formula88Lower C B P ξ a b := by
  have hpartition := sum_square_partition
    (fun l m => sCoord C B l a * sCoord C B m b *
      formula88Term C P ξ l m)
  rw [formula88Positive, formula88Diagonal, formula88Upper,
    formula88Lower]
  rw [hpartition]
  simp_rw [Finset.sum_add_distrib]
  ring

theorem formula88Term_self
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l : Fin C.r) :
    formula88Term C P ξ l l = formula78Left C P ξ l := by
  rfl

theorem formula88Term_pair
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) :
    formula88Term C P ξ l m + formula88Term C P ξ m l =
      formula79Left C P ξ l m := by
  unfold formula88Term formula79Left formula68Coefficient
    formula67Coefficient formula69Coefficient
  rw [← Finset.sum_add_distrib]

/-- Integer form of invariant-factor monotonicity. -/
theorem formula80_orderInt_dvd
    (B : GammaTwoFourBasis G) {a b : Fin B.n} (hab : a < b) :
    orderInt B.order a ∣ orderInt B.order b := by
  rcases B.order_dvd a b hab.le with ⟨q, hq⟩
  refine ⟨(q : ℤ), ?_⟩
  change (B.order b : ℤ) = (B.order a : ℤ) * (q : ℤ)
  exact_mod_cast hq

/-- The diagonal line of (88) is zero modulo `n(a)`. -/
theorem formula88_diagonal_dvd
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G)
    (a b : Fin B.n) :
    orderInt B.order a ∣ formula88Diagonal C B P ξ a b := by
  unfold formula88Diagonal
  apply Finset.dvd_sum
  intro l hl
  rcases formula78 C P hP ξ l with ⟨q, hq⟩
  have hbase := formula82 C B l a
  have hmul := dvd_mul_of_dvd_left hbase (sCoord C B l b * q)
  convert hmul using 1
  rw [formula88Term_self, hq]
  ring

/-- Divisibility statement underlying formula (89). -/
theorem formula89_pair_dvd
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G)
    {a b : Fin B.n} (hab : a < b)
    {l m : Fin C.r} (hlm : l < m) :
    orderInt B.order a ∣
      sCoord C B m a * sCoord C B l b *
        (formula88Term C P ξ l m + formula88Term C P ξ m l) := by
  rcases formula79 C P hP ξ hlm with ⟨q, hq⟩
  have hnab := formula80_orderInt_dvd B hab
  have hbase : orderInt B.order a ∣
      orderInt C.f l * sCoord C B l b :=
    dvd_trans hnab (formula82 C B l b)
  have hmul := dvd_mul_of_dvd_left hbase (sCoord C B m a * q)
  convert hmul using 1
  rw [formula88Term_pair, hq]
  ring

/-- Formula (89). -/
theorem formula89
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G)
    {a b : Fin B.n} (hab : a < b)
    {l m : Fin C.r} (hlm : l < m) :
    Int.ModEq (orderInt B.order a)
      (sCoord C B m a * sCoord C B l b * formula88Term C P ξ m l)
      (-sCoord C B m a * sCoord C B l b * formula88Term C P ξ l m) := by
  rw [Int.modEq_iff_dvd]
  have h := formula89_pair_dvd C B P hP ξ hab hlm
  convert dvd_neg.mpr h using 1
  ring

/-- The positive strict-pair expression retained after formulas (78)--(79)
have removed the diagonal and combined the two orientations. -/
def formula90Positive
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  ∑ l, ∑ m ∈ Finset.univ.filter (l < ·),
    (sCoord C B l a * sCoord C B m b -
      sCoord C B m a * sCoord C B l b) * formula88Term C P ξ l m

/-- The right side of formula (90), with the sign inherited from (87). -/
def formula90Right
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) : ℤ :=
  -formula90Positive C B P ξ a b

theorem formula90_positive_difference
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) :
    formula90Positive C B P ξ a b - formula88Positive C B P ξ a b =
      -formula88Diagonal C B P ξ a b -
        ∑ l, ∑ m ∈ Finset.univ.filter (l < ·),
          sCoord C B m a * sCoord C B l b *
            (formula88Term C P ξ l m + formula88Term C P ξ m l) := by
  rw [formula88 C B P ξ a b]
  unfold formula90Positive formula88Upper formula88Lower
  simp only [sub_mul, mul_add, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

theorem formula90_positive_congruence
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G)
    {a b : Fin B.n} (hab : a < b) :
    Int.ModEq (orderInt B.order a)
      (formula88Positive C B P ξ a b) (formula90Positive C B P ξ a b) := by
  rw [Int.modEq_iff_dvd, formula90_positive_difference]
  apply dvd_sub
  · exact dvd_neg.mpr (formula88_diagonal_dvd C B P hP ξ a b)
  · apply Finset.dvd_sum
    intro l hl
    apply Finset.dvd_sum
    intro m hm
    exact formula89_pair_dvd C B P hP ξ hab
      (Finset.mem_filter.mp hm).2

theorem formula87Third_eq_neg_formula88Positive
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (a b : Fin B.n) :
    formula87Third C B P ξ a b = -formula88Positive C B P ξ a b := by
  rfl

/-- Formula (90). -/
theorem formula90
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G)
    {a b : Fin B.n} (hab : a < b) :
    Int.ModEq (orderInt B.order a)
      (formula85Exponent C B P ξ a b) (formula90Right C B P ξ a b) := by
  have h87 := formula87 C B P hP ξ hab
  have htoThird : Int.ModEq (orderInt B.order a)
      (formula85Exponent C B P ξ a b) (formula87Third C B P ξ a b) := by
    rw [h87.1]
    exact h87.2.1.trans h87.2.2
  have hreduce := formula90_positive_congruence C B P hP ξ hab
  have hneg : Int.ModEq (orderInt B.order a)
      (-formula88Positive C B P ξ a b) (formula90Right C B P ξ a b) := by
    simpa [formula90Right] using hreduce.neg
  rw [formula87Third_eq_neg_formula88Positive] at htoThird
  exact htoThird.trans hneg

end

end D5.Tahara
