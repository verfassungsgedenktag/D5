import D5.Section21

/-!
# Section 22: cyclic coordinates in `γ₂(G) / γ₄(G)`

The existence of an invariant-factor cyclic basis is isolated as the
standard finite-abelian-group input.  Once that basis is fixed, formulas
(81)--(84), including all coordinate comparisons, are proved below.
-/

namespace D5.Tahara

universe u

/-- The invariant-factor data selected in formula (80). -/
structure GammaTwoFourBasis (G : Type u) [Group G] where
  n : ℕ
  y : Fin n → G
  order : Fin n → ℕ
  basis : IsCyclicBasis (D5.gamma G 2) (D5.gamma G 4) y order
  order_dvd : ∀ a b, a ≤ b → order a ∣ order b
  y_order_power : ∀ a, y a ^ orderInt order a ∈ D5.gamma G 4

end D5.Tahara

namespace D5.Background

/-- Standard invariant-factor theorem for the finite abelian quotient
`γ₂(G) / γ₄(G)`.  This is the sole new background input in Section 22. -/
axiom gammaTwoFourBasis_exists
    (G : Type u) [Group G] [Finite G] :
    Nonempty (D5.Tahara.GammaTwoFourBasis G)

end D5.Background

namespace D5.Tahara

noncomputable section

variable {G : Type u} [Group G]

namespace GammaTwoFourBasis

/-- A fixed basis supplied by the accepted finite abelian structure
theorem. -/
noncomputable def chosen (G : Type u) [Group G] [Finite G] :
    GammaTwoFourBasis G :=
  Classical.choice (D5.Background.gammaTwoFourBasis_exists G)

/-- Finite groups have the data required in formula (80). -/
theorem formula80_finite (G : Type u) [Group G] [Finite G] :
    Nonempty (GammaTwoFourBasis G) :=
  D5.Background.gammaTwoFourBasis_exists G

/-- Formula (80), in the unique-normal-form representation used throughout
the formalization. -/
theorem formula80 (B : GammaTwoFourBasis G) :
    IsCyclicBasis (D5.gamma G 2) (D5.gamma G 4) B.y B.order :=
  B.basis

theorem formula80_order_dvd (B : GammaTwoFourBasis G)
    {a b : Fin B.n} (hab : a < b) : B.order a ∣ B.order b :=
  B.order_dvd a b hab.le

theorem formula80_order_power (B : GammaTwoFourBasis G) (a : Fin B.n) :
    B.y a ^ orderInt B.order a ∈ D5.gamma G 4 :=
  B.y_order_power a

theorem order_gt_one (B : GammaTwoFourBasis G) (a : Fin B.n) :
    1 < B.order a :=
  B.basis.2.2.1 a

/-- Canonical coordinates in the basis of formula (80). -/
noncomputable def coordinates
    (B : GammaTwoFourBasis G) (g : G) (hg : g ∈ D5.gamma G 2) :
    ∀ a, Fin (B.order a) :=
  Classical.choose (B.basis.2.2.2 g hg)

theorem coordinates_spec
    (B : GammaTwoFourBasis G) (g : G) (hg : g ∈ D5.gamma G 2) :
    D5.ModEq (D5.gamma G 4) g
      (orderedProduct fun a => B.y a ^ (B.coordinates g hg a).val) :=
  (Classical.choose_spec (B.basis.2.2.2 g hg)).1

/-- An integer-coordinate word lying in `γ₄` has every coordinate divisible
by the corresponding invariant factor. -/
theorem coordinate_dvd_of_product_mem
    (B : GammaTwoFourBasis G) (c : Fin B.n → ℤ)
    (hc : orderedProduct (fun a => B.y a ^ c a) ∈ D5.gamma G 4)
    (a : Fin B.n) : orderInt B.order a ∣ c a := by
  let rem : ∀ b, Fin (B.order b) := fun b =>
    ⟨Int.natMod (c b) (orderInt B.order b),
      Int.natMod_lt (Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (B.order_gt_one b)))⟩
  let zero : ∀ b, Fin (B.order b) := fun b =>
    ⟨0, lt_trans Nat.zero_lt_one (B.order_gt_one b)⟩
  have hreduce : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun b => B.y b ^ c b)
      (orderedProduct fun b => B.y b ^ (rem b).val) := by
    apply modEq_orderedProduct
    intro b
    let n : ℤ := orderInt B.order b
    let q : ℤ := c b / n
    have hn : n ≠ 0 := by
      dsimp [n, orderInt]
      exact_mod_cast Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (B.order_gt_one b))
    have hceq : c b = n * q + c b % n := by
      simpa [q] using (Int.mul_ediv_add_emod (c b) n).symm
    have hrem : ((rem b).val : ℤ) = c b % n := by
      dsimp [rem, Int.natMod]
      exact Int.toNat_of_nonneg (Int.emod_nonneg _ hn)
    have hperiod : D5.ModEq (D5.gamma G 4)
        ((B.y b ^ n) ^ q) 1 := by
      apply D5.modEq_one_iff_mem.mpr
      exact (D5.gamma G 4).zpow_mem
        (by simpa [n] using B.y_order_power b) q
    rw [hceq, zpow_add, zpow_mul]
    rw [← zpow_natCast, hrem]
    simpa using hperiod.mul
      (D5.ModEq.refl (D5.gamma G 4) (B.y b ^ (c b % n)))
  have hres : D5.ModEq (D5.gamma G 4) 1
      (orderedProduct fun b => B.y b ^ (rem b).val) :=
    (D5.modEq_one_iff_mem.mpr hc).symm.trans hreduce
  have hzero : D5.ModEq (D5.gamma G 4) 1
      (orderedProduct fun b => B.y b ^ (zero b).val) := by
    simpa [orderedProduct, zero] using
      D5.ModEq.refl (D5.gamma G 4) (1 : G)
  obtain ⟨normal, hnormal, hunique⟩ :=
    B.basis.2.2.2 (1 : G) (by simp)
  have hremEq : rem = normal := hunique rem hres
  have hzeroEq : zero = normal := hunique zero hzero
  have hcoord : rem a = zero a := by rw [hremEq, hzeroEq]
  have hmod : c a % orderInt B.order a = 0 := by
    have hv := congrArg (fun z => (z.val : ℤ)) hcoord
    dsimp [rem, zero, Int.natMod] at hv
    have hn : orderInt B.order a ≠ 0 := by
      dsimp [orderInt]
      exact_mod_cast Nat.ne_of_gt (lt_trans Nat.zero_lt_one
        (B.order_gt_one a))
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hn)] at hv
    exact hv
  exact Int.dvd_iff_emod_eq_zero.mpr hmod

private theorem quotient_coe_orderedProduct_gamma4
    {k : ℕ} (z : Fin k → G) :
    ((orderedProduct z : G) : G ⧸ D5.gamma G 4) =
      orderedProduct (fun i => (z i : G ⧸ D5.gamma G 4)) := by
  unfold orderedProduct
  induction List.finRange k with
  | nil => simp
  | cons i is ih => simp [ih]

private theorem quotient_coe_orderedProductWhere_gamma4
    {k : ℕ} (q : Fin k → Prop) [DecidablePred q] (z : Fin k → G) :
    ((orderedProductWhere q z : G) : G ⧸ D5.gamma G 4) =
      orderedProductWhere q (fun i => (z i : G ⧸ D5.gamma G 4)) := by
  unfold orderedProductWhere
  induction (List.finRange k).filter q with
  | nil => simp
  | cons i is ih => simp [ih]

private theorem quotient_pairwise_commute
    (B : GammaTwoFourBasis G) (a b : Fin B.n) :
    Commute ((B.y a : G ⧸ D5.gamma G 4)) (B.y b) := by
  show (B.y a : G ⧸ D5.gamma G 4) * B.y b =
    B.y b * B.y a
  exact D5.mul_comm_mod_gamma (n := 4) (r := 2) (s := 2)
    (by norm_num) (by norm_num) (by norm_num)
    (B.basis.1 a) (B.basis.1 b)

/-- Powers of a coordinate word are taken coordinatewise modulo `γ₄`. -/
theorem coordinateProduct_zpow
    (B : GammaTwoFourBasis G) (c : Fin B.n → ℤ) (z : ℤ) :
    D5.ModEq (D5.gamma G 4)
      ((orderedProduct fun a => B.y a ^ c a) ^ z)
      (orderedProduct fun a => B.y a ^ (z * c a)) := by
  change
    ((((orderedProduct fun a => B.y a ^ c a) ^ z : G) :
        G ⧸ D5.gamma G 4)) = _
  rw [QuotientGroup.mk_zpow, quotient_coe_orderedProduct_gamma4,
    quotient_coe_orderedProduct_gamma4]
  simp_rw [QuotientGroup.mk_zpow]
  simpa [zpow_mul] using orderedProduct_zpow_of_pairwise_commute
    (fun a => (B.y a : G ⧸ D5.gamma G 4))
    (quotient_pairwise_commute B) c z

/-- Collect a finite family of coordinate words. -/
theorem coordinateProducts_collect
    (B : GammaTwoFourBasis G) {k : ℕ}
    (c : Fin k → Fin B.n → ℤ) :
    D5.ModEq (D5.gamma G 4)
      (orderedProduct fun i => orderedProduct fun a => B.y a ^ c i a)
      (orderedProduct fun a => B.y a ^ (∑ i, c i a)) := by
  change
    ((orderedProduct (fun i => orderedProduct fun a => B.y a ^ c i a) : G) :
        G ⧸ D5.gamma G 4) = _
  rw [quotient_coe_orderedProduct_gamma4,
    quotient_coe_orderedProduct_gamma4]
  simp_rw [quotient_coe_orderedProduct_gamma4, QuotientGroup.mk_zpow]
  exact orderedProduct_coordinates_of_pairwise_commute
    (fun a => (B.y a : G ⧸ D5.gamma G 4))
    (quotient_pairwise_commute B) c

/-- Collect a filtered family of coordinate words. -/
theorem coordinateProductsWhere_collect
    (B : GammaTwoFourBasis G) {k : ℕ}
    (q : Fin k → Prop) [DecidablePred q]
    (c : Fin k → Fin B.n → ℤ) :
    D5.ModEq (D5.gamma G 4)
      (orderedProductWhere q fun i =>
        orderedProduct fun a => B.y a ^ c i a)
      (orderedProduct fun a => B.y a ^
        (∑ i ∈ Finset.univ.filter q, c i a)) := by
  change
    ((orderedProductWhere q (fun i =>
      orderedProduct fun a => B.y a ^ c i a) : G) :
        G ⧸ D5.gamma G 4) = _
  rw [quotient_coe_orderedProductWhere_gamma4,
    quotient_coe_orderedProduct_gamma4]
  simp_rw [quotient_coe_orderedProduct_gamma4, QuotientGroup.mk_zpow]
  exact orderedProductWhere_coordinates_of_pairwise_commute
    (fun a => (B.y a : G ⧸ D5.gamma G 4))
    (quotient_pairwise_commute B) q c

/-- Two coordinate words add their exponents modulo `γ₄`. -/
theorem coordinateProduct_mul
    (B : GammaTwoFourBasis G) (c e : Fin B.n → ℤ) :
    D5.ModEq (D5.gamma G 4)
      (orderedProduct (fun a => B.y a ^ c a) *
        orderedProduct (fun a => B.y a ^ e a))
      (orderedProduct fun a => B.y a ^ (c a + e a)) := by
  change
    (((orderedProduct (fun a => B.y a ^ c a) *
      orderedProduct (fun a => B.y a ^ e a) : G) :
        G ⧸ D5.gamma G 4)) = _
  rw [QuotientGroup.mk_mul, quotient_coe_orderedProduct_gamma4,
    quotient_coe_orderedProduct_gamma4,
    quotient_coe_orderedProduct_gamma4]
  exact orderedProduct_mul_of_pairwise_commute
    (fun a => (B.y a : G ⧸ D5.gamma G 4))
    (quotient_pairwise_commute B) c e

/-- Congruent coordinate words have congruent integer coordinates. -/
theorem coordinate_modEq_of_words
    (B : GammaTwoFourBasis G) (c e : Fin B.n → ℤ)
    (h : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun a => B.y a ^ c a)
      (orderedProduct fun a => B.y a ^ e a))
    (a : Fin B.n) : Int.ModEq (orderInt B.order a) (c a) (e a) := by
  let Cw := orderedProduct fun b => B.y b ^ c b
  let Ew := orderedProduct fun b => B.y b ^ e b
  have hquot : D5.ModEq (D5.gamma G 4) (Cw * Ew ^ (-1 : ℤ)) 1 := by
    have hz := h.mul ((D5.ModEq.refl (D5.gamma G 4) Ew).zpow (-1 : ℤ))
    simpa [Cw, Ew] using hz
  have hinv := coordinateProduct_zpow B e (-1)
  have hcollect := coordinateProduct_mul B c (fun b => -e b)
  have hword : orderedProduct (fun b => B.y b ^ (c b - e b)) ∈
      D5.gamma G 4 := by
    apply D5.modEq_one_iff_mem.mp
    have hce : D5.ModEq (D5.gamma G 4)
        (Cw * Ew ^ (-1 : ℤ))
        (orderedProduct fun b => B.y b ^ (c b - e b)) := by
      have h := (D5.ModEq.refl (D5.gamma G 4) Cw).mul hinv
      exact h.trans <| by
        simpa [Cw] using hcollect
    exact hce.symm.trans hquot
  apply Int.modEq_iff_dvd.mpr
  rcases B.coordinate_dvd_of_product_mem
      (fun b => c b - e b) hword a with ⟨q, hq⟩
  refine ⟨-q, ?_⟩
  calc
    e a - c a = -(c a - e a) := by ring
    _ = -(orderInt B.order a * q) := by rw [hq]
    _ = orderInt B.order a * (-q) := by ring

end GammaTwoFourBasis

theorem formula81_first_mem_gamma2
    (C : Context G) (ξ : G) (i : Fin C.s) :
    D5.paperComm (C.x1 i) ξ ∈ D5.gamma G 2 := by
  have hi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hi hξ

theorem formula81_second_mem_gamma2
    (C : Context G) (l : Fin C.r) : C.x3 l ∈ D5.gamma G 2 :=
  D5.gamma_antitone G (by norm_num) (C.x3_mem_gamma3 l)

/-- The integer coordinates `r(i,a)` from formula (81). -/
def rCoord
    (C : Context G) (B : GammaTwoFourBasis G) (ξ : G)
    (i : Fin C.s) (a : Fin B.n) : ℤ :=
  (B.coordinates (D5.paperComm (C.x1 i) ξ)
    (formula81_first_mem_gamma2 C ξ i) a).val

/-- The integer coordinates `s(l,a)` from formula (81). -/
def sCoord
    (C : Context G) (B : GammaTwoFourBasis G)
    (l : Fin C.r) (a : Fin B.n) : ℤ :=
  (B.coordinates (C.x3 l) (formula81_second_mem_gamma2 C l) a).val

/-- First congruence in formula (81). -/
theorem formula81_first
    (C : Context G) (B : GammaTwoFourBasis G) (ξ : G)
    (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (D5.paperComm (C.x1 i) ξ)
      (orderedProduct fun a => B.y a ^ rCoord C B ξ i a) := by
  simpa [rCoord] using B.coordinates_spec
    (D5.paperComm (C.x1 i) ξ) (formula81_first_mem_gamma2 C ξ i)

/-- Second congruence in formula (81). -/
theorem formula81_second
    (C : Context G) (B : GammaTwoFourBasis G) (l : Fin C.r) :
    D5.ModEq (D5.gamma G 4) (C.x3 l)
      (orderedProduct fun a => B.y a ^ sCoord C B l a) := by
  simpa [sCoord] using B.coordinates_spec
    (C.x3 l) (formula81_second_mem_gamma2 C l)

/-- Replace an arbitrary `x₃` coordinate word by its `y` coordinates. -/
theorem x3Product_to_gammaTwoFourCoordinates
    (C : Context G) (B : GammaTwoFourBasis G)
    (c : Fin C.r → ℤ) :
    D5.ModEq (D5.gamma G 4)
      (orderedProduct fun l => C.x3 l ^ c l)
      (orderedProduct fun a => B.y a ^
        (∑ l, c l * sCoord C B l a)) := by
  have hlocal : D5.ModEq (D5.gamma G 4)
      (orderedProduct fun l => C.x3 l ^ c l)
      (orderedProduct fun l =>
        orderedProduct fun a => B.y a ^ (c l * sCoord C B l a)) := by
    apply modEq_orderedProduct
    intro l
    exact (formula81_second C B l).zpow (c l) |>.trans
      (B.coordinateProduct_zpow (sCoord C B l) (c l))
  exact hlocal.trans <| B.coordinateProducts_collect
    (fun l a => c l * sCoord C B l a)

/-- Formula (82). -/
theorem formula82
    (C : Context G) (B : GammaTwoFourBasis G)
    (l : Fin C.r) (a : Fin B.n) :
    orderInt B.order a ∣ orderInt C.f l * sCoord C B l a := by
  have hxpow : C.x3 l ^ orderInt C.f l ∈ D5.gamma G 4 :=
    C.x3_order_power l
  have hcoordPow :
      orderedProduct (fun b => B.y b ^
        (orderInt C.f l * sCoord C B l b)) ∈ D5.gamma G 4 := by
    have h81pow := (formula81_second C B l).zpow (orderInt C.f l)
    have hprodPow :
        (orderedProduct fun b => B.y b ^ sCoord C B l b) ^
            orderInt C.f l ∈ D5.gamma G 4 :=
      D5.mem_of_modEq_of_le le_rfl h81pow.symm hxpow
    exact D5.mem_of_modEq_of_le le_rfl
      (B.coordinateProduct_zpow (sCoord C B l) (orderInt C.f l)).symm
      hprodPow
  exact B.coordinate_dvd_of_product_mem
    (fun b => orderInt C.f l * sCoord C B l b) hcoordPow a

/-- Formula (83). -/
theorem formula83
    (C : Context G) (B : GammaTwoFourBasis G) (ξ : G)
    (i : Fin C.s) (a : Fin B.n) :
    Int.ModEq (orderInt B.order a)
      (orderInt C.d i * rCoord C B ξ i a)
      (∑ l,
        ((∑ p, C.b i p * lambda C ξ p l) -
          TaharaArithmetic.binom2 (C.d i) * eta C ξ i l) *
            sCoord C B l a) := by
  have hleft : D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 i) ξ ^ orderInt C.d i)
      (orderedProduct fun b => B.y b ^
        (orderInt C.d i * rCoord C B ξ i b)) :=
    (formula81_first C B ξ i).zpow (orderInt C.d i) |>.trans
      (B.coordinateProduct_zpow (rCoord C B ξ i) (orderInt C.d i))
  have hright : D5.ModEq (D5.gamma G 4)
      (D5.paperComm (C.x1 i) ξ ^ orderInt C.d i)
      (orderedProduct fun b => B.y b ^
        (∑ l, formula68Coefficient C ξ i l * sCoord C B l b)) :=
    (formula68 C ξ i).trans
      (x3Product_to_gammaTwoFourCoordinates C B
        (formula68Coefficient C ξ i))
  have hwords := hleft.symm.trans hright
  simpa [formula68Coefficient, formula67Coefficient] using
    B.coordinate_modEq_of_words
      (fun b => orderInt C.d i * rCoord C B ξ i b)
      (fun b => ∑ l, formula68Coefficient C ξ i l * sCoord C B l b)
      hwords a

/-- The complete coordinate on the left side of formula (84). -/
def formula84Coefficient
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G)
    (i : Fin C.s) (a : Fin B.n) : ℤ :=
  (∑ j ∈ Finset.univ.filter (i < ·),
      P.u i j * orderInt C.d j * rCoord C B ξ j a) -
    (∑ h ∈ Finset.univ.filter (· < i),
      P.u h i * orderInt C.d i * rCoord C B ξ h a) +
    orderInt C.d i *
      (∑ l,
        ((∑ p, P.v i p * lambda C ξ p l) +
          (∑ j ∈ Finset.univ.filter (i < ·),
            P.w i j j * eta C ξ j l) +
          (∑ h ∈ Finset.univ.filter (· < i),
            P.w'' h h i * eta C ξ h l)) * sCoord C B l a)

/-- Coordinate expansion of the full left side of (62), used in (84). -/
theorem formula84_coordinates
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 4) (formula62Left C P ξ i)
      (orderedProduct fun a => B.y a ^ formula84Coefficient C B P ξ i a) := by
  let H : Fin B.n → ℤ := fun a =>
    ∑ j ∈ Finset.univ.filter (i < ·),
      (P.u i j * orderInt C.d j) * rCoord C B ξ j a
  let L : Fin B.n → ℤ := fun a =>
    ∑ h ∈ Finset.univ.filter (· < i),
      (-P.u h i * orderInt C.d i) * rCoord C B ξ h a
  let R : Fin B.n → ℤ := fun a =>
    orderInt C.d i *
      (∑ l, formula69Coefficient C P ξ i l * sCoord C B l a)
  have hhighLocal : D5.ModEq (D5.gamma G 4)
      (formula62High C P ξ i)
      (orderedProductWhere (i < ·) fun j =>
        orderedProduct fun a => B.y a ^
          ((P.u i j * orderInt C.d j) * rCoord C B ξ j a)) := by
    unfold formula62High
    apply modEq_orderedProductWhere
    intro j hij
    exact (formula81_first C B ξ j).zpow
      (P.u i j * orderInt C.d j) |>.trans
        (B.coordinateProduct_zpow (rCoord C B ξ j)
          (P.u i j * orderInt C.d j))
  have hhigh : D5.ModEq (D5.gamma G 4)
      (formula62High C P ξ i)
      (orderedProduct fun a => B.y a ^ H a) := by
    exact hhighLocal.trans <| by
      simpa [H] using B.coordinateProductsWhere_collect (i < ·)
        (fun j a => (P.u i j * orderInt C.d j) * rCoord C B ξ j a)
  have hlowLocal : D5.ModEq (D5.gamma G 4)
      (formula62Low C P ξ i)
      (orderedProductWhere (· < i) fun h =>
        orderedProduct fun a => B.y a ^
          ((-P.u h i * orderInt C.d i) * rCoord C B ξ h a)) := by
    unfold formula62Low
    apply modEq_orderedProductWhere
    intro h hhi
    exact (formula81_first C B ξ h).zpow
      (-P.u h i * orderInt C.d i) |>.trans
        (B.coordinateProduct_zpow (rCoord C B ξ h)
          (-P.u h i * orderInt C.d i))
  have hlow : D5.ModEq (D5.gamma G 4)
      (formula62Low C P ξ i)
      (orderedProduct fun a => B.y a ^ L a) := by
    exact hlowLocal.trans <| by
      simpa [L] using B.coordinateProductsWhere_collect (· < i)
        (fun h a => (-P.u h i * orderInt C.d i) * rCoord C B ξ h a)
  have hinnerBase : D5.ModEq (D5.gamma G 4)
      (formula62Inner C P ξ i)
      (orderedProduct fun a => B.y a ^
        (∑ l, formula69Coefficient C P ξ i l * sCoord C B l a)) :=
    (formula69 C P ξ i).trans <|
      x3Product_to_gammaTwoFourCoordinates C B
        (formula69Coefficient C P ξ i)
  have hinner : D5.ModEq (D5.gamma G 4)
      (formula62Inner C P ξ i ^ orderInt C.d i)
      (orderedProduct fun a => B.y a ^ R a) := by
    exact (hinnerBase.zpow (orderInt C.d i)).trans <| by
      simpa [R] using B.coordinateProduct_zpow
        (fun a => ∑ l,
          formula69Coefficient C P ξ i l * sCoord C B l a)
        (orderInt C.d i)
  have hparts : D5.ModEq (D5.gamma G 4) (formula62Left C P ξ i)
      ((orderedProduct fun a => B.y a ^ H a) *
        (orderedProduct fun a => B.y a ^ L a) *
        (orderedProduct fun a => B.y a ^ R a)) := by
    simpa [formula62Left, mul_assoc] using (hhigh.mul hlow).mul hinner
  have hcollectHL := B.coordinateProduct_mul H L
  have hcollectR := B.coordinateProduct_mul (fun a => H a + L a) R
  have hcollect : D5.ModEq (D5.gamma G 4)
      ((orderedProduct fun a => B.y a ^ H a) *
        (orderedProduct fun a => B.y a ^ L a) *
        (orderedProduct fun a => B.y a ^ R a))
      (orderedProduct fun a => B.y a ^ ((H a + L a) + R a)) :=
    (hcollectHL.mul (D5.ModEq.refl (D5.gamma G 4) _)).trans hcollectR
  refine hparts.trans (hcollect.trans ?_)
  apply modEq_orderedProduct
  intro a
  congr 1
  dsimp [H, L, R, formula84Coefficient, formula69Coefficient]
  have hLneg :
      (∑ h ∈ Finset.univ.filter (· < i),
        (-P.u h i * orderInt C.d i) * rCoord C B ξ h a) =
        -(∑ h ∈ Finset.univ.filter (· < i),
          P.u h i * orderInt C.d i * rCoord C B ξ h a) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro h hh
    ring
  rw [hLneg]
  congr 1

/-- Formula (84). -/
theorem formula84
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (i : Fin C.s) (a : Fin B.n) :
    Int.ModEq (orderInt B.order a) (formula84Coefficient C B P ξ i a) 0 := by
  have hzero := formula62 C P hP ξ i
  have hcoords := formula84_coordinates C B P ξ i
  have hmem : orderedProduct
      (fun b => B.y b ^ formula84Coefficient C B P ξ i b) ∈
      D5.gamma G 4 :=
    D5.modEq_one_iff_mem.mp (hcoords.symm.trans hzero)
  exact Int.modEq_zero_iff_dvd.mpr
    (B.coordinate_dvd_of_product_mem
      (formula84Coefficient C B P ξ i) hmem a)

end

end D5.Tahara
