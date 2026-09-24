import D5.Section24

/-!
# Section 25: return to commutator products and `κ ≡ 1`

Formula (91) expands `[x₃ₗ,x₃ₘ]` in the cyclic coordinates selected in
Section 22.  Formula (90), the coordinate periods from (86), and a checked
exchange of two finite strict-pair products then identify `κ` with a product
of commutators of weight three.  Every such commutator lies in `γ₆`, which
proves formula (92).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

private def strictPairList (n : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n) ×ˢ (List.finRange n)).filter fun ij => ij.1 < ij.2

private theorem listProd_product
    {I J : Type*} (is : List I) (js : List J) (f : I → J → G) :
    (is.map fun i => (js.map fun j => f i j).prod).prod =
      ((is ×ˢ js).map fun ij => f ij.1 ij.2).prod := by
  induction is with
  | nil => simp
  | cons i is ih =>
      simp only [List.map_cons, List.prod_cons, List.product_cons,
        List.map_append, List.prod_append, ih]
      congr 1
      simp only [List.map_map]
      rfl

private theorem listProd_product_filtered
    {I J : Type*} (is : List I) (js : List J)
    (p : I → J → Prop) [DecidableRel p] (g : I → J → G) :
    (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
      (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
        fun ij => g ij.1 ij.2).prod := by
  induction is with
  | nil => simp
  | cons i is ih =>
      rw [List.map_cons, List.prod_cons, List.product_cons,
        List.filter_append, List.map_append, List.prod_append, ih]
      congr 1
      simp only [List.filter_map, List.map_map]
      rfl

theorem strictPairProduct_eq_strictPairList
    {n : ℕ} (f : Fin n → Fin n → G) :
    strictPairProduct f =
      ((strictPairList n).map fun ij => f ij.1 ij.2).prod := by
  simpa [strictPairProduct, orderedProduct, orderedProductWhere,
    strictPairList] using listProd_product_filtered
      (List.finRange n) (List.finRange n)
      (fun (i : Fin n) (j : Fin n) => i < j) f

/-- Exchange two independent strict-pair loops in the abelian layer
`γ₃(G)/γ₆(G)`. -/
theorem strictPairProduct_strictPairProduct_swap_gammaThree
    {s n : ℕ} (f : Fin s → Fin s → Fin n → Fin n → G)
    (hf : ∀ i j a b, i < j → a < b → f i j a b ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (strictPairProduct fun i j => strictPairProduct fun a b => f i j a b)
      (strictPairProduct fun a b => strictPairProduct fun i j => f i j a b) := by
  let is := strictPairList s
  let as := strictPairList n
  let rows := is ×ˢ as
  let cols := (as ×ˢ is).map fun z => (z.2, z.1)
  have his : is.Nodup := by
    exact ((List.nodup_finRange s).product (List.nodup_finRange s)).filter _
  have has : as.Nodup := by
    exact ((List.nodup_finRange n).product (List.nodup_finRange n)).filter _
  have hswap : Function.Injective
      (fun z : (Fin n × Fin n) × (Fin s × Fin s) => (z.2, z.1)) := by
    intro x y h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hrows : rows.Nodup := his.product has
  have hcols : cols.Nodup := (has.product his).map hswap
  have hpairs : rows.Perm cols := by
    apply (List.perm_ext_iff_of_nodup hrows hcols).2
    intro z
    change z ∈ is ×ˢ as ↔
      z ∈ (as ×ˢ is).map (fun w => (w.2, w.1))
    constructor
    · intro hz
      rcases List.mem_product.mp hz with ⟨hi, ha⟩
      exact List.mem_map.mpr ⟨(z.2, z.1),
        List.mem_product.mpr ⟨ha, hi⟩, by simp⟩
    · intro hz
      rcases List.mem_map.mp hz with ⟨w, hw, hswapEq⟩
      rcases List.mem_product.mp hw with ⟨ha, hi⟩
      subst z
      exact List.mem_product.mpr ⟨hi, ha⟩
  rw [strictPairProduct_eq_strictPairList]
  simp_rw [strictPairProduct_eq_strictPairList]
  rw [listProd_product]
  rw [listProd_product]
  have hmod : D5.ModGammaSix
      ((rows.map fun z => f z.1.1 z.1.2 z.2.1 z.2.2).prod)
      ((cols.map fun z => f z.1.1 z.1.2 z.2.1 z.2.2).prod) := by
    apply D5.listProd_perm_gammaThree (hpairs.map _)
    intro x hx
    rcases List.mem_map.mp hx with ⟨z, hz, rfl⟩
    have hi : z.1.1 < z.1.2 := by
      exact of_decide_eq_true (List.mem_filter.mp (List.mem_product.mp hz).1).2
    have ha : z.2.1 < z.2.2 := by
      exact of_decide_eq_true (List.mem_filter.mp (List.mem_product.mp hz).2).2
    exact hf z.1.1 z.1.2 z.2.1 z.2.2 hi ha
  simpa [rows, cols, List.map_map] using hmod

/-- Distribute a power through a strict-pair product of weight-three
factors. -/
theorem strictPairProduct_zpow_gammaThree
    {n : ℕ} (f : Fin n → Fin n → G)
    (hf : ∀ a b, a < b → f a b ∈ D5.gamma G 3) (z : ℤ) :
    D5.ModGammaSix (strictPairProduct f ^ z)
      (strictPairProduct fun a b => f a b ^ z) := by
  let R : Fin n → G := fun a => orderedProductWhere (a < ·) (f a)
  have hR : ∀ a, R a ∈ D5.gamma G 3 := by
    intro a
    apply orderedProductWhere_mem
    intro b hab
    exact hf a b hab
  have houter := D5.orderedProduct_zpow_gammaThree R hR z
  have hinner : D5.ModGammaSix
      (orderedProduct fun a => R a ^ z)
      (orderedProduct fun a => orderedProductWhere (a < ·)
        fun b => f a b ^ z) := by
    apply modEq_orderedProduct
    intro a
    exact orderedProductWhere_zpow_gammaThree (a < ·) (f a) (hf a) z
  simpa [strictPairProduct, R] using houter.trans hinner

/-- Collect a strict-pair family of powers of one fixed group element. -/
theorem strictPairProduct_zpow_same_base
    {n : ℕ} (x : G) (e : Fin n → Fin n → ℤ) :
    strictPairProduct (fun a b => x ^ e a b) =
      x ^ (∑ a, ∑ b ∈ Finset.univ.filter (a < ·), e a b) := by
  unfold strictPairProduct
  simp_rw [D5.orderedProductWhere_zpow_same_base]
  exact D5.orderedProduct_zpow_same_base x
    (fun a => ∑ b ∈ Finset.univ.filter (a < ·), e a b)

/-- Collapse a full square of coordinate commutators to its strict upper
triangle. -/
theorem coordinateCommSquare_to_strictPairs
    (B : GammaTwoFourBasis G) (A E : Fin B.n → ℤ) :
    D5.ModGammaSix
      (orderedProduct fun a => orderedProduct fun b =>
        D5.paperComm (B.y a) (B.y b) ^ (A a * E b))
      (strictPairProduct fun a b =>
        D5.paperComm (B.y a) (B.y b) ^ (A a * E b - A b * E a)) := by
  let K : Fin B.n → Fin B.n → G := fun a b =>
    D5.paperComm (B.y a) (B.y b)
  let F : Fin B.n → Fin B.n → G := fun a b => K a b ^ (A a * E b)
  have hF : ∀ a b, F a b ∈ D5.gamma G 3 := by
    intro a b
    apply (D5.gamma G 3).zpow_mem
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (B.basis.1 a) (B.basis.1 b)
  have hpartition := orderedProduct_square_partition_gammaThree F hF
  have hdiag : D5.ModGammaSix (orderedProduct fun a => F a a) 1 := by
    have hpoint : D5.ModGammaSix (orderedProduct fun a => F a a)
        (orderedProduct fun _a : Fin B.n => (1 : G)) := by
      apply modEq_orderedProduct
      intro a
      simpa [F, K, D5.paperComm_eq] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)
    exact hpoint.trans <| by
      simpa [orderedProduct] using D5.ModEq.refl (D5.gamma G 6) (1 : G)
  have hpairs : D5.ModGammaSix
      (strictPairProduct F * strictPairProduct fun a b => F b a)
      (strictPairProduct fun a b =>
        K a b ^ (A a * E b - A b * E a)) := by
    have hcombine := strictPairProduct_pointwise_gammaThree F
      (fun a b => F b a) (fun a b hab => hF a b)
      (fun a b hab => hF b a)
    refine hcombine.trans ?_
    unfold strictPairProduct
    apply modEq_orderedProduct
    intro a
    apply modEq_orderedProductWhere
    intro b hab
    have heq : F a b * F b a =
        K a b ^ (A a * E b - A b * E a) := by
      dsimp [F, K]
      rw [D5.paperComm_swap (B.y a) (B.y b), inv_zpow,
        ← zpow_neg, ← zpow_add, ← sub_eq_add_neg]
    change D5.ModGammaSix (F a b * F b a)
      (K a b ^ (A a * E b - A b * E a))
    rw [heq]
  simpa [F, K] using hpartition.trans (hdiag.mul hpairs)

def formula91Exponent
    (C : Context G) (B : GammaTwoFourBasis G)
    (l m : Fin C.r) (a b : Fin B.n) : ℤ :=
  sCoord C B l a * sCoord C B m b -
    sCoord C B m a * sCoord C B l b

def formula91Right
    (C : Context G) (B : GammaTwoFourBasis G)
    (l m : Fin C.r) : G :=
  strictPairProduct fun a b =>
    D5.paperComm (B.y a) (B.y b) ^ formula91Exponent C B l m a b

/-- Formula (91). -/
theorem formula91
    (C : Context G) (B : GammaTwoFourBasis G) (l m : Fin C.r) :
    D5.ModGammaSix (D5.paperComm (C.x3 l) (C.x3 m))
      (formula91Right C B l m) := by
  let W : Fin C.r → G := fun k =>
    orderedProduct fun a => B.y a ^ sCoord C B k a
  have hW : ∀ k, W k ∈ D5.gamma G 2 := by
    intro k
    apply orderedProduct_mem
    intro a
    exact (D5.gamma G 2).zpow_mem (B.basis.1 a) _
  have hl := formula56_replace_left (formula81_second C B l)
    (formula81_second_mem_gamma2 C m)
  have hm := formula56_replace_right (formula81_second C B m) (hW l)
  have hexpand := paperComm_coordinateProducts B
    (sCoord C B l) (sCoord C B m)
  have hcollapse := coordinateCommSquare_to_strictPairs B
    (sCoord C B l) (sCoord C B m)
  simpa [W, formula91Right, formula91Exponent, mul_comm] using
    hl.trans (hm.trans (hexpand.trans hcollapse))

def formula92Middle
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun l m =>
    D5.paperComm (C.x3 l) (C.x3 m) ^ (-formula88Term C P ξ l m)

def formula92CoordinateRight
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun a b =>
    D5.paperComm (B.y a) (B.y b) ^ formula90Right C B P ξ a b

/-- Exponent congruence can be applied to a group power whenever the base
has the corresponding period modulo `γ₆`. -/
theorem zpow_modEq_of_period
    (x : G) (n e f : ℤ) (hperiod : D5.ModGammaSix (x ^ n) 1)
    (hef : Int.ModEq n e f) :
    D5.ModGammaSix (x ^ e) (x ^ f) := by
  rcases hef.dvd with ⟨q, hq⟩
  have hf : f = e + n * q := by linarith
  have h := (D5.ModEq.refl (D5.gamma G 6) (x ^ e)).mul (hperiod.zpow q)
  simpa [hf, zpow_add, zpow_mul] using h.symm

/-- Formula (90) changes every exponent in formula (85) by an allowed
multiple of `n(a)`. -/
theorem formula85_to_formula90_coordinates
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (formula85Right C B P ξ)
      (formula92CoordinateRight C B P ξ) := by
  unfold formula85Right formula92CoordinateRight strictPairProduct
  apply modEq_orderedProduct
  intro a
  apply modEq_orderedProductWhere
  intro b hab
  exact zpow_modEq_of_period
    (D5.paperComm (B.y a) (B.y b)) (orderInt B.order a)
    (formula85Exponent C B P ξ a b) (formula90Right C B P ξ a b)
    (formula86 B a b) (formula90 C B P hP ξ hab)

/-- Expand the middle product in (92), exchange its two strict-pair loops,
and collect the powers of each `[yₐ,y_b]`. -/
theorem formula92_middle_coordinates
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula92Middle C P ξ)
      (formula92CoordinateRight C B P ξ) := by
  let K : Fin B.n → Fin B.n → G := fun a b =>
    D5.paperComm (B.y a) (B.y b)
  let e : Fin C.r → Fin C.r → Fin B.n → Fin B.n → ℤ :=
    fun l m a b => -(formula91Exponent C B l m a b *
      formula88Term C P ξ l m)
  have hK : ∀ a b, K a b ∈ D5.gamma G 3 := by
    intro a b
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (B.basis.1 a) (B.basis.1 b)
  have hlocal : D5.ModGammaSix (formula92Middle C P ξ)
      (strictPairProduct fun l m =>
        (formula91Right C B l m) ^ (-formula88Term C P ξ l m)) := by
    unfold formula92Middle strictPairProduct
    apply modEq_orderedProduct
    intro l
    apply modEq_orderedProductWhere
    intro m hlm
    exact (formula91 C B l m).zpow (-formula88Term C P ξ l m)
  have hdistribute : D5.ModGammaSix
      (strictPairProduct fun l m =>
        (formula91Right C B l m) ^ (-formula88Term C P ξ l m))
      (strictPairProduct fun l m => strictPairProduct fun a b =>
        K a b ^ e l m a b) := by
    unfold strictPairProduct
    apply modEq_orderedProduct
    intro l
    apply modEq_orderedProductWhere
    intro m hlm
    have hp := strictPairProduct_zpow_gammaThree
      (fun a b => K a b ^ formula91Exponent C B l m a b)
      (fun a b hab => (D5.gamma G 3).zpow_mem (hK a b) _)
      (-formula88Term C P ξ l m)
    have hnorm : D5.ModGammaSix
        (strictPairProduct fun a b =>
          (K a b ^ formula91Exponent C B l m a b) ^
            (-formula88Term C P ξ l m))
        (strictPairProduct fun a b => K a b ^ e l m a b) := by
      unfold strictPairProduct
      apply modEq_orderedProduct
      intro a
      apply modEq_orderedProductWhere
      intro b hab
      have heq :
          (K a b ^ formula91Exponent C B l m a b) ^
              (-formula88Term C P ξ l m) = K a b ^ e l m a b := by
        rw [← zpow_mul]
        congr 1
        dsimp [e]
        ring
      change D5.ModGammaSix
        ((K a b ^ formula91Exponent C B l m a b) ^
          (-formula88Term C P ξ l m)) (K a b ^ e l m a b)
      rw [heq]
    simpa [formula91Right, K] using hp.trans hnorm
  have hswap := strictPairProduct_strictPairProduct_swap_gammaThree
    (fun l m a b => K a b ^ e l m a b)
    (fun l m a b hlm hab => (D5.gamma G 3).zpow_mem (hK a b) _)
  have hcollect :
      (strictPairProduct fun a b => strictPairProduct fun l m =>
        K a b ^ e l m a b) = formula92CoordinateRight C B P ξ := by
    unfold formula92CoordinateRight
    apply congrArg strictPairProduct
    funext a b
    rw [strictPairProduct_zpow_same_base]
    congr 1
    rw [formula90Right, formula90Positive]
    dsimp [e, formula91Exponent]
    simp only [Finset.sum_neg_distrib]
  exact hlocal.trans <| hdistribute.trans <| hswap.trans <| by
    rw [hcollect]

/-- The last product in (92) is trivial modulo `γ₆`, factor by factor. -/
theorem formula92_middle_vanishes
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula92Middle C P ξ) 1 := by
  apply D5.modEq_one_iff_mem.mpr
  unfold formula92Middle
  apply orderedProduct_mem
  intro l
  apply orderedProductWhere_mem
  intro m hlm
  apply (D5.gamma G 6).zpow_mem
  exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
    (C.x3_mem_gamma3 l) (C.x3_mem_gamma3 m)

/-- Formula (92): the remainder `κ` is trivial modulo `γ₆`. -/
theorem formula92
    (C : Context G) (B : GammaTwoFourBasis G)
    (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (kappa C P ξ) 1 := by
  have h85 := formula85 C B P hP ξ
  have h90 := formula85_to_formula90_coordinates C B P hP ξ
  have h91 := formula92_middle_coordinates C B P ξ
  exact h85.trans <| h90.trans <| h91.symm.trans
    (formula92_middle_vanishes C P ξ)

/-- Finite-group form of formula (92), using the invariant-factor basis
whose existence was accepted in formula (80). -/
theorem formula92_finite [Finite G]
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies) (ξ : G) :
    D5.ModGammaSix (kappa C P ξ) 1 :=
  formula92 C (GammaTwoFourBasis.chosen G) P hP ξ

end

end D5.Tahara
