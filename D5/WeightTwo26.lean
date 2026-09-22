import D5.WeightTwo23
import D5.RotationSix
import D5.WeightFivePowers

/-!
# Conditions (14)--(15) and the cancellation in formula (26)

This file supplies the local weight-five identities used to pair the
off-diagonal factors of formula (23).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The Hall--Witt rotation needed between the two orientations of a
weight-two pair.  All correction terms in the general formula have weight
at least six for weights `(2,2,1)`. -/
theorem weight_two_pair_rotation
    {ξ a b : G} (hξ : ξ ∈ D5.gamma G 1)
    (ha : a ∈ D5.gamma G 2) (hb : b ∈ D5.gamma G 2) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ b) a)
      (D5.paperComm (D5.paperComm ξ a) b *
        D5.paperComm (D5.paperComm a b) ξ) := by
  let A := D5.paperComm (D5.paperComm a b) ξ
  let B := D5.paperComm (D5.paperComm ξ a) b
  let Q := D5.paperComm (D5.paperComm ξ b) a
  let D := D5.paperComm (D5.paperComm (D5.paperComm a b) b) ξ
  let E := (D5.paperComm (D5.paperComm (D5.paperComm a b) ξ) b)⁻¹
  let F := D5.paperComm (D5.paperComm (D5.paperComm b ξ) ξ) a
  let H := (D5.paperComm (D5.paperComm (D5.paperComm b ξ) a) ξ)⁻¹
  have ha1 : a ∈ D5.gamma G 1 := D5.gamma_antitone G (by norm_num) ha
  have hb1 : b ∈ D5.gamma G 1 := D5.gamma_antitone G (by norm_num) hb
  have hrot := D5.rotation_formula19 ha hb1 hξ
  have hab : D5.paperComm a b ∈ D5.gamma G 4 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb
  have hbξ : D5.paperComm b ξ ∈ D5.gamma G 3 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hξ
  have hD : D ∈ D5.gamma G 6 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hab hb) hξ
  have hE : E ∈ D5.gamma G 6 := by
    apply (D5.gamma G 6).inv_mem
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hab hξ) hb
  have hF : F ∈ D5.gamma G 6 := by
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hbξ hξ) ha
  have hH : H ∈ D5.gamma G 6 := by
    apply (D5.gamma G 6).inv_mem
    exact D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hbξ ha) hξ
  change ((Q : G) : G ⧸ D5.gamma G 6) =
    ((B * A : G) : G ⧸ D5.gamma G 6)
  change ((A : G) : G ⧸ D5.gamma G 6) =
    (((B⁻¹ * Q * D * E * F * H : G)) : G ⧸ D5.gamma G 6) at hrot
  have hDq : ((D : G) : G ⧸ D5.gamma G 6) = 1 :=
    (QuotientGroup.eq_one_iff D).mpr hD
  have hEq : ((E : G) : G ⧸ D5.gamma G 6) = 1 :=
    (QuotientGroup.eq_one_iff E).mpr hE
  have hFq : ((F : G) : G ⧸ D5.gamma G 6) = 1 :=
    (QuotientGroup.eq_one_iff F).mpr hF
  have hHq : ((H : G) : G ⧸ D5.gamma G 6) = 1 :=
    (QuotientGroup.eq_one_iff H).mpr hH
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_mul, QuotientGroup.mk_mul, hDq, hEq, hFq, hHq] at hrot
  simp only [mul_one] at hrot
  calc
    (Q : G ⧸ D5.gamma G 6) = B * (B⁻¹ * Q) := by
      rw [QuotientGroup.mk_inv]
      group
    _ = B * A := by rw [← hrot]
    _ = ((B * A : G) : G ⧸ D5.gamma G 6) := by
      rw [QuotientGroup.mk_mul]

/-- The order `e(p)` kills `[ξ,x₂ₚ,x₂_q]` modulo `γ₆`; relation (2)
places `x₂ₚ ^ e(p)` in `γ₃`. -/
theorem formula23_base_order_power_vanish
    (C : Context G) (ξ : G) (p q : Fin C.t) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
        orderInt C.e p) 1 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hq1 : C.x2 q ∈ D5.gamma G 1 :=
    D5.gamma_antitone G (by norm_num) (C.x2_mem_gamma2 q)
  have hpow := nested_weight_two_zpow_right hξ
    (C.x2_mem_gamma2 p) hq1 (orderInt C.e p)
  have hpe : C.x2 p ^ orderInt C.e p ∈ D5.gamma G 3 :=
    C.x2_order_power_mem_gamma3 p
  have hleft : D5.paperComm
      (D5.paperComm ξ (C.x2 p ^ orderInt C.e p)) (C.x2 q) ∈
      D5.gamma G 6 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hpe)
      (C.x2_mem_gamma2 q)
  exact hpow.symm.trans <| by
    rw [D5.modEq_one_iff_mem]
    exact hleft

theorem formula23_diagonal_vanish
    (C : Context G) (P : Parameters C.s C.t)
    (h14 : P.Condition14) (ξ : G) (p : Fin C.t) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 p) ^
        (-(∑ j, P.v j p * C.b j p))) 1 := by
  have hd : orderInt C.e p ∣ -(∑ j, P.v j p * C.b j p) := by
    exact dvd_neg.mpr (Int.modEq_zero_iff_dvd.mp (h14 p))
  exact D5.modGammaSix_zpow_eq_one_of_dvd
    (formula23_base_order_power_vanish C ξ p p) hd

def formula23Coefficient
    (C : Context G) (P : Parameters C.s C.t)
    (p q : Fin C.t) : ℤ :=
  ∑ j, P.v j p * C.b j q

/-- The same order also kills `[[x₂ₚ,x₂_q],ξ]`. -/
theorem formula26_base_order_power_vanish
    (C : Context G) (ξ : G) (p q : Fin C.t) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ ^
        orderInt C.e p) 1 := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hq1 : C.x2 q ∈ D5.gamma G 1 :=
    D5.gamma_antitone G (by norm_num) (C.x2_mem_gamma2 q)
  have hpow := D5.paperComm_paperComm_zpow_left_mod_gamma_six
    (C.x2_mem_gamma2 p) hq1 hξ (orderInt C.e p)
  have hpe : C.x2 p ^ orderInt C.e p ∈ D5.gamma G 3 :=
    C.x2_order_power_mem_gamma3 p
  have hleft : D5.paperComm
      (D5.paperComm (C.x2 p ^ orderInt C.e p) (C.x2 q)) ξ ∈
      D5.gamma G 6 :=
    D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        hpe (C.x2_mem_gamma2 q)) hξ
  exact hpow.symm.trans <| by
    rw [D5.modEq_one_iff_mem]
    exact hleft

private theorem formula26_exponent_replace
    (C : Context G) (P : Parameters C.s C.t)
    (h15 : P.Condition15) (ξ : G)
    {p q : Fin C.t} (hpq : p < q) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ ^
        (-formula23Coefficient C P q p))
      (D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ ^
        formula23Coefficient C P p q) := by
  let A := D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ
  let S := formula23Coefficient C P p q
  let T := formula23Coefficient C P q p
  have hd : orderInt C.e p ∣ S + T := by
    have hraw := Int.modEq_zero_iff_dvd.mp (h15 p q hpq)
    rw [Finset.sum_add_distrib] at hraw
    simpa [S, T, formula23Coefficient, add_comm] using hraw
  have hsum : D5.ModGammaSix (A ^ (S + T)) 1 :=
    D5.modGammaSix_zpow_eq_one_of_dvd
      (formula26_base_order_power_vanish C ξ p q) hd
  change ((A ^ (-T) : G) : G ⧸ D5.gamma G 6) =
    ((A ^ S : G) : G ⧸ D5.gamma G 6)
  have hqsum : ((A ^ (S + T) : G) : G ⧸ D5.gamma G 6) = 1 := hsum
  rw [QuotientGroup.mk_zpow] at hqsum
  change (A : G ⧸ D5.gamma G 6) ^ (-T) =
    (A : G ⧸ D5.gamma G 6) ^ S
  calc
    (A : G ⧸ D5.gamma G 6) ^ (-T) =
        (A : G ⧸ D5.gamma G 6) ^ (-T) * 1 := by simp
    _ = (A : G ⧸ D5.gamma G 6) ^ (-T) *
        (A : G ⧸ D5.gamma G 6) ^ (S + T) := by rw [hqsum]
    _ = (A : G ⧸ D5.gamma G 6) ^ S := by
      rw [← zpow_add]
      congr 1
      ring

/-- Conditions (14)--(15), locally for one strict pair: the two oriented
factors of (23) reduce to the correction factor in (26). -/
theorem formula23_pair_to_formula26
    (C : Context G) (P : Parameters C.s C.t)
    (h15 : P.Condition15) (ξ : G)
    {p q : Fin C.t} (hpq : p < q) :
    D5.ModGammaSix
      (D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
          (-formula23Coefficient C P p q) *
        D5.paperComm (D5.paperComm ξ (C.x2 q)) (C.x2 p) ^
          (-formula23Coefficient C P q p))
      (D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ ^
        formula23Coefficient C P p q) := by
  let B := D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q)
  let Q := D5.paperComm (D5.paperComm ξ (C.x2 q)) (C.x2 p)
  let A := D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ
  let S := formula23Coefficient C P p q
  let T := formula23Coefficient C P q p
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hrot := weight_two_pair_rotation hξ
    (C.x2_mem_gamma2 p) (C.x2_mem_gamma2 q)
  have hB : B ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x2_mem_gamma2 p)) (C.x2_mem_gamma2 q)
  have hA : A ∈ D5.gamma G 3 := by
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          (C.x2_mem_gamma2 p) (C.x2_mem_gamma2 q)) hξ
  have hqpow := hrot.zpow (-T)
  have hdist := D5.gammaThree_mul_zpow hB hA (-T)
  have hstart : D5.ModGammaSix
      (B ^ (-S) * Q ^ (-T))
      (B ^ (-S) * (B ^ (-T) * A ^ (-T))) :=
    (D5.ModEq.refl (D5.gamma G 6) (B ^ (-S))).mul
      (hqpow.trans hdist)
  have hd : orderInt C.e p ∣ -(S + T) := by
    apply dvd_neg.mpr
    have hraw := Int.modEq_zero_iff_dvd.mp (h15 p q hpq)
    rw [Finset.sum_add_distrib] at hraw
    simpa [S, T, formula23Coefficient, add_comm] using hraw
  have hBvanish : D5.ModGammaSix (B ^ (-(S + T))) 1 :=
    D5.modGammaSix_zpow_eq_one_of_dvd
      (formula23_base_order_power_vanish C ξ p q) hd
  have hAreplace : D5.ModGammaSix (A ^ (-T)) (A ^ S) := by
    simpa [A, S, T] using formula26_exponent_replace C P h15 ξ hpq
  refine hstart.trans <| (show D5.ModGammaSix
      (B ^ (-S) * (B ^ (-T) * A ^ (-T)))
      (A ^ S) by
    have hcombine : B ^ (-S) * B ^ (-T) = B ^ (-(S + T)) := by
      rw [← zpow_add]
      congr 1
      ring
    rw [← mul_assoc, hcombine]
    simpa only [one_mul] using hBvanish.mul hAreplace)

/-- Partition a square ordered product into its diagonal and its two
orientations of the strict upper triangle. -/
theorem orderedProduct_square_partition_gammaThree
    {n : ℕ} (f : Fin n → Fin n → G)
    (hf : ∀ p q, f p q ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (orderedProduct fun p => orderedProduct fun q => f p q)
      ((orderedProduct fun p => f p p) *
        (strictPairProduct f * strictPairProduct fun p q => f q p)) := by
  classical
  let all := List.finRange n
  let square := all ×ˢ all
  let diag := all.map fun p => (p, p)
  let upper := square.filter fun pq => pq.1 < pq.2
  let swap : Fin n × Fin n → Fin n × Fin n := fun pq => (pq.2, pq.1)
  let lower := upper.map swap
  have hall : all.Nodup := by simpa [all] using List.nodup_finRange n
  have hsquare : square.Nodup := hall.product hall
  have hswap : Function.Injective swap := by
    intro a b h
    exact Prod.ext (congrArg Prod.snd h) (congrArg Prod.fst h)
  have hdiag : diag.Nodup := by
    apply hall.map
    intro a b h
    exact congrArg Prod.fst h
  have hupper : upper.Nodup := hsquare.filter _
  have hlower : lower.Nodup := hupper.map hswap
  have hdu : diag.Disjoint upper := by
    rw [List.disjoint_left]
    intro pq hd hu
    rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
    have hlt := of_decide_eq_true (List.mem_filter.mp hu).2
    exact (lt_irrefl p hlt)
  have hdl : diag.Disjoint lower := by
    rw [List.disjoint_left]
    intro pq hd hl
    rcases List.mem_map.mp hd with ⟨p, hp, rfl⟩
    rcases List.mem_map.mp hl with ⟨ab, hab, hs⟩
    have hlt := of_decide_eq_true (List.mem_filter.mp hab).2
    have heq : ab.1 = ab.2 := by
      have h1 := congrArg Prod.fst hs
      have h2 := congrArg Prod.snd hs
      simpa [swap] using h2.trans h1.symm
    exact (ne_of_lt hlt heq)
  have hul : upper.Disjoint lower := by
    rw [List.disjoint_left]
    intro pq hu hl
    have hlt := of_decide_eq_true (List.mem_filter.mp hu).2
    rcases List.mem_map.mp hl with ⟨ab, hab, hs⟩
    have hba := of_decide_eq_true (List.mem_filter.mp hab).2
    have h1 : pq.1 = ab.2 := by simpa [swap] using congrArg Prod.fst hs.symm
    have h2 : pq.2 = ab.1 := by simpa [swap] using congrArg Prod.snd hs.symm
    exact (not_lt_of_ge (le_of_lt hba)) (by simpa [h1, h2] using hlt)
  have htarget : (diag ++ (upper ++ lower)).Nodup := by
    apply List.Nodup.append
    · exact hdiag
    · exact List.Nodup.append hupper hlower hul
    · rw [List.disjoint_left]
      intro pq hd hright
      rcases List.mem_append.mp hright with hu | hl
      · exact (List.disjoint_left.mp hdu) hd hu
      · exact (List.disjoint_left.mp hdl) hd hl
  have hpairs : square.Perm (diag ++ (upper ++ lower)) := by
    apply (List.perm_ext_iff_of_nodup hsquare htarget).2
    intro pq
    have hs : pq ∈ square := by
      exact List.mem_product.mpr ⟨by simp [all], by simp [all]⟩
    simp only [hs, true_iff, List.mem_append]
    by_cases heq : pq.1 = pq.2
    · left
      change pq ∈ all.map (fun p => (p, p))
      apply List.mem_map.mpr
      exact ⟨pq.1, by simp [all], Prod.ext rfl heq⟩
    · rcases lt_or_gt_of_ne heq with hlt | hgt
      · right; left
        change pq ∈ square.filter fun ab => ab.1 < ab.2
        exact List.mem_filter.mpr ⟨hs, by simp [hlt]⟩
      · right; right
        change pq ∈ upper.map swap
        apply List.mem_map.mpr
        exact ⟨(pq.2, pq.1),
          List.mem_filter.mpr ⟨List.mem_product.mpr
            ⟨by simp [all], by simp [all]⟩, by simp [hgt]⟩,
          by simp [swap]⟩
  have flatten : ∀ {α β : Type} (is : List α) (js : List β)
      (g : α → β → G),
      (is.map fun i => (js.map fun j => g i j).prod).prod =
        ((is ×ˢ js).map fun ij => g ij.1 ij.2).prod := by
    intro α β is js g
    induction is with
    | nil => simp
    | cons i is ih =>
        simp only [List.map_cons, List.prod_cons, List.product_cons,
          List.map_append, List.prod_append]
        rw [ih]
        congr 1
        simp only [List.map_map]
        rfl
  have flattenFiltered : ∀ {α β : Type} (is : List α) (js : List β)
      (p : α → β → Prop) [DecidableRel p] (g : α → β → G),
      (is.map fun i => ((js.filter (p i)).map (g i)).prod).prod =
        (((is ×ˢ js).filter fun ij => p ij.1 ij.2).map
          fun ij => g ij.1 ij.2).prod := by
    intro α β is js p inst g
    induction is with
    | nil => simp
    | cons i is ih =>
        rw [List.map_cons, List.prod_cons, List.product_cons,
          List.filter_append, List.map_append, List.prod_append, ih]
        congr 1
        simp only [List.filter_map, List.map_map]
        rfl
  have hsource : (orderedProduct fun p => orderedProduct fun q => f p q) =
      (square.map fun pq => f pq.1 pq.2).prod := by
    unfold orderedProduct
    simpa [square, all] using flatten (List.finRange n) (List.finRange n) f
  have hdiagEq : (orderedProduct fun p => f p p) =
      (diag.map fun pq => f pq.1 pq.2).prod := by
    unfold orderedProduct
    dsimp [diag, all]
    rw [List.map_map]
    rfl
  have hupperEq : strictPairProduct f =
      (upper.map fun pq => f pq.1 pq.2).prod := by
    unfold strictPairProduct orderedProduct orderedProductWhere
    simpa [upper, square, all] using
      flattenFiltered (List.finRange n) (List.finRange n)
        (fun p q => p < q) f
  have hlowerEq : strictPairProduct (fun p q => f q p) =
      (lower.map fun pq => f pq.1 pq.2).prod := by
    unfold strictPairProduct orderedProduct orderedProductWhere
    simpa [lower, upper, square, all, swap, List.map_map] using
      flattenFiltered (List.finRange n) (List.finRange n)
        (fun p q => p < q) (fun p q => f q p)
  rw [hsource, hdiagEq, hupperEq, hlowerEq, ← List.prod_append,
    ← List.prod_append]
  have hperm := D5.listProd_perm_gammaThree
    (hpairs.map fun pq => f pq.1 pq.2) (fun x hx => by
      rcases List.mem_map.mp hx with ⟨pq, hpq, rfl⟩
      exact hf pq.1 pq.2)
  simpa only [List.map_append] using hperm

theorem strictPairProduct_pointwise_gammaThree
    {n : ℕ} (f g : Fin n → Fin n → G)
    (hf : ∀ p q, p < q → f p q ∈ D5.gamma G 3)
    (hg : ∀ p q, p < q → g p q ∈ D5.gamma G 3) :
    D5.ModGammaSix
      (strictPairProduct f * strictPairProduct g)
      (strictPairProduct fun p q => f p q * g p q) := by
  let F : Fin n → G := fun p => orderedProductWhere (p < ·) (f p)
  let H : Fin n → G := fun p => orderedProductWhere (p < ·) (g p)
  have hF : ∀ p, F p ∈ D5.gamma G 3 := by
    intro p
    apply orderedProductWhere_mem
    intro q hpq
    exact hf p q hpq
  have hH : ∀ p, H p ∈ D5.gamma G 3 := by
    intro p
    apply orderedProductWhere_mem
    intro q hpq
    exact hg p q hpq
  have houter := (D5.orderedProduct_pointwise_mul_gammaThree F H hF hH).symm
  refine (show D5.ModGammaSix
      (strictPairProduct f * strictPairProduct g)
      (orderedProduct fun p => F p * H p) by
        simpa [strictPairProduct, F, H] using houter).trans ?_
  unfold strictPairProduct
  apply modEq_orderedProduct
  intro p
  exact (D5.orderedProductWhere_pointwise_mul_gammaThree
    (p < ·) (f p) (g p) (hf p) (hg p)).symm

/-- The correction product on the first line of formula (26). -/
def formula26Correction
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  strictPairProduct fun p q =>
    D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ ^
      formula23Coefficient C P p q

/-- Formulas (24)--(26): condition (14) removes the diagonal and condition
(15), together with the weight-two Hall--Witt rotation, pairs the two
off-diagonal orientations. -/
theorem weight_two_block_cancels26
    (C : Context G) (P : Parameters C.s C.t)
    (h14 : P.Condition14) (h15 : P.Condition15) (ξ : G) :
    D5.ModGammaSix
      (formula23Collected C P ξ)
      (formula26Correction C P ξ) := by
  let F : Fin C.t → Fin C.t → G := fun p q =>
    D5.paperComm (D5.paperComm ξ (C.x2 p)) (C.x2 q) ^
      (-formula23Coefficient C P p q)
  let R : Fin C.t → Fin C.t → G := fun p q =>
    D5.paperComm (D5.paperComm (C.x2 p) (C.x2 q)) ξ ^
      formula23Coefficient C P p q
  have hF : ∀ p q, F p q ∈ D5.gamma G 3 := by
    intro p q
    apply (D5.gamma G 3).zpow_mem
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x2_mem_gamma2 p)) (C.x2_mem_gamma2 q)
  have hpartition := orderedProduct_square_partition_gammaThree F hF
  have hdiag : D5.ModGammaSix (orderedProduct fun p => F p p) 1 := by
    have hpoint : D5.ModGammaSix
        (orderedProduct fun p => F p p)
        (orderedProduct fun _p : Fin C.t => (1 : G)) := by
      apply modEq_orderedProduct
      intro p
      simpa [F, formula23Coefficient] using
        formula23_diagonal_vanish C P h14 ξ p
    exact hpoint.trans <| by
      simpa [orderedProduct] using
        D5.ModEq.refl (D5.gamma G 6) (1 : G)
  have hpairs : D5.ModGammaSix
      (strictPairProduct F * strictPairProduct fun p q => F q p)
      (strictPairProduct R) := by
    have hcombine := strictPairProduct_pointwise_gammaThree F
      (fun p q => F q p)
      (fun p q hpq => hF p q) (fun p q hpq => hF q p)
    refine hcombine.trans ?_
    unfold strictPairProduct
    apply modEq_orderedProduct
    intro p
    apply modEq_orderedProductWhere
    intro q hpq
    simpa [F, R] using formula23_pair_to_formula26 C P h15 ξ hpq
  unfold formula23Collected formula26Correction
  have hstart : D5.ModGammaSix
      (orderedProduct fun p => orderedProduct fun q => F p q)
      ((orderedProduct fun p => F p p) *
        (strictPairProduct F * strictPairProduct fun p q => F q p)) :=
    hpartition
  exact hstart.trans <| by
    simpa [R] using hdiag.mul hpairs

end

end D5.Tahara
