import D5.OrderedCoordinates
import D5.TaharaExpand

/-!
# The multiplicative consequence of Tahara condition (4.3.6)

This file checks formula (6) of the proof.  The calculation is performed in
the abelian layer `γ₂/γ₃`; condition (4.3.6) leaves only multiples of the
orders of the second-layer cyclic generators.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The boxed word in formula (6). -/
def condition6Word (C : Context G) (P : Parameters C.s C.t)
    (i : Fin C.s) : G :=
  orderedProductWhere (i < ·)
      (fun h => C.x1 h ^ (P.u i h * orderInt C.d h)) *
    orderedProductWhere (· < i)
      (fun h => C.x1 h ^ (-P.u h i * orderInt C.d i)) *
    (orderedProduct (fun p => C.x2 p ^ P.v i p) ^ orderInt C.d i)

namespace Context

theorem x2_order_power_mem_gamma3 (C : Context G) (p : Fin C.t) :
    C.x2 p ^ orderInt C.e p ∈ D5.gamma G 3 := by
  have hx3 : orderedProduct (fun l => C.x3 l ^ C.delta p l) ∈ D5.gamma G 3 :=
    orderedProduct_mem (D5.gamma G 3) _ fun l =>
      (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _
  exact D5.mem_of_modEq_of_le (D5.gamma_antitone G (by norm_num : 3 ≤ 4))
    (C.x2_power p) hx3

theorem x1_power_mod_gamma3 (C : Context G) (i : Fin C.s) :
    D5.ModEq (D5.gamma G 3) (C.x1 i ^ orderInt C.d i)
      (orderedProduct fun p => C.x2 p ^ C.b i p) := by
  have hweak := (C.x1_power i).mono
    (D5.gamma_antitone G (by norm_num : 3 ≤ 4))
  have hx3 : orderedProduct (fun l => C.x3 l ^ C.c i l) ∈ D5.gamma G 3 :=
    orderedProduct_mem (D5.gamma G 3) _ fun l =>
      (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _
  have htail : D5.ModEq (D5.gamma G 3)
      (orderedProduct fun l => C.x3 l ^ C.c i l) 1 := by
    rw [D5.modEq_one_iff_mem]
    exact hx3
  exact hweak.trans <| by
    simpa using (D5.ModEq.refl (D5.gamma G 3)
      (orderedProduct fun p => C.x2 p ^ C.b i p)).mul htail

theorem orderInt_eq_mul_ratio (C : Context G) {i j : Fin C.s} (hij : i ≤ j) :
    orderInt C.d j = orderInt C.d i * orderRatio C.d i j := by
  have hdvd := C.d_dvd i j hij
  have hnat : C.d j = C.d i * (C.d j / C.d i) := by
    simpa [Nat.mul_comm] using (Nat.div_mul_cancel hdvd).symm
  have hz : (C.d j : ℤ) = (C.d i : ℤ) * ((C.d j / C.d i : ℕ) : ℤ) := by
    exact_mod_cast hnat
  simpa [orderInt, orderRatio] using hz

end Context

private theorem x2_quotient_pairwise_commute (C : Context G)
    (p q : Fin C.t) :
    Commute ((C.x2 p : G ⧸ D5.gamma G 3)) (C.x2 q) := by
  show (C.x2 p : G ⧸ D5.gamma G 3) * C.x2 q = C.x2 q * C.x2 p
  exact D5.mul_comm_mod_gamma (n := 3) (r := 2) (s := 2)
    (by norm_num) (by norm_num) (by norm_num)
    (C.x2_mem_gamma2 p) (C.x2_mem_gamma2 q)

private theorem quotient_coe_orderedProduct (C : Context G)
    (a : Fin C.t → G) :
    ((orderedProduct a : G) : G ⧸ D5.gamma G 3) =
      orderedProduct (fun p => (a p : G ⧸ D5.gamma G 3)) := by
  unfold orderedProduct
  induction List.finRange C.t with
  | nil => simp
  | cons x xs ih => simp [ih]

private theorem quotient_coe_orderedProductWhere
    {n : ℕ} (q : Fin n → Prop) [DecidablePred q] (a : Fin n → G) :
    ((orderedProductWhere q a : G) : G ⧸ D5.gamma G 3) =
      orderedProductWhere q (fun i => (a i : G ⧸ D5.gamma G 3)) := by
  unfold orderedProductWhere
  induction (List.finRange n).filter q with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem coordinateProduct_zpow_mod_gamma3 (C : Context G)
    (a : Fin C.t → ℤ) (z : ℤ) :
    D5.ModEq (D5.gamma G 3)
      (orderedProduct (fun p => C.x2 p ^ a p) ^ z)
      (orderedProduct fun p => C.x2 p ^ (z * a p)) := by
  change (((orderedProduct (fun p => C.x2 p ^ a p) ^ z : G) :
    G ⧸ D5.gamma G 3)) = _
  rw [QuotientGroup.mk_zpow, quotient_coe_orderedProduct C,
    quotient_coe_orderedProduct C]
  exact orderedProduct_zpow_of_pairwise_commute
    (fun p => (C.x2 p : G ⧸ D5.gamma G 3))
    (x2_quotient_pairwise_commute C) a z

theorem coordinateProduct_mul_mod_gamma3 (C : Context G)
    (a b : Fin C.t → ℤ) :
    D5.ModEq (D5.gamma G 3)
      (orderedProduct (fun p => C.x2 p ^ a p) *
        orderedProduct (fun p => C.x2 p ^ b p))
      (orderedProduct fun p => C.x2 p ^ (a p + b p)) := by
  change (((orderedProduct (fun p => C.x2 p ^ a p) *
    orderedProduct (fun p => C.x2 p ^ b p) : G) : G ⧸ D5.gamma G 3)) = _
  rw [QuotientGroup.mk_mul, quotient_coe_orderedProduct C, quotient_coe_orderedProduct C,
    quotient_coe_orderedProduct C]
  exact orderedProduct_mul_of_pairwise_commute
    (fun p => (C.x2 p : G ⧸ D5.gamma G 3))
    (x2_quotient_pairwise_commute C) a b

theorem coordinateProductWhere_mod_gamma3 (C : Context G)
    {n : ℕ} (q : Fin n → Prop) [DecidablePred q]
    (a : Fin n → Fin C.t → ℤ) :
    D5.ModEq (D5.gamma G 3)
      (orderedProductWhere q (fun h => orderedProduct fun p => C.x2 p ^ a h p))
      (orderedProduct fun p => C.x2 p ^
        (∑ h ∈ Finset.univ.filter q, a h p)) := by
  change (((orderedProductWhere q (fun h => orderedProduct fun p =>
    C.x2 p ^ a h p) : G) : G ⧸ D5.gamma G 3)) = _
  rw [quotient_coe_orderedProductWhere, quotient_coe_orderedProduct C]
  simp_rw [quotient_coe_orderedProduct C]
  exact orderedProductWhere_coordinates_of_pairwise_commute
    (fun p => (C.x2 p : G ⧸ D5.gamma G 3))
    (x2_quotient_pairwise_commute C) q a

theorem later_x1_factor_mod_gamma3 (C : Context G)
    (P : Parameters C.s C.t) {i h : Fin C.s} (_hih : i < h) :
    D5.ModEq (D5.gamma G 3)
      (C.x1 h ^ (P.u i h * orderInt C.d h))
      (orderedProduct fun p => C.x2 p ^ (P.u i h * C.b h p)) := by
  rw [mul_comm, zpow_mul]
  exact (C.x1_power_mod_gamma3 h).zpow (P.u i h) |>.trans
    (coordinateProduct_zpow_mod_gamma3 C (C.b h) (P.u i h))

theorem earlier_x1_factor_mod_gamma3 (C : Context G)
    (P : Parameters C.s C.t) {h i : Fin C.s} (hhi : h < i) :
    D5.ModEq (D5.gamma G 3)
      (C.x1 h ^ (-P.u h i * orderInt C.d i))
      (orderedProduct fun p => C.x2 p ^
        ((-P.u h i * orderRatio C.d h i) * C.b h p)) := by
  have hd := C.orderInt_eq_mul_ratio (le_of_lt hhi)
  have hexp : -P.u h i * orderInt C.d i =
      orderInt C.d h * (-P.u h i * orderRatio C.d h i) := by
    rw [hd]
    ring
  rw [hexp, zpow_mul]
  exact (C.x1_power_mod_gamma3 h).zpow
    (-P.u h i * orderRatio C.d h i) |>.trans
      (coordinateProduct_zpow_mod_gamma3 C (C.b h)
        (-P.u h i * orderRatio C.d h i))

/-- Formula (6): the multiplicative consequence of condition (4.3.6). -/
theorem condition6_multiplicative (C : Context G) (P : Parameters C.s C.t)
    (h6 : P.Condition6) (i : Fin C.s) :
    condition6Word C P i ∈ D5.gamma G 3 := by
  let ahigh : Fin C.s → Fin C.t → ℤ := fun h p => P.u i h * C.b h p
  let alow : Fin C.s → Fin C.t → ℤ := fun h p =>
    (-P.u h i * orderRatio C.d h i) * C.b h p
  let A : Fin C.t → ℤ := fun p =>
    (∑ h ∈ Finset.univ.filter (i < ·), ahigh h p)
  let B : Fin C.t → ℤ := fun p =>
    (∑ h ∈ Finset.univ.filter (· < i), alow h p)
  let V : Fin C.t → ℤ := fun p => orderInt C.d i * P.v i p
  have hhigh : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (i < ·)
        (fun h => C.x1 h ^ (P.u i h * orderInt C.d h)))
      (orderedProduct fun p => C.x2 p ^ A p) := by
    refine (modEq_orderedProductWhere (i < ·)
      (f := fun h => C.x1 h ^ (P.u i h * orderInt C.d h))
      (g := fun h => orderedProduct fun p => C.x2 p ^ ahigh h p) ?_).trans ?_
    · intro h hih
      exact later_x1_factor_mod_gamma3 C P hih
    · exact coordinateProductWhere_mod_gamma3 C (i < ·) ahigh
  have hlow : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (· < i)
        (fun h => C.x1 h ^ (-P.u h i * orderInt C.d i)))
      (orderedProduct fun p => C.x2 p ^ B p) := by
    refine (modEq_orderedProductWhere (· < i)
      (f := fun h => C.x1 h ^ (-P.u h i * orderInt C.d i))
      (g := fun h => orderedProduct fun p => C.x2 p ^ alow h p) ?_).trans ?_
    · intro h hhi
      exact earlier_x1_factor_mod_gamma3 C P hhi
    · exact coordinateProductWhere_mod_gamma3 C (· < i) alow
  have hv : D5.ModEq (D5.gamma G 3)
      (orderedProduct (fun p => C.x2 p ^ P.v i p) ^ orderInt C.d i)
      (orderedProduct fun p => C.x2 p ^ V p) := by
    simpa [V, mul_comm] using
      coordinateProduct_zpow_mod_gamma3 C (P.v i) (orderInt C.d i)
  have hcollect1 := coordinateProduct_mul_mod_gamma3 C A B
  have hcollect2 := coordinateProduct_mul_mod_gamma3 C
    (fun p => A p + B p) V
  have hall : D5.ModEq (D5.gamma G 3) (condition6Word C P i)
      (orderedProduct fun p => C.x2 p ^ (A p + B p + V p)) := by
    exact ((hhigh.mul hlow).mul hv).trans
      ((hcollect1.mul (D5.ModEq.refl (D5.gamma G 3)
        (orderedProduct fun p => C.x2 p ^ V p))).trans hcollect2)
  have hexp : ∀ p, A p + B p + V p = -P.v' i p * orderInt C.e p := by
    intro p
    have hc :
        (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.b h p) -
          (∑ h ∈ Finset.univ.filter (· < i),
            P.u h i * orderRatio C.d h i * C.b h p) +
          P.v i p * orderInt C.d i + P.v' i p * orderInt C.e p = 0 :=
      h6 i p
    have hsum : (∑ h ∈ Finset.univ.filter (· < i),
        ((-P.u h i * orderRatio C.d h i) * C.b h p)) =
        -(∑ h ∈ Finset.univ.filter (· < i),
          P.u h i * orderRatio C.d h i * C.b h p) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro h hh
      ring
    dsimp [A, B, V, ahigh, alow]
    rw [hsum]
    linarith
  apply D5.mem_of_modEq_of_le le_rfl hall
  apply orderedProduct_mem
  intro p
  rw [hexp p]
  have heq : -P.v' i p * orderInt C.e p =
      orderInt C.e p * (-P.v' i p) := by ring
  rw [heq, zpow_mul]
  exact (D5.gamma G 3).zpow_mem (C.x2_order_power_mem_gamma3 p) _

theorem condition6_multiplicative_of_satisfies
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (i : Fin C.s) : condition6Word C P i ∈ D5.gamma G 3 := by
  rcases hP with ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  exact condition6_multiplicative C P h6 i

end

end D5.Tahara
