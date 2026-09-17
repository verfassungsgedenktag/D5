import D5.TaharaWeights
import D5.CollectionWeighted

/-!
# First expansion of the commutator of a Tahara word

This file performs the product-collection part of formula (18).  The result
is deliberately kept in a raw form: powers inside individual factors have
not yet been extracted.  Thus this theorem checks the outer collection step
without concealing the later power-transfer calculation.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

theorem modEq_listProd {N : Subgroup G} [N.Normal]
    {xs ys : List G} (h : List.Forall₂ (D5.ModEq N) xs ys) :
    D5.ModEq N xs.prod ys.prod := by
  induction h with
  | nil => exact D5.ModEq.refl N 1
  | cons hab hrest ih =>
      simp only [List.prod_cons]
      exact hab.mul ih

theorem modEq_orderedProduct {N : Subgroup G} [N.Normal]
    {n : ℕ} {f g : Fin n → G} (h : ∀ i, D5.ModEq N (f i) (g i)) :
    D5.ModEq N (orderedProduct f) (orderedProduct g) := by
  unfold orderedProduct
  induction List.finRange n with
  | nil => exact D5.ModEq.refl N 1
  | cons i is ih =>
      simp only [List.map_cons, List.prod_cons]
      exact (h i).mul ih

theorem modEq_orderedProductWhere {N : Subgroup G} [N.Normal]
    {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    {f g : Fin n → G} (h : ∀ i, p i → D5.ModEq N (f i) (g i)) :
    D5.ModEq N (orderedProductWhere p f) (orderedProductWhere p g) := by
  unfold orderedProductWhere
  let is := (List.finRange n).filter p
  have hall : ∀ i ∈ is, D5.ModEq N (f i) (g i) := by
    intro i hi
    exact h i (of_decide_eq_true (List.mem_filter.mp hi).2)
  have aux : ∀ js : List (Fin n),
      (∀ i ∈ js, D5.ModEq N (f i) (g i)) →
        D5.ModEq N (js.map f).prod (js.map g).prod := by
    intro js hjs
    induction js with
    | nil => exact D5.ModEq.refl N 1
    | cons i js ih =>
        simp only [List.map_cons, List.prod_cons]
        exact (hjs i (by simp)).mul (ih fun j hj => hjs j (by simp [hj]))
  exact aux is hall

/-- Collection of a list product in the first commutator argument. -/
theorem paperComm_listProd_mod_gamma_six
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hsum : 6 ≤ r + s + r)
    (xs : List G) (hxs : ∀ x ∈ xs, x ∈ D5.gamma G r)
    {b : G} (hb : b ∈ D5.gamma G s) :
    D5.ModGammaSix (D5.paperComm xs.prod b)
      ((xs.map fun x => D5.paperComm x b).prod) := by
  induction xs with
  | nil =>
      simpa [D5.paperComm_eq] using D5.ModEq.refl (D5.gamma G 6) (1 : G)
  | cons x xs ih =>
      simp only [List.prod_cons, List.map_cons]
      have hx : x ∈ D5.gamma G r := hxs x (by simp)
      have htail : xs.prod ∈ D5.gamma G r :=
        listProd_mem (D5.gamma G r) xs fun y hy => hxs y (by simp [hy])
      exact (D5.paperComm_mul_left_mod_gamma_six_of_weights hr hr hs hsum
        hx htail hb).trans
          ((D5.ModEq.refl (D5.gamma G 6) (D5.paperComm x b)).mul
            (ih (fun y hy => hxs y (by simp [hy]))))

theorem paperComm_orderedProduct_mod_gamma_six
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hsum : 6 ≤ r + s + r)
    {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ D5.gamma G r)
    {b : G} (hb : b ∈ D5.gamma G s) :
    D5.ModGammaSix (D5.paperComm (orderedProduct f) b)
      (orderedProduct fun i => D5.paperComm (f i) b) := by
  unfold orderedProduct
  simpa [List.map_map] using
    (paperComm_listProd_mod_gamma_six hr hs hsum
      ((List.finRange n).map f)
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
        exact hf i) hb)

theorem paperComm_orderedProductWhere_mod_gamma_six
    {r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s) (hsum : 6 ≤ r + s + r)
    {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → G) (hf : ∀ i, p i → f i ∈ D5.gamma G r)
    {b : G} (hb : b ∈ D5.gamma G s) :
    D5.ModGammaSix (D5.paperComm (orderedProductWhere p f) b)
      (orderedProductWhere p fun i => D5.paperComm (f i) b) := by
  unfold orderedProductWhere
  simpa [List.map_map] using
    (paperComm_listProd_mod_gamma_six hr hs hsum
      (((List.finRange n).filter p).map f)
      (fun x hx => by
        rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
        exact hf i (of_decide_eq_true (List.mem_filter.mp hi).2)) hb)

/-- Raw product expansion of `[w, ξ]`: every factor of the three blocks is
commuted with `ξ`, but internal powers are retained. -/
def rawCommutatorExpansion (C : Context G) (P : Parameters C.s C.t)
    (ξ : G) : G :=
  orderedProduct (fun i => orderedProductWhere (i < ·) fun j =>
    D5.paperComm
      (D5.paperComm (C.x1 i ^ (P.u i j * orderInt C.d j)) (C.x1 j)) ξ) *
  (orderedProduct (fun i => orderedProduct fun p =>
    orderedProductWhere (p < ·) fun q =>
      D5.paperComm
        (D5.paperComm (C.x2 q) (C.x2 p) ^ (C.b i q * P.v i p)) ξ) *
  orderedProduct (fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      D5.paperComm
        (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k] ^ P.w i j k) ξ))

/-- The three products on the right hand side of formula (18). -/
def formula18Expansion (C : Context G) (P : Parameters C.s C.t)
    (ξ : G) : G :=
  orderedProduct (fun i => orderedProductWhere (i < ·) fun j =>
    D5.paperComm
      (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ ^ P.u i j) *
  (orderedProduct (fun i => orderedProduct fun p =>
    orderedProductWhere (p < ·) fun q =>
      D5.paperComm (D5.paperComm (C.x2 q) (C.x2 p)) ξ ^
        (C.b i q * P.v i p)) *
  orderedProduct (fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      D5.paperComm
        (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ^ P.w i j k))

theorem word_comm_congr_rawExpansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (D5.paperComm (word C P) ξ)
      (rawCommutatorExpansion C P ξ) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hfirst := firstBlock_mem_gamma3 C P
  have hsecond := secondBlock_mem_gamma4 C P
  have hthird := thirdBlock_mem_gamma4 C P
  have hsecondThird : secondBlock C P * thirdBlock C P ∈ D5.gamma G 4 :=
    (D5.gamma G 4).mul_mem hsecond hthird
  rw [word_eq_blocks]
  have hblocks : D5.ModGammaSix
      (D5.paperComm (firstBlock C P * secondBlock C P * thirdBlock C P) ξ)
      (D5.paperComm (firstBlock C P) ξ *
        (D5.paperComm (secondBlock C P) ξ * D5.paperComm (thirdBlock C P) ξ)) := by
    rw [mul_assoc]
    have h12 := D5.paperComm_mul_left_mod_gamma_six_of_weights
      (r := 3) (s := 4) (t := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hfirst hsecondThird hξ
    have h23 := D5.paperComm_mul_left_mod_gamma_six_of_weights
      (r := 4) (s := 4) (t := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hsecond hthird hξ
    exact h12.trans ((D5.ModEq.refl (D5.gamma G 6)
      (D5.paperComm (firstBlock C P) ξ)).mul h23)
  -- The three blockwise expansions are proved independently and then
  -- multiplied in the same right-associated order as the definition above.
  have hfirstExpand : D5.ModGammaSix (D5.paperComm (firstBlock C P) ξ)
      (orderedProduct fun i => orderedProductWhere (i < ·) fun j =>
        D5.paperComm
          (D5.paperComm (C.x1 i ^ (P.u i j * orderInt C.d j)) (C.x1 j)) ξ) := by
    unfold firstBlock
    refine (paperComm_orderedProduct_mod_gamma_six (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) _ ?_ hξ).trans ?_
    · intro i
      apply orderedProductWhere_mem
      intro j hij
      exact D5.paperComm_mem_gamma_add (r := 2) (s := 1)
        (by norm_num) (by norm_num)
        (C.x1_parameter_power_mem_gamma2 (le_of_lt hij) (P.u i j))
        (by simp [D5.gamma])
    · apply modEq_orderedProduct
      intro i
      apply paperComm_orderedProductWhere_mod_gamma_six
        (r := 3) (s := 1) (by norm_num) (by norm_num) (by norm_num)
      · intro j hij
        exact D5.paperComm_mem_gamma_add (r := 2) (s := 1)
          (by norm_num) (by norm_num)
          (C.x1_parameter_power_mem_gamma2 (le_of_lt hij) (P.u i j))
          (by simp [D5.gamma])
      · exact hξ
  have hsecondExpand : D5.ModGammaSix (D5.paperComm (secondBlock C P) ξ)
      (orderedProduct fun i => orderedProduct fun p =>
        orderedProductWhere (p < ·) fun q =>
          D5.paperComm
            (D5.paperComm (C.x2 q) (C.x2 p) ^ (C.b i q * P.v i p)) ξ) := by
    unfold secondBlock
    refine (paperComm_orderedProduct_mod_gamma_six (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) _ ?_ hξ).trans ?_
    · intro i
      apply orderedProduct_mem
      intro p
      apply orderedProductWhere_mem
      intro q hpq
      apply (D5.gamma G 4).zpow_mem
      exact D5.paperComm_mem_gamma_add (r := 2) (s := 2)
        (by norm_num) (by norm_num) (C.x2_mem_gamma2 q) (C.x2_mem_gamma2 p)
    · apply modEq_orderedProduct
      intro i
      refine (paperComm_orderedProduct_mod_gamma_six (r := 4) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) _ ?_ hξ).trans ?_
      · intro p
        apply orderedProductWhere_mem
        intro q hpq
        apply (D5.gamma G 4).zpow_mem
        exact D5.paperComm_mem_gamma_add (r := 2) (s := 2)
          (by norm_num) (by norm_num) (C.x2_mem_gamma2 q) (C.x2_mem_gamma2 p)
      · apply modEq_orderedProduct
        intro p
        apply paperComm_orderedProductWhere_mod_gamma_six
          (r := 4) (s := 1) (by norm_num) (by norm_num) (by norm_num)
        · intro q hpq
          apply (D5.gamma G 4).zpow_mem
          exact D5.paperComm_mem_gamma_add (r := 2) (s := 2)
            (by norm_num) (by norm_num) (C.x2_mem_gamma2 q) (C.x2_mem_gamma2 p)
        · exact hξ
  have hthirdExpand : D5.ModGammaSix (D5.paperComm (thirdBlock C P) ξ)
      (orderedProduct fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k =>
          D5.paperComm
            (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k] ^ P.w i j k) ξ) := by
    unfold thirdBlock
    refine (paperComm_orderedProduct_mod_gamma_six (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) _ ?_ hξ).trans ?_
    · intro i
      apply orderedProductWhere_mem
      intro j hij
      apply orderedProductWhere_mem
      intro k hjk
      apply (D5.gamma G 4).zpow_mem
      simpa using D5.leftComm_mem_gamma_of_first (r := 2) (by norm_num)
        (C.x1_order_power_mem_gamma2 i) [C.x1 j, C.x1 k]
    · apply modEq_orderedProduct
      intro i
      refine (paperComm_orderedProductWhere_mod_gamma_six
        (r := 4) (s := 1) (by norm_num) (by norm_num) (by norm_num)
        (i ≤ ·) _ ?_ hξ).trans ?_
      · intro j hij
        apply orderedProductWhere_mem
        intro k hjk
        apply (D5.gamma G 4).zpow_mem
        simpa using D5.leftComm_mem_gamma_of_first (r := 2) (by norm_num)
          (C.x1_order_power_mem_gamma2 i) [C.x1 j, C.x1 k]
      · apply modEq_orderedProductWhere
        intro j hij
        apply paperComm_orderedProductWhere_mod_gamma_six
          (r := 4) (s := 1) (by norm_num) (by norm_num) (by norm_num)
        · intro k hjk
          apply (D5.gamma G 4).zpow_mem
          simpa using D5.leftComm_mem_gamma_of_first (r := 2) (by norm_num)
            (C.x1_order_power_mem_gamma2 i) [C.x1 j, C.x1 k]
        · exact hξ
  exact hblocks.trans (hfirstExpand.mul (hsecondExpand.mul hthirdExpand))

/-- Extraction of all three displayed powers turns the raw collection into
the exact right hand side of formula (18). -/
theorem rawExpansion_congr_formula18
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (rawCommutatorExpansion C P ξ)
      (formula18Expansion C P ξ) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hfirst : D5.ModGammaSix
      (orderedProduct (fun i => orderedProductWhere (i < ·) fun j =>
        D5.paperComm
          (D5.paperComm (C.x1 i ^ (P.u i j * orderInt C.d j)) (C.x1 j)) ξ))
      (orderedProduct (fun i => orderedProductWhere (i < ·) fun j =>
        D5.paperComm
          (D5.paperComm (C.x1 i ^ orderInt C.d j) (C.x1 j)) ξ ^ P.u i j)) := by
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    have hbase : C.x1 i ^ orderInt C.d j ∈ D5.gamma G 2 :=
      C.x1_later_order_power_mem_gamma2 (le_of_lt hij)
    have hxj : C.x1 j ∈ D5.gamma G 1 := by simp [D5.gamma]
    have h := D5.paperComm_paperComm_zpow_left_mod_gamma_six
      hbase hxj hξ (P.u i j)
    simpa [mul_comm, zpow_mul] using h
  have hsecond : D5.ModGammaSix
      (orderedProduct (fun i => orderedProduct fun p =>
        orderedProductWhere (p < ·) fun q =>
          D5.paperComm
            (D5.paperComm (C.x2 q) (C.x2 p) ^ (C.b i q * P.v i p)) ξ))
      (orderedProduct (fun i => orderedProduct fun p =>
        orderedProductWhere (p < ·) fun q =>
          D5.paperComm (D5.paperComm (C.x2 q) (C.x2 p)) ξ ^
            (C.b i q * P.v i p))) := by
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProduct
    intro p
    apply modEq_orderedProductWhere
    intro q hpq
    have hpqComm : D5.paperComm (C.x2 q) (C.x2 p) ∈ D5.gamma G 4 := by
      exact D5.paperComm_mem_gamma_add (r := 2) (s := 2)
        (by norm_num) (by norm_num) (C.x2_mem_gamma2 q) (C.x2_mem_gamma2 p)
    exact D5.paperComm_zpow_left_mod_gamma_six_of_weights
      (r := 4) (s := 1) (by norm_num) (by norm_num) (by norm_num)
      hpqComm hξ (C.b i q * P.v i p)
  have hthird : D5.ModGammaSix
      (orderedProduct (fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k =>
          D5.paperComm
            (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k] ^ P.w i j k) ξ))
      (orderedProduct (fun i => orderedProductWhere (i ≤ ·) fun j =>
        orderedProductWhere (j ≤ ·) fun k =>
          D5.paperComm
            (D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k]) ξ ^ P.w i j k)) := by
    apply modEq_orderedProduct
    intro i
    apply modEq_orderedProductWhere
    intro j hij
    apply modEq_orderedProductWhere
    intro k hjk
    have hcomm : D5.leftComm (C.x1 i ^ orderInt C.d i)
        [C.x1 j, C.x1 k] ∈ D5.gamma G 4 := by
      simpa using D5.leftComm_mem_gamma_of_first (r := 2) (by norm_num)
        (C.x1_order_power_mem_gamma2 i) [C.x1 j, C.x1 k]
    exact D5.paperComm_zpow_left_mod_gamma_six_of_weights
      (r := 4) (s := 1) (by norm_num) (by norm_num) (by norm_num)
      hcomm hξ (P.w i j k)
  exact hfirst.mul (hsecond.mul hthird)

/-- Formula (18), proved with every collection and power extraction checked
inside Lean. -/
theorem commutator_representative_formula18
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (D5.paperComm (word C P) ξ)
      (formula18Expansion C P ξ) :=
  (word_comm_congr_rawExpansion C P ξ).trans
    (rawExpansion_congr_formula18 C P ξ)

end

end D5.Tahara
