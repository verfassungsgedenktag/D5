import D5.TaharaExpand

/-!
# Finite collection in `γ₃ / γ₆`

Elements of `γ₃` commute modulo `γ₆`.  The lemmas here package the finite
product rearrangements needed from formula (21) onward.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

private theorem gamma_three_commute_quotient
    {a b : G} (ha : a ∈ gamma G 3) (hb : b ∈ gamma G 3) :
    Commute ((a : G ⧸ gamma G 6)) (b : G ⧸ gamma G 6) := by
  show (a : G ⧸ gamma G 6) * b = b * a
  exact mul_comm_mod_gamma (n := 6) (r := 3) (s := 3)
    (by norm_num) (by norm_num) (by norm_num) ha hb

theorem gammaThree_mul_zpow
    {a b : G} (ha : a ∈ gamma G 3) (hb : b ∈ gamma G 3) (v : ℤ) :
    ModGammaSix ((a * b) ^ v) (a ^ v * b ^ v) := by
  change (((a * b) ^ v : G) : G ⧸ gamma G 6) =
    ((a ^ v * b ^ v : G) : G ⧸ gamma G 6)
  rw [QuotientGroup.mk_zpow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
  exact (gamma_three_commute_quotient ha hb).mul_zpow v

theorem gammaThree_interchange
    {a b c d : G} (hb : b ∈ gamma G 3) (hc : c ∈ gamma G 3) :
    ModGammaSix ((a * b) * (c * d)) ((a * c) * (b * d)) := by
  change (((a * b) * (c * d) : G) : G ⧸ gamma G 6) =
    (((a * c) * (b * d) : G) : G ⧸ gamma G 6)
  have hcomm := gamma_three_commute_quotient hb hc
  calc
    ((a * b) * (c * d) : G ⧸ gamma G 6) = a * (b * c) * d := by group
    _ = a * (c * b) * d := by rw [hcomm.eq]
    _ = (a * c) * (b * d) := by group

theorem listProd_zpow_gammaThree
    (xs : List G) (hxs : ∀ x ∈ xs, x ∈ gamma G 3) (v : ℤ) :
    ModGammaSix (xs.prod ^ v) ((xs.map fun x => x ^ v).prod) := by
  induction xs with
  | nil =>
      simpa only [List.prod_nil, List.map_nil, one_zpow] using
        ModEq.refl (gamma G 6) (1 : G)
  | cons x xs ih =>
      have hx : x ∈ gamma G 3 := hxs x (by simp)
      have htail : xs.prod ∈ gamma G 3 :=
        Tahara.listProd_mem (gamma G 3) xs fun y hy => hxs y (by simp [hy])
      simp only [List.prod_cons, List.map_cons]
      exact (gammaThree_mul_zpow hx htail v).trans <|
        (ModEq.refl (gamma G 6) (x ^ v)).mul
          (ih fun y hy => hxs y (by simp [hy]))

theorem orderedProduct_zpow_gammaThree
    {n : ℕ} (f : Fin n → G) (hf : ∀ i, f i ∈ gamma G 3) (v : ℤ) :
    ModGammaSix (Tahara.orderedProduct f ^ v)
      (Tahara.orderedProduct fun i => f i ^ v) := by
  unfold Tahara.orderedProduct
  simpa [List.map_map] using listProd_zpow_gammaThree
    ((List.finRange n).map f)
    (fun x hx => by
      rcases List.mem_map.mp hx with ⟨i, hi, rfl⟩
      exact hf i) v

theorem listProd_pointwise_mul_gammaThree
    {ι : Type*} (is : List ι) (f g : ι → G)
    (hf : ∀ i ∈ is, f i ∈ gamma G 3)
    (hg : ∀ i ∈ is, g i ∈ gamma G 3) :
    ModGammaSix
      ((is.map fun i => f i * g i).prod)
      ((is.map f).prod * (is.map g).prod) := by
  induction is with
  | nil =>
      simpa only [List.prod_nil, List.map_nil, one_mul] using
        ModEq.refl (gamma G 6) (1 : G)
  | cons i is ih =>
      have hfi := hf i (by simp)
      have hgi := hg i (by simp)
      have hftail : (is.map f).prod ∈ gamma G 3 :=
        Tahara.listProd_mem (gamma G 3) (is.map f) fun x hx => by
          rcases List.mem_map.mp hx with ⟨j, hj, rfl⟩
          exact hf j (by simp [hj])
      simp only [List.map_cons, List.prod_cons]
      have hind := ih (fun j hj => hf j (by simp [hj]))
        (fun j hj => hg j (by simp [hj]))
      exact ((ModEq.refl (gamma G 6) (f i * g i)).mul hind).trans <|
        gammaThree_interchange hgi hftail

theorem orderedProduct_pointwise_mul_gammaThree
    {n : ℕ} (f g : Fin n → G)
    (hf : ∀ i, f i ∈ gamma G 3) (hg : ∀ i, g i ∈ gamma G 3) :
    ModGammaSix
      (Tahara.orderedProduct fun i => f i * g i)
      (Tahara.orderedProduct f * Tahara.orderedProduct g) := by
  unfold Tahara.orderedProduct
  simpa [List.map_map] using listProd_pointwise_mul_gammaThree
    (List.finRange n) f g (fun i hi => hf i) (fun i hi => hg i)

/-- Fubini reindexing for two finite ordered products of elements of `γ₃`.
The relative order inside each row or column is retained; commutation modulo
`γ₆` permits exchanging the two loops. -/
theorem listProd_listProd_swap_gammaThree
    {ι κ : Type*} (is : List ι) (js : List κ) (f : ι → κ → G)
    (hf : ∀ i ∈ is, ∀ j ∈ js, f i j ∈ gamma G 3) :
    ModGammaSix
      ((is.map fun i => (js.map fun j => f i j).prod).prod)
      ((js.map fun j => (is.map fun i => f i j).prod).prod) := by
  induction is with
  | nil =>
      change ((1 : G) : G ⧸ gamma G 6) =
        (((js.map fun _ => (1 : G)).prod : G) : G ⧸ gamma G 6)
      induction js with
      | nil => simp
      | cons j js ih => simp [ih]
  | cons i is ih =>
      let row : κ → G := fun j => f i j
      let cols : κ → G := fun j => (is.map fun k => f k j).prod
      have hrow : ∀ j ∈ js, row j ∈ gamma G 3 := fun j hj =>
        hf i (by simp) j hj
      have hcols : ∀ j ∈ js, cols j ∈ gamma G 3 := by
        intro j hj
        apply Tahara.listProd_mem
        intro x hx
        rcases List.mem_map.mp hx with ⟨k, hk, rfl⟩
        exact hf k (by simp [hk]) j hj
      have hind := ih (fun k hk j hj => hf k (by simp [hk]) j hj)
      have hrows : ModGammaSix
          ((js.map fun j => row j * cols j).prod)
          ((js.map row).prod * (js.map cols).prod) :=
        listProd_pointwise_mul_gammaThree js row cols hrow hcols
      simp only [List.map_cons, List.prod_cons]
      exact ((ModEq.refl (gamma G 6) ((js.map row).prod)).mul hind).trans <| by
        simpa only [row, cols, List.map_map] using hrows.symm

theorem orderedProduct_orderedProduct_swap_gammaThree
    {m n : ℕ} (f : Fin m → Fin n → G)
    (hf : ∀ i j, f i j ∈ gamma G 3) :
    ModGammaSix
      (Tahara.orderedProduct fun i => Tahara.orderedProduct fun j => f i j)
      (Tahara.orderedProduct fun j => Tahara.orderedProduct fun i => f i j) := by
  unfold Tahara.orderedProduct
  simpa [List.map_map] using listProd_listProd_swap_gammaThree
    (List.finRange m) (List.finRange n) f
    (fun i hi j hj => hf i j)

/-- Exact collection of powers of one element.  No nilpotency assumption is
needed because powers of the same element commute. -/
theorem listProd_zpow_same_base (a : G) (zs : List ℤ) :
    (zs.map fun z => a ^ z).prod = a ^ zs.sum := by
  induction zs with
  | nil => simp
  | cons z zs ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons, ih]
      rw [zpow_add]

theorem orderedProduct_zpow_same_base
    {n : ℕ} (a : G) (e : Fin n → ℤ) :
    Tahara.orderedProduct (fun i => a ^ e i) = a ^ ∑ i, e i := by
  unfold Tahara.orderedProduct
  rw [show (List.finRange n).map (fun i => a ^ e i) =
      (((List.finRange n).map e).map fun z => a ^ z) by simp [List.map_map]]
  rw [listProd_zpow_same_base]
  congr 1

theorem orderedProductWhere_zpow_same_base
    {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (a : G) (e : Fin n → ℤ) :
    Tahara.orderedProductWhere p (fun i => a ^ e i) =
      a ^ ∑ i ∈ Finset.univ.filter p, e i := by
  unfold Tahara.orderedProductWhere
  let is := (List.finRange n).filter p
  rw [show is.map (fun i => a ^ e i) =
      ((is.map e).map fun z => a ^ z) by simp [List.map_map]]
  rw [listProd_zpow_same_base]
  congr 1

end

end D5
