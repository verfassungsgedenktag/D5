import D5.Tahara
import D5.CollectionWeighted

/-!
# Collection of finite cyclic coordinates

The group calculations in condition (6) take place in the abelian layer
`γ₂/γ₃`.  This file supplies the ordered-product algebra needed to collect
each coordinate without replacing noncommutative products by `Finset.prod`.
-/

namespace D5.Tahara

universe u v

noncomputable section

variable {A : Type u} [Group A]

theorem orderedProduct_mul_of_pairwise_commute
    {n : ℕ} (x : Fin n → A) (hcomm : ∀ i j, Commute (x i) (x j))
    (a b : Fin n → ℤ) :
    orderedProduct (fun i => x i ^ a i) *
        orderedProduct (fun i => x i ^ b i) =
      orderedProduct (fun i => x i ^ (a i + b i)) := by
  unfold orderedProduct
  have aux : ∀ is : List (Fin n),
      (is.map (fun i => x i ^ a i)).prod *
          (is.map (fun i => x i ^ b i)).prod =
        (is.map (fun i => x i ^ (a i + b i))).prod := by
    intro is
    induction is with
    | nil => simp
    | cons i is ih =>
        simp only [List.map_cons, List.prod_cons]
        have hc : Commute
            ((is.map (fun j => x j ^ a j)).prod) (x i ^ b i) :=
          Commute.list_prod_left _ _ fun y hy => by
            rcases List.mem_map.mp hy with ⟨j, hj, rfl⟩
            exact (hcomm j i).zpow_zpow _ _
        calc
          (x i ^ a i * (is.map (fun j => x j ^ a j)).prod) *
              (x i ^ b i * (is.map (fun j => x j ^ b j)).prod) =
            x i ^ a i *
              ((is.map (fun j => x j ^ a j)).prod * x i ^ b i) *
                (is.map (fun j => x j ^ b j)).prod := by group
          _ = x i ^ a i *
              (x i ^ b i * (is.map (fun j => x j ^ a j)).prod) *
                (is.map (fun j => x j ^ b j)).prod := by rw [hc.eq]
          _ =
            (x i ^ a i * x i ^ b i) *
              ((is.map (fun j => x j ^ a j)).prod *
                (is.map (fun j => x j ^ b j)).prod) := by group
          _ = x i ^ (a i + b i) *
              (is.map (fun j => x j ^ (a j + b j))).prod := by rw [zpow_add, ih]
  exact aux (List.finRange n)

theorem orderedProduct_zpow_of_pairwise_commute
    {n : ℕ} (x : Fin n → A) (hcomm : ∀ i j, Commute (x i) (x j))
    (a : Fin n → ℤ) (z : ℤ) :
    orderedProduct (fun i => x i ^ a i) ^ z =
      orderedProduct (fun i => x i ^ (z * a i)) := by
  induction z using Int.induction_on with
  | zero => simp [orderedProduct]
  | succ z ih =>
      rw [zpow_add_one, ih,
        orderedProduct_mul_of_pairwise_commute x hcomm]
      apply congrArg orderedProduct
      funext i
      congr 1
      ring
  | pred z ih =>
      rw [zpow_sub_one, ih]
      have hinv : (orderedProduct fun i => x i ^ a i)⁻¹ =
          orderedProduct (fun i => x i ^ (-a i)) := by
        have hmul := orderedProduct_mul_of_pairwise_commute x hcomm a (fun i => -a i)
        have hone : orderedProduct (fun i => x i ^ (a i + -a i)) = 1 := by
          simp [orderedProduct]
        have hprod := hmul.trans hone
        calc
          (orderedProduct fun i => x i ^ a i)⁻¹ =
              (orderedProduct fun i => x i ^ a i)⁻¹ *
                ((orderedProduct fun i => x i ^ a i) *
                  orderedProduct fun i => x i ^ (-a i)) := by rw [hprod]; simp
          _ = orderedProduct (fun i => x i ^ (-a i)) := by group
      rw [hinv, orderedProduct_mul_of_pairwise_commute x hcomm]
      apply congrArg orderedProduct
      funext i
      congr 1
      ring

theorem listProduct_coordinates_of_pairwise_commute
    {n : ℕ} (x : Fin n → A) (hcomm : ∀ i j, Commute (x i) (x j))
    {ι : Type v} (is : List ι) (a : ι → Fin n → ℤ) :
    (is.map (fun k => orderedProduct fun p => x p ^ a k p)).prod =
      orderedProduct (fun p => x p ^ (is.map fun k => a k p).sum) := by
  induction is with
  | nil => simp [orderedProduct]
  | cons i is ih =>
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      rw [ih, orderedProduct_mul_of_pairwise_commute x hcomm]

theorem orderedProductWhere_coordinates_of_pairwise_commute
    {n m : ℕ} (x : Fin m → A) (hcomm : ∀ i j, Commute (x i) (x j))
    (p : Fin n → Prop) [DecidablePred p] (a : Fin n → Fin m → ℤ) :
    orderedProductWhere p (fun i => orderedProduct fun k => x k ^ a i k) =
      orderedProduct (fun k => x k ^
        (∑ i ∈ Finset.univ.filter p, a i k)) := by
  unfold orderedProductWhere
  rw [listProduct_coordinates_of_pairwise_commute x hcomm]
  apply congrArg orderedProduct
  funext k
  congr 1

theorem orderedProduct_coordinates_of_pairwise_commute
    {n m : ℕ} (x : Fin m → A) (hcomm : ∀ i j, Commute (x i) (x j))
    (a : Fin n → Fin m → ℤ) :
    orderedProduct (fun i => orderedProduct fun k => x k ^ a i k) =
      orderedProduct (fun k => x k ^ (∑ i, a i k)) := by
  change ((List.finRange n).map
      (fun i => orderedProduct fun k => x k ^ a i k)).prod = _
  rw [listProduct_coordinates_of_pairwise_commute x hcomm]
  apply congrArg orderedProduct
  funext k
  congr 1

end

end D5.Tahara
