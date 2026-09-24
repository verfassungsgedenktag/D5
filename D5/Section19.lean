import D5.Section18

/-!
# Section 19: Tahara conditions (14) and (15)

This file verifies the two coordinate cancellations (70)--(71).  In
particular, the finite sums are expanded and partitioned into their diagonal
and strict-pair parts inside Lean; the displayed identities are not taken as
additional assumptions.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Reindex a product of two finite linear combinations. -/
theorem sum_product_reindex
    {s t : ℕ} (a b : Fin s → Fin t → ℤ) (x y : Fin t → ℤ) :
    (∑ i, (∑ p, a i p * x p) * (∑ q, b i q * y q)) =
      ∑ p, ∑ q, (∑ i, a i p * b i q) * (x p * y q) := by
  simp_rw [Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  calc
    ∑ i, a i p * x p * (b i q * y q) =
        ∑ i, (a i p * b i q) * (x p * y q) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = (∑ i, a i p * b i q) * (x p * y q) := by
      rw [Finset.sum_mul]

/-- Partition a square finite sum into its diagonal and the two
orientations of every strict pair. -/
theorem sum_square_partition
    {n : ℕ} (F : Fin n → Fin n → ℤ) :
    (∑ p, ∑ q, F p q) =
      (∑ p, F p p) +
        ∑ p, ∑ q ∈ Finset.univ.filter (p < ·), (F p q + F q p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hi := ih (fun p q => F p.succ q.succ)
      simp_rw [Finset.sum_filter] at hi ⊢
      simp_rw [Fin.sum_univ_succ]
      simp only [Fin.succ_pos, if_pos, Fin.not_lt_zero, if_false,
        Fin.succ_lt_succ_iff]
      simp only [Finset.sum_add_distrib, zero_add]
      rw [hi]
      ring

def formula70Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (l : Fin C.r) : ℤ :=
  ∑ i,
    (∑ p, C.b i p * lambda C ξ p l) *
      (∑ p, P.v i p * lambda C ξ p l)

def formula70Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (l : Fin C.r) : ℤ :=
  (∑ p, (∑ i, C.b i p * P.v i p) * lambda C ξ p l ^ 2) +
    ∑ p, ∑ q ∈ Finset.univ.filter (p < ·),
      (∑ i, (C.b i p * P.v i q + C.b i q * P.v i p)) *
        (lambda C ξ p l * lambda C ξ q l)

/-- The displayed integer expansion in formula (70). -/
theorem formula70_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) (l : Fin C.r) :
    formula70Left C P ξ l = formula70Right C P ξ l := by
  let L : Fin C.t → ℤ := fun p => lambda C ξ p l
  have hreindex := sum_product_reindex C.b P.v L L
  have hpartition := sum_square_partition
    (fun p q => (∑ i, C.b i p * P.v i q) * (L p * L q))
  rw [formula70Left, formula70Right]
  change (∑ i, (∑ p, C.b i p * L p) * (∑ p, P.v i p * L p)) = _
  rw [hreindex, hpartition]
  congr 1
  · apply Finset.sum_congr rfl
    intro p hp
    dsimp [L]
    ring
  · apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.sum_add_distrib]
    ring

/-- Formula (70): the complete diagonal and off-diagonal exponent sum is
zero modulo the order of the `l`-th `x₃` coordinate. -/
theorem formula70
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (l : Fin C.r) :
    orderInt C.f l ∣ formula70Left C P ξ l := by
  rw [formula70_expansion C P ξ l, formula70Right]
  rcases hP with
    ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  apply dvd_add
  · apply Finset.dvd_sum
    intro p hp
    have hcoef : orderInt C.e p ∣ ∑ i, C.b i p * P.v i p := by
      have hraw := Int.modEq_zero_iff_dvd.mp (h14 p)
      simpa [mul_comm] using hraw
    rcases hcoef with ⟨k, hk⟩
    rcases formula66_lambda C ξ p l with ⟨z, hz⟩
    refine ⟨k * lambda C ξ p l * z, ?_⟩
    rw [hk]
    calc
      orderInt C.e p * k * lambda C ξ p l ^ 2 =
          (orderInt C.e p * lambda C ξ p l) *
            (k * lambda C ξ p l) := by ring
      _ = orderInt C.f l * z * (k * lambda C ξ p l) := by rw [hz]
      _ = orderInt C.f l * (k * lambda C ξ p l * z) := by ring
  · apply Finset.dvd_sum
    intro p hp
    apply Finset.dvd_sum
    intro q hq
    have hpq : p < q := (Finset.mem_filter.mp hq).2
    have hcoef : orderInt C.e p ∣
        ∑ i, (C.b i p * P.v i q + C.b i q * P.v i p) := by
      have hraw := Int.modEq_zero_iff_dvd.mp (h15 p q hpq)
      simpa [add_comm, mul_comm] using hraw
    rcases hcoef with ⟨k, hk⟩
    rcases formula66_lambda C ξ p l with ⟨z, hz⟩
    refine ⟨k * lambda C ξ q l * z, ?_⟩
    rw [hk]
    calc
      orderInt C.e p * k *
          (lambda C ξ p l * lambda C ξ q l) =
        (orderInt C.e p * lambda C ξ p l) *
          (k * lambda C ξ q l) := by ring
      _ = orderInt C.f l * z * (k * lambda C ξ q l) := by rw [hz]
      _ = orderInt C.f l * (k * lambda C ξ q l * z) := by ring

def formula71Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) : ℤ :=
  ∑ i,
    ((∑ p, C.b i p * lambda C ξ p l) *
        (∑ p, P.v i p * lambda C ξ p m) +
      (∑ p, C.b i p * lambda C ξ p m) *
        (∑ p, P.v i p * lambda C ξ p l))

def formula71Right
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) : ℤ :=
  2 * ∑ p, (∑ i, C.b i p * P.v i p) *
      lambda C ξ p l * lambda C ξ p m +
    ∑ p, ∑ q ∈ Finset.univ.filter (p < ·),
      (∑ i, (C.b i p * P.v i q + C.b i q * P.v i p)) *
        (lambda C ξ p l * lambda C ξ q m +
          lambda C ξ p m * lambda C ξ q l)

/-- The displayed integer expansion in formula (71). -/
theorem formula71_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) :
    formula71Left C P ξ l m = formula71Right C P ξ l m := by
  let L : Fin C.t → ℤ := fun p => lambda C ξ p l
  let M : Fin C.t → ℤ := fun p => lambda C ξ p m
  have hLM := sum_product_reindex C.b P.v L M
  have hML := sum_product_reindex C.b P.v M L
  let F : Fin C.t → Fin C.t → ℤ := fun p q =>
    (∑ i, C.b i p * P.v i q) * (L p * M q + M p * L q)
  have hpartition := sum_square_partition F
  rw [formula71Left, formula71Right]
  change (∑ i, ((∑ p, C.b i p * L p) * (∑ p, P.v i p * M p) +
    (∑ p, C.b i p * M p) * (∑ p, P.v i p * L p))) = _
  rw [Finset.sum_add_distrib, hLM, hML]
  have hcombine :
      (∑ p, ∑ q, (∑ i, C.b i p * P.v i q) * (L p * M q)) +
        (∑ p, ∑ q, (∑ i, C.b i p * P.v i q) * (M p * L q)) =
      ∑ p, ∑ q, F p q := by
    dsimp [F]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p hp
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hcombine, hpartition]
  congr 1
  · dsimp [F, L, M]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring
  · apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    dsimp [F, L, M]
    rw [Finset.sum_add_distrib]
    ring

/-- Formula (71).  The hypothesis `l < m` supplies the order divisibility
`f(l) ∣ f(m)` used for the second mixed monomial. -/
theorem formula71
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {l m : Fin C.r} (hlm : l < m) :
    orderInt C.f l ∣ formula71Left C P ξ l m := by
  rw [formula71_expansion C P ξ l m, formula71Right]
  rcases hP with
    ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hfm : orderInt C.f l ∣ orderInt C.f m := by
    rcases C.f_dvd l m hlm.le with ⟨k, hk⟩
    refine ⟨(k : ℤ), ?_⟩
    change (C.f m : ℤ) = (C.f l : ℤ) * (k : ℤ)
    exact_mod_cast hk
  apply dvd_add
  · apply dvd_mul_of_dvd_right (c := (2 : ℤ))
    apply Finset.dvd_sum
    intro p hp
    have hcoef : orderInt C.e p ∣ ∑ i, C.b i p * P.v i p := by
      have hraw := Int.modEq_zero_iff_dvd.mp (h14 p)
      simpa [mul_comm] using hraw
    rcases hcoef with ⟨k, hk⟩
    rcases formula66_lambda C ξ p l with ⟨z, hz⟩
    refine ⟨k * lambda C ξ p m * z, ?_⟩
    rw [hk]
    calc
      orderInt C.e p * k * lambda C ξ p l * lambda C ξ p m =
        (orderInt C.e p * lambda C ξ p l) *
          (k * lambda C ξ p m) := by ring
      _ = orderInt C.f l * z * (k * lambda C ξ p m) := by rw [hz]
      _ = orderInt C.f l * (k * lambda C ξ p m * z) := by ring
  · apply Finset.dvd_sum
    intro p hp
    apply Finset.dvd_sum
    intro q hq
    have hpq : p < q := (Finset.mem_filter.mp hq).2
    have hcoef : orderInt C.e p ∣
        ∑ i, (C.b i p * P.v i q + C.b i q * P.v i p) := by
      have hraw := Int.modEq_zero_iff_dvd.mp (h15 p q hpq)
      simpa [add_comm, mul_comm] using hraw
    rcases hcoef with ⟨k, hk⟩
    have hpl := formula66_lambda C ξ p l
    have hpm : orderInt C.f l ∣
        orderInt C.e p * lambda C ξ p m :=
      dvd_trans hfm (formula66_lambda C ξ p m)
    rw [hk, mul_add]
    apply dvd_add
    · rcases hpl with ⟨z, hz⟩
      refine ⟨k * lambda C ξ q m * z, ?_⟩
      calc
        orderInt C.e p * k *
            (lambda C ξ p l * lambda C ξ q m) =
          (orderInt C.e p * lambda C ξ p l) *
            (k * lambda C ξ q m) := by ring
        _ = orderInt C.f l * z * (k * lambda C ξ q m) := by rw [hz]
        _ = orderInt C.f l * (k * lambda C ξ q m * z) := by ring
    · rcases hpm with ⟨z, hz⟩
      refine ⟨k * lambda C ξ q l * z, ?_⟩
      calc
        orderInt C.e p * k *
            (lambda C ξ p m * lambda C ξ q l) =
          (orderInt C.e p * lambda C ξ p m) *
            (k * lambda C ξ q l) := by ring
        _ = orderInt C.f l * z * (k * lambda C ξ q l) := by rw [hz]
        _ = orderInt C.f l * (k * lambda C ξ q l * z) := by ring

end

end D5.Tahara
