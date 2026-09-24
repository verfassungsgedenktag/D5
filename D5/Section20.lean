import D5.Section19

/-!
# Section 20: the mixed corrections from Tahara condition (11)

The first step is formula (72), where the diagonal term in condition (11)
is removed using condition (2).  The remaining group and coordinate
consequences are developed after this exact arithmetic normalization.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The coefficient printed in formula (72), with the diagonal
`w i i i` term already removed. -/
def formula72Coefficient
    (C : Context G) (P : Parameters C.s C.t)
    (i : Fin C.s) (p : Fin C.t) : ℤ :=
  TaharaArithmetic.binom2 (C.d i) * P.v i p -
    (∑ h ∈ Finset.univ.filter (· < i), P.w h i i * C.b h p) -
    (∑ j ∈ Finset.univ.filter (i < ·), P.w'' i i j * C.b j p)

/-- A weak lower triangular sum splits into the strict lower part and its
diagonal entry. -/
theorem sum_filter_le_eq_sum_filter_lt_add
    {n : ℕ} (i : Fin n) (a : Fin n → ℤ) :
    (∑ h ∈ Finset.univ.filter (· ≤ i), a h) =
      (∑ h ∈ Finset.univ.filter (· < i), a h) + a i := by
  have hset : Finset.univ.filter (· ≤ i) =
      insert i (Finset.univ.filter (· < i)) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    omega
  rw [hset, Finset.sum_insert (by simp)]
  rw [add_comm]

/-- Formula (72), derived from condition (11) after Lean checks that the
only removed summand is zero by condition (2). -/
theorem formula72
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (i : Fin C.s) (p : Fin C.t) :
    Int.ModEq (orderGCD C.d C.e i p) (formula72Coefficient C P i p) 0 := by
  rcases hP with
    ⟨h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩
  have hsplit := sum_filter_le_eq_sum_filter_lt_add i
    (fun h => P.w h i i * C.b h p)
  have hdiag : P.w i i i * C.b i p = 0 := by rw [h2 i, zero_mul]
  have hsum :
      (∑ h ∈ Finset.univ.filter (· ≤ i), P.w h i i * C.b h p) =
        ∑ h ∈ Finset.univ.filter (· < i), P.w h i i * C.b h p := by
    rw [hsplit, hdiag, add_zero]
  have h := condition11_formula30 C P h11 i p
  simpa [condition11Coefficient, formula72Coefficient, hsum, mul_comm] using h

/-- The group word displayed in formula (73).  The two last products use
flattened integer powers, definitionally equivalent to powers of
`x₁h ^ d(h)`. -/
def formula73Word
    (C : Context G) (P : Parameters C.s C.t) (i : Fin C.s) : G :=
  ((orderedProduct (fun p => C.x2 p ^ P.v i p) ^
      TaharaArithmetic.binom2 (C.d i)) *
    orderedProductWhere (· < i) (fun h =>
      C.x1 h ^ (orderInt C.d h * (-P.w h i i)))) *
    orderedProductWhere (i < ·) (fun j =>
      C.x1 j ^ (orderInt C.d j * (-P.w'' i i j)))

/-- Formula (73): condition (11), after removal of the zero diagonal term,
places the printed word in `γ₂(G)^{d(i)} γ₃(G)`. -/
theorem formula73
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (i : Fin C.s) :
    IsGammaTwoPowerModGammaThree (orderInt C.d i)
      (formula73Word C P i) := by
  let V : Fin C.t → ℤ := fun p =>
    TaharaArithmetic.binom2 (C.d i) * P.v i p
  let A : Fin C.t → ℤ := fun p =>
    ∑ h ∈ Finset.univ.filter (· < i), (-P.w h i i) * C.b h p
  let B : Fin C.t → ℤ := fun p =>
    ∑ j ∈ Finset.univ.filter (i < ·), (-P.w'' i i j) * C.b j p
  let M : Fin C.t → ℤ := fun p => V p + A p + B p
  have hv : D5.ModEq (D5.gamma G 3)
      (orderedProduct (fun p => C.x2 p ^ P.v i p) ^
        TaharaArithmetic.binom2 (C.d i))
      (orderedProduct fun p => C.x2 p ^ V p) := by
    simpa [V, mul_comm] using coordinateProduct_zpow_mod_gamma3 C
      (P.v i) (TaharaArithmetic.binom2 (C.d i))
  have hA : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (· < i) fun h =>
        C.x1 h ^ (orderInt C.d h * (-P.w h i i)))
      (orderedProduct fun p => C.x2 p ^ A p) := by
    refine (modEq_orderedProductWhere (· < i)
      (f := fun h => C.x1 h ^ (orderInt C.d h * (-P.w h i i)))
      (g := fun h => orderedProduct fun p =>
        C.x2 p ^ ((-P.w h i i) * C.b h p)) ?_).trans ?_
    · intro h hhi
      exact x1_order_multiple_mod_gamma3 C h (-P.w h i i)
    · exact coordinateProductWhere_mod_gamma3 C (· < i)
        (fun h p => (-P.w h i i) * C.b h p)
  have hB : D5.ModEq (D5.gamma G 3)
      (orderedProductWhere (i < ·) fun j =>
        C.x1 j ^ (orderInt C.d j * (-P.w'' i i j)))
      (orderedProduct fun p => C.x2 p ^ B p) := by
    refine (modEq_orderedProductWhere (i < ·)
      (f := fun j => C.x1 j ^ (orderInt C.d j * (-P.w'' i i j)))
      (g := fun j => orderedProduct fun p =>
        C.x2 p ^ ((-P.w'' i i j) * C.b j p)) ?_).trans ?_
    · intro j hij
      exact x1_order_multiple_mod_gamma3 C j (-P.w'' i i j)
    · exact coordinateProductWhere_mod_gamma3 C (i < ·)
        (fun j p => (-P.w'' i i j) * C.b j p)
  have hcollectVA := coordinateProduct_mul_mod_gamma3 C V A
  have hcollectM := coordinateProduct_mul_mod_gamma3 C
    (fun p => V p + A p) B
  have hword : D5.ModEq (D5.gamma G 3) (formula73Word C P i)
      (orderedProduct fun p => C.x2 p ^ M p) := by
    have h := (hv.mul hA).mul hB
    exact h.trans <| by
      simpa [M] using
        (hcollectVA.mul (D5.ModEq.refl (D5.gamma G 3) _)).trans hcollectM
  have hm : ∀ p, ((Nat.gcd (C.d i) (C.e p) : ℕ) : ℤ) ∣ M p := by
    intro p
    have hc := Int.modEq_zero_iff_dvd.mp (formula72 C P hP i p)
    change ((Nat.gcd (C.d i) (C.e p) : ℕ) : ℤ) ∣
      formula72Coefficient C P i p at hc
    convert hc using 1
    dsimp [M, V, A, B, formula72Coefficient]
    simp_rw [neg_mul]
    rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
    ring
  rcases coordinateProduct_is_gammaTwoPower_mod_gammaThree C (C.d i) M hm with
    ⟨y, hy, hcoord⟩
  exact ⟨y, hy, hword.trans hcoord⟩

end

end D5.Tahara
