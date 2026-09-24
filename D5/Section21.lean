import D5.Section20

/-!
# Section 21: cancellation of the corrected exponent products

Formulas (78) and (79) combine the four cancellations already established
in Sections 19 and 20.  Their polynomial expansions and every triangular
reindexing are checked explicitly below.
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- The complete corrected product of exponents on the left side of (78). -/
def formula78Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l : Fin C.r) : ℤ :=
  ∑ i,
    ((∑ p, C.b i p * lambda C ξ p l) -
        TaharaArithmetic.binom2 (C.d i) * eta C ξ i l) *
      ((∑ p, P.v i p * lambda C ξ p l) +
        (∑ j ∈ Finset.univ.filter (i < ·), P.w i j j * eta C ξ j l) +
        (∑ h ∈ Finset.univ.filter (· < i), P.w'' h h i * eta C ξ h l))

/-- The last strict-pair sum in the expansion (78). -/
def formula78Last
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l : Fin C.r) : ℤ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    (TaharaArithmetic.binom2 (C.d i) * P.w i j j +
      TaharaArithmetic.binom2 (C.d j) * P.w'' i i j) *
        eta C ξ i l * eta C ξ j l

/-- The exact integer identity displayed before the final congruence in
formula (78). -/
theorem formula78_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l : Fin C.r) :
    formula78Left C P ξ l =
      formula70Left C P ξ l + formula76Right C P ξ l -
        formula76Left C P ξ l - formula78Last C P ξ l := by
  let A : Fin C.s → ℤ := fun i => ∑ p, C.b i p * lambda C ξ p l
  let V : Fin C.s → ℤ := fun i => ∑ p, P.v i p * lambda C ξ p l
  let E : Fin C.s → ℤ := fun i =>
    TaharaArithmetic.binom2 (C.d i) * eta C ξ i l
  have hAlow := sum_lower_reindex
    (fun h i => A i * (P.w'' h h i * eta C ξ h l))
  have hElow := sum_lower_reindex
    (fun h i => E i * (P.w'' h h i * eta C ξ h l))
  rw [formula78Left, formula70Left, formula76Right, formula76Left,
    formula78Last]
  change
    (∑ i, (A i - E i) *
      (V i + (∑ j ∈ Finset.univ.filter (i < ·),
        P.w i j j * eta C ξ j l) +
        (∑ h ∈ Finset.univ.filter (· < i),
          P.w'' h h i * eta C ξ h l))) = _
  simp_rw [sub_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib]
  rw [hAlow, hElow]
  dsimp [A, V, E]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The coefficient of the last strict-pair sum in (78)--(79) is divisible
by `d(i)`, by the two relevant consequences of condition (14). -/
theorem formula78_pair_coefficient_dvd
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    {i j : Fin C.s} (hij : i < j) :
    orderInt C.d i ∣
      TaharaArithmetic.binom2 (C.d i) * P.w i j j +
        TaharaArithmetic.binom2 (C.d j) * P.w'' i i j := by
  have hp := pairConsequences C P hP hij
  apply dvd_add
  · simpa [mul_comm] using hp.dvd14_wijj
  · simpa [mul_comm] using hp.dvd14_wppiij

/-- The last line of (78) vanishes modulo `f(l)`. -/
theorem formula78_last_dvd
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (l : Fin C.r) :
    orderInt C.f l ∣ formula78Last C P ξ l := by
  unfold formula78Last
  apply Finset.dvd_sum
  intro i hi
  apply Finset.dvd_sum
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  rcases formula78_pair_coefficient_dvd C P hP hij with ⟨z, hz⟩
  rcases formula66_eta C ξ i l with ⟨q, hq⟩
  refine ⟨z * eta C ξ j l * q, ?_⟩
  rw [hz]
  calc
    orderInt C.d i * z * eta C ξ i l * eta C ξ j l =
        (orderInt C.d i * eta C ξ i l) *
          (z * eta C ξ j l) := by ring
    _ = orderInt C.f l * q * (z * eta C ξ j l) := by rw [hq]
    _ = orderInt C.f l * (z * eta C ξ j l * q) := by ring

/-- Formula (78). -/
theorem formula78
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) (l : Fin C.r) :
    orderInt C.f l ∣ formula78Left C P ξ l := by
  rw [formula78_expansion C P ξ l]
  have h70 := formula70 C P hP ξ l
  have h76 : orderInt C.f l ∣
      formula76Right C P ξ l - formula76Left C P ξ l :=
    (formula76 C P hP ξ l).dvd
  have hlast := formula78_last_dvd C P hP ξ l
  have hsum := dvd_add h70 h76
  have hsub := Int.dvd_sub hsum hlast
  convert hsub using 1 <;> ring

/-- The complete symmetric two-coordinate product on the left side of
formula (79). -/
def formula79Left
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) : ℤ :=
  ∑ i,
    (((∑ p, C.b i p * lambda C ξ p l) -
        TaharaArithmetic.binom2 (C.d i) * eta C ξ i l) *
      ((∑ p, P.v i p * lambda C ξ p m) +
        (∑ j ∈ Finset.univ.filter (i < ·), P.w i j j * eta C ξ j m) +
        (∑ h ∈ Finset.univ.filter (· < i), P.w'' h h i * eta C ξ h m)) +
    ((∑ p, C.b i p * lambda C ξ p m) -
        TaharaArithmetic.binom2 (C.d i) * eta C ξ i m) *
      ((∑ p, P.v i p * lambda C ξ p l) +
        (∑ j ∈ Finset.univ.filter (i < ·), P.w i j j * eta C ξ j l) +
        (∑ h ∈ Finset.univ.filter (· < i), P.w'' h h i * eta C ξ h l)))

/-- The last strict-pair sum in formula (79). -/
def formula79Last
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) : ℤ :=
  ∑ i, ∑ j ∈ Finset.univ.filter (i < ·),
    (TaharaArithmetic.binom2 (C.d i) * P.w i j j +
      TaharaArithmetic.binom2 (C.d j) * P.w'' i i j) *
      (eta C ξ i l * eta C ξ j m + eta C ξ i m * eta C ξ j l)

/-- Exact expansion in formula (79). -/
theorem formula79_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G)
    (l m : Fin C.r) :
    formula79Left C P ξ l m =
      formula71Left C P ξ l m + formula77Right C P ξ l m -
        formula77Left C P ξ l m - formula79Last C P ξ l m := by
  let A : Fin C.s → Fin C.r → ℤ := fun i k =>
    ∑ p, C.b i p * lambda C ξ p k
  let V : Fin C.s → Fin C.r → ℤ := fun i k =>
    ∑ p, P.v i p * lambda C ξ p k
  let E : Fin C.s → Fin C.r → ℤ := fun i k =>
    TaharaArithmetic.binom2 (C.d i) * eta C ξ i k
  have hAlowL := sum_lower_reindex
    (fun h i => A i l * (P.w'' h h i * eta C ξ h m))
  have hAlowM := sum_lower_reindex
    (fun h i => A i m * (P.w'' h h i * eta C ξ h l))
  have hElowL := sum_lower_reindex
    (fun h i => E i l * (P.w'' h h i * eta C ξ h m))
  have hElowM := sum_lower_reindex
    (fun h i => E i m * (P.w'' h h i * eta C ξ h l))
  rw [formula79Left, formula71Left, formula77Right, formula77Left,
    formula79Last]
  change
    (∑ i,
      ((A i l - E i l) *
        (V i m + (∑ j ∈ Finset.univ.filter (i < ·),
          P.w i j j * eta C ξ j m) +
          (∑ h ∈ Finset.univ.filter (· < i),
            P.w'' h h i * eta C ξ h m)) +
      (A i m - E i m) *
        (V i l + (∑ j ∈ Finset.univ.filter (i < ·),
          P.w i j j * eta C ξ j l) +
          (∑ h ∈ Finset.univ.filter (· < i),
            P.w'' h h i * eta C ξ h l)))) = _
  simp_rw [sub_mul, mul_add, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, Finset.mul_sum]
  simp_rw [Finset.sum_add_distrib]
  rw [hAlowL, hAlowM, hElowL, hElowM]
  dsimp [A, V, E]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]
  simp_rw [Finset.mul_sum]
  simp only [mul_left_comm]
  ring

/-- The last line of (79) vanishes modulo `f(l)` for `l < m`. -/
theorem formula79_last_dvd
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {l m : Fin C.r} (hlm : l < m) :
    orderInt C.f l ∣ formula79Last C P ξ l m := by
  have hfm : orderInt C.f l ∣ orderInt C.f m := by
    rcases C.f_dvd l m hlm.le with ⟨z, hz⟩
    refine ⟨(z : ℤ), ?_⟩
    change (C.f m : ℤ) = (C.f l : ℤ) * (z : ℤ)
    exact_mod_cast hz
  unfold formula79Last
  apply Finset.dvd_sum
  intro i hi
  apply Finset.dvd_sum
  intro j hj
  have hij : i < j := (Finset.mem_filter.mp hj).2
  rcases formula78_pair_coefficient_dvd C P hP hij with ⟨z, hz⟩
  rw [hz, mul_add]
  apply dvd_add
  · rcases formula66_eta C ξ i l with ⟨q, hq⟩
    refine ⟨z * eta C ξ j m * q, ?_⟩
    calc
      orderInt C.d i * z * (eta C ξ i l * eta C ξ j m) =
          (orderInt C.d i * eta C ξ i l) *
            (z * eta C ξ j m) := by ring
      _ = orderInt C.f l * q * (z * eta C ξ j m) := by rw [hq]
      _ = orderInt C.f l * (z * eta C ξ j m * q) := by ring
  · have him : orderInt C.f l ∣ orderInt C.d i * eta C ξ i m :=
      dvd_trans hfm (formula66_eta C ξ i m)
    rcases him with ⟨q, hq⟩
    refine ⟨z * eta C ξ j l * q, ?_⟩
    calc
      orderInt C.d i * z * (eta C ξ i m * eta C ξ j l) =
          (orderInt C.d i * eta C ξ i m) *
            (z * eta C ξ j l) := by ring
      _ = orderInt C.f l * q * (z * eta C ξ j l) := by rw [hq]
      _ = orderInt C.f l * (z * eta C ξ j l * q) := by ring

/-- Formula (79). -/
theorem formula79
    (C : Context G) (P : Parameters C.s C.t) (hP : P.Satisfies)
    (ξ : G) {l m : Fin C.r} (hlm : l < m) :
    orderInt C.f l ∣ formula79Left C P ξ l m := by
  rw [formula79_expansion C P ξ l m]
  have h71 := formula71 C P hP ξ hlm
  have h77 : orderInt C.f l ∣
      formula77Right C P ξ l m - formula77Left C P ξ l m :=
    (formula77 C P hP ξ hlm).dvd
  have hlast := formula79_last_dvd C P hP ξ hlm
  have hsum := dvd_add h71 h77
  have hsub := Int.dvd_sub hsum hlast
  convert hsub using 1 <;> ring

end

end D5.Tahara
