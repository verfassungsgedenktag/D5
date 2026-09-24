import D5.Congruence
import D5.TaharaArithmetic
import Mathlib.Data.Finset.Order
import Mathlib.Data.List.FinRange

/-!
# Tahara's description of the fifth dimension subgroup

This file is a direct formal statement of Theorem 4.3.3 from the cited
source.  The mathematical theorem itself is recorded as one named axiom, as
agreed for this project.  Everything surrounding that axiom -- the finite
cyclic-coordinate context, the word (4.3.1), and conditions (4.3.2)--(4.3.15)
-- is represented explicitly in Lean.

The printed statement has three index-range slips which are resolved by the
parameter declarations immediately above it (and by every subsequent use):
the first product in (4.3.1) has `i < j`, condition (4.3.10) has `k ≤ s`, and
condition (4.3.13) has `l ≤ r` (called `u` in the cited source).  These are the
well-typed ranges used below and in the working proof.

The source uses a cyclic basis for each of

* `G / gamma G 2`,
* `gamma G 2 / gamma G 3`, and
* `gamma G 3 / gamma G 4`.

`IsCyclicBasis` spells this out by unique normal forms with exponents in the
specified ranges.  Congruence is equality in the appropriate quotient.
-/

namespace D5.Tahara

open scoped BigOperators

universe u

noncomputable section

variable {G : Type u} [Group G]

/-- Product in the canonical order `0, ..., n-1`.  Unlike `Finset.prod`,
this definition is valid in a noncommutative group. -/
def orderedProduct {n : ℕ} (f : Fin n → G) : G :=
  ((List.finRange n).map f).prod

/-- Ordered product over those indices satisfying `p`. -/
def orderedProductWhere {n : ℕ} (p : Fin n → Prop) [DecidablePred p]
    (f : Fin n → G) : G :=
  (((List.finRange n).filter p).map f).prod

theorem orderedProduct_mem (H : Subgroup G) {n : ℕ} (f : Fin n → G)
    (hf : ∀ i, f i ∈ H) : orderedProduct f ∈ H := by
  unfold orderedProduct
  have aux : ∀ xs : List (Fin n), (∀ i ∈ xs, f i ∈ H) → (xs.map f).prod ∈ H := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
        intro h
        simp only [List.map_cons, List.prod_cons]
        exact H.mul_mem (h i (by simp)) (ih fun j hj => h j (by simp [hj]))
  exact aux (List.finRange n) fun i hi => hf i

theorem listProd_mem (H : Subgroup G) (xs : List G)
    (hxs : ∀ x ∈ xs, x ∈ H) : xs.prod ∈ H := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.prod_cons]
      exact H.mul_mem (hxs x (by simp)) (ih fun y hy => hxs y (by simp [hy]))

theorem orderedProductWhere_mem (H : Subgroup G) {n : ℕ}
    (p : Fin n → Prop) [DecidablePred p] (f : Fin n → G)
    (hf : ∀ i, p i → f i ∈ H) : orderedProductWhere p f ∈ H := by
  unfold orderedProductWhere
  have aux : ∀ xs : List (Fin n), (∀ i ∈ xs, p i → f i ∈ H) →
      (((xs.filter p).map f).prod : G) ∈ H := by
    intro xs
    induction xs with
    | nil => simp
    | cons i xs ih =>
        intro h
        by_cases hi : p i
        · rw [List.filter_cons_of_pos (p := fun b => decide (p b))
            (decide_eq_true hi)]
          simp only [List.map_cons, List.prod_cons]
          exact H.mul_mem (h i (by simp) hi)
            (ih fun j hj hjp => h j (by simp [hj]) hjp)
        · rw [List.filter_cons_of_neg (p := fun b => decide (p b))
            (by simp [decide_eq_false hi])]
          exact ih fun j hj hjp => h j (by simp [hj]) hjp
  exact aux (List.finRange n) fun i hi hip => hf i hip

/-- A finite ordered family is a cyclic basis for `H / K`, with the listed
orders, when every coset has a unique ordered normal form. -/
def IsCyclicBasis {n : ℕ} (H K : Subgroup G) [K.Normal]
    (x : Fin n → G) (order : Fin n → ℕ) : Prop :=
  (∀ i, x i ∈ H) ∧
  (∀ i, x i ∉ K) ∧
  (∀ i, 1 < order i) ∧
  ∀ y, y ∈ H → ∃! a : ∀ i, Fin (order i),
    D5.ModEq K y (orderedProduct fun i => x i ^ (a i).val)

/-- Integer cast of a cyclic factor order. -/
def orderInt {n : ℕ} (d : Fin n → ℕ) (i : Fin n) : ℤ :=
  d i

/-- The integral ratio `d(j) / d(i)`.  Contexts separately assert the
divisibility which makes this the exact quotient used by Tahara. -/
def orderRatio {n : ℕ} (d : Fin n → ℕ) (i j : Fin n) : ℤ :=
  ((d j / d i : ℕ) : ℤ)

/-- The modulus `gcd(d(i),e(k))`, cast to the integers. -/
def orderGCD {m n : ℕ} (d : Fin m → ℕ) (e : Fin n → ℕ)
    (i : Fin m) (k : Fin n) : ℤ :=
  Nat.gcd (d i) (e k)

/-- All group-theoretic coordinate data preceding Theorem 4.3.3.

The three global divisibility fields are the transitive form of the source's
adjacent divisibility chains.  The structural relations are equations (1)--
(3) of the working proof, i.e. the relations immediately before Theorem
4.3.3, written as quotient congruences modulo `gamma G 4`.
-/
structure Context (G : Type u) [Group G] where
  s : ℕ
  t : ℕ
  r : ℕ
  x1 : Fin s → G
  x2 : Fin t → G
  x3 : Fin r → G
  d : Fin s → ℕ
  e : Fin t → ℕ
  f : Fin r → ℕ
  b : Fin s → Fin t → ℤ
  c : Fin s → Fin r → ℤ
  delta : Fin t → Fin r → ℤ
  alpha : Fin s → Fin s → Fin r → ℤ
  basis1 : IsCyclicBasis (⊤ : Subgroup G) (D5.gamma G 2) x1 d
  basis2 : IsCyclicBasis (D5.gamma G 2) (D5.gamma G 3) x2 e
  basis3 : IsCyclicBasis (D5.gamma G 3) (D5.gamma G 4) x3 f
  d_dvd : ∀ i j, i ≤ j → d i ∣ d j
  e_dvd : ∀ i j, i ≤ j → e i ∣ e j
  f_dvd : ∀ i j, i ≤ j → f i ∣ f j
  alpha_diag : ∀ i l, alpha i i l = 0
  x1_power : ∀ i, D5.ModEq (D5.gamma G 4)
    (x1 i ^ orderInt d i)
    (orderedProduct (fun p => x2 p ^ b i p) *
      orderedProduct fun l => x3 l ^ c i l)
  x2_power : ∀ p, D5.ModEq (D5.gamma G 4)
    (x2 p ^ orderInt e p) (orderedProduct fun l => x3 l ^ delta p l)
  /-- The order relation in the cyclic quotient `γ₃/γ₄`.  It is recorded
  explicitly because the chosen normal-form predicate alone only encodes
  representatives, whereas formulas (27)--(28) use this power membership. -/
  x3_order_power : ∀ l, x3 l ^ orderInt f l ∈ D5.gamma G 4
  x1_power_comm : ∀ i j, i < j → D5.ModEq (D5.gamma G 4)
    (D5.paperComm (x1 i ^ orderInt d i) (x1 j))
    (orderedProduct fun l => x3 l ^ alpha i j l)

/-- The six integer parameter families occurring in Theorem 4.3.3.  Values
outside the index ranges used by the theorem are harmless and ignored. -/
structure Parameters (s t : ℕ) where
  u : Fin s → Fin s → ℤ
  v : Fin s → Fin t → ℤ
  v' : Fin s → Fin t → ℤ
  w : Fin s → Fin s → Fin s → ℤ
  w' : Fin s → Fin s → Fin s → ℤ
  w'' : Fin s → Fin s → Fin s → ℤ

namespace Parameters

variable {C : Context G}

/-- Condition (4.3.2). -/
def Condition2 (P : Parameters C.s C.t) : Prop :=
  ∀ i, P.w i i i = 0

/-- Condition (4.3.3). -/
def Condition3 (P : Parameters C.s C.t) : Prop :=
  ∀ i j, i < j →
    P.u i j * orderRatio C.d i j * TaharaArithmetic.binom2 (C.d i) +
      P.w i i j * orderInt C.d i + P.w'' i i j * orderInt C.d j = 0

/-- Condition (4.3.4). -/
def Condition4 (P : Parameters C.s C.t) : Prop :=
  ∀ i j, i < j →
    -P.u i j * TaharaArithmetic.binom2 (C.d j) +
      P.w i j j * orderInt C.d i + P.w' i j j * orderInt C.d j = 0

/-- Condition (4.3.5). -/
def Condition5 (P : Parameters C.s C.t) : Prop :=
  ∀ i j k, i < j → j < k →
    P.w i j k * orderInt C.d i + P.w' i j k * orderInt C.d j +
      P.w'' i j k * orderInt C.d k = 0

/-- Condition (4.3.6). -/
def Condition6 (P : Parameters C.s C.t) : Prop :=
  ∀ i k,
    (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.b h k) -
      (∑ h ∈ Finset.univ.filter (· < i),
        P.u h i * orderRatio C.d h i * C.b h k) +
      P.v i k * orderInt C.d i + P.v' i k * orderInt C.e k = 0

/-- Condition (4.3.7). -/
def Condition7 (P : Parameters C.s C.t) : Prop :=
  ∀ i j, i < j → Int.ModEq (orderInt C.d i)
    (P.u i j * orderRatio C.d i j * TaharaArithmetic.binom3 (C.d i) +
      P.w i i j * TaharaArithmetic.binom2 (C.d i)) 0

/-- Condition (4.3.8). -/
def Condition8 (P : Parameters C.s C.t) : Prop :=
  ∀ i j, i < j → Int.ModEq (orderInt C.d i)
    (P.w i i j * TaharaArithmetic.binom2 (C.d i) +
      P.w'' i i j * TaharaArithmetic.binom2 (C.d j)) 0

/-- Condition (4.3.9). -/
def Condition9 (P : Parameters C.s C.t) : Prop :=
  ∀ i j, i < j → Int.ModEq (orderInt C.d i)
    (-P.u i j * TaharaArithmetic.binom3 (C.d j) +
      P.w' i j j * TaharaArithmetic.binom2 (C.d j)) 0

/-- The three congruences in condition (4.3.10). -/
def Condition10 (P : Parameters C.s C.t) : Prop :=
  ∀ i j k, i < j → j < k →
    Int.ModEq (orderInt C.d i)
      (P.w i j k * TaharaArithmetic.binom2 (C.d i)) 0 ∧
    Int.ModEq (orderInt C.d i)
      (P.w' i j k * TaharaArithmetic.binom2 (C.d j)) 0 ∧
    Int.ModEq (orderInt C.d i)
      (P.w'' i j k * TaharaArithmetic.binom2 (C.d k)) 0

/-- Condition (4.3.11). -/
def Condition11 (P : Parameters C.s C.t) : Prop :=
  ∀ i k, Int.ModEq (orderGCD C.d C.e i k)
    (P.v i k * TaharaArithmetic.binom2 (C.d i) -
      (∑ h ∈ Finset.univ.filter (· ≤ i), P.w h i i * C.b h k) -
      (∑ h ∈ Finset.univ.filter (i < ·), P.w'' i i h * C.b h k)) 0

/-- Condition (4.3.12). -/
def Condition12 (P : Parameters C.s C.t) : Prop :=
  ∀ i j k, i < j → Int.ModEq (orderGCD C.d C.e i k)
    ((∑ h ∈ Finset.univ.filter (· ≤ i), P.w h i j * C.b h k) +
      (∑ h ∈ Finset.univ.filter (fun h => i < h ∧ h ≤ j),
        P.w' i h j * C.b h k) +
      (∑ h ∈ Finset.univ.filter (j < ·), P.w'' i j h * C.b h k)) 0

/-- Condition (4.3.13). -/
def Condition13 (P : Parameters C.s C.t) : Prop :=
  ∀ i l, Int.ModEq (orderGCD C.d C.f i l)
    (-(∑ h ∈ Finset.univ.filter (· < i),
        P.u h i * orderRatio C.d h i * C.alpha h i l) +
      (∑ h ∈ Finset.univ.filter (i < ·), P.u i h * C.c h l) -
      (∑ h ∈ Finset.univ.filter (· < i),
        P.u h i * orderRatio C.d h i * C.c h l) -
      (∑ k, P.v' i k * C.delta k l) -
      (∑ g ∈ Finset.univ.filter (· ≤ i),
        ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l) -
      (∑ g ∈ Finset.univ.filter (· ≤ i),
        ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
          P.w g h i * C.alpha g h l) -
      (∑ g ∈ Finset.univ.filter (i < ·),
        ∑ h ∈ Finset.univ.filter (g ≤ ·), P.w' i g h * C.alpha g h l)) 0

/-- Condition (4.3.14). -/
def Condition14 (P : Parameters C.s C.t) : Prop :=
  ∀ k, Int.ModEq (orderInt C.e k) (∑ i, P.v i k * C.b i k) 0

/-- Condition (4.3.15). -/
def Condition15 (P : Parameters C.s C.t) : Prop :=
  ∀ k l, k < l → Int.ModEq (orderInt C.e k)
    (∑ i, (P.v i k * C.b i l + P.v i l * C.b i k)) 0

/-- The complete conjunction of Tahara's conditions (4.3.2)--(4.3.15). -/
def Satisfies (P : Parameters C.s C.t) : Prop :=
  P.Condition2 ∧ P.Condition3 ∧ P.Condition4 ∧ P.Condition5 ∧
    P.Condition6 ∧ P.Condition7 ∧ P.Condition8 ∧ P.Condition9 ∧
    P.Condition10 ∧ P.Condition11 ∧ P.Condition12 ∧ P.Condition13 ∧
    P.Condition14 ∧ P.Condition15

end Parameters

/-- The word displayed in (4.3.1), in the source's lexicographic product
order. -/
def word (C : Context G) (P : Parameters C.s C.t) : G :=
  orderedProduct (fun i => orderedProductWhere (i < ·) fun j =>
      D5.paperComm (C.x1 i ^ (P.u i j * orderInt C.d j)) (C.x1 j)) *
  orderedProduct (fun i => orderedProduct fun p =>
    orderedProductWhere (p < ·) fun q =>
      D5.paperComm (C.x2 q) (C.x2 p) ^ (C.b i q * P.v i p)) *
  orderedProduct (fun i => orderedProductWhere (i ≤ ·) fun j =>
    orderedProductWhere (j ≤ ·) fun k =>
      D5.leftComm (C.x1 i ^ orderInt C.d i) [C.x1 j, C.x1 k] ^ P.w i j k)

/-- The set of all words (4.3.1) whose parameters satisfy (4.3.2)--
(4.3.15). -/
def generatorSet (C : Context G) : Set G :=
  {g | ∃ P : Parameters C.s C.t, P.Satisfies ∧ word C P = g}

/-- The subgroup generated by the words in Tahara's description. -/
def generatedSubgroup (C : Context G) : Subgroup G :=
  Subgroup.closure (generatorSet C)

/-- A word with admissible parameters belongs to the subgroup occurring on
the right side of Tahara's theorem. -/
theorem word_mem_generatedSubgroup (C : Context G) (P : Parameters C.s C.t)
    (hP : P.Satisfies) : word C P ∈ generatedSubgroup C := by
  apply Subgroup.subset_closure
  exact ⟨P, hP, rfl⟩

/-- Existence of the cyclic coordinate data used in Tahara's description.

This is an explicitly declared standard-background assumption: for a finite
group, choose invariant-factor coordinates in the successive lower-central
quotients relevant modulo `γ₅`. -/
axiom context_exists (G : Type u) [Group G] [Finite G] : Nonempty (Context G)

namespace Context

/-- A fixed choice of Tahara coordinates for a finite group. -/
noncomputable def chosen (G : Type u) [Group G] [Finite G] : Context G :=
  Classical.choice (context_exists G)

end Context

/-- **Tahara's Theorem 4.3.3, lifted from `G / γ₅(G)`.**  For a finite
group equipped with the cyclic coordinates and structural coefficients
specified above, the fifth integral dimension subgroup is generated modulo
`γ₅` by the words (4.3.1) satisfying conditions (4.3.2)--(4.3.15).

This is the single Tahara assumption approved for the project. -/
axiom description (C : Context G) [Finite G] :
  D5.dimensionSubgroup G 5 = generatedSubgroup C ⊔ D5.gamma G 5

/-- Membership form of Tahara's description.  This theorem is merely the
subgroup equality above rewritten pointwise. -/
theorem mem_dimensionSubgroup_five_iff (C : Context G) [Finite G] (g : G) :
    g ∈ D5.dimensionSubgroup G 5 ↔
      g ∈ generatedSubgroup C ⊔ D5.gamma G 5 := by
  rw [description C]

/-- Direct usable consequence: every admissible word (4.3.1) is in `D₅`. -/
theorem word_mem_dimensionSubgroup_five (C : Context G) [Finite G]
    (P : Parameters C.s C.t) (hP : P.Satisfies) :
    word C P ∈ D5.dimensionSubgroup G 5 := by
  rw [description C]
  exact (le_sup_left : generatedSubgroup C ≤
    generatedSubgroup C ⊔ D5.gamma G 5) (word_mem_generatedSubgroup C P hP)

end

end D5.Tahara
