import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.NoncommRing

/-!
# Basic definitions

This file fixes the conventions used in the source proof. The paper numbers
the lower central series from `1`, while Mathlib numbers it from `0`.
The paper also uses `[a,b] = a⁻¹ b⁻¹ a b`, whereas Mathlib's element bracket
is `⁅a,b⁆ = a b a⁻¹ b⁻¹`.
-/

namespace D5

universe u

noncomputable section

section Commutators

variable {G : Type u} [Group G]

/-- The commutator convention of the source document: `[a,b] = a⁻¹b⁻¹ab`. -/
def paperComm (a b : G) : G :=
  ⁅a⁻¹, b⁻¹⁆

@[simp]
theorem paperComm_eq (a b : G) : paperComm a b = a⁻¹ * b⁻¹ * a * b := by
  simp [paperComm, commutatorElement_def]

/-- Left-normed commutator `[a₁,...,aₙ]`, with the first entry separated
from the remaining list. -/
def leftComm (a : G) : List G → G
  | [] => a
  | b :: bs => leftComm (paperComm a b) bs

@[simp]
theorem leftComm_nil (a : G) : leftComm a [] = a := rfl

@[simp]
theorem leftComm_cons (a b : G) (bs : List G) :
    leftComm a (b :: bs) = leftComm (paperComm a b) bs := rfl

end Commutators

section CentralSeries

variable (G : Type u) [Group G]

/-- The lower central series with the paper's indexing: `γ₁(G) = G`.
The value at `0` is also `G`; only positive indices are used. -/
def gamma (n : ℕ) : Subgroup G :=
  lowerCentralSeries G (n - 1)

@[simp]
theorem gamma_zero : gamma G 0 = ⊤ := by
  simp [gamma]

@[simp]
theorem gamma_one : gamma G 1 = ⊤ := by
  simp [gamma]

theorem gamma_succ (n : ℕ) (hn : 1 ≤ n) :
    gamma G (n + 1) = ⁅gamma G n, (⊤ : Subgroup G)⁆ := by
  simp only [gamma]
  rw [Nat.add_sub_cancel]
  conv_lhs => rw [← show n - 1 + 1 = n by omega]
  rfl

theorem gamma_antitone : Antitone (gamma G) := by
  intro m n hmn
  exact lowerCentralSeries_antitone (Nat.sub_le_sub_right hmn 1)

instance gamma_normal (n : ℕ) : (gamma G n).Normal := by
  unfold gamma
  infer_instance

end CentralSeries

section DimensionSubgroups

variable (G : Type u) [Group G]

/-- The integral group ring `ℤ[G]`. -/
abbrev GroupRing := MonoidAlgebra ℤ G

/-- The canonical multiplicative map `G → ℤ[G]`. -/
noncomputable def groupRingOf : G →* GroupRing G :=
  MonoidAlgebra.of ℤ G

/-- The augmentation homomorphism `ℤ[G] → ℤ`. -/
noncomputable def augmentation : GroupRing G →+* ℤ :=
  (MonoidAlgebra.lift ℤ G ℤ (1 : G →* ℤ)).toRingHom

/-- The augmentation ideal in the integral group ring. -/
def augmentationIdeal : TwoSidedIdeal (GroupRing G) :=
  TwoSidedIdeal.ker (augmentation G)

/-- Product of two two-sided ideals, defined as the two-sided ideal spanned by
pairwise products. Mathlib currently does not provide this multiplication as
an instance for `TwoSidedIdeal`. -/
def twoSidedIdealMul {R : Type*} [Ring R]
    (I J : TwoSidedIdeal R) : TwoSidedIdeal R :=
  TwoSidedIdeal.span {x | ∃ a ∈ I, ∃ b ∈ J, a * b = x}

/-- Natural powers of a two-sided ideal. -/
def twoSidedIdealPow {R : Type*} [Ring R]
    (I : TwoSidedIdeal R) : ℕ → TwoSidedIdeal R
  | 0 => ⊤
  | n + 1 => twoSidedIdealMul (twoSidedIdealPow I n) I

/-- The `n`th power of the augmentation ideal. -/
def augmentationIdealPow (n : ℕ) : TwoSidedIdeal (GroupRing G) :=
  twoSidedIdealPow (augmentationIdeal G) n

@[simp]
theorem augmentation_groupRingOf (g : G) :
    augmentation G (groupRingOf G g) = 1 := by
  simp [augmentation, groupRingOf]

/-- The integral dimension subgroup
`Dₙ(G) = {g | g - 1 ∈ I(G)^n}`. -/
def dimensionSubgroup (n : ℕ) : Subgroup G where
  carrier := {g | groupRingOf G g - 1 ∈ augmentationIdealPow G n}
  one_mem' := by
    change groupRingOf G 1 - 1 ∈ augmentationIdealPow G n
    rw [map_one]
    simp
  mul_mem' := by
    intro a b ha hb
    change groupRingOf G (a * b) - 1 ∈ augmentationIdealPow G n
    rw [map_mul]
    rw [show groupRingOf G a * groupRingOf G b - 1 =
        (groupRingOf G a - 1) + groupRingOf G a * (groupRingOf G b - 1) by
      noncomm_ring]
    exact (augmentationIdealPow G n).add_mem ha
      ((augmentationIdealPow G n).mul_mem_left _ _ hb)
  inv_mem' := by
    intro a ha
    change groupRingOf G a⁻¹ - 1 ∈ augmentationIdealPow G n
    have hmul : groupRingOf G a⁻¹ * groupRingOf G a = 1 := by
      rw [← map_mul]
      simp
    rw [show groupRingOf G a⁻¹ - 1 =
        (-groupRingOf G a⁻¹) * (groupRingOf G a - 1) by
      rw [mul_sub, neg_mul, hmul]
      simp [sub_eq_add_neg, add_comm]]
    exact (augmentationIdealPow G n).mul_mem_left _ _ ha

@[simp]
theorem mem_dimensionSubgroup_iff (n : ℕ) (g : G) :
    g ∈ dimensionSubgroup G n ↔
      groupRingOf G g - 1 ∈ augmentationIdealPow G n :=
  Iff.rfl

end DimensionSubgroups

end

end D5
