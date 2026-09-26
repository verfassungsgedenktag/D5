import D5.Foundations
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-!
# Functoriality of integral dimension subgroups

This file proves the group-ring functoriality needed for the final reduction
to `G / gamma G 6`.  The proof works directly with the project's
noncommutative two-sided ideal powers.
-/

namespace D5

universe u v

noncomputable section

section GroupRingMap

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- The ring homomorphism `ℤ[G] → ℤ[H]` induced by a group homomorphism. -/
def groupRingMap (f : G →* H) : GroupRing G →+* GroupRing H :=
  MonoidAlgebra.mapDomainRingHom ℤ f

@[simp]
theorem groupRingMap_groupRingOf (f : G →* H) (g : G) :
    groupRingMap f (groupRingOf G g) = groupRingOf H (f g) := by
  simp [groupRingMap, groupRingOf, MonoidAlgebra.of]

@[simp]
theorem augmentation_groupRingMap (f : G →* H) (x : GroupRing G) :
    augmentation H (groupRingMap f x) = augmentation G x := by
  have hhom : (augmentation H).comp (groupRingMap f) = augmentation G := by
    apply MonoidAlgebra.ringHom_ext
    · intro z
      simp [groupRingMap, augmentation]
    · intro g
      simp [groupRingMap, augmentation]
  exact DFunLike.congr_fun hhom x

end GroupRingMap

section IdealPowers

variable {R : Type u} {S : Type v} [Ring R] [Ring S]

/-- A ring homomorphism carrying `I` into `J` carries every element of the
project's `n`th two-sided ideal power into the corresponding power of `J`. -/
theorem map_twoSidedIdealPow_mem (F : R →+* S)
    (I : TwoSidedIdeal R) (J : TwoSidedIdeal S)
    (hF : ∀ x, x ∈ I → F x ∈ J) :
    ∀ n x, x ∈ twoSidedIdealPow I n → F x ∈ twoSidedIdealPow J n := by
  intro n
  induction n with
  | zero =>
      intro x hx
      simp [twoSidedIdealPow]
  | succ n ih =>
      intro x hx
      unfold twoSidedIdealPow at hx ⊢
      unfold twoSidedIdealMul at hx ⊢
      refine TwoSidedIdeal.span_induction
        (p := fun x _ => F x ∈ TwoSidedIdeal.span
          {z | ∃ a ∈ twoSidedIdealPow J n, ∃ b ∈ J, a * b = z})
        ?_ ?_ ?_ ?_ ?_ ?_ hx
      · intro z hz
        rcases hz with ⟨a, ha, b, hb, rfl⟩
        rw [map_mul]
        exact TwoSidedIdeal.subset_span ⟨F a, ih a ha, F b, hF b hb, rfl⟩
      · change F 0 ∈ _
        rw [map_zero]
        exact TwoSidedIdeal.zero_mem _
      · intro a b ha hb hma hmb
        rw [map_add]
        exact TwoSidedIdeal.add_mem _ hma hmb
      · intro a ha hma
        rw [map_neg]
        exact TwoSidedIdeal.neg_mem _ hma
      · intro a x hx hmx
        rw [map_mul]
        exact TwoSidedIdeal.mul_mem_left _ _ _ hmx
      · intro b x hx hmx
        rw [map_mul]
        exact TwoSidedIdeal.mul_mem_right _ _ _ hmx

end IdealPowers

section DimensionSubgroup

variable {G : Type u} {H : Type v} [Group G] [Group H]

/-- Integral dimension subgroups are functorial under group homomorphisms. -/
theorem dimensionSubgroup_map (f : G →* H) (n : ℕ) :
    Subgroup.map f (dimensionSubgroup G n) ≤ dimensionSubgroup H n := by
  rintro y ⟨x, hx, rfl⟩
  have hx' : x ∈ dimensionSubgroup G n := hx
  rw [mem_dimensionSubgroup_iff] at hx' ⊢
  have hmap := map_twoSidedIdealPow_mem (groupRingMap f)
    (augmentationIdeal G) (augmentationIdeal H) (fun z hz => by
      change augmentation H (groupRingMap f z) = 0
      rw [augmentation_groupRingMap]
      exact hz) n (groupRingOf G x - 1) hx'
  simpa using hmap

theorem map_mem_dimensionSubgroup (f : G →* H) (n : ℕ) {g : G}
    (hg : g ∈ dimensionSubgroup G n) :
    f g ∈ dimensionSubgroup H n :=
  dimensionSubgroup_map f n (Subgroup.mem_map_of_mem f hg)

end DimensionSubgroup

end

end D5
