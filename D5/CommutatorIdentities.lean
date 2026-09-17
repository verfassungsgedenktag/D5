import D5.Foundations
import Mathlib.Tactic.Group

/-!
# Exact elementary commutator identities

These identities are proved directly from the definition
`[a,b] = a⁻¹ b⁻¹ a b` using the `group` normalizer. They contain no
nilpotency or quotient assumptions.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

/-- Conjugation in the exponent convention used in collection formulas:
`x ^ y = y⁻¹ x y`. -/
def conjugateBy (x y : G) : G :=
  y⁻¹ * x * y

@[simp]
theorem conjugateBy_one_right (x : G) : conjugateBy x 1 = x := by
  simp [conjugateBy]

theorem paperComm_mul_left (a b c : G) :
    paperComm (a * b) c =
      conjugateBy (paperComm a c) b * paperComm b c := by
  simp only [paperComm_eq, conjugateBy]
  group

theorem paperComm_mul_right (a b c : G) :
    paperComm a (b * c) =
      paperComm a c * conjugateBy (paperComm a b) c := by
  simp only [paperComm_eq, conjugateBy]
  group

theorem paperComm_inv_left (a b : G) :
    paperComm a⁻¹ b = conjugateBy (paperComm b a) a⁻¹ := by
  simp only [paperComm_eq, conjugateBy, inv_inv]
  group

theorem paperComm_inv_right (a b : G) :
    paperComm a b⁻¹ = conjugateBy (paperComm b a) b⁻¹ := by
  simp only [paperComm_eq, conjugateBy, inv_inv]
  group

theorem paperComm_swap (a b : G) :
    paperComm b a = (paperComm a b)⁻¹ := by
  simp only [paperComm_eq]
  group

/-- Dictionary from Mathlib's element commutator to the paper convention. -/
theorem commutatorElement_eq_paperComm_inv (a b : G) :
    ⁅a, b⁆ = paperComm a⁻¹ b⁻¹ := by
  simp only [paperComm_eq, inv_inv, commutatorElement_def]

/-- Expanding a conjugation as a commutator correction. -/
theorem conjugateBy_eq_mul_paperComm (x y : G) :
    conjugateBy x y = x * paperComm x y := by
  simp only [paperComm_eq, conjugateBy]
  group

/-- First power-collection identity. It is kept exact; later files discard
the correction factor by a weight estimate when appropriate. -/
theorem paperComm_sq_left (a b : G) :
    paperComm (a ^ 2) b =
      paperComm a b * paperComm (paperComm a b) a * paperComm a b := by
  rw [show a ^ 2 = a * a by simp [pow_two], paperComm_mul_left,
    conjugateBy_eq_mul_paperComm]

/-- Symmetric exact square identity in the second argument. -/
theorem paperComm_sq_right (a b : G) :
    paperComm a (b ^ 2) =
      paperComm a b * paperComm a b * paperComm (paperComm a b) b := by
  rw [show b ^ 2 = b * b by simp [pow_two], paperComm_mul_right,
    conjugateBy_eq_mul_paperComm]
  simp [mul_assoc]

/-- The Hall--Witt identity in the commutator and conjugation conventions
used by the source proof.  This is an exact group identity. -/
theorem hallWitt (x y z : G) :
    conjugateBy (paperComm (paperComm x y⁻¹) z) y *
      conjugateBy (paperComm (paperComm y z⁻¹) x) z *
      conjugateBy (paperComm (paperComm z x⁻¹) y) x = 1 := by
  simp only [paperComm_eq, conjugateBy, inv_inv]
  group

end

end D5
