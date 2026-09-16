import D5.Foundations
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Arithmetic consequences of Tahara's pair conditions

This file begins the verification of Section 4 of the source proof. We write
`d = d(i)`, `e = d(j)` and `q = e / d`. Binomial coefficients are represented
by variables together with the elementary identities actually used in the
paper. This isolates integer divisibility from the later group calculations.
-/

namespace D5.TaharaArithmetic

/-- Integer-valued notation for `C(n,2)`. -/
def binom2 (n : ℕ) : ℤ :=
  n.choose 2

/-- Integer-valued notation for `C(n,3)`. -/
def binom3 (n : ℕ) : ℤ :=
  n.choose 3

/-- The first elementary binomial identity used in Section 4. The subtraction
on the right is kept in `ℕ`, so this statement has no positivity hypothesis. -/
theorem two_mul_binom2 (n : ℕ) :
    2 * binom2 n = (n : ℤ) * ((n - 1 : ℕ) : ℤ) := by
  have h := Nat.choose_succ_right_eq n 1
  norm_num at h
  have hz := congrArg (fun x : ℕ => (x : ℤ)) h
  norm_num at hz
  simpa [binom2, mul_comm] using hz

/-- The second elementary binomial identity used in Section 4. -/
theorem three_mul_binom3 (n : ℕ) :
    3 * binom3 n = binom2 n * ((n - 2 : ℕ) : ℤ) := by
  have h := Nat.choose_succ_right_eq n 2
  norm_num at h
  have hz := congrArg (fun x : ℕ => (x : ℤ)) h
  norm_num at hz
  simpa [binom2, binom3, mul_comm] using hz

/-- If `d` divides both `2x` and `3x`, then it divides `x`. This is the
Bezout step used repeatedly in Section 4. -/
theorem dvd_of_dvd_two_mul_of_dvd_three_mul {d x : ℤ}
    (h2 : d ∣ 2 * x) (h3 : d ∣ 3 * x) : d ∣ x := by
  rcases h2 with ⟨a, ha⟩
  rcases h3 with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  nlinarith

/-- Equation (12), written without division in `ℤ`. -/
theorem equation12
    {d e q u B2e wijj wpijj : ℤ}
    (he : e = d * q)
    (h8 : -u * B2e + d * wijj + e * wpijj = 0) :
    u * B2e = d * (wijj + q * wpijj) := by
  rw [he] at h8
  nlinarith

/-- Equation (13), written without division in `ℤ`. -/
theorem equation13
    {d e q u B2d wiij wppiij : ℤ}
    (he : e = d * q)
    (h7 : u * q * B2d + d * wiij + e * wppiij = 0) :
    u * q * B2d = d * (-wiij - q * wppiij) := by
  rw [he] at h7
  nlinarith

/-- The two divisibilities displayed in (17). -/
theorem divisibility17
    {d e q u B2d B2e wiij wijj wpijj wppiij : ℤ}
    (he : e = d * q)
    (h7 : u * q * B2d + d * wiij + e * wppiij = 0)
    (h8 : -u * B2e + d * wijj + e * wpijj = 0) :
    d ∣ u * q * B2d ∧ d ∣ u * B2e := by
  constructor
  · exact ⟨-wiij - q * wppiij, equation13 he h7⟩
  · exact ⟨wijj + q * wpijj, equation12 he h8⟩

/-- The first divisibility in (14): `d ∣ wᵢᵢⱼ * C(d,2)`. -/
theorem dvd_wiij_mul_B2d
    {d u q B2d B3d wiij : ℤ}
    (h17 : d ∣ u * q * B2d)
    (h9 : d ∣ u * q * B3d + wiij * B2d)
    (hB2 : 2 * B2d = d * (d - 1))
    (hB3 : 3 * B3d = B2d * (d - 2)) :
    d ∣ wiij * B2d := by
  apply dvd_of_dvd_two_mul_of_dvd_three_mul
  · refine ⟨wiij * (d - 1), ?_⟩
    calc
      2 * (wiij * B2d) = wiij * (2 * B2d) := by ring
      _ = wiij * (d * (d - 1)) := by rw [hB2]
      _ = d * (wiij * (d - 1)) := by ring
  · rcases h17 with ⟨k, hk⟩
    rcases h9 with ⟨t, ht⟩
    refine ⟨3 * t - k * (d - 2), ?_⟩
    calc
      3 * (wiij * B2d) =
          3 * (u * q * B3d + wiij * B2d) - 3 * (u * q * B3d) := by ring
      _ = 3 * (d * t) - 3 * (u * q * B3d) := by rw [ht]
      _ = 3 * d * t - u * q * (3 * B3d) := by ring
      _ = 3 * d * t - u * q * (B2d * (d - 2)) := by rw [hB3]
      _ = 3 * d * t - (u * q * B2d) * (d - 2) := by ring
      _ = 3 * d * t - (d * k) * (d - 2) := by rw [hk]
      _ = d * (3 * t - k * (d - 2)) := by ring

/-- The third divisibility in (14): `d ∣ w'ᵢⱼⱼ * C(e,2)`. -/
theorem dvd_wpijj_mul_B2e
    {d e q u B2e B3e wpijj : ℤ}
    (he : e = d * q)
    (h17 : d ∣ u * B2e)
    (h11 : d ∣ -u * B3e + wpijj * B2e)
    (hB2 : 2 * B2e = e * (e - 1))
    (hB3 : 3 * B3e = B2e * (e - 2)) :
    d ∣ wpijj * B2e := by
  apply dvd_of_dvd_two_mul_of_dvd_three_mul
  · refine ⟨wpijj * q * (e - 1), ?_⟩
    calc
      2 * (wpijj * B2e) = wpijj * (2 * B2e) := by ring
      _ = wpijj * (e * (e - 1)) := by rw [hB2]
      _ = wpijj * (d * q * (e - 1)) := by rw [he]
      _ = d * (wpijj * q * (e - 1)) := by ring
  · rcases h17 with ⟨k, hk⟩
    rcases h11 with ⟨t, ht⟩
    refine ⟨3 * t + k * (e - 2), ?_⟩
    calc
      3 * (wpijj * B2e) =
          3 * (-u * B3e + wpijj * B2e) + 3 * (u * B3e) := by ring
      _ = 3 * (d * t) + 3 * (u * B3e) := by rw [ht]
      _ = 3 * d * t + u * (3 * B3e) := by ring
      _ = 3 * d * t + u * (B2e * (e - 2)) := by rw [hB3]
      _ = 3 * d * t + (u * B2e) * (e - 2) := by ring
      _ = 3 * d * t + (d * k) * (e - 2) := by rw [hk]
      _ = d * (3 * t + k * (e - 2)) := by ring

/-- The second divisibility in (14), obtained from condition (10). -/
theorem dvd_wppiij_mul_B2e
    {d B2d B2e wiij wppiij : ℤ}
    (hfirst : d ∣ wiij * B2d)
    (h10 : d ∣ wiij * B2d + wppiij * B2e) :
    d ∣ wppiij * B2e := by
  rcases hfirst with ⟨a, ha⟩
  rcases h10 with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  nlinarith

/-- The first divisibility in (16), obtained from condition (9). -/
theorem dvd_uq_mul_B3d
    {d u q B2d B3d wiij : ℤ}
    (hwi : d ∣ wiij * B2d)
    (h9 : d ∣ u * q * B3d + wiij * B2d) :
    d ∣ u * q * B3d := by
  rcases hwi with ⟨a, ha⟩
  rcases h9 with ⟨b, hb⟩
  refine ⟨b - a, ?_⟩
  nlinarith

/-- The second divisibility in (16), obtained from condition (11). -/
theorem dvd_u_mul_B3e
    {d u B2e B3e wpijj : ℤ}
    (hwp : d ∣ wpijj * B2e)
    (h11 : d ∣ -u * B3e + wpijj * B2e) :
    d ∣ u * B3e := by
  rcases hwp with ⟨a, ha⟩
  rcases h11 with ⟨b, hb⟩
  refine ⟨a - b, ?_⟩
  nlinarith

/-- The binomial difference identity transfers divisibility from a multiple
of `B2e` to the corresponding multiple of `q * B2d`. -/
theorem dvd_q_mul_B2d_of_dvd_mul_B2e
    {d q B2d B2e B2q z : ℤ}
    (hdiff : B2e - q * B2d = d * d * B2q)
    (hz : d ∣ z * B2e) :
    d ∣ q * z * B2d := by
  rcases hz with ⟨k, hk⟩
  refine ⟨k - z * d * B2q, ?_⟩
  calc
    q * z * B2d = z * B2e - z * (B2e - q * B2d) := by ring
    _ = d * k - z * (d * d * B2q) := by rw [hk, hdiff]
    _ = d * (k - z * d * B2q) := by ring

/-- The second divisibility in (15), in a denominator-free form:
`d² ∣ u q C(d,2)²`. -/
theorem dvd_sq_mul_uq_B2d_sq
    {d e q u B2d wiij wppiij : ℤ}
    (he : e = d * q)
    (h7 : u * q * B2d + d * wiij + e * wppiij = 0)
    (hwi : d ∣ wiij * B2d)
    (hqwpp : d ∣ q * wppiij * B2d) :
    d * d ∣ u * q * B2d * B2d := by
  have h13 := equation13 he h7
  rcases hwi with ⟨a, ha⟩
  rcases hqwpp with ⟨b, hb⟩
  refine ⟨-a - b, ?_⟩
  calc
    u * q * B2d * B2d = d * (-wiij - q * wppiij) * B2d := by rw [h13]
    _ = d * (-(wiij * B2d) - q * wppiij * B2d) := by ring
    _ = d * (-(d * a) - d * b) := by rw [ha, hb]
    _ = d * d * (-a - b) := by ring

/-- The first divisibility in (15), in a denominator-free form:
`d² ∣ u C(e,2) C(d,2)`. -/
theorem dvd_sq_mul_u_B2e_B2d
    {d q u B2d B2e B2q : ℤ}
    (hdiff : B2e - q * B2d = d * d * B2q)
    (hsecond : d * d ∣ u * q * B2d * B2d) :
    d * d ∣ u * B2e * B2d := by
  rcases hsecond with ⟨k, hk⟩
  refine ⟨k + u * B2q * B2d, ?_⟩
  calc
    u * B2e * B2d =
        u * q * B2d * B2d + u * (B2e - q * B2d) * B2d := by ring
    _ = d * d * k + u * (d * d * B2q) * B2d := by rw [hk, hdiff]
    _ = d * d * (k + u * B2q * B2d) := by ring

/-- The fourth divisibility in (14): `d ∣ wᵢⱼⱼ * C(d,2)`. -/
theorem dvd_wijj_mul_B2d
    {d e q u B2d B2e wijj wpijj : ℤ}
    (hd : d ≠ 0)
    (he : e = d * q)
    (h8 : -u * B2e + d * wijj + e * wpijj = 0)
    (hfirst15 : d * d ∣ u * B2e * B2d)
    (hqwp : d ∣ q * wpijj * B2d) :
    d ∣ wijj * B2d := by
  have h12 := equation12 he h8
  rcases hfirst15 with ⟨k, hk⟩
  rcases hqwp with ⟨b, hb⟩
  have hcancel : wijj * B2d + q * wpijj * B2d = d * k := by
    apply mul_left_cancel₀ hd
    calc
      d * (wijj * B2d + q * wpijj * B2d) =
          (d * (wijj + q * wpijj)) * B2d := by ring
      _ = u * B2e * B2d := by rw [← h12]
      _ = d * d * k := hk
      _ = d * (d * k) := by ring
  refine ⟨k - b, ?_⟩
  nlinarith

end D5.TaharaArithmetic
