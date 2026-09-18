import D5.HallPetresco

/-!
# The weight `(1,2,1)` transfer in formula (22)

This is the second power-transfer calculation in the source proof.  Its
middle argument has weight two, so only one weight-five correction remains.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

/-- Formula (22), for an arbitrary element `y ∈ γ₂`. -/
theorem transfer_formula22
    {ξ y x : G} (hξ : ξ ∈ gamma G 1) (hy : y ∈ gamma G 2)
    (hx : x ∈ gamma G 1) (n : ℕ) :
    ModGammaSix
      (paperComm (paperComm ξ (y ^ (n : ℤ))) x)
      (paperComm (paperComm ξ y) (x ^ (n : ℤ)) *
        paperComm (paperComm (paperComm y ξ) x) x ^
          TaharaArithmetic.binom2 n) := by
  let q := paperComm ξ y
  let A := paperComm q x
  let B := paperComm A x
  let C := paperComm B x
  let D := paperComm (paperComm (paperComm y ξ) x) x
  have hq : q ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hy
  have hA : A ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have hB : B ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hx
  have hC : C ∈ gamma G 6 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hB hx
  have hinner : ModEq (gamma G 5) (paperComm ξ (y ^ (n : ℤ)))
      (q ^ (n : ℤ)) :=
    paperComm_zpow_right_mod_gamma
      (n := 5) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hξ hy (n : ℤ)
  have hlift : ModGammaSix
      (paperComm (paperComm ξ (y ^ (n : ℤ))) x)
      (paperComm (q ^ (n : ℤ)) x) :=
    paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hx
  have hleftPower : ModGammaSix (paperComm (q ^ (n : ℤ)) x)
      (A ^ (n : ℤ)) := by
    simpa [A] using paperComm_zpow_left_mod_gamma
      (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hx (n : ℤ)
  have hleft : ModGammaSix
      (paperComm (paperComm ξ (y ^ (n : ℤ))) x) (A ^ (n : ℤ)) :=
    hlift.trans hleftPower
  have hrightRaw : ModGammaSix
      (paperComm q (x ^ (n : ℤ)))
      (A ^ (n : ℤ) * B ^ TaharaArithmetic.binom2 n *
        C ^ TaharaArithmetic.binom3 n) := by
    simpa [A, B, C] using paperComm_zpow_right_hallPetresco
      (gamma_antitone G (by norm_num) hq) hx n
  have hCvanish : ModGammaSix
      (C ^ TaharaArithmetic.binom3 n) 1 := by
    change ((C ^ TaharaArithmetic.binom3 n : G) : G ⧸ gamma G 6) = 1
    rw [QuotientGroup.eq_one_iff]
    exact (gamma G 6).zpow_mem hC _
  have hright : ModGammaSix
      (paperComm q (x ^ (n : ℤ)))
      (A ^ (n : ℤ) * B ^ TaharaArithmetic.binom2 n) :=
    hrightRaw.trans <| by
      simpa only [mul_one] using
        ((ModEq.refl (gamma G 6)
          (A ^ (n : ℤ) * B ^ TaharaArithmetic.binom2 n)).mul hCvanish)
  have hqInv : paperComm y ξ = q⁻¹ := paperComm_swap ξ y
  have hinnerInv : ModEq (gamma G 5) (paperComm q⁻¹ x) A⁻¹ :=
    paperComm_inv_left_mod_gamma
      (n := 5) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hx
  have hliftInv := paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinnerInv hx
  have hAInv : ModGammaSix (paperComm A⁻¹ x) B⁻¹ :=
    paperComm_inv_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hA hx
  have hD : ModGammaSix D B⁻¹ := by
    change ModGammaSix
      (paperComm (paperComm (paperComm y ξ) x) x) B⁻¹
    rw [hqInv]
    exact hliftInv.trans hAInv
  have hrightCorrected : ModGammaSix
      (paperComm q (x ^ (n : ℤ)) *
        D ^ TaharaArithmetic.binom2 n)
      (A ^ (n : ℤ)) := by
    have hpow := hD.zpow (TaharaArithmetic.binom2 n)
    have hcombined := hright.mul hpow
    have hcancel :
        A ^ (n : ℤ) * B ^ TaharaArithmetic.binom2 n *
          B⁻¹ ^ TaharaArithmetic.binom2 n = A ^ (n : ℤ) := by
      rw [inv_zpow]
      group
    exact hcombined.trans <| by rw [hcancel]
  change ModGammaSix (paperComm (paperComm ξ (y ^ (n : ℤ))) x)
    (paperComm q (x ^ (n : ℤ)) * D ^ TaharaArithmetic.binom2 n)
  exact hleft.trans hrightCorrected.symm

end

end D5
