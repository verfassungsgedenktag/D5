import D5.CollectionWeighted

/-!
# Powers of weight-five commutators

These lemmas verify the rule used immediately after formula (20): if a
weight-five commutator contains `z` and `z^d ∈ γ₂`, then its `d`-th power is
trivial modulo `γ₆`.  The exponent is moved to the chosen occurrence one
commutator at a time, with the required intermediate moduli made explicit.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

theorem modGammaSix_zpow_eq_one_of_dvd
    {g : G} {d m : ℤ} (hd : ModGammaSix (g ^ d) 1) (hdiv : d ∣ m) :
    ModGammaSix (g ^ m) 1 := by
  rcases hdiv with ⟨k, rfl⟩
  rw [zpow_mul]
  simpa using hd.zpow k

/-- Vanishing for `[ξ,x,x,x,z]^d`. -/
theorem weightFive_last_entry_power_vanish
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) {d : ℤ} (hzd : z ^ d ∈ gamma G 2) :
    ModGammaSix
      (paperComm (paperComm (paperComm (paperComm ξ x) x) x) z ^ d) 1 := by
  let q := paperComm ξ x
  let r := paperComm q x
  let s := paperComm r x
  have hq : q ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hr : r ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have hs : s ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hr hx
  have htransfer := paperComm_zpow_right_mod_gamma
    (n := 6) (r := 4) (s := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hs hz d
  have hfinal : paperComm s (z ^ d) ∈ gamma G 6 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hs hzd
  exact htransfer.symm.trans <| by
    rw [modEq_one_iff_mem]
    exact hfinal

/-- Vanishing for `[ξ,x,z,z,z]^d`. -/
theorem weightFive_three_repeated_entry_power_vanish
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) {d : ℤ} (hzd : z ^ d ∈ gamma G 2) :
    ModGammaSix
      (paperComm (paperComm (paperComm (paperComm ξ x) z) z) z ^ d) 1 := by
  let q := paperComm ξ x
  let r := paperComm q z
  let s := paperComm r z
  have hq : q ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hr : r ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hz
  have hs : s ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hr hz
  have houter : ModGammaSix (paperComm (s ^ d) z)
      (paperComm s z ^ d) :=
    paperComm_zpow_left_mod_gamma (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hs hz d
  have hmid : ModEq (gamma G 5) (s ^ d) (paperComm (r ^ d) z) := by
    exact (paperComm_zpow_left_mod_gamma (n := 5) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hr hz d).symm
  have hmidLift := paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hmid hz
  have hinner : ModEq (gamma G 4) (r ^ d) (paperComm q (z ^ d)) := by
    exact (paperComm_zpow_right_mod_gamma
      (n := 4) (r := 2) (s := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hq hz d).symm
  have hinnerLift1 := paperComm_left_of_modEq_gamma
    (r := 4) (s := 1) (by norm_num) (by norm_num) hinner hz
  have hinnerLift2 := paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinnerLift1 hz
  have hfinal : paperComm (paperComm (paperComm q (z ^ d)) z) z ∈ gamma G 6 := by
    have h4 : paperComm q (z ^ d) ∈ gamma G 4 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hzd
    have h5 : paperComm (paperComm q (z ^ d)) z ∈ gamma G 5 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) h4 hz
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) h5 hz
  exact houter.symm.trans <| hmidLift.trans <| hinnerLift2.trans <| by
    rw [modEq_one_iff_mem]
    exact hfinal

/-- Vanishing for `[ξ,x,z,[ξ,x]]^d`. -/
theorem weightFive_commutator_suffix_power_vanish
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) {d : ℤ} (hzd : z ^ d ∈ gamma G 2) :
    ModGammaSix
      (paperComm (paperComm (paperComm ξ x) z) (paperComm ξ x) ^ d) 1 := by
  let q := paperComm ξ x
  let r := paperComm q z
  have hq : q ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hr : r ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hz
  have houter : ModGammaSix (paperComm (r ^ d) q) (paperComm r q ^ d) :=
    paperComm_zpow_left_mod_gamma (n := 6) (r := 3) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hr hq d
  have hinner : ModEq (gamma G 4) (r ^ d) (paperComm q (z ^ d)) :=
    (paperComm_zpow_right_mod_gamma
      (n := 4) (r := 2) (s := 1) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) hq hz d).symm
  have hlift := paperComm_left_of_modEq_gamma
    (r := 4) (s := 2) (by norm_num) (by norm_num) hinner hq
  have hfinal : paperComm (paperComm q (z ^ d)) q ∈ gamma G 6 := by
    have h4 : paperComm q (z ^ d) ∈ gamma G 4 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hzd
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) h4 hq
  exact houter.symm.trans <| hlift.trans <| by
    rw [modEq_one_iff_mem]
    exact hfinal

end

end D5
