import D5.Rotation

/-!
# Weight-five corrections in the rotation formula

The lemmas here retain the corrections which disappeared in
`rotation_main_mod_gamma_five`.  Together they are the local calculation
behind formula (19).
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

theorem hallWitt_first_factor_mod_gamma_six
    {a b c : G} (ha : a ∈ gamma G 2)
    (hb : b ∈ gamma G 1) (hc : c ∈ gamma G 1) :
    ModGammaSix
      (conjugateBy (paperComm (paperComm a b⁻¹) c) b)
      ((paperComm (paperComm a b) c)⁻¹ *
        paperComm (paperComm (paperComm a b) b) c *
        (paperComm (paperComm (paperComm a b) c) b)⁻¹) := by
  let r := paperComm a b
  let A := paperComm r c
  let q := paperComm r⁻¹ b⁻¹
  let D := paperComm (paperComm r b) c
  let E := (paperComm A b)⁻¹
  have hr : r ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb
  have hA : A ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hr hc
  have hq : q ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num)
      ((gamma G 3).inv_mem hr) ((gamma G 1).inv_mem hb)
  have hinner : paperComm a b⁻¹ = r⁻¹ * q := by
    calc
      paperComm a b⁻¹ = conjugateBy (paperComm b a) b⁻¹ :=
        paperComm_inv_right a b
      _ = conjugateBy r⁻¹ b⁻¹ := by rw [paperComm_swap a b]
      _ = r⁻¹ * q := conjugateBy_eq_mul_paperComm r⁻¹ b⁻¹
  have hsplit : ModGammaSix (paperComm (paperComm a b⁻¹) c)
      (paperComm r⁻¹ c * paperComm q c) := by
    rw [hinner]
    exact paperComm_mul_left_mod_gamma
      (n := 6) (r := 3) (s := 4) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ((gamma G 3).inv_mem hr) hq hc
  have hAinv : ModGammaSix (paperComm r⁻¹ c) A⁻¹ :=
    paperComm_inv_left_mod_gamma (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hr hc
  have hqbase : ModEq (gamma G 5) q (paperComm r b) := by
    have hright : ModEq (gamma G 5) q (paperComm r⁻¹ b)⁻¹ :=
      paperComm_inv_right_mod_gamma (n := 5) (r := 3) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) ((gamma G 3).inv_mem hr) hb
    have hleft : ModEq (gamma G 5) (paperComm r⁻¹ b) (paperComm r b)⁻¹ :=
      paperComm_inv_left_mod_gamma (n := 5) (r := 3) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) hr hb
    exact hright.trans (by
      have := hleft.inv
      simpa using this)
  have hqcomm : ModGammaSix (paperComm q c) D :=
    paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hqbase hc
  have hbase : ModGammaSix (paperComm (paperComm a b⁻¹) c) (A⁻¹ * D) :=
    hsplit.trans (hAinv.mul hqcomm)
  have hbase5 : ModEq (gamma G 5) (paperComm (paperComm a b⁻¹) c) A⁻¹ := by
    have hweak := hbase.mono (gamma_antitone G (by norm_num : 5 ≤ 6))
    have hD : D ∈ gamma G 5 := by
      have hrb : paperComm r b ∈ gamma G 4 :=
        paperComm_mem_gamma_add (by norm_num) (by norm_num) hr hb
      exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hrb hc
    exact hweak.trans <| by
      simpa using (ModEq.refl (gamma G 5) A⁻¹).mul
        (show ModEq (gamma G 5) D 1 by rw [modEq_one_iff_mem]; exact hD)
  have hcorr : ModGammaSix
      (paperComm (paperComm (paperComm a b⁻¹) c) b) E := by
    have hlift := paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hbase5 hb
    exact hlift.trans <|
      paperComm_inv_left_mod_gamma (n := 6) (r := 4) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) hA hb
  rw [conjugateBy_eq_mul_paperComm]
  exact hbase.mul hcorr

theorem hallWitt_second_factor_mod_gamma_six
    {a b c : G} (ha : a ∈ gamma G 2)
    (hb : b ∈ gamma G 1) (hc : c ∈ gamma G 1) :
    ModGammaSix
      (conjugateBy (paperComm (paperComm b c⁻¹) a) c)
      (paperComm (paperComm c b) a *
        paperComm (paperComm (paperComm b c) c) a *
        (paperComm (paperComm (paperComm b c) a) c)⁻¹) := by
  let p := paperComm b c
  let s := paperComm c b
  let B := paperComm s a
  let q := paperComm s c⁻¹
  let F := paperComm (paperComm p c) a
  let Gc := (paperComm (paperComm p a) c)⁻¹
  have hp : p ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hc
  have hs : s ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hc hb
  have hB : B ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hs ha
  have hq : q ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hs
      ((gamma G 1).inv_mem hc)
  have hinner : paperComm b c⁻¹ = s * q := by
    calc
      paperComm b c⁻¹ = conjugateBy (paperComm c b) c⁻¹ :=
        paperComm_inv_right b c
      _ = s * q := conjugateBy_eq_mul_paperComm s c⁻¹
  have hsplit : ModGammaSix (paperComm (paperComm b c⁻¹) a)
      (B * paperComm q a) := by
    rw [hinner]
    exact paperComm_mul_left_mod_gamma
      (n := 6) (r := 2) (s := 3) (t := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) hs hq ha
  have hqbase : ModEq (gamma G 4) q (paperComm p c) := by
    have hright : ModEq (gamma G 4) q (paperComm s c)⁻¹ :=
      paperComm_inv_right_mod_gamma (n := 4) (r := 2) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) hs hc
    have hsp : s = p⁻¹ := paperComm_swap b c
    have hleft : ModEq (gamma G 4) (paperComm s c) (paperComm p c)⁻¹ := by
      rw [hsp]
      exact paperComm_inv_left_mod_gamma (n := 4) (r := 2) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) hp hc
    exact hright.trans (by
      have := hleft.inv
      simpa using this)
  have hqcomm : ModGammaSix (paperComm q a) F :=
    paperComm_left_of_modEq_gamma
      (r := 4) (s := 2) (by norm_num) (by norm_num) hqbase ha
  have hbase : ModGammaSix (paperComm (paperComm b c⁻¹) a) (B * F) :=
    hsplit.trans ((ModEq.refl (gamma G 6) B).mul hqcomm)
  have hbase5 : ModEq (gamma G 5) (paperComm (paperComm b c⁻¹) a) B := by
    have hweak := hbase.mono (gamma_antitone G (by norm_num : 5 ≤ 6))
    have hF : F ∈ gamma G 5 := by
      have hpc : paperComm p c ∈ gamma G 3 :=
        paperComm_mem_gamma_add (by norm_num) (by norm_num) hp hc
      exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hpc ha
    exact hweak.trans <| by
      simpa using (ModEq.refl (gamma G 5) B).mul
        (show ModEq (gamma G 5) F 1 by rw [modEq_one_iff_mem]; exact hF)
  have hBbase : ModEq (gamma G 5) B (paperComm p a)⁻¹ := by
    change ModEq (gamma G 5) (paperComm s a) (paperComm p a)⁻¹
    rw [show s = p⁻¹ by exact paperComm_swap b c]
    exact paperComm_inv_left_mod_gamma (n := 5) (r := 2) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hp ha
  have hcorr : ModGammaSix
      (paperComm (paperComm (paperComm b c⁻¹) a) c) Gc := by
    have h1 := paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hbase5 hc
    have h2 := paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hBbase hc
    have hpa : paperComm p a ∈ gamma G 4 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hp ha
    exact h1.trans <| h2.trans <|
      paperComm_inv_left_mod_gamma (n := 6) (r := 4) (s := 1)
        (by norm_num) (by norm_num) (by norm_num) hpa hc
  rw [conjugateBy_eq_mul_paperComm]
  exact hbase.mul hcorr

theorem hallWitt_third_factor_mod_gamma_six
    {a b c : G} (ha : a ∈ gamma G 2)
    (hb : b ∈ gamma G 1) (hc : c ∈ gamma G 1) :
    ModGammaSix
      (conjugateBy (paperComm (paperComm c a⁻¹) b) a)
      (paperComm (paperComm c a) b)⁻¹ := by
  have hca : paperComm c a ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hc ha
  have hinner : ModEq (gamma G 5) (paperComm c a⁻¹) (paperComm c a)⁻¹ :=
    paperComm_inv_right_mod_gamma (n := 5) (r := 1) (s := 2)
      (by norm_num) (by norm_num) (by norm_num) hc ha
  have hlift := paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hb
  have hinv : ModGammaSix (paperComm (paperComm c a)⁻¹ b)
      (paperComm (paperComm c a) b)⁻¹ :=
    paperComm_inv_left_mod_gamma (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hca hb
  have hraw : paperComm (paperComm c a⁻¹) b ∈ gamma G 4 := by
    have hi : paperComm c a⁻¹ ∈ gamma G 3 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hc
        ((gamma G 2).inv_mem ha)
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hi hb
  exact (conjugateBy_mod_gamma (n := 6) (r := 4) (s := 2)
    (by norm_num) (by norm_num) (by norm_num) hraw ha).trans (hlift.trans hinv)

/-- Formula (19), including all four corrections of weight five. -/
theorem rotation_formula19
    {a b c : G} (ha : a ∈ gamma G 2)
    (hb : b ∈ gamma G 1) (hc : c ∈ gamma G 1) :
    ModGammaSix (paperComm (paperComm a b) c)
      ((paperComm (paperComm c a) b)⁻¹ *
        paperComm (paperComm c b) a *
        paperComm (paperComm (paperComm a b) b) c *
        (paperComm (paperComm (paperComm a b) c) b)⁻¹ *
        paperComm (paperComm (paperComm b c) c) a *
        (paperComm (paperComm (paperComm b c) a) c)⁻¹) := by
  let A := paperComm (paperComm a b) c
  let B := paperComm (paperComm c b) a
  let C := paperComm (paperComm c a) b
  let D := paperComm (paperComm (paperComm a b) b) c
  let E := (paperComm (paperComm (paperComm a b) c) b)⁻¹
  let F := paperComm (paperComm (paperComm b c) c) a
  let H := (paperComm (paperComm (paperComm b c) a) c)⁻¹
  have h1 := hallWitt_first_factor_mod_gamma_six ha hb hc
  have h2 := hallWitt_second_factor_mod_gamma_six ha hb hc
  have h3 := hallWitt_third_factor_mod_gamma_six ha hb hc
  have hHall : ModGammaSix
      (conjugateBy (paperComm (paperComm a b⁻¹) c) b *
        conjugateBy (paperComm (paperComm b c⁻¹) a) c *
        conjugateBy (paperComm (paperComm c a⁻¹) b) a) 1 := by
    rw [hallWitt]
  have hrel : ModGammaSix ((A⁻¹ * D * E) * (B * F * H) * C⁻¹) 1 := by
    exact ((h1.mul h2).mul h3).symm.trans hHall
  let X := D * E
  let Y := F * H
  have hsolve0 : ModGammaSix A (D * E * B * (F * H) * C⁻¹) := by
    change (A : G ⧸ gamma G 6) =
      ((D * E * B * (F * H) * C⁻¹ : G) : G ⧸ gamma G 6)
    have hq : (((A⁻¹ * D * E) * (B * F * H) * C⁻¹ : G) :
        G ⧸ gamma G 6) = 1 := hrel
    calc
      (A : G ⧸ gamma G 6) = A * 1 := by simp
      _ = (A : G ⧸ gamma G 6) *
          ((((A⁻¹ * D * E) * (B * F * H) * C⁻¹ : G) : G ⧸ gamma G 6)) := by rw [hq]
      _ = ((D * E * B * (F * H) * C⁻¹ : G) : G ⧸ gamma G 6) := by
        change (A : G ⧸ gamma G 6) *
          ((((A : G ⧸ gamma G 6)⁻¹ * (D : G ⧸ gamma G 6)) *
            (E : G ⧸ gamma G 6)) *
            (((B : G ⧸ gamma G 6) * (F : G ⧸ gamma G 6)) *
              (H : G ⧸ gamma G 6)) *
            (C : G ⧸ gamma G 6)⁻¹) =
          (D : G ⧸ gamma G 6) * (E : G ⧸ gamma G 6) *
            (B : G ⧸ gamma G 6) * ((F : G ⧸ gamma G 6) *
              (H : G ⧸ gamma G 6)) * (C : G ⧸ gamma G 6)⁻¹
        group
  have hsolve : ModGammaSix A (X * B * Y * C⁻¹) := by
    simpa only [X, Y, mul_assoc] using hsolve0
  have hab : paperComm a b ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) ha hb
  have hcb : paperComm c b ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hc hb
  have hca : paperComm c a ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hc ha
  have hB : B ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hcb ha
  have hC : C ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hca hb
  have hD : D ∈ gamma G 5 := by
    have h : paperComm (paperComm a b) b ∈ gamma G 4 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hab hb
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) h hc
  have hE : E ∈ gamma G 5 := by
    have h : paperComm (paperComm a b) c ∈ gamma G 4 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hab hc
    exact (gamma G 5).inv_mem
      (paperComm_mem_gamma_add (by norm_num) (by norm_num) h hb)
  have hp : paperComm b c ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hb hc
  have hF : F ∈ gamma G 5 := by
    have h : paperComm (paperComm b c) c ∈ gamma G 3 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hp hc
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) h ha
  have hH : H ∈ gamma G 5 := by
    have h : paperComm (paperComm b c) a ∈ gamma G 4 :=
      paperComm_mem_gamma_add (by norm_num) (by norm_num) hp ha
    exact (gamma G 5).inv_mem
      (paperComm_mem_gamma_add (by norm_num) (by norm_num) h hc)
  have hX : X ∈ gamma G 4 := by
    exact (gamma G 4).mul_mem (gamma_antitone G (by norm_num) hD)
      (gamma_antitone G (by norm_num) hE)
  have hY : Y ∈ gamma G 4 := by
    exact (gamma G 4).mul_mem (gamma_antitone G (by norm_num) hF)
      (gamma_antitone G (by norm_num) hH)
  have hswapXB : ModGammaSix (X * B) (B * X) :=
    mul_comm_mod_gamma (n := 6) (r := 4) (s := 4)
      (by norm_num) (by norm_num) (by norm_num) hX hB
  have hZ : B * X * Y ∈ gamma G 4 :=
    (gamma G 4).mul_mem ((gamma G 4).mul_mem hB hX) hY
  have hswapC : ModGammaSix ((B * X * Y) * C⁻¹) (C⁻¹ * (B * X * Y)) :=
    mul_comm_mod_gamma (n := 6) (r := 4) (s := 4)
      (by norm_num) (by norm_num) (by norm_num) hZ ((gamma G 4).inv_mem hC)
  have hreorder : ModGammaSix (X * B * Y * C⁻¹) (C⁻¹ * (B * X * Y)) :=
    (((hswapXB.mul (ModEq.refl (gamma G 6) Y)).mul
      (ModEq.refl (gamma G 6) C⁻¹))).trans hswapC
  simpa only [X, Y, A, B, C, D, E, F, H, mul_assoc] using hsolve.trans hreorder

end

end D5
