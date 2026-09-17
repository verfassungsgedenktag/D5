import D5.HallPetresco

/-!
# The full power transfer in formula (20)

This file derives the local collection identities used in formula (20).
All variables have weight one; the proof keeps every correction through
weight five and discards only `γ₆`.
-/

namespace D5

universe u

section

variable {G : Type u} [Group G]

private theorem commute_gamma_three_in_quotient
    {x y : G} (hx : x ∈ gamma G 3) (hy : y ∈ gamma G 3) :
    Commute ((x : G ⧸ gamma G 6)) (y : G ⧸ gamma G 6) := by
  show (x : G ⧸ gamma G 6) * y = y * x
  exact mul_comm_mod_gamma (n := 6) (r := 3) (s := 3)
    (by norm_num) (by norm_num) (by norm_num) hx hy

private theorem mul_zpow_mod_gamma_three
    {x y : G} (hx : x ∈ gamma G 3) (hy : y ∈ gamma G 3) (v : ℤ) :
    ModGammaSix ((x * y) ^ v) (x ^ v * y ^ v) := by
  change (((x * y) ^ v : G) : G ⧸ gamma G 6) =
    ((x ^ v * y ^ v : G) : G ⧸ gamma G 6)
  rw [QuotientGroup.mk_zpow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
    QuotientGroup.mk_zpow, QuotientGroup.mk_zpow]
  exact (commute_gamma_three_in_quotient hx hy).mul_zpow v

private theorem six_mul_zpow_mod_gamma_three
    {a b c d e f : G}
    (ha : a ∈ gamma G 3) (hb : b ∈ gamma G 3)
    (hc : c ∈ gamma G 3) (hd : d ∈ gamma G 3)
    (he : e ∈ gamma G 3) (hf : f ∈ gamma G 3) (v : ℤ) :
    ModGammaSix ((((((a * b) * c) * d) * e) * f) ^ v)
      (((((a ^ v * b ^ v) * c ^ v) * d ^ v) * e ^ v) * f ^ v) := by
  have hab : a * b ∈ gamma G 3 := (gamma G 3).mul_mem ha hb
  have habc : (a * b) * c ∈ gamma G 3 := (gamma G 3).mul_mem hab hc
  have habcd : ((a * b) * c) * d ∈ gamma G 3 :=
    (gamma G 3).mul_mem habc hd
  have habcde : (((a * b) * c) * d) * e ∈ gamma G 3 :=
    (gamma G 3).mul_mem habcd he
  have h2 := mul_zpow_mod_gamma_three ha hb v
  have h3 := (mul_zpow_mod_gamma_three hab hc v).trans <|
    h2.mul (ModEq.refl (gamma G 6) (c ^ v))
  have h4 := (mul_zpow_mod_gamma_three habc hd v).trans <|
    h3.mul (ModEq.refl (gamma G 6) (d ^ v))
  have h5 := (mul_zpow_mod_gamma_three habcd he v).trans <|
    h4.mul (ModEq.refl (gamma G 6) (e ^ v))
  exact (mul_zpow_mod_gamma_three habcde hf v).trans <|
    h5.mul (ModEq.refl (gamma G 6) (f ^ v))

/-- Expansion of the main term on the right of (20). -/
theorem formula20_main_term_expansion
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) (n : ℕ) :
    ModGammaSix
      (paperComm (paperComm ξ (x ^ (n : ℤ))) z)
      (((paperComm (paperComm ξ x) z ^ (n : ℤ) *
          paperComm (paperComm (paperComm ξ x) z) (paperComm ξ x) ^
            TaharaArithmetic.binom2 n) *
        paperComm (paperComm (paperComm ξ x) x) z ^
          TaharaArithmetic.binom2 n) *
        paperComm (paperComm (paperComm (paperComm ξ x) x) x) z ^
          TaharaArithmetic.binom3 n) := by
  let q := paperComm ξ x
  let d := paperComm q x
  let e := paperComm d x
  let A := paperComm q z
  let K := paperComm A q
  have hq : q ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hd : d ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have he : e ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hx
  have hinner : ModEq (gamma G 5) (paperComm ξ (x ^ (n : ℤ)))
      (q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n *
        e ^ TaharaArithmetic.binom3 n) := by
    simpa [q, d, e] using
      paperComm_zpow_right_hallPetresco_mod_gamma_five hξ hx n
  have htransport : ModGammaSix
      (paperComm (paperComm ξ (x ^ (n : ℤ))) z)
      (paperComm
        (q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n *
          e ^ TaharaArithmetic.binom3 n) z) :=
    paperComm_left_of_modEq_gamma
      (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hz
  have hqn : q ^ (n : ℤ) ∈ gamma G 2 :=
    (gamma G 2).zpow_mem hq (n : ℤ)
  have hdn : d ^ TaharaArithmetic.binom2 n ∈ gamma G 3 :=
    (gamma G 3).zpow_mem hd (TaharaArithmetic.binom2 n)
  have hen : e ^ TaharaArithmetic.binom3 n ∈ gamma G 4 :=
    (gamma G 4).zpow_mem he (TaharaArithmetic.binom3 n)
  have hqd : q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n ∈ gamma G 2 :=
    (gamma G 2).mul_mem hqn
      (gamma_antitone G (by norm_num) hdn)
  have houter : ModGammaSix
      (paperComm
        (q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n *
          e ^ TaharaArithmetic.binom3 n) z)
      (paperComm (q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) z *
        paperComm (e ^ TaharaArithmetic.binom3 n) z) :=
    paperComm_mul_left_mod_gamma
      (n := 6) (r := 2) (s := 4) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hqd hen hz
  have hfirst : ModGammaSix
      (paperComm (q ^ (n : ℤ) * d ^ TaharaArithmetic.binom2 n) z)
      (paperComm (q ^ (n : ℤ)) z *
        paperComm (d ^ TaharaArithmetic.binom2 n) z) :=
    paperComm_mul_left_mod_gamma
      (n := 6) (r := 2) (s := 3) (t := 1)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      hqn hdn hz
  have hqpow : ModGammaSix (paperComm (q ^ (n : ℤ)) z)
      (A ^ (n : ℤ) * K ^ TaharaArithmetic.binom2 n) := by
    simpa [A, K] using
      paperComm_zpow_left_hallPetresco_weight_two hq hz n
  have hdpow : ModGammaSix
      (paperComm (d ^ TaharaArithmetic.binom2 n) z)
      (paperComm d z ^ TaharaArithmetic.binom2 n) :=
    paperComm_zpow_left_mod_gamma
      (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hd hz _
  have hepow : ModGammaSix
      (paperComm (e ^ TaharaArithmetic.binom3 n) z)
      (paperComm e z ^ TaharaArithmetic.binom3 n) :=
    paperComm_zpow_left_mod_gamma
      (n := 6) (r := 4) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) he hz _
  exact htransport.trans <| houter.trans <|
    (hfirst.trans (hqpow.mul hdpow)).mul hepow

/-- The first inverse replacement in (20): `[x,ξ,x,z]` is the inverse of
`[ξ,x,x,z]` modulo `γ₆`. -/
theorem formula20_swap_xi_x_x_z
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) :
    ModGammaSix
      (paperComm (paperComm (paperComm x ξ) x) z)
      (paperComm (paperComm (paperComm ξ x) x) z)⁻¹ := by
  let q := paperComm ξ x
  let d := paperComm q x
  have hq : q ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hd : d ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have hinner : ModEq (gamma G 5) (paperComm q⁻¹ x) d⁻¹ :=
    paperComm_inv_left_mod_gamma
      (n := 5) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hx
  have hlift := paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hz
  have hinv : ModGammaSix (paperComm d⁻¹ z) (paperComm d z)⁻¹ :=
    paperComm_inv_left_mod_gamma
      (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hd hz
  rw [show paperComm x ξ = q⁻¹ by exact paperComm_swap ξ x]
  exact hlift.trans hinv

/-- The second inverse replacement in (20). -/
theorem formula20_swap_xi_x_z_z
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) :
    ModGammaSix
      (paperComm (paperComm (paperComm x ξ) z) z)
      (paperComm (paperComm (paperComm ξ x) z) z)⁻¹ := by
  let q := paperComm ξ x
  let A := paperComm q z
  have hq : q ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hA : A ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hz
  have hinner : ModEq (gamma G 5) (paperComm q⁻¹ z) A⁻¹ :=
    paperComm_inv_left_mod_gamma
      (n := 5) (r := 2) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hq hz
  have hlift := paperComm_left_of_modEq_gamma
    (r := 5) (s := 1) (by norm_num) (by norm_num) hinner hz
  have hinv : ModGammaSix (paperComm A⁻¹ z) (paperComm A z)⁻¹ :=
    paperComm_inv_left_mod_gamma
      (n := 6) (r := 3) (s := 1)
      (by norm_num) (by norm_num) (by norm_num) hA hz
  rw [show paperComm x ξ = q⁻¹ by exact paperComm_swap ξ x]
  exact hlift.trans hinv

private theorem formula20_cancel_in_commuting_range
    {Q : Type*} [Group Q] {a k d e b c : Q}
    (hed : Commute e d) (heb : Commute e b) (hek : Commute e k)
    (hkb : Commute k b) (hec : Commute e c) :
    (((((((a * k) * d) * e) * d⁻¹) * b) * k⁻¹) * c) * e⁻¹ =
      (a * b) * c := by
  calc
    (((((((a * k) * d) * e) * d⁻¹) * b) * k⁻¹) * c) * e⁻¹ =
        a * k * d * (e * d⁻¹) * b * k⁻¹ * c * e⁻¹ := by group
    _ = a * k * d * (d⁻¹ * e) * b * k⁻¹ * c * e⁻¹ := by
      rw [hed.inv_right.eq]
    _ = a * k * e * b * k⁻¹ * c * e⁻¹ := by group
    _ = (a * k) * (e * b) * k⁻¹ * c * e⁻¹ := by group
    _ = (a * k) * (b * e) * k⁻¹ * c * e⁻¹ := by rw [heb.eq]
    _ = a * k * b * e * k⁻¹ * c * e⁻¹ := by group
    _ = (a * k * b) * (e * k⁻¹) * c * e⁻¹ := by group
    _ = (a * k * b) * (k⁻¹ * e) * c * e⁻¹ := by
      rw [hek.inv_right.eq]
    _ = a * k * b * k⁻¹ * e * c * e⁻¹ := by group
    _ = a * (k * b) * k⁻¹ * e * c * e⁻¹ := by group
    _ = a * (b * k) * k⁻¹ * e * c * e⁻¹ := by rw [hkb.eq]
    _ = a * b * k * k⁻¹ * e * c * e⁻¹ := by group
    _ = a * b * e * c * e⁻¹ := by group
    _ = (a * b) * (e * c) * e⁻¹ := by group
    _ = (a * b) * (c * e) * e⁻¹ := by rw [hec.eq]
    _ = a * b * c * e * e⁻¹ := by group
    _ = (a * b) * c := by group

/-- Formula (20) before the common outer exponent `u` is applied. -/
theorem transfer_formula20_base
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) (n : ℕ) :
    ModGammaSix
      (paperComm (paperComm ξ x) (z ^ (n : ℤ)))
      (paperComm (paperComm ξ (x ^ (n : ℤ))) z *
        paperComm (paperComm (paperComm x ξ) x) z ^
          TaharaArithmetic.binom2 n *
        paperComm (paperComm (paperComm x ξ) z) z ^
          (-TaharaArithmetic.binom2 n) *
        paperComm (paperComm (paperComm ξ x) z) (paperComm ξ x) ^
          (-TaharaArithmetic.binom2 n) *
        paperComm
          (paperComm (paperComm (paperComm ξ x) z) z) z ^
            TaharaArithmetic.binom3 n *
        paperComm
          (paperComm (paperComm (paperComm ξ x) x) x) z ^
            (-TaharaArithmetic.binom3 n)) := by
  let q := paperComm ξ x
  let A := paperComm q z
  let B := paperComm A z
  let C := paperComm B z
  let d := paperComm q x
  let e := paperComm d x
  let K := paperComm A q
  let dz := paperComm d z
  let ez := paperComm e z
  let D := paperComm (paperComm (paperComm x ξ) x) z
  let E := paperComm (paperComm (paperComm x ξ) z) z
  have hq : q ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hA : A ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hz
  have hB : B ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hz
  have hC : C ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hB hz
  have hd : d ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have he : e ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hx
  have hK : K ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hq
  have hdz : dz ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hz
  have hez : ez ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) he hz
  have hleft : ModGammaSix
      (paperComm q (z ^ (n : ℤ)))
      (A ^ (n : ℤ) * B ^ TaharaArithmetic.binom2 n *
        C ^ TaharaArithmetic.binom3 n) := by
    simpa [A, B, C] using paperComm_zpow_right_hallPetresco hq hz n
  have hmain : ModGammaSix
      (paperComm (paperComm ξ (x ^ (n : ℤ))) z)
      (((A ^ (n : ℤ) * K ^ TaharaArithmetic.binom2 n) *
        dz ^ TaharaArithmetic.binom2 n) *
        ez ^ TaharaArithmetic.binom3 n) := by
    simpa [q, A, K, d, e, dz, ez] using
      formula20_main_term_expansion hξ hx hz n
  have hD : ModGammaSix D dz⁻¹ := by
    simpa [q, D, d, dz] using formula20_swap_xi_x_x_z hξ hx hz
  have hE : ModGammaSix E B⁻¹ := by
    simpa [q, E, A, B] using formula20_swap_xi_x_z_z hξ hx hz
  have hcorrections : ModGammaSix
      (paperComm (paperComm ξ (x ^ (n : ℤ))) z *
        D ^ TaharaArithmetic.binom2 n *
        E ^ (-TaharaArithmetic.binom2 n) *
        K ^ (-TaharaArithmetic.binom2 n) *
        C ^ TaharaArithmetic.binom3 n *
        ez ^ (-TaharaArithmetic.binom3 n))
      (A ^ (n : ℤ) * K ^ TaharaArithmetic.binom2 n *
        dz ^ TaharaArithmetic.binom2 n *
        ez ^ TaharaArithmetic.binom3 n *
        (dz ^ TaharaArithmetic.binom2 n)⁻¹ *
        B ^ TaharaArithmetic.binom2 n *
        (K ^ TaharaArithmetic.binom2 n)⁻¹ *
        C ^ TaharaArithmetic.binom3 n *
        (ez ^ TaharaArithmetic.binom3 n)⁻¹) := by
    have hDz := hD.zpow (TaharaArithmetic.binom2 n)
    have hEz := hE.zpow (-TaharaArithmetic.binom2 n)
    simpa only [inv_zpow, zpow_neg, inv_inv] using
      (((((hmain.mul hDz).mul hEz).mul
        (ModEq.refl (gamma G 6) (K ^ (-TaharaArithmetic.binom2 n)))).mul
        (ModEq.refl (gamma G 6) (C ^ TaharaArithmetic.binom3 n))).mul
        (ModEq.refl (gamma G 6) (ez ^ (-TaharaArithmetic.binom3 n))))
  have ha3 : A ^ (n : ℤ) ∈ gamma G 3 :=
    (gamma G 3).zpow_mem hA (n : ℤ)
  have hk3 : K ^ TaharaArithmetic.binom2 n ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <|
      (gamma G 5).zpow_mem hK (TaharaArithmetic.binom2 n)
  have hd3 : dz ^ TaharaArithmetic.binom2 n ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <|
      (gamma G 4).zpow_mem hdz (TaharaArithmetic.binom2 n)
  have he3 : ez ^ TaharaArithmetic.binom3 n ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <|
      (gamma G 5).zpow_mem hez (TaharaArithmetic.binom3 n)
  have hb3 : B ^ TaharaArithmetic.binom2 n ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <|
      (gamma G 4).zpow_mem hB (TaharaArithmetic.binom2 n)
  have hc3 : C ^ TaharaArithmetic.binom3 n ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <|
      (gamma G 5).zpow_mem hC (TaharaArithmetic.binom3 n)
  have hcancel : ModGammaSix
      (A ^ (n : ℤ) * K ^ TaharaArithmetic.binom2 n *
        dz ^ TaharaArithmetic.binom2 n *
        ez ^ TaharaArithmetic.binom3 n *
        (dz ^ TaharaArithmetic.binom2 n)⁻¹ *
        B ^ TaharaArithmetic.binom2 n *
        (K ^ TaharaArithmetic.binom2 n)⁻¹ *
        C ^ TaharaArithmetic.binom3 n *
        (ez ^ TaharaArithmetic.binom3 n)⁻¹)
      (A ^ (n : ℤ) * B ^ TaharaArithmetic.binom2 n *
        C ^ TaharaArithmetic.binom3 n) := by
    change
      (((((((((A ^ (n : ℤ) : G) : G ⧸ gamma G 6) *
        K ^ TaharaArithmetic.binom2 n) *
        dz ^ TaharaArithmetic.binom2 n) *
        ez ^ TaharaArithmetic.binom3 n) *
        (dz ^ TaharaArithmetic.binom2 n)⁻¹) *
        B ^ TaharaArithmetic.binom2 n) *
        (K ^ TaharaArithmetic.binom2 n)⁻¹) *
        C ^ TaharaArithmetic.binom3 n) *
        (ez ^ TaharaArithmetic.binom3 n)⁻¹ =
      (A ^ (n : ℤ) : G ⧸ gamma G 6) *
        B ^ TaharaArithmetic.binom2 n * C ^ TaharaArithmetic.binom3 n
    apply formula20_cancel_in_commuting_range
    all_goals
      exact commute_gamma_three_in_quotient (by assumption) (by assumption)
  change ModGammaSix (paperComm q (z ^ (n : ℤ))) _
  exact hleft.trans (hcorrections.trans hcancel).symm

/-- Formula (20), including the arbitrary common exponent `u`. -/
theorem transfer_formula20
    {ξ x z : G} (hξ : ξ ∈ gamma G 1) (hx : x ∈ gamma G 1)
    (hz : z ∈ gamma G 1) (n : ℕ) (u : ℤ) :
    ModGammaSix
      (paperComm (paperComm ξ x) (z ^ (n : ℤ)) ^ u)
      (paperComm (paperComm ξ (x ^ (n : ℤ))) z ^ u *
        paperComm (paperComm (paperComm x ξ) x) z ^
          (u * TaharaArithmetic.binom2 n) *
        paperComm (paperComm (paperComm x ξ) z) z ^
          (-u * TaharaArithmetic.binom2 n) *
        paperComm (paperComm (paperComm ξ x) z) (paperComm ξ x) ^
          (-u * TaharaArithmetic.binom2 n) *
        paperComm
          (paperComm (paperComm (paperComm ξ x) z) z) z ^
            (u * TaharaArithmetic.binom3 n) *
        paperComm
          (paperComm (paperComm (paperComm ξ x) x) x) z ^
            (-u * TaharaArithmetic.binom3 n)) := by
  let P := paperComm (paperComm ξ (x ^ (n : ℤ))) z
  let D := paperComm (paperComm (paperComm x ξ) x) z
  let E := paperComm (paperComm (paperComm x ξ) z) z
  let K := paperComm (paperComm (paperComm ξ x) z) (paperComm ξ x)
  let C := paperComm (paperComm (paperComm (paperComm ξ x) z) z) z
  let H := paperComm (paperComm (paperComm (paperComm ξ x) x) x) z
  let b2 := TaharaArithmetic.binom2 n
  let b3 := TaharaArithmetic.binom3 n
  have hq : paperComm ξ x ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hx
  have hxn : x ^ (n : ℤ) ∈ gamma G 1 :=
    (gamma G 1).zpow_mem hx (n : ℤ)
  have hP : P ∈ gamma G 3 := by
    apply paperComm_mem_gamma_add (by norm_num) (by norm_num) _ hz
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hξ hxn
  have hxξ : paperComm x ξ ∈ gamma G 2 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hx hξ
  have hD : D ∈ gamma G 4 := by
    apply paperComm_mem_gamma_add (by norm_num) (by norm_num) _ hz
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num) hxξ hx
  have hE : E ∈ gamma G 4 := by
    exact paperComm_mem_gamma_add (by norm_num) (by norm_num)
      (paperComm_mem_gamma_add (by norm_num) (by norm_num) hxξ hz) hz
  have hA : paperComm (paperComm ξ x) z ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hz
  have hK : K ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hq
  have hB : paperComm (paperComm (paperComm ξ x) z) z ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hA hz
  have hC : C ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hB hz
  have hd : paperComm (paperComm ξ x) x ∈ gamma G 3 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hq hx
  have he : paperComm (paperComm (paperComm ξ x) x) x ∈ gamma G 4 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) hd hx
  have hH : H ∈ gamma G 5 :=
    paperComm_mem_gamma_add (by norm_num) (by norm_num) he hz
  have hbase : ModGammaSix
      (paperComm (paperComm ξ x) (z ^ (n : ℤ)))
      (P * D ^ b2 * E ^ (-b2) * K ^ (-b2) * C ^ b3 * H ^ (-b3)) := by
    simpa [P, D, E, K, C, H, b2, b3] using
      transfer_formula20_base hξ hx hz n
  have hP3 : P ∈ gamma G 3 := hP
  have hD3 : D ^ b2 ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <| (gamma G 4).zpow_mem hD b2
  have hE3 : E ^ (-b2) ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <| (gamma G 4).zpow_mem hE (-b2)
  have hK3 : K ^ (-b2) ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <| (gamma G 5).zpow_mem hK (-b2)
  have hC3 : C ^ b3 ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <| (gamma G 5).zpow_mem hC b3
  have hH3 : H ^ (-b3) ∈ gamma G 3 :=
    gamma_antitone G (by norm_num) <| (gamma G 5).zpow_mem hH (-b3)
  have hdist := six_mul_zpow_mod_gamma_three
    hP3 hD3 hE3 hK3 hC3 hH3 u
  refine (hbase.zpow u).trans <| hdist.trans ?_
  simp only [← zpow_mul]
  simp only [P, D, E, K, C, H, b2, b3]
  congr 1
  all_goals ring_nf

end

end D5
