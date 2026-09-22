import D5.TaharaCondition13

/-!
# The local alpha-coordinate expansion for formula (28)

Relation (3) expresses a power commutator of first-layer generators in the
`x₃` coordinates.  Here it is transported through the two commutators used
in formula (28).
-/

namespace D5.Tahara

universe u

noncomputable section

variable {G : Type u} [Group G]

def alphaCoordinateBlock
    (C : Context G) (ξ : G) (i g h : Fin C.s) : G :=
  orderedProduct fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^ C.alpha g h l

theorem alpha_coordinate_expansion
    (C : Context G) (ξ : G) (i g h : Fin C.s) (hgh : g < h) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
        (C.x1 i))
      (alphaCoordinateBlock C ξ i g h) := by
  have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
  have hreplace := nested_middle_of_modEq_gamma4 hξ hxi
    (C.x1_power_comm g h hgh)
  have hcollect := nested_weight_three_orderedProduct_right hξ hxi
    (fun l => C.x3 l ^ C.alpha g h l)
    (fun l => (D5.gamma G 3).zpow_mem (C.x3_mem_gamma3 l) _)
  refine (show D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
        (C.x1 i))
      (orderedProduct fun l =>
        D5.paperComm
          (D5.paperComm ξ (C.x3 l ^ C.alpha g h l)) (C.x1 i)) by
    exact hreplace.trans <| hcollect).trans ?_
  unfold alphaCoordinateBlock
  apply modEq_orderedProduct
  intro l
  exact nested_weight_three_zpow_right hξ (C.x3_mem_gamma3 l) hxi _

theorem alpha_coordinate_expansion_zpow
    (C : Context G) (ξ : G) (i g h : Fin C.s) (hgh : g < h)
    (z : ℤ) :
    D5.ModGammaSix
      (D5.paperComm
        (D5.paperComm ξ
          (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
        (C.x1 i) ^ z)
      (orderedProduct fun l =>
        D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
          (z * C.alpha g h l)) := by
  let A : Fin C.r → G := fun l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hbase := (alpha_coordinate_expansion C ξ i g h hgh).zpow z
  have hA : ∀ l, A l ^ C.alpha g h l ∈ D5.gamma G 3 := by
    intro l
    apply (D5.gamma G 3).zpow_mem
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x3_mem_gamma3 l)) hxi
  have hdistribute := D5.orderedProduct_zpow_gammaThree
    (fun l => A l ^ C.alpha g h l) hA z
  refine hbase.trans <| hdistribute.trans ?_
  apply modEq_orderedProduct
  intro l
  change D5.ModGammaSix ((A l ^ C.alpha g h l) ^ z)
    (A l ^ (z * C.alpha g h l))
  rw [← zpow_mul]
  congr 1
  ring

/-- The four coordinate streams occurring on the right hand side of (27).
Keeping them separate makes the subsequent use of relation (3) local to one
pair of first-layer indices at a time. -/
def formula28UCoordinateStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    ∑ h ∈ Finset.univ.filter (· < i),
      P.u h i * orderRatio C.d h i * C.alpha h i l

def formula28WLeftCoordinateStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    ∑ g ∈ Finset.univ.filter (· ≤ i),
      ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l

def formula28WRightCoordinateStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    ∑ g ∈ Finset.univ.filter (· ≤ i),
      ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
        P.w g h i * C.alpha g h l

def formula28WPrimeCoordinateStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
    ∑ g ∈ Finset.univ.filter (i < ·),
      ∑ h ∈ Finset.univ.filter (g ≤ ·), P.w' i g h * C.alpha g h l

/-- Formula (27), separated into the four alpha-coordinate streams which
are expanded in formula (28).  This is a collection calculation in the
weight-three quotient; no Tahara relation is used here. -/
theorem formula27_split_alpha_streams
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula27ReplacementGrouped C P ξ)
      ((formula28UCoordinateStream C P ξ *
          formula28WLeftCoordinateStream C P ξ) *
        (formula28WRightCoordinateStream C P ξ *
          formula28WPrimeCoordinateStream C P ξ)) := by
  let U : Fin C.s → Fin C.r → ℤ := fun i l =>
    ∑ h ∈ Finset.univ.filter (· < i),
      P.u h i * orderRatio C.d h i * C.alpha h i l
  let WL : Fin C.s → Fin C.r → ℤ := fun i l =>
    ∑ g ∈ Finset.univ.filter (· ≤ i),
      ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l
  let WR : Fin C.s → Fin C.r → ℤ := fun i l =>
    ∑ g ∈ Finset.univ.filter (· ≤ i),
      ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
        P.w g h i * C.alpha g h l
  let WP : Fin C.s → Fin C.r → ℤ := fun i l =>
    ∑ g ∈ Finset.univ.filter (i < ·),
      ∑ h ∈ Finset.univ.filter (g ≤ ·), P.w' i g h * C.alpha g h l
  have hrow : ∀ i,
      D5.ModGammaSix
        ((formula21ThirdCoordinateBlock C ξ i (U i) *
            formula21ThirdCoordinateBlock C ξ i (WL i)) *
          (formula21ThirdCoordinateBlock C ξ i (WR i) *
            formula21ThirdCoordinateBlock C ξ i (WP i)))
        (formula21ThirdCoordinateBlock C ξ i fun l =>
          (U i l + WL i l) + (WR i l + WP i l)) := by
    intro i
    exact ((formula21ThirdCoordinateBlock_add C ξ i (U i) (WL i)).mul
      (formula21ThirdCoordinateBlock_add C ξ i (WR i) (WP i))).trans
      (formula21ThirdCoordinateBlock_add C ξ i
        (fun l => U i l + WL i l) (fun l => WR i l + WP i l))
  have hrow' : ∀ i,
      D5.ModGammaSix
        ((formula21ThirdCoordinateBlock C ξ i (U i) *
            formula21ThirdCoordinateBlock C ξ i (WL i)) *
          (formula21ThirdCoordinateBlock C ξ i (WR i) *
            formula21ThirdCoordinateBlock C ξ i (WP i)))
        (formula21ThirdCoordinateBlock C ξ i fun l =>
          condition13ReplacementCoefficient C P i l) := by
    intro i
    refine (hrow i).trans ?_
    change ((formula21ThirdCoordinateBlock C ξ i fun l =>
      (U i l + WL i l) + (WR i l + WP i l) : G) :
        G ⧸ D5.gamma G 6) =
      ((formula21ThirdCoordinateBlock C ξ i fun l =>
        condition13ReplacementCoefficient C P i l : G) :
          G ⧸ D5.gamma G 6)
    congr 1
    unfold formula21ThirdCoordinateBlock
    congr 1
    funext l
    dsimp [U, WL, WR, WP, condition13ReplacementCoefficient]
    ring
  have hinner : D5.ModGammaSix
      (orderedProduct fun i =>
        ((formula21ThirdCoordinateBlock C ξ i (U i) *
            formula21ThirdCoordinateBlock C ξ i (WL i)) *
          (formula21ThirdCoordinateBlock C ξ i (WR i) *
            formula21ThirdCoordinateBlock C ξ i (WP i))))
      (formula27ReplacementGrouped C P ξ) := by
    unfold formula27ReplacementGrouped
    apply modEq_orderedProduct
    intro i
    exact hrow' i
  have houter := D5.orderedProduct_four_gammaThree
    (fun i => formula21ThirdCoordinateBlock C ξ i (U i))
    (fun i => formula21ThirdCoordinateBlock C ξ i (WL i))
    (fun i => formula21ThirdCoordinateBlock C ξ i (WR i))
    (fun i => formula21ThirdCoordinateBlock C ξ i (WP i))
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)
    (fun i => formula21ThirdCoordinateBlock_mem_gamma3 C ξ i _)
  exact hinner.symm.trans <| by
    simpa [formula28UCoordinateStream, formula28WLeftCoordinateStream,
      formula28WRightCoordinateStream, formula28WPrimeCoordinateStream,
      U, WL, WR, WP] using houter

/-- The first stream after its coordinates have been recollected by the
pair `(h,i)`. -/
def formula28UAlphaPairStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (· < i) fun h =>
    orderedProduct fun l =>
      D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
        ((P.u h i * orderRatio C.d h i) * C.alpha h i l)

/-- The same first stream, with each alpha-coordinate block replaced by its
source commutator from relation (3). -/
def formula28URawPairStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (· < i) fun h =>
    D5.paperComm
      (D5.paperComm ξ
        (D5.paperComm (C.x1 h ^ orderInt C.d h) (C.x1 i)))
      (C.x1 i) ^ (P.u h i * orderRatio C.d h i)

/-- Relation (3) expands the `u`-part of (27) into the corresponding
finite product of first-layer commutators.  This is the first of the four
summands in formula (28), before its final commutator rotations. -/
theorem formula28_u_coordinate_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula28UCoordinateStream C P ξ)
      (formula28URawPairStream C P ξ) := by
  let A : Fin C.s → Fin C.r → G := fun i l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hA : ∀ i l, A i l ∈ D5.gamma G 3 := by
    intro i l
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (show 3 ≤ 5 by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x3_mem_gamma3 l)) hxi
  have hcollect : ∀ i,
      D5.ModGammaSix
        (orderedProductWhere (· < i) fun h => orderedProduct fun l =>
          A i l ^ ((P.u h i * orderRatio C.d h i) * C.alpha h i l))
        (formula21ThirdCoordinateBlock C ξ i fun l =>
          ∑ h ∈ Finset.univ.filter (· < i),
            P.u h i * orderRatio C.d h i * C.alpha h i l) := by
    intro i
    simpa [A, formula21ThirdCoordinateBlock] using
      D5.orderedProductWhere_coordinateBlocks_gammaThree (· < i)
        (A i) (hA i)
        (fun h l => (P.u h i * orderRatio C.d h i) * C.alpha h i l)
  have hlocal : ∀ i,
      D5.ModGammaSix
        (orderedProductWhere (· < i) fun h =>
          D5.paperComm
            (D5.paperComm ξ
              (D5.paperComm (C.x1 h ^ orderInt C.d h) (C.x1 i)))
            (C.x1 i) ^ (P.u h i * orderRatio C.d h i))
        (orderedProductWhere (· < i) fun h => orderedProduct fun l =>
          A i l ^ ((P.u h i * orderRatio C.d h i) * C.alpha h i l)) := by
    intro i
    apply modEq_orderedProductWhere
    intro h hhi
    simpa [A] using alpha_coordinate_expansion_zpow C ξ i h i hhi
      (P.u h i * orderRatio C.d h i)
  unfold formula28UCoordinateStream formula28URawPairStream
  have houter : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (· < i) fun h =>
        D5.paperComm
          (D5.paperComm ξ
            (D5.paperComm (C.x1 h ^ orderInt C.d h) (C.x1 i)))
          (C.x1 i) ^ (P.u h i * orderRatio C.d h i))
      (orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
        ∑ h ∈ Finset.univ.filter (· < i),
          P.u h i * orderRatio C.d h i * C.alpha h i l) := by
    apply modEq_orderedProduct
    intro i
    exact (hlocal i).trans (hcollect i)
  exact houter.symm

/-- The alpha-coordinate form of the second stream in (28). -/
def formula28WLeftAlphaTripleStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (· ≤ i) fun g =>
    orderedProductWhere (i ≤ ·) fun h => orderedProduct fun l =>
      D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i) ^
        (P.w g i h * C.alpha g h l)

/-- The second stream after relation (3); its only possible diagonal index
is represented by `1`, because the diagonal alpha-coordinate is zero. -/
def formula28WLeftRawTripleStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (· ≤ i) fun g =>
    orderedProductWhere (i ≤ ·) fun h =>
      if _ : g < h then
        D5.paperComm
          (D5.paperComm ξ
            (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
          (C.x1 i) ^ P.w g i h
      else 1

private theorem alphaCoordinateBlock_diag
    (C : Context G) (ξ : G) (i g : Fin C.s) :
    alphaCoordinateBlock C ξ i g g = 1 := by
  unfold alphaCoordinateBlock
  simp [orderedProduct, C.alpha_diag]

/-- Relation (3) expands the `w(g,i,h)` stream.  The proof retains all
three finite index loops and discharges the diagonal solely from
`alpha(i,i,l)=0`. -/
theorem formula28_wleft_coordinate_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula28WLeftCoordinateStream C P ξ)
      (formula28WLeftRawTripleStream C P ξ) := by
  let A : Fin C.s → Fin C.r → G := fun i l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hA : ∀ i l, A i l ∈ D5.gamma G 3 := by
    intro i l
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (show 3 ≤ 5 by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x3_mem_gamma3 l)) hxi
  have hcollectH : ∀ i g,
      D5.ModGammaSix
        (orderedProductWhere (i ≤ ·) fun h => orderedProduct fun l =>
          A i l ^ (P.w g i h * C.alpha g h l))
        (formula21ThirdCoordinateBlock C ξ i fun l =>
          ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l) := by
    intro i g
    simpa [A, formula21ThirdCoordinateBlock] using
      D5.orderedProductWhere_coordinateBlocks_gammaThree (i ≤ ·)
        (A i) (hA i) (fun h l => P.w g i h * C.alpha g h l)
  have hcollectG : ∀ i,
      D5.ModGammaSix
        (orderedProductWhere (· ≤ i) fun g => orderedProductWhere (i ≤ ·)
          fun h => orderedProduct fun l => A i l ^ (P.w g i h * C.alpha g h l))
        (formula21ThirdCoordinateBlock C ξ i fun l =>
          ∑ g ∈ Finset.univ.filter (· ≤ i),
            ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l) := by
    intro i
    refine (modEq_orderedProductWhere (· ≤ i) fun g hg => hcollectH i g).trans ?_
    change D5.ModGammaSix
      (orderedProductWhere (· ≤ i) fun g => orderedProduct fun l =>
        A i l ^ ∑ h ∈ Finset.univ.filter (i ≤ ·),
          P.w g i h * C.alpha g h l)
      (orderedProduct fun l => A i l ^ ∑ g ∈ Finset.univ.filter (· ≤ i),
        ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l)
    exact
      D5.orderedProductWhere_coordinateBlocks_gammaThree (· ≤ i)
        (A i) (hA i) (fun g l =>
          ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l)
  have hlocal : ∀ i,
      D5.ModGammaSix
        (orderedProductWhere (· ≤ i) fun g => orderedProductWhere (i ≤ ·)
          fun h => if hgh : g < h then
            D5.paperComm
              (D5.paperComm ξ
                (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
              (C.x1 i) ^ P.w g i h
          else 1)
        (orderedProductWhere (· ≤ i) fun g => orderedProductWhere (i ≤ ·)
          fun h => orderedProduct fun l => A i l ^ (P.w g i h * C.alpha g h l)) := by
    intro i
    apply modEq_orderedProductWhere
    intro g hgi
    apply modEq_orderedProductWhere
    intro h hih
    by_cases hgh : g < h
    · simpa [A, hgh] using alpha_coordinate_expansion_zpow C ξ i g h hgh
        (P.w g i h)
    · have hge : h ≤ g := le_of_not_gt hgh
      have hgh' : g = h := le_antisymm (le_trans hgi hih) hge
      subst h
      simpa [A, orderedProduct, C.alpha_diag] using
        (D5.ModEq.refl (D5.gamma G 6) (1 : G))
  unfold formula28WLeftCoordinateStream formula28WLeftRawTripleStream
  have houter : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (· ≤ i) fun g =>
        orderedProductWhere (i ≤ ·) fun h => if hgh : g < h then
          D5.paperComm
            (D5.paperComm ξ
              (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
            (C.x1 i) ^ P.w g i h
        else 1)
      (orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
        ∑ g ∈ Finset.univ.filter (· ≤ i),
          ∑ h ∈ Finset.univ.filter (i ≤ ·), P.w g i h * C.alpha g h l) := by
    apply modEq_orderedProduct
    intro i
    exact (hlocal i).trans (hcollectG i)
  exact houter.symm

/-- The third stream of (28), indexed by `g ≤ h ≤ i`, after relation (3).
The value is `1` on its diagonal `g=h`. -/
def formula28WRightRawTripleStream
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) : G :=
  orderedProduct fun i => orderedProductWhere (· ≤ i) fun g =>
    orderedProductWhere (fun h => g ≤ h ∧ h ≤ i) fun h =>
      if _ : g < h then
        D5.paperComm
          (D5.paperComm ξ
            (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
          (C.x1 i) ^ P.w g h i
      else 1

theorem formula28_wright_coordinate_expansion
    (C : Context G) (P : Parameters C.s C.t) (ξ : G) :
    D5.ModGammaSix (formula28WRightCoordinateStream C P ξ)
      (formula28WRightRawTripleStream C P ξ) := by
  let A : Fin C.s → Fin C.r → G := fun i l =>
    D5.paperComm (D5.paperComm ξ (C.x3 l)) (C.x1 i)
  have hA : ∀ i l, A i l ∈ D5.gamma G 3 := by
    intro i l
    have hξ : ξ ∈ D5.gamma G 1 := by simp [D5.gamma]
    have hxi : C.x1 i ∈ D5.gamma G 1 := by simp [D5.gamma]
    exact D5.gamma_antitone G (show 3 ≤ 5 by norm_num) <|
      D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
        (D5.paperComm_mem_gamma_add (by norm_num) (by norm_num)
          hξ (C.x3_mem_gamma3 l)) hxi
  have hH : ∀ i g,
      D5.ModGammaSix
        (orderedProductWhere (fun h => g ≤ h ∧ h ≤ i) fun h =>
          orderedProduct fun l => A i l ^ (P.w g h i * C.alpha g h l))
        (formula21ThirdCoordinateBlock C ξ i fun l =>
          ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
            P.w g h i * C.alpha g h l) := by
    intro i g
    simpa [A, formula21ThirdCoordinateBlock] using
      D5.orderedProductWhere_coordinateBlocks_gammaThree
        (fun h => g ≤ h ∧ h ≤ i) (A i) (hA i)
        (fun h l => P.w g h i * C.alpha g h l)
  have hG : ∀ i,
      D5.ModGammaSix
        (orderedProductWhere (· ≤ i) fun g => orderedProductWhere
          (fun h => g ≤ h ∧ h ≤ i) fun h => orderedProduct fun l =>
            A i l ^ (P.w g h i * C.alpha g h l))
        (formula21ThirdCoordinateBlock C ξ i fun l =>
          ∑ g ∈ Finset.univ.filter (· ≤ i),
            ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
              P.w g h i * C.alpha g h l) := by
    intro i
    refine (modEq_orderedProductWhere (· ≤ i) fun g hg => hH i g).trans ?_
    change D5.ModGammaSix
      (orderedProductWhere (· ≤ i) fun g => orderedProduct fun l => A i l ^
        ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
          P.w g h i * C.alpha g h l)
      (orderedProduct fun l => A i l ^ ∑ g ∈ Finset.univ.filter (· ≤ i),
        ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
          P.w g h i * C.alpha g h l)
    exact D5.orderedProductWhere_coordinateBlocks_gammaThree (· ≤ i)
      (A i) (hA i) (fun g l =>
        ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
          P.w g h i * C.alpha g h l)
  have hlocal : ∀ i,
      D5.ModGammaSix
        (orderedProductWhere (· ≤ i) fun g => orderedProductWhere
          (fun h => g ≤ h ∧ h ≤ i) fun h => if hgh : g < h then
            D5.paperComm (D5.paperComm ξ
              (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
              (C.x1 i) ^ P.w g h i else 1)
        (orderedProductWhere (· ≤ i) fun g => orderedProductWhere
          (fun h => g ≤ h ∧ h ≤ i) fun h => orderedProduct fun l =>
            A i l ^ (P.w g h i * C.alpha g h l)) := by
    intro i
    apply modEq_orderedProductWhere
    intro g hgi
    apply modEq_orderedProductWhere
    intro h hh
    by_cases hgh : g < h
    · simpa [A, hgh] using alpha_coordinate_expansion_zpow C ξ i g h hgh
        (P.w g h i)
    · have hEq : g = h := le_antisymm hh.1 (le_of_not_gt hgh)
      subst h
      simpa [A, orderedProduct, C.alpha_diag] using
        (D5.ModEq.refl (D5.gamma G 6) (1 : G))
  unfold formula28WRightCoordinateStream formula28WRightRawTripleStream
  have H : D5.ModGammaSix
      (orderedProduct fun i => orderedProductWhere (· ≤ i) fun g =>
        orderedProductWhere (fun h => g ≤ h ∧ h ≤ i) fun h => if hgh : g < h then
          D5.paperComm (D5.paperComm ξ
            (D5.paperComm (C.x1 g ^ orderInt C.d g) (C.x1 h)))
            (C.x1 i) ^ P.w g h i else 1)
      (orderedProduct fun i => formula21ThirdCoordinateBlock C ξ i fun l =>
        ∑ g ∈ Finset.univ.filter (· ≤ i),
          ∑ h ∈ Finset.univ.filter (fun h => g ≤ h ∧ h ≤ i),
            P.w g h i * C.alpha g h l) := by
    apply modEq_orderedProduct
    intro i
    exact (hlocal i).trans (hG i)
  exact H.symm

end

end D5.Tahara
