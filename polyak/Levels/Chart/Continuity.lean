import polyak.Levels.Chart.Inverse

/-! Continuity of the stable branch follows from strict scalar separation
on both sides of its root. No ordering of colliding complex roots is used. -/
noncomputable section
namespace polyak.Levels.Chart
open Set Filter
open scoped Topology

theorem secular_neg_iff (C : CoefficientPoint) {d : ℝ}
    (hda : -2*C.val.c2<d) (hdv : |C.val.c1|≤d) :
    secular (-C.val.c2) C.val.c1 (-C.val.c2-C.val.c0) d<0 ↔ d<stableRoot C := by
  constructor
  · intro hn
    by_contra hh
    have he : stableRoot C≤d := le_of_not_gt hh
    rcases he.eq_or_lt with he|he
    · rw [← he,(stableRoot_spec C).2.2] at hn
      exact lt_irrefl _ hn
    · have hm := secular_strictMono (t:= -C.val.c2-C.val.c0)
        (neg_pos.mpr C.property.1) (by linarith [(stableRoot_spec C).1])
        (stableRoot_spec C).2.1.le he
      rw [(stableRoot_spec C).2.2] at hm
      linarith
  · intro hd
    have hm := secular_strictMono (t:= -C.val.c2-C.val.c0)
      (neg_pos.mpr C.property.1) (by linarith) hdv hd
    rwa [(stableRoot_spec C).2.2] at hm

theorem secular_pos_iff (C : CoefficientPoint) {d : ℝ}
    (hda : -2*C.val.c2<d) (hdv : |C.val.c1|≤d) :
    0<secular (-C.val.c2) C.val.c1 (-C.val.c2-C.val.c0) d ↔ stableRoot C<d := by
  constructor
  · intro hp
    by_contra hh
    have he : d≤stableRoot C := le_of_not_gt hh
    rcases he.eq_or_lt with he|he
    · rw [he,(stableRoot_spec C).2.2] at hp
      exact lt_irrefl _ hp
    · have hm := (secular_neg_iff C hda hdv).mpr he
      linarith
  · intro hd
    have hm := secular_strictMono (t:= -C.val.c2-C.val.c0)
      (neg_pos.mpr C.property.1) (by linarith [(stableRoot_spec C).1])
      (stableRoot_spec C).2.1.le hd
    rwa [(stableRoot_spec C).2.2] at hm

@[fun_prop] theorem continuous_c0_point : Continuous (fun C : CoefficientPoint=>C.val.c0) :=
  Coefficients.continuous_c0.comp continuous_subtype_val
@[fun_prop] theorem continuous_c1_point : Continuous (fun C : CoefficientPoint=>C.val.c1) :=
  Coefficients.continuous_c1.comp continuous_subtype_val
@[fun_prop] theorem continuous_c2_point : Continuous (fun C : CoefficientPoint=>C.val.c2) :=
  Coefficients.continuous_c2.comp continuous_subtype_val

theorem secular_continuousAt (C : CoefficientPoint) {d : ℝ} (hda : -2*C.val.c2<d) :
    ContinuousAt (fun D : CoefficientPoint=>secular (-D.val.c2) D.val.c1
      (-D.val.c2-D.val.c0) d) C := by
  have hd0 : 0<d := by linarith [C.property.1]
  unfold secular
  fun_prop (disch := first | exact ne_of_gt hd0 | apply ne_of_gt; linarith)

@[fun_prop] theorem continuous_stableRoot : Continuous stableRoot := by
  apply continuous_iff_continuousAt.mpr
  intro C
  apply tendsto_order.2
  constructor
  · intro b hb
    let l := max b ((max (-2*C.val.c2) |C.val.c1|+stableRoot C)/2)
    have hmax : max (-2*C.val.c2) |C.val.c1|<stableRoot C :=
      max_lt (stableRoot_spec C).1 (stableRoot_spec C).2.1
    have hl : l<stableRoot C := by dsimp [l]; apply max_lt hb; linarith
    have hla : -2*C.val.c2<l := by
      have h1 := le_max_left (-2*C.val.c2) |C.val.c1|
      have h2 := le_max_right b ((max (-2*C.val.c2) |C.val.c1|+stableRoot C)/2)
      change _≤l at h2
      linarith
    have hlv : |C.val.c1|<l := by
      have h1 := le_max_right (-2*C.val.c2) |C.val.c1|
      have h2 := le_max_right b ((max (-2*C.val.c2) |C.val.c1|+stableRoot C)/2)
      change _≤l at h2
      linarith
    have hn := (secular_neg_iff C hla hlv.le).mpr hl
    have he : ∀ᶠ D : CoefficientPoint in 𝓝 C,
        -2*D.val.c2<l ∧ |D.val.c1|<l ∧
        secular (-D.val.c2) D.val.c1 (-D.val.c2-D.val.c0) l<0 := by
      have h1 : Continuous (fun D : CoefficientPoint=> -2*D.val.c2) := by fun_prop
      have h2 : Continuous (fun D : CoefficientPoint=>|D.val.c1|) := by fun_prop
      exact (h1.continuousAt.eventually (eventually_lt_nhds hla)).and
        ((h2.continuousAt.eventually (eventually_lt_nhds hlv)).and
          ((secular_continuousAt C hla).eventually (eventually_lt_nhds hn)))
    filter_upwards [he] with D hD
    exact (le_max_left _ _).trans_lt ((secular_neg_iff D hD.1 hD.2.1.le).mp hD.2.2)
  · intro b hb
    have hba : -2*C.val.c2<b := (stableRoot_spec C).1.trans hb
    have hbv : |C.val.c1|<b := (stableRoot_spec C).2.1.trans hb
    have hp := (secular_pos_iff C hba hbv.le).mpr hb
    have he : ∀ᶠ D : CoefficientPoint in 𝓝 C,
        -2*D.val.c2<b ∧ |D.val.c1|<b ∧
        0<secular (-D.val.c2) D.val.c1 (-D.val.c2-D.val.c0) b := by
      have h1 : Continuous (fun D : CoefficientPoint=> -2*D.val.c2) := by fun_prop
      have h2 : Continuous (fun D : CoefficientPoint=>|D.val.c1|) := by fun_prop
      exact (h1.continuousAt.eventually (eventually_lt_nhds hba)).and
        ((h2.continuousAt.eventually (eventually_lt_nhds hbv)).and
          ((secular_continuousAt C hba).eventually (eventually_gt_nhds hp)))
    filter_upwards [he] with D hD
    exact (secular_pos_iff D hD.1 hD.2.1.le).mp hD.2.2

@[fun_prop] theorem continuous_normalizedB : Continuous normalizedB := by
  unfold normalizedB
  fun_prop (disch := intro C; linarith [(stableRoot_spec C).1])
@[fun_prop] theorem continuous_normalizedU : Continuous normalizedU := by
  unfold normalizedU
  fun_prop
@[fun_prop] theorem continuous_normalizedA : Continuous normalizedA := by
  unfold normalizedA
  fun_prop (disch := intro C; exact ne_of_gt (zero_lt_one.trans (one_lt_normalizedU C)))

@[fun_prop] theorem continuous_inverseBeta : Continuous inverseBeta := by
  unfold inverseBeta
  fun_prop (disch := intro C; linarith [one_lt_normalizedU C])
@[fun_prop] theorem continuous_inverseA : Continuous inverseA := by unfold inverseA; fun_prop
@[fun_prop] theorem continuous_inverseB : Continuous inverseB := by unfold inverseB; fun_prop
@[fun_prop] theorem continuous_inverseX : Continuous inverseX := by unfold inverseX; fun_prop
@[fun_prop] theorem continuous_inverseY : Continuous inverseY := by unfold inverseY; fun_prop

theorem continuous_inverseTuning : Continuous inverseTuning := by
  apply continuous_induced_rng.mpr
  change Continuous (fun C : CoefficientPoint=>(inverseY C/inverseX C,1*inverseY C,inverseBeta C))
  fun_prop (disch := intro C; exact ne_of_gt (inverseX_pos C))

end polyak.Levels.Chart
