import polyak.Global.Sampling.Phase
import polyak.Global.Sampling.AliasingPhase
import Mathlib.Topology.Order.ExtrClosure

/-! The literal source supremum constants, not larger substituted bounds.
The compact branch extrema equal the open-branch suprema. -/
noncomputable section
namespace polyak.Global.Sampling
open polyak.General polyak.Levels Set

theorem phase_derivative_bounds_of_branch_bounds (q:Tuning) (s:ℝ) {M1 M2:ℝ}
    (hb1:∀x∈Icc 0 Real.pi,|deriv (phaseBranch q s) x|≤M1)
    (hb2:∀x∈Icc 0 Real.pi,|deriv (deriv (phaseBranch q s)) x|≤M2) :
    (∀x,|phaseDerivative q s x|≤M1) ∧
      ∀x y,|phaseDerivative q s x-phaseDerivative q s y|≤M2*|x-y| := by
  have hmem (x:ℝ) : toIcoMod Real.two_pi_pos 0 x∈Ico 0 (2*Real.pi) := by
    simpa only [zero_add] using toIcoMod_mem_Ico Real.two_pi_pos 0 x
  have hdf : ∀x∈Icc 0 Real.pi,HasDerivAt (deriv (phaseBranch q s))
      (deriv (deriv (phaseBranch q s)) x) x := by
    intro x hx
    exact (analyticAt_phaseBranch q s hx).deriv.differentiableAt.hasDerivAt
  constructor
  · intro x
    dsimp [phaseDerivative,periodicExtension,mirrorDerivative]
    split_ifs with hx
    · exact hb1 _ ⟨(hmem x).1,hx⟩
    · apply hb1
      constructor <;> linarith [(hmem x).2,le_of_not_ge hx]
  · intro x y
    apply periodicExtension_lipschitz Real.two_pi_pos (mirrorDerivative_ends q s)
      (continuousOn_mirrorDerivative (fun z hz=>(hdf z hz).continuousAt))
      (fun z hz=>hasDerivWithinAt_mirrorDerivative_right hdf hz)
    intro z hz
    split_ifs with hza
    · exact hb2 z ⟨hz.1,hza.le⟩
    · rw [abs_neg]
      apply hb2
      constructor <;> linarith [hz.2,le_of_not_gt hza]

theorem phase_uniform_taylor_of_branch_bounds (q:Tuning) (s:ℝ) {M1 M2:ℝ}
    (hb1:∀x∈Icc 0 Real.pi,|deriv (phaseBranch q s) x|≤M1)
    (hb2:∀x∈Icc 0 Real.pi,|deriv (deriv (phaseBranch q s)) x|≤M2) :
    (∀x,|phaseDerivative q s x|≤M1) ∧
      ∀v t,|phase q s (v+t)-phase q s v-phaseDerivative q s v*t|≤M2*t^2/2 := by
  obtain ⟨h1,h2⟩:=phase_derivative_bounds_of_branch_bounds q s hb1 hb2
  exact ⟨h1,phase_taylor_bound (hasDerivAt_phase q s) h2⟩

def canonicalM1 (q:Tuning) (s:ℝ) : ℝ :=
  sSup ((fun x=>|deriv (phaseBranch q s) x|) '' Icc 0 Real.pi)

def canonicalM2 (q:Tuning) (s:ℝ) : ℝ :=
  sSup ((fun x=>|deriv (deriv (phaseBranch q s)) x|) '' Icc 0 Real.pi)

theorem continuousOn_abs_phaseBranch_first (q:Tuning) (s:ℝ) :
    ContinuousOn (fun x=>|deriv (phaseBranch q s) x|) (Icc 0 Real.pi) :=
  fun _x hx=>(analyticAt_phaseBranch q s hx).deriv.continuousAt.abs.continuousWithinAt

theorem continuousOn_abs_phaseBranch_second (q:Tuning) (s:ℝ) :
    ContinuousOn (fun x=>|deriv (deriv (phaseBranch q s)) x|) (Icc 0 Real.pi) :=
  fun _x hx=>(analyticAt_phaseBranch q s hx).deriv.deriv.continuousAt.abs.continuousWithinAt

theorem compact_branch_sup_attained {f:ℝ→ℝ} (hf:ContinuousOn f (Icc 0 Real.pi)) :
    ∃x∈Icc 0 Real.pi,f x=sSup (f '' Icc 0 Real.pi) ∧
      ∀y∈Icc 0 Real.pi,f y≤sSup (f '' Icc 0 Real.pi) := by
  obtain ⟨x,hx,hmax⟩:=isCompact_Icc.exists_isMaxOn
    (show (Icc (0:ℝ) Real.pi).Nonempty from ⟨0,le_rfl,Real.pi_pos.le⟩) hf
  have hG : IsGreatest (f '' Icc 0 Real.pi) (f x) :=
    ⟨⟨x,hx,rfl⟩,fun z hz=>by obtain ⟨y,hy,rfl⟩:=hz;exact hmax hy⟩
  refine ⟨x,hx,hG.csSup_eq.symm,?_⟩
  intro y hy
  rw [hG.csSup_eq]
  exact hmax hy

theorem canonicalM1_attained (q:Tuning) (s:ℝ) :
    ∃x∈Icc 0 Real.pi,|deriv (phaseBranch q s) x|=canonicalM1 q s := by
  obtain ⟨x,hx,he,_⟩:=compact_branch_sup_attained (continuousOn_abs_phaseBranch_first q s)
  exact ⟨x,hx,he⟩

theorem canonicalM2_attained (q:Tuning) (s:ℝ) :
    ∃x∈Icc 0 Real.pi,|deriv (deriv (phaseBranch q s)) x|=canonicalM2 q s := by
  obtain ⟨x,hx,he,_⟩:=compact_branch_sup_attained (continuousOn_abs_phaseBranch_second q s)
  exact ⟨x,hx,he⟩

theorem canonicalM1_bound (q:Tuning) (s:ℝ) :
    ∀x∈Icc 0 Real.pi,|deriv (phaseBranch q s) x|≤canonicalM1 q s := by
  obtain ⟨_,_,_,hb⟩:=compact_branch_sup_attained (continuousOn_abs_phaseBranch_first q s)
  exact hb

theorem canonicalM2_bound (q:Tuning) (s:ℝ) :
    ∀x∈Icc 0 Real.pi,|deriv (deriv (phaseBranch q s)) x|≤canonicalM2 q s := by
  obtain ⟨_,_,_,hb⟩:=compact_branch_sup_attained (continuousOn_abs_phaseBranch_second q s)
  exact hb

theorem canonicalM1_nonneg (q:Tuning) (s:ℝ) : 0≤canonicalM1 q s :=
  (abs_nonneg _).trans (canonicalM1_bound q s 0 ⟨le_rfl,Real.pi_pos.le⟩)

theorem canonicalM2_nonneg (q:Tuning) (s:ℝ) : 0≤canonicalM2 q s :=
  (abs_nonneg _).trans (canonicalM2_bound q s 0 ⟨le_rfl,Real.pi_pos.le⟩)

theorem canonical_phase_uniform_taylor (q:Tuning) (s:ℝ) :
    (∀x,|phaseDerivative q s x|≤canonicalM1 q s) ∧
      ∀v t,|phase q s (v+t)-phase q s v-phaseDerivative q s v*t|≤canonicalM2 q s*t^2/2 :=
  phase_uniform_taylor_of_branch_bounds q s (canonicalM1_bound q s) (canonicalM2_bound q s)

/-- Endpoint extrema do not enlarge the source supremum on the open analytic branch. -/
theorem compact_branch_sup_eq_open {f:ℝ→ℝ} (hf:ContinuousOn f (Icc 0 Real.pi)) :
    sSup (f '' Icc 0 Real.pi)=sSup (f '' Ioo 0 Real.pi) := by
  have hne : (f '' Ioo 0 Real.pi).Nonempty := by
    refine ⟨f (Real.pi/2),Real.pi/2,?_,rfl⟩
    constructor <;> linarith [Real.pi_pos]
  have hbd : BddAbove (f '' Ioo 0 Real.pi) :=
    (isCompact_Icc.bddAbove_image hf).mono (image_mono Ioo_subset_Icc_self)
  have hb : ∀x∈Ioo 0 Real.pi,f x≤sSup (f '' Ioo 0 Real.pi) :=
    fun x hx=>le_csSup hbd ⟨x,hx,rfl⟩
  have hclose : closure (Ioo (0:ℝ) Real.pi)=Icc 0 Real.pi := closure_Ioo Real.pi_pos.ne
  have hbclosed : ∀x∈Icc 0 Real.pi,f x≤sSup (f '' Ioo 0 Real.pi) := by
    intro x hx
    apply le_on_closure hb
    · rwa [hclose]
    · exact continuousOn_const
    · rwa [hclose]
  apply le_antisymm
  · apply csSup_le
    · exact ⟨f 0,0,⟨le_rfl,Real.pi_pos.le⟩,rfl⟩
    · rintro _ ⟨x,hx,rfl⟩
      exact hbclosed x hx
  · apply csSup_le hne
    rintro _ ⟨x,hx,rfl⟩
    exact le_csSup (isCompact_Icc.bddAbove_image hf) ⟨x,Ioo_subset_Icc_self hx,rfl⟩

theorem canonicalM1_open_sup (q:Tuning) (s:ℝ) :
    canonicalM1 q s=sSup ((fun x=>|deriv (phaseBranch q s) x|) '' Ioo 0 Real.pi) :=
  compact_branch_sup_eq_open (continuousOn_abs_phaseBranch_first q s)

theorem canonicalM2_open_sup (q:Tuning) (s:ℝ) :
    canonicalM2 q s=sSup ((fun x=>|deriv (deriv (phaseBranch q s)) x|) '' Ioo 0 Real.pi) :=
  compact_branch_sup_eq_open (continuousOn_abs_phaseBranch_second q s)

theorem phaseDerivative_on_branch (q:Tuning) (s:ℝ) {x:ℝ} (hx:x∈Icc 0 Real.pi) :
    phaseDerivative q s x=deriv (phaseBranch q s) x := by
  have hm:x∈Ico 0 (0+2*Real.pi) := ⟨hx.1,by linarith [hx.2,Real.pi_pos]⟩
  simp only [phaseDerivative,periodicExtension,(toIcoMod_eq_self Real.two_pi_pos).mpr hm,
    mirrorDerivative,ite_eq_left hx.2]

/-- The canonical first constant is exactly the global source derivative supremum. -/
theorem canonicalM1_global_sup (q:Tuning) (s:ℝ) :
    sSup (range (fun x=>|phaseDerivative q s x|))=canonicalM1 q s := by
  apply IsGreatest.csSup_eq
  obtain ⟨x,hx,he⟩:=canonicalM1_attained q s
  refine ⟨⟨x,?_⟩,?_⟩
  · change |phaseDerivative q s x|=canonicalM1 q s
    rw [phaseDerivative_on_branch q s hx,he]
  · rintro _ ⟨y,rfl⟩
    exact (canonical_phase_uniform_taylor q s).1 y

def regularPhaseInterval : Set ℝ := Ioo 0 (2*Real.pi) \ {Real.pi}

theorem phaseSecond_canonical_bound (q:Tuning) (s:ℝ) {x:ℝ} (hx:x∈Icc 0 (2*Real.pi)) :
    |phaseSecond q s x|≤canonicalM2 q s := by
  unfold phaseSecond
  split_ifs with hp
  · exact canonicalM2_bound q s x ⟨hx.1,hp.le⟩
  · rw [abs_neg]
    exact canonicalM2_bound q s _ ⟨by linarith [hx.2],by linarith [le_of_not_gt hp]⟩

/-- The compact branch second derivative supremum is exactly the source
supremum off both periodic analytic junctions. -/
theorem canonicalM2_fundamental_sup (q:Tuning) (s:ℝ) :
    sSup ((fun x=>|phaseSecond q s x|) '' regularPhaseInterval)=canonicalM2 q s := by
  have hne : ((fun x=>|phaseSecond q s x|) '' regularPhaseInterval).Nonempty := by
    refine ⟨_,Real.pi/2,?_,rfl⟩
    change (0<Real.pi/2 ∧ Real.pi/2<2*Real.pi) ∧ Real.pi/2∉({Real.pi}:Set ℝ)
    constructor
    · constructor <;> linarith [Real.pi_pos]
    · simp only [mem_singleton_iff]
      linarith [Real.pi_pos]
  have hbd : BddAbove ((fun x=>|phaseSecond q s x|) '' regularPhaseInterval) := by
    refine ⟨canonicalM2 q s,?_⟩
    rintro _ ⟨x,hx,rfl⟩
    exact phaseSecond_canonical_bound q s ⟨hx.1.1.le,hx.1.2.le⟩
  apply le_antisymm
  · apply csSup_le hne
    rintro _ ⟨x,hx,rfl⟩
    exact phaseSecond_canonical_bound q s ⟨hx.1.1.le,hx.1.2.le⟩
  · rw [canonicalM2_open_sup]
    apply csSup_le
    · refine ⟨_,Real.pi/2,?_,rfl⟩
      constructor <;> linarith [Real.pi_pos]
    · rintro _ ⟨x,hx,rfl⟩
      apply le_csSup hbd
      refine ⟨x,?_,?_⟩
      · exact ⟨⟨hx.1,by linarith [hx.2,Real.pi_pos]⟩,by simpa only [mem_singleton_iff] using hx.2.ne⟩
      · simp only [phaseSecond,ite_eq_left hx.2]

theorem hasDerivAt_phaseDerivative_off_junction (q:Tuning) (s:ℝ) {x:ℝ}
    (hx:x∈regularPhaseInterval) :
    HasDerivAt (phaseDerivative q s) (phaseSecond q s x) x := by
  have hx0:=hx.1.1
  have hx2:=hx.1.2
  have hxp:x≠Real.pi:=by simpa only [mem_singleton_iff] using hx.2
  by_cases hleft:x<Real.pi
  · have hh := (analyticAt_phaseBranch q s ⟨hx0.le,hleft.le⟩).deriv.differentiableAt.hasDerivAt
    rw [show phaseSecond q s x=deriv (deriv (phaseBranch q s)) x by simp only [phaseSecond,ite_eq_left hleft]]
    apply hh.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hx0,eventually_lt_nhds hleft] with y hy0 hyp
    have hym:y∈Ico 0 (0+2*Real.pi):=⟨hy0.le,by linarith [hyp,Real.pi_pos]⟩
    simp only [phaseDerivative,periodicExtension,(toIcoMod_eq_self Real.two_pi_pos).mpr hym,
      mirrorDerivative,ite_eq_left hyp.le]
  · have hright:Real.pi<x:=lt_of_le_of_ne (le_of_not_gt hleft) hxp.symm
    have hmem:2*Real.pi-x∈Icc 0 Real.pi:=⟨by linarith,by linarith⟩
    have hh := (analyticAt_phaseBranch q s hmem).deriv.differentiableAt.hasDerivAt
    have hc := hh.comp x ((hasDerivAt_id x).const_sub (2*Real.pi))
    have hd:HasDerivAt (fun y=>deriv (phaseBranch q s) (2*Real.pi-y))
        (-deriv (deriv (phaseBranch q s)) (2*Real.pi-x)) x := by
      simpa only [Function.comp_def,mul_neg_one] using hc
    rw [show phaseSecond q s x= -deriv (deriv (phaseBranch q s)) (2*Real.pi-x) by simp only [phaseSecond,ite_eq_right hleft]]
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hright,eventually_lt_nhds hx2] with y hyp hy2
    have hym:y∈Ico 0 (0+2*Real.pi):=⟨by linarith [Real.pi_pos],by linarith⟩
    simp only [phaseDerivative,periodicExtension,(toIcoMod_eq_self Real.two_pi_pos).mpr hym,
      mirrorDerivative,ite_eq_right (not_le.mpr hyp)]

/-- Literal M₂=sup |Φ''| on the smooth part of one entire circle. -/
theorem canonicalM2_source_sup (q:Tuning) (s:ℝ) :
    sSup ((fun x=>|deriv (deriv (phase q s)) x|) '' regularPhaseInterval)=canonicalM2 q s := by
  have hfirst:deriv (phase q s)=phaseDerivative q s :=
    funext (fun x=>(hasDerivAt_phase q s x).deriv)
  rw [hfirst]
  have he : (fun x=>|deriv (phaseDerivative q s) x|) '' regularPhaseInterval=
      (fun x=>|phaseSecond q s x|) '' regularPhaseInterval := by
    apply image_congr
    intro x hx
    rw [(hasDerivAt_phaseDerivative_off_junction q s hx).deriv]
  rw [he,canonicalM2_fundamental_sup]

/-- Literal M₁=sup |Φ'| on the entire periodic real lift. -/
theorem canonicalM1_source_sup (q:Tuning) (s:ℝ) :
    sSup (range (fun x=>|deriv (phase q s) x|))=canonicalM1 q s := by
  have hfirst:deriv (phase q s)=phaseDerivative q s :=
    funext (fun x=>(hasDerivAt_phase q s x).deriv)
  rw [hfirst,canonicalM1_global_sup]

end polyak.Global.Sampling
