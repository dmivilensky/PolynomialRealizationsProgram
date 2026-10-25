import polyak.Levels.Chart.DoubleRoot
import polyak.Levels.Chart.RealRoots
import polyak.Levels.Chart.Window
import polyak.Levels.Geometry.LevelZeroExclusive

/-! The converse double-root face theorem for the actual relative
boundary, and the strict nonperiodic part of that face in every window. -/
noncomputable section
namespace polyak.Levels.Chart
open General Set Filter
open scoped Topology

theorem double_root_of_weak_contact (q : Tuning)
    {r : ℝ} (hr : r∈Ioo (-1:ℝ) 1)
    (hweak : ∀c∈Icc (-1:ℝ) 1,q.Xi c≤1+c)
    (hcontact : q.Xi r=1+r) :
    coefficients q=gapPolynomial (-(coefficients q).c2) r r := by
  let C:=coefficients q
  let g : ℝ→ℝ:=fun c=>1+c-C.eval c
  have hz : g r=0:=by dsimp [g,C]; rw [eval_coefficients,hcontact]; ring
  have hmin : IsLocalMin g r := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with c hc
    rw [hz]
    exact sub_nonneg.mpr (by simpa only [C,eval_coefficients] using hweak c ⟨hc.1.le,hc.2.le⟩)
  have hd : HasDerivAt g (1-C.c1-2*C.c2*r) r := by
    have he:=((hasDerivAt_const r (1:ℝ)).add (hasDerivAt_id r)).sub
      (((hasDerivAt_const r C.c0).add ((hasDerivAt_id r).const_mul C.c1)).add
        (((hasDerivAt_id r).pow 2).const_mul C.c2))
    convert he using 1
    · rfl
    · simp only [id_eq]
      ring
  have hder:=hmin.hasDerivAt_eq_zero hd
  have hzero : 1+r-(C.c0+C.c1*r+C.c2*r^2)=0:=hz
  apply Coefficients.ext
  · change C.c0=1-(-C.c2)*r*r
    linear_combination -hzero+r*hder
  · change C.c1=1+(-C.c2)*(r+r)
    linarith
  · change C.c2= -(-C.c2)
    ring

/-- Every actual relative boundary point, including a putative beta-zero
point, has positive momentum and a genuine interior double-root chart. -/
theorem frontier_double_root (q : Tuning)
    (hq : q∈frontier {p:Tuning | Regions.OmegaOne p}) :
    0<q.beta ∧ ∃a r : ℝ,0<a ∧ r∈Ioo (-1:ℝ) 1 ∧
      amplitudeFloor r r<a ∧ coefficients q=gapPolynomial a r r := by
  obtain ⟨hb,hr,hzero,_⟩:=Regions.frontier_omegaOne_tangent hq
  let r:=Regions.vertex q
  have hweakL:=Regions.closure_omegaOne_subset_weak (frontier_subset_closure hq)
  have hp : 0<(q.y-q.x)*(1-q.beta):=mul_pos (sub_pos.mpr q.x_lt_y) (sub_pos.mpr q.beta_lt_one)
  have hw : ∀c∈Icc (-1:ℝ) 1,q.Xi c≤1+c := by
    intro c hc
    have hh:=hweakL c hc
    rw [q.L_eq_Xi] at hh
    have hn:=nonneg_of_mul_nonneg_right hh hp
    linarith
  have hcontact : q.Xi r=1+r := by
    rw [q.L_eq_Xi] at hzero
    have hn:=(mul_eq_zero.mp hzero).resolve_left hp.ne'
    dsimp only [r]
    linarith
  have he:=double_root_of_weak_contact q hr hw hcontact
  have hc : (coefficients q).c2<0:=(coefficient_quadratic_neg_iff q).mpr hb
  have hfloor : amplitudeFloor r r< -(coefficients q).c2 := by
    have hh:=q.Xi_one_neg
    rw [←eval_coefficients,he,gapPolynomial_one] at hh
    unfold amplitudeFloor
    exact (div_lt_iff₀ (mul_pos (sub_pos.mpr hr.2) (sub_pos.mpr hr.2))).mpr (by nlinarith)
  exact ⟨hb,-(coefficients q).c2,r,neg_pos.mpr hc,hr,hfloor,he⟩

 theorem frontier_iff_double_root (q : Tuning) :
    q∈frontier {p:Tuning | Regions.OmegaOne p} ↔
      ∃a r : ℝ,0<a ∧ r∈Ioo (-1:ℝ) 1 ∧ coefficients q=gapPolynomial a r r := by
  constructor
  · intro hq
    obtain ⟨_,a,r,ha,hr,_,he⟩:=frontier_double_root q hq
    exact ⟨a,r,ha,hr,he⟩
  · rintro ⟨a,r,ha,hr,he⟩
    exact (double_root_boundary q ha hr he).2.2

/-- A double root whose frequency is strictly inside a gap window is a
non-phase-locked boundary point with the actual two-lag strict symbol. -/
theorem double_root_window_strict (q : Tuning) {a r : ℝ} (ha : 0<a)
    (hr : r∈Ioo (-1:ℝ) 1) (he : coefficients q=gapPolynomial a r r)
    {K : ℕ} (hK : 2≤K)
    (hwin : Geometry.InWindow K
      ⟨Real.arccos r,⟨(Real.arccos_pos.mpr hr.2).le,(Real.arccos_lt_pi.mpr hr.1).le⟩⟩) :
    q∈frontier {p:Tuning | Regions.OmegaOne p} ∧
      ¬Geometry.PhaseLockedContact q ∧ q.rate<1 ∧
      ∃S : StrictSymbol (tuningCurve q) nonzeroLags,S.symbol.lags={1,-(K:ℤ)} := by
  obtain ⟨hweak,hcontact,hfront⟩:=double_root_boundary q ha hr he
  let ω : Frequency:=⟨Real.arccos r,⟨(Real.arccos_pos.mpr hr.2).le,(Real.arccos_lt_pi.mpr hr.1).le⟩⟩
  have hw : ∀η : Frequency,(η:ℝ)/2≤q.angle η := by
    intro η
    by_cases hz : (η:ℝ)=0
    · rw [hz,q.angle_zero]
      linarith [Real.pi_pos]
    · exact hweak η ⟨lt_of_le_of_ne η.property.1 (Ne.symm hz),η.property.2⟩
  have hgrid : ∀L : ℕ,∀hL : 3≤L,ω≠Geometry.firstFrequency L (by omega) := by
    intro L hL heq
    apply Geometry.firstFrequency_not_in_window hK hL
    rw [←heq]
    exact hwin
  obtain ⟨J,hJ,hJwin,S,hS,hrate⟩:=Geometry.nonperiodic_tangency_certificate q (ω:=ω) hw hcontact hgrid
  have hJK : J=K:=Geometry.window_disjoint hJ hK hJwin hwin
  subst J
  exact ⟨hfront,Geometry.singleton_window_not_phase_locked q hfront hrate,hrate,S,hS⟩

theorem double_root_between_boundaries_strict (q : Tuning) {a r : ℝ} (ha : 0<a)
    {K : ℕ} (hK : 2≤K) (hl : boundaryCosine K<r) (hu : r<boundaryCosine (K+1))
    (he : coefficients q=gapPolynomial a r r) :
    q∈frontier {p:Tuning | Regions.OmegaOne p} ∧
      ¬Geometry.PhaseLockedContact q ∧ q.rate<1 ∧
      ∃S : StrictSymbol (tuningCurve q) nonzeroLags,S.symbol.lags={1,-(K:ℤ)} := by
  have hr : r∈Ioo (-1:ℝ) 1:=
    ⟨(boundaryCosine_ge_neg_one K).trans_lt hl,hu.trans (boundaryCosine_succ_lt_one hK)⟩
  have hω : Real.arccos r∈Icc (0:ℝ) Real.pi:=
    ⟨(Real.arccos_pos.mpr hr.2).le,(Real.arccos_lt_pi.mpr hr.1).le⟩
  have hc : boundaryCosine K<Real.cos (Real.arccos r) ∧
      Real.cos (Real.arccos r)<boundaryCosine (K+1) := by
    simpa only [Real.cos_arccos hr.1.le hr.2.le] using And.intro hl hu
  have hw:=(cos_window_iff hK hω).mp hc
  apply double_root_window_strict q ha hr he hK
  simpa only [Geometry.InWindow,boundaryAngle,Nat.cast_add,Nat.cast_one] using hw

end polyak.Levels.Chart
