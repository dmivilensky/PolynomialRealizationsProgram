import polyak.General.Regions.Topology
import polyak.General.Angle

/-! The source condition-number comparison, with a uniform positive
cotangent gap on the complete open frequency interval. -/
noncomputable section
namespace polyak.Levels
open General Set

def kappaNumerator (y β c : ℝ) : ℝ :=
  (y-(1+β)*(1-c))^2+(1-β)^2*(1-c^2)

theorem kappaNumerator_pos (q : Tuning) {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) :
    0<kappaNumerator q.y q.beta c := by
  by_cases hp : c=1
  · subst c
    simpa only [kappaNumerator,sub_self,mul_zero,sub_zero,one_pow,zero_mul,add_zero] using
      sq_pos_of_pos q.y_pos
  by_cases hm : c= -1
  · subst c
    have hn : q.y-2*(1+q.beta)<0 := by linarith [q.y_lt]
    simpa only [kappaNumerator,neg_one_sq,sub_self,mul_zero,add_zero] using
      (show 0<(q.y-(1+q.beta)*(1- -1))^2 by apply sq_pos_of_ne_zero; nlinarith)
  have hi : 0<1-c^2 := by
    have h1 : c<1 := lt_of_le_of_ne hc.2 hp
    have h2 : -1<c := lt_of_le_of_ne hc.1 (Ne.symm hm)
    nlinarith [mul_pos (by linarith : 0<1-c) (by linarith : 0<1+c)]
  exact add_pos_of_nonneg_of_pos (sq_nonneg _)
    (mul_pos (sq_pos_of_pos (by linarith [q.beta_lt_one])) hi)

/-- The finite-difference version of the source derivative identity. -/
theorem Xi_kappa_difference (q p : Tuning) (hy : p.y=q.y) (hb : p.beta=q.beta)
    (c : ℝ) :
    p.Xi c-q.Xi c=kappaNumerator q.y q.beta c*(p.kappa-q.kappa)/
      (q.y*(1-q.beta)*(p.kappa-1)*(q.kappa-1)) := by
  have hκq : q.kappa≠0 := ne_of_gt q.kappa_pos
  have hκp : p.kappa≠0 := ne_of_gt p.kappa_pos
  have hq : q.kappa-1≠0 := ne_of_gt (sub_pos.mpr q.kappa_gt_one)
  have hp : p.kappa-1≠0 := ne_of_gt (sub_pos.mpr p.kappa_gt_one)
  have hβ : 1-q.beta≠0 := ne_of_gt (sub_pos.mpr q.beta_lt_one)
  have hy0 : q.y≠0 := ne_of_gt q.y_pos
  dsimp [Tuning.Xi,Tuning.A,Tuning.B,Tuning.x,kappaNumerator]
  rw [hy,hb]
  field_simp [hκq,hκp,hq,hp,hβ,hy0]
  ring

theorem Xi_strictMono_kappa (q p : Tuning) (hy : p.y=q.y) (hb : p.beta=q.beta)
    (hκ : q.kappa<p.kappa) {c : ℝ} (hc : c∈Icc (-1:ℝ) 1) : q.Xi c<p.Xi c := by
  apply sub_pos.mp
  rw [Xi_kappa_difference q p hy hb]
  exact div_pos (mul_pos (kappaNumerator_pos q hc) (sub_pos.mpr hκ))
    (by positivity [q.y_pos,q.beta_lt_one,p.kappa_gt_one,q.kappa_gt_one])

/-- Compactness upgrades strict pointwise growth to one uniform margin. -/
theorem exists_uniform_Xi_kappa_gap (q p : Tuning) (hy : p.y=q.y) (hb : p.beta=q.beta)
    (hκ : q.kappa<p.kappa) :
    ∃ ε : ℝ,0<ε ∧ ∀ c∈Icc (-1:ℝ) 1,q.Xi c+ε≤p.Xi c := by
  have hcont : ContinuousOn (fun c : ℝ=>p.Xi c-q.Xi c) (Icc (-1:ℝ) 1) := by
    unfold Tuning.Xi
    fun_prop
  obtain ⟨c,hc,hmin⟩ := isCompact_Icc.exists_isMinOn (by norm_num : (Icc (-1:ℝ) 1).Nonempty) hcont
  refine ⟨p.Xi c-q.Xi c,sub_pos.mpr (Xi_strictMono_kappa q p hy hb hκ hc),?_⟩
  intro d hd
  have hh := hmin hd
  change p.Xi c-q.Xi c≤p.Xi d-q.Xi d at hh
  linarith

theorem exists_uniform_cotangent_kappa_gap (q p : Tuning)
    (hy : p.y=q.y) (hb : p.beta=q.beta) (hκ : q.kappa<p.kappa) :
    ∃ ε : ℝ,0<ε ∧ ∀ ω∈Ioo (0:ℝ) Real.pi,
      q.Xi (Real.cos ω)/Real.sin ω+ε≤p.Xi (Real.cos ω)/Real.sin ω := by
  obtain ⟨ε,hε,hgap⟩ := exists_uniform_Xi_kappa_gap q p hy hb hκ
  refine ⟨ε,hε,?_⟩
  intro ω hω
  have hs : 0<Real.sin ω := Real.sin_pos_of_pos_of_lt_pi hω.1 hω.2
  have hc := hgap (Real.cos ω) ⟨Real.neg_one_le_cos _,Real.cos_le_one _⟩
  apply (le_div_iff₀ hs).mpr
  rw [add_mul,div_mul_cancel₀ _ (ne_of_gt hs)]
  have he := mul_le_mul_of_nonneg_left (Real.sin_le_one ω) hε.le
  linarith

end polyak.Levels
