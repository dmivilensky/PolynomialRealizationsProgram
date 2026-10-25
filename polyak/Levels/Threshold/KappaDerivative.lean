import polyak.Levels.Threshold.Kappa

/-! The literal derivative formula of Lemma kappa, in original source
coordinates at fixed αL and momentum. -/
noncomputable section
namespace polyak.Levels
open General Filter
open scoped Topology

def XiAtKappa (q : Tuning) (κ c : ℝ) : ℝ :=
  let A := 1+q.beta-(q.y/κ+q.y)/2
  let B := (q.y-q.y/κ)/2
  (B^2-(1-q.beta)^2-A^2+2*A*(1+q.beta)*c-4*q.beta*c^2)/(2*B*(1-q.beta))

theorem XiAtKappa_at_self (q : Tuning) (c : ℝ) : XiAtKappa q q.kappa c=q.Xi c := rfl

theorem XiAtKappa_inverse_form (q : Tuning) {κ : ℝ} (hκ : 1<κ) (c : ℝ) :
    XiAtKappa q κ c=XiAtKappa q 2 c+
      (kappaNumerator q.y q.beta c/(q.y*(1-q.beta)))*(1-(κ-1)⁻¹) := by
  have hk : κ≠0 := ne_of_gt (zero_lt_one.trans hκ)
  have hk1 : κ-1≠0 := ne_of_gt (sub_pos.mpr hκ)
  have hβ : 1-q.beta≠0 := ne_of_gt (sub_pos.mpr q.beta_lt_one)
  have hy : q.y≠0 := ne_of_gt q.y_pos
  dsimp [XiAtKappa,kappaNumerator]
  field_simp [hk,hk1,hβ,hy]
  ring

theorem hasDerivAt_XiAtKappa (q : Tuning) {κ : ℝ} (hκ : 1<κ) (c : ℝ) :
    HasDerivAt (fun k=>XiAtKappa q k c)
      (kappaNumerator q.y q.beta c/(q.y*(1-q.beta)*(κ-1)^2)) κ := by
  have hk1 : κ-1≠0 := ne_of_gt (sub_pos.mpr hκ)
  have hh := (((((hasDerivAt_id κ).sub_const 1).inv hk1).const_sub 1).const_mul
    (kappaNumerator q.y q.beta c/(q.y*(1-q.beta)))).const_add (XiAtKappa q 2 c)
  have hderiv : HasDerivAt
      (fun k=>XiAtKappa q 2 c+
        (kappaNumerator q.y q.beta c/(q.y*(1-q.beta)))*(1-(k-1)⁻¹))
      (kappaNumerator q.y q.beta c/(q.y*(1-q.beta)*(κ-1)^2)) κ := by
    convert hh using 1
    · rfl
    · dsimp only [id_eq]
      field_simp
  apply hderiv.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hκ] with k hk
  exact XiAtKappa_inverse_form q hk c

theorem deriv_XiAtKappa (q : Tuning) {κ : ℝ} (hκ : 1<κ) (c : ℝ) :
    deriv (fun k=>XiAtKappa q k c) κ=
      kappaNumerator q.y q.beta c/(q.y*(1-q.beta)*(κ-1)^2) :=
  (hasDerivAt_XiAtKappa q hκ c).deriv

end polyak.Levels
