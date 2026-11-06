import nesterov.TwoStep.AsymptoticsBasics

/-! The finite-condition-number quadratic lower bound for every Nesterov
query τ=β, proved directly from the endpoint root conditions. -/
namespace nesterov.TwoStep
noncomputable section

private theorem endpoint_combination {μ h r X B D d : ℝ}
    (hμ : 0<μ) (hX : 0<X) (hB : 0<B) (hD : 0<D)
    (hlow : X-r^2≤X*h*μ) (hhigh : h*B≤B+r^2)
    (halg : 3*d^2*X*(B+r^2)≤D*(X-r^2)*B) :
    3*d^2≤μ*D := by
  have hright : 0<X*(B+r^2) := mul_pos hX (add_pos_of_pos_of_nonneg hB (sq_nonneg r))
  apply (mul_le_mul_iff_of_pos_right hright).mp
  calc
    (3*d^2)*(X*(B+r^2))=3*d^2*X*(B+r^2) := by ring
    _≤D*(X-r^2)*B := halg
    _≤D*(X*h*μ)*B := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlow hD.le) hB.le
    _=(μ*D*X)*(h*B) := by ring
    _≤(μ*D*X)*(B+r^2) := mul_le_mul_of_nonneg_left hhigh (by positivity)
    _=(μ*D)*(X*(B+r^2)) := by ring

/-- Endpoint signs and the small-curvature determinant force the sharp
Nesterov radius inequality. No stability assumption is added. -/
theorem nesterov_radius_constraint {μ b h r : ℝ} (hμ : 0<μ) (hb : 0≤b)
    (hr : 0<r) (hr1 : r<1)
    (hfirst : 0≤r^2-Quadratic.S b b h μ*r+Quadratic.Q b b h μ)
    (hlast : 0≤r^2+Quadratic.S b b h 1*r+Quadratic.Q b b h 1)
    (hdet : Quadratic.Q b b h μ≤r^2) :
    (3+μ)*(1-r)^2≤4*μ := by
  let d := 1-r
  let A := r-b*d
  let B := r+b*(1+r)
  let D := (1+r)*(3-r)
  have hd : 0<d := by dsimp [d];linarith
  have h3r : 0<3-r := by linarith
  have hB : 0<B := by dsimp [B];positivity
  have hD : 0<D := by dsimp [D];positivity
  have hhigh : h*B≤B+r^2 := by
    dsimp [B,Quadratic.S,Quadratic.Q] at hlast ⊢
    nlinarith
  have hineq : 3*d^2≤μ*D := by
    by_cases hsplit : b≤r/(2-r)
    · have hmargin : 0≤r-(2-r)*b := by
        have hh := (le_div_iff₀ (by linarith : 0<2-r)).mp hsplit
        nlinarith
      have hA : 0<A := by dsimp [A,d];nlinarith
      have hlow : A-r^2≤A*h*μ := by
        dsimp [A,d,Quadratic.S,Quadratic.Q] at hfirst ⊢
        nlinarith
      have hi : D*(A-r^2)*B-3*d^2*A*(B+r^2)=
          2*d*(1+r)*r*(r-(2-r)*b)*(r+2*b) := by dsimp [D,A,B,d];ring
      have hpos : 0≤2*d*(1+r)*r*(r-(2-r)*b)*(r+2*b) := by positivity
      exact endpoint_combination hμ hA hB hD hlow hhigh (by linarith)
    · have hsplit' : r/(2-r)<b := lt_of_not_ge hsplit
      have hbpos : 0<b := (div_pos hr (by linarith : 0<2-r)).trans hsplit'
      have hmargin : 0≤(2-r)*b-r := by
        have hh := (div_lt_iff₀ (by linarith : 0<2-r)).mp hsplit'
        nlinarith
      have hlow : b-r^2≤b*h*μ := by dsimp [Quadratic.Q] at hdet;nlinarith
      have hi : D*(b-r^2)*B-3*d^2*b*(B+r^2)=
          (1+r)*r*((2-r)*b-r)*(4*b+r*(3-r)) := by dsimp [D,B,d];ring
      have hpos : 0≤(1+r)*r*((2-r)*b-r)*(4*b+r*(3-r)) := by positivity
      exact endpoint_combination hμ hbpos hB hD hlow hhigh (by linarith)
  have hDexpr : D=4-d^2 := by dsimp [D,d];ring
  rw [hDexpr] at hineq
  dsimp [d] at hineq
  nlinarith

/-- The sharp finite quadratic lower bound over every β and every positive
step size, with the Nesterov query restriction τ=β. -/
theorem nesterov_quadratic_price (q : Momentum.Tuning) {μ : ℝ}
    (hμ : 0<μ) (hμ1 : μ<1) (hτ : q.tau=q.beta) :
    1-2*Real.sqrt (μ/(3+μ))≤Quadratic.quadraticRate μ 1 q.beta q.tau q.stepSize := by
  have hden : 0<3+μ := by linarith
  let s := Real.sqrt (μ/(3+μ))
  have hs : 0<s := Real.sqrt_pos.mpr (div_pos hμ hden)
  have hsq : s^2=μ/(3+μ) := Real.sq_sqrt (div_pos hμ hden).le
  have hsqden : (3+μ)*s^2=μ := by rw [hsq];field_simp
  have hsquarter : s^2<1/4 := by rw [hsq];apply (div_lt_iff₀ hden).mpr;linarith
  have hbound0 : 0<1-2*s := by nlinarith
  have hbound1 : 1-2*s<1 := by linarith
  by_contra hn
  have hρ : 0≤Quadratic.quadraticRate μ 1 q.beta q.tau q.stepSize :=
    Quadratic.quadraticRate_nonneg_general hμ1.le
  obtain ⟨r,hρr,hrb⟩ := exists_between (lt_of_not_ge hn)
  have hr : 0<r := hρ.trans_lt hρr
  have hr1 : r<1 := hrb.trans hbound1
  have hroots (lam : ℝ) (hlam : lam∈Set.Icc μ 1) (z : ℂ)
      (hz : z^2-(Quadratic.S q.beta q.beta q.stepSize lam:ℂ)*z+
        (Quadratic.Q q.beta q.beta q.stepSize lam:ℂ)=0) : ‖z‖≤r := by
    apply (Quadratic.root_norm_le_rate_general hμ1.le hlam ?_).trans hρr.le
    rw [hτ,Quadratic.characteristic_eq]
    exact hz
  have hp := (roots_le_radius_signs hr.le (hroots μ ⟨le_rfl,hμ1.le⟩)).1
  have hm := (roots_le_radius_signs hr.le (hroots 1 ⟨hμ1.le,le_rfl⟩)).2
  have hq := (Quadratic.endpoint_bounds hr.le hr1 (hroots μ ⟨le_rfl,hμ1.le⟩)).2.2
  have hc := nesterov_radius_constraint hμ q.beta_nonneg hr hr1 hp hm hq
  have hgap : (2*s)^2<(1-r)^2 := by nlinarith
  have hh := mul_lt_mul_of_pos_left hgap hden
  nlinarith

theorem nesterov_quadratic_price_epsilon (q : Momentum.Tuning) {ε : ℝ}
    (hε : 0<ε) (hε1 : ε<1) (hτ : q.tau=q.beta) :
    1-2*ε/Real.sqrt (3+ε^2)≤Quadratic.quadraticRate (ε^2) 1 q.beta q.tau q.stepSize := by
  have hh := nesterov_quadratic_price q (sq_pos_of_pos hε) (by nlinarith : ε^2<1) hτ
  rw [Real.sqrt_div (sq_nonneg ε),Real.sqrt_sq hε.le] at hh
  convert hh using 1
  ring

theorem nesterov_quadratic_price_kappa (q : Momentum.Tuning) {κ : ℝ}
    (hκ : 1<κ) (hτ : q.tau=q.beta) :
    1-2/Real.sqrt (3*κ+1)≤Quadratic.quadraticRate (1/κ) 1 q.beta q.tau q.stepSize := by
  have hκ0 : 0<κ := zero_lt_one.trans hκ
  have hh := nesterov_quadratic_price q (one_div_pos.mpr hκ0)
    ((div_lt_one hκ0).mpr hκ) hτ
  have he : (1/κ)/(3+1/κ)=1/(3*κ+1) := by
    field_simp [hκ0.ne',show 3*κ+1≠0 by positivity]
  rw [he,Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one] at hh
  convert hh using 1
  ring

/-- Closed scaled Jury sufficiency, including repeated boundary roots. -/
theorem quadratic_roots_le_radius {a q r : ℝ} (hr : 0<r) (hq : q≤r^2)
    (hp : 0≤r^2-a*r+q) (hm : 0≤r^2+a*r+q) :
    ∀ z : ℂ,z^2-(a:ℂ)*z+(q:ℂ)=0 → ‖z‖≤r := by
  have ha : a≤2*r := (mul_le_mul_iff_of_pos_right hr).mp (by nlinarith)
  have hna : -a≤2*r := (mul_le_mul_iff_of_pos_right hr).mp (by nlinarith)
  intro z hz
  by_contra hn
  obtain ⟨s,hrs,hsz⟩ := exists_between (lt_of_not_ge hn)
  have hs : 0<s := hr.trans hrs
  have hp' : 0<s^2-a*s+q := by
    have hh := mul_pos (sub_pos.mpr hrs) (show 0<s+r-a by linarith)
    nlinarith
  have hm' : 0<s^2+a*s+q := by
    have hh := mul_pos (sub_pos.mpr hrs) (show 0<s+r+a by linarith)
    nlinarith
  have hq' : q<s^2 := by nlinarith
  exact (not_lt_of_ge hsz.le) (((Quadratic.roots_lt_radius_iff hs).mpr ⟨hq',hp',hm'⟩) z hz)

private theorem nesterov_rate_of_radius {μ h r : ℝ} (hμ : 0<μ) (hμ1 : μ<1)
    (hr : 0<r) (hr1 : r<1) (hh : 0<h)
    (hhμ : h*μ=(1-r)^2) (hhsum : h*(3+μ)=4) :
    Quadratic.quadraticRate μ 1 (r/(2-r)) (r/(2-r)) h=r := by
  let b := r/(2-r)
  have hd : 0<2-r := by linarith
  have hb : 0<b := div_pos hr hd
  have hAb : (1+b)*r-b=b := by dsimp [b];field_simp [hd.ne'];ring
  have hh1 : 1-h= -r*(2-r)/3 := by nlinarith
  have hSμ : Quadratic.S b b h μ=2*r := by
    unfold Quadratic.S
    rw [hhμ]
    dsimp [b]
    field_simp [hd.ne']
    ring
  have hQμ : Quadratic.Q b b h μ=r^2 := by
    unfold Quadratic.Q
    rw [hhμ]
    dsimp [b]
    field_simp [hd.ne']
    ring
  have hS1 : Quadratic.S b b h 1= -2*r/3 := by
    rw [show Quadratic.S b b h 1=(1+b)*(1-h) by unfold Quadratic.S;ring,hh1]
    dsimp [b]
    field_simp [hd.ne']
    ring
  have hQ1 : Quadratic.Q b b h 1= -r^2/3 := by
    rw [show Quadratic.Q b b h 1=b*(1-h) by unfold Quadratic.Q;ring,hh1]
    dsimp [b]
    field_simp [hd.ne']
  have hall (lam : ℝ) (hlam : lam∈Set.Icc μ 1) (z : ℂ)
      (hz : Quadratic.characteristic b b h lam z=0) : ‖z‖≤r := by
    have hq : Quadratic.Q b b h lam≤r^2 := by
      have hid : Quadratic.Q b b h lam=Quadratic.Q b b h μ-h*b*(lam-μ) := by
        unfold Quadratic.Q;ring
      rw [hid,hQμ]
      have hn : 0≤h*b*(lam-μ) := mul_nonneg (mul_pos hh hb).le (sub_nonneg.mpr hlam.1)
      linarith
    have hp : 0≤r^2-Quadratic.S b b h lam*r+Quadratic.Q b b h lam := by
      have hid : r^2-Quadratic.S b b h lam*r+Quadratic.Q b b h lam=
          (r^2-Quadratic.S b b h μ*r+Quadratic.Q b b h μ)+h*(lam-μ)*((1+b)*r-b) := by
        unfold Quadratic.S Quadratic.Q;ring
      rw [hid,hSμ,hQμ,hAb]
      have hn : 0≤h*(lam-μ)*b := mul_nonneg (mul_nonneg hh.le (sub_nonneg.mpr hlam.1)) hb.le
      nlinarith
    have hm : 0≤r^2+Quadratic.S b b h lam*r+Quadratic.Q b b h lam := by
      have hid : r^2+Quadratic.S b b h lam*r+Quadratic.Q b b h lam=
          (r^2+Quadratic.S b b h 1*r+Quadratic.Q b b h 1)+h*(1-lam)*((1+b)*r+b) := by
        unfold Quadratic.S Quadratic.Q;ring
      rw [hid,hS1,hQ1]
      have h1lam : 0≤1-lam := sub_nonneg.mpr hlam.2
      have hn : 0≤h*(1-lam)*((1+b)*r+b) := by positivity
      nlinarith
    exact quadratic_roots_le_radius hr hq hp hm z (by rwa [←Quadratic.characteristic_eq])
  apply le_antisymm
  · obtain ⟨lam,hlam,z,hz,hρ⟩ := (Quadratic.quadraticRate_isGreatest_general (β:=b) (τ:=b) (h:=h) hμ1.le).1
    rw [hρ]
    exact hall lam hlam z hz
  · have hroot : Quadratic.characteristic b b h μ (r:ℂ)=0 := by
      rw [Quadratic.characteristic_eq,hSμ,hQμ]
      push_cast
      ring
    have hn := Quadratic.root_norm_le_rate_general hμ1.le ⟨le_rfl,hμ1.le⟩ hroot
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr] using hn

/-- The explicit selected Nesterov tuning attains the sharp finite lower bound. -/
theorem nesterov_quadratic_optimal_rate {μ : ℝ} (hμ : 0<μ) (hμ1 : μ<1) :
    let r := 1-2*Real.sqrt (μ/(3+μ))
    Quadratic.quadraticRate μ 1 (r/(2-r)) (r/(2-r)) (4/(3+μ))=r := by
  let s := Real.sqrt (μ/(3+μ))
  have hden : 0<3+μ := by linarith
  have hs : 0<s := Real.sqrt_pos.mpr (div_pos hμ hden)
  have hsq : s^2=μ/(3+μ) := Real.sq_sqrt (div_pos hμ hden).le
  have hquarter : s^2<1/4 := by rw [hsq];apply (div_lt_iff₀ hden).mpr;linarith
  have hr : 0<1-2*s := by nlinarith
  have hr1 : 1-2*s<1 := by linarith
  apply nesterov_rate_of_radius hμ hμ1 hr hr1 (div_pos (by norm_num) hden)
  · have hsqden : (3+μ)*s^2=μ := by rw [hsq];field_simp
    apply mul_right_cancel₀ hden.ne'
    field_simp [hden.ne']
    nlinarith [hsqden]
  · field_simp

private theorem radius_to_beta (a b : ℝ) (ha : a≠0) :
    (1-b/a)/(2-(1-b/a))=(a-b)/(a+b) := by
  rw [show 1-b/a=(a-b)/a by field_simp]
  rw [show 2-(a-b)/a=(a+b)/a by field_simp;ring]
  exact div_div_div_cancel_right₀ ha _ _

theorem nesterov_quadratic_optimal_rate_epsilon {ε : ℝ} (hε : 0<ε) (hε1 : ε<1) :
    let b := (Real.sqrt (3+ε^2)-2*ε)/(Real.sqrt (3+ε^2)+2*ε)
    Quadratic.quadraticRate (ε^2) 1 b b (4/(3+ε^2))=1-2*ε/Real.sqrt (3+ε^2) := by
  have hh := nesterov_quadratic_optimal_rate (sq_pos_of_pos hε) (by nlinarith : ε^2<1)
  have hR : 0<Real.sqrt (3+ε^2) := Real.sqrt_pos.mpr (by positivity)
  have hr : 1-2*Real.sqrt (ε^2/(3+ε^2))=1-2*ε/Real.sqrt (3+ε^2) := by
    rw [Real.sqrt_div (sq_nonneg ε),Real.sqrt_sq hε.le]
    ring
  dsimp only at hh
  rw [hr] at hh
  have hb : (1-2*ε/Real.sqrt (3+ε^2))/(2-(1-2*ε/Real.sqrt (3+ε^2)))=
      (Real.sqrt (3+ε^2)-2*ε)/(Real.sqrt (3+ε^2)+2*ε) := by
    exact radius_to_beta _ _ hR.ne'
  rw [hb] at hh
  exact hh

theorem nesterov_quadratic_optimal_rate_kappa {κ : ℝ} (hκ : 1<κ) :
    let b := (Real.sqrt (3*κ+1)-2)/(Real.sqrt (3*κ+1)+2)
    Quadratic.quadraticRate (1/κ) 1 b b (4*κ/(3*κ+1))=1-2/Real.sqrt (3*κ+1) := by
  have hκ0 : 0<κ := zero_lt_one.trans hκ
  have hh := nesterov_quadratic_optimal_rate (one_div_pos.mpr hκ0) ((div_lt_one hκ0).mpr hκ)
  have hR : 0<Real.sqrt (3*κ+1) := Real.sqrt_pos.mpr (by positivity)
  have hfrac : (1/κ)/(3+1/κ)=1/(3*κ+1) := by
    field_simp [hκ0.ne',show 3*κ+1≠0 by positivity]
  have hr : 1-2*Real.sqrt ((1/κ)/(3+1/κ))=1-2/Real.sqrt (3*κ+1) := by
    rw [hfrac,Real.sqrt_div (by norm_num : (0:ℝ)≤1),Real.sqrt_one]
    ring
  dsimp only at hh
  rw [hr] at hh
  have hb : (1-2/Real.sqrt (3*κ+1))/(2-(1-2/Real.sqrt (3*κ+1)))=
      (Real.sqrt (3*κ+1)-2)/(Real.sqrt (3*κ+1)+2) := by
    exact radius_to_beta _ _ hR.ne'
  have hstep : 4/(3+1/κ)=4*κ/(3*κ+1) := by
    field_simp [hκ0.ne',show 3*κ+1≠0 by positivity]
  rw [hb,hstep] at hh
  exact hh

end
end nesterov.TwoStep
