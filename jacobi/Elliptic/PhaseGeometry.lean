import jacobi.Elliptic.ClippedUniqueness

/-!
Article: jacobi, Theorem D.5.
The turning cubic has just one zero between the limiting shift and the
attained maximum. Reflection uniqueness gives an even profile about the
peak; translation uniqueness and decay exclude any second turning point.
Consequently the actual descending branch has no zero of its slope.
Source: autonomous ODE uniqueness, the cubic factorization and decay at infinity.
Use: excludes every critical value other than the peak in the actual elliptic profile.
-/
namespace jacobi.Elliptic
noncomputable section
open Real Filter Set
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The turning cubic is strictly positive below its positive maximum and above the negative limiting shift.
Use: excludes every critical value other than the peak in the actual elliptic profile.
Article: jacobi, Appendix D.4 (green first integral and optimizer geometry).
Proof: below zero the cubic is a positive square; above zero factor it as
(Y-v)*(v²+(Y-1)*v+sigma²/Y), whose second factor is strictly positive. -/
theorem turning_polynomial_pos {Y σ v : ℝ} (hY : 1≤Y)
    (hroot : (Y-σ)^2=Y^3) (hv : σ<v) (hvY : v<Y) :
    0<(v-σ)^2-(max v 0)^3 := by
  -- The factorization uses the actual turning equation, fixing the correct cubic root.
  by_cases hv0 : v≤0
  · rw [max_eq_right hv0,zero_pow (by decide : 3≠0),sub_zero]
    exact sq_pos_of_pos (sub_pos.mpr hv)
  · have hvp : 0<v := lt_of_not_ge hv0
    have hYp : 0<Y := lt_of_lt_of_le zero_lt_one hY
    have hfactor : (v-σ)^2-v^3=(Y-v)*(v^2+(Y-1)*v+σ^2/Y) := by
      apply (mul_right_inj' hYp.ne').mp
      field_simp
      linear_combination v * hroot
    rw [max_eq_left hvp.le,hfactor]
    exact mul_pos (sub_pos.mpr hvY) (by positivity)

/-- A positive-period function with a finite limit at plus infinity equals that limit everywhere.
Use: excludes repeated turning points, which autonomous uniqueness would make periodic.
Article: jacobi, Theorem D.5.
Source: periodicity and uniqueness of limits at infinity.
Proof: evaluate along x+n*p, which tends to infinity while its function value stays f(x). -/
theorem periodic_eq_limit {f : ℝ → ℝ} {p σ : ℝ} (hp : 0<p)
    (hf : Function.Periodic f p) (hlim : Tendsto f atTop (𝓝 σ)) (x : ℝ) : f x=σ := by
  have ht : Tendsto (fun n : ℕ => x+(n:ℝ)*p) atTop atTop := by
    exact tendsto_const_nhds.add_atTop (Filter.Tendsto.atTop_mul_const hp tendsto_natCast_atTop_atTop)
  have he (n : ℕ) : f (x+(n:ℝ)*p)=f x := hf.nat_mul n x
  have hc : Tendsto (fun n : ℕ => f (x+(n:ℝ)*p)) atTop (𝓝 (f x)) := by
    simpa only [he] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => f x) atTop (𝓝 (f x)))
  exact tendsto_nhds_unique hc (hlim.comp ht)

/-- An actual clipped solution is symmetric about every point with zero slope.
Use: gives reflection symmetry of the elliptic optimizer from its attained turning data.
Article: jacobi, Theorem D.5.
Proof: reflection of the value and sign reversal of the slope solve the
same autonomous equation and have identical initial data at the turning point. -/
theorem clipped_reflect {f d : ℝ → ℝ} (σ b : ℝ)
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d (4*(f x-σ)-6*(max (f x) 0)^2) x) (hdb : d b=0) :
    (∀ x,f (2*b-x)=f x) ∧ (∀ x,d (2*b-x)=-d x) := by
  -- The reflected slope carries a minus sign; its derivative has the original field value.
  have hg (x : ℝ) : HasDerivAt (fun y => f (2*b-y)) (-d (2*b-x)) x := by
    simpa only [Function.comp_def,mul_neg_one] using
      (hf (2*b-x)).comp x ((hasDerivAt_id x).const_sub (2*b))
  have he (x : ℝ) : HasDerivAt (fun y => -d (2*b-y))
      (4*(f (2*b-x)-σ)-6*(max (f (2*b-x)) 0)^2) x := by
    convert ((hd (2*b-x)).comp x ((hasDerivAt_id x).const_sub (2*b))).neg using 1
    · rfl
    · ring
  have hu := clipped_unique σ b hf hd hg he (by rw [show 2*b-b=b by ring])
    (by rw [show 2*b-b=b by ring,hdb,neg_zero])
  refine ⟨fun x => (congrFun hu.1 x).symm,fun x => ?_⟩
  have h := congrFun hu.2 x
  change d x=-d (2*b-x) at h
  linarith

/-- The descending side of a decaying actual clipped optimizer has no second critical point.
Use: the first integral therefore fixes one nonvanishing square-root Jacobian for the elliptic quadratures.
Article: jacobi, Theorem D.5.
Proof: a zero slope forces the same maximum value by the strict cubic
factorization. Autonomous uniqueness then supplies a positive period;
the finite endpoint limit contradicts the strictly larger peak value. -/
theorem clipped_no_second_turning {f d : ℝ → ℝ} {σ b : ℝ} (hσ : σ<0)
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d (4*(f x-σ)-6*(max (f x) 0)^2) x)
    (hfirst : ∀ x,d x^2=4*((f x-σ)^2-(max (f x) 0)^3))
    (hY : 1≤f b) (hdb : d b=0) (hroot : (f b-σ)^2=f b^3)
    (hmax : ∀ x,f x≤f b) (hlower : ∀ x,σ<f x) (hlim : Tendsto f atTop (𝓝 σ))
    {x : ℝ} (hx : b<x) : d x≠0 := by
  -- A second critical state would repeat the entire autonomous trajectory.
  intro hdx
  have hfx : f x=f b := by
    apply le_antisymm (hmax x)
    by_contra! hlt
    have hp := turning_polynomial_pos hY hroot (hlower x) hlt
    have hw := hfirst x
    rw [hdx] at hw
    nlinarith
  let p := x-b
  have hp : 0<p := sub_pos.mpr hx
  have hg (z : ℝ) : HasDerivAt (fun y => f (y+p)) (d (z+p)) z := by
    simpa only [Function.comp_def,id_eq,mul_one] using (hf (z+p)).comp z ((hasDerivAt_id z).add_const p)
  have he (z : ℝ) : HasDerivAt (fun y => d (y+p))
      (4*(f (z+p)-σ)-6*(max (f (z+p)) 0)^2) z := by
    simpa only [Function.comp_def,id_eq,mul_one] using (hd (z+p)).comp z ((hasDerivAt_id z).add_const p)
  have hb : b+p=x := by dsimp only [p]; ring
  have hu := clipped_unique σ b hf hd hg he (by rw [hb,hfx]) (by rw [hb,hdb,hdx])
  have hper : Function.Periodic f p := fun z => (congrFun hu.1 z).symm
  have hz := periodic_eq_limit hp hper hlim b
  linarith

/-- The normalized elliptic turning point has strictly negative actual acceleration.
Use: selects the negative square-root branch of the first integral to the right of the peak.
Article: jacobi, Theorem D.5.
Proof: the turning equation gives Y-sigma=Y*sqrt(Y); since Y>=1,
sqrt(Y)<=Y and the acceleration is at most -2Y²<0. -/
theorem turning_acceleration_neg {Y σ : ℝ} (hY : 1≤Y) (hσ : σ<0)
    (hroot : (Y-σ)^2=Y^3) : 4*(Y-σ)-6*(max Y 0)^2<0 := by
  -- Nonnegative square roots select the same branch as the actual turning equation.
  have hYp : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hs2 := Real.sq_sqrt hYp.le
  have hb : Y-σ=Y*sqrt Y := by
    apply (sq_eq_sq₀ (by linarith : 0≤Y-σ) (by positivity : 0≤Y*sqrt Y)).mp
    rw [hroot,mul_pow,hs2]
    ring
  have hsq : sqrt Y≤Y := (Real.sqrt_le_iff).mpr ⟨hYp.le,by nlinarith⟩
  rw [max_eq_left hYp.le,hb]
  nlinarith [mul_le_mul_of_nonneg_left hsq hYp.le,sq_pos_of_pos hYp]

/-- The actual clipped optimizer has strictly negative slope at every point right of its maximum.
Use: provides the nonvanishing descending Jacobian in the elliptic mass and energy quadratures.
Article: jacobi, Theorem D.5.
Proof: negative turning acceleration gives negative slope immediately to
the right. A later nonnegative slope would cross zero by continuity,
contradicting the proved absence of any second turning point. -/
theorem clipped_slope_neg {f d : ℝ → ℝ} {σ b : ℝ} (hσ : σ<0)
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d (4*(f x-σ)-6*(max (f x) 0)^2) x)
    (hfirst : ∀ x,d x^2=4*((f x-σ)^2-(max (f x) 0)^3))
    (hY : 1≤f b) (hdb : d b=0) (hroot : (f b-σ)^2=f b^3)
    (hmax : ∀ x,f x≤f b) (hlower : ∀ x,σ<f x) (hlim : Tendsto f atTop (𝓝 σ))
    {x : ℝ} (hx : b<x) : d x<0 := by
  -- Short right increments start on the negative-slope branch.
  have hD : HasDerivAt (fun t : ℝ => d (b+t))
      (4*(f b-σ)-6*(max (f b) 0)^2) 0 := by
    simpa only [Function.comp_def,id_eq,add_zero,mul_one] using
      (hd (b+id 0)).comp 0 ((hasDerivAt_id (0:ℝ)).const_add b)
  have he := jacobi.Variational.HasDerivAt.eventually_right_descent hD
    (turning_acceleration_neg hY hσ hroot)
  have hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,t<x-b := by
    have hh : ∀ᶠ t : ℝ in 𝓝 0,t<x-b := Iio_mem_nhds (sub_pos.mpr hx)
    exact hh.filter_mono nhdsWithin_le_nhds
  obtain ⟨t,htd,htx,htp⟩ := (he.and (hsmall.and self_mem_nhdsWithin)).exists
  have ht0 : 0<t := htp
  have hneg : d (b+t)<0 := by simpa only [add_zero,hdb] using htd
  by_contra! hdx
  have hc : Continuous d := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  obtain ⟨z,hz,hdz⟩ := (intermediate_value_Icc
    (show b+t≤x by linarith) hc.continuousOn) ⟨hneg.le,hdx⟩
  exact clipped_no_second_turning hσ hf hd hfirst hY hdb hroot hmax hlower hlim
    (by have hh := hz.1; linarith : b<z) hdz

end
end jacobi.Elliptic
