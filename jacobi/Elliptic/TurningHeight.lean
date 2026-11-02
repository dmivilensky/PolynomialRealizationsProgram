import jacobi.Elliptic.FirstIntegral

/-!
Article: jacobi, Theorem D.5.
Every actual nonzero normalized Euler state has an attained positive
maximum with zero slope. The proved zero first integral fixes its turning
height Y>=1 and the exact branch (Y-sigma)=Y*sqrt(Y). A negative mass shift
then gives a genuine parameter t in (0,1), with Y=t^(-2) and
sigma=t^(-2)-t^(-3), as required by the elliptic quadrature substitution.
Source: attainment from two-sided decay and the actual conserved energy.
Use: ensures that a positive turning height is attained at a finite point.
-/
namespace jacobi.Elliptic
noncomputable section
open MeasureTheory Real Filter Set jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual normalized Euler state tends to its printed mass shift at both ends.
Use: ensures that a positive turning height is attained at a finite point.
Article: jacobi, Theorem D.5.
Proof: the actual H1 Green potential vanishes at both ends, and y is its affine normalization. -/
theorem eulerState_limits (m : Density) (μ l : ℝ) :
    Tendsto (eulerState m μ l) atTop (𝓝 (eulerShift μ l)) ∧
      Tendsto (eulerState m μ l) atBot (𝓝 (eulerShift μ l)) := by
  -- The affine normalization transfers both actual Green endpoint limits.
  have he : eulerState m μ l=fun x => (2*μ/eulerScale μ)*potential m x+eulerShift μ l := by
    funext x
    unfold eulerState eulerShift
    ring
  rw [he]
  constructor
  · simpa only [mul_zero,zero_add] using
      ((potential_sobolev m).tendsto_zero.1.const_mul (2*μ/eulerScale μ)).add_const (eulerShift μ l)
  · simpa only [mul_zero,zero_add] using
      ((potential_sobolev m).tendsto_zero.2.const_mul (2*μ/eulerScale μ)).add_const (eulerShift μ l)

/-- A nonzero actual Euler density forces its normalized positive part to be nonzero.
Use: excludes a trivial clipped ODE state before applying the turning-height argument.
Article: jacobi, Theorem D.5.
Proof: if y<=0 everywhere, the normalized Euler density vanishes everywhere,
forcing the a.e. equal original density's positive mass to vanish. -/
theorem eulerState_positive_point (m : Density) (hm : 0<m.mass) {μ : ℝ} (hμ : 0<μ) (l : ℝ)
    (he : m.value=ᵐ[volume] eulerDensity m μ l) : ∃ x,0<eulerState m μ l x := by
  -- The actual density normalization identifies zero clipping with zero source mass.
  by_contra! hn
  have hz (x : ℝ) : eulerDensity m μ l x=0 := by
    rw [eulerDensity_normalized m hμ,max_eq_right (hn x),zero_pow (by decide : 2≠0),mul_zero]
  have hae : m.value=ᵐ[volume] 0 := he.mono fun x hx => (hx.trans (hz x))
  have hmass : m.mass=0 := by simpa only [Density.mass,Pi.zero_apply,integral_zero] using integral_congr_ae hae
  exact hm.ne' hmass

/-- The actual finite-energy clipped solution has an attained positive turning height at least one.
Use: fixes the positive root and maximum in the elliptic quadrature substitution.
Article: jacobi, Theorem D.5.
Proof: two-sided decay to a nonpositive shift makes a positive maximum
attained. Its actual derivative vanishes. The zero first integral fixes
the turning equation, whose nonpositive shift forces the height at least one. -/
theorem clipped_turning_height {f d : ℝ → ℝ} {σ : ℝ} (hσ : σ≤0)
    (hf : ∀ x,HasDerivAt f (d x) x)
    (hd : ∀ x,HasDerivAt d (4*(f x-σ)-6*(max (f x) 0)^2) x)
    (hf2 : Integrable (fun x => (f x-σ)^2)) (hd2 : Integrable (fun x => d x^2))
    (hf3 : Integrable (fun x => (max (f x) 0)^3))
    (ht : Tendsto f atTop (𝓝 σ)) (hb : Tendsto f atBot (𝓝 σ))
    (hp : ∃ z,0<f z) :
    ∃ b : ℝ,1≤f b ∧ d b=0 ∧ (f b-σ)^2=f b^3 ∧ ∀ x,f x≤f b := by
  -- Positivity separates the maximum from the common limiting shift at both ends.
  obtain ⟨z,hz⟩ := hp
  have hc : Continuous f := continuous_iff_continuousAt.mpr fun x => (hf x).continuousAt
  have hlim : Tendsto f (cocompact ℝ) (𝓝 σ) := by
    rw [cocompact_eq_atBot_atTop]
    exact tendsto_sup.mpr ⟨hb,ht⟩
  have hσz : σ<f z := hσ.trans_lt hz
  obtain ⟨b,hmax⟩ := hc.exists_forall_ge' z ((hlim.eventually (Iio_mem_nhds hσz)).mono fun _ h => h.le)
  have hpos : 0<f b := hz.trans_le (hmax z)
  have hlocal : IsLocalMax f b := (show IsMaxOn f univ b from fun x _ => hmax x).isLocalMax univ_mem
  have hzero : d b=0 := hlocal.hasDerivAt_eq_zero (hf b)
  have hfirst := clipped_first_integral σ hf hd hf2 hd2 hf3 b
  rw [hzero,max_eq_left hpos.le] at hfirst
  have hroot : (f b-σ)^2=f b^3 := by nlinarith
  have hheight : 1≤f b := by
    have hsq : f b^2≤(f b-σ)^2 := by nlinarith [mul_nonpos_of_nonneg_of_nonpos hpos.le hσ,sq_nonneg σ]
    by_contra! hlt
    have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos hpos) (sub_neg.mpr hlt)
    nlinarith
  exact ⟨b,hheight,hzero,hroot,hmax⟩

/-- The negative-shift turning equation gives exactly the article's interior elliptic shape parameter.
Use: identifies the actual ODE turning data with the t-variable in Q_t, i_k, kappa and Xi.
Article: jacobi, Theorem D.5.
Proof: the positive root branch is Y-sigma=Y*sqrt(Y). Set t=1/sqrt(Y);
the negative shift forces sqrt(Y)>1, fixing all inverse powers exactly. -/
theorem turning_shape_parameter {Y σ : ℝ} (hY : 1≤Y) (hσ : σ<0)
    (he : (Y-σ)^2=Y^3) :
    ∃ t : ℝ,0<t ∧ t<1 ∧ Y=(t⁻¹)^2 ∧ σ=(t⁻¹)^2-(t⁻¹)^3 := by
  -- Nonnegative square roots select the unique physically relevant turning branch.
  have hYpos : 0<Y := lt_of_lt_of_le zero_lt_one hY
  have hspos : 0<sqrt Y := sqrt_pos.mpr hYpos
  have hs2 := Real.sq_sqrt hYpos.le
  have hbranch : Y-σ=Y*sqrt Y := by
    apply (sq_eq_sq₀ (by linarith : 0≤Y-σ) (by positivity : 0≤Y*sqrt Y)).mp
    rw [he,mul_pow,hs2]
    ring
  have hs1 : 1<sqrt Y := by nlinarith [sqrt_nonneg Y]
  let t := (sqrt Y)⁻¹
  have htpos : 0<t := inv_pos.mpr hspos
  have htprod : t*sqrt Y=1 := inv_mul_cancel₀ hspos.ne'
  have ht1 : t<1 := by nlinarith
  refine ⟨t,htpos,ht1,?_,?_⟩
  · simpa only [t,inv_inv] using hs2.symm
  · simp only [t,inv_inv]
    rw [show (sqrt Y)^3=(sqrt Y)^2*sqrt Y by ring,hs2]
    linarith

end
end jacobi.Elliptic
