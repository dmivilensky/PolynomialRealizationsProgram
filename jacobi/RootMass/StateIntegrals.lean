import jacobi.RootMass.SpatialQuadrature
import jacobi.RootMass.Constraint

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
All power quadratures are evaluated on the same actual attained optimizing
density. The actual amplitude multiplier and active constraint then give
its true spectral normalization, rather than a candidate profile identity.
Source: the proved genuine spatial and inverse-coordinate substitutions.
Use: the actual optimizer's amplitude equation gives its full spectral quadrature.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
set_option backward.isDefEq.respectTransparency false

/-- The four printed nonsingular quadratures satisfy their exact common linear identity.
Use: the actual optimizer's amplitude equation gives its full spectral quadrature.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: n*p(n)=3*n³+a*n²+n pointwise on the actual inverse branch. The
three actual continuous weights are integrable, so linearity of the integral applies. -/
theorem Ghat_terms (a : ℝ) (ha : -2*sqrt 3<a) (y : ℝ) :
    Ghat a ha y=2*y*(3*hat 3 a ha y+a*hat 2 a ha y+hat 1 a ha y) := by
  -- All three weights share the identical actual inverse-coordinate state.
  have he : (fun u => K a (node a ha y u))=
      fun u => 3*W 3 a (node a ha y u)+a*W 2 a (node a ha y u)+W 1 a (node a ha y u) := by
    funext u
    have hn := inverse_ge_one a ha (y*(1-u^2))
    have hn0 : 0<node a ha y u := zero_lt_one.trans_le hn
    have hq := q_pos ha hn
    unfold K W p
    field_simp
  unfold Ghat
  rw [he,intervalIntegral.integral_add
      (((hat_integrable 3 a ha y).const_mul 3).add ((hat_integrable 2 a ha y).const_mul a))
      (hat_integrable 1 a ha y),
    intervalIntegral.integral_add ((hat_integrable 3 a ha y).const_mul 3) ((hat_integrable 2 a ha y).const_mul a),
    intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]
  unfold hat
  ring

/-- Every positive integer root-power of the actual compact optimizer has the literal normalized quadrature.
Use: k=1,2,3 give the actual root mass, ordinary mass and energy.
Article: jacobi, Theorem D.8.
Proof: the original density equals the proved compact representative a.e.
Its positive branch has square root b*nhat on the core and zero outside.
Use the true spatial quadrature followed by the true inverse substitution. -/
theorem Profile.rootPower {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b)
    (k : ℕ) (hk : k≠0) :
    (∫ x,sqrt (P.density.value x)^k)=b^k*hat k a ha P.y := by
  -- Endpoint choices are retained until the final null-set interval replacement.
  have he : (fun x => sqrt (P.density.value x)^k)=ᵐ[volume]
      (Icc (-P.radius) P.radius).indicator (fun x => b^k*P.state x^k) := by
    filter_upwards [P.representative] with x hx
    rw [hx]
    by_cases hi : x∈Icc (-P.radius) P.radius
    · have hn := P.state_ge_one hb (abs_le.mpr hi)
      have heq : branch P.density a b P.mu x=b*P.state x := by unfold Profile.state; field_simp
      have hbr : 0≤branch P.density a b P.mu x := by rw [heq]; positivity
      rw [compactValue,indicator_of_mem hi,sqrt_sq hbr,heq,mul_pow,indicator_of_mem hi]
    · rw [compactValue,indicator_of_notMem hi,sqrt_zero,zero_pow hk,indicator_of_notMem hi]
  rw [integral_congr_ae he,integral_indicator measurableSet_Icc,integral_const_mul,
    integral_Icc_eq_integral_Ioo,P.quadrature ha hb (fun n => n^k),turningIntegral_power ha (P.y_pos hb)]

/-- The actual attained optimizer has the stated finite root-mass quadrature.
Use: evaluates the root penalty in the exact inner minimum and final weak duality bound.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: use the actual root-power quadrature at k=1. -/
theorem Profile.rootIntegral {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b) :
    P.density.rootIntegral=b*hat 1 a ha P.y := by
  unfold RootDensity.rootIntegral
  simpa only [pow_one] using P.rootPower ha hb 1 (by decide)

/-- The actual attained optimizer has the stated exact ordinary mass.
Use: evaluates the possibly signed mass penalty in the root-mass bound.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: sqrt(m)²=m pointwise, so the actual k=2 quadrature is exactly its mass. -/
theorem Profile.mass {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b) :
    P.density.mass=b^2*hat 2 a ha P.y := by
  unfold Density.mass
  have hh := P.rootPower ha hb 2 (by decide)
  simpa only [sq_sqrt (P.density.nonneg _)] using hh

/-- The actual attained optimizer has the stated exact finite energy.
Use: determines the true inner infimum, not just the cost of a candidate density.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: m^(3/2)=sqrt(m)³ on the actual nonnegative density, then use the genuine k=3 quadrature. -/
theorem Profile.energy {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b) :
    P.density.energy=b^3*hat 3 a ha P.y := by
  have hh := P.rootPower ha hb 3 (by decide)
  have he : (∫ x,sqrt (P.density.value x)^3)=P.density.energy := by
    unfold Density.energy
    congr 1
    funext x
    rw [rpow_div_two_eq_sqrt 3 (P.density.nonneg x),rpow_ofNat]
  rwa [he] at hh

/-- The true active moment of the attained optimizer equals the printed spectral quadrature.
Use: identifies its actual y with the unique defining root for T/b⁴.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: retain the multiplier's actual amplitude-derivative formula. Substitute
the three proved actual state integrals; y=1/(8*mu*b) and the exact Ghat
linear identity reduce the active threshold to the stated quadrature. -/
theorem Profile.constraint {a b T : ℝ} (P : Profile a b T) (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T) :
    T=b^4*Ghat a ha P.y := by
  -- The amplitude equation is the one proved by the actual normalized needle argument.
  have hnormal := P.normal
  unfold normalMultiplier at hnormal
  rw [P.energy ha hb,P.mass ha hb,P.rootIntegral ha hb] at hnormal
  rw [Ghat_terms]
  unfold Profile.y Profile.kappa at hnormal ⊢
  field_simp [P.mu_pos.ne',hb.ne'] at hnormal ⊢
  nlinarith

end
end jacobi.RootMass
