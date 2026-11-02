import jacobi.RootMass.Activity

/-!
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Root-amplitude scaling has exact objective and spectral formulas in the
original density domain. Its fourth-root normalizing factor has the stated
right derivative at a positive active constraint. The polynomial cost
chain rule is kept separate from the genuine localized spectral derivative.
Source: actual amplitude identities and classical one-sided chain/product rules.
Use: normalized needle objectives retain the original root-mass term exactly.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The true root integral has its exact root-amplitude scaling law.
Use: normalized needle objectives retain the original root-mass term exactly.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the actual pointwise square-root scaling factor leaves the genuine root integral. -/
theorem RootDensity.scaleRoot_rootIntegral (m : RootDensity) (r : ℝ) (hr : 0≤r) :
    (m.scaleRoot r hr).rootIntegral=r*m.rootIntegral := by
  unfold RootDensity.rootIntegral
  simp_rw [m.scaleRoot_sqrt]
  exact integral_const_mul _ _

/-- The actual root-scaled objective has its exact polynomial amplitude formula.
Use: differentiates the genuine normalized needle cost, with every root-power integral already finite.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: substitute the proved actual energy, mass and root-integral scaling laws;
the nonnegative amplitude branch turns (r²)^(3/2) into r³ exactly. -/
theorem RootDensity.scaleRoot_objective (m : RootDensity) (a b r : ℝ) (hr : 0≤r) :
    (m.scaleRoot r hr).objective a b=r^3*m.energy+(a*b/2)*r^2*m.mass+b^2*r*m.rootIntegral := by
  have hpow : (r^2)^(3/2:ℝ)=r^3 := by rw [rpow_div_two_eq_sqrt 3 (sq_nonneg r),rpow_ofNat,sqrt_sq hr]
  rw [(m.scaleRoot r hr).objective_terms,m.scaleRoot_rootIntegral]
  change (m.toDensity.scale (r^2) (sq_nonneg r)).energy+(a*b/2)*(m.toDensity.scale (r^2) (sq_nonneg r)).mass+_=_
  rw [Density.scale_energy,Density.scale_mass,hpow]
  ring

/-- The actual root-amplitude factor that normalizes a positive spectral second moment to T.
Use: supplies a genuine admissible normalized needle with exact G_2=T near its base point.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
-/
def normalization (T G : ℝ) : ℝ := sqrt (sqrt (T/G))

/-- A positive active constraint has root-amplitude normalization exactly one.
Use: the normalized variation has the original optimizer as its exact base value.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the positive target cancels itself and both square roots of one equal one. -/
theorem normalization_self {T : ℝ} (hT : 0<T) : normalization T T=1 := by simp [normalization,hT.ne']

/-- The actual normalization has the exact fourth power needed for the original spectral constraint.
Use: proves genuine feasibility of every sufficiently small normalized needle.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: square both nonnegative square roots and cancel the positive actual moment G. -/
theorem normalization_fourth {T G : ℝ} (hT : 0<T) (hG : 0<G) : (normalization T G)^4*G=T := by
  have hs := sq_sqrt (sqrt_nonneg (T/G))
  have ht := sq_sqrt (div_nonneg hT.le hG.le)
  change (sqrt (sqrt (T/G)))^4*G=T
  rw [show (sqrt (sqrt (T/G)))^4=((sqrt (sqrt (T/G)))^2)^2 by ring,hs,ht]
  exact div_mul_cancel₀ _ hG.ne'

/-- The genuine fourth-root normalizing factor has its exact one-sided derivative at a positive active moment.
Use: the localized spectral variation gives the correct normal multiplier in the pointwise minimum principle.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: apply the quotient rule and two positive square-root chain rules to the actual varying spectral moment. -/
theorem normalization_derivative {G : ℝ → ℝ} {T d : ℝ} (hT : 0<T) (hG0 : G 0=T)
    (hG : HasDerivWithinAt G d (Ici (0:ℝ)) 0) :
    HasDerivWithinAt (fun eps => normalization T (G eps)) (-d/(4*T)) (Ici (0:ℝ)) 0 := by
  -- The two actual square-root derivatives are taken at the positive normalized value one.
  have hp : T/G 0=1 := by rw [hG0,div_self hT.ne']
  have hq := (hasDerivWithinAt_const (0:ℝ) (Ici (0:ℝ)) T).div hG (by rw [hG0]; exact hT.ne')
  have hr := (hq.sqrt (by change T/G 0≠0; rw [hp]; norm_num)).sqrt
    (by change sqrt (T/G 0)≠0; rw [hp,sqrt_one]; norm_num)
  unfold normalization
  convert hr using 1
  change -d/(4*T)=(0*G 0-T*d)/(G 0)^2/(2*sqrt (T/G 0))/(2*sqrt (sqrt (T/G 0)))
  rw [hp,sqrt_one,hG0]
  field_simp [hT.ne']
  norm_num [mul_comm]

/-- The genuine normalized cost has the full polynomial right derivative, including the normalizing correction.
Use: the actual needle primitive derivatives are assembled into the exact scalar pointwise minimum inequality.
Article: jacobi, Appendix D.5 (global pointwise minimum principle).
Proof: the proved fourth-root derivative and exact polynomial amplitude
formula permit the ordinary product rule for each of the three actual cost terms. -/
theorem normalized_cost_derivative {G E M R : ℝ → ℝ} {T dG dE dM dR a b : ℝ}
    (hT : 0<T) (hG0 : G 0=T) (hG : HasDerivWithinAt G dG (Ici (0:ℝ)) 0)
    (hE : HasDerivWithinAt E dE (Ici (0:ℝ)) 0)
    (hM : HasDerivWithinAt M dM (Ici (0:ℝ)) 0)
    (hR : HasDerivWithinAt R dR (Ici (0:ℝ)) 0) :
    HasDerivWithinAt (fun eps => (normalization T (G eps))^3*E eps+
      (a*b/2)*(normalization T (G eps))^2*M eps+b^2*normalization T (G eps)*R eps)
      (dE+(a*b/2)*dM+b^2*dR-(dG/(4*T))*(3*E 0+a*b*M 0+b^2*R 0)) (Ici (0:ℝ)) 0 := by
  -- The correction is computed before substituting the actual needle's local values.
  have hr := normalization_derivative hT hG0 hG
  have hr0 : normalization T (G 0)=1 := by rw [hG0,normalization_self hT]
  convert (((hr.pow 3).mul hE).add ((((hr.pow 2).const_mul (a*b/2)).mul hM))).add
    (((hr.const_mul (b^2)).mul hR)) using 1
  dsimp only [Pi.pow_apply]
  rw [hr0]
  norm_num only [one_pow,Nat.cast_ofNat,Nat.reduceSub,mul_one]
  ring

end
end jacobi.RootMass
