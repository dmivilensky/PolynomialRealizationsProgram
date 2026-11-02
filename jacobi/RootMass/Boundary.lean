import jacobi.RootMass.ProfileGeometry

/-!
Article: jacobi, Appendix D.5 (compact root-mass profile).
The exterior source vanishes, so the actual right Green half is zero at
the free boundary. The original convolution halves then give the exact
slope matching, with no assumed exterior ODE solution or limit condition.
Source: the previously verified Green half-integrals in chebyshev2.
Use: fixes the constant of the inner profile's conserved energy.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open chebyshev2.GroundState chebyshev2.Sobolev
set_option backward.isDefEq.respectTransparency false

/-- Compact support gives the exact exterior Green matching at the actual right endpoint.
Use: fixes the constant of the inner profile's conserved energy.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the true right half-convolution integral is zero at 2*A because the
rescaled compact source vanishes strictly to its right. The actual
convolution and its slope are the sum and difference of the same halves. -/
theorem Profile.potential_boundary {a b T : ℝ} (P : Profile a b T) :
    potentialSlope P.density.toDensity P.radius = -2*potential P.density.toDensity P.radius := by
  -- Transfer both the true integral potential and its derivative to the actual compact representative.
  let q := compactDensity P.density a b P.mu P.radius P.representative
  have hp : potential P.density.toDensity=potential q := potential_congr P.representative
  have hs : potentialSlope P.density.toDensity=potentialSlope q := by
    funext x
    have hh := potential_hasDerivAt P.density.toDensity x
    rw [hp] at hh
    exact hh.unique (potential_hasDerivAt q x)
  rw [hs,hp]
  have hR : rightGreen (source q) (2*P.radius)=0 := by
    unfold rightGreen
    have hi : (∫ t in Ioi (2*P.radius),exp (-t)*source q t)=0 := by
      apply setIntegral_eq_zero_of_forall_eq_zero
      intro t ht
      have hnot : t/2∉Icc (-P.radius) P.radius := fun h => (by have ht' : 2*P.radius<t := ht; linarith : P.radius<t/2).not_ge h.2
      change exp (-t)*compactValue P.density a b P.mu P.radius (t/2)=0
      rw [compactValue,indicator_of_notMem hnot,mul_zero]
    rw [hi,mul_zero]
  change convolutionSlope (source q) (2*P.radius)= -2*((1/2:ℝ)*H1.rep (convolution (source q)) (2*P.radius))
  rw [convolutionSlope,convolution_halves (source_integrable q),hR]
  ring

/-- The actual dimensionless slope has the exact printed value at the free boundary.
Use: proves the zero value of the inner conserved first integral.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: combine actual compact Green matching with the actual switching equation c(A)=2*b. -/
theorem Profile.D_boundary {a b T : ℝ} (P : Profile a b T) (hb : 0<b) : P.D P.radius= -(4+a) := by
  have hbound := P.boundary
  unfold coefficient at hbound
  unfold Profile.D
  rw [P.potential_boundary]
  field_simp
  nlinarith

/-- The genuine centered dimensionless Green slope vanishes at the turning point.
Use: identifies the peak with the actual inverse turning level psi^{-1}(y).
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: differentiate the even original coefficient after reflection; uniqueness of its actual derivative forces it to equal its negative. -/
theorem Profile.D_zero {a b T : ℝ} (P : Profile a b T) : P.D 0=0 := by
  -- Reflection differentiates the same even coefficient at its actual center.
  have heven : (fun x => P.C (-x))=P.C := by
    funext x
    unfold Profile.C coefficient
    rw [potential_even P.density.toDensity P.radial]
  have hbase : HasDerivAt P.C (P.D 0) (-id (0:ℝ)) := by simpa only [id_eq,neg_zero] using P.C_hasDerivAt 0
  have hh := hbase.comp 0 ((hasDerivAt_id (0:ℝ)).neg)
  change HasDerivAt (fun t => P.C (-t)) (P.D 0 * -1) 0 at hh
  rw [heven] at hh
  have h := hh.unique (P.C_hasDerivAt 0)
  linarith

/-- The actual dimensionless slope is strictly negative at every positive radius.
Use: selects the negative square-root branch in the genuine spatial Jacobian.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: the original nonzero radial Green potential has strictly negative derivative, and its normal multiplier is positive. -/
theorem Profile.D_neg {a b T : ℝ} (P : Profile a b T) (hb : 0<b) {x : ℝ} (hx : 0<x) : P.D x<0 :=
  mul_neg_of_pos_of_neg (by exact div_pos (mul_pos (by norm_num) P.mu_pos) hb)
    (potentialSlope_radial_neg P.density.toDensity P.mass_pos P.radial hx)

end
end jacobi.RootMass
