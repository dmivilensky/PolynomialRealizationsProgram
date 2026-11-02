import jacobi.RootMass.CompactProfile

/-!
Article: jacobi, Theorem D.8.
A profile packages only conclusions already constructed from the literal
minimization problem. Existence requires just the printed parameter range,
b>0 and T>0. In particular compact support, global scalar minimality and
activity are proved outputs, never additional admissibility hypotheses.
Source: actual inner attainment, actual normalized needles and scalar rigidity.
Use: the first-integral and quadrature derivation retains the same actual minimizer throughout.
-/
namespace jacobi.RootMass
noncomputable section
open Real Set MeasureTheory Filter jacobi.Variational jacobi.Young
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- An actual attained inner optimizer with its proved switching geometry.
Use: the first-integral and quadrature derivation retains the same actual minimizer throughout.
Article: jacobi, Theorem D.8.
-/
structure Profile (a b T : ℝ) where
  /-- The actual finite-energy, finite-root density attaining the inner infimum. -/
  density : RootDensity
  /-- The centered decreasing representative is furnished by actual rearrangement. -/
  radial : SymmetricDecreasing density.value
  /-- The positive threshold forces a genuinely nonzero density. -/
  mass_pos : 0<density.mass
  /-- Actual attainment, rather than an assumed Euler profile. -/
  optimal : density.cost a b=inner a b T
  /-- The actual constraint is saturated by amplitude variation. -/
  active : observe density.toDensity .second=T
  /-- The normal multiplier is constructed by actual normalized needles. -/
  mu : ℝ
  /-- Positivity is deduced from global scalar minimality. -/
  mu_pos : 0<mu
  /-- The multiplier retains its actual amplitude-derivative formula for the active moment. -/
  normal : mu=normalMultiplier density a b T
  /-- The unique actual switching radius. -/
  radius : ℝ
  /-- The positive core is nonempty. -/
  radius_pos : 0<radius
  /-- The actual Green coefficient equals the switching value at this radius. -/
  boundary : coefficient density a b mu radius=2*b
  /-- The exact centered positive superlevel set of the actual coefficient. -/
  core : ∀ x : ℝ,2*b<coefficient density a b mu x ↔ |x|<radius
  /-- The actual coefficient is below the switching value in the exterior. -/
  exterior : ∀ x : ℝ,radius< |x| → coefficient density a b mu x<2*b
  /-- The original optimizing density equals the proved compact formula modulo null sets. -/
  representative : density.value=ᵐ[volume] compactValue density a b mu radius

/-- Every actual radial inner minimizer has the complete proved compact profile structure.
Use: the source profile and quadrature conclusions apply to every minimizer, not only the existence witness.
Article: jacobi, Theorem D.8.
Proof: normalized needles construct the actual positive multiplier. Strict
radial Green geometry constructs its finite boundary, and the unique scalar
minimum identifies the original density almost everywhere. -/
theorem profile_of_minimizer {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T)
    (m : RootDensity) (hrad : SymmetricDecreasing m.value) (hG : T≤observe m.toDensity .second)
    (hmin : m.cost a b=inner a b T) : ∃ P : Profile a b T,P.density=m := by
  -- Every profile field is obtained from this very minimizer's actual data.
  have hm := mass_pos_of_observe_pos m.toDensity .second (hT.trans_le hG)
  obtain ⟨mu,hmu,hnormal,hP⟩ := pointwise_minimum ha hb hT m hmin hG
  obtain ⟨A,hA,hbound,hcore,hout⟩ := coefficient_boundary ha hb m hm hrad hmu hP
  exact ⟨⟨m,hrad,hm,hmin,inner_constraint_active ha hb hT m hG hmin,
    mu,hmu,hnormal,A,hA,hbound,hcore,hout,compactValue_ae hb m hcore hout hP⟩,rfl⟩

/-- Every admissible parameter triple constructs an actual compact optimizer of the inner problem.
Use: discharges every optimizer premise in the final explicit root-mass calibration.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: actual radial attainment and the proved characterization of every
radial minimizer give the complete compact profile. -/
theorem profile_exists {a b T : ℝ} (ha : -2*sqrt 3<a) (hb : 0<b) (hT : 0<T) :
    Nonempty (Profile a b T) := by
  obtain ⟨m,hrad,_hm,hG,hmin⟩ := inner_minimizer_exists ha hb hT
  obtain ⟨P,_hP⟩ := profile_of_minimizer ha hb hT m hrad hG hmin
  exact ⟨P⟩

/-- The actual optimizer's dimensionless positive branch.
Use: its true spatial first integral gives the printed state quadratures.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def Profile.state {a b T : ℝ} (P : Profile a b T) (x : ℝ) : ℝ := branch P.density a b P.mu x/b

/-- The dimensionless original Green coefficient of the actual optimizer.
Use: provides the classical core ODE and its exact exterior matching.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def Profile.C {a b T : ℝ} (P : Profile a b T) (x : ℝ) : ℝ := coefficient P.density a b P.mu x/b

/-- The actual first derivative of the dimensionless Green coefficient.
Use: retains classical C1 matching across the genuine density jump.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def Profile.D {a b T : ℝ} (P : Profile a b T) (x : ℝ) : ℝ := (2*P.mu/b)*potentialSlope P.density.toDensity x

/-- The actual positive first-integral parameter of the optimizer.
Use: its inverse selects the unique nonsingular quadrature parameter.
Article: jacobi, Appendix D.5 (compact root-mass profile).
-/
def Profile.kappa {a b T : ℝ} (P : Profile a b T) : ℝ := 8*P.mu*b

/-- The actual Green coefficient has its declared classical derivative everywhere, including the jump boundary.
Use: the first integral uses the original potential's true C1 derivative.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: divide the actual Green derivative by b and simplify the coefficient. -/
theorem Profile.C_hasDerivAt {a b T : ℝ} (P : Profile a b T) (x : ℝ) :
    HasDerivAt P.C (P.D x) x := by
  convert (((potential_hasDerivAt P.density.toDensity x).const_mul (2*P.mu)).const_add (-a*b/2)).div_const b using 1
  · rfl
  · unfold Profile.D
    ring

/-- The actual core Green slope satisfies its genuine classical semilinear equation.
Use: differentiating the first integral has no unproved ODE premise.
Article: jacobi, Appendix D.5 (compact root-mass profile).
Proof: use the actual compact representative's local Green equation and
rescale its source and its coefficient by the same b. -/
theorem Profile.D_hasDerivAt {a b T : ℝ} (P : Profile a b T) (hb : 0<b)
    {x : ℝ} (hx : x∈Ioo (-P.radius) P.radius) :
    HasDerivAt P.D (4*P.C x+2*a-P.kappa*P.state x^2) x := by
  convert (compactPotential_classical P.density a b P.mu P.radius P.representative hx).const_mul (2*P.mu/b) using 1
  · rfl
  · unfold Profile.C Profile.kappa Profile.state coefficient
    field_simp
    ring

end
end jacobi.RootMass
