import jacobi.Keller.StateIntegrals
import jacobi.Variational.ExtendedEnergy

/-!
Article: jacobi, Section 3.2 (sharp comparison at U).
The actual radial minimizer, its genuine normalized ground state and the
proved Jacobian determine its unique shape and exact energy. This closes
both mass regimes, including their common boundary and actual attainment.
The edge-spectrum statement uses the original variational admissible set.
Source: Keller's one-dimensional inequality (Keller; Lieb--Thirring) and
the article's mass-constrained refinement, proved here from the actual KKT system.
Use: the theorem evaluates this actual infimum rather than a profile-restricted proxy.
-/
namespace jacobi.Keller
noncomputable section
open MeasureTheory Real Set Filter jacobi.Variational
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The genuine mass-constrained Keller variational infimum.
Use: the theorem evaluates this actual infimum rather than a profile-restricted proxy.
Article: jacobi, Theorem D.6.
-/
def Kel (ell M : ℝ) : ℝ≥0∞ := relaxedInfimum {Observation.top} M (fun _ => ell)

/-- The exact energy in the free-mass Keller regime.
Use: states the first branch of the complete attained calibration.
Article: jacobi, Theorem D.6.
-/
def freeValue (ell : ℝ) : ℝ := (Real.pi/4)*(3*ell/2)^(3/2:ℝ)

/-- The exact energy at a finite admissible constrained Keller shape.
Use: the unique mass equation selects the second branch of the calibration.
Article: jacobi, Theorem D.6.
-/
def constrainedValue (ell c : ℝ) : ℝ := 2*(3*ell/2)^(3/2:ℝ)*c*j 3 c

/-- The printed energy expression agrees with the free Keller value at the transition shape.
Use: includes the equality mass threshold in the free branch with its exact constant.
Article: jacobi, Theorem D.6.
Proof: the true transition primitive gives j_3(1)=Real.pi/8. -/
theorem constrainedValue_one (ell : ℝ) : constrainedValue ell 1=freeValue ell := by
  have hj : j 3 1=Real.pi/8 := by
    have hh := j_rescale 3 zero_lt_one
    simpa only [sqrt_one,one_mul,inv_one,J_one_values.2.2] using hh
  rw [constrainedValue,hj,freeValue]
  ring

/-- Any actual normalized minimizing profile in the free-mass regime has shape exactly one.
Use: determines its energy and excludes an unproved choice of profile branch.
Article: jacobi, Theorem D.6.
Proof: c>1 would saturate mass, but its genuine mass curve is strictly below one half. -/
theorem Profile.shape_free {m : Density} {ell M : ℝ} (p : Profile m ell M)
    (hell : 0<ell) (_hmM : m.mass≤M) (hregime : 3*ell/2≤M) : p.shape=1 := by
  have hc := p.shape_ge_one hell
  by_contra hn
  have hc1 : 1<p.shape := lt_of_le_of_ne hc (Ne.symm hn)
  have hm := p.mass_quadrature hell
  rw [p.mass_saturated hc1] at hm
  have hb := (massCurve_bounds hc1).2
  nlinarith

/-- Any actual normalized minimizing profile in the strict mass regime has shape greater than one.
Use: its complementarity and exact mass quadrature produce the original defining equation.
Article: jacobi, Theorem D.6.
Proof: shape one has exact mass 3*ell/2, contradicting the actual mass bound. -/
theorem Profile.shape_constrained {m : Density} {ell M : ℝ} (p : Profile m ell M)
    (hell : 0<ell) (hmM : m.mass≤M) (hregime : M<3*ell/2) : 1<p.shape := by
  apply lt_of_le_of_ne (p.shape_ge_one hell)
  intro hz
  have hm := p.mass_quadrature hell
  rw [← hz,massCurve_one] at hm
  nlinarith

/-- The complete free-mass Keller branch, including an actual radial attainer and its true ground profile.
Use: proves the first line of the source theorem, including the mass-threshold boundary.
Article: jacobi, Theorem D.6.
Proof: the direct method gives a genuine radial minimizer. Its proved KKT
profile must have shape one by the mass-curve comparison. Its actual
Jacobian energy and the exact transition primitive give the stated infimum. -/
theorem free_calibration {ell M : ℝ} (hell : 0<ell) (hsub : ell<M)
    (hregime : 3*ell/2≤M) :
    Kel ell M=ENNReal.ofReal (freeValue ell) ∧
      ∃ m : Density,SymmetricDecreasing m.value ∧ m.mass=3*ell/2 ∧ observe m .top=ell ∧
        m.energy=freeValue ell ∧ m.cost=Kel ell M ∧ ∃ p : Profile m ell M,p.shape=1 := by
  -- Existence and every optimizer premise come from the already proved genuine variational theorem.
  obtain ⟨m,hs,hm,hmM,hG,hmin⟩ := top_minimizer_exists (hell.trans hsub) hell hsub
  obtain ⟨_hactive,⟨p⟩⟩ := optimizer_profile hell m hm hs hmM hG.ge hmin
  have hc : p.shape=1 := p.shape_free hell hmM hregime
  have hmass := p.mass_quadrature hell
  rw [hc,massCurve_one] at hmass
  have hE : m.energy=freeValue ell := by
    rw [← constrainedValue_one]
    simpa only [constrainedValue,hc] using p.energy_quadrature hell
  have hcost : m.cost=Kel ell M := hmin
  exact ⟨by rw [← hcost]; exact congrArg ENNReal.ofReal hE,
    m,hs,by nlinarith [hmass],hG,hE,hcost,p,hc⟩

/-- The complete strict mass-constrained Keller branch with unique parameter and an actual radial attainer.
Use: proves the second line of the source theorem without numerical roots or assumed optimizer certificates.
Article: jacobi, Theorem D.6.
Proof: the actual radial minimizer has shape c>1, hence saturates its mass.
Its proved actual quadratures give the exact root equation and energy.
The proved global strict mass monotonicity makes that parameter unique. -/
theorem constrained_calibration {ell M : ℝ} (hell : 0<ell) (hsub : ell<M)
    (hregime : M<3*ell/2) :
    ∃ c : ℝ,1<c ∧ 3*ell*massCurve c=M ∧
      (∀ d : ℝ,1<d → 3*ell*massCurve d=M → d=c) ∧
      Kel ell M=ENNReal.ofReal (constrainedValue ell c) ∧
      ∃ m : Density,SymmetricDecreasing m.value ∧ m.mass=M ∧ observe m .top=ell ∧
        m.energy=constrainedValue ell c ∧ m.cost=Kel ell M ∧ ∃ p : Profile m ell M,p.shape=c := by
  -- The unique root is the genuine optimizer's own finite shape.
  obtain ⟨m,hs,hm,hmM,hG,hmin⟩ := top_minimizer_exists (hell.trans hsub) hell hsub
  obtain ⟨_hactive,⟨p⟩⟩ := optimizer_profile hell m hm hs hmM hG.ge hmin
  have hc := p.shape_constrained hell hmM hregime
  have hmass := p.mass_saturated hc
  have hroot : 3*ell*massCurve p.shape=M := (p.mass_quadrature hell).symm.trans hmass
  have hE : m.energy=constrainedValue ell p.shape := p.energy_quadrature hell
  refine ⟨p.shape,hc,hroot,?_,?_,m,hs,hmass,hG,hE,hmin,p,rfl⟩
  · intro d hd hde
    apply massCurve_strictAnti.injOn hd.le hc.le
    nlinarith [hde,hroot]
  · rw [Kel,← hmin]
    exact congrArg ENNReal.ofReal hE

/-- Every actual edge-spectrum top relaxation is exactly its mass-constrained Keller problem.
Use: transfers both proved complete calibration branches to the source's original edge-spectrum notation.
Article: jacobi, Theorem D.6.
Proof: the singleton top constraint reads only the first eigenvalue threshold; its admissible sets coincide. -/
theorem edge_problem (Λ : EdgeSpectrum) :
    relaxedInfimum {Observation.top} Λ.mass (threshold Λ)=Kel (Λ.value 0) Λ.mass := by
  unfold relaxedInfimum Kel
  congr 1
  ext m
  simp [threshold]

/-- The genuine Keller infimum is unchanged when all nonnegative L1 competitors of possibly infinite energy are included.
Use: both exact calibration branches apply to the full variational domain printed in the article.
Article: jacobi, Theorem D.6.
Proof: specialize the proved equality of the unrestricted and finite-energy moment infima. -/
theorem unrestricted_problem (ell M : ℝ) :
    extendedMomentInfimum {Observation.top} M (fun _ => ell)=Kel ell M :=
  extendedMomentInfimum_eq {Observation.top} M (fun _ => ell)

/-- The sharp free-branch Keller inequality holds for every admissible nonnegative L1 source, with no finite-energy premise.
Use: the proved calibrated constant bounds the actual extended energy of arbitrary competitors.
Article: jacobi, Theorem D.6.
Proof: the exact attained calibration evaluates the infimum; the unrestricted
variational lower bound applies to the same source, including infinite energy. -/
theorem free_lower_bound {ell M : ℝ} (hell : 0<ell) (hsub : ell<M) (hregime : 3*ell/2≤M)
    (m : L1Source) (hm : m.mass≤M) (hT : ell≤observe m .top) :
    ENNReal.ofReal (freeValue ell)≤m.energyCost := by
  rw [← (free_calibration hell hsub hregime).1]
  apply relaxed_le_extended_energy {Observation.top} M (fun _ => ell) m hm
  intro i hi
  have hh : i=Observation.top := mem_singleton_iff.mp hi
  subst i
  exact hT

/-- The actual edge-spectrum free Keller branch has the exact printed value, without additional feasibility premises.
Use: states the first branch directly for the article's original edge-spectrum relaxation.
Article: jacobi, Theorem D.6.
Proof: the actual edge spectrum proves positivity and strict subcriticality;
its original admissible set is the proved Keller problem. -/
theorem edge_free_value (Λ : EdgeSpectrum) (hregime : 3*Λ.value 0/2≤Λ.mass) :
    relaxedInfimum {Observation.top} Λ.mass (threshold Λ)=ENNReal.ofReal (freeValue (Λ.value 0)) := by
  rw [edge_problem]
  exact (free_calibration (Λ.positive 0) Λ.top_lt_mass hregime).1

/-- The actual edge-spectrum constrained Keller branch has its unique printed mass parameter and exact value.
Use: states the second branch directly on the original edge-spectrum relaxation.
Article: jacobi, Theorem D.6.
Proof: apply the complete actual constrained calibration with the source
edge's proved positive top eigenvalue and strict top-to-mass inequality. -/
theorem edge_constrained_value (Λ : EdgeSpectrum) (hregime : Λ.mass<3*Λ.value 0/2) :
    ∃ c : ℝ,1<c ∧ 3*Λ.value 0*massCurve c=Λ.mass ∧
      (∀ d : ℝ,1<d → 3*Λ.value 0*massCurve d=Λ.mass → d=c) ∧
      relaxedInfimum {Observation.top} Λ.mass (threshold Λ)=
        ENNReal.ofReal (constrainedValue (Λ.value 0) c) := by
  obtain ⟨c,hc,hr,hu,hvalue,_hm⟩ := constrained_calibration (Λ.positive 0) Λ.top_lt_mass hregime
  exact ⟨c,hc,hr,hu,by rw [edge_problem,hvalue]⟩

/-- The Jacobi mass and leading-zero formulas give exactly the source's algebraic Keller branch criterion.
Use: stage 8 substitutes its genuinely proved Bessel edge data into this unconditional scalar equivalence.
Article: jacobi, Theorem D.6.
Proof: multiply M<3*ell/2 by the positive denominators in the printed
M=1/(2*(alpha+1)) and ell=2/z² formulas. No Bessel zero fact is assumed here. -/
theorem jacobi_branch_criterion {alpha z : ℝ} (ha : -1<alpha) (hz : 0<z) :
    (1/(2*(alpha+1)):ℝ)<3*(2/z^2)/2 ↔ z^2<6*(alpha+1) := by
  -- Positive denominators preserve the exact branch inequality under clearing fractions.
  have hA : 0<2*(alpha+1) := by linarith
  have hZ : 0<z^2 := sq_pos_of_pos hz
  rw [div_lt_iff₀ hA]
  constructor <;> intro hh
  · have hh' := (lt_div_iff₀ hZ).mp (show (1:ℝ)<(3*(alpha+1))*2/z^2 by convert hh using 1; ring)
    nlinarith
  · have hh' : (1:ℝ)<(3*(alpha+1))*2/z^2 := (lt_div_iff₀ hZ).mpr (by nlinarith)
    convert hh' using 1
    ring

end
end jacobi.Keller
