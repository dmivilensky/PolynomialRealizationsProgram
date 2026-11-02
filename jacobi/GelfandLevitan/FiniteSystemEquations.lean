import jacobi.GelfandLevitan.FiniteGramGreen

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The actual original finite coefficient equation is differentiated once
and twice using its already proved genuine spatial derivatives.
Uniqueness of derivatives on the original nondegenerate physical strip
identifies the resulting original finite differential equations.
These are the actual equations needed in the finite Darboux cancellation.
Use: entrywise original reference derivatives and bounded-operator evaluation share the same original finite operator topology.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope

/-- The actual finite coefficient operator norm structure, cached for the genuine second derivative calculus.
Use: entrywise original reference derivatives and bounded-operator evaluation share the same original finite operator topology.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance (N : ℕ) : NormedAddCommGroup ((FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ)) := inferInstance

/-- The genuine second spatial derivative formula for the original finite Gram coefficient operator.
Use: finiteFeatureSystemSlope_hasDerivWithinAt identifies this same operator with the actual original derivative of B'.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSystemAcceleration (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    (FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ) :=
  ∑ i : FeatureIndex N,∑ j : FeatureIndex N,
    (finiteFeatureWeight a ha i*(realSlope a (finiteFeatureEnergy a ha i) t*realSolution a (finiteFeatureEnergy a ha j) t+
      realSolution a (finiteFeatureEnergy a ha i) t*realSlope a (finiteFeatureEnergy a ha j) t)) • featureMatrixUnit i j

/-- The genuine second spatial derivative formula for the actual original finite source vector.
Use: finiteFeatureSourceSlope_hasDerivWithinAt supplies the original reference ODE term in the twice differentiated true finite coefficient equation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSourceAcceleration (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : FeatureIndex N→ℝ :=
  fun i => finiteFeatureWeight a ha i*((potential a t-finiteFeatureEnergy a ha i)*realSolution a (finiteFeatureEnergy a ha i) t)

/-- The actual original finite Gram system slope has its genuine displayed second-derivative operator formula on the physical positive strip.
Use: finiteFeatureCoefficients_equation_second differentiates the actual finite inverse-system equation twice in the original norm.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: differentiate the actual original selected-solution product in each original finite matrix entry, multiply by its fixed original signed weight and coordinate matrix unit, and sum the genuine finite derivatives. -/
theorem finiteFeatureSystemSlope_hasDerivWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) :
    HasDerivWithinAt (finiteFeatureSystemSlope a ha N) (finiteFeatureSystemAcceleration a ha N t) (Icc d (1/2)) t := by
  -- All derivatives belong to the actual original selected solutions; the matrix calculation is a true finite operator sum.
  have hsol (i : FeatureIndex N) := (realSolution_hasDerivAt a (finiteFeatureEnergy a ha i)
    (show t∈Ioo (0:ℝ) 1 from ⟨hd.trans_le ht.1,by linarith [ht.2]⟩)).hasDerivWithinAt (s := Icc d (1/2))
  exact HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
      (((hsol i).mul (hsol j)).const_mul (finiteFeatureWeight a ha i)).smul_const (featureMatrixUnit i j)))

/-- The actual original finite selected-slope source has its genuine second derivative from the independently proved original reference ODE.
Use: the second differentiated finite coefficient equation retains exactly the original potential and feature energies.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the actual reference selected-slope acceleration is (q-E)*f at every genuine original feature energy; fixed weights and finite product-space differentiation give the original vector derivative. -/
theorem finiteFeatureSourceSlope_hasDerivWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) :
    HasDerivWithinAt (finiteFeatureSourceSlope a ha N) (finiteFeatureSourceAcceleration a ha N t) (Icc d (1/2)) t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  exact ((realSlope_hasDerivAt_equation ha (finiteFeatureEnergy a ha i)
    ⟨hd.trans_le ht.1,by linarith [ht.2]⟩).const_mul (finiteFeatureWeight a ha i)).hasDerivWithinAt

/-- The actual original finite coefficients satisfy the genuine once-differentiated original finite Gram-system equation.
Use: finiteFeatureCoefficients_equation_second differentiates this same actual original identity once more in the finite Darboux calculation.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: bounded-operator evaluation differentiates the actual original product B*a. Its independently proved original inverse equation identifies that same function with -C*h. Their derivatives are unique on the true nondegenerate closed physical strip. -/
theorem finiteFeatureCoefficients_equation_first {a d t : ℝ} (ha : -1<a) (hd : 0<d) (hds : d<(1/2:ℝ)) (N : ℕ)
    (ht : t∈Icc d (1/2)) (hu : ∀ x : ℝ,IsUnit (finiteFeatureSystem a ha N x)) :
    finiteFeatureSystemSlope a ha N t (finiteFeatureCoefficients a ha N t)+
      finiteFeatureSystem a ha N t (finiteFeatureCoefficientsSlope a ha N t)= -finiteFeatureSourceSlope a ha N t := by
  -- The actual original coefficient equation is used as a function identity, so derivative equality follows from genuine uniqueness rather than formal differentiation alone.
  have hL := (finiteFeatureSystem_hasDerivWithinAt ha hd N ht).clm_apply
    (finiteFeatureCoefficients_hasDerivWithinAt ha hd N ht (hu t))
  have hR := (finiteFeatureSource_hasDerivWithinAt ha hd N ht).neg
  have hEq : HasDerivWithinAt (fun x => -finiteFeatureSource a ha N x) _ (Icc d (1/2)) t :=
    hL.congr (fun x _ => (finiteFeatureCoefficients_equation a ha N x (hu x)).symm)
      (finiteFeatureCoefficients_equation a ha N t (hu t)).symm
  exact (hEq.derivWithin ((uniqueDiffOn_Icc hds) t ht)).symm.trans (hR.derivWithin ((uniqueDiffOn_Icc hds) t ht))

/-- The actual original finite coefficients satisfy the genuine twice-differentiated finite Gram-system equation for every actual second derivative.
Use: combines with the actual original Gram Green commutator and finite diagonal derivative to cancel the finite Darboux residual.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: differentiate the independently proved original first coefficient equation using the actual original matrix, coefficient and supplied genuine second derivatives. Identify the same function with the independently differentiated original selected-slope source. Uniqueness on the original nondegenerate physical strip gives the actual second equation. -/
theorem finiteFeatureCoefficients_equation_second {a d t : ℝ} (ha : -1<a) (hd : 0<d) (hds : d<(1/2:ℝ)) (N : ℕ)
    (ht : t∈Icc d (1/2)) (hu : ∀ x : ℝ,IsUnit (finiteFeatureSystem a ha N x))
    (a2 : FeatureIndex N→ℝ) (ha2 : HasDerivWithinAt (finiteFeatureCoefficientsSlope a ha N) a2 (Icc d (1/2)) t) :
    (finiteFeatureSystemAcceleration a ha N t (finiteFeatureCoefficients a ha N t)+
      finiteFeatureSystemSlope a ha N t (finiteFeatureCoefficientsSlope a ha N t))+
      (finiteFeatureSystemSlope a ha N t (finiteFeatureCoefficientsSlope a ha N t)+finiteFeatureSystem a ha N t a2)=
        -finiteFeatureSourceAcceleration a ha N t := by
  -- Both derivatives of the original product identity use the same genuine original finite coefficient functions.
  have hα := finiteFeatureCoefficients_hasDerivWithinAt ha hd N ht (hu t)
  have hL := ((finiteFeatureSystemSlope_hasDerivWithinAt ha hd N ht).clm_apply hα).add
    ((finiteFeatureSystem_hasDerivWithinAt ha hd N ht).clm_apply ha2)
  have hR := (finiteFeatureSourceSlope_hasDerivWithinAt ha hd N ht).neg
  have hEq : HasDerivWithinAt (fun x => -finiteFeatureSourceSlope a ha N x) _ (Icc d (1/2)) t :=
    hL.congr (fun x hx => (finiteFeatureCoefficients_equation_first ha hd hds N hx hu).symm)
      (finiteFeatureCoefficients_equation_first ha hd hds N ht hu).symm
  exact (hEq.derivWithin ((uniqueDiffOn_Icc hds) t ht)).symm.trans (hR.derivWithin ((uniqueDiffOn_Icc hds) t ht))

end
end jacobi.GelfandLevitan
