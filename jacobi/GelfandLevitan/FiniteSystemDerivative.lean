import jacobi.GelfandLevitan.FiniteCoefficients
import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
The original finite Gram system, its genuine inverse and original
kernel coefficients have their actual first spatial derivatives.
Finite coordinate matrix units transfer the proved genuine Gram FTC
to the true operator norm. Inversion is differentiated only at actual
units supplied by the proved original finite-system invertibility.
Use: the actual inverse derivative and the coordinate FTC use the same genuine operator topology and real module.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set Filter jacobi.Reference
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution realSlope

/-- The existing original finite coefficient operator norm structure, cached for derivative inference.
Use: the actual inverse derivative and the coordinate FTC use the same genuine operator topology and real module.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
local instance (N : ℕ) : NormedAddCommGroup ((FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ)) := inferInstance

/-- An actual finite coordinate matrix unit as a bounded operator on the original finite coefficient space.
Use: finiteFeatureSystem_operator_formula writes the genuine Gram system as a finite operator sum, so its original entrywise FTC gives a derivative in the actual operator norm.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: standard coordinate matrix units. -/
def featureMatrixUnit {N : ℕ} (i j : FeatureIndex N) :
    (FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ) :=
  ContinuousLinearMap.pi (fun k => if k=i then ContinuousLinearMap.proj j else 0)

/-- The genuine finite coordinate matrix unit has precisely its standard original coordinate action.
Use: finiteFeatureSystem_operator_formula identifies the actual Gram system with its finite operator expansion before differentiating it.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: the standard coordinate matrix unit E_ij.
Proof: split the selected output-coordinate equality and evaluate the actual original projection or zero map. -/
theorem featureMatrixUnit_apply {N : ℕ} (i j : FeatureIndex N) (y : FeatureIndex N→ℝ) (k : FeatureIndex N) :
    featureMatrixUnit i j y k=if k=i then y j else 0 := by
  by_cases hki : k=i
  · simp [featureMatrixUnit,hki]
  · simp [featureMatrixUnit,hki]

/-- The original finite-system derivative from its genuine original Gram-entry derivatives.
Use: finiteFeatureSystem_hasDerivWithinAt proves this is the actual derivative of the original coefficient operator in its genuine norm.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSystemSlope (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    (FeatureIndex N→ℝ) →L[ℝ] (FeatureIndex N→ℝ) :=
  ∑ i : FeatureIndex N,∑ j : FeatureIndex N,
    (finiteFeatureWeight a ha i*(realSolution a (finiteFeatureEnergy a ha i) t*
      realSolution a (finiteFeatureEnergy a ha j) t)) • featureMatrixUnit i j

/-- The true original source-vector derivative at the same actual finite spectral feature energies.
Use: finiteFeatureSource_hasDerivWithinAt differentiates the genuine right-hand side in the actual finite inverse-system coefficient formula.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureSourceSlope (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : FeatureIndex N→ℝ :=
  fun i => finiteFeatureWeight a ha i*realSlope a (finiteFeatureEnergy a ha i) t

/-- The actual original finite coefficient operator is exactly its genuine original Gram-entry expansion in finite coordinate matrix units.
Use: the actual operator-norm derivative follows directly from the independently proved original Gram-entry FTC.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: evaluate on an arbitrary original coefficient vector and coordinate. The true matrix unit selects exactly its original row; the actual finite sums are the already proved original I+C*X action. -/
theorem finiteFeatureSystem_operator_formula (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) :
    finiteFeatureSystem a ha N t=ContinuousLinearMap.id ℝ (FeatureIndex N→ℝ)+
      ∑ i : FeatureIndex N,∑ j : FeatureIndex N,
        (finiteFeatureWeight a ha i*finiteFeatureGram a ha N t i j) • featureMatrixUnit i j := by
  apply ContinuousLinearMap.ext
  intro y
  funext k
  rw [finiteFeatureSystem_apply]
  simp [featureMatrixUnit_apply,Finset.mul_sum,mul_assoc]

/-- The actual original finite Gram coefficient operator has its genuine norm derivative on every positive physical strip.
Use: finiteFeatureSystemInverse_hasDerivWithinAt differentiates its actual original inverse, and the finite transformation kernel coefficients are then genuinely differentiated.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: each genuine original Gram entry has the independently proved original endpoint FTC derivative. Multiply by its actual fixed signed weight and coordinate matrix unit, then take the true finite operator sum. The exact original matrix-unit expansion identifies its derivative with that of the genuine finite system. -/
theorem finiteFeatureSystem_hasDerivWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) :
    HasDerivWithinAt (finiteFeatureSystem a ha N) (finiteFeatureSystemSlope a ha N t) (Icc d (1/2)) t := by
  -- The actual coordinate FTC is lifted to the actual operator norm by finite sums of constant original matrix units.
  have hsum := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun i _ =>
    HasDerivWithinAt.fun_sum (u := Finset.univ) (fun j _ =>
      ((finiteFeatureGram_hasDerivWithinAt ha hd N ht i j).const_mul (finiteFeatureWeight a ha i)).smul_const (featureMatrixUnit i j)))
  have h := hsum.const_add (ContinuousLinearMap.id ℝ (FeatureIndex N→ℝ))
  change HasDerivWithinAt _ (finiteFeatureSystemSlope a ha N t) _ _ at h
  exact h.congr (fun x _ => finiteFeatureSystem_operator_formula a ha N x)
    (finiteFeatureSystem_operator_formula a ha N t)

/-- The actual original finite reference source vector has its genuine selected-slope derivative in the true finite-dimensional norm.
Use: combines with the independently proved actual inverse derivative to differentiate the same original finite kernel coefficients.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: each original real selected solution has its independently proved genuine spatial derivative at the actual original energy; multiply by its fixed original weight and use community finite product-space differentiation. -/
theorem finiteFeatureSource_hasDerivWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) :
    HasDerivWithinAt (finiteFeatureSource a ha N) (finiteFeatureSourceSlope a ha N t) (Icc d (1/2)) t := by
  apply hasDerivWithinAt_pi.mpr
  intro i
  exact ((realSolution_hasDerivAt a (finiteFeatureEnergy a ha i)
    ⟨hd.trans_le ht.1,by linarith [ht.2]⟩).const_mul (finiteFeatureWeight a ha i)).hasDerivWithinAt

/-- The genuine inverse of the actual original finite coefficient system has the true norm derivative -B^-1*B'*B^-1 at every original physical point where the independently proved system is a unit.
Use: the finite kernel's actual original inverse-system coefficients can be differentiated, including their midpoint one-sided values, with no derivative assumption on the inverse.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Source: mathlib's derivative of inversion in a real Banach algebra.
Proof: compose the genuine original finite-system norm derivative with the community derivative of inversion at its actual proved unit. The unit inverse is the same original Ring.inverse used in finiteFeatureCoefficients. -/
theorem finiteFeatureSystemInverse_hasDerivWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) (hu : IsUnit (finiteFeatureSystem a ha N t)) :
    HasDerivWithinAt (fun x => Ring.inverse (finiteFeatureSystem a ha N x))
      (-(Ring.inverse (finiteFeatureSystem a ha N t)*finiteFeatureSystemSlope a ha N t*
        Ring.inverse (finiteFeatureSystem a ha N t))) (Icc d (1/2)) t := by
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) hu.unit
  rw [IsUnit.unit_spec] at hi
  have h := hi.comp_hasDerivWithinAt t (finiteFeatureSystem_hasDerivWithinAt ha hd N ht)
  change HasDerivWithinAt (fun x => Ring.inverse (finiteFeatureSystem a ha N x)) _ _ _ at h
  simpa only [neg_apply,ContinuousLinearMap.mulLeftRight_apply,
    ← Ring.inverse_unit hu.unit,IsUnit.unit_spec] using h

/-- The genuine derivative formula for the original finite inverse-system kernel coefficients.
Use: finiteFeatureCoefficients_hasDerivWithinAt proves this expression is the actual original spatial derivative, which differentiates the actual finite K feature formula.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
-/
def finiteFeatureCoefficientsSlope (a : ℝ) (ha : -1<a) (N : ℕ) (t : ℝ) : FeatureIndex N→ℝ :=
  let Q := Ring.inverse (finiteFeatureSystem a ha N t)
  (Q*finiteFeatureSystemSlope a ha N t*Q) (finiteFeatureSource a ha N t)-Q (finiteFeatureSourceSlope a ha N t)

/-- The actual original finite kernel coefficients have their genuine displayed spatial derivative on the physical positive strip, including its midpoint one-sided interpretation.
Use: the original finite transformation kernel feature formula can now be differentiated in its actual first physical coordinate, without assuming any kernel or inverse regularity.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: differentiate the independently proved actual inverse and original source vector, apply the genuine bounded-operator evaluation derivative and retain the original overall minus sign. The elementary additive identity gives the displayed coefficient slope. -/
theorem finiteFeatureCoefficients_hasDerivWithinAt {a d t : ℝ} (ha : -1<a) (hd : 0<d) (N : ℕ)
    (ht : t∈Icc d (1/2)) (hu : IsUnit (finiteFeatureSystem a ha N t)) :
    HasDerivWithinAt (finiteFeatureCoefficients a ha N) (finiteFeatureCoefficientsSlope a ha N t) (Icc d (1/2)) t := by
  have h := ((finiteFeatureSystemInverse_hasDerivWithinAt ha hd N ht hu).clm_apply
    (finiteFeatureSource_hasDerivWithinAt ha hd N ht)).neg
  convert h using 1
  · rfl
  · unfold finiteFeatureCoefficientsSlope
    rw [neg_apply]
    abel_nf

/-- The original finite inverse-system coefficients have their genuine spatial derivatives for every sufficiently long original spectral prefix, at every point of every positive physical strip, with invertibility fully discharged.
Use: finite spatial calculus for the actual K^(N) uses this same original coefficient family, including the midpoint, without a separately assumed finite inverse or regularity certificate.
Article: jacobi, Appendix C.2 (transformed ODE and Green identity).
Proof: the genuine original finite-system unit threshold works for every physical endpoint. Apply the independently proved original inverse-system derivative at each point of each positive strip. -/
theorem finiteFeatureCoefficients_hasDerivWithinAt_eventually (a : ℝ) (ha : -1<a) :
    ∀ᶠ N : ℕ in atTop,∀ (d : ℝ) (_hd : 0<d) (t : ℝ),t∈Icc d (1/2) →
      HasDerivWithinAt (finiteFeatureCoefficients a ha N) (finiteFeatureCoefficientsSlope a ha N t) (Icc d (1/2)) t := by
  filter_upwards [finiteFeatureSystem_isUnit a ha] with N hN d hd t ht
  exact finiteFeatureCoefficients_hasDerivWithinAt ha hd N ht (hN t)

end
end jacobi.GelfandLevitan
