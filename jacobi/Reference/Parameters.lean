import jacobi.Bessel.McMahonSquared
import jacobi.Bessel.ZeroGeometry
import jacobi.Jacobi.LiouvilleEquation

/-!
Article: jacobi, Lemma C.1.
These are the literal reference parameter, potential and eigenvalues.
The reference eigenvalues are strictly increasing; no positivity of their
first entry is imposed. Their displacement from the genuine Bessel
spectrum has the full proved inverse-square McMahon bound.
Use: fixes the selected endpoint branch in the reference and transformed equations.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter
open scoped Topology

/-- The source reference exponent, in terms of the original Bessel order.
Use: fixes the selected endpoint branch in the reference and transformed equations.
Article: jacobi, Lemma C.1.
-/
def gamma (a : ℝ) : ℝ := a/2+3/4

/-- The equal Jacobi parameter for the actual reference Gegenbauer eigenfunctions.
Use: specializes the already proved genuine Jacobi family without duplicating polynomial theory.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def jacobiIndex (a : ℝ) : ℝ := gamma a-1/2

/-- The source reference eigenvalues, with original one-based indices shifted down by one.
Use: defines the actual Poeschl--Teller reference spectrum and the norming-ratio product.
Article: jacobi, Theorem 2.1.
-/
def eigenvalue (a : ℝ) (k : ℕ) : ℝ :=
  Real.pi^2*(k+gamma a)^2+ jacobi.Jacobi.endpointCorrection a

/-- The literal source Poeschl--Teller potential on the open unit interval.
Use: the genuine reference functions solve -f''+q_alpha*f=z*f.
Article: jacobi, Lemma C.1.
-/
def potential (a t : ℝ) : ℝ :=
  gamma a*(gamma a-1)*Real.pi^2/sin (Real.pi*t)^2+ jacobi.Jacobi.endpointCorrection a

/-- The full original order range gives both the printed positive reference exponent and an admissible genuine Jacobi parameter.
Use: discharges the parameter premises of all reference polynomial and singular-endpoint results.
Article: jacobi, Appendix C.3 (positive coefficients, persymmetry and spectrum).
Proof: substitute the two literal affine parameter definitions. -/
theorem parameters {a : ℝ} (ha : -1<a) : 1/4<gamma a ∧ -1<jacobiIndex a := by
  dsimp [gamma,jacobiIndex]
  constructor <;> linarith

/-- The original Bessel leading phase is exactly the reference angular frequency.
Use: imports the already proved McMahon remainder directly into the reference spectrum.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the original source phase grid has the same literal affine offset. -/
theorem phaseGrid_eq (a : ℝ) (k : ℕ) : jacobi.Bessel.phaseGrid a k=Real.pi*(k+gamma a) := by
  unfold jacobi.Bessel.phaseGrid gamma
  ring

/-- The true reference eigenvalues are exactly the squared McMahon phase plus the original correction.
Use: transfers the established original squared-zero error without a new spectral approximation assumption.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: substitute the exact original phase identification and expand the square. -/
theorem eigenvalue_eq (a : ℝ) (k : ℕ) :
    eigenvalue a k=(jacobi.Bessel.phaseGrid a k)^2+(1/4-a^2) := by
  rw [phaseGrid_eq]
  dsimp [eigenvalue,jacobi.Jacobi.endpointCorrection]
  ring

/-- Every original reference oscillation frequency is genuinely positive after subtracting the fixed potential shift.
Use: selects the positive square root in the reference solution formulas; the unshifted eigenvalue itself need not be positive.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the actual leading Bessel phase is strictly positive for every original index. -/
theorem eigenvalue_sub_correction_pos {a : ℝ} (ha : -1<a) (k : ℕ) :
    0<eigenvalue a k- jacobi.Jacobi.endpointCorrection a := by
  rw [eigenvalue_eq]
  change 0<(jacobi.Bessel.phaseGrid a k)^2+(1/4-a^2)-(1/4-a^2)
  nlinarith [sq_pos_of_pos (jacobi.Bessel.phaseGrid_pos ha k)]

/-- The complete source reference spectrum is strictly increasing in its genuine original enumeration.
Use: fixes all signs and nonzero denominators in the norming-ratio products.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: its exact consecutive difference is pi^2*(2*k+1+2*gamma), positive throughout the full parameter range. -/
theorem eigenvalue_strictMono {a : ℝ} (ha : -1<a) : StrictMono (eigenvalue a) := by
  -- The fixed endpoint correction cancels; the exact consecutive gap retains the positive reference exponent.
  apply strictMono_nat_of_lt_succ
  intro k
  have hg := (parameters ha).1
  have hp := Real.pi_pos
  have hk : (0:ℝ)≤k := Nat.cast_nonneg k
  have hdiff : eigenvalue a (k+1)-eigenvalue a k=Real.pi^2*(2*k+1+2*gamma a) := by
    dsimp [eigenvalue]
    push_cast
    ring
  have hh : 0<Real.pi^2*(2*k+1+2*gamma a) := mul_pos (sq_pos_of_pos hp) (by linarith)
  linarith

/-- The true reference eigenvalues differ from the actual Bessel spectrum by one uniform inverse-square error, including every small original index.
Use: supplies the genuine spectral input to norming-ratio convergence and the Gel'fand--Levitan kernel estimates.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the literal reference spectrum is precisely the already proved squared McMahon comparison spectrum. -/
theorem spectrum_error {a : ℝ} (ha : -1<a) :
    ∃ C : ℝ,0<C ∧ ∀ k,|jacobi.Bessel.sigma a ha k-eigenvalue a k|≤C/(k+1:ℝ)^2 := by
  simpa only [eigenvalue_eq] using jacobi.Bessel.mcmahon_squared ha

/-- The actual reference potential is reflection symmetric on the whole open interval.
Use: the reference eigenfunctions split into the midpoint Neumann and Dirichlet classes in Proposition C.2.
Article: jacobi, Proposition 2.2.
Proof: sin(pi*(1-t))=sin(pi*t), leaving the literal potential unchanged. -/
theorem potential_reflection (a t : ℝ) : potential a (1-t)=potential a t := by
  unfold potential
  rw [show Real.pi*(1-t)=Real.pi-Real.pi*t by ring,Real.sin_pi_sub]

/-- The actual reference potential is continuous on the full physical interior.
Use: the reference equation is a classical differential equation at every interior point, including the midpoint.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the sine denominator is nonzero on the physical angle interval and all numerator factors are constant. -/
theorem potential_continuousOn (a : ℝ) : ContinuousOn (potential a) (Ioo 0 1) := by
  intro t ht
  have hs : 0<sin (Real.pi*t) := Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ht.1) (by nlinarith [Real.pi_pos,ht.2])
  exact (((continuousAt_const.div (((Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousAt).pow 2)
    (pow_ne_zero 2 hs.ne')).add continuousAt_const)).continuousWithinAt

end
end jacobi.Reference
