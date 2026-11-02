import jacobi.Reference.WeightDerivatives

/-!
Article: jacobi, Lemma C.1.
The literal reference Gegenbauer functions satisfy the printed
Poeschl--Teller equation with genuine ordinary derivatives. The proof
specializes the existing exact Jacobi angular equation and differentiates
the original sine-power prefactor. It covers the full source order range.
Use: fixes the genuine midpoint derivative and reference Neumann boundary condition.
-/
namespace jacobi.Reference
noncomputable section
open Real Set
set_option backward.isDefEq.respectTransparency false

/-- The explicit first derivative of the actual reference eigenfunction.
Use: fixes the genuine midpoint derivative and reference Neumann boundary condition.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def eigenfunctionSlope (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  weight a t*(Real.pi* jacobi.Jacobi.angularSlope (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)+
    weightLogSlope a t* jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t))

/-- The explicit second derivative of the actual reference eigenfunction.
Use: proves the original reference differential equation and identifies its classical second derivative.
Article: jacobi, Appendix C.1 (selected endpoint branch).
-/
def eigenfunctionAcceleration (a : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  weight a t*(Real.pi^2* jacobi.Jacobi.angularAcceleration (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)+
    2*weightLogSlope a t*Real.pi* jacobi.Jacobi.angularSlope (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)+
    (weightLogAcceleration a t+weightLogSlope a t^2)* jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t))

/-- The explicit reference slope is the true ordinary first derivative throughout the physical interior.
Use: the reference spectral boundary values and Green identities concern actual functions and derivatives.
Article: jacobi, Lemma C.1.
Proof: multiply the actual prefactor derivative by the actual Jacobi angular chain derivative. -/
theorem eigenfunction_hasDerivAt (a : ℝ) (k : ℕ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (eigenfunction a k) (eigenfunctionSlope a k t) t := by
  have hi := (hasDerivAt_id t).const_mul Real.pi
  have hp := (jacobi.Jacobi.angular_hasDerivAt (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)).comp t hi
  convert (weight_hasDerivAt a ht).mul hp using 1
  · rfl
  · dsimp [eigenfunctionSlope]
    ring

/-- The explicit reference acceleration is the true derivative of the actual reference slope.
Use: establishes the reference equation with genuine second derivatives and gives the original C2 regularity.
Article: jacobi, Lemma C.1.
Proof: apply the chain and product rules to the already identified actual slope and logarithmic prefactor slope. -/
theorem eigenfunctionSlope_hasDerivAt (a : ℝ) (k : ℕ) {t : ℝ} (ht : t∈Ioo 0 1) :
    HasDerivAt (eigenfunctionSlope a k) (eigenfunctionAcceleration a k t) t := by
  -- All derivative inputs are unconditional statements about the actual source prefactor and the original finite polynomial.
  have hi := (hasDerivAt_id t).const_mul Real.pi
  have hp := (jacobi.Jacobi.angular_hasDerivAt (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)).comp t hi
  have hpp := (jacobi.Jacobi.angularSlope_hasDerivAt (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)).comp t hi
  have hinner := (hpp.const_mul Real.pi).add ((weightLogSlope_hasDerivAt a ht).mul hp)
  convert (weight_hasDerivAt a ht).mul hinner using 1
  · rfl
  · dsimp [eigenfunctionAcceleration,eigenfunctionSlope]
    ring

/-- The source reference first-derivative coefficient cancels exactly against the true sine-power logarithmic derivative.
Use: specializes the existing genuine Jacobi angular equation to the reference Schrodinger equation.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: the equal Jacobi parameter is gamma-1/2; substitute its literal value. -/
theorem first_coefficient (a t : ℝ) :
    2*weightLogSlope a t*Real.pi=Real.pi^2*
      (((jacobiIndex a-jacobiIndex a)+(jacobiIndex a+jacobiIndex a+1)*cos (Real.pi*t))/sin (Real.pi*t)) := by
  dsimp [weightLogSlope,jacobiIndex]
  ring

/-- The literal reference eigenvalue and potential give exactly the transformed Jacobi zeroth coefficient.
Use: the true reference equation has precisely the printed tau_k and q_alpha, with no assumed spectral identification.
Article: jacobi, Appendix C.1 (selected endpoint branch).
Proof: substitute the original coefficients and use sin^2+cos^2=1 after clearing the nonzero physical sine. -/
theorem zeroth_coefficient (a : ℝ) (k : ℕ) {t : ℝ} (ht : t∈Ioo 0 1) :
    eigenvalue a k-potential a t+weightLogAcceleration a t+weightLogSlope a t^2=
      Real.pi^2*(k:ℝ)*(k+jacobiIndex a+jacobiIndex a+1) := by
  -- The fixed c_0alpha shift cancels on both sides of the actual equation.
  have hs := sine_pos ht
  unfold eigenvalue potential weightLogAcceleration weightLogSlope jacobiIndex
  field_simp [hs.ne']
  linear_combination 2*Real.pi^2*gamma a^2*(Real.sin_sq_add_cos_sq (Real.pi*t))

/-- Every literal reference Gegenbauer eigenfunction satisfies its exact original Poeschl--Teller equation on the full physical interior.
Use: constructs the reference spectral realization and supplies the actual reference Green identities for Proposition C.2.
Article: jacobi, Lemma C.1.
Proof: the actual symmetric Jacobi angular equation cancels the first
derivative coefficient after the sine-power substitution. The exact
zeroth coefficient identity supplies the literal reference potential
and eigenvalue. All original parameter conditions are discharged. -/
theorem eigenfunction_equation {a : ℝ} (ha : -1<a) (k : ℕ) {t : ℝ} (ht : t∈Ioo 0 1) :
    -eigenfunctionAcceleration a k t+potential a t*eigenfunction a k t=
      eigenvalue a k*eigenfunction a k t := by
  -- This is an identity for the actual defined functions, obtained from the existing genuine polynomial equation.
  have htheta : Real.pi*t∈Ioo 0 Real.pi := ⟨mul_pos Real.pi_pos ht.1,by nlinarith [Real.pi_pos,ht.2]⟩
  have h := jacobi.Jacobi.angular_equation (b := jacobiIndex a) (parameters ha).2 k htheta
  have hfirst := first_coefficient a t
  have hzero := zeroth_coefficient a k ht
  unfold eigenfunctionAcceleration eigenfunction
  linear_combination -weight a t*Real.pi^2*h-
    weight a t* jacobi.Jacobi.angularSlope (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)*hfirst-
    weight a t* jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)*hzero

/-- The actual reference eigenfunction is real analytic at every physical interior point.
Use: supplies all local classical regularity needed by midpoint parity splitting and the transformed equation.
Article: jacobi, Lemma C.1.
Proof: multiply the positive analytic sine-power prefactor by the actual analytic Jacobi angular polynomial composed with pi*t. -/
theorem eigenfunction_analytic (a : ℝ) (k : ℕ) {t : ℝ} (ht : t∈Ioo 0 1) :
    AnalyticAt ℝ (eigenfunction a k) t :=
  (weight_analytic a ht).mul ((jacobi.Jacobi.angular_analytic (jacobiIndex a) (jacobiIndex a) k (Real.pi*t)).comp
    (f := fun s : ℝ => Real.pi*s) (analyticAt_const.mul analyticAt_id))

end
end jacobi.Reference
