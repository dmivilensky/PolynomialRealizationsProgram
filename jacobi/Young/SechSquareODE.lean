import jacobi.Young.FirstIntegral

/-!
Article: jacobi, Section 3.2 (sharp Young inequality).
The explicit sech-squared function solves the actual semilinear equation
with its forced peak height. The zero first integral and global uniqueness
therefore identify every nonzero decaying finite-energy classical solution.
Source: elementary hyperbolic calculus and Picard--Lindelof uniqueness.
Use: verifies the explicit equality ODE solution, with its exact spatial scale.
-/
namespace jacobi.Young
noncomputable section
open Set Real Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The actual derivative of the squared hyperbolic secant.
Use: verifies the explicit equality ODE solution, with its exact spatial scale.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: differentiate sech²=1-tanh² using the already proved tanh derivative. -/
theorem sech_sq_derivative (x : ℝ) :
    HasDerivAt (fun y => sech y^2) (-2*sech x^2*Real.tanh x) x := by
  have he : (fun y => sech y^2)=(fun y => 1-Real.tanh y^2) := funext sech_sq
  rw [he]
  convert ((tanh_derivative x).pow 2).const_sub 1 using 1
  ring

/-- The literal forced-height solution of the semilinear Green equation.
Use: the equality classification and the zero-mass-multiplier elliptic endpoint.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def sechSquareSolution (a b x : ℝ) : ℝ := (6/a)*sech (x-b)^2

/-- The literal slope of the explicit forced-height solution.
Use: verifies the initial slope and the first-order ODE system for profile uniqueness.
Article: jacobi, Section 3.2 (sharp Young inequality).
-/
def sechSquareSlope (a b x : ℝ) : ℝ := -(12/a)*sech (x-b)^2*Real.tanh (x-b)

/-- The declared explicit slope is the actual derivative of the candidate.
Use: applies the general semilinear uniqueness theorem to the literal hyperbolic profile.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: compose the sech-squared derivative with translation and multiply its amplitude. -/
theorem sechSquareSolution_derivative (a b x : ℝ) :
    HasDerivAt (sechSquareSolution a b) (sechSquareSlope a b x) x := by
  convert ((sech_sq_derivative (x-b)).comp x ((hasDerivAt_id x).sub_const b)).const_mul (6/a) using 1
  · rfl
  · dsimp only [sechSquareSlope]
    ring

/-- The explicit hyperbolic candidate solves the actual classical semilinear equation.
Use: uniqueness identifies every finite-energy equality solution without a profile assumption.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: differentiate the literal slope, use tanh²=1-sech², and cancel the nonzero amplitude denominator. -/
theorem sechSquareSlope_derivative {a : ℝ} (ha : a≠0) (b x : ℝ) :
    HasDerivAt (sechSquareSlope a b)
      (4*sechSquareSolution a b x-a*sechSquareSolution a b x^2) x := by
  -- All differential identities concern real functions at every real point.
  have ht := (hasDerivAt_id x).sub_const b
  convert ((((sech_sq_derivative (x-b)).comp x ht).const_mul (-(12/a))).mul
    ((tanh_derivative (x-b)).comp x ht)) using 1
  · rfl
  · dsimp only [sechSquareSolution]
    simp only [Function.comp_def,id_eq]
    have hs := sech_sq (x-b)
    field_simp [ha]
    nlinarith [congrArg (fun r : ℝ => r*sech (x-b)^2) hs]

/-- The explicit profile has the exact forced value and zero slope at its center.
Use: matches the initial data deduced from the actual first integral.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: sech(0)=1 and tanh(0)=0. -/
theorem sechSquare_initial (a b : ℝ) :
    sechSquareSolution a b b=6/a ∧ sechSquareSlope a b b=0 := by
  simp [sechSquareSolution,sechSquareSlope,sech]

/-- Every nonzero finite-energy decaying classical semilinear solution is a translated sech square.
Use: completes necessity of the Young equality family after the actual potential has been regularized.
Article: jacobi, Section 3.2 (sharp Young inequality).
Proof: the zero first integral fixes a positive maximum at height 6/a and
zero slope. The explicit candidate has these same data, so the proved global
Picard--Lindelof uniqueness identifies both value and slope everywhere. -/
theorem semilinear_classification {f d : ℝ → ℝ} {a : ℝ} (ha : 0<a)
    (hf : ∀ x, HasDerivAt f (d x) x)
    (hd : ∀ x, HasDerivAt d (4*f x-a*f x^2) x)
    (hf2 : Integrable (fun x => f x^2)) (hd2 : Integrable (fun x => d x^2))
    (hf3 : Integrable (fun x => f x^3))
    (ht : Tendsto f atTop (𝓝 0)) (hb : Tendsto f atBot (𝓝 0))
    (hn : ∃ z, 0<f z) : ∃ b, f=sechSquareSolution a b ∧ d=sechSquareSlope a b := by
  -- Every premise comes from the actual equality potential in the application.
  obtain ⟨b,h0,h1⟩ := semilinear_peak ha hf hd hf2 hd2 hf3 ht hb hn
  refine ⟨b,?_⟩
  exact semilinear_unique a b hf hd (sechSquareSolution_derivative a b)
    (sechSquareSlope_derivative ha.ne' b) (h0.trans (sechSquare_initial a b).1.symm)
    (h1.trans (sechSquare_initial a b).2.symm)

end
end jacobi.Young
