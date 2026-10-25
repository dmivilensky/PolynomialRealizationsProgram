import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Article: chebyshev2, Theorem 6.1.
An explicit normalization correction.
Use: `chebyshev2.LocalObstruction.quadraticCorrection_equation` feeds
`chebyshev2.LocalObstruction.curveDensity_mass` (curve Density mass).
Proof chain: `chebyshev2.LocalObstruction.theorem_6_1` — chebyshev2, Theorem 6.1; No locally
sharp C1 bound from finitely many spectral observations.
-/
namespace chebyshev2.LocalObstruction
noncomputable section
open Real Filter
open scoped Topology ContDiff
set_option autoImplicit false

/--
Defines `correctionDiscriminant` of type `ℝ` by `(B+2*t*C)^2-4*D*t^2*E`.

Use: `chebyshev2.LocalObstruction.quadraticCorrection` uses this definition in the
displayed construction of `quadraticCorrection`. Its inputs and component formulas are fixed by
that definition.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def correctionDiscriminant (B C D E t : ℝ) : ℝ := (B+2*t*C)^2-4*D*t^2*E
/--
Defines `quadraticCorrection` of type `ℝ` by `-2*t^2*E/(B+2*t*C+sqrt (correctionDiscriminant B
C D E t))`.

Use: `chebyshev2.LocalObstruction.quadraticCorrection_zero` rewrites with this definition
to establish the identity `quadraticCorrection B C D E 0=0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.
-/
def quadraticCorrection (B C D E t : ℝ) : ℝ :=
  -2*t^2*E/(B+2*t*C+sqrt (correctionDiscriminant B C D E t))

 /--
Exact identity `quadraticCorrection B C D E 0=0`.

Use: `chebyshev2.LocalObstruction.curveCorrection_zero` uses this identity to establish
exact identity `curveCorrection h w 0=0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem quadraticCorrection_zero {B C D E : ℝ} : quadraticCorrection B C D E 0=0 := by simp [quadraticCorrection]

 /--
Smoothness to the stated order: `ContDiffAt ℝ ∞ (quadraticCorrection B C D E) 0`.

Use: `chebyshev2.LocalObstruction.curveParameters_smooth` uses this assertion to establish
smoothness to the stated order: `ContDiffAt ℝ ∞ (curveParameters h w) 0`.

Article: chebyshev2, Theorem 6.1.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem quadraticCorrection_smooth {B C D E : ℝ} (hB : 0<B) :
    ContDiffAt ℝ ∞ (quadraticCorrection B C D E) 0 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hdisc : ContDiffAt ℝ ∞ (correctionDiscriminant B C D E) 0 := by
    unfold correctionDiscriminant
    fun_prop
  have hpos : 0<correctionDiscriminant B C D E 0 := by
    simpa [correctionDiscriminant] using sq_pos_of_pos hB
  have hden : B+2*(0:ℝ)*C+sqrt (correctionDiscriminant B C D E 0)≠0 := by
    simp only [correctionDiscriminant,mul_zero,zero_mul,zero_pow (by decide : 2≠0),
      add_zero,sub_zero,sqrt_sq hB.le]
    linarith
  exact (by fun_prop : ContDiffAt ℝ ∞ (fun t : ℝ => -2*t^2*E) 0).div
    ((by fun_prop : ContDiffAt ℝ ∞ (fun t : ℝ => B+2*t*C) 0).add
      (hdisc.sqrt hpos.ne')) hden

 /--
The actual derivative at the stated point: `HasDerivAt (quadraticCorrection B C D E) 0 0`.

Use: `chebyshev2.LocalObstruction.curveCorrection_derivative` uses this derivative formula
to establish the actual derivative at the stated point: `HasDerivAt (curveCorrection h w) 0 0`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Rewrite the definitions and library identities explicitly named in the proof, then
discharge the resulting algebraic or order relation.
-/
theorem quadraticCorrection_derivative {B C D E : ℝ} (hB : 0<B) :
    HasDerivAt (quadraticCorrection B C D E) 0 0 := by
  -- Rewrite the definitions and library identities explicitly named in the proof, then
  -- discharge the resulting algebraic or order relation.
  have hd : HasDerivAt (fun t : ℝ => -2*t^2*E) 0 0 := by
    convert! (((hasDerivAt_id (0:ℝ)).pow 2).const_mul (-2)).mul_const E using 1; norm_num
  have hdc : DifferentiableAt ℝ (fun t : ℝ =>
      B+2*t*C+sqrt (correctionDiscriminant B C D E t)) 0 := by
    have hpoly : DifferentiableAt ℝ (correctionDiscriminant B C D E) 0 := by
      unfold correctionDiscriminant
      fun_prop
    exact (by fun_prop : DifferentiableAt ℝ (fun t : ℝ => B+2*t*C) 0).add
      (hpoly.sqrt (by simpa [correctionDiscriminant] using (sq_pos_of_pos hB).ne'))
  have hne : B+2*(0:ℝ)*C+sqrt (correctionDiscriminant B C D E 0)≠0 := by
    simp [correctionDiscriminant,sqrt_sq hB.le,ne_of_gt (by linarith : 0<B+B)]
  convert! hd.div hdc.hasDerivAt hne using 1
  simp

 /--
Establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ),
t^2*E+quadraticCorrection B C D E t*(B+2*t*C)+ D*(quadraticCorrection B C D E t)^2=0`.

Use: `chebyshev2.LocalObstruction.curveDensity_mass` uses this identity to establish
establishes the stated eventual or almost-everywhere assertion `∀ᶠ t in 𝓝 (0:ℝ), (∫ x,
curveDensity h w t x)=1`.

Article: chebyshev2, Theorem 6.1 via `chebyshev2.LocalObstruction.theorem_6_1`.

Proof: Intersect the eventual or almost-everywhere hypotheses, then prove the asserted relation
at an arbitrary point in that intersection. Clear the denominators using the available nonzero
hypotheses, then verify the remaining algebraic identity.
-/
theorem quadraticCorrection_equation {B C D E : ℝ} (hB : 0<B) :
    ∀ᶠ t in 𝓝 (0:ℝ), t^2*E+quadraticCorrection B C D E t*(B+2*t*C)+
      D*(quadraticCorrection B C D E t)^2=0 := by
  -- Establish continuity hcont before using the function at limits or in calculus arguments.
  have hcont : Continuous (correctionDiscriminant B C D E) := by
    unfold correctionDiscriminant
    fun_prop
  have hpos : 0<correctionDiscriminant B C D E 0 := by
    simpa [correctionDiscriminant] using sq_pos_of_pos hB
  -- Establish continuity hdc before using the function at limits or in calculus arguments.
  have hdc : Continuous (fun t : ℝ => B+2*t*C+sqrt (correctionDiscriminant B C D E t)) := by
    fun_prop
  have hden : 0<B+2*(0:ℝ)*C+sqrt (correctionDiscriminant B C D E 0) := by
    simp only [correctionDiscriminant,mul_zero,zero_mul,zero_pow (by decide : 2≠0),
      add_zero,sub_zero,sqrt_sq hB.le]
    linarith
  filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hpos),
    hdc.continuousAt.eventually (lt_mem_nhds hden)] with t ht hd
  let a := B+2*t*C
  let z := sqrt (correctionDiscriminant B C D E t)
  have hs : z^2=a^2-4*D*t^2*E := sq_sqrt ht.le
  have hdz : a+z≠0 := hd.ne'
  change t^2*E+(-2*t^2*E/(a+z))*a+D*(-2*t^2*E/(a+z))^2=0
  field_simp [hdz]
  linear_combination t^2*E*hs

end
end chebyshev2.LocalObstruction
