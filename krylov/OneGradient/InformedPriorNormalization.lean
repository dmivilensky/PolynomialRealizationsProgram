import krylov.OneGradient.InformedPriorBase
import krylov.Correction.ReferenceOperator
import krylov.Reference.Energy
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), exact actual physical prior normalization.
Use: original attaining scenarios use their genuine own-base penultimate
reference error, with an exact derived formula rather than an assumed limit.
Source: true common physical CG prefix, exact original final line length
and genuine CG energy/terminal-step identities.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix krylov.Reference krylov.Secant krylov.Correction
open scoped Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The genuine penultimate reference-error norm squared on the actual
physical prior base is its known value divided exactly by 1+rho.
Use: sharpness uses the source's true own reference normalization.
Article: main_krylov, thm:local(b), exact actual prior energy normalization.
Proof: the true last CG energy is its actual final length times the
unchanged real last residual norm squared. The physical prior keeps that
whole CG prefix fixed and divides its real final length by 1+rho. Actual
full-reference termination identifies both true penultimate error norms. -/
theorem informedPriorBase_error_norm_sq
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤rho) :
    ‖cgCanonicalError (informedPriorBase A hA g hg hc rho) g n‖^2=
      ‖cgCanonicalError A g n‖^2/(1+rho) := by
  let B := informedPriorBase A hA g hg hc rho
  have hB := informedPriorBase_posDef A hA g hg hc rho hrho
  have hcount := informedPriorBase_full_atoms A hA g hg hc rho hrho
  have hcountA := full_gradient_atom_count A hA g hc
  have hgrad : CG.gradient (cgOperator B) g n=CG.gradient (cgOperator A) g n :=
    congrArg CGState.gradient (informedPriorBase_cg_prefix A hA g hg hc rho n le_rfl)
  have hcountB : referenceAtomCount B hB g=n+1 := hcount
  have henergy := cgEnergy_eq_length_norm B hB g (k := n) (by rw [hcountB];omega)
  have henergyA := cgEnergy_eq_length_norm A hA g (k := n) (by rw [hcountA];omega)
  rw [cgEnergy_eq_norm_sq B hB,← terminal_step_error_norm B hB g hcount.ge,hgrad,
    informedPriorBase_last_length A hA g hg hc rho hrho] at henergy
  rw [cgEnergy_eq_norm_sq A hA,← terminal_step_error_norm A hA g hcountA.ge] at henergyA
  rw [henergy,henergyA]
  ring

/-- The actual physical prior family's own penultimate error norm is
exactly its known value divided by the square root of 1+rho, including rho=0.
Use: actual source normalization tends to the original known normalization
with every positive prior radius and all zero budget profiles included.
Article: main_krylov, thm:local(b), exact actual prior norm normalization.
Proof: the genuine squared-energy identity is already proved. Both real
norms and the positive square-root denominator are nonnegative, so their
equal squares identify their actual nonnegative values uniquely. -/
theorem informedPriorBase_error_norm
    (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (n+1))) (hg : g≠0)
    (hc : (activeSpectralValues A hA.1 g).card=n+1) (rho : ℝ) (hrho : 0≤rho) :
    ‖cgCanonicalError (informedPriorBase A hA g hg hc rho) g n‖=
      ‖cgCanonicalError A g n‖/Real.sqrt (1+rho) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))).mp
  rw [div_pow,Real.sq_sqrt (by linarith : 0≤1+rho)]
  exact informedPriorBase_error_norm_sq A hA g hg hc rho hrho

end
end krylov.OneGradient
