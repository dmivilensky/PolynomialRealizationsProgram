import krylov.Stability.ContDiffVirtual
import Mathlib.Analysis.Calculus.Deriv.Mul
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, first jets of genuine zero-reference error identities.
Use: differentiate actual native weighted replay equations without retaining
spurious derivatives of trial or virtual coefficients multiplying zero errors.
Source: mathlib real scalar/vector product rule, finite-sum derivative rule
and derivative uniqueness under genuine local equality.
-/

namespace krylov.Stability
noncomputable section
open Filter Topology
open scoped BigOperators
variable {V ι : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype ι]

/-- A genuine locally equal weighted zero-reference identity has the exact
frozen-coefficient first-jet identity.
Use: trial and virtual-coefficient derivatives multiply actual zero errors.
Article: main_krylov, thm:I.
Proof: apply the real product and finite-sum derivative rules, remove the
true zero-reference factors, and use local derivative uniqueness. -/
theorem weighted_zero_identity_deriv (a : ℝ → ℝ) (v : ℝ → V)
    (w : ℝ → ι → ℝ) (F : ℝ → ι → V)
    (ha : DifferentiableAt ℝ a 0) (hv : DifferentiableAt ℝ v 0)
    (hw : ∀ i,DifferentiableAt ℝ (fun t => w t i) 0)
    (hF : ∀ i,DifferentiableAt ℝ (fun t => F t i) 0)
    (hv0 : v 0=0) (hF0 : ∀ i,F 0 i=0)
    (he : (fun t => a t • v t)=ᶠ[𝓝 (0 : ℝ)] (fun t => ∑ i,w t i • F t i)) :
    a 0 • deriv v 0=∑ i,w 0 i • deriv (fun t => F t i) 0 := by
  have hL := ha.hasDerivAt.fun_smul hv.hasDerivAt
  simp only [hv0,smul_zero,add_zero] at hL
  have hterm (i : ι) : HasDerivAt (fun t => w t i • F t i)
      (w 0 i • deriv (fun t => F t i) 0) 0 := by
    simpa only [hF0 i,smul_zero,add_zero] using (hw i).hasDerivAt.fun_smul (hF i).hasDerivAt
  have hR := HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i)
  exact (hL.congr_of_eventuallyEq he.symm).unique hR

/-- The true first variation of a zero-reference operator drift acting on a
moving direction has no direction-derivative contribution.
Use: each actual replay-error bracket has the printed frozen CG direction.
Article: main_krylov, thm:I.
Proof: the genuine continuous-linear action product rule has a zero operator
factor at the reference; subtract the actual earlier error derivative. -/
theorem zero_drift_action_deriv (A B : ℝ → V →L[ℝ] V) (d e : ℝ → V)
    (hA : DifferentiableAt ℝ A 0) (hB : DifferentiableAt ℝ B 0)
    (hd : DifferentiableAt ℝ d 0) (he : DifferentiableAt ℝ e 0) (hAB : A 0=B 0) :
    deriv (fun t => (A t-B t) (d t)-e t) 0=
      (deriv A 0-deriv B 0) (d 0)-deriv e 0 := by
  have h := ((hA.hasDerivAt.fun_sub hB.hasDerivAt).clm_apply hd.hasDerivAt).fun_sub he.hasDerivAt
  simpa only [hAB,sub_self,zero_apply,add_zero] using h.deriv

end
end krylov.Stability
