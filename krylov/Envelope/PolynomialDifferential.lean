import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
Article: main_krylov, apB:lem:DK, genuine noncommutative polynomial first derivative.
Use: compute the true operator-polynomial variation that enters the source
Daleckii--Krein pairing, without assuming commuting perturbations or a
prescribed first-variation formula.
Source: DaleckiiKrein65 for attribution; actual proof reuses mathlib
HasDerivAt.fun_pow' and finite real coefficient evaluation/sum rules.
-/

namespace krylov.Envelope
noncomputable section
open Polynomial
open scoped BigOperators
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The genuine finite ordered-insertion operator polynomial variation.
Use: The genuine finite ordered-insertion operator polynomial variation.
Article: main_krylov, apB:lem:DK, genuine noncommutative polynomial first derivative.
Proof: Keep the perturbation between the actual left and right powers, without commuting it with the true reference operator. -/
def polynomialFirstVariation (p : ℝ[X]) (Q D : A) : A :=
  ∑ j∈Finset.range (p.natDegree+1), p.coeff j •
    (∑ r∈Finset.range j, Q^(j.pred-r)*D*Q^r)

/-- The real derivative of an actual operator-polynomial path equals the genuine finite ordered-insertion formula.
Use: The real derivative of an actual operator-polynomial path equals the genuine finite ordered-insertion formula.
Article: main_krylov, apB:lem:DK, genuine noncommutative polynomial first derivative.
Proof: Use mathlib noncommutative power differentiation termwise in the actual finite polynomial evaluation sum. -/
theorem hasDerivAt_polynomial (p : ℝ[X]) (Q : ℝ → A) (D : A) (t : ℝ)
    (hQ : HasDerivAt Q D t) :
    HasDerivAt (fun s => aeval (Q s) p) (polynomialFirstVariation p (Q t) D) t := by
  convert HasDerivAt.sum (fun j (_ : j∈Finset.range (p.natDegree+1)) =>
    (hQ.fun_pow' j).const_smul (p.coeff j)) using 1
  funext s
  simpa only [Finset.sum_apply,Pi.smul_apply] using (Polynomial.aeval_eq_sum_range (Q s) (p := p))
  rfl

/-- The genuine operator-polynomial first variation is additive in its real perturbation.
Use: The genuine operator-polynomial first variation is additive in its real perturbation.
Article: main_krylov, apB:lem:DK, genuine noncommutative polynomial first derivative.
Proof: Distribute the true ordered left/right multiplications through the finite sum. -/
theorem polynomialFirstVariation_add (p : ℝ[X]) (Q D F : A) :
    polynomialFirstVariation p Q (D+F)=polynomialFirstVariation p Q D+polynomialFirstVariation p Q F := by
  simp only [polynomialFirstVariation,mul_add,add_mul,Finset.sum_add_distrib,smul_add]

/-- The genuine operator-polynomial first variation is real-linear under perturbation scaling.
Use: The genuine operator-polynomial first variation is real-linear under perturbation scaling.
Article: main_krylov, apB:lem:DK, genuine noncommutative polynomial first derivative.
Proof: Move the real scalar through each genuine ordered insertion and its finite coefficient sum. -/
theorem polynomialFirstVariation_smul (p : ℝ[X]) (Q D : A) (c : ℝ) :
    polynomialFirstVariation p Q (c • D)=c • polynomialFirstVariation p Q D := by
  simp only [polynomialFirstVariation,mul_smul_comm,smul_mul_assoc,
    Finset.smul_sum,smul_comm (p.coeff _) c]
end
end krylov.Envelope
