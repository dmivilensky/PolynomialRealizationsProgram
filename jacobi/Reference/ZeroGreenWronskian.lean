import jacobi.Reference.MidpointSimplicity
import jacobi.Reference.GreenIdentity
import jacobi.Reference.PositiveIntegral
import Mathlib.Analysis.Calculus.MeanValue

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
The two selected zero-frequency solutions have the actual constant
Wronskian kappa/Gamma(gamma)^2. Its sign and normalization are proved
from the original midpoint characteristic, rather than imposed on a
candidate Green function. This fixes the denominator of G_(c_0).
Use: zeroGreenWronskian and zeroGreenKernel construct the Green term removed from F before spatial differentiation.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The original selected solution at the reference energy c_0.
Use: zeroGreenWronskian and zeroGreenKernel construct the Green term removed from F before spatial differentiation.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroSolution (a t : ℝ) : ℂ :=
  solution a (jacobi.Jacobi.endpointCorrection a:ℂ) t

/-- The actual spatial slope of the original selected zero-frequency solution.
Use: computes the genuine constant Wronskian in Appendix C.2 (b).
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
-/
def zeroSlope (a t : ℝ) : ℂ :=
  solutionSlope a (jacobi.Jacobi.endpointCorrection a:ℂ) t

/-- The original zero-frequency solution is the actual wave at frequency zero.
Use: zeroSolution_pos obtains the positivity needed for the Green representation.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the defining energy square root is zero. -/
theorem zeroSolution_eq_wave (a t : ℝ) : zeroSolution a t=wave a 0 t := by
  simp only [zeroSolution,solution,sub_self,Complex.sqrt_zero]

/-- The genuine selected solution at c_0 is strictly positive in the physical interior.
Use: the reference Green factorization has positive selected factors and a nonzero denominator.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: its original beta integral is strictly positive at zero frequency. -/
theorem zeroSolution_pos {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    0<(zeroSolution a t).re := by
  rw [zeroSolution_eq_wave]
  exact wave_zero_pos ha ht

/-- The actual Wronskian of the selected left solution and its reflected right solution.
Use: supplies the normalization of the actual zero-energy Green kernel and its derivative jump.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def zeroGreenWronskian (a t : ℝ) : ℂ :=
  zeroSolution a (1-t)*zeroSlope a t+zeroSolution a t*zeroSlope a (1-t)

/-- Reflection of the original selected zero-energy solution has the genuine negative reflected derivative.
Use: differentiates zeroGreenWronskian with the true right-end selected branch.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: apply the ordinary chain rule to the actual reference solution. -/
theorem zeroSolution_reflection_hasDerivAt (a : ℝ) {t : ℝ} (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (fun s => zeroSolution a (1-s)) (-zeroSlope a (1-t)) t := by
  have hh := (solution_hasDerivAt a (jacobi.Jacobi.endpointCorrection a:ℂ)
    (show 1-t∈Ioo (0:ℝ) 1 from ⟨by linarith [ht.2],by linarith [ht.1]⟩)).scomp t
      ((hasDerivAt_id t).const_sub 1)
  convert! hh using 1
  simp only [zeroSlope,neg_smul,one_smul]

/-- The actual zero-energy Green Wronskian has derivative zero everywhere in the physical interior.
Use: zeroGreenWronskian_formula evaluates it at the midpoint without an unproved constancy premise.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Source: Abel's Wronskian identity for a scalar Schrodinger equation, proved directly here.
Proof: differentiate both genuine products. The mixed slopes cancel;
the two accelerations cancel because the original potential is reflection symmetric. -/
theorem zeroGreenWronskian_hasDerivAt {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    HasDerivAt (zeroGreenWronskian a) 0 t := by
  -- Both factors are actual selected solutions of the same reflected differential equation.
  have hr : 1-t∈Ioo (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have hχ := solution_hasDerivAt a (jacobi.Jacobi.endpointCorrection a:ℂ) ht
  have hχ' := solutionSlope_hasDerivAt a (jacobi.Jacobi.endpointCorrection a:ℂ) ht
  have hR' := (solutionSlope_hasDerivAt a (jacobi.Jacobi.endpointCorrection a:ℂ) hr).scomp t
    ((hasDerivAt_id t).const_sub 1)
  have h := ((zeroSolution_reflection_hasDerivAt a ht).mul hχ').add (hχ.mul hR')
  convert h using 1
  · rfl
  · have he := solution_equation ha (jacobi.Jacobi.endpointCorrection a:ℂ) ht
    have her := solution_equation ha (jacobi.Jacobi.endpointCorrection a:ℂ) hr
    rw [potential_reflection] at her
    dsimp only [zeroSolution,zeroSlope]
    simp only [neg_smul,one_smul,Function.comp_apply]
    linear_combination solution a (jacobi.Jacobi.endpointCorrection a:ℂ) (1-t)*he-
      solution a (jacobi.Jacobi.endpointCorrection a:ℂ) t*her

/-- The original constant Green denominator is exactly its printed positive normalization.
Use: normalizes the reference Green term in F and fixes its derivative jump for the K regularity argument.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the actual Wronskian has zero derivative on the connected physical
interval. At the midpoint the genuine characteristic identity evaluates
it as kappa*Delta_tau(c_0), whose Gamma arguments both equal gamma. -/
theorem zeroGreenWronskian_formula {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    zeroGreenWronskian a t=
      ((2*Real.pi^2*normConstant a:ℝ):ℂ)/(Complex.Gamma (gamma a:ℂ))^2 := by
  -- Constancy is proved for the original Wronskian, not for a separately normalized expression.
  have hc := isOpen_Ioo.is_const_of_deriv_eq_zero (convex_Ioo (0:ℝ) 1).isPreconnected
    (fun t ht => (zeroGreenWronskian_hasDerivAt ha ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (zeroGreenWronskian_hasDerivAt ha ht).deriv) ht
      (show (1/2:ℝ)∈Ioo (0:ℝ) 1 by norm_num)
  rw [hc]
  have hm := solution_midpoint_product ha (jacobi.Jacobi.endpointCorrection a:ℂ)
  have he : zeroGreenWronskian a (1/2)=
      2*solution a (jacobi.Jacobi.endpointCorrection a:ℂ) (1/2)*
        solutionSlope a (jacobi.Jacobi.endpointCorrection a:ℂ) (1/2) := by
    dsimp [zeroGreenWronskian,zeroSolution,zeroSlope]
    norm_num only [show (1:ℝ)-1/2=1/2 by ring]
    ring
  rw [he,hm]
  simp only [characteristicTau,characteristicGamma,sub_self,Complex.sqrt_zero,
    zero_div,sub_zero,add_zero]
  ring

/-- The actual constant Green Wronskian has strictly positive real part.
Use: zeroGreenKernel is well defined and has the positive Green sign required by Appendix C.2.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: the exact original scalar kappa is positive, as is Gamma(gamma). -/
theorem zeroGreenWronskian_pos {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    0<(zeroGreenWronskian a t).re := by
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  rw [zeroGreenWronskian_formula ha ht,Complex.Gamma_ofReal]
  norm_cast
  exact div_pos (by positivity [normConstant_pos ha])
    (sq_pos_of_pos (Real.Gamma_pos_of_pos hg))

end
end jacobi.Reference
