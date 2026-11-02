import jacobi.Reference.MidpointCharacteristic
import jacobi.Reference.MidpointZeros
import jacobi.Reference.NegativeQuotient

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The exact midpoint factorization is transferred to the original entire
energy functions. Every zero of either original midpoint function is
simple. Together with MidpointZeros and NegativeQuotient this proves
the reference midpoint lemma for the actual f and its genuine derivative.
Use: supplies the correctly normalized entire midpoint comparison for Proposition C.2 and proves both midpoint zero sets are simple.
-/
namespace jacobi.Reference
noncomputable section
open Real Set _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- The product of the original midpoint reference value and its true spatial derivative is exactly kappa times the literal entire energy characteristic.
Use: supplies the correctly normalized entire midpoint comparison for Proposition C.2 and proves both midpoint zero sets are simple.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: evaluate the exact frequency product at the actual square root defining f; the same square root defines Delta_tau. -/
theorem solution_midpoint_product {a : ℝ} (ha : -1<a) (z : ℂ) :
    2*solution a z (1/2)*solutionSlope a z (1/2)=
      ((2*Real.pi^2*normConstant a:ℝ):ℂ)*characteristicTau a z :=
  wave_midpoint_characteristic ha _

/-- The derivative of the actual entire midpoint factorization has its exact product-rule identity at every original complex energy.
Use: proves genuine simple midpoint zeros without differentiating a square-root branch or postulating midpoint derivatives.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: both original midpoint functions and the original characteristic
are entire. Differentiate the same proved global equality and use
uniqueness of the genuine complex derivative. -/
theorem solution_midpoint_product_derivative {a : ℝ} (ha : -1<a) (z : ℂ) :
    2*deriv (fun w => solution a w (1/2)) z*solutionSlope a z (1/2)+
      2*solution a z (1/2)*deriv (fun w => solutionSlope a w (1/2)) z=
        ((2*Real.pi^2*normConstant a:ℝ):ℂ)*deriv (characteristicTau a) z := by
  -- These are the genuine energy derivatives of the same original reference functions used in the source factorization.
  have hA := (solution_energy_analytic a (t := (1/2:ℝ)) (by norm_num) z).differentiableAt.hasDerivAt
  have hB := (solutionSlope_midpoint_analytic ha z).differentiableAt.hasDerivAt
  have hD := (characteristicTau_analytic a z).differentiableAt.hasDerivAt
  have hL := (hA.const_mul 2).mul hB
  change HasDerivAt (fun w => 2*solution a w (1/2)*solutionSlope a w (1/2)) _ z at hL
  have he : (fun w => 2*solution a w (1/2)*solutionSlope a w (1/2))=
      (fun w => ((2*Real.pi^2*normConstant a:ℝ):ℂ)*characteristicTau a w) :=
    funext (solution_midpoint_product ha)
  rw [he] at hL
  simpa only [mul_assoc] using hL.unique (hD.const_mul ((2*Real.pi^2*normConstant a:ℝ):ℂ))

/-- Every complex zero of the actual midpoint reference value is simple in the original energy variable.
Use: supplies the complete simple Dirichlet reference characteristic class in the midpoint comparison of Proposition C.2.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: its zero makes Delta_tau vanish by the exact product identity.
The derivative product identity and the already proved simple reference
characteristic zero then exclude a zero energy derivative of a_0. -/
theorem solution_midpoint_simple {a : ℝ} (ha : -1<a) {z : ℂ}
    (hz : solution a z (1/2)=0) : deriv (fun w => solution a w (1/2)) z≠0 := by
  -- The characteristic normalization is the original positive norm scalar, so its factor cannot annihilate a true derivative.
  have hc : ((2*Real.pi^2*normConstant a:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity [normConstant_pos ha]))
  have hprod := solution_midpoint_product ha z
  rw [hz,mul_zero,zero_mul] at hprod
  have hd := characteristicTau_simple ha ((mul_eq_zero.mp hprod.symm).resolve_left hc)
  intro hzero
  have h := solution_midpoint_product_derivative ha z
  simp only [hz,hzero,mul_zero,zero_mul,zero_add] at h
  exact (mul_ne_zero hc hd) h.symm

/-- Every complex zero of the actual midpoint spatial slope is simple in the original energy variable.
Use: supplies the complete simple Neumann reference characteristic class in Proposition C.2's midpoint comparison.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: the exact entire product and its genuine derivative reduce a hypothetical double zero to a double zero of the proved simple reference characteristic. -/
theorem solutionSlope_midpoint_simple {a : ℝ} (ha : -1<a) {z : ℂ}
    (hz : solutionSlope a z (1/2)=0) : deriv (fun w => solutionSlope a w (1/2)) z≠0 := by
  -- A vanishing actual slope derivative would force the genuine simple reference characteristic derivative to vanish.
  have hc : ((2*Real.pi^2*normConstant a:ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity [normConstant_pos ha]))
  have hprod := solution_midpoint_product ha z
  rw [hz,mul_zero] at hprod
  have hd := characteristicTau_simple ha ((mul_eq_zero.mp hprod.symm).resolve_left hc)
  intro hzero
  have h := solution_midpoint_product_derivative ha z
  simp only [hz,hzero,mul_zero,zero_add] at h
  exact (mul_ne_zero hc hd) h.symm

end
end jacobi.Reference
