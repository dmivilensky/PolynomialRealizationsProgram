import jacobi.Reference.ZeroGreenFactor

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
The actual selected-solution Green factor has the exact original
reference spectral coefficients. Both endpoint boundary terms are
discharged by the proved singular Green identity and exact reference
reflection, rather than by a formal integration-by-parts placeholder.
Use: zeroGreenFactor_coefficient combines the genuine Green identities on both halves of the physical interval.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Filter MeasureTheory
open scoped Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] realSolution zeroGreenFactor zeroGreenConstant

/-- The actual reference slope has the precise opposite reflected parity of its original reference solution.
Use: zeroGreenFactor_coefficient combines the genuine Green identities on both halves of the physical interval.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: differentiate the exact original eigenfunction reflection through the independently proved genuine spatial derivative, and take real parts of the resulting complex identity. -/
theorem realSlope_reference_reflection {a t : ℝ} (ha : -1<a) (k : ℕ) (ht : t∈Ioo (0:ℝ) 1) :
    realSlope a (eigenvalue a k) (1-t)= -(-1:ℝ)^k*realSlope a (eigenvalue a k) t := by
  -- Parity is an equality of the original actual functions before any derivative is taken.
  have hr : 1-t∈Ioo (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have he : (fun x : ℝ => solution a (eigenvalue a k:ℂ) (1-x))=
      (fun x : ℝ => ((-1:ℝ)^k:ℂ)*solution a (eigenvalue a k:ℂ) x) := by
    funext x
    simp only [solution_at_eigenvalue,eigenfunction_reflection ha,Complex.ofReal_mul,Complex.ofReal_pow]
  have hl : HasDerivAt (fun x : ℝ => solution a (eigenvalue a k:ℂ) (1-x))
      (-solutionSlope a (eigenvalue a k:ℂ) (1-t)) t := by
    convert! (solution_hasDerivAt a (eigenvalue a k:ℂ) hr).scomp t ((hasDerivAt_id t).const_sub 1) using 1
    simp only [neg_smul,one_smul]
  rw [he] at hl
  have hh := congrArg Complex.re (hl.unique ((solution_hasDerivAt a (eigenvalue a k:ℂ) ht).const_mul ((-1:ℝ)^k:ℂ)))
  rw [← Complex.ofReal_pow] at hh
  simp only [Complex.neg_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at hh
  dsimp [realSlope]
  linarith

/-- The original real Green denominator equals the same genuine left/right Wronskian at every interior point.
Use: the selected Green factor coefficient reduces exactly to f(s,tau_k)/varpi_k^2 after both original boundary contributions are combined.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: express the true complex Wronskian through the proved real solutions and real slopes, and use its independently proved constant Gamma evaluation at the point and midpoint. -/
theorem zeroGreenConstant_at {a t : ℝ} (ha : -1<a) (ht : t∈Ioo (0:ℝ) 1) :
    realSolution a (jacobi.Jacobi.endpointCorrection a) (1-t)*realSlope a (jacobi.Jacobi.endpointCorrection a) t+
      realSolution a (jacobi.Jacobi.endpointCorrection a) t*realSlope a (jacobi.Jacobi.endpointCorrection a) (1-t)=
    zeroGreenConstant a := by
  -- Both point evaluations use the same true constant Wronskian, with its original sign.
  have hr : 1-t∈Ioo (0:ℝ) 1 := ⟨by linarith [ht.2],by linarith [ht.1]⟩
  have he : zeroGreenWronskian a t=zeroGreenWronskian a (1/2) :=
    (zeroGreenWronskian_formula ha ht).trans (zeroGreenWronskian_formula ha (by norm_num : (1/2:ℝ)∈Ioo (0:ℝ) 1)).symm
  have hw : ((realSolution a (jacobi.Jacobi.endpointCorrection a) (1-t)*realSlope a (jacobi.Jacobi.endpointCorrection a) t+
      realSolution a (jacobi.Jacobi.endpointCorrection a) t*realSlope a (jacobi.Jacobi.endpointCorrection a) (1-t):ℝ):ℂ)=
      zeroGreenWronskian a t := by
    simp only [Complex.ofReal_add,Complex.ofReal_mul,realSolution_cast,realSlope,
      solutionSlope_real a (jacobi.Jacobi.endpointCorrection a) ht,
      solutionSlope_real a (jacobi.Jacobi.endpointCorrection a) hr,zeroGreenWronskian,zeroSolution,zeroSlope]
  rw [zeroGreenConstant]
  exact (congrArg Complex.re hw).trans (congrArg Complex.re he)

/-- The actual selected-solution Green factor has exactly its original reference Fourier coefficient.
Use: zeroGreen_factorization invokes the proved complete reference Hilbert expansion and genuine continuous-function norm summability to identify the factor with the original Green series pointwise.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: split the genuine integral at s, reflect the right interval, and apply the independently proved zero-endpoint Green identity on each half. Exact solution and slope parity makes the two boundary terms combine into the actual positive constant W_0. -/
theorem zeroGreenFactor_coefficient {a s : ℝ} (ha : -1<a) (hs : s∈Ioo (0:ℝ) 1) (k : ℕ) :
    (jacobi.Bessel.phaseGrid a k)^2*
      (∫ t in (0:ℝ)..1,zeroGreenFactor a t s*eigenfunction a k t)=eigenfunction a k s := by
  -- Both integrals are genuine convergent integrals of the original continuous patched factor.
  let E := jacobi.Jacobi.endpointCorrection a
  have hc : ContinuousOn (fun t : ℝ => zeroGreenFactor a t s*eigenfunction a k t) (Icc (0:ℝ) 1) :=
    (zeroGreenFactor_continuousOn ha hs).mul (eigenfunction_properties ha k).1.continuousOn
  have hleft : (∫ t in (0:ℝ)..s,zeroGreenFactor a t s*eigenfunction a k t)=
      realSolution a E (1-s)/zeroGreenConstant a*
        (∫ t in (0:ℝ)..s,realSolution a (eigenvalue a k) t*realSolution a E t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [uIcc_of_le hs.1.le] at ht
    rw [zeroGreenFactor,min_eq_left ht.2,max_eq_right ht.2,realSolution_at_reference]
    ring
  have hright : (∫ t in s..1,zeroGreenFactor a t s*eigenfunction a k t)=
      realSolution a E s/zeroGreenConstant a*(-1:ℝ)^k*
        (∫ t in (0:ℝ)..(1-s),realSolution a (eigenvalue a k) t*realSolution a E t) := by
    rw [← intervalIntegral.integral_const_mul]
    have he : (∫ t in s..1,zeroGreenFactor a t s*eigenfunction a k t)=
        ∫ t in s..1,(realSolution a E s/zeroGreenConstant a*(-1:ℝ)^k)*
          (realSolution a (eigenvalue a k) (1-t)*realSolution a E (1-t)) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [uIcc_of_le hs.2.le] at ht
      rw [zeroGreenFactor,min_eq_right ht.1,max_eq_left ht.1,realSolution_at_reference,
        eigenfunction_reflection ha]
      have heven : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
      dsimp [E]
      linear_combination - (realSolution a (jacobi.Jacobi.endpointCorrection a) s/zeroGreenConstant a*
        eigenfunction a k t*realSolution a (jacobi.Jacobi.endpointCorrection a) (1-t))*heven
    rw [he]
    simpa only [sub_self,sub_zero] using
      intervalIntegral.integral_comp_sub_left
        (fun x : ℝ => (realSolution a E s/zeroGreenConstant a*(-1:ℝ)^k)*
          (realSolution a (eigenvalue a k) x*realSolution a E x)) (a := s) (b := 1) 1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    ((hc.mono (Icc_subset_Icc le_rfl hs.2.le)).intervalIntegrable_of_Icc hs.1.le)
    ((hc.mono (Icc_subset_Icc hs.1.le le_rfl)).intervalIntegrable_of_Icc hs.2.le),hleft,hright]
  have hL := reference_zero_green_identity ha k hs
  have hr : 1-s∈Ioo (0:ℝ) 1 := ⟨by linarith [hs.2],by linarith [hs.1]⟩
  have hR := reference_zero_green_identity ha k hr
  have hW := zeroGreenConstant_at ha hs
  simp only [realSolution_at_reference,eigenfunction_reflection ha,
    realSlope_reference_reflection ha k hs] at hL hR
  have hp : (-1:ℝ)^k*(-1:ℝ)^k=1 := by rw [← mul_pow]; norm_num
  have hWne := (zeroGreenConstant_pos ha).ne'
  dsimp only [E]
  simp only [realSolution_at_reference]
  field_simp [hWne]
  linear_combination
    realSolution a (jacobi.Jacobi.endpointCorrection a) (1-s)*hL+
    realSolution a (jacobi.Jacobi.endpointCorrection a) s*(-1:ℝ)^k*hR+
    eigenfunction a k s*hW+
    (realSolution a (jacobi.Jacobi.endpointCorrection a) s*eigenfunction a k s*
      realSlope a (jacobi.Jacobi.endpointCorrection a) (1-s)+
    realSolution a (jacobi.Jacobi.endpointCorrection a) s*realSolution a (jacobi.Jacobi.endpointCorrection a) (1-s)*
      realSlope a (eigenvalue a k) s)*hp

end
end jacobi.Reference
