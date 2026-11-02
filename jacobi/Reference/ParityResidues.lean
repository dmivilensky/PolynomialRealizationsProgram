import jacobi.Reference.NormingSigns
import jacobi.GelfandLevitan.KernelTerm

/-!
Article: jacobi, Appendix C.2 (exact parity splitting).
The actual simple-pole residues of the two original characteristic
quotients differ by exactly the original signed GL summand, with
the printed kappa normalization and the zero-based index sign.
Use: parity_residue_term converts both proved original norming-weight identities to the actual residue difference.
-/
namespace jacobi.Reference
noncomputable section
open Real _root_.Complex
set_option backward.isDefEq.respectTransparency false

/-- A signed reciprocal derivative coefficient gives its genuine simple-pole residue with the exact involutive sign.
Use: parity_residue_term converts both proved original norming-weight identities to the actual residue difference.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: the signed power has square one; multiply the exact reciprocal coefficient by that same sign and cancel the two nonzero scalar factors. -/
theorem signed_residue_coefficient {w d kappa v : ℂ} (k : ℕ)
    (hkappa : kappa≠0) (hd : d≠0) (hw : w=(-1:ℂ)^(k+1)/(kappa*d)) :
    v/d=kappa*(-1:ℂ)^(k+1)*w*v := by
  have hs : (-1:ℂ)^(k+1)*(-1:ℂ)^(k+1)=1 := by rw [← mul_pow]; simp
  rw [hw]
  calc
    _ = ((-1:ℂ)^(k+1)*(-1:ℂ)^(k+1))*v/d := by rw [hs,one_mul]
    _ = _ := by field_simp [hkappa,hd]

/-- The actual difference of the target and reference simple-pole residues is exactly minus kappa times the original signed kernel summand.
Use: parity_contour_residue_identity sums these genuine residues in their original spectral order and then uses their vanishing contour limit.
Article: jacobi, Appendix C.2 (exact parity splitting).
Proof: apply both proved exact signed norming formulas, use reality of the original reference solution at both actual energies, and regroup the result into the defining GL summand. -/
theorem parity_residue_term {a : ℝ} (ha : -1<a) (k : ℕ) (t s : ℝ) :
    (solution a (jacobi.Bessel.sigma a ha k:ℂ) t*solution a (jacobi.Bessel.sigma a ha k:ℂ) s)/
        deriv (characteristicSigma a) (jacobi.Bessel.sigma a ha k:ℂ)-
      (solution a (eigenvalue a k:ℂ) t*solution a (eigenvalue a k:ℂ) s)/
        deriv (characteristicTau a) (eigenvalue a k:ℂ)=
      -((2*Real.pi^2*normConstant a:ℝ):ℂ)*
        ((((-1:ℝ)^k* jacobi.GelfandLevitan.kernelTerm a ha k t s:ℝ):ℂ)) := by
  -- All residue denominators are the actual derivatives at the original simple characteristic zeros.
  let kappa : ℂ := ((2*Real.pi^2*normConstant a:ℝ):ℂ)
  have hkappa : kappa≠0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (by positivity [normConstant_pos ha]))
  have hSigma := characteristicSigma_simple ha ((characteristicSigma_zero_iff ha _).mpr ⟨k,rfl⟩)
  have hTau := characteristicTau_simple ha ((characteristicTau_zero_iff a _).mpr ⟨k,rfl⟩)
  have hS := signed_residue_coefficient k hkappa hSigma (norming_signed_bessel ha k)
    (v := solution a (jacobi.Bessel.sigma a ha k:ℂ) t*solution a (jacobi.Bessel.sigma a ha k:ℂ) s)
  have hT := signed_residue_coefficient k hkappa hTau (norming_signed_reference ha k)
    (v := solution a (eigenvalue a k:ℂ) t*solution a (eigenvalue a k:ℂ) s)
  have hr (E u : ℝ) : (realSolution a E u:ℂ)=solution a (E:ℂ) u := solution_real a E u
  have hterm : (jacobi.GelfandLevitan.kernelTerm a ha k t s:ℂ)=
      ((normingRatio a ha k/norming a k:ℝ):ℂ)*
        (solution a (jacobi.Bessel.sigma a ha k:ℂ) t*solution a (jacobi.Bessel.sigma a ha k:ℂ) s)-
      ((1/norming a k:ℝ):ℂ)*(solution a (eigenvalue a k:ℂ) t*solution a (eigenvalue a k:ℂ) s) := by
    rw [jacobi.GelfandLevitan.kernelTerm]
    push_cast
    simp only [hr]
    ring
  rw [hS,hT]
  push_cast
  rw [hterm,pow_succ]
  dsimp only [kappa]
  push_cast
  ring

end
end jacobi.Reference
