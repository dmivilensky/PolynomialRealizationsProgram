import jacobi.Reference.SpectralSeries

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The actual spectral polynomial coefficients commute with conjugation.
Thus the original arbitrary-energy function satisfies Schwarz reflection,
and every original real-energy reference value is genuinely real.
Use: proves reality of the actual source kernel data without imposing a square-root branch restriction.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
open scoped ComplexConjugate

/-- The true reference energy coefficient commutes with complex conjugation.
Use: proves reality of the actual source kernel data without imposing a square-root branch restriction.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: conjugate the genuine finite energy polynomial product. Every source parameter and fixed denominator is real, and conjugation commutes with all finite products. -/
theorem energyCoefficient_conj (a : ℝ) (n : ℕ) (z : ℂ) :
    conj (energyCoefficient a n z)=energyCoefficient a n (conj z) := by
  unfold energyCoefficient
  simp only [_root_.map_mul,_root_.map_inv₀,_root_.map_prod,_root_.map_sub,
    _root_.map_div₀,_root_.map_pow,_root_.map_add,conj_natCast,conj_ofReal,
    jacobi.Jacobi.pochhammer_conj,_root_.map_one,conj_ofNat]

/-- The original reference solution satisfies genuine Schwarz reflection at every spatial point and complex energy.
Use: shows all actual real-energy GL data are real, even when the reference energy itself is negative.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
Proof: conjugate the actual square-root-free energy series. Conjugation
commutes with the genuine infinite sum, and the finite polynomial
coefficient identity gives the reflected energy term by term. -/
theorem solution_conj (a : ℝ) (z : ℂ) (t : ℝ) :
    conj (solution a z t)=solution a (conj z) t := by
  -- No positivity of the original reference eigenvalues is assumed or needed.
  rw [solution_eq_energy_series,solution_eq_energy_series]
  simp only [_root_.map_mul,conj_ofReal,Complex.conj_tsum,energyCoefficient_conj,_root_.map_pow]

/-- The original reference solution at a real source energy is genuinely real, throughout its actual spatial definition.
Use: justifies the real quadratic forms and positive spectral weights in the original GL positivity identity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: Schwarz reflection fixes a real energy; the community fixed-conjugation characterization identifies the value with its actual real part. -/
theorem solution_real (a E t : ℝ) : ((solution a (E:ℂ) t).re:ℂ)=solution a (E:ℂ) t := by
  exact Complex.conj_eq_iff_re.mp (by simpa only [conj_ofReal] using solution_conj a (E:ℂ) t)

end
end jacobi.Reference
