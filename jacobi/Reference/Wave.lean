import jacobi.Reference.Hypergeometric
import jacobi.Reference.EigenEquation
import jacobi.Reference.Coordinate
import Mathlib.Analysis.Complex.RealDeriv

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The original hypergeometric reference solution is realized with a complex
frequency omega and spectral value c_0alpha+omega^2. Its spatial argument
is the actual physical cosine coordinate, inside the genuine convergence
disk. Frequency reflection leaves the solution unchanged.
Use: its genuine Gauss equation gives the original reference Schrodinger equation for every complex spectral parameter.
-/
namespace jacobi.Reference
noncomputable section
open Real Set Complex
set_option backward.isDefEq.respectTransparency false

/-- The actual community hypergeometric factor of the source reference solution.
Use: its genuine Gauss equation gives the original reference Schrodinger equation for every complex spectral parameter.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def waveCore (a : ℝ) (omega : ℂ) : ℂ → ℂ :=
  ordinaryHypergeometric ((gamma a:ℂ)-omega/(Real.pi:ℂ)) ((gamma a:ℂ)+omega/(Real.pi:ℂ)) ((gamma a:ℂ)+1/2)

/-- The original reference solution in its frequency coordinate, using the source's actual hypergeometric formula.
Use: supplies the reference functions at arbitrary complex energy in the GL kernel and transformed equation.
Article: jacobi, Appendix C.1 (negative-energy bounds).
-/
def wave (a : ℝ) (omega : ℂ) (t : ℝ) : ℂ := (weight a t:ℂ)*waveCore a omega (coordinate t:ℂ)

/-- The source reference frequency solution is even in its complex frequency.
Use: permits interpretation as a function of the true spectral parameter c_0alpha+omega^2 independent of the square-root choice.
Article: jacobi, Lemma C.1.
Proof: frequency reflection exchanges the two actual numerator parameters, and the community hypergeometric series is symmetric in them. -/
theorem wave_even (a : ℝ) (omega : ℂ) (t : ℝ) : wave a (-omega) t=wave a omega t := by
  have h := congrArg FormalMultilinearSeries.sum
    (ordinaryHypergeometricSeries_symm (𝔸 := ℂ) ((gamma a:ℂ)-omega/(Real.pi:ℂ)) ((gamma a:ℂ)+omega/(Real.pi:ℂ)) ((gamma a:ℂ)+1/2))
  have hp : (gamma a:ℂ)-(-omega)/(Real.pi:ℂ)=(gamma a:ℂ)+omega/(Real.pi:ℂ) := by ring
  have hm : (gamma a:ℂ)+(-omega)/(Real.pi:ℂ)=(gamma a:ℂ)-omega/(Real.pi:ℂ) := by ring
  unfold wave waveCore
  rw [hp,hm]
  exact congrArg (fun f : ℂ → ℂ => (weight a t:ℂ)*f (coordinate t:ℂ)) h.symm

/-- Every physical reference coordinate lies strictly inside the actual complex hypergeometric convergence disk.
Use: all genuine complex derivative and Gauss-equation theorems apply at the original spatial arguments.
Article: jacobi, Appendix C.1 (negative-energy bounds).
Proof: cosine is strictly greater than minus one before pi, and the original shifted coordinate is nonnegative. -/
theorem coordinate_norm_lt_one {t : ℝ} (ht : t∈Ioo 0 1) : ‖(coordinate t:ℂ)‖<1 := by
  have htheta : Real.pi*t∈Icc 0 Real.pi := ⟨(mul_pos Real.pi_pos ht.1).le,by nlinarith [Real.pi_pos,ht.2]⟩
  have hcos := Real.strictAntiOn_cos htheta ⟨Real.pi_pos.le,le_rfl⟩ (show Real.pi*t<Real.pi by nlinarith [Real.pi_pos,ht.2])
  rw [Real.cos_pi] at hcos
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (coordinate_properties.2.2 t).1]
  dsimp [coordinate]
  linarith

/-- The actual reference core is analytic at each physical spatial argument, for every complex frequency.
Use: supplies the genuine first and second complex derivatives in the original reference equation.
Article: jacobi, Lemma C.1.
Proof: the actual coordinate is strictly inside the proved community convergence disk. -/
theorem waveCore_analytic (a : ℝ) (omega : ℂ) {t : ℝ} (ht : t∈Ioo 0 1) :
    AnalyticAt ℂ (waveCore a omega) (coordinate t:ℂ) := Hypergeometric.analytic (coordinate_norm_lt_one ht)

/-- The original physical core at its true reference frequency equals the actual normalized Jacobi polynomial.
Use: identifies the arbitrary-energy reference solution with the already proved complete original reference basis at its source spectral values.
Article: jacobi, Lemma C.1.
Proof: the first numerator parameter becomes minus the original degree;
the other numerator and denominator become the exact equal-parameter
Jacobi parameters. Reality identifies the actual real polynomial value. -/
theorem wave_at_reference (a : ℝ) (k : ℕ) (t : ℝ) :
    wave a ((Real.pi*((k:ℝ)+gamma a):ℝ):ℂ) t=(eigenfunction a k t:ℂ) := by
  -- The true original reference eigenfunctions are retained, including their actual endpoint normalization.
  have hreal := Complex.conj_eq_iff_re.mp (jacobi.Jacobi.normalized_conj (jacobiIndex a) (jacobiIndex a) (Real.cos (Real.pi*t)) k)
  have hangular : (jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t):ℂ)=
      jacobi.Jacobi.normalized (jacobiIndex a:ℂ) (jacobiIndex a:ℂ) k (Real.cos (Real.pi*t):ℂ) := by
    rw [jacobi.Jacobi.angular_eq_realNormalized,jacobi.Jacobi.realNormalized]
    exact hreal
  unfold wave eigenfunction
  rw [show ((weight a t* jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t):ℝ):ℂ)=
    (weight a t:ℂ)*(jacobi.Jacobi.angular (jacobiIndex a) (jacobiIndex a) k (Real.pi*t):ℂ) from Complex.ofReal_mul _ _,hangular]
  congr 1
  unfold waveCore jacobi.Jacobi.normalized
  have hpi : (Real.pi:ℂ)≠0 := by exact_mod_cast Real.pi_ne_zero
  have h1 : (gamma a:ℂ)-((Real.pi*((k:ℝ)+gamma a):ℝ):ℂ)/(Real.pi:ℂ)= -(k:ℂ) := by push_cast; field_simp [hpi]; ring
  have h2 : (gamma a:ℂ)+((Real.pi*((k:ℝ)+gamma a):ℝ):ℂ)/(Real.pi:ℂ)=
      (k:ℂ)+(jacobiIndex a:ℂ)+(jacobiIndex a:ℂ)+1 := by dsimp [jacobiIndex]; push_cast; field_simp [hpi]; ring
  have h3 : (gamma a:ℂ)+1/2=(jacobiIndex a:ℂ)+1 := by dsimp [jacobiIndex]; push_cast; ring
  rw [h1,h2,h3]
  congr 1
  dsimp [coordinate]
  push_cast
  rfl

end
end jacobi.Reference
