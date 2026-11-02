import jacobi.Reference.NormingBounds

/-!
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
The coefficient of the strengthened norming asymptotic is the actual
absolutely convergent sum of the original spectral displacements.
The same genuine leading phase controls its weighted summands.
Use: displacementMass is the actual leading coefficient in rho_k=1+s/varpi_k^2+O(k^-3 log k), and spectralPerturbation is the original factor perturbation.
-/
namespace jacobi.Reference
noncomputable section
open Real Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The genuine displacement between the original Bessel and reference eigenvalues.
Use: displacementMass is the actual leading coefficient in rho_k=1+s/varpi_k^2+O(k^-3 log k), and spectralPerturbation is the original factor perturbation.
Article: jacobi, Appendix C.1 (midpoint characteristics and negative-axis normalization).
-/
def spectralDisplacement (a : ℝ) (ha : -1<a) (k : ℕ) : ℝ :=
  jacobi.Bessel.sigma a ha k-eigenvalue a k

/-- The original spectral displacement series converges absolutely.
Use: displacementMass has genuine convergence evidence and can be split, rearranged and compared with the first-order norming correction.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: the proved actual McMahon remainder is bounded by the summable inverse-square positive-index series. -/
theorem spectralDisplacement_summable {a : ℝ} (ha : -1<a) :
    Summable (fun k : ℕ => |spectralDisplacement a ha k|) := by
  obtain ⟨C,hC,hbound⟩ := spectrum_error ha
  have hm : Summable (fun k : ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact hm.of_nonneg_of_le (fun _ => abs_nonneg _) hbound

/-- The actual complete displacement sum, rather than an assumed trace coefficient.
Use: defines the exact original coefficient subtracted in the regularized kernel F-flat and in the sharpened norming asymptotic.
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
-/
def displacementMass (a : ℝ) (ha : -1<a) : ℝ := ∑' k : ℕ,spectralDisplacement a ha k

/-- The genuine reference phases have positive linear lower and upper index bounds for every original spectral index.
Use: displacement_phase_bounds converts the weighted displacement and inverse phase into uniform index estimates in Structure of F (a).
Article: jacobi, Appendix C.2 (green part and regularized kernel series).
Proof: gamma>1/4 bounds k+gamma below by (k+1)/4 and above by (gamma+1)*(k+1); multiply by positive pi. -/
theorem reference_phase_bounds {a : ℝ} (ha : -1<a) :
    ∃ c C : ℝ,0<c ∧ 0<C ∧ ∀ k : ℕ,
      c*(k+1:ℝ)≤ jacobi.Bessel.phaseGrid a k ∧ jacobi.Bessel.phaseGrid a k≤C*(k+1:ℝ) := by
  -- These are bounds for the already fixed actual phase, not for a comparison sequence.
  have hg : 0<gamma a := by linarith [(parameters ha).1]
  refine ⟨Real.pi/4,Real.pi*(gamma a+1),by positivity,by positivity,fun k => ?_⟩
  have hk := Nat.cast_nonneg (α := ℝ) k
  rw [phaseGrid_eq]
  constructor
  · nlinarith [mul_nonneg Real.pi_pos.le (show 0≤(k:ℝ)+gamma a-(k+1:ℝ)/4 by linarith [(parameters ha).1])]
  · have hh := mul_nonneg hg.le hk
    calc
      _ ≤ Real.pi*((gamma a+1)*(k+1:ℝ)) := mul_le_mul_of_nonneg_left (by nlinarith) Real.pi_pos.le
      _ = _ := by ring

/-- The original weighted displacement is uniformly bounded, and the reciprocal squared reference phase has an inverse-square index bound.
Use: the exact first-order remainder identity reduces the strengthened norming asymptotic to the summable reciprocal-gap row estimate.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: combine the genuine inverse-square McMahon error with the two actual linear phase bounds, keeping all positive denominators before cancellation. -/
theorem displacement_phase_bounds {a : ℝ} (ha : -1<a) :
    ∃ B D : ℝ,0<B ∧ 0<D ∧ ∀ k : ℕ,
      |spectralDisplacement a ha k| * (jacobi.Bessel.phaseGrid a k)^2≤B ∧
      1/(jacobi.Bessel.phaseGrid a k)^2≤D/(k+1:ℝ)^2 := by
  -- The estimates cover the genuine finite small-index part as well as the asymptotic tail.
  obtain ⟨C,hC,he⟩ := spectrum_error ha
  obtain ⟨c,L,hc,hL,hphase⟩ := reference_phase_bounds ha
  refine ⟨C*L^2,1/c^2,by positivity,by positivity,fun k => ?_⟩
  have hk : 0<(k+1:ℝ) := by positivity
  have hv : 0< jacobi.Bessel.phaseGrid a k := jacobi.Bessel.phaseGrid_pos ha k
  have hupper := (sq_le_sq₀ hv.le (by positivity : 0≤L*(k+1:ℝ))).mpr (hphase k).2
  have hlower := (sq_le_sq₀ (by positivity : 0≤c*(k+1:ℝ)) hv.le).mpr (hphase k).1
  constructor
  · exact (mul_le_mul (he k) hupper (sq_nonneg _) (by positivity)).trans_eq (by field_simp)
  · apply (div_le_div_iff₀ (sq_pos_of_pos hv) (sq_pos_of_pos hk)).mpr
    have hh := mul_le_mul_of_nonneg_left hlower (show 0≤1/c^2 by positivity)
    rw [mul_pow,show (1/c^2)*(c^2*(k+1:ℝ)^2)=(k+1:ℝ)^2 by field_simp] at hh
    simpa only [one_mul] using hh

/-- The original first-order factor perturbation, with its omitted diagonal equal to zero.
Use: norming logarithm linearization and its complete first-order sum retain precisely the article's epsilon_(k,l).
Article: jacobi, Appendix C.2 (norming ratios).
-/
def spectralPerturbation (a : ℝ) (ha : -1<a) (k l : ℕ) : ℝ :=
  (spectralDisplacement a ha l-spectralDisplacement a ha k)/(eigenvalue a l-eigenvalue a k)

/-- The original norming factor is exactly the reciprocal of one plus its genuine first-order spectral perturbation, including the omitted diagonal convention.
Use: the logarithm of the actual norming product is linearized through the same epsilon used in Structure of F (a).
Article: jacobi, Appendix C.2 (norming ratios).
Proof: off the diagonal the nonzero reference gap clears the quotient and the two actual displacements cancel; on the diagonal both prescribed values are one. -/
theorem normingFactor_perturbation {a : ℝ} (ha : -1<a) (k l : ℕ) :
    normingFactor a ha k l=(1+spectralPerturbation a ha k l)⁻¹ := by
  classical
  -- Both conventions agree on the diagonal, and strict spectral order excludes the off-diagonal reference zero.
  by_cases h : l=k
  · subst l
    simp [normingFactor,spectralPerturbation]
  · have hgap : eigenvalue a l-eigenvalue a k≠0 := sub_ne_zero.mpr
      (fun he => h ((eigenvalue_strictMono ha).injective he))
    simp only [normingFactor,h,ite_false,spectralPerturbation,spectralDisplacement]
    field_simp [hgap]
    ring

end
end jacobi.Reference
