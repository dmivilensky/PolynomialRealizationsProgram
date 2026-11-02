import jacobi.Support.EdgeLimit
import jacobi.Support.AffinePolynomials
import jacobi.Reference.SpectralSolutions

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Use: correctedEdgeEnergy_limit and supportPolynomial_edge apply the genuine complex finite edge theorem to the same corrected polynomials occurring in the actual target Gram matrix.
-/
namespace jacobi.Support
noncomputable section
open Real Set Filter Polynomial jacobi.Reference
open scoped Topology

/-- The exact original natural scaled energy corresponding to a corrected support spectral point.
Use: correctedEdgeEnergy_limit and supportPolynomial_edge apply the genuine complex finite edge theorem to the same corrected polynomials occurring in the actual target Gram matrix.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
-/
def correctedEdgeEnergy (a b:ℝ) (n:ℕ) (x:ℝ) : ℝ :=
  2*(jacobi.Jacobi.frequency a b (n+1))^2*
    (1-(x- jacobi.Jacobi.modelShift a b (n+1))/ jacobi.Jacobi.modelScale a b (n+1))

/-- The actual corrected energy is exactly the printed affine quotient at every original finite dimension.
Use: correctedEdgeEnergy_limit discharges the full affine correction in the actual fixed-edge Gram terms before taking limits.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: multiply by the genuinely positive original affine scale. The residual equality is exactly the already proved original endpoint correction identity. -/
theorem correctedEdgeEnergy_eq {a b:ℝ} (ha:-1<a) (hb:-1<b) (n:ℕ) (x:ℝ) :
    correctedEdgeEnergy a b n x=
      (2*(jacobi.Jacobi.frequency a b (n+1))^2*(1-x)- jacobi.Jacobi.endpointCorrection a)/
        jacobi.Jacobi.modelScale a b (n+1) := by
  have hc := modelScale_pos ha hb (by omega : 0<n+1)
  have he := affine_endpoint_correction ha hb (by omega : 0<n+1)
  unfold correctedEdgeEnergy
  field_simp [hc.ne']
  linear_combination -he

/-- A convergent actual corrected spectral energy has its exact natural-energy limit after the original affine substitution.
Use: supportPolynomial_edge specializes the proved full complex polynomial theorem to the true support or target energies, without assuming a natural-coordinate limit separately.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: use the exact finite affine quotient, the given original corrected energy limit and the proved actual scale limit one. -/
theorem correctedEdgeEnergy_limit {a b:ℝ} (ha:-1<a) (hb:-1<b) {x:ℕ→ℝ} {E:ℝ}
    (hx:Tendsto (fun n => 2*(jacobi.Jacobi.frequency a b (n+1))^2*(1-x n)) atTop (𝓝 E)) :
    Tendsto (fun n => correctedEdgeEnergy a b n (x n)) atTop
      (𝓝 (E- jacobi.Jacobi.endpointCorrection a)) := by
  have hscale := (jacobi.Jacobi.modelScale_tendsto a b).comp (tendsto_add_atTop_nat 1)
  have h := (hx.sub_const (jacobi.Jacobi.endpointCorrection a)).div hscale one_ne_zero
  change Tendsto (fun n => (2*(jacobi.Jacobi.frequency a b (n+1))^2*(1-x n)-
    jacobi.Jacobi.endpointCorrection a)/ jacobi.Jacobi.modelScale a b (n+1)) atTop
    (𝓝 ((E- jacobi.Jacobi.endpointCorrection a)/1)) at h
  simpa only [div_one,correctedEdgeEnergy_eq ha hb] using h

/-- The true corrected support polynomials have their uniform real edge limit at every convergent corrected energy, with the actual source amplitude.
Use: the original target and support node energy limits give the actual fixed-index limits of every Gram summand. Their actual probability limits cancel this exact original amplitude and yield the original kernelTerm.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the exact affine energy has its proved original limit. Apply the full complex finite edge theorem, identify the actual natural wave at its real affine input with the genuine real polynomial evaluation, and project the actual error to its real part. The c_0 correction cancels exactly. -/
theorem supportPolynomial_edge {a b:ℝ} (ha:-1<a) (hb:-1<b) {x:ℕ→ℝ} {E:ℝ}
    (hx:Tendsto (fun n => 2*(jacobi.Jacobi.frequency a b (n+1))^2*(1-x n)) atTop (𝓝 E)) :
    ∀ε:ℝ,0<ε→∃n₀:ℕ,∀n≥n₀,∀i:Fin (n+1),2*i.val≤n+1→
      |(n:ℝ)^(-gamma a)*(supportPolynomial a b ha hb n i).eval (x n)-
        (topConstant a b*π^gamma a)*realSolution a E ((i.val:ℝ)/(n:ℝ))|<ε := by
  -- Apply the full complex theorem after proving the original affine energy limit.
  have hz := Complex.continuous_ofReal.continuousAt.tendsto.comp (correctedEdgeEnergy_limit ha hb hx)
  have h := naturalWave_complex_edge ha hb hz
  simp only [Function.comp_def,Complex.ofReal_sub,sub_add_cancel] at h
  intro ε hε
  obtain ⟨N,hN⟩ := h ε hε
  refine ⟨N,?_⟩
  intro n hn i hi
  have hF : (jacobi.Jacobi.frequency a b (n+1):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (jacobi.Jacobi.frequency_pos ha hb (by omega)).ne'
  have hy : 1-(correctedEdgeEnergy a b n (x n):ℂ)/(2*(jacobi.Jacobi.frequency a b (n+1):ℂ)^2)=
      (((x n- jacobi.Jacobi.modelShift a b (n+1))/ jacobi.Jacobi.modelScale a b (n+1):ℝ):ℂ) := by
    dsimp only [correctedEdgeEnergy]
    push_cast
    field_simp [hF]
    ring
  have herr := hN n hn i.val hi
  -- Return to the genuine real corrected polynomial before projecting its error.
  rw [hy] at herr
  have hwave : naturalWave a b ha hb n i
      (((x n- jacobi.Jacobi.modelShift a b (n+1))/ jacobi.Jacobi.modelScale a b (n+1):ℝ):ℂ)=
      (((supportPolynomial a b ha hb n i).eval (x n):ℝ):ℂ) := by
    rw [supportPolynomial_eval]
    exact Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval _ _
  rw [hwave] at herr
  have hre := (Complex.abs_re_le_norm _).trans_lt herr
  simpa only [Complex.sub_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero,realSolution,mul_assoc] using hre

end
end jacobi.Support
