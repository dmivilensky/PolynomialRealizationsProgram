import jacobi.Variational.FredholmSpatialIntegral

/-!
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
The actual logarithmic spectral series converges and equals the spatial
integral of 1-1/(2g). Adding back the exact trace s*mass to the proved
regularized determinant identity gives this printed companion formula.
Source: the actual spectral mass trace and absolutely convergent sum and integral algebra.
Use: supplies the unregularized determinant identity preceding equation (Dg).
-/
namespace jacobi.Variational
noncomputable section
open MeasureTheory Real chebyshev2.Continuum
set_option backward.isDefEq.respectTransparency false

/-- The actual logarithmic determinant series converges and has the printed exact Green-diagonal integral.
Use: supplies the unregularized determinant identity preceding equation (Dg).
Article: jacobi, Appendix D.4 (green diagonal and determinant identities).
Proof: each negative logarithm is its regularized term plus s*lambda.
Both spectral series converge. The true spectral trace equals the density
mass; add the same integrable s*m to the proved spatial regularized identity. -/
theorem L1Source.green_log_determinant (m : L1Source) (hc : Continuous m.value) {s : ℝ}
    (hs : 0≤s) (hp : s*observe m .top<1) :
    Summable (fun n => -log (1-s*m.spectrum n)) ∧
      Integrable (fun x => 1-(2*m.fredholmGreen s hs hp x x)⁻¹) ∧
      -(∑' n,log (1-s*m.spectrum n))=
        (∫ x,1-(2*m.fredholmGreen s hs hp x x)⁻¹) := by
  -- Restore the actual first spectral moment on both convergent sides of (Dg).
  have he (n : ℕ) : -log (1-s*m.spectrum n)=fredholmLog s (m.spectrum n)+s*m.spectrum n := by
    unfold fredholmLog
    ring
  have hfs := fredholmLog_summable hs (sub_pos.mpr hp)
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable
    (kernelSpectralData m.integrable m.nonneg).eigenvalue_nonneg
    (m.spectral_margin hs (by linarith : s*observe m .top≤1-(1-s*observe m .top)))
  have hlin := (kernelSpectralData m.integrable m.nonneg).eigenvalue_summable.mul_left s
  change Summable (fun n => fredholmLog s (m.spectrum n)) at hfs
  change Summable (fun n => s*m.spectrum n) at hlin
  have hlog : Summable (fun n => -log (1-s*m.spectrum n)) := by
    simpa only [he] using hfs.add hlin
  obtain ⟨hFi,hFeq,_⟩ := m.fredholm_spatial_integral hc hs hp
  have hadd : (fun x => 1-(2*m.fredholmGreen s hs hp x x)⁻¹)=
      fun x => (1-(2*m.fredholmGreen s hs hp x x)⁻¹-s*m.value x)+s*m.value x := by
    funext x
    ring
  refine ⟨hlog,?_,?_⟩
  · rw [hadd]
    exact hFi.add (m.integrable.const_mul s)
  · rw [← tsum_neg,hadd,integral_add hFi (m.integrable.const_mul s),← hFeq]
    simp_rw [he]
    rw [hfs.tsum_add hlin,tsum_mul_left,integral_const_mul,
      show (∑' n,m.spectrum n)=∫ x,m.value x from kernelEigenvalue_mass m.integrable m.nonneg]
    rfl

end
end jacobi.Variational
