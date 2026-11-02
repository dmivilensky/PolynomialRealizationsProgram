import jacobi.Support.Parameters

/-!
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
The actual printed affine correction has positive scale at every
nonempty original dimension, not only eventually. Its exact endpoint
corrections and parameter exchange retain the original two-edge model.
Use: supportChain has precisely its genuine original affine-image matrix and strictly positive couplings, without a large-degree qualification.
-/
namespace jacobi.Support
noncomputable section
open Real jacobi.Reference

/-- The original affine cosine correction scale is positive for every nonempty finite original Jacobi family.
Use: supportChain has precisely its genuine original affine-image matrix and strictly positive couplings, without a large-degree qualification.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the actual frequency satisfies 2*N>=alpha+beta+3>0. The numerator at the smallest degree is a sum of three genuine squares plus 5/2; increasing N preserves the strict bound. -/
theorem modelScale_pos {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    0< jacobi.Jacobi.modelScale a b n := by
  -- Keep the original two-edge correction; positivity follows from its actual formula throughout the full parameter range.
  have hN := jacobi.Jacobi.frequency_pos ha hb hn
  have hnR : (1:ℝ)≤n := by exact_mod_cast hn
  have hNge : a+b+3≤2* jacobi.Jacobi.frequency a b n := by
    dsimp [jacobi.Jacobi.frequency]
    linarith
  have hbase : 0<a+b+3 := by linarith
  have hsq : (a+b+3)^2≤4*(jacobi.Jacobi.frequency a b n)^2 := by nlinarith
  have hnum : jacobi.Jacobi.endpointCorrection a+ jacobi.Jacobi.endpointCorrection b<
      4*(jacobi.Jacobi.frequency a b n)^2 := by
    dsimp [jacobi.Jacobi.endpointCorrection]
    nlinarith [sq_nonneg (a+1),sq_nonneg (b+1),sq_nonneg (a+b+2)]
  unfold jacobi.Jacobi.modelScale
  exact sub_pos.mpr ((div_lt_one (by positivity : 0<4*(jacobi.Jacobi.frequency a b n)^2)).mpr hnum)

/-- The genuine original affine correction has the exact original right-endpoint spectral shift.
Use: the support edge limit identifies the actual corrected natural frequencies with the genuine reference tau spectrum.
Article: jacobi, Appendix C.3 (support weights and segment bounds).
Proof: substitute the literal original two-edge scale and shift and cancel their genuine nonzero frequency denominator. -/
theorem affine_endpoint_correction {a b : ℝ} (ha : -1<a) (hb : -1<b) {n : ℕ} (hn : 0<n) :
    2*(jacobi.Jacobi.frequency a b n)^2*(1- jacobi.Jacobi.modelScale a b n- jacobi.Jacobi.modelShift a b n)=
      jacobi.Jacobi.endpointCorrection a := by
  unfold jacobi.Jacobi.modelScale jacobi.Jacobi.modelShift
  field_simp [(jacobi.Jacobi.frequency_pos ha hb hn).ne']
  ring

/-- Exchanging the original endpoint indices leaves the actual affine scale unchanged and negates its genuine shift.
Use: the original support parameter reflection and opposite-edge Gram contribution use exactly the source's affine correction.
Article: jacobi, Appendix C.3 (complex edge-wave convergence).
Proof: the frequency and correction sum are symmetric, whereas the correction difference changes sign. -/
theorem affine_swap (a b : ℝ) (n : ℕ) :
    jacobi.Jacobi.modelScale b a n= jacobi.Jacobi.modelScale a b n ∧
      jacobi.Jacobi.modelShift b a n= - jacobi.Jacobi.modelShift a b n := by
  have hfreq : jacobi.Jacobi.frequency b a n= jacobi.Jacobi.frequency a b n := by
    unfold jacobi.Jacobi.frequency
    ring
  simp only [jacobi.Jacobi.modelScale,jacobi.Jacobi.modelShift,hfreq]
  constructor <;> ring

end
end jacobi.Support
