import jacobi.Reference.HilbertBasis

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
The original reference coefficients are actual spatial integrals against
the true Gegenbauer functions. Their squared norming-weighted sum equals
the genuine Lebesgue L2 norm for every original L2 vector. This uses the
already proved complete reference basis, without a completeness premise.
Use: supplies the true source V(tau_k) in the Parseval and GL quadratic identities.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual original reference coefficient integral of an arbitrary genuine L2 vector.
Use: supplies the true source V(tau_k) in the Parseval and GL quadratic identities.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def referenceCoefficient (a : ℝ) (k : ℕ) (v : Space) : ℝ :=
  ∫ t:Interval,v t*eigenfunction a k t

/-- The genuine source coefficient integral is exactly the Hilbert inner product with the original reference vector.
Use: transfers the complete actual reference Hilbert basis expansion to the literal source coefficient integrals.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the L2 inner product is its original integral. Replace the actual reference vector by its proved genuine eigenfunction representative almost everywhere. -/
theorem referenceCoefficient_inner (a : ℝ) (ha : -1<a) (k : ℕ) (v : Space) :
    referenceCoefficient a k v=inner ℝ (waveVector a ha k) v := by
  rw [L2.inner_def]
  unfold referenceCoefficient
  apply integral_congr_ae
  filter_upwards [waveVector_ae a ha k] with t ht
  rw [ht]
  rfl

/-- The actual original reference coefficient squares divided by their genuine positive norming integrals have sum equal to the true L2 norm square.
Use: supplies the unconditional original Parseval identity for every L2 vector in the GL quadratic form proof.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: apply the community Parseval series theorem to the genuine
complete original reference Hilbert basis. Identify its entries with
the actual reference vectors divided by their positive square-root
norming constants, then use the exact original coefficient integrals. -/
theorem reference_parseval_hasSum (a : ℝ) (ha : -1<a) (v : Space) :
    HasSum (fun k => (referenceCoefficient a k v)^2/norming a k) (‖v‖^2) := by
  -- Completeness and every normalizing integral were proved for the actual original reference system.
  have hh := (hilbertBasis a ha).hasSum_inner_mul_inner v v
  have he (k : ℕ) : inner ℝ v (hilbertBasis a ha k)*inner ℝ (hilbertBasis a ha k) v=
      (referenceCoefficient a k v)^2/norming a k := by
    have hvcoef : inner ℝ v (waveVector a ha k)=referenceCoefficient a k v := by
      calc
        _ = inner ℝ (waveVector a ha k) v := real_inner_comm _ _
        _ = _ := (referenceCoefficient_inner a ha k v).symm
    rw [hilbertBasis_apply,normalizedWave,real_inner_smul_left,real_inner_smul_right]
    simp only [hvcoef,← referenceCoefficient_inner]
    have hp := norming_pos ha k
    have hs := Real.sq_sqrt hp.le
    field_simp [(Real.sqrt_pos.mpr hp).ne',hp.ne']
    nlinarith [congrArg (fun x:ℝ => (referenceCoefficient a k v)^2*x) hs]
  simpa only [he,real_inner_self_eq_norm_sq] using hh

/-- The genuine original reference Parseval series is summable for every actual original L2 vector.
Use: the GL quadratic identity may add this convergent true reference series to the uniformly convergent kernel correction.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the actual reference coefficient series has the proved genuine L2 norm square as its sum. -/
theorem reference_parseval_summable (a : ℝ) (ha : -1<a) (v : Space) :
    Summable (fun k => (referenceCoefficient a k v)^2/norming a k) :=
  (reference_parseval_hasSum a ha v).summable

end
end jacobi.Reference
