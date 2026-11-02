import jacobi.Reference.PolynomialDensity

/-!
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
The source reference eigenfunctions divided by their genuine L2 norms
form a complete orthonormal Hilbert basis. Completeness uses uniform
coordinate-polynomial density and the onto weighted-L2 unitary already
proved in chebyshev2. All representatives are the original functions.
Use: transports the proved dense polynomial system to the source reference waves without repeating weighted L2 analysis.
-/
namespace jacobi.Reference
noncomputable section
open Real Set MeasureTheory Polynomial
open scoped Topology
attribute [local instance] Measure.Subtype.measureSpace
set_option backward.isDefEq.respectTransparency false

/-- The actual reference polynomial map into Lebesgue L2, via the earlier article's genuine onto weight unitary.
Use: transports the proved dense polynomial system to the source reference waves without repeating weighted L2 analysis.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def polynomialL2 (a : ℝ) (ha : -1<a) : Polynomial ℝ →ₗ[ℝ] Space :=
  (weightUnitary a ha).toLinearMap.comp (polynomialWeightedL2 a ha)

/-- The actual transported reference polynomial map has dense range in the whole original Lebesgue Hilbert space.
Use: proves completeness of the source reference system after the genuine degree-graded polynomial spanning theorem.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: compose the dense coordinate-polynomial map with the already proved onto continuous weight unitary. -/
theorem polynomialL2_denseRange (a : ℝ) (ha : -1<a) : DenseRange (polynomialL2 a ha) :=
  ((weightUnitary a ha).surjective.denseRange).comp (polynomialWeightedL2_denseRange a ha) (weightUnitary a ha).continuous

/-- Every transported reference polynomial has its literal sine-power times polynomial representative almost everywhere in Lebesgue measure.
Use: identifies the constructed L2 vectors with the actual reference functions before proving orthogonality or completeness.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: reuse the earlier article's genuine multiplication representative and its absolute-continuity transfer of the weighted polynomial representative. -/
theorem polynomialL2_ae (a : ℝ) (ha : -1<a) (p : Polynomial ℝ) :
    polynomialL2 a ha p=ᵐ[volume] fun t : Interval => weight a t*p.eval (coordinate t) := by
  -- The weighted and unweighted measures have the same null sets, as proved by the reused general multiplier theorem.
  have hm := (hilbertWeight a ha).mul_ae (polynomialWeightedL2 a ha p)
  have hp := (hilbertWeight a ha).base_ac.ae_eq (polynomialWeightedL2_ae a ha p)
  filter_upwards [hm,hp] with t hm hp
  change (hilbertWeight a ha).mul (polynomialWeightedL2 a ha p) t=weight a t*p.eval (coordinate t)
  rw [hm,hp]
  rfl

/-- The original reference eigenfunction as an actual Lebesgue L2 vector.
Use: supplies the complete reference spectral basis and Parseval expansion used in the GL positivity proof.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def waveVector (a : ℝ) (ha : -1<a) (k : ℕ) : Space :=
  polynomialL2 a ha (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a) k)

/-- The original reference vector has precisely its genuine pointwise reference eigenfunction as representative almost everywhere.
Use: all Hilbert-space orthogonality and Parseval statements concern the source's actual functions.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: substitute the actual Jacobi polynomial into the proved transported polynomial representative. -/
theorem waveVector_ae (a : ℝ) (ha : -1<a) (k : ℕ) :
    waveVector a ha k=ᵐ[volume] fun t : Interval => eigenfunction a k t := polynomialL2_ae a ha _

/-- Inner products of actual reference vectors equal their original convergent spatial integrals.
Use: obtains the genuine normalized orthonormal reference system from the already proved integral orthogonality and norm values.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: replace both vectors by their proved actual representatives and identify the subtype Lebesgue integral with the original interval integral. -/
theorem waveVector_inner (a : ℝ) (ha : -1<a) (i j : ℕ) :
    inner ℝ (waveVector a ha i) (waveVector a ha j)=
      ∫ t in (0:ℝ)..1,eigenfunction a i t*eigenfunction a j t := by
  -- The two endpoint values are null, so the compact subtype is the same original L2 interval.
  rw [L2.inner_def]
  have he : (fun t : Interval => inner ℝ (waveVector a ha i t) (waveVector a ha j t))=ᵐ[volume]
      fun t : Interval => eigenfunction a i t*eigenfunction a j t := by
    filter_upwards [waveVector_ae a ha i,waveVector_ae a ha j] with t hi hj
    rw [hi,hj]
    change eigenfunction a j t*eigenfunction a i t=eigenfunction a i t*eigenfunction a j t
    ring
  rw [integral_congr_ae he,integral_subtype (s := Icc (0:ℝ) 1) measurableSet_Icc
    (fun t : ℝ => eigenfunction a i t*eigenfunction a j t)]
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),← integral_Icc_eq_integral_Ioc]

/-- The actual original reference vector normalized by its genuine positive norming integral.
Use: constructs the full orthonormal reference Hilbert basis and the original Parseval identity.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def normalizedWave (a : ℝ) (ha : -1<a) (k : ℕ) : Space :=
  (Real.sqrt (norming a k))⁻¹ • waveVector a ha k

/-- The genuine normalized source reference vectors form an orthonormal system in the original Lebesgue Hilbert space.
Use: together with proved dense span, supplies the actual complete reference basis for the GL construction.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the actual vector inner products are the proved original spatial integrals. Distinct indices are genuinely orthogonal and the identical-index integral is the actual positive norming constant. -/
theorem normalizedWave_orthonormal (a : ℝ) (ha : -1<a) : Orthonormal ℝ (normalizedWave a ha) := by
  -- The normalizing denominator is the genuine integral, with positivity proved independently.
  rw [orthonormal_iff_ite]
  intro i j
  rw [normalizedWave,normalizedWave,inner_smul_left,inner_smul_right,waveVector_inner]
  simp only [starRingEnd_apply,star_trivial]
  split_ifs with hij
  · subst j
    rw [show (∫ t in (0:ℝ)..1,eigenfunction a i t*eigenfunction a i t)=norming a i by simp only [norming,pow_two]]
    change (Real.sqrt (norming a i))⁻¹*((Real.sqrt (norming a i))⁻¹*norming a i)=1
    have hp := norming_pos ha i
    have hs := Real.sq_sqrt hp.le
    field_simp [(Real.sqrt_pos.mpr hp).ne']
    nlinarith
  · rw [eigenfunction_orthogonal ha hij,mul_zero,mul_zero]

/-- The actual reference vectors span a dense subspace of the entire original Hilbert space.
Use: rules out any missing reference eigenfunctions and proves the exact complete Parseval system used by GL positivity.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
Proof: the original Jacobi degree-graded sequence spans every polynomial.
Their true weighted coordinate classes are dense and the weight unitary
is onto. Normalization by nonzero actual reference norms preserves the
span. The continuous dense polynomial map therefore lies in its closure. -/
theorem normalizedWave_span_dense (a : ℝ) (ha : -1<a) :
    (Submodule.span ℝ (range (normalizedWave a ha))).topologicalClosure=⊤ := by
  -- The complete density proof uses the original physical coordinate and the earlier article's onto unitary, rather than assuming spectral completeness.
  let S := Submodule.span ℝ (range (normalizedWave a ha))
  have hm : ∀ k,waveVector a ha k∈S := by
    intro k
    have hs : Real.sqrt (norming a k)≠0 := (Real.sqrt_pos.mpr (norming_pos ha k)).ne'
    have h := S.smul_mem (Real.sqrt (norming a k)) (Submodule.subset_span (mem_range_self k))
    simpa only [normalizedWave,smul_smul,mul_inv_cancel₀ hs,one_smul] using h
  have hspan : Submodule.span ℝ (range (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a)))=⊤ := by
    exact (jacobi.Jacobi.shiftedSequence (jacobiIndex a) (jacobiIndex a) (parameters ha).2 (parameters ha).2).span
      (fun k => isUnit_iff_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr
        (jacobi.Jacobi.shiftedPolynomial_ne_zero (parameters ha).2 (parameters ha).2 k)))
  have hs : ∀ p,polynomialL2 a ha p∈S := by
    intro p
    have hp : p∈Submodule.span ℝ (range (jacobi.Jacobi.shiftedPolynomial (jacobiIndex a) (jacobiIndex a))) := by rw [hspan]; trivial
    induction hp using Submodule.span_induction with
    | mem p hp => obtain ⟨k,rfl⟩ := hp; exact hm k
    | zero => simpa only [map_zero] using S.zero_mem
    | add p q _ _ hp hq => simpa only [map_add] using S.add_mem hp hq
    | smul c p _ hp => simpa only [map_smul] using S.smul_mem c hp
  apply top_unique
  intro v _
  have hv : v∈closure (range (polynomialL2 a ha)) := by rw [(polynomialL2_denseRange a ha).closure_range]; trivial
  exact closure_mono (range_subset_iff.mpr hs) hv

/-- The actual complete original normalized reference Hilbert basis.
Use: supplies the source Parseval theorem, midpoint parity splitting and the true reference spectral realization in Proposition C.2.
Article: jacobi, Appendix C.5 (zero-energy reference Green factorization).
-/
def hilbertBasis (a : ℝ) (ha : -1<a) : HilbertBasis ℕ ℝ Space :=
  HilbertBasis.mk (normalizedWave_orthonormal a ha) (by rw [normalizedWave_span_dense a ha])

/-- The constructed complete reference basis has exactly the actual normalized original reference vectors as its entries.
Use: transfers HilbertBasis Parseval and expansion theorems to the literal original functions.
Article: jacobi, Appendix C.2 (two transformed orthonormal bases).
Proof: the community HilbertBasis constructor retains its original orthonormal family. -/
theorem hilbertBasis_apply (a : ℝ) (ha : -1<a) (k : ℕ) : hilbertBasis a ha k=normalizedWave a ha k :=
  congrFun (HilbertBasis.coe_mk _ _) k

/-- Every entry of the actual complete reference basis has exactly the original normalized reference eigenfunction as its almost-everywhere representative.
Use: identifies the reference spectral realization with the original differential equation and selected endpoint branch.
Article: jacobi, Lemma C.1.
Proof: combine the actual basis-entry identity with the community Lp scalar-multiplication representative and the proved genuine wave representative. -/
theorem hilbertBasis_ae (a : ℝ) (ha : -1<a) (k : ℕ) :
    hilbertBasis a ha k=ᵐ[volume] fun t : Interval => eigenfunction a k t/Real.sqrt (norming a k) := by
  rw [hilbertBasis_apply,normalizedWave]
  filter_upwards [Lp.coeFn_smul (Real.sqrt (norming a k))⁻¹ (waveVector a ha k),waveVector_ae a ha k] with t hs hw
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul]
  rw [hw]
  ring

end
end jacobi.Reference
