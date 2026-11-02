import jacobi.GelfandLevitan.CoefficientVectors
import jacobi.Reference.IntegralNorm
import Mathlib.Analysis.InnerProductSpace.Rayleigh

/-!
Article: jacobi, Appendix C.2 (uniform GL coercivity).
The genuine uniform source summand estimate gives the same summable
bound in the true half-interval operator norm. The community symmetric
Rayleigh norm formula and the actual unit-interval L1/L2 comparison
are used, so no spectral or operator convergence premise is added.
Use: proves the summable true operator norm bound on every genuine compact source correction before constructing the actual GL operator.
-/
namespace jacobi.GelfandLevitan
noncomputable section
open Real Set MeasureTheory jacobi.Reference
open scoped Topology InnerProductSpace
attribute [local instance] Measure.Subtype.measureSpace
attribute [local irreducible] kernelTerm rankCorrection

/-- A genuine uniform bound on an original GL summand controls its actual Hilbert quadratic form by the same constant and the original squared L2 norm.
Use: proves the summable true operator norm bound on every genuine compact source correction before constructing the actual GL operator.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: identify the actual rank-one quadratic form with its proved
literal source kernel double integral. Bound the integrand by the
uniform summand bound times the product of the true absolute input.
The genuine product integral is its squared L1 norm, bounded by the
actual squared L2 norm in the original unit-interval normalization. -/
theorem rankCorrection_quadratic_bound (a : ℝ) (ha : -1<a) (k : ℕ) {M : ℝ} (hM : 0≤M)
    (hbound : ∀ t∈Icc (0:ℝ) (1/2),∀ s∈Icc (0:ℝ) (1/2),|kernelTerm a ha k t s|≤M)
    (v : halfSubspace) : |inner ℝ (rankCorrection a ha k v) v|≤M*‖v‖^2 := by
  -- The genuine operator and the genuine original integrand have already been identified at every actual spectral index.
  have he : inner ℝ (rankCorrection a ha k v) v=
      ∫ p:Interval×Interval,((v:Space) p.1*(v:Space) p.2)*kernelTerm a ha k (halfTime p.1) (halfTime p.2)
        ∂(volume.prod volume) := by
    rw [rankCorrection_inner,kernelTerm_quadratic]
    ring
  let L := ∫ t:Interval,‖(v:Space) t‖
  have hL : 0≤L := integral_nonneg (fun _ => norm_nonneg _)
  have hLn : L≤‖v‖ := space_L1_le_norm (v:Space)
  have hprod : Integrable (fun p:Interval×Interval => ‖(v:Space) p.1‖*‖(v:Space) p.2‖)
      (volume.prod volume) := (space_integrable (v:Space)).norm.mul_prod (space_integrable (v:Space)).norm
  have hh := norm_integral_le_of_norm_le
    (f := fun p:Interval×Interval => ((v:Space) p.1*(v:Space) p.2)*kernelTerm a ha k (halfTime p.1) (halfTime p.2))
    (hprod.const_mul M) (Filter.Eventually.of_forall (fun p => by
      change |((v:Space) p.1*(v:Space) p.2)*kernelTerm a ha k (halfTime p.1) (halfTime p.2)|≤_
      rw [abs_mul,abs_mul]
      have hb := mul_le_mul_of_nonneg_left (hbound _ (halfTime_mem p.1) _ (halfTime_mem p.2))
        (show (0:ℝ)≤|(v:Space) p.1| * |(v:Space) p.2| by positivity)
      simpa only [Real.norm_eq_abs,mul_comm M] using hb))
  have hpair : (∫ p:Interval×Interval,‖(v:Space) p.1‖*‖(v:Space) p.2‖ ∂(volume.prod volume))=L*L :=
    integral_prod_mul (fun t:Interval => ‖(v:Space) t‖) (fun t:Interval => ‖(v:Space) t‖)
  rw [integral_const_mul,hpair,Real.norm_eq_abs,← he] at hh
  have hs : L*L≤‖v‖*‖v‖ := mul_le_mul hLn hLn hL (norm_nonneg v)
  calc
    _ ≤ M*(L*L) := hh
    _ ≤ M*(‖v‖*‖v‖) := mul_le_mul_of_nonneg_left hs hM
    _ = _ := by rw [pow_two]

/-- The actual original compact GL summands obey one genuine summable inverse-square operator norm bound, at every original spectral index.
Use: constructs the source GL integral operator as an actual norm-convergent series of the true compact symmetric rank-one corrections.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: use the proved full-index genuine uniform source kernel bound.
The true symmetric Rayleigh norm formula reduces operator norm to the
original normalized quadratic form, bounded by the preceding actual
integral estimate. The zero vector is treated by its true zero value. -/
theorem rankCorrection_norm_bound (a : ℝ) (ha : -1<a) :
    ∃ C:ℝ,0<C ∧ ∀ k:ℕ,‖rankCorrection a ha k‖≤C/(k+1:ℝ)^2 := by
  -- The actual operator norm is bounded through the community symmetric norm theorem, not by separately summing the two nonsummable rank-one norms.
  obtain ⟨C,hC,hbound⟩ := kernelTerm_uniform_bound a ha
  refine ⟨C,hC,fun k => ?_⟩
  rw [(rankCorrection a ha k).norm_eq_iSup_rayleighQuotient (rankCorrection_symmetric a ha k)]
  apply ciSup_le
  intro v
  change |inner ℝ (rankCorrection a ha k v) v/‖v‖^2|≤C/(k+1:ℝ)^2
  by_cases hv : v=0
  · subst v
    simp only [map_zero,inner_zero_left,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),zero_div,abs_zero]
    positivity
  · rw [abs_div,abs_of_nonneg (sq_nonneg ‖v‖)]
    apply (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hv))).mpr
    exact rankCorrection_quadratic_bound a ha k (by positivity)
      (fun t ht s hs => hbound k t ht s hs) v

/-- The original genuine compact GL correction series is summable in the actual half-interval Hilbert operator norm.
Use: its true sum is the original compact symmetric F operator needed to upgrade the proved strict quadratic positivity to uniform coercivity.
Article: jacobi, Appendix C.2 (uniform GL coercivity).
Proof: the proved actual operator norms are bounded by the original positive constant times the genuinely summable shifted inverse-square p-series. -/
theorem rankCorrection_summable (a : ℝ) (ha : -1<a) : Summable (rankCorrection a ha) := by
  obtain ⟨C,_,hbound⟩ := rankCorrection_norm_bound a ha
  have hM : Summable (fun k:ℕ => C/(k+1:ℝ)^2) := by
    simpa only [one_pow,mul_one_div] using (jacobi.Bessel.inverse_square_majorant_summable 1).mul_left C
  exact hM.of_norm_bounded (f := rankCorrection a ha) hbound

end
end jacobi.GelfandLevitan
