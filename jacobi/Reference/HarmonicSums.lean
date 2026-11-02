import jacobi.Reference.IndexMajorant
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
Article: jacobi, Appendix C.2 (norming ratios).
Exact harmonic sums control the complete reciprocal quadratic-gap
row. The shifted reciprocal difference telescopes before taking its
limit, so no divergent series is subtracted from another.
Source: elementary harmonic-number identities and the classical
bound H_n<=1+log(n), formalized in mathlib.
Use: reciprocal_product_hasSum evaluates the infinite quadratic-gap tail, and harmonicSum_log_bound gives its logarithmic growth in Structure of F (a).
-/
namespace jacobi.Reference
noncomputable section
open Real Finset Filter
open scoped Topology
set_option backward.isDefEq.respectTransparency false

/-- The real finite harmonic sum with its original positive-integer denominators.
Use: reciprocal_product_hasSum evaluates the infinite quadratic-gap tail, and harmonicSum_log_bound gives its logarithmic growth in Structure of F (a).
Article: jacobi, Appendix C.2 (norming ratios).
Source: harmonic numbers H_n. -/
def harmonicSum (n : ℕ) : ℝ := ∑ j∈range n,1/(j+1:ℝ)

/-- The finite real harmonic sum agrees with the community rational harmonic number.
Use: harmonicSum_log_bound reuses the proved community logarithmic estimate without repeating the integral comparison.
Article: jacobi, Appendix C.2 (norming ratios).
Source: mathlib NumberTheory.Harmonic.Defs.
Proof: cast each term in the defining finite rational sum to the real numbers. -/
theorem harmonicSum_eq (n : ℕ) : harmonicSum n=(harmonic n:ℝ) := by
  simp [harmonicSum,harmonic,one_div]

/-- The genuine harmonic sum has the classical logarithmic upper bound at every positive index.
Use: converts the exact reciprocal-gap sum into O(log(k)/k) in the strengthened rho asymptotic.
Article: jacobi, Appendix C.2 (norming ratios).
Source: harmonic_le_one_add_log, the standard harmonic-number integral comparison.
Proof: identify the real finite sum with mathlib's harmonic number and apply its proved estimate. -/
theorem harmonicSum_log_bound (n : ℕ) : harmonicSum n≤1+Real.log n := by
  rw [harmonicSum_eq]
  exact harmonic_le_one_add_log n

/-- The actual finite harmonic sums are nonnegative and increase with the number of terms.
Use: quadratic_gap_row_bound replaces its shorter prefix by the same harmonic sum as its infinite right tail.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: each reciprocal denominator is positive, and extending the finite range adds only nonnegative terms. -/
theorem harmonicSum_mono : Monotone harmonicSum := by
  intro n m hnm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hnm) (fun _ _ _ => by positivity)

/-- Finite shifted reciprocal differences telescope to a harmonic prefix minus a finite translated prefix.
Use: reciprocal_product_hasSum takes a limit only after this finite identity, avoiding subtraction of divergent reciprocal series.
Article: jacobi, Appendix C.2 (norming ratios).
Proof: expand the same finite sum of length n+N in the two possible orders and subtract the common overlap. -/
theorem harmonic_shift_telescope (N n : ℕ) :
    (∑ j∈range n,(1/(j+1:ℝ)-1/(j+N+1:ℝ)))=
      harmonicSum N-∑ j∈range N,1/(j+n+1:ℝ) := by
  -- Both sides involve finite sums; the harmonic divergence never enters this identity.
  have h₁ := Finset.sum_range_add (fun j : ℕ => 1/(j+1:ℝ)) n N
  have h₂ := Finset.sum_range_add (fun j : ℕ => 1/(j+1:ℝ)) N n
  rw [Nat.add_comm N n] at h₂
  simp only [Nat.cast_add,add_comm (n:ℝ),add_comm (N:ℝ)] at h₁ h₂
  rw [Finset.sum_sub_distrib]
  dsimp [harmonicSum]
  linarith

/-- The actual translated reciprocal-product series sums to the harmonic number divided by its shift.
Use: quadratic_gap_right_hasSum evaluates the full right part of the reciprocal-gap row in Structure of F (a).
Article: jacobi, Appendix C.2 (norming ratios).
Source: the elementary telescoping identity sum_j 1/((j+1)*(j+N+1))=H_N/N.
Proof: partial fractions turn each finite partial sum into the proved telescoping difference. The finite translated harmonic prefix tends to zero; nonnegativity then supplies the actual HasSum. -/
theorem reciprocal_product_hasSum {N : ℕ} (hN : 0<N) :
    HasSum (fun j : ℕ => 1/((j+1:ℝ)*(j+N+1:ℝ))) (harmonicSum N/(N:ℝ)) := by
  -- Partial fractions are used in finite sums before passage to the genuine convergent infinite series.
  have hNp : 0<(N:ℝ) := by exact_mod_cast hN
  have htail : Tendsto (fun n : ℕ => ∑ j∈range N,1/(j+n+1:ℝ)) atTop (𝓝 0) := by
    convert! tendsto_finsetSum (range N) (fun j _ =>
      (tendsto_atTop_add_const_right _ ((j:ℝ)+1) tendsto_natCast_atTop_atTop).const_div_atTop 1) using 1
    · funext n
      apply Finset.sum_congr rfl
      intro j _hj
      congr 1
      ring
    · simp
  have hl := ((tendsto_const_nhds (x := harmonicSum N)).sub htail).div_const (N:ℝ)
  simp only [sub_zero] at hl
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun j => by positivity) _).mpr
  apply hl.congr'
  exact Eventually.of_forall fun n => by
    dsimp only
    rw [← harmonic_shift_telescope,Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _hj
    have hjp : 0<(j+1:ℝ) := by positivity
    have hjNp : 0<(j+N+1:ℝ) := by positivity
    field_simp [hNp.ne',hjp.ne',hjNp.ne']
    ring

end
end jacobi.Reference
