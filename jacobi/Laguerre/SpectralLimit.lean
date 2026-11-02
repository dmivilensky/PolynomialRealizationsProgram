import jacobi.Laguerre.ZeroLimit
import jacobi.Counterexample.LaguerreAttainment
import jacobi.Jacobi.SpectralLimit

/-!
Article: jacobi, Proposition 6.1.
The exact original inverse trace gives sum 1/(n*y_(n,k))=1/(a+1).
Together with the genuine ordered hard-edge zero limit, the existing
discrete Scheffe theorem proves convergence of the entire zero-padded
spectrum in l1. No summable finite-spectrum envelope is assumed.
Use: scaledInverse_mass gives the true total finite spectral mass, excluding loss of mass in the l1 limit.
-/
namespace jacobi.Laguerre
noncomputable section
open Matrix Set Filter jacobi.Finite
open scoped Topology BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The full sum of reciprocals of the actual original Laguerre zeros is exactly n/(a+1).
Use: scaledInverse_mass gives the true total finite spectral mass, excluding loss of mass in the l1 limit.
Article: jacobi, Proposition 6.1.
Proof: the genuine increasing spectral inverse trace identity applies
because every original Laguerre zero is positive. The exact actual
constant-drift inverse trace then evaluates the same unchanged matrix. -/
theorem inverse_root_sum {a:ℝ} (ha:-1 < a) (n:ℕ) :
    (∑i:Fin n,1/roots a ha n i)=(n:ℝ)/(a+1) := by
  have h:=increasingSpectrum_inverse_trace (chain a n) (chain_irreducible ha n)
    (fun i=>(roots_pos ha i).ne')
  rw [chain_matrix,matrix_eq_factor ha] at h
  exact h.symm.trans (jacobi.Counterexample.laguerre_inverse_trace ha n)

/-- The original Laguerre scaled reciprocal zeros, with the genuine finite list padded by zero.
Use: scaledInverse_l1_limit proves convergence of the complete original spectral sequence.
Article: jacobi, Proposition 6.1.
-/
def scaledInverse (a:ℝ) (ha:-1 < a) (n k:ℕ) : ℝ :=
  if hk:k < n then 1/((n:ℝ)*roots a ha n ⟨k,hk⟩) else 0

/-- Every term of the original finite scaled reciprocal spectrum is nonnegative.
Use: scaledInverse_l1_limit invokes the actual nonnegative discrete Scheffe theorem.
Article: jacobi, Proposition 6.1.
Proof: every actual root and positive dimension denominator is positive; the original padding is zero. -/
theorem scaledInverse_nonneg {a:ℝ} (ha:-1 < a) (n k:ℕ) : 0≤scaledInverse a ha n k := by
  unfold scaledInverse
  split_ifs with hk
  · exact div_nonneg zero_le_one (mul_nonneg (Nat.cast_nonneg n) (roots_pos ha _).le)
  · rfl

/-- The whole actual zero-padded finite Laguerre spectrum is genuinely summable.
Use: scaledInverse_l1_limit and the exact finite mass identity use actual convergent sums.
Article: jacobi, Proposition 6.1.
Proof: every term outside the genuine degree range is zero. -/
theorem scaledInverse_summable {a:ℝ} (ha:-1 < a) (n:ℕ) : Summable (scaledInverse a ha n) := by
  apply summable_of_ne_finset_zero (s:=Finset.range n)
  intro k hk
  have hn:¬k < n:=by simpa only [Finset.mem_range] using hk
  simp only [scaledInverse,hn,dite_false]

/-- The actual finite reciprocal spectrum has its exact unchanged finite-index sum.
Use: scaledInverse_mass evaluates its complete mass from the proved actual Laguerre inverse-root sum.
Article: jacobi, Proposition 6.1.
Proof: truncate only the genuinely zero padded tail and use the community finite natural-to-Fin sum identity. -/
theorem scaledInverse_tsum {a:ℝ} (ha:-1 < a) (n:ℕ) :
    (∑'k,scaledInverse a ha n k)=∑i:Fin n,1/((n:ℝ)*roots a ha n i) := by
  -- Remove only the padded zero tail, then retain each original finite physical index.
  have he:(∑'k,scaledInverse a ha n k)=∑k∈Finset.range n,scaledInverse a ha n k := by
    apply tsum_eq_sum
    intro k hk
    have hn:¬k < n:=by simpa only [Finset.mem_range] using hk
    simp only [scaledInverse,hn,dite_false]
  rw [he,← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [scaledInverse,dite_eq_left i.isLt]

/-- The full actual positive-degree Laguerre scaled reciprocal spectrum has mass exactly 1/(a+1).
Use: scaledInverse_l1_limit rules out an unverified infinite-tail mass defect.
Article: jacobi, Proposition 6.1.
Proof: factor out the true reciprocal dimension from the complete finite sum and apply the exact original inverse-root sum. -/
theorem scaledInverse_mass {a:ℝ} (ha:-1 < a) {n:ℕ} (hn:0 < n) :
    (∑'k,scaledInverse a ha n k)=1/(a+1) := by
  -- The complete original inverse-root sum is evaluated before cancelling the positive matrix dimension.
  rw [scaledInverse_tsum]
  have he:(∑i:Fin n,1/((n:ℝ)*roots a ha n i))=
      (1/(n:ℝ))*(∑i:Fin n,1/roots a ha n i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp only [one_div,_root_.mul_inv_rev,mul_comm]
  rw [he,inverse_root_sum ha]
  have hn0:(n:ℝ)≠0:=Nat.cast_ne_zero.mpr hn.ne'
  field_simp [hn0]

/-- Each original finite scaled reciprocal Laguerre zero tends to twice the original Bessel edge value.
Use: scaledInverse_l1_limit combines actual fixed-index convergence with the proved full total mass.
Article: jacobi, Proposition 6.1.
Proof: take the continuous positive reciprocal of the actual ordered
squared-zero limit. The exact finite identity is 1/(n*y)=4/(4*n*y). -/
theorem scaledInverse_limit {a:ℝ} (ha:-1 < a) (k:ℕ) :
    Tendsto (fun n:ℕ=>scaledInverse a ha n k) atTop
      (𝓝 (2* jacobi.Bessel.edgeValue a ha k)) := by
  -- The actual limiting denominator is strictly positive, already proved for every Bessel zero.
  have hp:= jacobi.Bessel.spectralZero_pos ha (jacobi.Bessel.sigma_mem ha k)
  have h:=(tendsto_const_nhds (x:=(4:ℝ))).div (finiteSigmaAt_limit ha k) hp.ne'
  have hv:4/ jacobi.Bessel.sigma a ha k=2* jacobi.Bessel.edgeValue a ha k:=by
    unfold jacobi.Bessel.edgeValue
    ring
  rw [hv] at h
  apply (tendsto_congr' ?_).mpr h
  filter_upwards [eventually_gt_atTop k] with n hn
  dsimp only [Pi.div_apply]
  rw [scaledInverse,dite_eq_left hn,jacobi.Bessel.finiteZeroAt_eq _ hn,finiteSigma]
  field_simp

/-- The entire original Laguerre reciprocal edge spectrum converges in l1 to twice the original Bessel edge spectrum.
Use: the actual source scale H_n/n then gives the complete Laguerre edge limit in Proposition 6.1.
Article: jacobi, Proposition 6.1.
Source: the discrete Scheffe theorem already proved for the Jacobi spectrum.
Proof: all finite spectra and the genuine limiting spectrum are
nonnegative and summable. Their actual coordinates converge, and their
true total masses agree by the exact finite trace and first Bessel
Rayleigh sum. The existing Scheffe theorem finishes the whole infinite tail. -/
theorem scaledInverse_l1_limit {a:ℝ} (ha:-1 < a) :
    Tendsto (fun n:ℕ=>∑'k,|scaledInverse a ha n k-2* jacobi.Bessel.edgeValue a ha k|)
      atTop (𝓝 0) := by
  -- No uniform dominating bound for the original finite spectrum is introduced.
  apply jacobi.Jacobi.nonnegative_scheffe (scaledInverse_summable ha)
    ((jacobi.Bessel.edgeValue_summable ha).mul_left 2)
    (scaledInverse_nonneg ha) (fun k=>mul_nonneg (by norm_num) ((jacobi.Bessel.edgeValue_properties ha).1 k).le)
    (scaledInverse_limit ha)
  rw [tsum_mul_left,jacobi.Bessel.first_rayleigh_sum ha]
  have he:2*(1/(2*(a+1)))=1/(a+1):=by field_simp
  rw [he]
  apply (tendsto_congr' ?_).mpr tendsto_const_nhds
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  exact scaledInverse_mass ha hn

end
end jacobi.Laguerre
