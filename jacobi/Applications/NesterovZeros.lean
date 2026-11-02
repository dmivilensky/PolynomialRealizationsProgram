import jacobi.Applications.ResidualPolynomials
import jacobi.Jacobi.OrderedZeroLimit

/-!
Article: jacobi, Proposition A.1.
Lean indices start at zero: index j denotes the source's (j+1)st zero.
Use: nesterovSmallZeros and its complete zero equivalence instantiate the actual Jacobi root theorem with no extra parameter assumptions.
-/
namespace jacobi.Applications
noncomputable section
open Polynomial Set Filter jacobi.Jacobi
open scoped Topology

/-- Both original Jacobi parameters of the Nesterov factor lie in the full verified real zero range.
Use: nesterovSmallZeros and its complete zero equivalence instantiate the actual Jacobi root theorem with no extra parameter assumptions.
Article: jacobi, Proposition A.1.
Proof: b>-1 gives alpha>-1/2; every natural e is nonnegative. -/
theorem nesterov_parameters {b : ℝ} (hb : -1<b) (e : ℕ) :
    -1<b/2 ∧ -1<(e:ℝ)-1/2 := by
  constructor <;> linarith [Nat.cast_nonneg (α := ℝ) e]

/-- The complete increasingly ordered interior zeros of the literal Nesterov residual.
Use: nesterov_small_zero_iff identifies these as all actual zeros in (0,1); nesterov_small_zero_limit proves their exact source scaling.
Article: jacobi, Proposition A.1.
-/
def nesterovSmallZeros (b : ℝ) (hb : -1<b) (e m : ℕ) : Fin m ↪o ℝ :=
  shiftedRoots (b/2) ((e:ℝ)-1/2) (nesterov_parameters hb e).1 (nesterov_parameters hb e).2 m

/-- An interior zero of the original Nesterov residual is exactly one of its increasingly ordered genuine Jacobi-factor zeros.
Use: nesterov_small_zero_limit concerns the jth actual residual zero, and excludes a different ordering or a competing Landweber zero.
Article: jacobi, Proposition A.1.
Proof: the Landweber factor is nonzero on this open interval; cancel it and apply the independently proved exhaustive original Jacobi root theorem. -/
theorem nesterov_small_zero_iff {b : ℝ} (hb : -1<b) (e m : ℕ) {x : ℝ}
    (hx : x∈Ioo (0:ℝ) 1) :
    (nesterovResidual b m e).eval x=0 ↔ ∃ i : Fin m,nesterovSmallZeros b hb e m i=x := by
  have hn : (1-x)^(m+1+e)≠0 := pow_ne_zero _ (sub_ne_zero.mpr hx.2.ne')
  simp only [nesterovResidual,eval_mul,eval_pow,eval_sub,eval_one,eval_X,
    mul_eq_zero,or_iff_right hn,nesterovFactor,nesterovSmallZeros]
  exact shiftedRoots_exhaustive (nesterov_parameters hb e).1 (nesterov_parameters hb e).2 m x

/-- Every listed small zero is a zero of the literal residual and lies strictly between zero and one.
Use: verifies the actual residual interpretation and ordering of the source's lambda_(k,j), including finite completeness.
Article: jacobi, Proposition A.1.
Proof: the genuine Jacobi root theorem gives its interval; the complete residual zero equivalence then supplies actual vanishing. -/
theorem nesterovSmallZeros_properties {b : ℝ} (hb : -1<b) (e m : ℕ) (i : Fin m) :
    nesterovSmallZeros b hb e m i∈Ioo (0:ℝ) 1 ∧
      (nesterovResidual b m e).eval (nesterovSmallZeros b hb e m i)=0 := by
  have hx := (shiftedRoots_properties (nesterov_parameters hb e).1
    (nesterov_parameters hb e).2 i).2
  exact ⟨hx,(nesterov_small_zero_iff hb e m hx).mpr ⟨i,rfl⟩⟩

/-- Every actual interior zero of the original Nesterov residual is simple, despite its separate repeated Landweber endpoint zero.
Use: supplies the source proposition's genuine simple small-zero geometry for its complete ordered zero list.
Article: jacobi, Proposition A.1.
Proof: the nonvanishing Landweber factor has multiplicity zero at the interior point. Additivity of actual polynomial root multiplicities reduces to the proved duplicate-free Jacobi root multiset; actual residual vanishing gives multiplicity at least one. -/
theorem nesterov_small_zero_simple {b : ℝ} (hb : -1<b) (e m : ℕ) {x : ℝ}
    (hx : x∈Ioo (0:ℝ) 1) (hz : (nesterovResidual b m e).eval x=0) :
    (nesterovResidual b m e).rootMultiplicity x=1 := by
  -- Simplicity is proved for the original product polynomial, not only for an independently named factor.
  classical
  have hp : nesterovResidual b m e≠0 := by
    intro h
    have h0 := congrArg (fun p : Polynomial ℝ => p.eval 0) h
    rw [nesterovResidual_zero,eval_zero] at h0
    norm_num at h0
  have hpos := (rootMultiplicity_pos hp).mpr hz
  have hmult : (nesterovFactor b m e).rootMultiplicity x≤1 := by
    rw [← count_roots]
    exact Multiset.nodup_iff_count_le_one.mp
      (shiftedPolynomial_roots (nesterov_parameters hb e).1 (nesterov_parameters hb e).2 m).2.1 x
  have hf : ¬((1-X)^(m+1+e):Polynomial ℝ).IsRoot x := by
    simp only [IsRoot,eval_pow,eval_sub,eval_one,eval_X]
    exact pow_ne_zero _ (sub_ne_zero.mpr hx.2.ne')
  have he : (nesterovResidual b m e).rootMultiplicity x=(nesterovFactor b m e).rootMultiplicity x := by
    rw [nesterovResidual,rootMultiplicity_mul hp,rootMultiplicity_eq_zero hf,zero_add]
  omega

/-- The exact scaled jth small residual zero, with zero padding only before the index exists.
Use: nesterov_small_zero_limit states the actual full fixed-index source limit on natural degrees.
Article: jacobi, Proposition A.1.
-/
def nesterovSmallZeroAt (b : ℝ) (hb : -1<b) (e m j : ℕ) : ℝ :=
  if hj : j<m then ((2*m+1+e:ℕ):ℝ)^2*nesterovSmallZeros b hb e m ⟨j,hj⟩ else 0

/-- The exact iteration-count to twice-degree ratio tends to one in either parity.
Use: nesterov_small_zero_limit converts the already proved genuine Jacobi scaling 4*m^2 to the original Nesterov scaling k^2.
Article: jacobi, Proposition A.1.
Proof: its error is (1+e)/(2*m), and reciprocal degree tends to zero. -/
theorem count_degree_ratio (e : ℕ) :
    Tendsto (fun m : ℕ => ((2*m+1+e:ℕ):ℝ)/(2*(m:ℝ))) atTop (𝓝 1) := by
  -- Discard only the initial zero degree before cancelling its reciprocal.
  have h := ((tendsto_inv_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((1+(e:ℝ))/2)).const_add 1
  norm_num only [mul_zero,add_zero] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with m hm
  have hn : (m:ℝ)≠0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
  ring

/-- The exact original Nesterov scaled jth interior zero converges to the correctly numbered original Bessel squared zero in either parity.
Use: nesterov_all_small_zero_limit merges the parity subsequences without assuming any zero existence, simplicity or ordering.
Article: jacobi, Proposition A.1.
Proof: reuse the already proved exhaustive Jacobi ordered-zero limit and multiply by the square of k/(2*m), whose actual limit is one. Identify the same padded entries exactly once m>j. -/
theorem nesterov_small_zero_limit {b : ℝ} (hb : -1<b) (e j : ℕ) :
    Tendsto (fun m : ℕ => nesterovSmallZeroAt b hb e m j) atTop
      (𝓝 (jacobi.Bessel.sigma (b/2) (nesterov_parameters hb e).1 j)) := by
  -- The finite zero enumeration is inherited from the original simple Jacobi polynomial, not reconstructed from an unspecified limit.
  have h := ((count_degree_ratio e).pow 2).mul
    (finiteSigmaAt_tendsto (nesterov_parameters hb e).1 (nesterov_parameters hb e).2 j)
  simp only [one_pow,one_mul] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop j] with m hm
  rw [nesterovSmallZeroAt,dite_eq_left hm,finiteSigmaAt_eq _ _ hm,finiteSigma,nesterovSmallZeros]
  have hn : (m:ℝ)≠0 := by exact_mod_cast (show m≠0 by omega)
  field_simp
  ring

end
end jacobi.Applications
