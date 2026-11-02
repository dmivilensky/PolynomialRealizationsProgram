import jacobi.Comparison.FloorEigenvectorLimit
import jacobi.Finite.GreenEntries
import jacobi.Jacobi.FibreLimit

/-!
Article: jacobi, Theorem 2.1.
The original target Green matrix is expressed through the actual
zero-padded Jacobi resolvent spectrum and genuine signed target
vectors. Its complete scaled spectral observables are uniformly bounded.
Use: spectral Green formulas and their limits use one scalar index range with the exact original finite vectors and their true signs.
-/
namespace jacobi.Comparison
noncomputable section
open Real Filter Matrix jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Finite
open scoped Topology

/-- The actual target eigenvector in its true physical square-root
matrix-size normalization, padded only beyond the spectral dimension.
Use: spectral Green formulas and their limits use one scalar index
range with the exact original finite vectors and their true signs.
Article: jacobi, Theorem 2.1.
-/
def scaledTargetEigenvector (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i:Fin (n+1)) (k:ℕ) : ℝ :=
  sqrt ((n:ℝ)+1)*targetEigenvectorEntry a b ha hb n i k

/-- The actual scaled original eigenvectors have a common absolute
bound on every physical row and every padded spectral index.
Use: the genuine L1 spectral limit may be summed against their
products in Theorem 2.1 and the Green-matrix limit of Theorem 2.1.
Article: jacobi, Theorem 2.1.
Proof: genuine indices use the independently proved actual full
bound. All remaining scalar indices contribute their true padded zero. -/
theorem scaledTargetEigenvector_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∀ᶠn:ℕ in atTop,∀i:Fin (n+1),∀k:ℕ,
      |scaledTargetEigenvector a b ha hb n i k|≤C := by
  obtain ⟨C,hC,hbnd⟩ := target_eigenvector_uniform_bound ha hb
  refine ⟨C,hC,?_⟩
  filter_upwards [hbnd] with n hn i k
  by_cases hk:k<n+1
  · simpa only [scaledTargetEigenvector,targetEigenvectorEntry,dite_eq_left hk,abs_mul,
      abs_of_nonneg (sqrt_nonneg _)] using hn i ⟨k,hk⟩
  · simp only [scaledTargetEigenvector,targetEigenvectorEntry,dite_eq_right hk,mul_zero,abs_zero]
    exact hC.le

/-- The actual target Green matrix in its printed physical N inverse
normalization, with no spectral replacement in its definition.
Use: its diagonal and full matrix-entry limits give the two Green-kernel assertions of Theorem 2.1.
Article: jacobi, Theorem 2.1.
-/
def scaledTargetGreen (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i j:Fin (n+1)) : ℝ :=
  (targetChain a b ha hb n).green i j/((n:ℝ)+1)

/-- The actual normalized target Green matrix has its exact original
spectral series at every physical pair.
Use: Green limits sum the proved genuine vector products against the
actual L1-convergent Jacobi spectrum; the diagonal gives equation (dred).
Article: jacobi, Theorem 2.1.
Proof: the original inverse has its finite orthogonal spectral formula.
Zero padding contributes no extra terms; the positive true dimension
cancels the two actual eigenvector square-root factors exactly. -/
theorem scaledTargetGreen_spectral (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (i j:Fin (n+1)) :
    scaledTargetGreen a b ha hb n i j=∑'k,jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k*
      (scaledTargetEigenvector a b ha hb n i k*scaledTargetEigenvector a b ha hb n j k) := by
  -- Every denominator is an actual original spectral gap, already known positive.
  have hg := green_entry_spectral (targetMeasure a b ha hb n).reconstructed
    (targetMeasure a b ha hb n).reconstructedBasis
    (fun k => (sub_pos.mpr ((jacobi.Jacobi.nodes a b ha hb (n+1)).interval k).2).ne') i j
  have he : (∑'k,jacobi.Jacobi.finiteLambdaAt a b ha hb (n+1) k*
      (scaledTargetEigenvector a b ha hb n i k*scaledTargetEigenvector a b ha hb n j k))=
      ∑k:Fin (n+1),jacobi.Jacobi.finiteLambda a b ha hb (n+1) k*
        (((n:ℝ)+1)*(targetMeasure a b ha hb n).reconstructedBasis.Q i k*
          (targetMeasure a b ha hb n).reconstructedBasis.Q j k) := by
    rw [tsum_eq_sum (s:=Finset.range (n+1)) (fun k hk => by
      rw [jacobi.Jacobi.finiteLambdaAt_zero ha hb (by simpa only [Finset.mem_range,not_lt] using hk),zero_mul])]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k _
    rw [jacobi.Jacobi.finiteLambdaAt_eq ha hb k.isLt]
    simp only [scaledTargetEigenvector,targetEigenvectorEntry,dite_eq_left k.isLt]
    have hs := sq_sqrt (by positivity : (0:ℝ)≤(n:ℝ)+1)
    change jacobi.Jacobi.finiteLambda a b ha hb (n+1) k*_= jacobi.Jacobi.finiteLambda a b ha hb (n+1) k*_
    congr 1
    calc
      _=(sqrt ((n:ℝ)+1))^2*(targetMeasure a b ha hb n).reconstructedBasis.Q i k*
          (targetMeasure a b ha hb n).reconstructedBasis.Q j k := by ring
      _=_ := by rw [hs]
  rw [he]
  unfold scaledTargetGreen
  change (targetMeasure a b ha hb n).reconstructed.green i j/((n:ℝ)+1)=_
  rw [hg,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  rw [jacobi.Jacobi.finiteLambda_node ha hb k]
  push_cast
  field_simp
  rfl

end
end jacobi.Comparison
