import jacobi.Comparison.EigenvectorTransform
import jacobi.Comparison.CholeskyLimit
import jacobi.Analysis.PrefixAverageBound

/-!
Article: jacobi, Proposition C.3.
The actual target-polynomial Schur correction is uniformly approximated
by the actual two-edge continuum model row. Both original growing-row
errors are proved small: the true Cholesky coefficient error and the
true support-polynomial edge error, with their common genuine bounds.
Use: targetPolynomial_edge_limit inserts the proved original model-row integral limit into the same actual target polynomial transformation.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Filter jacobi.Reference jacobi.Analysis jacobi.GelfandLevitan jacobi.Support jacobi.Finite
open scoped Topology

/-- The full actual original Schur correction has its uniform genuine
two-edge reference-profile approximation on every physical half row.
Use: targetPolynomial_edge_limit inserts the proved original model-row
integral limit into the same actual target polynomial transformation.
Article: jacobi, Proposition C.3.
Proof: split each original row term into its true scaled-coefficient
error times the actual support value, plus the bounded actual K times
the genuine support-wave error. Both errors are uniformly small and
the actual prefix count is at most the true matrix size. The complete
normalized error sum therefore vanishes uniformly over physical rows. -/
theorem eigenvectorRow_uniform_approximation {a b:ℝ} (ha:-1<a) (hb:-1<b) (k:ℕ) :
    ∀ ε:ℝ,0<ε → ∃N:ℕ,∀n≥N,∀i:Fin (n+1),2*i.val≤n+1 →
      |(∑j:Fin i.val, rowCoefficient a b ha hb n i j*
          supportEdgeValue a b ha hb n k (Gram.before i j))-
        eigenvectorModelRow a b ha hb n k i|<ε := by
  -- Both approximation errors concern the original polynomial and coefficient rows.
  obtain ⟨B,hB,hP⟩ := supportPolynomial_target_scaled_bound ha hb k
  obtain ⟨NP,hNP⟩ := eventually_atTop.mp hP
  obtain ⟨C,hC,hK⟩ := twoEdgeTransformation_bounded a b ha hb
  intro ε hε
  let δ : ℝ := ε/(2*(B+C))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨NC,hNC⟩ := cholesky_uniform_limit a b ha hb δ hδ
  obtain ⟨NS,hNS⟩ := supportPolynomial_target_uniform ha hb k δ hδ
  refine ⟨max (max NP NC) NS,fun n hn i hi => ?_⟩
  let P (j:Fin i.val) := supportEdgeValue a b ha hb n k (Gram.before i j)
  let R (j:Fin i.val) := referenceEdgeProfile a b ha k (matrixHalfPoint n (Gram.before i j))
  let K (j:Fin i.val) := twoEdgeTransformation a b ha hb n i (Gram.before i j)
  let c := rowCoefficient a b ha hb n i
  let e (j:Fin i.val) := (((n:ℝ)+1)*c j-K j)*P j+K j*(P j-R j)
  have hbefore (j:Fin i.val) : 2*(Gram.before i j).val≤n+1 := by
    have hj := j.isLt
    change 2*j.val≤n+1
    omega
  have hPbound (j:Fin i.val) : |P j|≤B := hNP n (by omega) (Gram.before i j) (hbefore j)
  have hc (j:Fin i.val) : |((n:ℝ)+1)*c j-K j|≤δ := (hNC n (by omega) i hi j).le
  have hr (j:Fin i.val) : |P j-R j|≤δ := by
    have hh := hNS n (by omega) (Gram.before i j) (hbefore j)
    rw [← referenceEdgeProfile_sample a b ha k (Gram.before i j) (hbefore j)] at hh
    exact hh.le
  have he (j:Fin i.val) : |e j|≤δ*B+C*δ := by
    exact (abs_add_le _ _).trans (add_le_add
      (by rw [abs_mul]; exact mul_le_mul (hc j) (hPbound j) (abs_nonneg _) hδ.le)
      (by rw [abs_mul]; exact mul_le_mul (hK n i (Gram.before i j)) (hr j) (abs_nonneg _) hC.le))
  -- Division by N absorbs the entire actual prefix length, not just a fixed number of terms.
  have hsum := prefix_average_bound (by positivity : (0:ℝ)<(n:ℝ)+1)
    (show (i.val:ℝ)≤(n:ℝ)+1 from by exact_mod_cast i.isLt.le)
    (by positivity : 0≤δ*B+C*δ) e he
  have hterm (j:Fin i.val) : e j/((n:ℝ)+1)=c j*P j-(K j*R j)/((n:ℝ)+1) := by
    dsimp [e]
    field_simp
    ring
  have hs : (∑j:Fin i.val,e j)/((n:ℝ)+1)=
      (∑j:Fin i.val,c j*P j)-eigenvectorModelRow a b ha hb n k i := by
    rw [Finset.sum_div]
    simp_rw [hterm,Finset.sum_sub_distrib,← Finset.sum_div]
    rfl
  rw [hs] at hsum
  have hδeq : δ*B+C*δ=ε/2 := by dsimp [δ]; field_simp
  exact hsum.trans_lt (by rw [hδeq]; linarith)

end
end jacobi.Comparison
