import jacobi.Comparison.GramNodeBounds
import jacobi.Comparison.WeightReflection
import jacobi.Comparison.Gram

/-!
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Each literal original target-minus-support spectral Gram summand has
the full uniform summable inverse-square edge bound and a common
remainder epsilon_N with N*epsilon_N->0. The original weight comparison,
weighted polynomial values, full spectral derivatives and node errors
are all independently proved for the same actual finite matrices.
Use: gramSummand_bound gives a summable uniform edge majorant for the actual spectral representation of the original Gram matrix used in the two-edge limit.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set Finset Filter jacobi.Support jacobi.Jacobi
open scoped Topology

/-- The original target-minus-support spectral contribution to the genuine Gram perturbation.
Use: gramSummand_bound gives a summable uniform edge majorant for the actual spectral representation of the original Gram matrix used in the two-edge limit.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
-/
def gramSummand (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j k:Fin (n+1)) : ℝ :=
  (targetMeasure a b ha hb n).weight k*
      (supportPolynomial a b ha hb n i).eval ((nodes a b ha hb (n+1)).value k)*
      (supportPolynomial a b ha hb n j).eval ((nodes a b ha hb (n+1)).value k)-
    (supportMeasure a b ha hb n).weight k*
      (supportPolynomial a b ha hb n i).eval (modelNode a b (n+1) k.val)*
      (supportPolynomial a b ha hb n j).eval (modelNode a b (n+1) k.val)

/-- The actual original target Gram perturbation is exactly the complete original spectral summand row.
Use: the uniform Gram limit combines the finite-prefix limits and the summable original gramSummand_bound on this same literal spectral representation.
Article: jacobi, Appendix C.4 (uniform Cholesky limit).
Proof: the independently proved exact target-minus-support representation has precisely these actual target nodes, corrected support nodes, probabilities and polynomials. -/
theorem gramPerturbation_sum (a b:ℝ) (ha:-1<a) (hb:-1<b) (n:ℕ) (i j:Fin (n+1)) :
    gramPerturbation a b ha hb n i j=∑k,gramSummand a b ha hb n i j k :=
  targetGram_perturbation_terms a b ha hb n i j

/-- Every genuine original spectral Gram summand has the complete uniform summable edge majorant with a common matrix-size little-o remainder.
Use: the two-edge Gram limit controls all actual growing spectral tails with this bound; the common remainder vanishes even after summation over the entire original dimension.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: split the literal original summand into its actual probability-ratio error times the weighted target-node polynomial product, plus the original support-weighted product's node displacement. Apply the independently proved uniform weight-ratio error and support-weight product bound in Appendix C.3 to the first term, and the actual mean-value node-error estimate to the second. Combine the common little-o remainder with the reciprocal-square matrix-size term. -/
theorem gramSummand_bound {a b:ℝ} (ha:-1<a) (hb:-1<b) :
    ∃C:ℝ,0<C ∧ ∃ε:ℕ→ℝ,(∀n,0≤ε n) ∧
      Tendsto (fun n:ℕ => ((n:ℝ)+1)*ε n) atTop (𝓝 0) ∧
      ∀ᶠn:ℕ in atTop,∀i j:Fin (n+1),2*i.val≤n+1→2*j.val≤n+1→∀k:Fin (n+1),
        ((n:ℝ)+1)*|gramSummand a b ha hb n i j k|≤C/(edgeIndex (n+1) k.val:ℝ)^2+ε n := by
  -- All inputs have their actual original spectral data and full uniform index ranges already proved.
  obtain ⟨A,hA,hprod⟩ := supportGram_segment_product ha hb
  obtain ⟨B,hB,δ,hδ,hδlim,hweight⟩ := comparisonWeight_error ha hb
  obtain ⟨D,hD,hnode⟩ := supportGram_node_error ha hb
  let ε (n:ℕ) : ℝ := A*δ n+D/((n:ℝ)+1)^2
  refine ⟨A*B+D,by positivity,ε,fun n =>
    add_nonneg (mul_nonneg hA.le (hδ n)) (div_nonneg hD.le (sq_nonneg _)),?_,?_⟩
  · have hN : Tendsto (fun n:ℕ => (n:ℝ)+1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    have ht := (hδlim.const_mul A).add ((tendsto_inv_atTop_zero.comp hN).const_mul D)
    simp only [mul_zero,add_zero] at ht
    apply ht.congr'
    exact Eventually.of_forall (fun n => by
      dsimp [ε]
      have hN0 : (n:ℝ)+1≠0 := by positivity
      field_simp)
  · filter_upwards [hprod,hweight,hnode] with n hnp hnw hnn
    intro i j hi hj k
    let N : ℝ := (n:ℝ)+1
    let w := (supportMeasure a b ha hb n).weight k
    let v := (targetMeasure a b ha hb n).weight k
    let p := (supportPolynomial a b ha hb n i).eval ((nodes a b ha hb (n+1)).value k)*
      (supportPolynomial a b ha hb n j).eval ((nodes a b ha hb (n+1)).value k)
    let q := (supportPolynomial a b ha hb n i).eval (modelNode a b (n+1) k.val)*
      (supportPolynomial a b ha hb n j).eval (modelNode a b (n+1) k.val)
    have hw : 0<w := (supportMeasure a b ha hb n).positive k
    have hN : 0<N := by dsimp [N]; positivity
    have hδn : 0≤δ n := hδ n
    have hvalue : N*w*|p|≤A := hnp i j hi hj k _ right_mem_uIcc
    have hchange : N*w*|p-q|≤D*(1/(edgeIndex (n+1) k.val:ℝ)^2+1/N^2) := hnn i j hi hj k
    have he : gramSummand a b ha hb n i j k=(v/w-1)*(w*p)+w*(p-q) := by
      change v*((supportPolynomial a b ha hb n i).eval ((nodes a b ha hb (n+1)).value k))*
        ((supportPolynomial a b ha hb n j).eval ((nodes a b ha hb (n+1)).value k))-
        w*((supportPolynomial a b ha hb n i).eval (modelNode a b (n+1) k.val))*
        ((supportPolynomial a b ha hb n j).eval (modelNode a b (n+1) k.val))=_
      dsimp [p,q]
      field_simp [hw.ne']
      ring
    rw [he]
    calc
      _ ≤ N*(|(v/w-1)*(w*p)|+|w*(p-q)|) := mul_le_mul_of_nonneg_left (abs_add_le _ _) hN.le
      _ = |v/w-1| *(N*w*|p|)+N*w*|p-q| := by simp only [abs_mul,abs_of_pos hw]; ring
      _ ≤ (B/(edgeIndex (n+1) k.val:ℝ)^2+δ n)*A+D*(1/(edgeIndex (n+1) k.val:ℝ)^2+1/N^2) :=
        add_le_add (mul_le_mul (hnw k) hvalue (by positivity) (by positivity)) hchange
      _ = _ := by dsimp [ε,N]; ring

end
end jacobi.Comparison
