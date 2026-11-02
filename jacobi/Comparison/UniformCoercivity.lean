import jacobi.Comparison.GramCellLimit

/-!
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
The original finite Gram matrices have one strictly positive lower
bound on their complete physical half prefixes. Both the actual
continuum gaps and the full finite-to-continuum error are discharged.
The bound covers every smaller principal section by zero extension.
Use: targetGram_uniform_coercive absorbs the proved complete cell-kernel error into the genuine fixed continuum coercivity gap.
-/
namespace jacobi.Comparison
noncomputable section
open Real Set MeasureTheory jacobi.Reference jacobi.Analysis
open scoped Topology

/-- A uniform matrix-size-scaled entry bound on the physical half
controls the full quadratic error of every actual half-supported vector.
Use: targetGram_uniform_coercive absorbs the proved complete cell-kernel
error into the genuine fixed continuum coercivity gap.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: mask only rows and columns whose actual vector coordinates are
zero. The remaining entry bound is delta/N; finite Cauchy--Schwarz
supplies exactly N, so the true dimension cancels completely. -/
theorem half_quadratic_error {n:ℕ} (E:Fin (n+1)→Fin (n+1)→ℝ)
    {δ:ℝ} (hδ:0≤δ)
    (hE:∀i j, 2*i.val≤n+1 → 2*j.val≤n+1 → |((n:ℝ)+1)*E i j|≤δ)
    (v:Fin (n+1)→ℝ) (hv:∀i, n+1<2*i.val → v i=0) :
    |∑ i,∑ j, E i j*v i*v j|≤δ*∑ i, (v i)^2 := by
  -- Mask only coordinates whose actual vector values are zero outside the physical half.
  classical
  let D (i j:Fin (n+1)) : ℝ := if 2*i.val≤n+1 ∧ 2*j.val≤n+1 then E i j else 0
  have hN : (0:ℝ)<(n:ℝ)+1 := by positivity
  have hD (i j:Fin (n+1)) : |D i j|≤δ/((n:ℝ)+1) := by
    by_cases hij : 2*i.val≤n+1 ∧ 2*j.val≤n+1
    · simp only [D,ite_eq_left_iff.mpr (fun h => (h hij).elim)]
      have hh := hE i j hij.1 hij.2
      rw [abs_mul,abs_of_pos hN] at hh
      apply (le_div_iff₀ hN).mpr
      nlinarith
    · simp only [D,ite_eq_right_iff.mpr (fun h => (hij h).elim),abs_zero]
      positivity
  have he : (∑ i,∑ j, D i j*v i*v j) = ∑ i,∑ j, E i j*v i*v j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hi : 2*i.val≤n+1 <;> by_cases hj : 2*j.val≤n+1
    · simp [D,hi,hj]
    · simp [D,hi,hj,hv j (by omega)]
    · simp [D,hi,hj,hv i (by omega)]
    · simp [D,hi,hj,hv i (by omega)]
  have hh := matrix_quadratic_error D (by positivity : 0≤δ/((n:ℝ)+1)) hD v
  rw [he] at hh
  simpa only [Fintype.card_fin,Nat.cast_add,Nat.cast_one,div_mul_cancel₀ _ hN.ne'] using hh

/-- The actual original target Gram form is its Euclidean identity
form plus the actual original Gram perturbation form.
Use: targetGram_uniform_coercive states its lower bound directly for
the original Gram matrix, which is used by Cholesky and eigenvectors.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: expand the actual perturbation definition. The identity-matrix
quadratic sum has exactly the original Euclidean squared norm. -/
theorem targetGram_quadratic (a b:ℝ) (ha:-1<a) (hb:-1<b)
    (n:ℕ) (v:Fin (n+1)→ℝ) :
    (∑ i,∑ j, targetGram a b ha hb n i j*v i*v j) =
      (∑ i, (v i)^2)+(∑ i,∑ j, gramPerturbation a b ha hb n i j*v i*v j) := by
  -- The finite identity-matrix term contributes exactly the original Euclidean norm.
  classical
  have he (i j:Fin (n+1)) : targetGram a b ha hb n i j =
      (if i=j then (1:ℝ) else 0)+gramPerturbation a b ha hb n i j := by
    simp only [gramPerturbation,Matrix.sub_apply,Matrix.one_apply]
    ring
  simp_rw [he,add_mul,Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [pow_two]

/-- The actual original Gram matrices have one strictly positive uniform
quadratic lower bound on the entire original physical half prefix.
Use: principalGram_uniform_coercive and the Cholesky inverse bounds use
this genuine finite gap, with no undischarged positivity assumption.
Article: jacobi, Appendix C.4 (uniform Gram limit and coercivity).
Proof: the two actual continuum GL operators give one genuine positive
gap for their cell-integrated original-index forms. The complete
original two-edge Gram approximation differs uniformly by o(1/N).
The proved finite quadratic-error bound absorbs half the true gap,
including the original middle row and any zero padded coordinate. -/
theorem targetGram_uniform_coercive (a b:ℝ) (ha:-1<a) (hb:-1<b) :
    ∃ κ:ℝ, 0<κ ∧ ∃ N:ℕ, ∀ n≥N, ∀ v:Fin (n+1)→ℝ,
      (∀i, n+1<2*i.val → v i=0) →
      κ*(∑ i, (v i)^2) ≤ ∑ i,∑ j, targetGram a b ha hb n i j*v i*v j := by
  -- Reserve half the genuine cell-form gap to absorb the complete original Gram error.
  obtain ⟨κ,hκ,hC⟩ := cellPerturbation_coercive a b ha hb
  obtain ⟨N,hN⟩ := gramCell_uniform ha hb (κ/2) (by positivity)
  refine ⟨κ/2,by positivity,max N 1,fun n hn v hv => ?_⟩
  have hcell := hC n ((le_max_right N 1).trans hn) v hv
  have herror := half_quadratic_error
    (fun i j => gramPerturbation a b ha hb n i j-cellPerturbation a b ha hb n i j)
    (by positivity : 0≤κ/2) (hN n ((le_max_left N 1).trans hn)) v hv
  have hdiff : (∑ i,∑ j,
      (gramPerturbation a b ha hb n i j-cellPerturbation a b ha hb n i j)*v i*v j) =
      (∑ i,∑ j, gramPerturbation a b ha hb n i j*v i*v j)-
      (∑ i,∑ j, cellPerturbation a b ha hb n i j*v i*v j) := by
    simp_rw [sub_mul,Finset.sum_sub_distrib]
  rw [hdiff] at herror
  rw [targetGram_quadratic]
  have hh := (abs_le.mp herror).1
  linarith

end
end jacobi.Comparison
