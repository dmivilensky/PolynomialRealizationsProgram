import jacobi.Finite.FlowSortingPolynomials

/-!
Matrix sorting from the genuine dominant-atom polynomial limits.
The subleading continuant coefficient is minus the physical prefix trace.
Its limit fixes every diagonal entry. Orthogonal spectral invariance fixes
the complete sum of squared entries, so every off-diagonal entry vanishes.
Use: FlowSorting specializes this finite-dimensional theorem to the actual
resolvent exponential tilt in both time directions.
Article: jacobi, Proposition 5.5 and Section 5.6.
Article role: both sorted matrix limits, limiting Richardson energy and its quartic Jacobi
asymptotic.
-/
namespace jacobi.Finite
noncomputable section
open Real Polynomial Filter Set Matrix chebyshev1 chebyshev2
open scoped Topology BigOperators Classical
set_option backward.isDefEq.respectTransparency false

/-- The physical prefix trace is the negative subleading continuant
coefficient. This identity holds for every finite Jacobi chain.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem prefix_diagonal_coefficient {N m : ℕ} (J : Jacobi N) (hm : 0 < m) :
    (∑ j∈Finset.range m,J.data.b j)= -(J.data.leading m).coeff (m-1) := by
  let : Nonempty (Fin m) := ⟨⟨0,hm⟩⟩
  have h := Matrix.trace_eq_neg_charpoly_coeff (J.data.matrix 0 m)
  rw [← J.data.block_eq_charpoly J.coupling_nonneg] at h
  simpa only [JacobiData.leading,Matrix.trace,Matrix.diag_apply,
    JacobiData.matrix_apply,ite_true,Nat.zero_add,Fin.sum_univ_eq_sum_range,Fintype.card_fin] using h

/-- Every physical prefix trace converges to the corresponding sum of
dominant spectral atoms. The empty and full prefixes are included.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem reconstructed_prefix_limit {N : ℕ} (M : ℝ → DiscreteMeasure N)
    (x : Fin N → ℝ) (hx : ∀ t,(M t).node=x) (ord : Fin N ≃ Fin N)
    (hratio : ∀ j k : Fin N,j < k →
      Tendsto (fun t : ℝ => (M t).weight (ord k)/(M t).weight (ord j)) atTop (𝓝 0))
    (m : ℕ) (hm : m≤N) :
    Tendsto (fun t : ℝ => ∑ j∈Finset.range m,(M t).reconstructed.data.b j) atTop
      (𝓝 (∑ j : Fin m,x (ord ⟨j.val,j.isLt.trans_le hm⟩))) := by
  by_cases hm0 : m=0
  · subst m
    simp only [Finset.range_zero,Finset.sum_empty,Finset.univ_eq_empty,Finset.sum_empty]
    exact tendsto_const_nhds
  have hmp : 0 < m := Nat.pos_of_ne_zero hm0
  simp_rw [prefix_diagonal_coefficient _ hmp]
  by_cases hlt : m < N
  · have h := (leading_subleading_limit M x hx ord hratio ⟨m,hlt⟩ hmp).neg
    simpa only [Fin.val_mk,neg_neg] using h
  · have hmN : m=N := by omega
    subst m
    have he (t : ℝ) : ((M t).reconstructed.data.leading N).coeff (N-1)=
        -(∑ j : Fin N,x j) := by
      have hp : (M t).reconstructed.data.leading N=(M t).reconstructed.matrix.charpoly :=
        (M t).reconstructed.data.block_eq_charpoly (M t).reconstructed.coupling_nonneg 0 N
      rw [hp,(M t).reconstructed_charpoly,hx]
      simpa only [Finset.card_univ,Fintype.card_fin] using
        prod_X_sub_C_coeff_card_pred Finset.univ x (by simpa using hmp)
    simp_rw [he,neg_neg]
    have hs : (∑ j : Fin N,x j)=∑ j : Fin N,x (ord ⟨j.val,j.isLt.trans_le hm⟩) := by
      simpa only [Fin.eta] using (Equiv.sum_comp ord x).symm
    rw [hs]
    exact tendsto_const_nhds

/-- The actual diagonal entries converge in the selected dominance order.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem reconstructed_diagonal_limit {N : ℕ} (M : ℝ → DiscreteMeasure N)
    (x : Fin N → ℝ) (hx : ∀ t,(M t).node=x) (ord : Fin N ≃ Fin N)
    (hratio : ∀ j k : Fin N,j < k →
      Tendsto (fun t : ℝ => (M t).weight (ord k)/(M t).weight (ord j)) atTop (𝓝 0))
    (i : Fin N) :
    Tendsto (fun t : ℝ => (M t).reconstructed.matrix i i) atTop (𝓝 (x (ord i))) := by
  have h := (reconstructed_prefix_limit M x hx ord hratio (i.val+1) i.isLt).sub
    (reconstructed_prefix_limit M x hx ord hratio i.val i.isLt.le)
  have he (t : ℝ) : (∑ j∈Finset.range (i.val+1),(M t).reconstructed.data.b j)-
      (∑ j∈Finset.range i.val,(M t).reconstructed.data.b j)=
      (M t).reconstructed.matrix i i := by
    rw [Finset.sum_range_succ]
    simp [Jacobi.matrix,JacobiData.matrix_apply]
  have hs : (∑ j : Fin (i.val+1),x (ord ⟨j.val,j.isLt.trans_le i.isLt⟩))-
      (∑ j : Fin i.val,x (ord ⟨j.val,j.isLt.trans_le i.isLt.le⟩))=x (ord i) := by
    rw [Fin.sum_univ_castSucc]
    simp
  simpa only [he,hs] using h

/-- The full sum of squared entries is exactly the fixed spectral
second trace. This removes all remaining off-diagonal freedom.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem DiscreteMeasure.reconstructed_square_sum {N : ℕ} (M : DiscreteMeasure N) :
    (∑ i,∑ j,(M.reconstructed.matrix i j)^2)=∑ k,(M.node k)^2 := by
  have he : M.reconstructed.matrix=M.eigenvectors*diagonal M.node*M.eigenvectorsᵀ := by
    rw [M.reconstructed_matrix,M.multiplication_diagonalization]
  have hs : M.reconstructed.matrix*M.reconstructed.matrix=M.eigenvectors*diagonal (fun k => (M.node k)^2)*M.eigenvectorsᵀ := by
    rw [he]
    calc
      _=M.eigenvectors*(diagonal M.node*(M.eigenvectorsᵀ*M.eigenvectors)*diagonal M.node)*M.eigenvectorsᵀ := by
        simp only [Matrix.mul_assoc]
      _=_ := by rw [M.eigenvectors_transpose_mul,Matrix.mul_one,Matrix.diagonal_mul_diagonal]; simp [pow_two]
  have ht := congrArg Matrix.trace hs
  rw [Matrix.trace_mul_cycle,M.eigenvectors_transpose_mul,Matrix.one_mul,Matrix.trace_diagonal] at ht
  rw [← ht]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.diag_apply,Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [← M.reconstructed.matrix_isHermitian.isSymm.apply i j,pow_two]

/-- Convergent diagonals and the fixed spectral second trace force the
whole actual matrix to converge to the sorted diagonal. The proof uses
only finite sums of squares and includes every off-diagonal entry.
Article: jacobi, Proposition 5.5 and Section 5.6.
-/
theorem reconstructed_matrix_sorting {N : ℕ} (M : ℝ → DiscreteMeasure N)
    (x : Fin N → ℝ) (hx : ∀ t,(M t).node=x) (ord : Fin N ≃ Fin N)
    (hratio : ∀ j k : Fin N,j < k →
      Tendsto (fun t : ℝ => (M t).weight (ord k)/(M t).weight (ord j)) atTop (𝓝 0)) :
    Tendsto (fun t : ℝ => (M t).reconstructed.matrix) atTop
      (𝓝 (diagonal (fun i => x (ord i)))) := by
  let D := diagonal (fun i => x (ord i))
  let E t := ∑ i,∑ j,((M t).reconstructed.matrix i j-D i j)^2
  have he (t : ℝ) : E t=2*(∑ i,(x (ord i))^2)-
      2*(∑ i,(M t).reconstructed.matrix i i*x (ord i)) := by
    have hs : (∑ i,∑ j,((M t).reconstructed.matrix i j)^2)=∑ i,(x (ord i))^2 := by
      rw [(M t).reconstructed_square_sum,hx]
      exact (Equiv.sum_comp ord (fun i => (x i)^2)).symm
    have hexp : E t=(∑ i,∑ j,((M t).reconstructed.matrix i j)^2)-
        2*(∑ i,(M t).reconstructed.matrix i i*x (ord i))+(∑ i,(x (ord i))^2) := by
      dsimp only [E,D]
      simp only [sub_sq,Matrix.diagonal_apply,Finset.sum_add_distrib,Finset.sum_sub_distrib,
        Finset.mul_sum]
      simp
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hexp,hs]
    ring
  have hdiag := tendsto_finsetSum Finset.univ (fun i _ =>
    (reconstructed_diagonal_limit M x hx ord hratio i).mul_const (x (ord i)))
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := (tendsto_const_nhds (x := 2*(∑ i,(x (ord i))^2))).sub (hdiag.const_mul 2)
    change Tendsto (fun t : ℝ => E t) atTop (𝓝 0)
    simp_rw [he]
    simpa only [pow_two,sub_self] using h
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hs : Tendsto (fun t : ℝ => ((M t).reconstructed.matrix i j-D i j)^2) atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) _ hE
    intro t
    exact (Finset.single_le_sum (fun k _ => sq_nonneg ((M t).reconstructed.matrix i k-D i k))
      (Finset.mem_univ j)).trans (Finset.single_le_sum (fun k _ =>
        Finset.sum_nonneg (fun l _ => sq_nonneg ((M t).reconstructed.matrix k l-D k l))) (Finset.mem_univ i))
  have habs := hs.sqrt
  simp only [sqrt_zero,sqrt_sq_eq_abs] at habs
  exact tendsto_sub_nhds_zero_iff.mp (tendsto_zero_iff_norm_tendsto_zero.mpr
    (by simpa only [Real.norm_eq_abs] using habs))

end
end jacobi.Finite
