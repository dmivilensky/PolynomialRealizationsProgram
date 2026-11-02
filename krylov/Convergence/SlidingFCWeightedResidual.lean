import krylov.Convergence.SlidingFCSourceResidual

/-!
Article: main_krylov, thm:G, isolation of the oldest/next staircase term.
Use: preserve individual pair contributions rather than a uniform common
bound. Source: the exact observed telescope, scalar Schwarz symmetry and
actual frame reconstruction. This retains the sharp one-half coefficient.
-/
namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Reference
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {n : ℕ}
set_option maxHeartbeats 800000

/-- The true FC staircase retains every genuine operator difference and
later step length separately. -/
theorem conjugate_staircase_weighted_coordinate (g s : ℕ → E) (A : ℕ → E →L[ℝ] E)
    (N : ℕ) (hy : ∀ j<N,g (j+1)-g j=A j (s j))
    (hsym : ∀ j<N,(A j).toLinearMap.IsSymmetric)
    (hline : ∀ j<N,inner ℝ (s j) (g (j+1))=0)
    (hc : ∀ i j,i<j → j<N → inner ℝ (g (i+1)-g i) (s j)=0)
    {i : ℕ} (hi : i<N) :
    |inner ℝ (‖s i‖⁻¹ • s i) (g N)|≤
      ∑ j∈Finset.Ico (i+1) N,‖A j-A i‖*‖s j‖ := by
  have hu : ‖‖s i‖⁻¹ • s i‖≤1 := by
    by_cases hz : s i=0
    · simp only [hz,smul_zero,norm_zero,zero_le_one]
    · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  rw [observed_path_staircase g (fun j=>‖s j‖⁻¹ • s j) hi
    (by simp only [real_inner_smul_left,hline i hi,mul_zero])]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j hj
  obtain ⟨hij,hjN⟩ := Finset.mem_Ico.mp hj
  have he := observed_pair_operator_difference (s i) (s j) (g (i+1)-g i) (A i) (A j)
    (hsym i hi) (hy i hi).symm (hc i j (by omega) hjN)
  rw [hy j hjN,real_inner_smul_left,he,←real_inner_smul_left]
  have hh := norm_inner_le_norm (𝕜:=ℝ) (‖s i‖⁻¹ • s i) ((A j-A i) (s j))
  rw [Real.norm_eq_abs] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right hu (norm_nonneg _)).trans
    (by simpa only [one_mul] using (A j-A i).le_opNorm (s j)))

/-- The Euclidean coefficient norm is at most its genuine absolute sum. -/
theorem euclidean_norm_le_sum_abs (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 v‖≤∑ i,|v i| := by
  have he : WithLp.toLp 2 v=∑ i : Fin n,(PiLp.single 2 i (v i):EuclideanSpace ℝ (Fin n)) := by
    ext j
    simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.single_apply,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [he]
  exact (norm_sum_le _ _).trans_eq (by simp only [PiLp.norm_single,Real.norm_eq_abs])

/-- Actual full-frame reconstruction with the separate absolute old
coordinates; one exceptional pair therefore incurs no dimension factor. -/
theorem full_frame_residual_sum_bound
    (s : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (g : EuclideanSpace ℝ (Fin (n+1))) (hu : IsUnit (windowMatrix s).det) :
    ‖g‖≤‖(windowMatrix s)⁻¹‖*∑ i,|inner ℝ (s i) g| := by
  let V := windowMatrix s
  let r := WithLp.toLp 2 (coordinates s g)
  have hr : r=cgOperator Vᵀ g := by
    change WithLp.toLp 2 (coordinates s g)=_
    rw [coordinates_windowMatrix]
    rfl
  have hg : g=cgOperator Vᵀ⁻¹ r := by
    rw [hr]
    change g=WithLp.toLp 2 (Vᵀ⁻¹*ᵥ(Vᵀ*ᵥWithLp.ofLp g))
    rw [mulVec_mulVec,nonsing_inv_mul _ (by simpa only [det_transpose] using hu),one_mulVec]
  have hinv : ‖cgOperator Vᵀ⁻¹‖=‖V⁻¹‖ := by
    rw [cgOperator,Matrix.l2_opNorm_toEuclideanCLM,←transpose_nonsing_inv]
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using norm_star (V⁻¹)
  calc
    ‖g‖=‖cgOperator Vᵀ⁻¹ r‖ := congrArg norm hg
    _ ≤ ‖cgOperator Vᵀ⁻¹‖*‖r‖ := (cgOperator Vᵀ⁻¹).le_opNorm r
    _ ≤ _ := by rw [hinv];exact mul_le_mul_of_nonneg_left (euclidean_norm_le_sum_abs _) (norm_nonneg _)

/-- The full genuine FC residual is bounded by the sum of its separate
chronological pair contributions. A single dominant pair retains factor1. -/
theorem conjugate_staircase_weighted_frame
    (g s : ℕ → EuclideanSpace ℝ (Fin (n+1)))
    (A : ℕ → EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (hy : ∀ j<n+1,g (j+1)-g j=A j (s j))
    (hsym : ∀ j<n+1,(A j).toLinearMap.IsSymmetric)
    (hline : ∀ j<n+1,inner ℝ (s j) (g (j+1))=0)
    (hc : ∀ i j,i<j → j<n+1 → inner ℝ (g (i+1)-g i) (s j)=0)
    (hu : IsUnit (windowMatrix (unitWindow (fun i : Fin (n+1)=>s i.val))).det) :
    ‖g (n+1)‖≤‖(windowMatrix (unitWindow (fun i : Fin (n+1)=>s i.val)))⁻¹‖*
      ∑ i : Fin (n+1),∑ j : Fin (n+1),if i<j then ‖A j.val-A i.val‖*‖s j.val‖ else 0 := by
  apply (full_frame_residual_sum_bound _ _ hu).trans
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro i _hi
  have hh := conjugate_staircase_weighted_coordinate g s A (n+1) hy hsym hline hc i.isLt
  have hset : Finset.Ico (i.val+1) (n+1)=(Finset.range (n+1)).filter (fun j=>i.val<j) := by
    ext j
    simp only [Finset.mem_Ico,Finset.mem_filter,Finset.mem_range]
    omega
  rw [hset,Finset.sum_filter] at hh
  change |inner ℝ (‖s i.val‖⁻¹ • s i.val) (g (n+1))|≤_
  rw [←Fin.sum_univ_eq_sum_range (fun j : ℕ=>if i.val<j then ‖A j-A i.val‖*‖s j‖ else 0)] at hh
  exact hh

end
end krylov.Convergence
