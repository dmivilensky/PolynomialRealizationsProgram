import krylov.Convergence.SlidingFCConditioning
import krylov.Methods.ProjectedSearch

/-!
Article: main_krylov, thm:G, actual sliding residual staircase.
Use: transfer genuine line stationarity and retained observed conjugacy to
the terminal gradient, preserving the printed (dimension−1)^(3/2) factor.
Source: finite telescoping, symmetry of the true segment Hessians, and
Euclidean reconstruction in the actual normalized step frame.
-/

namespace krylov.Convergence
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Functions krylov.Reference
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Exact observed-gradient telescope in a Hilbert space, before imposing
any model approximation or independence. -/
theorem observed_path_staircase (g : ℕ → E) (s : ℕ → E) {i N : ℕ}
    (hi : i<N) (hline : inner ℝ (s i) (g (i+1))=0) :
    inner ℝ (s i) (g N)=
      ∑ j∈Finset.Ico (i+1) N,inner ℝ (s i) (g (j+1)-g j) := by
  have ht : g N-g (i+1)=∑ j∈Finset.Ico (i+1) N,(g (j+1)-g j) :=
    (Finset.sum_Ico_sub g hi).symm
  have he := congrArg (fun v=>inner ℝ (s i) v) ht
  simpa only [inner_sub_right,hline,sub_zero,inner_sum] using he

/-- A true symmetric older segment operator cancels against its measured
conjugacy equation, leaving exactly the operator difference. -/
theorem observed_pair_operator_difference (s t y : E) (A B : E →L[ℝ] E)
    (hs : A.toLinearMap.IsSymmetric) (hy : A s=y)
    (hc : inner ℝ y t=0) :
    inner ℝ s (B t)=inner ℝ s ((B-A) t) := by
  have hz : inner ℝ s (A t)=0 := by
    have hh := hs s t
    change inner ℝ (A s) t=inner ℝ s (A t) at hh
    rw [←hh,hy]
    exact hc
  simp only [_root_.sub_apply,inner_sub_right,hz,sub_zero]

/-- Finite exact FC staircase bound for each normalized old coordinate.
Only genuinely later step lengths enter its bound. -/
theorem conjugate_staircase_coordinate_bound (g s : ℕ → E) (A : ℕ → E →L[ℝ] E)
    (N : ℕ) {D B : ℝ} (hD : 0≤D) (hB : 0≤B)
    (hy : ∀ j<N,g (j+1)-g j=A j (s j))
    (hsym : ∀ j<N,(A j).toLinearMap.IsSymmetric)
    (hline : ∀ j<N,inner ℝ (s j) (g (j+1))=0)
    (hc : ∀ i j,i<j → j<N → inner ℝ (g (i+1)-g i) (s j)=0)
    (hdiff : ∀ i j,i<j → j<N → ‖A j-A i‖≤D)
    (hstep : ∀ j,0<j → j<N → ‖s j‖≤B)
    {i : ℕ} (hi : i<N) :
    |inner ℝ (‖s i‖⁻¹ • s i) (g N)|≤(N-1:ℕ)*D*B := by
  have hnorm : ‖‖s i‖⁻¹ • s i‖≤1 := by
    by_cases hz : s i=0
    · simp only [hz,smul_zero,norm_zero,zero_le_one]
    · rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]
  have ht := observed_path_staircase g (fun j=>‖s j‖⁻¹ • s j) hi (by
    simp only [real_inner_smul_left,hline i hi,mul_zero])
  rw [ht]
  calc
    _ ≤ ∑ j∈Finset.Ico (i+1) N,|inner ℝ (‖s i‖⁻¹ • s i) (g (j+1)-g j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j∈Finset.Ico (i+1) N,D*B := by
      apply Finset.sum_le_sum
      intro j hj
      obtain ⟨hij,hjN⟩ := Finset.mem_Ico.mp hj
      have hj : i<j := by omega
      have he := observed_pair_operator_difference (s i) (s j) (g (i+1)-g i)
        (A i) (A j) (hsym i hi) (hy i hi).symm (hc i j hj hjN)
      rw [hy j hjN,real_inner_smul_left,he,←real_inner_smul_left]
      have hh := norm_inner_le_norm (𝕜:=ℝ) (‖s i‖⁻¹ • s i) ((A j-A i) (s j))
      rw [Real.norm_eq_abs] at hh
      have hb := ((A j-A i).le_opNorm (s j)).trans
        (mul_le_mul (hdiff i j hj hjN) (hstep j (by omega) hjN)
          (norm_nonneg _) hD)
      exact hh.trans ((mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)).trans
        (by simpa only [one_mul] using hb))
    _ ≤ (N-1:ℕ)*D*B := by
      simp only [Finset.sum_const,Nat.card_Ico,nsmul_eq_mul]
      have hcN : (N-(i+1):ℕ)≤N-1 := by omega
      exact (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcN) (mul_nonneg hD hB)).trans_eq
        (by ring)

/-- A zero final coordinate preserves the norm of the chronological old
coordinates. This keeps dimension−1, rather than dimension, in thm:G. -/
theorem coordinate_norm_zero_last (v : Fin (n+1) → ℝ) (h : v (Fin.last n)=0) :
    ‖WithLp.toLp 2 v‖=‖WithLp.toLp 2 (fun i : Fin n=>v i.castSucc)‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.real_norm_sq_eq,Fin.sum_univ_castSucc,h,zero_pow (by decide : 2≠0),add_zero]

/-- Reconstruction in a genuinely nonsingular normalized full frame.
The actual inverse norm is retained for its sharp limit one. -/
theorem full_frame_residual_bound (s : Fin (n+1) → EuclideanSpace ℝ (Fin (n+1)))
    (g : EuclideanSpace ℝ (Fin (n+1))) (hu : IsUnit (windowMatrix s).det)
    {C : ℝ} (hC : 0≤C) (hlast : inner ℝ (s (Fin.last n)) g=0)
    (hold : ∀ i : Fin n,|inner ℝ (s i.castSucc) g|≤C) :
    ‖g‖≤‖(windowMatrix s)⁻¹‖*(Real.sqrt n*C) := by
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
  have hcoords : ‖r‖≤Real.sqrt n*C := by
    rw [show ‖r‖=‖WithLp.toLp 2 (fun i : Fin n=>coordinates s g i.castSucc)‖ from
      coordinate_norm_zero_last _ hlast]
    exact coordinate_norm_le_sqrt_card _ hC hold
  have hinv : ‖cgOperator Vᵀ⁻¹‖=‖V⁻¹‖ := by
    rw [cgOperator,Matrix.l2_opNorm_toEuclideanCLM,←transpose_nonsing_inv]
    simpa only [Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial]
      using norm_star (V⁻¹)
  calc
    ‖g‖=‖cgOperator Vᵀ⁻¹ r‖ := congrArg norm hg
    _ ≤ ‖cgOperator Vᵀ⁻¹‖*‖r‖ := (cgOperator Vᵀ⁻¹).le_opNorm r
    _ ≤ ‖V⁻¹‖*(Real.sqrt n*C) := by rw [hinv]; exact mul_le_mul_of_nonneg_left hcoords (norm_nonneg _)

end
end krylov.Convergence
