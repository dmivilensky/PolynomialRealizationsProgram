import krylov.Methods.DirectionReindex
import krylov.Methods.ProjectedSearch

/-!
Article: main_krylov, thm:A and apB:lem:UAsteps, direction-based actual FC staircase.
Use: reconstruct a defined actual FC cycle through its genuine directions,
without imposing a nonzero last line step that the source does not require.
Source: actual nonsingular observed solves, exact real line searches and
finite telescoping of the true queried gradients.
-/

namespace krylov.Methods
noncomputable section
open Matrix krylov.Reference
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A genuine nonsingular cross-Gram solve has no zero synthesis column.
Use: any step retained by a later defined solve is truly nonzero.
Article: main_krylov, apB:lem:UAsteps.
Proof: a zero actual column would make the true finite coefficient determinant zero. -/
theorem crossGram_right_ne_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s y : ι → E) (hu : IsUnit (crossGram y s).det) (i : ι) : s i≠0 := by
  intro hs
  apply isUnit_iff_ne_zero.mp hu
  apply Matrix.det_eq_zero_of_column_eq_zero i
  intro j
  simp only [crossGram,hs,inner_zero_right]

/-- Every actual FC step used by the next defined solve is nonzero.
Use: positivity of the final step length is unnecessary; only genuinely retained preceding steps are divided by.
Article: main_krylov, apB:lem:UAsteps.
Proof: the actual fixed-age coordinates identify that step with the newest
column of the genuine nonsingular next observed conjugacy matrix. -/
theorem fullFC_step_ne_of_next_solve
    (A : ℕ → E →L[ℝ] E) (g : E) (i : ℕ)
    (hsolve : IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g (i+1))))).det) :
    fcStep fullMemory A g i≠0 := by
  rw [fullFC_conjugacy_det_array] at hsolve
  simpa only [Nat.add_sub_cancel,Nat.sub_zero,Fin.val_zero] using
    crossGram_right_ne_zero _ _ hsolve (0 : Fin (i+1))

/-- The true full-memory FC direction annihilates each real earlier secant image.
Use: this direction equation remains valid when the current exact line scalar is zero.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: locate the genuine earlier pair in the actual retained transcript;
its true coefficient-solve equation is exactly the desired old-image pairing. -/
theorem fullFC_direction_conjugate (A : ℕ → E →L[ℝ] E) (g : E) {i k : ℕ} (hi : i<k)
    (hC : IsUnit (crossGram (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det) :
    inner ℝ (fcDirection fullMemory A g k) (fcSecant fullMemory A g i)=0 := by
  -- Locate the real observed old pair in the true window used by the actual inverse solve.
  let W := selectedWindow fullMemory (fcHistory fullMemory A g k)
  have hp : (fcStep fullMemory A g i,fcSecant fullMemory A g i)∈W := by
    rw [show W=executedPairs (fcStep fullMemory A g) (fcSecant fullMemory A g) k from fullFC_window A g k]
    exact executedPairs_contains _ _ hi
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hp
  have he := congrFun (conjugacyDirection_conjugate (windowSteps W) (windowImages W)
    (fcGradient fullMemory A g k) hC) j
  have hy : windowImages W j=fcSecant fullMemory A g i := congrArg Prod.snd hj
  change inner ℝ (windowImages W j) (fcDirection fullMemory A g k)=0 at he
  rw [hy,real_inner_comm] at he
  exact he

/-- The actual defined exact FC search makes the direction orthogonal to its true next gradient.
Use: retain the final search equation even for a zero actual line displacement.
Article: main_krylov, thm:A and apB:lem:UAsteps.
Proof: apply the real searched-gradient identity with its actual nonzero curvature. -/
theorem fullFC_direction_line_orth (A : ℕ → E →L[ℝ] E) (g : E) (i : ℕ)
    (hc : inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g i))≠0) :
    inner ℝ (fcDirection fullMemory A g i) (fcGradient fullMemory A g (i+1))=0 :=
  searchedGradient_inner_zero _ _ _ hc

/-- The actual defined FC cycle has its exact operator-defect staircase in true direction coordinates, allowing a zero last line displacement.
Use: the global uniform remainder can use a genuine well-conditioned direction basis without strengthening the source defined-cycle hypothesis.
Article: main_krylov, thm:A, exact full-cycle residual.
Proof: telescope the real observed secant updates from each actual line
orthogonality equation. A later defined solve forces every earlier retained
step nonzero; divide only by those real earlier line scalars to transfer
observed conjugacy to directions. True older-operator symmetry removes the
old action, leaving precisely the actual operator difference on each real step. -/
theorem fullFC_direction_staircase (A : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hsym : ∀ i<N, (A i).toLinearMap.IsSymmetric)
    (hsolve : ∀ k<N, IsUnit (crossGram
      (windowImages (selectedWindow fullMemory (fcHistory fullMemory A g k)))
      (windowSteps (selectedWindow fullMemory (fcHistory fullMemory A g k)))).det)
    (hcurv : ∀ k<N, inner ℝ (fcDirection fullMemory A g k) (A k (fcDirection fullMemory A g k))≠0)
    {i : ℕ} (hi : i<N) :
    inner ℝ (fcDirection fullMemory A g i) (fcGradient fullMemory A g N)=
      ∑ j∈Finset.Ico (i+1) N, inner ℝ (fcDirection fullMemory A g i)
        ((A j-A i) (fcStep fullMemory A g j)) := by
  -- The exact telescope is taken along the actually evaluated steps, including a possible zero final step.
  have htel : fcGradient fullMemory A g N-fcGradient fullMemory A g (i+1)=
      ∑ j∈Finset.Ico (i+1) N, fcSecant fullMemory A g j := by
    rw [← Finset.sum_Ico_sub _ hi]
    apply Finset.sum_congr rfl
    intro j _
    rw [fcGradient_succ,add_sub_cancel_left]
  have he := congrArg (fun v => inner ℝ (fcDirection fullMemory A g i) v) htel
  rw [inner_sub_right,fullFC_direction_line_orth A g i (hcurv i hi),sub_zero,inner_sum] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hij,hjN⟩ := Finset.mem_Ico.mp hj
  have hn := fullFC_step_ne_of_next_solve A g i (hsolve (i+1) (by omega))
  have hα : lineLength (fcGradient fullMemory A g i) (fcDirection fullMemory A g i)
      (A i (fcDirection fullMemory A g i))≠0 := by
    intro hz
    apply hn
    simp only [fcStep,hz,zero_smul]
  have hc := fullFC_direction_conjugate A g (show i<j by omega) (hsolve j hjN)
  rw [fcSecant,fcStep,map_smul,real_inner_smul_right] at hc
  have ho := (mul_eq_zero.mp hc).resolve_left hα
  have hAi : inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g j))=0 := by
    have hs := (hsym i hi) (fcDirection fullMemory A g i) (fcDirection fullMemory A g j)
    change inner ℝ (A i (fcDirection fullMemory A g i)) (fcDirection fullMemory A g j)=
      inner ℝ (fcDirection fullMemory A g i) (A i (fcDirection fullMemory A g j)) at hs
    rw [← hs,real_inner_comm]
    exact ho
  simp only [_root_.sub_apply,inner_sub_right,fcSecant,fcStep,map_smul,real_inner_smul_right,hAi,sub_zero]
end
end krylov.Methods
