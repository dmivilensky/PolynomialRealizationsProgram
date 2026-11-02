import krylov.XR.ConditionalUpper

/-!
Article: main_krylov, prop:cond, data-only observation dictionary.
Use: identify the hidden-normalized ratio with the signed actually
observed pairing ratio, including arbitrary positive conjugate column
scales. Source: uniqueness of the positive square root of a diagonal
matrix and the original chronological observation convention.
-/
namespace krylov.XR
noncomputable section
open Matrix krylov.Secant
open scoped Matrix.Norms.L2Operator MatrixOrder

/-- The canonical positive root of a positive diagonal base is its
entrywise positive root. Article: main_krylov, prop:cond. -/
theorem metricRoot_diagonal {p : ℕ} (d : Fin p → ℝ) (hd : ∀ i,0≤d i) :
    metricRoot (diagonal d)=diagonal (fun i=>Real.sqrt (d i)) := by
  let R := diagonal (fun i=>Real.sqrt (d i))
  have hs : R*R=diagonal d := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simpa only [pow_two] using Real.sq_sqrt (hd i)
  calc
    _ = CFC.sqrt (R*R) := congrArg CFC.sqrt hs.symm
    _ = R := by
      apply CFC.sqrt_mul_self
      exact Matrix.PosSemidef.nonneg
        (Matrix.posSemidef_diagonal_iff.mpr (fun i=>Real.sqrt_nonneg (d i)))

/-- Canonical whitening in a true diagonal base is actual diagonal
pair rescaling, with its precise positive factors. Article: prop:cond. -/
theorem relativeOperator_diagonal {p : ℕ} (d : Fin p → ℝ) (hd : ∀ i,0<d i)
    (X : Matrix (Fin p) (Fin p) ℝ) :
    relativeOperator (diagonal d) X=
      diagonal (fun i=>(Real.sqrt (d i))⁻¹)*X*diagonal (fun i=>(Real.sqrt (d i))⁻¹) := by
  have hi : (diagonal (fun i=>Real.sqrt (d i)))⁻¹=
      diagonal (fun i=>(Real.sqrt (d i))⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [diagonal_mul_diagonal]
    rw [←diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (Real.sqrt_pos.mpr (hd i)).ne'
  simp only [relativeOperator,metricRoot_diagonal d (fun i=>(hd i).le),hi]

/-- The signed normalized cross datum is unchanged by every positive
pair rescaling. Article: prop:cond(b), delta'=M01/sqrt(M00 M11). -/
theorem conditional_observed_ratio_rescale (M : Matrix (Fin 2) (Fin 2) ℝ)
    (h₀ : 0<M 0 0) (h₁ : 0<M 1 1) (r : Fin 2 → ℝ) (hr : ∀ i,0<r i) :
    let N := diagonal r*M*diagonal r
    N 0 1/Real.sqrt (N 0 0*N 1 1)=M 0 1/Real.sqrt (M 0 0*M 1 1) := by
  dsimp only
  simp only [diagonal_mul,mul_diagonal]
  have hs : Real.sqrt ((r 0*M 0 0*r 0)*(r 1*M 1 1*r 1))=
      r 0*r 1*Real.sqrt (M 0 0*M 1 1) := by
    have he : (r 0*M 0 0*r 0)*(r 1*M 1 1*r 1)=(r 0*r 1)^2*(M 0 0*M 1 1) := by ring
    rw [he,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (mul_pos (hr 0) (hr 1)).le]
  rw [hs]
  have hnonzero := (Real.sqrt_pos.mpr (mul_pos h₀ h₁)).ne'
  field_simp [(hr 0).ne', (hr 1).ne']

/-- The actual canonical pairing matrix in an initially conjugate
window has the printed triangular entries. Article: prop:cond(a,b). -/
theorem conditional_normalized_observation (C : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (d : Fin 2 → ℝ) (hd : ∀ i,0<d i) (hbase : C 0=diagonal d) :
    let K := relativeOperator (diagonal d) (C 1-C 0)
    diagonal (fun i=>(Real.sqrt (d i))⁻¹)*observed C*
      diagonal (fun i=>(Real.sqrt (d i))⁻¹)=!![1,K 0 1;0,1+K 1 1] := by
  dsimp only
  rw [relativeOperator_diagonal d hd]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonal_mul,mul_diagonal,observed,hbase]
  all_goals
    have hzero := (Real.sqrt_pos.mpr (hd 0)).ne'
    have hone := (Real.sqrt_pos.mpr (hd 1)).ne'
    have hs₀ := Real.sq_sqrt (hd 0).le
    have hs₁ := Real.sq_sqrt (hd 1).le
    field_simp
    nlinarith

/-- The hidden-normalized ratio in the conditional upper theorem equals
the signed ratio formed directly from the original observed matrix.
Its observed diagonal energies are positive consequences of the genuine
base and the already derived positive hidden diagonal. Article: prop:cond(b). -/
theorem conditional_original_observation_ratio (C : ℕ → Matrix (Fin 2) (Fin 2) ℝ)
    (d : Fin 2 → ℝ) (hd : ∀ i,0<d i) (hbase : C 0=diagonal d)
    (hk : 0<1+relativeOperator (diagonal d) (C 1-C 0) 1 1) :
    let K := relativeOperator (diagonal d) (C 1-C 0)
    let M := observed C
    0<M 0 0 ∧ 0<M 1 1 ∧
      M 0 1/Real.sqrt (M 0 0*M 1 1)=K 0 1/Real.sqrt (1+K 1 1) := by
  let r := fun i=>(Real.sqrt (d i))⁻¹
  have hr (i : Fin 2) : 0<r i := inv_pos.mpr (Real.sqrt_pos.mpr (hd i))
  have hN := conditional_normalized_observation C d hd hbase
  have hm₀ : 0<observed C 0 0 := by simpa only [observed,Fin.val_zero,hbase,diagonal_apply_eq] using hd 0
  have hn₁ := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℝ=>N 1 1) hN
  have hp : 0<r 1*observed C 1 1*r 1 := by
    have he : r 1*observed C 1 1*r 1=1+relativeOperator (diagonal d) (C 1-C 0) 1 1 := by
      simpa [r,diagonal_mul,mul_diagonal] using hn₁
    rw [he]
    exact hk
  have hm₁ : 0<observed C 1 1 :=
    (mul_pos_iff_of_pos_left (hr 1)).mp ((mul_pos_iff_of_pos_right (hr 1)).mp hp)
  refine ⟨hm₀,hm₁,?_⟩
  have hh := conditional_observed_ratio_rescale (observed C) hm₀ hm₁ r hr
  dsimp only at hh
  rw [hN] at hh
  simpa using hh.symm

end
end krylov.XR
