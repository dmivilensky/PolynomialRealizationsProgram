import krylov.Information.FormCoordinates
import krylov.Information.FlagMetric

/-!
Article: main_krylov, s4:cor-Q, genuine pre-quadratic near-conjugacy geometry.
Use: derive the original sharp Gram defect from actual primitive increment
budgets and true common CG probe actions, before any reflection or slack claim.
Source: exact positive-root metric pairing, genuine CG conjugacy, normalized
actual operator-angle bounds and the proved sharp Gershgorin Gram estimate.
-/

namespace krylov.Information
noncomputable section
open Matrix krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.LinearAlgebra
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {N : ℕ}

/-- The actual energy-normalized direction-coordinate Gram is exactly the Gram of its true unit canonical physical columns on the derived nonsingular domain.
Use: identify the source flag defect with real normalized physical direction angles.
Article: main_krylov, s4:cor-Q and apD:centre, true physical normalized direction Gram.
Proof: true compressed entries are actual root-image pairings, so every original energy square root is its real column norm. Actual full rank gives positive normalizers. Their genuine diagonal inverse cancels pointwise, leaving precisely the original normalized physical column pairings. -/
theorem normalizedDirectionGram_unitWindow (A D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef) (hD : IsUnit D.det) :
    normalizedDirectionGram (Dᵀ*A*D)=crossGram
      (fun i => NormedSpace.normalize (cgOperator (metricRoot A) (euclideanColumn D i)))
      (fun i => NormedSpace.normalize (cgOperator (metricRoot A) (euclideanColumn D i))) := by
  -- Derive actual normalization energies from the genuine compressed physical pairings.
  let u := fun i => cgOperator (metricRoot A) (euclideanColumn D i)
  have hpair (i j : Fin (N+1)) : (Dᵀ*A*D) i j=inner ℝ (u i) (u j) := by
    have he := compressed_entry_pairing D A i j
    change (Dᵀ*A*D) i j=inner ℝ (euclideanColumn D i) (cgOperator A (euclideanColumn D j)) at he
    rw [he]
    have ha : cgOperator A (euclideanColumn D j)=cgOperator (metricRoot A) (u j) := by
      simp only [u,cgOperator,← mul_apply_eq_comp,← map_mul,metricRoot_square A hA]
    rw [ha,root_pairing]
  have hdiag (i : Fin (N+1)) : Real.sqrt ((Dᵀ*A*D) i i)=‖u i‖ := by
    rw [hpair,real_inner_self_eq_norm_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]
  have hn (i : Fin (N+1)) : ‖u i‖≠0 := by
    have hi := columnEnergies_pos A D hA hD i
    change 0<‖u i‖ at hi
    exact hi.ne'
  have hN : (directionScale (Dᵀ*A*D))⁻¹=diagonal (fun i => ‖u i‖⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [directionScale,diagonal_mul_diagonal,← diagonal_one]
    congr 1
    funext i
    rw [hdiag,inv_mul_cancel₀ (hn i)]
  ext i j
  simp only [normalizedDirectionGram,hN,Matrix.diagonal_mul,Matrix.mul_diagonal,
    crossGram,NormedSpace.normalize,real_inner_smul_left,real_inner_smul_right,hpair]
  dsimp only [u]
  ring


/-- Every actual normalized physical matrix column is exactly the genuine zero-safe unit normalization of the original root-image column.
Use: reuse the proved true normalized-column unit-norm theorem in the original source direction geometry.
Article: main_krylov, s4:cor-Q and apD:centre, true physical normalized direction Gram.
Proof: the original right diagonal multiplication rescales each true physical column by its own inverse energy. That energy is exactly the norm of the real root-image column. -/
theorem normalizedColumns_column (A D : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (i : Fin (N+1)) :
    euclideanColumn (normalizedColumns A D) i=
      NormedSpace.normalize (cgOperator (metricRoot A) (euclideanColumn D i)) := by
  -- Preserve the real column and its own actual inverse-energy scaling.
  have he : euclideanColumn (normalizedColumns A D) i=
      (columnEnergies A D i)⁻¹ • euclideanColumn (metricRoot A*D) i := by
    ext a
    simp only [euclideanColumn,normalizedColumns,mul_diagonal,PiLp.smul_apply,smul_eq_mul]
    exact mul_comm _ _
  have hcol : euclideanColumn (metricRoot A*D) i=cgOperator (metricRoot A) (euclideanColumn D i) := rfl
  rw [he]
  change ‖euclideanColumn (metricRoot A*D) i‖⁻¹ • euclideanColumn (metricRoot A*D) i=_
  rw [hcol]
  rfl

end
end krylov.Information

