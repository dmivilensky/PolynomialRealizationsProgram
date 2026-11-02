import bezout.Channel.SignalBounds

/-!
Article: bezout, Proposition D.1, root-order invariance of the actual channel matrix.
Use: changing physical root order permutes temporal columns and preserves both
actual operator gain and Hilbert--Schmidt signal energy.
Proof: the corresponding temporal coordinate permutation is an exact Euclidean
isometry; finite sums are reindexed by the same bijection.
-/

namespace bezout.Channel
noncomputable section
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J]

/-- Relabel the temporal columns of a physical signal matrix. -/
def columnPermutation (M : Matrix J (Fin N) ℝ) (p : Equiv.Perm (Fin N)) : Matrix J (Fin N) ℝ :=
  fun j s => M j (p s)

/-- The matching norm-preserving relabeling of temporal input profiles. -/
def temporalPermutation (p : Equiv.Perm (Fin N)) :
    EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ p

/-- Coordinates of the temporal permutation. -/
@[simp] theorem temporalPermutation_apply (p : Equiv.Perm (Fin N))
    (e : EuclideanSpace ℝ (Fin N)) (s : Fin N) :
    temporalPermutation p e s=e (p.symm s) := by
  simp [temporalPermutation, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- Column permutation is a genuine isometric change of temporal input. -/
theorem columnPermutation_action (M : Matrix J (Fin N) ℝ) (p : Equiv.Perm (Fin N))
    (e : EuclideanSpace ℝ (Fin N)) :
    rectangularOperator (columnPermutation M p) e=rectangularOperator M (temporalPermutation p e) := by
  ext j
  simp only [rectangularOperator_apply, columnPermutation, temporalPermutation_apply]
  simpa only [Equiv.symm_apply_apply] using Equiv.sum_comp p (fun s => M j s*e (p.symm s))

/-- Temporal column permutation cannot enlarge the actual operator gain. -/
theorem rectangularNorm_colperm_le (M : Matrix J (Fin N) ℝ) (p : Equiv.Perm (Fin N)) :
    rectangularNorm (columnPermutation M p)≤rectangularNorm M := by
  apply (rectangularOperator (columnPermutation M p)).opNorm_le_bound (norm_nonneg (rectangularOperator M))
  intro e
  rw [columnPermutation_action]
  simpa only [LinearIsometryEquiv.norm_map] using (rectangularOperator M).le_opNorm (temporalPermutation p e)

/-- The actual operator gain is invariant under root-order column permutations. -/
theorem rectangularNorm_colperm (M : Matrix J (Fin N) ℝ) (p : Equiv.Perm (Fin N)) :
    rectangularNorm (columnPermutation M p)=rectangularNorm M := by
  apply le_antisymm (rectangularNorm_colperm_le M p)
  have hr := rectangularNorm_colperm_le (columnPermutation M p) p.symm
  have he : columnPermutation (columnPermutation M p) p.symm=M := by
    funext j s
    simp [columnPermutation]
  rw [he] at hr
  exact hr

/-- The actual squared Hilbert--Schmidt energy is invariant under column permutations. -/
theorem rectangularHsSq_colperm (M : Matrix J (Fin N) ℝ) (p : Equiv.Perm (Fin N)) :
    rectangularHsSq (columnPermutation M p)=rectangularHsSq M := by
  apply Finset.sum_congr rfl
  intro j _
  exact Equiv.sum_comp p (fun s => M j s^2)

end
end bezout.Channel
