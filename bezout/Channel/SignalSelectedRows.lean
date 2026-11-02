import bezout.Channel.SignalTwoRows

/-!
Article: bezout, Appendix D, the two endpoint modes inside a general finite signal.
Use: exact two-row Gram coefficients remain valid in an arbitrary eigenbasis;
all additional modes change squared gain by at most their total HS row energy.
Proof: orthogonal coordinate masking and the exact two-row norm formula.
-/

namespace bezout.Channel
noncomputable section
open scoped BigOperators
variable {N : ℕ} {J : Type*} [Fintype J] [DecidableEq J]

/-- The actual squared action of a two-coordinate row mask. -/
theorem rowMask_two_action_sq (M : Matrix J (Fin N) ℝ) (j0 j1 : J) (hne : j0≠j1)
    (e : EuclideanSpace ℝ (Fin N)) :
    ‖rectangularOperator (rowMask {j0,j1} M) e‖^2=
      ‖rectangularOperator (twoRowMatrix (M j0) (M j1)) e‖^2 := by
  have hp (j : J) : (rectangularOperator (rowMask {j0,j1} M) e j)^2=
      (if j=j0 then (rectangularOperator M e j0)^2 else 0)+
      (if j=j1 then (rectangularOperator M e j1)^2 else 0) := by
    rw [rowMask_action]
    by_cases h0 : j=j0
    · subst j; simp [hne]
    · by_cases h1 : j=j1
      · subst j; simp [Ne.symm hne]
      · simp [h0,h1]
  rw [EuclideanSpace.norm_sq_eq, twoRow_action_sq]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Finset.sum_congr rfl (fun j _ => hp j), Finset.sum_add_distrib]
  simp [temporalDot]

/-- Selecting two endpoint coordinates has the same true norm as its two-row matrix. -/
theorem rowMask_two_norm (M : Matrix J (Fin N) ℝ) (j0 j1 : J) (hne : j0≠j1) :
    rectangularNorm (rowMask {j0,j1} M)=rectangularNorm (twoRowMatrix (M j0) (M j1)) := by
  have he (e : EuclideanSpace ℝ (Fin N)) :
      ‖rectangularOperator (rowMask {j0,j1} M) e‖=
        ‖rectangularOperator (twoRowMatrix (M j0) (M j1)) e‖ :=
    (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (rowMask_two_action_sq M j0 j1 hne e)
  change ‖rectangularOperator (rowMask {j0,j1} M)‖=‖rectangularOperator (twoRowMatrix (M j0) (M j1))‖
  apply le_antisymm
  · apply (rectangularOperator (rowMask {j0,j1} M)).opNorm_le_bound
      (norm_nonneg (rectangularOperator (twoRowMatrix (M j0) (M j1))))
    intro e
    rw [he]
    exact (rectangularOperator (twoRowMatrix (M j0) (M j1))).le_opNorm e
  · apply (rectangularOperator (twoRowMatrix (M j0) (M j1))).opNorm_le_bound
      (norm_nonneg (rectangularOperator (rowMask {j0,j1} M)))
    intro e
    rw [← he]
    exact (rectangularOperator (rowMask {j0,j1} M)).le_opNorm e

/-- Exact HS energy of the two selected spectral rows. -/
theorem rowMask_two_hsSq (M : Matrix J (Fin N) ℝ) (j0 j1 : J) (hne : j0≠j1) :
    rectangularHsSq (rowMask {j0,j1} M)=temporalDot (M j0) (M j0)+temporalDot (M j1) (M j1) := by
  have hp (j : J) : (∑ s, rowMask {j0,j1} M j s^2)=
      (if j=j0 then temporalDot (M j0) (M j0) else 0)+
      (if j=j1 then temporalDot (M j1) (M j1) else 0) := by
    by_cases h0 : j=j0
    · subst j; simp [rowMask, hne, temporalDot_self]
    · by_cases h1 : j=j1
      · subst j; simp [rowMask, Ne.symm hne, temporalDot_self]
      · simp [rowMask, h0,h1]
  unfold rectangularHsSq
  rw [Finset.sum_congr rfl (fun j _ => hp j), Finset.sum_add_distrib]
  simp

/-- Exact endpoint Gram gain plus a finite-bulk energy sandwich in any ambient dimension. -/
theorem selectedRows_equalEnergy_sandwich (M : Matrix J (Fin N) ℝ)
    (j0 j1 : J) (hne : j0≠j1) (R : ℝ)
    (h0 : temporalDot (M j0) (M j0)=R) (h1 : temporalDot (M j1) (M j1)=R) :
    (R+|temporalDot (M j0) (M j1)|≤rectangularNorm M^2 ∧
      rectangularNorm M^2≤R+|temporalDot (M j0) (M j1)|+
        rectangularHsSq (rowMask ({j0,j1}ᶜ) M)) ∧
    rectangularHsSq M=2*R+rectangularHsSq (rowMask ({j0,j1}ᶜ) M) := by
  have hb := rowMask_norm_sq_sandwich ({j0,j1}:Finset J) M
  rw [rowMask_two_norm M j0 j1 hne, twoRow_norm_sq (M j0) (M j1) R h0 h1] at hb
  refine ⟨hb, ?_⟩
  rw [rowMask_hsSq_split ({j0,j1}:Finset J) M, rowMask_two_hsSq M j0 j1 hne, h0,h1]
  ring

end
end bezout.Channel
