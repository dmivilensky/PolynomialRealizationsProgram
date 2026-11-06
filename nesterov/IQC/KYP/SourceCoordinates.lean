import nesterov.IQC.KYP.Window
import nesterov.Stationary.Normalized

/-!
Article: Proposition `lyap`, the source state X_k.
Use: the latent finite window and the two-position/gradient state are
linearly equivalent whenever the leading normalized coefficient is nonzero.
The inverse is the actual causal second-order triangular recursion, on any
real normed space; no finite-dimensional assumption on that space is used.
-/

namespace nesterov.IQC.KYP
noncomputable section

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def sourceCoordinates (M : ℕ) (p₀ p₁ p₂ : ℝ) (w : Fin (M + 2) → E) (i : Fin (M + 2)) : E :=
  if h₀ : i.val = 0 then w ⟨0, by omega⟩ else
  if h₁ : i.val = 1 then w ⟨1, by omega⟩ else
    p₀ • w ⟨i.val - 2, by omega⟩ + p₁ • w ⟨i.val - 1, by omega⟩ + p₂ • w i

@[simp] theorem sourceCoordinates_zero (M : ℕ) (p₀ p₁ p₂ : ℝ) (w : Fin (M + 2) → E) :
    sourceCoordinates M p₀ p₁ p₂ w ⟨0, by omega⟩ = w ⟨0, by omega⟩ := by
  simp [sourceCoordinates]

@[simp] theorem sourceCoordinates_one (M : ℕ) (p₀ p₁ p₂ : ℝ) (w : Fin (M + 2) → E) :
    sourceCoordinates M p₀ p₁ p₂ w ⟨1, by omega⟩ = w ⟨1, by omega⟩ := by
  simp [sourceCoordinates]

theorem sourceCoordinates_succsucc (M : ℕ) (p₀ p₁ p₂ : ℝ) (w : Fin (M + 2) → E)
    (n : ℕ) (hn : n + 2 < M + 2) :
    sourceCoordinates M p₀ p₁ p₂ w ⟨n + 2, hn⟩ =
      p₀ • w ⟨n, by omega⟩ + p₁ • w ⟨n + 1, by omega⟩ + p₂ • w ⟨n + 2, hn⟩ := by
  simp [sourceCoordinates]

def extendedCoordinate (M : ℕ) (X : Fin (M + 2) → E) (n : ℕ) : E :=
  if hn : n < M + 2 then X ⟨n, hn⟩ else 0

omit [NormedSpace ℝ E] in
@[simp] theorem extendedCoordinate_of_lt (M : ℕ) (X : Fin (M + 2) → E) (n : ℕ)
    (hn : n < M + 2) : extendedCoordinate M X n = X ⟨n, hn⟩ := by
  simp [extendedCoordinate, hn]

def recoverCoordinates (M : ℕ) (p₀ p₁ p₂ : ℝ) (X : Fin (M + 2) → E) : ℕ → E
  | 0 => X ⟨0, by omega⟩
  | 1 => X ⟨1, by omega⟩
  | n + 2 => p₂⁻¹ • (extendedCoordinate M X (n + 2) -
      p₀ • recoverCoordinates M p₀ p₁ p₂ X n - p₁ • recoverCoordinates M p₀ p₁ p₂ X (n + 1))

theorem recover_sourceCoordinates (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0)
    (w : Fin (M + 2) → E) (n : ℕ) (hn : n < M + 2) :
    recoverCoordinates M p₀ p₁ p₂ (sourceCoordinates M p₀ p₁ p₂ w) n = w ⟨n, hn⟩ := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simp [recoverCoordinates, sourceCoordinates]
    · rcases n with _ | n
      · simp [recoverCoordinates, sourceCoordinates]
      · rw [recoverCoordinates, extendedCoordinate_of_lt M _ (n + 2) hn,
          sourceCoordinates_succsucc, ih n (by omega) (by omega), ih (n + 1) (by omega) (by omega)]
        have he : (p₀ • w ⟨n, by omega⟩ + p₁ • w ⟨n + 1, by omega⟩ + p₂ • w ⟨n + 2, hn⟩) -
            p₀ • w ⟨n, by omega⟩ - p₁ • w ⟨n + 1, by omega⟩ = p₂ • w ⟨n + 2, hn⟩ := by abel
        rw [he, smul_smul, inv_mul_cancel₀ hp₂, one_smul]

theorem source_recoverCoordinates (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0)
    (X : Fin (M + 2) → E) :
    sourceCoordinates M p₀ p₁ p₂ (fun i => recoverCoordinates M p₀ p₁ p₂ X i) = X := by
  funext i
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · simp [sourceCoordinates, recoverCoordinates]
  · rcases i with _ | i
    · simp [sourceCoordinates, recoverCoordinates]
    · rw [sourceCoordinates_succsucc, recoverCoordinates, extendedCoordinate_of_lt M X (i + 2) hi,
        smul_smul, mul_inv_cancel₀ hp₂, one_smul]
      abel

def sourceCoordinatesLM (M : ℕ) (p₀ p₁ p₂ : ℝ) :
    (Fin (M + 2) → E) →ₗ[ℝ] (Fin (M + 2) → E) where
  toFun := sourceCoordinates M p₀ p₁ p₂
  map_add' u v := by
    funext i
    dsimp [sourceCoordinates]
    split_ifs <;> module
  map_smul' a u := by
    funext i
    dsimp [sourceCoordinates]
    split_ifs <;> module

theorem sourceCoordinates_continuous (M : ℕ) (p₀ p₁ p₂ : ℝ) :
    Continuous (sourceCoordinates M p₀ p₁ p₂ : (Fin (M + 2) → E) → (Fin (M + 2) → E)) := by
  apply continuous_pi
  intro i
  dsimp [sourceCoordinates]
  split_ifs <;> fun_prop

theorem recoverCoordinates_continuous (M : ℕ) (p₀ p₁ p₂ : ℝ) (n : ℕ) :
    Continuous (fun X : Fin (M + 2) → E => recoverCoordinates M p₀ p₁ p₂ X n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · exact continuous_apply _
    · rcases n with _ | n
      · exact continuous_apply _
      · simp only [recoverCoordinates]
        have he : Continuous (fun X : Fin (M + 2) → E => extendedCoordinate M X (n + 2)) := by
          dsimp [extendedCoordinate]
          split_ifs <;> fun_prop
        exact ((he.sub ((ih n (by omega)).const_smul p₀)).sub
          ((ih (n + 1) (by omega)).const_smul p₁)).const_smul _

/-- The source state and latent window are continuously linearly equivalent
for every real normed state space, with an explicit triangular inverse. -/
def sourceCoordinatesEquiv (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0) :
    (Fin (M + 2) → E) ≃L[ℝ] (Fin (M + 2) → E) :=
  { sourceCoordinatesLM M p₀ p₁ p₂ with
    invFun := fun X i => recoverCoordinates M p₀ p₁ p₂ X i
    left_inv := fun w => by
      funext i
      exact recover_sourceCoordinates M p₀ p₁ p₂ hp₂ w i i.isLt
    right_inv := source_recoverCoordinates M p₀ p₁ p₂ hp₂
    continuous_toFun := sourceCoordinates_continuous M p₀ p₁ p₂
    continuous_invFun := continuous_pi fun i => recoverCoordinates_continuous M p₀ p₁ p₂ i }

@[simp] theorem sourceCoordinatesEquiv_apply (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0)
    (w : Fin (M + 2) → E) : sourceCoordinatesEquiv M p₀ p₁ p₂ hp₂ w = sourceCoordinates M p₀ p₁ p₂ w := rfl

/-- Both norm comparisons required when transporting a bounded quadratic
storage between the two finite state descriptions. -/
theorem sourceCoordinates_norm_comparison (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧ ∀ w : Fin (M + 2) → E,
      ‖sourceCoordinates M p₀ p₁ p₂ w‖ ≤ C * ‖w‖ ∧
        ‖w‖ ≤ D * ‖sourceCoordinates M p₀ p₁ p₂ w‖ := by
  let T := sourceCoordinatesEquiv (E := E) M p₀ p₁ p₂ hp₂
  refine ⟨‖T.toContinuousLinearMap‖ + 1, ‖T.symm.toContinuousLinearMap‖ + 1,
    by positivity, by positivity, fun w => ?_⟩
  have h1 := T.toContinuousLinearMap.le_opNorm w
  have h2 := T.symm.toContinuousLinearMap.le_opNorm (T w)
  simp only [ContinuousLinearEquiv.coe_coe, T.symm_apply_apply] at h2
  change ‖T w‖ ≤ (‖T.toContinuousLinearMap‖ + 1) * ‖w‖ ∧
    ‖w‖ ≤ (‖T.symm.toContinuousLinearMap‖ + 1) * ‖T w‖
  constructor
  · exact h1.trans (by nlinarith [norm_nonneg w])
  · exact h2.trans (by nlinarith [norm_nonneg (T w)])

/-- On an actual latent sequence, the triangular map is exactly the source
state consisting of the first two positions and the M prescribed gradients. -/
theorem sourceCoordinates_window (M : ℕ) (p₀ p₁ p₂ : ℝ) (w σ : ℕ → E)
    (hσ : ∀ k, p₀ • w k + p₁ • w (k + 1) + p₂ • w (k + 2) = σ k) (k : ℕ) :
    sourceCoordinates M p₀ p₁ p₂ (window (M + 2) w k) =
      fun i : Fin (M + 2) => if i.val = 0 then w k else
        if i.val = 1 then w (k + 1) else σ (k + (i.val - 2)) := by
  funext i
  rcases i with ⟨i, hi⟩
  rcases i with _ | i
  · simp [sourceCoordinates, window]
  · rcases i with _ | i
    · simp [sourceCoordinates, window]
    · rw [sourceCoordinates_succsucc]
      simpa [window, Nat.add_assoc] using hσ (k + i)

theorem extendedCoordinate_reconstruction (M n : ℕ) (X : Fin (M + 2) → E) :
    extendedCoordinate M X n = ∑ j : Fin (M + 2),
      extendedCoordinate M (Pi.single j (1 : ℝ)) n • X j := by
  classical
  by_cases hn : n < M + 2
  · simp [extendedCoordinate, hn, Pi.single_apply]
  · simp [extendedCoordinate, hn]

/-- The inverse coefficients are fixed real numbers, independent of the
spatial Hilbert space; they are the inverse's values on the scalar basis. -/
theorem recoverCoordinates_eq_coefficients (M : ℕ) (p₀ p₁ p₂ : ℝ)
    (X : Fin (M + 2) → E) (n : ℕ) :
    recoverCoordinates M p₀ p₁ p₂ X n = ∑ j : Fin (M + 2),
      recoverCoordinates M p₀ p₁ p₂ (Pi.single j (1 : ℝ)) n • X j := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases n with _ | n
    · simp [recoverCoordinates, Pi.single_apply]
    · rcases n with _ | n
      · simp [recoverCoordinates, Pi.single_apply]
      · rw [recoverCoordinates, ih n (by omega), ih (n + 1) (by omega)]
        simp only [recoverCoordinates, smul_eq_mul, sub_smul, mul_smul,
          Finset.sum_sub_distrib, ← Finset.smul_sum]
        rw [← extendedCoordinate_reconstruction]

end General
section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Applying a finite real matrix to Hilbert vectors. -/
def scalarAction {I J : Type*} [Fintype I] [DecidableEq I] (A : (I → ℝ) →L[ℝ] (J → ℝ))
    (x : I → E) (j : J) : E := ∑ i, A (Pi.single i 1) j • x i

theorem sourceCoordinatesEquiv_symm_scalarAction (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0)
    (X : Fin (M + 2) → E) :
    (sourceCoordinatesEquiv (E := E) M p₀ p₁ p₂ hp₂).symm X =
      scalarAction (sourceCoordinatesEquiv (E := ℝ) M p₀ p₁ p₂ hp₂).symm.toContinuousLinearMap X := by
  funext i
  exact recoverCoordinates_eq_coefficients M p₀ p₁ p₂ X i

theorem tensorForm_scalarAction {I J : Type*} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (B : Bilinear (J → ℝ))
    (A : (I → ℝ) →L[ℝ] (J → ℝ)) (x : I → E) :
    tensorForm (B.bilinearComp A A) x x = tensorForm B (scalarAction A x) (scalarAction A x) := by
  unfold tensorForm matrixInner
  conv_lhs =>
    unfold bilinearMatrix
    simp only [ContinuousLinearMap.bilinearComp_apply]
    arg 2
    ext i
    arg 2
    ext j
    arg 1
    rw [bilinearMatrix_apply]
  simp only [Finset.sum_mul]
  rw [sum_four_comm]
  simp only [scalarAction, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The finite storage becomes a fixed scalar quadratic form in the exact
source state X, with the same coefficients on every Hilbert space. -/
theorem tensorForm_sourceCoordinates (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0)
    (W : Bilinear (Fin (M + 2) → ℝ)) (w : Fin (M + 2) → E) :
    tensorForm W w w =
      tensorForm (W.bilinearComp
        (sourceCoordinatesEquiv (E := ℝ) M p₀ p₁ p₂ hp₂).symm.toContinuousLinearMap
        (sourceCoordinatesEquiv (E := ℝ) M p₀ p₁ p₂ hp₂).symm.toContinuousLinearMap)
        (sourceCoordinates M p₀ p₁ p₂ w) (sourceCoordinates M p₀ p₁ p₂ w) := by
  rw [tensorForm_scalarAction, ← sourceCoordinatesEquiv_symm_scalarAction]
  rw [← sourceCoordinatesEquiv_apply M p₀ p₁ p₂ hp₂ w]
  simp only [ContinuousLinearEquiv.symm_apply_apply]

def scalarActionBound {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : (I → ℝ) →L[ℝ] (J → ℝ)) : ℝ :=
  1 + ∑ j, ∑ i, |A (Pi.single i 1) j|

theorem scalarActionBound_pos {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : (I → ℝ) →L[ℝ] (J → ℝ)) : 0 < scalarActionBound A := by
  dsimp [scalarActionBound]
  positivity

/-- The scalar matrix gives a norm constant independent of the ambient
Hilbert space, including in infinite dimension. -/
theorem scalarAction_norm_le {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : (I → ℝ) →L[ℝ] (J → ℝ)) (x : I → E) :
    ‖scalarAction A x‖ ≤ scalarActionBound A * ‖x‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (scalarActionBound_pos A).le (norm_nonneg x))).mpr
  intro j
  have hrow : (∑ i, |A (Pi.single i 1) j|) ≤ scalarActionBound A := by
    have hh : (∑ i, |A (Pi.single i 1) j|) ≤ ∑ r, ∑ i, |A (Pi.single i 1) r| :=
      Finset.single_le_sum (s := Finset.univ)
      (fun j _ => Finset.sum_nonneg (fun i _ => abs_nonneg (A (Pi.single i 1) j)))
      (Finset.mem_univ j)
    dsimp [scalarActionBound]
    linarith
  calc
    _ ≤ ∑ i, ‖A (Pi.single i 1) j • x i‖ := norm_sum_le _ _
    _ = ∑ i, |A (Pi.single i 1) j| * ‖x i‖ := by simp only [norm_smul, Real.norm_eq_abs]
    _ ≤ ∑ i, |A (Pi.single i 1) j| * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x i) (abs_nonneg _)
    _ = (∑ i, |A (Pi.single i 1) j|) * ‖x‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hrow (norm_nonneg x)

def sourceInverseBound (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0) : ℝ :=
  scalarActionBound (sourceCoordinatesEquiv (E := ℝ) M p₀ p₁ p₂ hp₂).symm.toContinuousLinearMap

theorem sourceCoordinates_inverse_uniform_bound (M : ℕ) (p₀ p₁ p₂ : ℝ) (hp₂ : p₂ ≠ 0)
    (w : Fin (M + 2) → E) :
    ‖w‖ ≤ sourceInverseBound M p₀ p₁ p₂ hp₂ * ‖sourceCoordinates M p₀ p₁ p₂ w‖ := by
  have hh := scalarAction_norm_le
    (sourceCoordinatesEquiv (E := ℝ) M p₀ p₁ p₂ hp₂).symm.toContinuousLinearMap
    (sourceCoordinates M p₀ p₁ p₂ w)
  rw [← sourceCoordinatesEquiv_symm_scalarAction,
    ← sourceCoordinatesEquiv_apply M p₀ p₁ p₂ hp₂ w,
    ContinuousLinearEquiv.symm_apply_apply] at hh
  exact hh

theorem sourceCoordinates_forward_uniform_bound (M : ℕ) (p₀ p₁ p₂ : ℝ)
    (w : Fin (M + 2) → E) :
    ‖sourceCoordinates M p₀ p₁ p₂ w‖ ≤ (1 + |p₀| + |p₁| + |p₂|) * ‖w‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  have hnorm (j : Fin (M + 2)) := norm_le_pi_norm w j
  have hcoef : (1 : ℝ) ≤ 1 + |p₀| + |p₁| + |p₂| := by
    linarith [abs_nonneg p₀, abs_nonneg p₁, abs_nonneg p₂]
  have hmul : ‖w‖ ≤ (1 + |p₀| + |p₁| + |p₂|) * ‖w‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hcoef (norm_nonneg w)
  dsimp [sourceCoordinates]
  split_ifs
  · exact (hnorm ⟨0, by omega⟩).trans hmul
  · exact (hnorm ⟨1, by omega⟩).trans hmul
  · apply (norm_add_le _ _).trans
    have hfirst := norm_add_le (p₀ • w ⟨i.val - 2, by omega⟩) (p₁ • w ⟨i.val - 1, by omega⟩)
    simp only [norm_smul, Real.norm_eq_abs] at hfirst ⊢
    have h0 := mul_le_mul_of_nonneg_left (hnorm ⟨i.val - 2, by omega⟩) (abs_nonneg p₀)
    have h1 := mul_le_mul_of_nonneg_left (hnorm ⟨i.val - 1, by omega⟩) (abs_nonneg p₁)
    have h2 := mul_le_mul_of_nonneg_left (hnorm i) (abs_nonneg p₂)
    nlinarith [norm_nonneg w]

end Hilbert

end
end nesterov.IQC.KYP
