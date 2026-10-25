import chebyshev2.Primal.Filters

/-!
Article: chebyshev2, Theorem 5.1.
Symmetry.
Use: `chebyshev2.Primal.density_reflection` feeds
`chebyshev2.Primal.actualRightFilter_mirror_cubic` (actual Right Filter mirror cubic).
Proof chain: `chebyshev2.Primal.determinant_cubic` — chebyshev2, Theorem 5.1; General
measurable speed gives a density with the prescribed ground parameter.
-/
namespace chebyshev2.Primal
noncomputable section
open Set MeasureTheory Real chebyshev2.PrescribedSpeed
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/--
Exact identity `(speedData φ hφ).reciprocal (2-q)=(speedData φ hφ).reciprocal q`.

Use: `chebyshev2.Primal.X_reflection` uses this identity to establish the identity
`(speedData φ hφ).X (2-q)=-(speedData φ hφ).X q`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Separate `q∈Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
exclusive hypotheses.
-/
theorem reciprocal_reflection {φ : ℝ → ℝ} (hφ : Continuous φ) (q : ℝ) :
    (speedData φ hφ).reciprocal (2-q)=(speedData φ hφ).reciprocal q := by
  -- Separate `q∈Ioo (0:ℝ) 2` from its negation; prove the goal under each of these mutually
  -- exclusive hypotheses.
  by_cases hq : q∈Ioo (0:ℝ) 2
  · have hr : 2-q∈Ioo (0:ℝ) 2 := ⟨by linarith [hq.2],by linarith [hq.1]⟩
    simp only [SpeedData.reciprocal,indicator_of_mem hq,indicator_of_mem hr]
    change (speed φ (2-q))⁻¹=(speed φ q)⁻¹
    rw [speed,speed,coordinate_reflection]
  · have hr : 2-q∉Ioo (0:ℝ) 2 := fun hr => hq ⟨by linarith [hr.2],by linarith [hr.1]⟩
    simp only [SpeedData.reciprocal,indicator_of_notMem hq,indicator_of_notMem hr]

/--
Exact identity `(speedData φ hφ).X (2-q)=-(speedData φ hφ).X q`.

Use: `chebyshev2.Primal.inverse_reflection` rewrites with this identity to establish exact
identity `(speedData φ hφ).q (-x)=2-(speedData φ hφ).q x`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Primal.reciprocal_reflection` with the
arguments shown in the proof.
-/
theorem X_reflection {φ : ℝ → ℝ} (hφ : Continuous φ) (q : ℝ) :
    (speedData φ hφ).X (2-q)=-(speedData φ hφ).X q := by
  -- Use the identities/estimates `chebyshev2.Primal.reciprocal_reflection` with the
  -- arguments shown in the proof.
  let S := speedData φ hφ
  have h := intervalIntegral.integral_comp_sub_left (a:=1) (b:=q) S.reciprocal 2
  have he : (∫ t in (1:ℝ)..q,S.reciprocal (2-t))=∫ t in (1:ℝ)..q,S.reciprocal t :=
    intervalIntegral.integral_congr (fun t _ => reciprocal_reflection hφ t)
  rw [he] at h
  norm_num only at h
  rw [intervalIntegral.integral_symm (a:=1) (b:=2-q)] at h
  change S.X (2-q)=-S.X q
  dsimp only [SpeedData.X]
  linarith

/--
Exact identity `(speedData φ hφ).q (-x)=2-(speedData φ hφ).q x`.

Use: `chebyshev2.Primal.density_reflection` rewrites with this identity to establish exact
identity `(speedData φ hφ).density κ (-x)=(speedData φ hφ).density κ x`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Primal.X_reflection`,
`chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
`chebyshev2.PrescribedSpeed.SpeedData.q_two_right` with the arguments shown in the proof.
-/
theorem inverse_reflection {φ : ℝ → ℝ} (hφ : Continuous φ) (x : ℝ) :
    (speedData φ hφ).q (-x)=2-(speedData φ hφ).q x := by
  -- Use the identities/estimates `chebyshev2.Primal.X_reflection`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_zero_left`,
  -- `chebyshev2.PrescribedSpeed.SpeedData.q_two_right` with the arguments shown in the
  -- proof.
  let S := speedData φ hφ
  have he : S.X 2=-S.X 0 := by simpa only [sub_zero] using X_reflection hφ 0
  rcases le_or_gt x (S.X 0) with hl|hl
  · rw [S.q_zero_left hl,S.q_two_right (by linarith)]
    norm_num
  · rcases le_or_gt (S.X 2) x with hr|hr
    · rw [S.q_two_right hr,S.q_zero_left (by linarith)]
      norm_num
    · have hx : x∈Icc (S.X 0) (S.X 2) := ⟨hl.le,hr.le⟩
      have hq : 2-S.q x∈Icc (0:ℝ) 2 := by
        constructor <;> linarith [(S.q_mem x).1,(S.q_mem x).2]
      have hi := S.q_X hq
      have hX : S.X (2-S.q x)=-x := by rw [X_reflection hφ,S.X_q hx]
      rw [hX] at hi
      exact hi

/--
Exact identity `(speedData φ hφ).density κ (-x)=(speedData φ hφ).density κ x`.

Use: `chebyshev2.Primal.actualRightFilter_cubic` uses this identity to establish exact
identity `actualRightFilter hψ κ s (t^3)=reflectedNonlinearFilter hψ κ s t`.

Article: chebyshev2, Theorem 5.1 via `chebyshev2.Primal.determinant_cubic`.

Proof: Use the identities/estimates `chebyshev2.Primal.density_formula`,
`chebyshev2.Primal.inverse_reflection`, `chebyshev2.Primal.coordinate_reflection` with
the arguments shown in the proof.
-/
theorem density_reflection {φ : ℝ → ℝ} (hφ : Continuous φ) (κ x : ℝ) :
    (speedData φ hφ).density κ (-x)=(speedData φ hφ).density κ x := by
  -- Use the identities/estimates `chebyshev2.Primal.density_formula`,
  -- `chebyshev2.Primal.inverse_reflection`, `chebyshev2.Primal.coordinate_reflection`
  -- with the arguments shown in the proof.
  rw [density_formula hφ,density_formula hφ,inverse_reflection hφ]
  have hD : speed φ (2-(speedData φ hφ).q x)=speed φ ((speedData φ hφ).q x) := by
    rw [speed,speed,coordinate_reflection]
  rw [hD]
  dsimp only [SpeedData.Q]
  rw [inverse_reflection hφ]
  congr 1
  ring

end
end chebyshev2.Primal
