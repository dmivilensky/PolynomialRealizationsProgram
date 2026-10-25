import polyak.General.IQC.HalfLineCertificate
import polyak.General.IQC.Certificate
import polyak.General.IQC.PlantGradient

/-! The strict certificate controls plant output energy.  The genuine
bounded inverse recurrence filter converts it into the input gap required
by the causal homotopy theorem, with a dimension-independent constant. -/

namespace polyak.General.IQC
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def gradientGain (A B beta t : ℝ) : ℝ :=
  |Real.exp t/B|+|A/B|+|beta*Real.exp (-t)/B|

theorem gradientGain_nonneg (A B beta t : ℝ) : 0 ≤ gradientGain A B beta t := by
  unfold gradientGain
  positivity

theorem gradientGain_eq (A B beta t : ℝ) :
    gradientGain A B beta t=(Real.exp t+|A|+|beta| *Real.exp (-t))/|B| := by
  simp only [gradientGain,abs_div,abs_mul,abs_of_pos (Real.exp_pos _)]
  ring

def gradientCLM (A B beta t : ℝ) : ZSpace E →L[ℝ] ZSpace E :=
  (Real.exp t/B) • zShiftCLM 1 - (A/B) • ContinuousLinearMap.id ℝ _ +
    (beta*Real.exp (-t)/B) • zShiftCLM (-1)

@[simp] theorem gradientCLM_apply (A B beta t : ℝ) (x : ZSpace E) (k : ℤ) :
    gradientCLM A B beta t x k=Energy.filterEval (Energy.gradientFilter A B beta t) x k := by
  rw [Energy.filterEval_gradient]
  rfl

theorem gradientCLM_bound (A B beta t : ℝ) (x : ZSpace E) :
    ‖gradientCLM A B beta t x‖ ≤ gradientGain A B beta t*‖x‖ := by
  change ‖(Real.exp t/B) • zShift 1 x-(A/B) • x+
    (beta*Real.exp (-t)/B) • zShift (-1) x‖ ≤ _
  calc
    _ ≤ ‖(Real.exp t/B) • zShift 1 x-(A/B) • x‖+
      ‖(beta*Real.exp (-t)/B) • zShift (-1) x‖ := norm_add_le _ _
    _ ≤ (‖(Real.exp t/B) • zShift 1 x‖+‖(A/B) • x‖)+
      ‖(beta*Real.exp (-t)/B) • zShift (-1) x‖ :=
        add_le_add (norm_sub_le _ _) le_rfl
    _ = _ := by rw [norm_smul,norm_smul,norm_smul,zShift_norm,zShift_norm]; simp only [Real.norm_eq_abs,gradientGain]; ring

theorem gradient_norm_bound (A B beta t : ℝ) (x sigma : ZSpace E)
    (hs : ∀ k,sigma k=Energy.filterEval (Energy.gradientFilter A B beta t) x k) :
    ‖sigma‖ ≤ gradientGain A B beta t*‖x‖ := by
  have he : sigma=gradientCLM A B beta t x := by
    apply Subtype.ext
    funext k
    rw [gradientCLM_apply]
    exact hs k
  rw [he]
  exact gradientCLM_bound _ _ _ _ _

theorem input_gap {a b M epsilon : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hM : 0 ≤ M) (he : 0 < epsilon) (hab : a ≤ M*b) :
    epsilon/(1+M^2)*a^2 ≤ epsilon*b^2 := by
  have hs : a^2 ≤ (1+M^2)*b^2 := by
    have hs' := (sq_le_sq₀ ha (mul_nonneg hM hb)).mpr hab
    nlinarith [sq_nonneg b]
  have hden : 0 < 1+M^2 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ hden).2
  have hmul := mul_le_mul_of_nonneg_left hs he.le
  nlinarith only [hmul]

theorem halfLineCertificate_strict_graph (A B beta t : ℝ) (hB : B ≠ 0)
    (cert : Duality.StrictCertificate (Waves.multiplierMap A B beta t) t)
    (output input : SequenceSpace E)
    (hs : ∀ k,zeroExtend (fun n => input n) k=
      Energy.filterEval (Energy.gradientFilter A B beta t)
        (zeroExtend (fun n => output n)) k) :
    iqcValue (halfLineCertificate cert) output input ≤
      -(cert.ε/(1+(gradientGain A B beta t)^2))*‖input‖^2 := by
  have hgap := certificateForm_strict_graph A B beta t hB cert
    (zeroExtendL2 output) (zeroExtendL2 input) hs
  have hnorm := gradient_norm_bound A B beta t (zeroExtendL2 output) (zeroExtendL2 input) hs
  rw [zeroExtendL2_norm,zeroExtendL2_norm] at hnorm
  rw [zeroExtendL2_norm] at hgap
  have hcoerce := input_gap (norm_nonneg input) (norm_nonneg output)
    (gradientGain_nonneg A B beta t) cert.ε_pos hnorm
  exact hgap.trans (by nlinarith only [hcoerce])

end
end polyak.General.IQC
