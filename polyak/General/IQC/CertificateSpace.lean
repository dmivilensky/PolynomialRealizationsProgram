import polyak.General.IQC.CertificateTime
import polyak.General.IQC.Apriori

/-! Article: lem:iqc. Integer shifts are genuine isometries of ℓ²;
finite quadratic filters therefore define bounded two-channel forms. -/
noncomputable section
namespace polyak.General.IQC
open polyak Energy
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]
abbrev ZSpace (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℤ => E) 2

theorem zlp_squareSummable (x : ZSpace E) : ZSquareSummable (fun k => x k) := by
  have h := (lp.memℓp x).summable (by norm_num : 0<(2:ℝ≥0∞).toReal)
  simpa only [ZSquareSummable,ENNReal.toReal_ofNat,Real.rpow_two] using h

def toZL2 (x : ℤ → E) (hx : ZSquareSummable x) : ZSpace E :=
  ⟨x,(memℓp_gen_iff (by norm_num : 0<(2:ℝ≥0∞).toReal)).mpr (by
    simpa only [ZSquareSummable,ENNReal.toReal_ofNat,Real.rpow_two] using hx)⟩
@[simp] theorem toZL2_apply (x : ℤ → E) (hx : ZSquareSummable x) (k : ℤ) : toZL2 x hx k=x k := rfl

theorem zlp_norm_sq (x : ZSpace E) : ‖x‖^2=∑' k,‖x k‖^2 := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
    lp.norm_rpow_eq_tsum (by norm_num : 0<(2:ℝ≥0∞).toReal) x

def zShift (n : ℤ) (x : ZSpace E) : ZSpace E := toZL2
  (fun k => x (k+n)) ((zlp_squareSummable x).shift n)
@[simp] theorem zShift_apply (n : ℤ) (x : ZSpace E) (k : ℤ) : zShift n x k=x (k+n) := rfl
theorem zShift_norm (n : ℤ) (x : ZSpace E) : ‖zShift n x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [zlp_norm_sq,zlp_norm_sq]
  exact (Equiv.addRight n).tsum_eq (fun k => ‖x k‖^2)

variable [NormedSpace ℝ E]
def zShiftLinear (n : ℤ) : ZSpace E →ₗ[ℝ] ZSpace E where
  toFun := zShift n
  map_add' x y := by apply Subtype.ext; rfl
  map_smul' r x := by apply Subtype.ext; rfl
def zShiftCLM (n : ℤ) : ZSpace E →L[ℝ] ZSpace E :=
  (zShiftLinear n).mkContinuous 1 (fun x => by change ‖zShift n x‖≤1*‖x‖; rw [zShift_norm,one_mul])
@[simp] theorem zShiftCLM_apply (n : ℤ) (x : ZSpace E) (k : ℤ) : zShiftCLM n x k=x (k+n) := rfl
theorem zShiftCLM_norm_le (n : ℤ) : ‖zShiftCLM (E:=E) n‖≤1 := by
  apply (zShiftCLM (E:=E) n).opNorm_le_bound (by norm_num)
  intro x
  change ‖zShift n x‖≤1*‖x‖
  rw [zShift_norm,one_mul]

end polyak.General.IQC
