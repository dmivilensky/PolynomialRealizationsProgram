import polyak.General.IQC.StablePlant
import polyak.General.IQC.CertificateSpace

/-! Exact isometric extension from the causal ℓ² space to whole-line ℓ².
Both summability and the norm identity are established before defining the
bounded embedding used to pull back the certificate. -/

namespace polyak.General.IQC
noncomputable section
variable {E : Type*} [NormedAddCommGroup E]

@[simp] theorem zeroExtend_negSucc (x : ℕ → E) (n : ℕ) :
    zeroExtend x (-((n:ℤ)+1))=0 := zeroExtend_neg x (by omega)

theorem zeroExtend_squareSummable {x : ℕ → E} (hx : SquareSummable x) :
    ZSquareSummable (zeroExtend x) := by
  have hxn : Summable (fun n => ‖x n‖^2) := hx
  have hn : Summable (fun n : ℕ => ‖zeroExtend x n‖^2) := by
    simpa only [zeroExtend_nat] using hxn
  have hm : Summable (fun n : ℕ => ‖zeroExtend x (-((n:ℤ)+1))‖^2) := by
    have he : (fun n : ℕ => ‖zeroExtend x (-((n:ℤ)+1))‖^2) = 0 := by
      funext n
      rw [zeroExtend_neg x (by omega),norm_zero,zero_pow (by norm_num : 2≠0)]
      rfl
    rw [he]
    exact summable_zero
  exact Summable.of_nat_of_neg_add_one (f := fun k : ℤ => ‖zeroExtend x k‖^2) hn hm

theorem zeroExtend_tsum_norm_sq {x : ℕ → E} (hx : SquareSummable x) :
    (∑' k : ℤ, ‖zeroExtend x k‖^2) = ∑' n : ℕ, ‖x n‖^2 := by
  have hxn : Summable (fun n => ‖x n‖^2) := hx
  have hn : Summable (fun n : ℕ => ‖zeroExtend x n‖^2) := by
    simpa only [zeroExtend_nat] using hxn
  have he : (fun n : ℕ => ‖zeroExtend x (-((n:ℤ)+1))‖^2) = 0 := by
    funext n
    rw [zeroExtend_neg x (by omega),norm_zero,zero_pow (by norm_num : 2≠0)]
    rfl
  have hm : Summable (fun n : ℕ => ‖zeroExtend x (-((n:ℤ)+1))‖^2) := by
    rw [he]; exact summable_zero
  have hsum := tsum_of_nat_of_neg_add_one (f := fun k : ℤ => ‖zeroExtend x k‖^2) hn hm
  rw [he] at hsum
  have hzero : tsum (0 : ℕ → ℝ) = 0 := tsum_zero
  rw [hzero,add_zero] at hsum
  rw [hsum]
  apply tsum_congr
  intro n
  rw [zeroExtend_nat]

def zeroExtendL2 (x : SequenceSpace E) : ZSpace E :=
  toZL2 (zeroExtend (fun n => x n)) (zeroExtend_squareSummable (lp_squareSummable x))

@[simp] theorem zeroExtendL2_apply (x : SequenceSpace E) (k : ℤ) :
    zeroExtendL2 x k=zeroExtend (fun n => x n) k := rfl

theorem zeroExtendL2_norm (x : SequenceSpace E) : ‖zeroExtendL2 x‖=‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [zlp_norm_sq]
  change (∑' k : ℤ, ‖zeroExtend (fun n => x n) k‖^2)=‖x‖^2
  rw [zeroExtend_tsum_norm_sq (lp_squareSummable x),lp_norm_eq_sequenceNorm,
    sequenceNorm,Real.sq_sqrt (tsum_nonneg (fun _ => sq_nonneg _))]

variable [NormedSpace ℝ E]

def zeroExtendLinear : SequenceSpace E →ₗ[ℝ] ZSpace E where
  toFun := zeroExtendL2
  map_add' x y := by
    apply Subtype.ext
    funext k
    change zeroExtend (fun n => x n+y n) k=zeroExtend (fun n => x n) k+zeroExtend (fun n => y n) k
    by_cases hk : 0 ≤ k <;> simp [zeroExtend,hk]
  map_smul' r x := by
    apply Subtype.ext
    funext k
    change zeroExtend (fun n => r • x n) k=r • zeroExtend (fun n => x n) k
    by_cases hk : 0 ≤ k <;> simp [zeroExtend,hk]

def zeroExtendLI : SequenceSpace E →ₗᵢ[ℝ] ZSpace E where
  toLinearMap := zeroExtendLinear
  norm_map' := zeroExtendL2_norm

def zeroExtendCLM : SequenceSpace E →L[ℝ] ZSpace E := zeroExtendLI.toContinuousLinearMap

@[simp] theorem zeroExtendCLM_apply (x : SequenceSpace E) (k : ℤ) :
    zeroExtendCLM x k=zeroExtend (fun n => x n) k := rfl

theorem zeroExtendCLM_norm (x : SequenceSpace E) : ‖zeroExtendCLM x‖=‖x‖ :=
  zeroExtendLI.norm_map x

theorem zeroExtendCLM_isometry : Isometry (zeroExtendCLM (E:=E)) := zeroExtendLI.isometry

end
end polyak.General.IQC
