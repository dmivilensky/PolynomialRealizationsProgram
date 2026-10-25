import polyak.General.IQC.Homotopy
import Mathlib.Analysis.InnerProductSpace.l2Space

/-! Article: Appendix D, the actual ℓ² space behind the truncation proof.
The unrestricted causal solution is embedded only after its summability has
been established. Operator bounds are inherited from finite-prefix bounds. -/
noncomputable section
namespace polyak.General.IQC
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E]

abbrev SequenceSpace (E : Type*) [NormedAddCommGroup E] := lp (fun _ : ℕ => E) 2

theorem lp_squareSummable (x : SequenceSpace E) : SquareSummable (fun k => x k) := by
  have h:=(lp.memℓp x).summable (by norm_num : 0<(2 : ℝ≥0∞).toReal)
  simpa only [SquareSummable,ENNReal.toReal_ofNat,Real.rpow_two] using h

def toL2 (x : ℕ → E) (hx : SquareSummable x) : SequenceSpace E :=
  ⟨x,(memℓp_gen_iff (by norm_num : 0<(2 : ℝ≥0∞).toReal)).mpr (by
    simpa only [SquareSummable,ENNReal.toReal_ofNat,Real.rpow_two] using hx)⟩

@[simp] theorem toL2_apply (x : ℕ → E) (hx : SquareSummable x) (k : ℕ) : toL2 x hx k=x k := rfl

theorem lp_norm_eq_sequenceNorm (x : SequenceSpace E) : ‖x‖=sequenceNorm (fun k => x k) := by
  apply (sq_eq_sq₀ (norm_nonneg _) (sequenceNorm_nonneg _)).mp
  have h:=lp.norm_rpow_eq_tsum (by norm_num : 0<(2 : ℝ≥0∞).toReal) x
  simp only [ENNReal.toReal_ofNat,Real.rpow_two] at h
  rw [sequenceNorm,Real.sq_sqrt (tsum_nonneg (fun k => sq_nonneg _))]
  exact h

theorem toL2_norm (x : ℕ → E) (hx : SquareSummable x) : ‖toL2 x hx‖=sequenceNorm x :=
  lp_norm_eq_sequenceNorm _

variable [NormedSpace ℝ E]
namespace Feedback
variable (F : Feedback E)

theorem plant_squareSummable {x : ℕ → E} (hx : SquareSummable x) :
    SquareSummable (F.plant x) := by
  apply squareSummable_of_prefix_bound (C:=F.gain*sequenceNorm x)
  intro N
  exact (F.prefix_gain x N).trans
    (mul_le_mul_of_nonneg_left (prefixNorm_le_sequenceNorm hx N) F.gain_nonneg)

theorem plant_norm_bound {x : ℕ → E} (hx : SquareSummable x) :
    sequenceNorm (F.plant x)≤F.gain*sequenceNorm x :=
  sequenceNorm_le_of_prefix_bound (mul_nonneg F.gain_nonneg (sequenceNorm_nonneg x))
    (fun N => (F.prefix_gain x N).trans
      (mul_le_mul_of_nonneg_left (prefixNorm_le_sequenceNorm hx N) F.gain_nonneg))

def plantLinear : SequenceSpace E →ₗ[ℝ] SequenceSpace E where
  toFun x:=toL2 (F.plant x) (F.plant_squareSummable (lp_squareSummable x))
  map_add' x y:=by
    apply Subtype.ext
    exact F.plant.map_add x y
  map_smul' r x:=by
    apply Subtype.ext
    exact F.plant.map_smul r x

def plantL2 : SequenceSpace E →L[ℝ] SequenceSpace E :=
  F.plantLinear.mkContinuous F.gain (fun x => by
    rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
    exact F.plant_norm_bound (lp_squareSummable x))

@[simp] theorem plantL2_apply (x : SequenceSpace E) (k : ℕ) : F.plantL2 x k=F.plant x k := rfl

theorem plantL2_norm_le : ‖F.plantL2‖≤F.gain := by
  apply F.plantL2.opNorm_le_bound F.gain_nonneg
  intro x
  rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
  exact F.plant_norm_bound (lp_squareSummable x)

theorem delta_squareSummable {x : ℕ → E} (hx : SquareSummable x) :
    SquareSummable (F.delta x) :=
  squareSummable_of_prefix_bound (fun N =>
    (F.delta_prefix_bound x N).trans (prefixNorm_le_sequenceNorm hx N))

def deltaL2 (x : SequenceSpace E) : SequenceSpace E :=
  toL2 (F.delta x) (F.delta_squareSummable (lp_squareSummable x))

@[simp] theorem deltaL2_apply (x : SequenceSpace E) (k : ℕ) : F.deltaL2 x k=F.delta x k := rfl

theorem deltaL2_norm_le (x : SequenceSpace E) : ‖F.deltaL2 x‖≤‖x‖ := by
  rw [lp_norm_eq_sequenceNorm,lp_norm_eq_sequenceNorm]
  exact sequenceNorm_le_of_prefix_bound (sequenceNorm_nonneg _)
    (fun N => (F.delta_prefix_bound x N).trans
      (prefixNorm_le_sequenceNorm (lp_squareSummable x) N))

theorem run_toL2_equation (τ : ℝ) (f : ℕ → E) (hf : SquareSummable f)
    (hx : SquareSummable (F.run τ f)) :
    toL2 (F.run τ f) hx=
      F.plantL2 (τ • F.deltaL2 (toL2 (F.run τ f) hx))+toL2 f hf := by
  apply Subtype.ext
  exact F.run_equation τ f

end Feedback
end polyak.General.IQC
