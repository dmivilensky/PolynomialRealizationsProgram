import krylov.LotkaVolterra.GlobalLogisticField
import krylov.LotkaVolterra.GlobalWholeStrip
import krylov.LotkaVolterra.GlobalEndpointGraph
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
Article: `main_krylov`, `apC:prop:LV`, full state ranges of both branches.

Whole-line shooting constructs the compactified lower and upper slope
solutions for every real logistic parameter. Neither a global branch nor
a maximal continuation theorem is assumed.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

def logisticParameter (t : ℝ) : ℝ := 1 / (1 + Real.exp t)

theorem logisticParameter_mem (t : ℝ) : logisticParameter t ∈ Ioo (0 : ℝ) 1 := by
  have hp := Real.exp_pos t
  exact ⟨div_pos (by norm_num) (by linarith),
    (div_lt_one (by linarith : 0 < 1 + Real.exp t)).mpr (by linarith)⟩

theorem logisticParameter_continuous : Continuous logisticParameter := by
  unfold logisticParameter
  exact continuous_const.div (continuous_const.add Real.continuous_exp)
    (fun t ↦ ne_of_gt (by linarith [Real.exp_pos t]))

theorem logisticParameter_hasDerivAt (t : ℝ) :
    HasDerivAt logisticParameter (-logisticParameter t * (1 - logisticParameter t)) t := by
  have hd : 1 + Real.exp t ≠ 0 := ne_of_gt (by linarith [Real.exp_pos t])
  convert (hasDerivAt_const t (1 : ℝ)).div
    ((hasDerivAt_const t (1 : ℝ)).add (Real.hasDerivAt_exp t)) hd using 1
  · rfl
  · dsimp [logisticParameter]
    field_simp
    ring

def clippedLogisticSlopeRate (γ : ℝ) (lower : Bool) (t v : ℝ) : ℝ :=
  logisticSlopeRate γ lower (logisticParameter t) (saddleSlopeClip γ v)

theorem clippedLogisticSlopeRate_continuous_time (γ : ℝ) (lower : Bool) (v : ℝ) :
    Continuous (fun t ↦ clippedLogisticSlopeRate γ lower t v) := by
  have hP : Continuous (fun t ↦ logisticP γ lower (logisticParameter t)) := by
    cases lower <;> simp only [logisticP, Bool.false_eq_true, ite_false, ite_true]
    · exact continuous_const.mul (continuous_const.sub logisticParameter_continuous)
    · exact continuous_const
  have hQ : Continuous (fun t ↦ logisticQ lower (logisticParameter t)) := by
    cases lower <;> simp only [logisticQ, Bool.false_eq_true, ite_false, ite_true]
    · exact logisticParameter_continuous
    · exact logisticParameter_continuous.neg
  have hR : Continuous (fun t ↦ logisticR lower (logisticParameter t)) := by
    cases lower <;> simp only [logisticR, Bool.false_eq_true, ite_false, ite_true]
    · exact continuous_const
    · exact continuous_const.sub logisticParameter_continuous
  exact (((hP.add (hQ.mul continuous_const)).const_mul (-2)).mul continuous_const).add
    (hR.mul continuous_const)

theorem clippedLogisticSlopeRate_bounds {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (lower : Bool) :
    ∃ L K : ℝ≥0, (∀ t v, ‖clippedLogisticSlopeRate γ lower t v‖ ≤ L) ∧
      ∀ t, LipschitzWith K (clippedLogisticSlopeRate γ lower t) := by
  obtain ⟨L, K, hL, hK⟩ := logisticSlopeRate_uniform_bounds hγ₁ lower
  refine ⟨L, K, fun t v ↦ hL _ ⟨(logisticParameter_mem t).1.le, (logisticParameter_mem t).2.le⟩
    _ (saddleSlopeClip_mem hγ.le v), fun t ↦ ?_⟩
  apply LipschitzWith.of_dist_le_mul
  intro v w
  calc
    dist (clippedLogisticSlopeRate γ lower t v) (clippedLogisticSlopeRate γ lower t w) ≤
        K * dist (saddleSlopeClip γ v) (saddleSlopeClip γ w) :=
      (hK _ ⟨(logisticParameter_mem t).1.le, (logisticParameter_mem t).2.le⟩).dist_le_mul
        _ (saddleSlopeClip_mem hγ.le v) _ (saddleSlopeClip_mem hγ.le w)
    _ ≤ K * dist v w := by
      gcongr
      simpa using (saddleSlopeClip_lipschitz γ).dist_le_mul v w

/-- Both full-range compactified branches exist as actual scalar integral
curves on the entire real parameter axis. -/
theorem exists_whole_logistic_slope {γ : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (lower : Bool) :
    ∃ v : ℝ → ℝ, ∀ t, v t ∈ Ioo 0 γ ∧
      HasDerivAt v (logisticSlopeRate γ lower (logisticParameter t) (v t)) t := by
  obtain ⟨L, K, hbound, hLip⟩ := clippedLogisticSlopeRate_bounds hγ hγ₁ lower
  have ha (t : ℝ) : clippedLogisticSlopeRate γ lower t 0 < 0 := by
    rw [clippedLogisticSlopeRate, saddleSlopeClip_eq (show (0 : ℝ) ∈ Icc 0 γ from ⟨le_rfl, hγ.le⟩)]
    exact logisticSlopeRate_zero_neg hγ hγ₁ lower (logisticParameter_mem t).2
  have hb (t : ℝ) : 0 < clippedLogisticSlopeRate γ lower t γ := by
    rw [clippedLogisticSlopeRate, saddleSlopeClip_eq (show γ ∈ Icc 0 γ from ⟨hγ.le, le_rfl⟩)]
    exact logisticSlopeRate_gamma_pos hγ lower (logisticParameter_mem t).2
  obtain ⟨v, hv⟩ := exists_whole_strip_solution hLip
    (clippedLogisticSlopeRate_continuous_time γ lower) hbound hγ ha hb
  have hstrict (t : ℝ) : v t ∈ Ioo 0 γ := by
    have hh := hv t
    constructor
    · by_contra! hle
      have heq : v t = 0 := le_antisymm hle hh.1.1
      have hd := derivative_nonneg_of_right_lower_bound hh.2
        (fun T _ ↦ by rw [heq]; exact (hv T).1.1)
      rw [heq] at hd
      exact (not_le_of_gt (ha t)) hd
    · by_contra! hle
      have heq : v t = γ := le_antisymm hh.1.2 hle
      have hd := derivative_nonpos_of_right_upper_bound hh.2
        (fun T _ ↦ by rw [heq]; exact (hv T).1.2)
      rw [heq] at hd
      exact (not_le_of_gt (hb t)) hd
  refine ⟨v, fun t ↦ ⟨hstrict t, ?_⟩⟩
  simpa only [clippedLogisticSlopeRate, saddleSlopeClip_eq (hv t).1] using (hv t).2

end
end krylov.LotkaVolterra
