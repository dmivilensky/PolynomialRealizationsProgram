import krylov.LotkaVolterra.GlobalSaddleField

/-!
Article: `main_krylov`, `apC:prop:LV`, full-range stable graph coordinates.

Logistic parameters cancel the state denominator of the lower branch and
compactify the unbounded upper branch. Both resulting slope fields are
rational only in `1-v`, which stays uniformly positive on `0 ≤ v ≤ γ`.
Uniform bounds therefore follow from ordinary compact C1 calculus.
-/
namespace krylov.LotkaVolterra
noncomputable section
open Set
open scoped NNReal

/-- Affine numerator coefficients for the two compactified graph equations.
`lower = true` denotes `0<U<U_F`; `false` denotes `U>U_F`. -/
def logisticP (γ : ℝ) (lower : Bool) (q : ℝ) : ℝ :=
  if lower then saddleS γ / saddleU γ else (saddleS γ / saddleU γ) * (1 - q)

def logisticQ (lower : Bool) (q : ℝ) : ℝ := if lower then -q else q
def logisticR (lower : Bool) (q : ℝ) : ℝ := if lower then 1 - q else 1

def logisticSlopeRate (γ : ℝ) (lower : Bool) (q v : ℝ) : ℝ :=
  (-2 * (logisticP γ lower q + logisticQ lower q * v)) * ((γ - v) / (1 - v)) +
    logisticR lower q * v

def logisticSlopeDerivative (γ : ℝ) (lower : Bool) (q v : ℝ) : ℝ :=
  (-2 * logisticQ lower q) * ((γ - v) / (1 - v)) +
    (-2 * (logisticP γ lower q + logisticQ lower q * v)) * ((γ - 1) / (1 - v) ^ 2) +
      logisticR lower q

theorem logisticSlopeRate_hasDerivAt {γ q v : ℝ} (lower : Bool) (hv : 1 - v ≠ 0) :
    HasDerivAt (logisticSlopeRate γ lower q) (logisticSlopeDerivative γ lower q v) v := by
  have hA := ((hasDerivAt_const v (logisticP γ lower q)).add
    ((hasDerivAt_id v).const_mul (logisticQ lower q))).const_mul (-2)
  have hB := ((hasDerivAt_id v).const_sub γ).div ((hasDerivAt_id v).const_sub 1) hv
  have hR := (hasDerivAt_id v).const_mul (logisticR lower q)
  convert (hA.mul hB).add hR using 1
  · rfl
  · dsimp [logisticSlopeDerivative]
    ring

theorem logisticSlopeRate_uniform_bounds {γ : ℝ} (hγ₁ : γ < 1) (lower : Bool) :
    ∃ L K : ℝ≥0,
      (∀ q ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc 0 γ, ‖logisticSlopeRate γ lower q v‖ ≤ L) ∧
      ∀ q ∈ Icc (0 : ℝ) 1, LipschitzOnWith K (logisticSlopeRate γ lower q) (Icc 0 γ) := by
  have hP : Continuous (logisticP γ lower) := by
    cases lower <;> unfold logisticP <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hQ : Continuous (logisticQ lower) := by
    cases lower <;> unfold logisticQ <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  have hR : Continuous (logisticR lower) := by
    cases lower <;> unfold logisticR <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> fun_prop
  let C : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc 0 γ
  have hden (p : ℝ × ℝ) (hp : p ∈ C) : 1 - p.2 ≠ 0 := by linarith [hp.2.2]
  have hA : ContinuousOn (fun p : ℝ × ℝ ↦
      -2 * (logisticP γ lower p.1 + logisticQ lower p.1 * p.2)) C :=
    ((hP.comp continuous_fst).continuousOn.add
      ((hQ.comp continuous_fst).continuousOn.mul continuous_snd.continuousOn)).const_mul (-2)
  have hB : ContinuousOn (fun p : ℝ × ℝ ↦ (γ - p.2) / (1 - p.2)) C :=
    (continuousOn_const.sub continuous_snd.continuousOn).div
      (continuousOn_const.sub continuous_snd.continuousOn) hden
  have hF : ContinuousOn (fun p : ℝ × ℝ ↦ logisticSlopeRate γ lower p.1 p.2) C :=
    (hA.mul hB).add ((hR.comp continuous_fst).continuousOn.mul continuous_snd.continuousOn)
  have hD : ContinuousOn (fun p : ℝ × ℝ ↦ logisticSlopeDerivative γ lower p.1 p.2) C :=
    ((((hQ.comp continuous_fst).continuousOn.const_mul (-2)).mul hB).add
      (hA.mul (continuousOn_const.div ((continuousOn_const.sub continuous_snd.continuousOn).pow 2)
        (fun p hp ↦ pow_ne_zero _ (hden p hp))))).add (hR.comp continuous_fst).continuousOn
  exact exists_uniform_bounds_on_rectangle hF hD
    (fun _ _ _ hv ↦ logisticSlopeRate_hasDerivAt lower (by linarith [hv.2]))

theorem logisticP_pos {γ q : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1) (lower : Bool)
    (hq : q < 1) : 0 < logisticP γ lower q := by
  have hA := div_pos (saddleS_pos hγ hγ₁) (saddleU_pos hγ₁)
  cases lower <;> simp only [logisticP, Bool.false_eq_true, ite_false, ite_true]
  · exact mul_pos hA (by linarith)
  · exact hA

theorem logisticSlopeRate_zero_neg {γ q : ℝ} (hγ : 0 < γ) (hγ₁ : γ < 1)
    (lower : Bool) (hq : q < 1) : logisticSlopeRate γ lower q 0 < 0 := by
  simp only [logisticSlopeRate, mul_zero, add_zero, sub_zero, div_one]
  have hp := logisticP_pos hγ hγ₁ lower hq
  exact mul_neg_of_neg_of_pos (by linarith) hγ

theorem logisticSlopeRate_gamma_pos {γ q : ℝ} (hγ : 0 < γ)
    (lower : Bool) (hq : q < 1) : 0 < logisticSlopeRate γ lower q γ := by
  simp only [logisticSlopeRate, sub_self, zero_div, mul_zero, zero_add]
  have hR : 0 < logisticR lower q := by
    cases lower
    · norm_num [logisticR]
    · simpa [logisticR, sub_pos] using hq
  exact mul_pos hR hγ

end
end krylov.LotkaVolterra
