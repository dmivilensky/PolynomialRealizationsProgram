import polyak.General.IQC.HomotopyFrequency

/-! Finite real spatial coordinates of causal l2 signals. Coordinate
projection and zero extension/Fourier preserve the exact sum of energies;
the multiplier and IQC act blockwise without a dimension-dependent loss. -/
noncomputable section
namespace polyak.General.IQC.Fourier
open MeasureTheory Filter Set
open scoped ENNReal
local instance : Fact (0<2*Real.pi) := ⟨Real.two_pi_pos⟩

private theorem coordinate_squareSummable {d : ℕ} (i : Fin d)
    (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    SquareSummable (fun n=>(x n i:ℂ)) := by
  have hx := lp_squareSummable x
  apply Summable.of_nonneg_of_le (fun _=>sq_nonneg _) ?_ hx
  intro n
  have hh := PiLp.norm_apply_le (x n) i
  have he : ‖(x n i:ℂ)‖=‖x n i‖ := by simp
  rw [he]
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

def coordinateSignal {d : ℕ} (i : Fin d) (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    SequenceSpace ℂ := toL2 (fun n=>(x n i:ℂ)) (coordinate_squareSummable i x)

@[simp] theorem coordinateSignal_apply {d : ℕ} (i : Fin d)
    (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) (n : ℕ) : coordinateSignal i x n=(x n i:ℂ) := rfl

theorem coordinateSignal_norm_sq {d : ℕ} (i : Fin d)
    (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    ‖coordinateSignal i x‖^2=∑' n,‖x n i‖^2 := by
  rw [lp_norm_eq_sequenceNorm,sequenceNorm,Real.sq_sqrt (tsum_nonneg (fun _=>sq_nonneg _))]
  apply tsum_congr
  intro n
  simp only [coordinateSignal_apply,Complex.norm_real,Real.norm_eq_abs]

theorem coordinateSignal_norm_le {d : ℕ} (i : Fin d)
    (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) : ‖coordinateSignal i x‖≤‖x‖ := by
  have hleft : Summable (fun n=>‖x n i‖^2) := by
    simpa only [SquareSummable,Complex.norm_real,Real.norm_eq_abs] using coordinate_squareSummable i x
  have hh : (∑' n,‖x n i‖^2)≤∑' n,‖x n‖^2 :=
    hleft.tsum_le_tsum (fun n=>pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (x n) i) 2)
      (lp_squareSummable x)
  rw [← coordinateSignal_norm_sq] at hh
  have hx : ‖x‖^2=∑' n,‖x n‖^2 := by
    rw [lp_norm_eq_sequenceNorm,sequenceNorm,Real.sq_sqrt (tsum_nonneg (fun _=>sq_nonneg _))]
  nlinarith [norm_nonneg (coordinateSignal i x),norm_nonneg x]

def coordinateLinear {d : ℕ} (i : Fin d) : SequenceSpace (EuclideanSpace ℝ (Fin d))→ₗ[ℝ]SequenceSpace ℂ where
  toFun := coordinateSignal i
  map_add' x y := by
    ext n
    simp only [coordinateSignal_apply,lp.coeFn_add,Pi.add_apply,PiLp.add_apply,Complex.ofReal_add]
  map_smul' r x := by
    ext n
    simp only [coordinateSignal_apply,lp.coeFn_smul,Pi.smul_apply,PiLp.smul_apply,
      RingHom.id_apply,Complex.real_smul,Complex.ofReal_mul,smul_eq_mul]

def coordinateCLM {d : ℕ} (i : Fin d) : SequenceSpace (EuclideanSpace ℝ (Fin d))→L[ℝ]SequenceSpace ℂ :=
  (coordinateLinear i).mkContinuous 1 (fun x=>by change ‖coordinateSignal i x‖≤1*‖x‖; simpa only [one_mul] using coordinateSignal_norm_le i x)

/-- Exact spatial energy sum, with no factor depending on the number of coordinates. -/
theorem sum_coordinate_norm_sq {d : ℕ} (x : SequenceSpace (EuclideanSpace ℝ (Fin d))) :
    ∑ i,‖coordinateSignal i x‖^2=‖x‖^2 := by
  simp only [coordinateSignal_norm_sq]
  have hs (i : Fin d) : Summable (fun n=>‖x n i‖^2) := by
    simpa only [SquareSummable,Complex.norm_real,Real.norm_eq_abs] using coordinate_squareSummable i x
  have hx : ‖x‖^2=∑' n,‖x n‖^2 := by
    rw [lp_norm_eq_sequenceNorm,sequenceNorm,Real.sq_sqrt (tsum_nonneg (fun _=>sq_nonneg _))]
  rw [hx,← Summable.tsum_finsetSum (fun i _=>hs i)]
  apply tsum_congr
  intro n
  exact (PiLp.norm_sq_eq_of_L2 (fun _ : Fin d=>ℝ) (x n)).symm

end polyak.General.IQC.Fourier
