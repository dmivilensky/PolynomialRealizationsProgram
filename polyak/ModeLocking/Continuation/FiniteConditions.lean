import polyak.ModeLocking.Continuation.ActualSlacks

/-! The remaining finite strict conditions persist by their actual source
formulas and positive base margins. -/
noncomputable section
namespace polyak.ModeLocking.RegularData.ContinuationData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} {D : RegularData q s L} (C : D.ContinuationData)

theorem continuousAt_weight_actual (n : ℤ) :
    ContinuousAt (fun q' : Tuning => C.weight (Continuation.parameters q') n) q :=
  (C.analytic_weight n).continuousAt.comp Continuation.continuous_parameters.continuousAt

theorem pinning_pos_near : ∀ᶠ q' in 𝓝 q, ∀ i : Fin D.d,
    0 < pinningPolynomial D.lags (C.weight (Continuation.parameters q')) (D.atoms i) := by
  have hi (i : Fin D.d) : ∀ᶠ q' in 𝓝 q,
      0 < pinningPolynomial D.lags (C.weight (Continuation.parameters q')) (D.atoms i) := by
    have hc : ContinuousAt (fun q' : Tuning =>
        pinningPolynomial D.lags (C.weight (Continuation.parameters q')) (D.atoms i)) q :=
      tendsto_finsetSum D.lags (fun n _ => (C.continuousAt_weight_actual n).mul continuousAt_const)
    apply hc.eventually
    apply eventually_gt_nhds
    simpa only [pinningPolynomial, C.weight_base] using D.pinning_pos i
  exact Filter.eventually_all.mpr hi

def actualPinning (q' : Tuning) : Matrix (Fin D.d) (Fin D.d) ℝ :=
  fun i r => Real.sin ((D.reps r : ℝ) * (D.atoms i : ℝ) -
    Geometry.shiftedCurve q' (C.shift (Continuation.parameters q')) (D.atoms i))

theorem pinning_det_near : ∀ᶠ q' in 𝓝 q, (C.actualPinning q').det ≠ 0 := by
  have hc : ContinuousAt C.actualPinning q := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro r
    exact Real.continuous_sin.continuousAt.comp (continuousAt_const.sub (C.continuousAt_phase_actual i))
  have hd : ContinuousAt (fun q' : Tuning => (C.actualPinning q').det) q :=
    (continuous_id.matrix_det : Continuous (fun M : Matrix (Fin D.d) (Fin D.d) ℝ => M.det)).continuousAt.comp hc
  apply hd.eventually_ne
  have he : C.actualPinning q = (fun i r : Fin D.d => Real.sin ((D.reps r : ℝ) * (D.atoms i : ℝ) -
      Geometry.shiftedCurve q s (D.atoms i))) := by
    ext i r
    change Real.sin (_ - Geometry.shiftedCurve q (C.shift (Continuation.parameters q)) _) = _
    rw [C.shift_base]
  rw [he]
  exact D.pinning_det

end polyak.ModeLocking.RegularData.ContinuationData
