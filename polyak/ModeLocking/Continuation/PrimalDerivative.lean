import polyak.ModeLocking.Continuation.PrimalSystem

/-! The partial derivative of the original primal system is exactly the
bordered equivalence obtained from the primary regularity conditions. -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels
open scoped BigOperators
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

theorem hasFDerivAt_primalSystem_partial :
    HasFDerivAt (fun z : ℝ × (Fin D.d → ℝ) => Continuation.primalSystem D.reps D.atoms
      (Continuation.parameters q, z)) D.primalDerivativeEquiv.toContinuousLinearMap
      (s, fun i => (D.primal i : ℝ)) := by
  let w : Fin D.d → ℝ := fun i => D.primal i
  let a : Fin D.d → Fin D.d → ℝ → ℝ :=
    fun r i t => (Geometry.shiftedCurve q t).lag (D.reps r) (D.atoms i)
  let da : Fin D.d → Fin D.d → ℝ := fun r i => deriv (a r i) s
  have ha (r i : Fin D.d) : HasDerivAt (a r i) (da r i) s :=
    (Continuation.hasDerivAt_lag_shift q s (D.reps r) (D.atoms i)
      ⟨(D.atoms_grid i).1, D.atoms_lt_pi i⟩).differentiableAt.hasDerivAt
  let lrow (r : Fin D.d) := Continuation.weightedDerivative (fun i => a r i s) (da r) w
  have hrows : HasFDerivAt (fun z : ℝ × (Fin D.d → ℝ) => fun r => ∑ i, z.2 i * a r i z.1)
      (ContinuousLinearMap.pi lrow) (s, w) := by
    apply hasFDerivAt_pi.mpr
    intro r
    exact Continuation.hasFDerivAt_weighted_sum (a r) (da r) w s (ha r)
  let normMap : (ℝ × (Fin D.d → ℝ)) →L[ℝ] ℝ :=
    ∑ i, ((ContinuousLinearMap.proj (R := ℝ) i : (Fin D.d → ℝ) →L[ℝ] ℝ).comp
      (ContinuousLinearMap.snd ℝ ℝ (Fin D.d → ℝ)))
  have hnorm : HasFDerivAt (fun z : ℝ × (Fin D.d → ℝ) => (∑ i, z.2 i) - 1) normMap (s, w) := by
    exact (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ =>
      (((ContinuousLinearMap.proj (R := ℝ) i : (Fin D.d → ℝ) →L[ℝ] ℝ).comp
        (ContinuousLinearMap.snd ℝ ℝ (Fin D.d → ℝ))).hasFDerivAt))).sub_const 1
  have hb (r : Fin D.d) : (∑ i, w i * da r i) = D.shiftVector r := by
    have he := (HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ => (ha r i).const_mul (w i))).deriv
    exact he.symm
  have hlin : (ContinuousLinearMap.pi lrow).prod normMap = D.primalDerivativeEquiv.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    intro z
    apply Prod.ext
    · funext r
      change Continuation.weightedDerivative (fun i => a r i s) (da r) w z =
        D.matrix.mulVec z.2 r + z.1 * D.shiftVector r
      rw [Continuation.weightedDerivative_apply, hb]
      rfl
    · change normMap z = ∑ i, z.2 i
      simp [normMap]
  have hpair := hrows.prodMk hnorm
  rw [hlin] at hpair
  convert hpair using 1
  funext z
  apply Prod.ext
  · funext r
    change (∑ i, Continuation.ambientLag (D.reps r) (D.atoms i)
      (Continuation.sourcePoint q z.1) * z.2 i) = ∑ i, z.2 i * a r i z.1
    simp only [Continuation.ambientLag_actual, a, mul_comm]
  · rfl

end polyak.ModeLocking.RegularData
