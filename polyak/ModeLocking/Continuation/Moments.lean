import polyak.ModeLocking.Continuation.SlopeIdentity
import polyak.ModeLocking.Continuation.LinearSystem

/-! Analytic continuation of the actual slope moments by the nonsingular
pinning matrix of (R3). -/
noncomputable section
namespace polyak.ModeLocking.RegularData
open General Levels Filter
open scoped BigOperators Topology
variable {q : Tuning} {s : ℝ} {L : ℕ} (D : RegularData q s L)

def continuedPoint (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (ω : Frequency) (p : Continuation.Parameters) : Chart.AmbientPoint :=
  ![p 0, p 1, p 2, (ψ p).1, (ω : ℝ)]

theorem analyticAt_continuedPoint (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (hψ : AnalyticAt ℝ ψ (Continuation.parameters q)) (ω : Frequency) :
    AnalyticAt ℝ (D.continuedPoint ψ ω) (Continuation.parameters q) := by
  apply AnalyticAt.pi
  intro i
  fin_cases i
  · exact (ContinuousLinearMap.proj (R := ℝ) (0 : Fin 3) : Continuation.Parameters →L[ℝ] ℝ).analyticAt _
  · exact (ContinuousLinearMap.proj (R := ℝ) (1 : Fin 3) : Continuation.Parameters →L[ℝ] ℝ).analyticAt _
  · exact (ContinuousLinearMap.proj (R := ℝ) (2 : Fin 3) : Continuation.Parameters →L[ℝ] ℝ).analyticAt _
  · exact analyticAt_fst.comp hψ
  · exact analyticAt_const

theorem continuedPoint_base (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (hψ : ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ))) (ω : Frequency) :
    D.continuedPoint ψ ω (Continuation.parameters q) = ![q.kappa, q.y, q.beta, s, (ω : ℝ)] := by
  unfold continuedPoint
  rw [hψ]
  rfl

def continuedClassSlope (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (p : Continuation.Parameters) (i r : Fin D.d) : ℝ :=
  Continuation.jointSlope (D.reps r) (D.continuedPoint ψ (D.atoms i) p)

def continuedZeroSlope (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (p : Continuation.Parameters) (i : Fin D.d) : ℝ :=
  ∑ n ∈ D.lags, if n % (L : ℤ) = 0 then
    D.dual n * Continuation.jointSlope n (D.continuedPoint ψ (D.atoms i) p) else 0

def continuedPinning (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (p : Continuation.Parameters) : Matrix (Fin D.d) (Fin D.d) ℝ := fun i r =>
  (L : ℝ) * Real.sin ((D.reps r : ℝ) * (D.atoms i : ℝ) -
    Geometry.jointAngle (D.continuedPoint ψ (D.atoms i) p))

def slopeTarget (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (μ : Continuation.Parameters → (Fin D.d → ℝ)) (p : Continuation.Parameters) (i : Fin D.d) : ℝ :=
  -(∑ r, μ p r * D.continuedClassSlope ψ p i r) - D.continuedZeroSlope ψ p i

theorem pinningMatrix_det_ne_zero : D.pinningMatrix.det ≠ 0 := by
  have hL : (L : ℝ) ≠ 0 := by exact_mod_cast (by have h := D.period_ge; omega : L ≠ 0)
  let V : Matrix (Fin D.d) (Fin D.d) ℝ := fun i r => Real.sin
    ((D.reps r : ℝ) * (D.atoms i : ℝ) - Geometry.shiftedCurve q s (D.atoms i))
  have he : D.pinningMatrix = (L : ℝ) • V := rfl
  rw [he, Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hL) D.pinning_det

theorem analyticAt_continuedSlope (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (hψ : AnalyticAt ℝ ψ (Continuation.parameters q))
    (hbase : ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ)))
    (n : ℤ) (i : Fin D.d) : AnalyticAt ℝ
      (fun p => Continuation.jointSlope n (D.continuedPoint ψ (D.atoms i) p))
      (Continuation.parameters q) := by
  have hout : AnalyticAt ℝ (Continuation.jointSlope n)
      (D.continuedPoint ψ (D.atoms i) (Continuation.parameters q)) := by
    rw [D.continuedPoint_base ψ hbase]
    exact Continuation.analyticAt_jointSlope q s n (D.atoms i).property
  exact hout.comp (D.analyticAt_continuedPoint ψ hψ (D.atoms i))

theorem analytic_moment_continuation (ψ : Continuation.Parameters → (ℝ × (Fin D.d → ℝ)))
    (μ : Continuation.Parameters → (Fin D.d → ℝ))
    (hψ : AnalyticAt ℝ ψ (Continuation.parameters q))
    (hμ : AnalyticAt ℝ μ (Continuation.parameters q))
    (hψbase : ψ (Continuation.parameters q) = (s, fun i => (D.primal i : ℝ)))
    (hμbase : μ (Continuation.parameters q) = D.classWeight) :
    ∃ m : Continuation.Parameters → (Fin D.d → ℝ), AnalyticAt ℝ m (Continuation.parameters q) ∧
      m (Continuation.parameters q) = D.slopeMoment ∧
      ∀ᶠ p in 𝓝 (Continuation.parameters q),
        (D.continuedPinning ψ p).mulVec (m p) = D.slopeTarget ψ μ p := by
  have hV (i r : Fin D.d) : AnalyticAt ℝ (fun p => D.continuedPinning ψ p i r)
      (Continuation.parameters q) := by
    have hout : AnalyticAt ℝ Geometry.jointAngle
        (D.continuedPoint ψ (D.atoms i) (Continuation.parameters q)) := by
      rw [D.continuedPoint_base ψ hψbase]
      exact Geometry.analyticAt_jointAngle_actual q s (D.atoms i).property
    exact analyticAt_const.mul (Real.analyticAt_sin.comp
      (analyticAt_const.sub (hout.comp (D.analyticAt_continuedPoint ψ hψ (D.atoms i)))))
  have ht : AnalyticAt ℝ (D.slopeTarget ψ μ) (Continuation.parameters q) := by
    apply AnalyticAt.pi
    intro i
    have hmu (r : Fin D.d) : AnalyticAt ℝ (fun p => μ p r) (Continuation.parameters q) :=
      ((ContinuousLinearMap.proj (R := ℝ) r : (Fin D.d → ℝ) →L[ℝ] ℝ).analyticAt _).comp hμ
    have hsum : AnalyticAt ℝ (fun p => ∑ r, μ p r * D.continuedClassSlope ψ p i r)
        (Continuation.parameters q) :=
      Finset.analyticAt_fun_sum Finset.univ (fun r _ =>
        (hmu r).mul (D.analyticAt_continuedSlope ψ hψ hψbase (D.reps r) i))
    have hz : AnalyticAt ℝ (fun p => D.continuedZeroSlope ψ p i) (Continuation.parameters q) := by
      apply Finset.analyticAt_fun_sum
      intro n _
      by_cases hn : n % (L : ℤ) = 0
      · simp only [ite_eq_left hn]
        exact analyticAt_const.mul (D.analyticAt_continuedSlope ψ hψ hψbase n i)
      · simp only [ite_eq_right hn]
        exact analyticAt_const
    exact hsum.neg.sub hz
  have hVbase : D.continuedPinning ψ (Continuation.parameters q) = D.pinningMatrix := by
    ext i r
    unfold continuedPinning
    rw [D.continuedPoint_base ψ hψbase, Geometry.jointAngle_actual q s (D.atoms i).property]
    rfl
  have htbase : D.slopeTarget ψ μ (Continuation.parameters q) =
      fun i => -(∑ r, D.classWeight r * D.classSlope i r) - D.zeroClassSlope i := by
    funext i
    have hslope (n : ℤ) : Continuation.jointSlope n
        (D.continuedPoint ψ (D.atoms i) (Continuation.parameters q)) =
          deriv (lagExtension q s n) (D.atoms i) := by
      rw [D.continuedPoint_base ψ hψbase]
      exact Continuation.jointSlope_actual q s n (D.atoms i).property
    simp only [slopeTarget, continuedClassSlope, continuedZeroSlope, hμbase, hslope, classSlope, zeroClassSlope]
  have hbase : (D.continuedPinning ψ (Continuation.parameters q)).mulVec D.slopeMoment =
      D.slopeTarget ψ μ (Continuation.parameters q) := by
    rw [hVbase, htbase]
    exact D.pinning_system_base
  apply Continuation.analytic_linear_solution (D.continuedPinning ψ) (D.slopeTarget ψ μ)
    (Continuation.parameters q) D.slopeMoment hV ht _ hbase
  rw [hVbase]
  exact D.pinningMatrix_det_ne_zero

end polyak.ModeLocking.RegularData
