import krylov.Functions.MetricCubicSource
import krylov.Functions.NativeRFCSpatialResponse

/-!
Article: main_krylov, thm:H, actual native RFC on the cubic realization.
Use: specialize genuine function-to-operator transfer to an actual physical
quadratic-plus-cubic objective, proving every derivative and every local
regularity hypothesis from its formula and the constructed positive root.
Source: actual scalar derivatives, the exact metric root and native RFC.
-/

namespace krylov.Functions
noncomputable section
open Set Metric Matrix krylov.Reference krylov.Nonlinear krylov.Secant krylov.Methods
open scoped InnerProductSpace NNReal Matrix.Norms.L2Operator
variable {k : ℕ}

/-- The true positive metric root is self-adjoint as an actual continuous map.
Article: main_krylov, thm:H. -/
theorem metricCoordinates_forward_symmetric
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) :
    (metricCoordinates base hb).toContinuousLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  exact Matrix.isHermitian_iff_isSymm.mpr (metricRoot_isSymm base)

/-- The true physical cubic minimizer Hessian is exactly the original positive
reference matrix, preserving its genuine n-atom CG geometry.
Article: main_krylov, thm:H. -/
theorem metricCubicHessian_metric_zero
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1)))) :
    metricCubicHessian (metricCoordinates base hb) T 0 = cgOperator base := by
  apply ContinuousLinearMap.ext
  intro v
  change cgOperator (metricRoot base) (canonicalHessian T
    ((metricCoordinates base hb) 0) (cgOperator (metricRoot base) v)) = cgOperator base v
  rw [map_zero, canonicalHessian_zero, ContinuousLinearMap.id_apply]
  simp only [cgOperator, ← mul_apply_eq_comp, ← map_mul, metricRoot_square base hb]

/-- Every genuine physical cubic with a full-atom original reference has the
actual native RFC cubic asymptotic with the literal compatible tensor
staircase coefficient. No derivative, query-bound or transfer assumptions
are supplied by the caller. Article: main_krylov, thm:H. -/
theorem metricCubic_nativeRFC_spatial
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef) (hk : 0 < k)
    (T : SymmetricCubic (EuclideanSpace ℝ (Fin (k+1))))
    (u : EuclideanSpace ℝ (Fin (k+1)))
    (hNu : referenceAtomCount base hb (cgOperator base u) = k+1) :
    ∃ r : ℝ, 0 < r ∧ ∀ η : ℝ, 0 < η → ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ →
        ‖cgOperator (metricRoot base)⁻¹
            (gradient (metricCubicObjective (metricCoordinates base hb) T)
              (rfcFunctionPoint (metricCoordinates base hb)
                (metricCubicObjective (metricCoordinates base hb) T)
                (metricCubicGradient (metricCoordinates base hb) T) fullMemory r (ε • u) (k+1))) +
          ε^3 • rfcTensorCanonicalCoefficient base hb
            (metricCubicVariation (metricCoordinates base hb) T) u‖ ≤ η * ε^3 := by
  let S := metricCoordinates base hb
  let L : ℝ≥0 := ‖canonicalVariation T‖₊
  let r : ℝ := (4*((L : ℝ)+1))⁻¹
  have hr : 0 < r := by dsimp only [r]; positivity
  have hLr : (L : ℝ)*r ≤ 1/2 := by
    dsimp only [r]
    rw [mul_inv_le_iff₀ (by positivity)]
    have hL := L.coe_nonneg
    linarith
  have hS : S.toContinuousLinearMap.IsSymmetric := metricCoordinates_forward_symmetric base hb
  have hH := (metricCubicHessian_canonical_lipschitz S T).lipschitzOnWith (s := closedBall 0 r)
  have hp := metricRFCPoint_spatial_leading_gradient base hb hk
    (metricCubicObjective S T) (metricCubicGradient S T) (metricCubicHessian S T)
    (metricCubicVariation S T) (metricCubicHessian_hasFDerivAt S T 0)
    hr (metricCubicGradient_zero S T) (metricCubicHessian_metric_zero base hb T) hLr hH
    (fun z _ => metricCubicObjective_hasFDerivAt S hS T z)
    (fun z _ => metricCubicGradient_hasFDerivAt S T z)
    {cgOperator base u} isCompact_singleton
    (fun g hg => by simpa only [mem_singleton_iff.mp hg] using hNu)
    (‖u‖+1) (by positivity)
  refine ⟨r, hr, ?_⟩
  intro η hη
  obtain ⟨ep, hep, hbnd⟩ := hp η hη
  refine ⟨ep, hep, ?_⟩
  intro ε hε he
  rw [gradient_metricCubicObjective S hS T]
  exact hbnd ε hε he u (by linarith) (mem_singleton _)

end
end krylov.Functions
