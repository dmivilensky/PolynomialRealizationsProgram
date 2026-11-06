import chebyshev1.Perturbations.SmoothExpansion
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-! The gradient tensor in the nonlinear expansion is the Riesz representation of D³f. -/
namespace chebyshev1.Perturbations
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped RealInnerProductSpace

private theorem iteratedFDeriv_equiv_comp_right {X Y Z : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (T : X ≃L[ℝ] Y) (g : Y → Z) (n : ℕ) (x : X) :
    iteratedFDeriv ℝ n (g ∘ T) x =
      (iteratedFDeriv ℝ n g (T x)).compContinuousLinearMap fun _ => T.toContinuousLinearMap := by
  simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using
    T.iteratedFDerivWithin_comp_right g uniqueDiffOn_univ (Set.mem_univ (T x)) n

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Transport through the constant Riesz equivalence identifies the tensors without permuting slots. -/
theorem gradient_second_derivative_inner (f : E → ℝ) (x u v w : E) :
    ⟪(fderiv ℝ (fderiv ℝ (gradient f)) x u) v, w⟫ =
      iteratedFDeriv ℝ 3 f x ![u, v, w] := by
  let R := (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv
  have hgrad : gradient f = R ∘ fderiv ℝ f := rfl
  have htransport : iteratedFDeriv ℝ 2 (gradient f) x ![u, v] =
      R (iteratedFDeriv ℝ 2 (fderiv ℝ f) x ![u, v]) := by
    rw [hgrad, R.iteratedFDeriv_comp_left]
    rfl
  calc
    _ = ⟪iteratedFDeriv ℝ 2 (gradient f) x ![u, v], w⟫ := by
      simp [iteratedFDeriv_succ_apply_right, Fin.init]
    _ = ⟪R (iteratedFDeriv ℝ 2 (fderiv ℝ f) x ![u, v]), w⟫ := by rw [htransport]
    _ = (iteratedFDeriv ℝ 2 (fderiv ℝ f) x ![u, v]) w := by
      change ⟪(InnerProductSpace.toDual ℝ E).symm _, w⟫ = _
      rw [← InnerProductSpace.toDual_apply_apply, LinearIsometryEquiv.apply_symm_apply]
    _ = _ := by simp [iteratedFDeriv_succ_apply_right, Fin.init]

/-- The tensor occurring in the finite-coordinate nonlinear expansion has exactly the same D³f slots. -/
theorem coordinate_gradient_second_derivative_inner {d : Type*} [Fintype d]
    (f : EuclideanSpace ℝ d → ℝ) (u v w : d → ℝ) :
    ⟪WithLp.toLp 2 ((fderiv ℝ (fderiv ℝ (Nonlinear.gradientCoordinates (gradient f))) 0 u) v),
        WithLp.toLp 2 w⟫ =
      iteratedFDeriv ℝ 3 f 0 ![WithLp.toLp 2 u, WithLp.toLp 2 v, WithLp.toLp 2 w] := by
  let T := PiLp.continuousLinearEquiv 2 ℝ (fun _ : d => ℝ)
  let g := Nonlinear.gradientCoordinates (gradient f)
  have hg : g = T ∘ (gradient f ∘ T.symm) := rfl
  have htransport : T.symm (iteratedFDeriv ℝ 2 g 0 ![u, v]) =
      iteratedFDeriv ℝ 2 (gradient f) 0 ![T.symm u, T.symm v] := by
    rw [hg, T.iteratedFDeriv_comp_left, iteratedFDeriv_equiv_comp_right]
    change T.symm (T ((iteratedFDeriv ℝ 2 (gradient f) (T.symm 0))
      (fun i : Fin 2 => T.symm (![u, v] i)))) = _
    rw [T.symm_apply_apply, map_zero]
    congr 1
    funext i
    fin_cases i <;> rfl
  change ⟪T.symm (((fderiv ℝ (fderiv ℝ g)) 0 u) v), T.symm w⟫ = _
  calc
    _ = ⟪T.symm (iteratedFDeriv ℝ 2 g 0 ![u, v]), T.symm w⟫ := by
      simp [iteratedFDeriv_succ_apply_right, Fin.init]
    _ = ⟪iteratedFDeriv ℝ 2 (gradient f) 0 ![T.symm u, T.symm v], T.symm w⟫ := by
      rw [htransport]
    _ = _ := by
      rw [← gradient_second_derivative_inner]
      simp [iteratedFDeriv_succ_apply_right, Fin.init]
      rfl

end
end chebyshev1.Perturbations
