import krylov.Stability.ObservedProjection
import krylov.Methods.CanonicalWindows
set_option autoImplicit false
/-!
Article: main_krylov, apH:dcs2(a), the genuine inverse-Gram residual norm.
Use: identify the printed physical window residual with its actual canonical
orthogonal projection, for arbitrary independent physical window columns.
Source: the proved real observed-projection inverse-Gram formula and actual
positive-root primal/dual pairing; no metric identification is assumed.
-/

namespace krylov.Cancellation
noncomputable section
open Matrix krylov.Methods krylov.Stability krylov.Secant
open scoped InnerProductSpace BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {n p : ℕ}

/-- The actual old-span projection norm is exactly its observed coordinates'
inverse-Gram quadratic norm.
Use: bridge true orthogonal projections to the printed window residual metric.
Article: main_krylov, apH:dcs2(a), inverse-Gram projection identity.
Proof: the true projection error is orthogonal to the projected vector. Insert
the proved inverse-Gram synthesis into the remaining genuine physical pairing. -/
theorem observed_projection_norm_sq (s : Fin p → E) (hu : IsUnit (crossGram s s).det) (v : E) :
    ‖observedProjection s v‖^2=coordinates s v ⬝ᵥ ((crossGram s s)⁻¹ *ᵥ coordinates s v) := by
  let K := Submodule.span ℝ (Set.range s)
  have ho := K.starProjection_inner_eq_zero v (K.starProjection v) (K.starProjection_apply_mem v)
  rw [inner_sub_left] at ho
  have hp : inner ℝ (observedProjection s v) v=‖observedProjection s v‖^2 := by
    rw [real_inner_comm]
    change inner ℝ v (K.starProjection v)=‖K.starProjection v‖^2
    rw [sub_eq_zero.mp ho,real_inner_self_eq_norm_sq]
  rw [← hp,observedProjection_apply s hu,combine_inner_coordinates]
  simp only [projectedResidual,EuclideanSpace.inner_toLp_toLp,star_trivial]

/-- The true physical old-window residual norm, measured in the reference
energy metric through its actual canonical orthogonal projection.
Use: the printed inverse-Gram norm has a direct geometric definition.
Article: main_krylov, apH:dcs2(a), norm of S transpose g in inverse G_A. -/
def windowMetricResidual (base : Matrix (Fin n) (Fin n) ℝ)
    (s : Fin p → EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ‖observedProjection (primalWindow base s) (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ v)‖

/-- The geometrically defined physical window residual equals exactly the
article's inverse-energy-Gram norm of the real physical pairings.
Use: source lower and upper fresh bounds concern the literal original metric.
Article: main_krylov, apH:dcs2(a), G_A equals the true energy Gram.
Proof: the genuine canonical projection formula supplies its actual Gram;
the proved positive-root pairing identifies its coordinates with S transpose g. -/
theorem window_metric_residual_formula (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s : Fin p → EuclideanSpace ℝ (Fin n))
    (hu : IsUnit (crossGram (primalWindow base s) (primalWindow base s)).det)
    (v : EuclideanSpace ℝ (Fin n)) :
    windowMetricResidual base s v=
      Real.sqrt (coordinates s v ⬝ᵥ ((crossGram (primalWindow base s) (primalWindow base s))⁻¹ *ᵥ coordinates s v)) := by
  have he := observed_projection_norm_sq (primalWindow base s) hu
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ v)
  rw [canonical_window_coordinates base hb] at he
  rw [← he,Real.sqrt_sq (norm_nonneg _)]
  rfl

end
end krylov.Cancellation
