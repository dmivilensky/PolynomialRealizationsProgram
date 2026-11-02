import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
Article: main_krylov, thm:value, construction underlying the principal measure.
Use: construct a genuine scalar spectral measure of a bounded selfadjoint
Hilbert-space operator from its actual continuous functional calculus.
The measure is produced by Riesz–Markov, rather than supplied with spectral
identities as certificate fields. Identifying the string's actual Neumann
resolvent remains a separate operator-construction step.
Source: mathlib CFC and the Riesz–Markov–Kakutani representation theorem.
-/

namespace krylov.Strings.Spectral
noncomputable section
open Set Filter MeasureTheory
open scoped Topology CompactlySupported ContinuousFunctionalCalculus

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The actual scalar CFC functional associated to one Hilbert vector. -/
def scalarCFC (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℝ T, ℝ)) : ℝ :=
  (inner ℂ v ((cfcHom hT f) v)).re

/-- Positivity of the scalar CFC functional is obtained by taking a genuine
continuous square root of a nonnegative function on the actual spectrum. -/
theorem scalarCFC_nonneg (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℝ T, ℝ)) (hf : ∀ x, 0 ≤ f x) : 0 ≤ scalarCFC T hT v f := by
  let g : C(spectrum ℝ T, ℝ) := ⟨fun x => Real.sqrt (f x), Real.continuous_sqrt.comp f.continuous⟩
  have hgf : g * g = f := by
    ext x
    exact Real.mul_self_sqrt (hf x)
  let S : E →L[ℂ] E := cfcHom hT g
  have hS : IsSelfAdjoint S := cfcHom_predicate hT g
  have hSS : cfcHom hT f = S.adjoint ∘L S := by
    rw [← hgf, map_mul]
    change S * S = _
    have hs : S.adjoint = S := hS.star_eq
    rw [hs]
    rfl
  change 0 ≤ (inner ℂ v ((cfcHom hT f) v)).re
  rw [hSS]
  exact (ContinuousLinearMap.isPositive_adjoint_comp_self S).re_inner_nonneg_right v

/-- The positive real functional on continuous compactly supported functions
used in the actual Riesz–Markov measure construction. -/
def scalarFunctional (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    C_c(spectrum ℝ T, ℝ) →ₚ[ℝ] ℝ where
  toFun f := scalarCFC T hT v f.toContinuousMap
  map_add' f g := by
    change scalarCFC T hT v (f.toContinuousMap + g.toContinuousMap) = _
    simp only [scalarCFC, map_add, add_apply, inner_add_right, Complex.add_re]
  map_smul' r f := by
    change scalarCFC T hT v (r • f.toContinuousMap) = _
    simp only [scalarCFC, map_smul, smul_apply]
    rw [← algebraMap_smul ℂ r]
    change (inner ℂ v ((r : ℂ) • ((cfcHom hT f.toContinuousMap) v))).re =
      r * (inner ℂ v ((cfcHom hT f.toContinuousMap) v)).re
    rw [inner_smul_right]
    simp
  monotone' f g hfg := by
    have hpos := scalarCFC_nonneg T hT v (g.toContinuousMap - f.toContinuousMap)
      (fun x => sub_nonneg.2 (hfg x))
    simp only [scalarCFC, map_sub, sub_apply, inner_sub_right, Complex.sub_re] at hpos
    exact sub_nonneg.1 hpos

/-- The genuine scalar spectral measure, on the actual compact spectrum. -/
def scalarMeasure (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) : Measure (spectrum ℝ T) :=
  RealRMK.rieszMeasure (scalarFunctional T hT v)

instance scalarMeasure_isFinite (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    IsFiniteMeasure (scalarMeasure T hT v) := by
  dsimp [scalarMeasure]
  infer_instance

instance scalarMeasure_regular (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    (scalarMeasure T hT v).Regular := by
  dsimp [scalarMeasure]
  infer_instance

/-- The constructed measure represents the actual scalar CFC on every
continuous function of the spectrum, not only on polynomials. -/
theorem scalarMeasure_integral (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℝ T, ℝ)) :
    (∫ x, f x ∂scalarMeasure T hT v) = scalarCFC T hT v f := by
  let g : C_c(spectrum ℝ T, ℝ) := ⟨f, HasCompactSupport.of_compactSpace _⟩
  exact RealRMK.integral_rieszMeasure (scalarFunctional T hT v) g

/-- The total scalar spectral mass is the true squared Hilbert norm of the
distinguished vector. -/
theorem scalarMeasure_univ (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E) :
    scalarMeasure T hT v univ = ENNReal.ofReal (‖v‖ ^ 2) := by
  have he := scalarMeasure_integral T hT v (1 : C(spectrum ℝ T, ℝ))
  simp only [ContinuousMap.one_apply, scalarCFC, map_one, one_apply_eq_self,
    integral_const, smul_eq_mul, mul_one] at he
  change (scalarMeasure T hT v).real univ = RCLike.re (inner ℂ v v) at he
  rw [inner_self_eq_norm_sq] at he
  calc
    scalarMeasure T hT v univ = ENNReal.ofReal ((scalarMeasure T hT v).real univ) :=
      (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
    _ = _ := congrArg ENNReal.ofReal he

/-- A unit boundary vector gives an actual probability spectral measure. -/
theorem scalarMeasure_probability (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) {v : E}
    (hv : ‖v‖ = 1) : IsProbabilityMeasure (scalarMeasure T hT v) := by
  refine ⟨?_⟩
  simp [scalarMeasure_univ, hv]

end
end krylov.Strings.Spectral
