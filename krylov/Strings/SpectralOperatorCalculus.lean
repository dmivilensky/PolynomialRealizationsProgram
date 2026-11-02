import krylov.Strings.SpectralScalar

/-!
Article: main_krylov, apC:prop:tauber, resolvent functional calculus.
Use: expose the actual operator CFC on generic complex Hilbert spaces
before specializing to concrete L² spaces. This also keeps the real-scalar
restriction coherent with the complex Hilbert-space structure.
Source: mathlib continuous functional calculus for self-adjoint operators.
-/

namespace krylov.Strings.Spectral
noncomputable section
open scoped ContinuousFunctionalCalculus
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The genuine real operator calculus on the actual self-adjoint spectrum. -/
def operatorCalculus (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    C(spectrum ℝ T, ℝ) →⋆ₐ[ℝ] (E →L[ℂ] E) := cfcHom hT

/-- The actual spectral coordinate maps back to its original operator. -/
theorem operatorCalculus_id (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) :
    operatorCalculus T hT ((ContinuousMap.id ℝ).restrict (spectrum ℝ T)) = T := cfcHom_id hT

/-- The constructed scalar measure represents this same actual operator
calculus, with the scalar restriction fixed on the generic Hilbert space. -/
theorem integral_operatorCalculus (T : E →L[ℂ] E) (hT : IsSelfAdjoint T) (v : E)
    (f : C(spectrum ℝ T, ℝ)) :
    (∫ r, f r ∂scalarMeasure T hT v) = (inner ℂ v ((operatorCalculus T hT f) v)).re :=
  scalarMeasure_integral T hT v f

end
end krylov.Strings.Spectral
