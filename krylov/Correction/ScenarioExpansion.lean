import krylov.Correction.CanonicalBounds
import krylov.Envelope.ScenarioCoordinates

/-!
Article: main_krylov, thm:C, the complete finite symmetric scenario space.
Use: specialize the actual canonical cubic expansion to all original finite
increment/correction variables at once, rather than only to individual paths.
Source: reuse the genuine finite canonical scenario, its true zero extension
and the inherited norm on the closed real subspace of symmetric matrix arrays.
-/

namespace krylov.Correction
noncomputable section
open Matrix Filter Asymptotics Topology krylov.Reference krylov.Variation krylov.Envelope
  krylov.Methods krylov.Secant krylov.Stability
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The real linear space of the original finite symmetric canonical scenarios.
Use: primitive parameters remain precisely the actual symmetric source increments and independent correction perturbations.
Article: main_krylov, thm:C, the full finite symmetric scenario variables. -/
def symmetricScenarios (n N : ℕ) : Submodule ℝ (CanonicalScenario n N) where
  carrier := {Θ | (∀ i, (Θ.1 i).IsSymm) ∧ ∀ i, (Θ.2 i).IsSymm}
  zero_mem' := ⟨fun _ => Matrix.isSymm_zero,fun _ => Matrix.isSymm_zero⟩
  add_mem' := by
    intro x y hx hy
    constructor
    · intro i
      change (x.1 i+y.1 i)ᵀ=x.1 i+y.1 i
      rw [transpose_add,(hx.1 i).eq,(hy.1 i).eq]
    · intro i
      change (x.2 i+y.2 i)ᵀ=x.2 i+y.2 i
      rw [transpose_add,(hx.2 i).eq,(hy.2 i).eq]
  smul_mem' := by
    intro c x hx
    constructor
    · intro i
      change (c • x.1 i)ᵀ=c • x.1 i
      rw [transpose_smul,(hx.1 i).eq]
    · intro i
      change (c • x.2 i)ᵀ=c • x.2 i
      rw [transpose_smul,(hx.2 i).eq]

/-- Every actual finite increment coordinate on the true symmetric scenario space is analytic.
Use: discharge primitive analyticity from the original source variables themselves.
Article: main_krylov, thm:C, finite parameter regularity.
Proof: a real finite coordinate is a continuous linear projection of the
actual subspace inclusion; outside the source horizon the true extension is zero. -/
theorem symmetricScenario_increment_analytic (k : ℕ) :
    AnalyticAt ℝ (fun Θ : symmetricScenarios n N =>
      matrixSequenceExtension (N-1) Θ.val.1 k) 0 := by
  by_cases hk : k<N-1
  · simp only [matrixSequenceExtension,dite_eq_left hk]
    exact ((ContinuousLinearMap.proj (⟨k,hk⟩ : Fin (N-1))) ∘L
      (ContinuousLinearMap.fst ℝ _ _) ∘L (symmetricScenarios n N).subtypeL).analyticAt _
  · simp only [matrixSequenceExtension,dite_eq_right hk]
    exact analyticAt_const

/-- Every actual finite independent correction coordinate on the symmetric source space is analytic.
Use: allow all intermediate correction defects and the true final output defect to vary independently.
Article: main_krylov, thm:C, finite correction parameter regularity.
Proof: compose the actual subspace inclusion with the true second-array
coordinate projection, retaining the genuine zero default outside its horizon. -/
theorem symmetricScenario_correction_analytic (k : ℕ) :
    AnalyticAt ℝ (fun Θ : symmetricScenarios n N =>
      matrixSequenceExtension N Θ.val.2 k) 0 := by
  by_cases hk : k<N
  · simp only [matrixSequenceExtension,dite_eq_left hk]
    exact ((ContinuousLinearMap.proj (⟨k,hk⟩ : Fin N)) ∘L
      (ContinuousLinearMap.snd ℝ _ _) ∘L (symmetricScenarios n N).subtypeL).analyticAt _
  · simp only [matrixSequenceExtension,dite_eq_right hk]
    exact analyticAt_const

/-- The actual extended probe increment of every original symmetric finite scenario is symmetric.
Use: no global symmetry assumption on a fictitious perturbation chart is needed.
Article: main_krylov, thm:C, symmetric source query operators.
Proof: use the true coordinate symmetry or the genuine zero matrix outside its horizon. -/
theorem symmetricScenario_increment_symm (Θ : symmetricScenarios n N) (k : ℕ) :
    (matrixSequenceExtension (N-1) Θ.val.1 k).IsSymm := by
  by_cases hk : k<N-1
  · simp only [matrixSequenceExtension,dite_eq_left hk]
    exact Θ.property.1 ⟨k,hk⟩
  · simp only [matrixSequenceExtension,dite_eq_right hk]
    exact Matrix.isSymm_zero

/-- The genuine full RFC expansion has a cubic remainder in the norm of all original finite symmetric scenario variables jointly.
Use: one local bound covers every sufficiently small source budget profile,
including degenerate profiles and all independent intermediate corrections.
Article: main_krylov, thm:C, full finite-scenario cubic remainder at a fixed reference.
Proof: the true symmetric finite scenario is a real normed parameter space.
Its original increment and correction coordinates are analytic continuous
linear projections, with genuine zero reference values and derived probe
symmetry. Apply the actual canonical expansion in precisely this full space. -/
theorem scenario_second_order {k : ℕ}
    (base : Matrix (Fin (k+1)) (Fin (k+1)) ℝ) (hb : base.PosDef)
    (g : EuclideanSpace ℝ (Fin (k+1)))
    (hN : k+1≤referenceAtomCount base hb g) (hk : 0<k) :
    (fun Θ : symmetricScenarios (k+1) (k+1) =>
      cgOperator (metricRoot base)⁻¹
        (probedGradient (rfcMethod fullMemory 1) (scenarioProbe base Θ.val)
          (scenarioCorrection base Θ.val) g (k+1))+
      ‖canonicalCGStep base g k‖ • staircaseOperator base g
        (matrixSequenceExtension k Θ.val.1) (matrixSequenceExtension (k+1) Θ.val.2 k) (k+1)
        (freshDefect base g (matrixSequenceExtension k Θ.val.1) (k+1))) =O[𝓝 0]
          (fun Θ => ‖Θ‖^3) := by
  -- The actual source arrays, including zero-budget coordinates, are the parameters of this joint estimate.
  apply full_canonical_second_order base hb g hN hk
    (fun Θ : symmetricScenarios (k+1) (k+1) => matrixSequenceExtension k Θ.val.1)
    (fun Θ => matrixSequenceExtension (k+1) Θ.val.2)
  · intro i
    by_cases hi : i<k
    · simp only [matrixSequenceExtension,dite_eq_left hi]
      exact ((ContinuousLinearMap.proj (⟨i,hi⟩ : Fin k)) ∘L
        (ContinuousLinearMap.fst ℝ _ _) ∘L (symmetricScenarios (k+1) (k+1)).subtypeL).analyticAt _
    · simp only [matrixSequenceExtension,dite_eq_right hi]
      exact analyticAt_const
  · exact symmetricScenario_correction_analytic
  · intro i
    exact matrixSequenceExtension_zero k i
  · intro i
    exact matrixSequenceExtension_zero (k+1) i
  · intro Θ i
    by_cases hi : i<k
    · simp only [matrixSequenceExtension,dite_eq_left hi]
      exact Θ.property.1 ⟨i,hi⟩
    · simp only [matrixSequenceExtension,dite_eq_right hi]
      exact Matrix.isSymm_zero

end
end krylov.Correction
