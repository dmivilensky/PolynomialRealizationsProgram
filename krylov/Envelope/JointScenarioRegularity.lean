import krylov.Envelope.ScenarioCoordinates

set_option autoImplicit false
/-!
Article: main_krylov, thm:E and s3:cor:qn, genuine joint source-scenario regularity.
Use: vary actual quadratic references and true finite canonical scenarios
jointly when deriving the real compact-uniform output remainder.
Source: proved positive metric-root calculus and genuine finite
coordinate extension, prefix summation and operator congruence.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability Matrix Filter Topology
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n N : ℕ}

/-- The genuine finite canonical line and independent correction operators are jointly C-r in the actual varying positive reference and source scenario.
Use: The genuine finite canonical line and independent correction operators are jointly C-r in the actual varying positive reference and source scenario.
Article: main_krylov, thm:E and s3:cor:qn, genuine joint source-scenario regularity.
Proof: Each real finite coordinate or zero default is smooth; compose the actual positive metric roots with genuine cumulative increments and independent correction defects. -/
theorem jointScenarioPrimitive_regular (base : X → Matrix (Fin n) (Fin n) ℝ)
    (Θ : X → CanonicalScenario n N) (x : X) (r : WithTop ℕ∞)
    (hb : ContDiffAt ℝ r base x) (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hΘ : ContDiffAt ℝ r Θ x) (k : ℕ) :
    ContDiffAt ℝ r (fun p => scenarioProbe (base p) (Θ p) k) x ∧
      ContDiffAt ℝ r (fun p => scenarioCorrection (base p) (Θ p) k) x := by
  -- Keep the true finite source coordinates and the actual varying positive metric in the same primitive parameter chart.
  have hE (l : ℕ) : ContDiffAt ℝ r (fun p => matrixSequenceExtension (N-1) (Θ p).1 l) x := by
    by_cases hl : l<N-1
    · simp only [matrixSequenceExtension,dite_eq_left hl]
      exact contDiffAt_pi.mp hΘ.fst (⟨l,hl⟩ : Fin (N-1))
    · simp only [matrixSequenceExtension,dite_eq_right hl]
      exact contDiffAt_const
  have hF : ContDiffAt ℝ r (fun p => matrixSequenceExtension N (Θ p).2 k) x := by
    by_cases hk : k<N
    · simp only [matrixSequenceExtension,dite_eq_left hk]
      exact contDiffAt_pi.mp hΘ.snd (⟨k,hk⟩ : Fin N)
    · simp only [matrixSequenceExtension,dite_eq_right hk]
      exact contDiffAt_const
  have hA := canonicalFCPath_contDiffAt base (fun p => matrixSequenceExtension (N-1) (Θ p).1) x hb hpos hE k
  have hR := metricRoot_contDiffAt base x hb hpos
  exact ⟨hA,hA.add (matrixOperator_contDiffAt _ x ((hR.mul hF).mul hR))⟩
end
end krylov.Envelope
