import krylov.Functions.ValueCentreMethod

/-!
Article: main_krylov, thm:Fplanar, genuine native attaining value method.
Use: execute the actual original one-correction centre on all sufficiently
small full-reference scalar cubics and obtain the sharp budget-dependent
uniform gradient coefficient. Search domains, trajectories and observations
are derived from the primitive scalar source, not method-class fields.
Source: actual causal scalar replay and exact endpoint-only centre transport.
-/
namespace krylov.Functions
noncomputable section
open krylov.Methods krylov.Reference krylov.Tensor krylov.Nonlinear krylov.Correction krylov.Tensor.BinaryCubic
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The true original value-method output on a constructed source is its
own final retained-span rule applied to the genuinely proved reference
history and genuinely observed endpoint data. Article: thm:Fplanar. -/
theorem OneCorrectionValueMethod.output_reference
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (t : krylov.Tensor.BinaryCubic) (R : ℝ) (hH : ReferencePlanePositiveBall A hA g t R)
    (hnodes : ∀ i≤referenceAtomCount A hA g, ‖referencePlaneNode A g i‖≤R)
    (M : OneCorrectionValueMethod (EuclideanSpace ℝ (Fin n)) (referenceAtomCount A hA g)) :
    M.output (by omega) (metricCoordinates A hA) (referencePlaneCubicObjective A hA g t) R 0=
      observedSpanFinalPolicy (by omega) M.coefficients
        (methodRun M.gradientPolicy (fun _=>cgOperator A) (fun _=>cgOperator A) g (referenceAtomCount A hA g-1))
        (functionSearchTranscript (referencePlaneCubicObjective A hA g t)
          (CG.displacement (cgOperator A) g) (referenceStep (cgOperator A) g) (referenceAtomCount A hA g)) := by
  unfold OneCorrectionValueMethod.output scalarValueFinalOutput
  rw [referencePlaneCubic_scalar_prefix A hA g hN t R hH hnodes M.gradientPolicy M.consistent _ le_rfl,
    referencePlaneCubic_value_transcript A hA g hN t R hH hnodes M.gradientPolicy M.consistent]

set_option maxHeartbeats 800000 in
/-- The admitted original data-only method attains the sharp full-space
value-information coefficient for every sufficiently small actual source,
uniformly over the full genuine tensor ball and with an explicit fourth
order remainder. The known tensor budget appears quadratically, exactly
as printed in the article. Article: main_krylov, thm:Fplanar. -/
theorem nativeCentreValueMethod_gradient_upper
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin n)) (hN : 2≤referenceAtomCount A hA g)
    (B : ℝ) (hB : 0<B) :
    ∃ R ep C : ℝ, 0<R ∧ 0<ep ∧ 0<C ∧
      ∀ (ε : ℝ) (hε : 0<ε), ε<ep → ∀ t : krylov.Tensor.BinaryCubic, t.InBall →
      let p := ε*‖canonicalCGStep A g 0‖
      let r := referencePlaneRatio A hA g
      let f := referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic B t)
      let M := budgetedCentreValueMethod (metricCoordinates A hA) B
        (show 0<referenceAtomCount A hA (ε • g) by rw [referenceAtomCount_scalar A hA g ε hε.ne']; omega)
      ‖(metricCoordinates A hA).symm (gradient f (M.output (by
        rw [referenceAtomCount_scalar A hA g ε hε.ne']; omega) (metricCoordinates A hA) f R 0))‖≤
        B^2*(r^2/4*Real.sqrt (1+4*r^2)*fibreMinimax r)*p^3+C*p^4 := by
  obtain ⟨R,ep,hR,hep,hdom⟩ := referencePlane_small_source_domain A hA g hN B hB
  obtain ⟨C,hC,hupper⟩ := budgetedPlaneCentreOutput_gradient_upper B (referencePlaneRatio A hA g) hB
  let p₀ := ‖canonicalCGStep A g 0‖
  have hp₀ : 0<p₀ := (referencePlane_sample_lines A hA g hN).1
  have hd : 0<B*p₀+1 := add_pos (mul_pos hB hp₀) zero_lt_one
  refine ⟨R,min ep (1/(B*p₀+1)),C,hR,lt_min hep (div_pos zero_lt_one hd),hC,?_⟩
  intro ε hε heps t ht
  dsimp only
  have hNε : 2≤referenceAtomCount A hA (ε • g) := by rwa [referenceAtomCount_scalar A hA g ε hε.ne']
  have hp : 0<ε*p₀ := mul_pos hε hp₀
  have hps : B*(ε*p₀)≤1 := by
    have hh := (lt_div_iff₀ hd).mp (heps.trans_le (min_le_right _ _))
    nlinarith only [hh,hε]
  have hD := hdom ε hε (heps.trans_le (min_le_left _ _)) B hB.le le_rfl t ht
  rw [OneCorrectionValueMethod.output_reference A hA (ε • g) hNε (scaleBinaryCubic B t) R hD.1 hD.2]
  change ‖(metricCoordinates A hA).symm (gradient (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic B t))
    (metricPlaneResponseFinalPolicy (budgetedPlaneCentreOutput B) (metricCoordinates A hA) (by omega)
      (methodRun (fcMethod fullMemory) (fun _=>cgOperator A) (fun _=>cgOperator A) (ε • g) (referenceAtomCount A hA (ε • g)-1))
      (functionSearchTranscript (referencePlaneCubicObjective A hA (ε • g) (scaleBinaryCubic B t))
        (CG.displacement (cgOperator A) (ε • g)) (referenceStep (cgOperator A) (ε • g)) (referenceAtomCount A hA (ε • g)))))‖≤_
  apply (referencePlaneCubic_response_gradient_le (budgetedPlaneCentreOutput B) A hA (ε • g) hNε (scaleBinaryCubic B t) _).trans
  rw [referencePlaneFirstLength_scalar A hA g hε,referencePlaneRatio_scalar A hA g hε]
  exact hupper (ε*p₀) hp hps t ht

end
end krylov.Functions
