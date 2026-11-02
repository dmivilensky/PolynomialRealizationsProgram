import krylov.Information.PlanarLowerFibre
import krylov.Information.PlanarRadius

/-!
Article: main_krylov, thm:C, genuine terminal outputs on the lower fibre.
Use: derive the exact common-query terminal residuals from the actual complete
nonanticipating execution with at most one correction per iteration.
Source: proved complete physical data equality, actual one-query execution
and exact physical/canonical lower-scenario operator identities.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Secant krylov.Reference krylov.LinearAlgebra krylov.Correction
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {n : ℕ}

/-- A genuinely at-most-one-query phase returns exactly the original gradient plus its actual first operator action.
Use: every common last decision in the source information class has one real correction vector, including the no-query case.
Article: main_krylov, thm:C, actual terminal correction output.
Proof: inspect the real correction tree. A stopped phase has zero movement;
a queried phase has an immediately stopping continuation on its actual answer. -/
theorem one_correction_gradient {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (q : krylov.Methods.CorrectionTree V) (hq : krylov.Methods.CorrectionsAtMostOne q)
    (B : V →L[ℝ] V) (g : V) :
    (krylov.Methods.runCorrections q B g).gradient=g+B (firstCorrectionStep q) := by
  cases q with
  | done => simp only [krylov.Methods.runCorrections,firstCorrectionStep,map_zero,add_zero]
  | query u next =>
    have hn := hq (g+B u)
    simp only [krylov.Methods.runCorrections,hn,firstCorrectionStep]

/-- The actual terminal operator of the signed lower scenario is the common cross mean plus its signed hidden diagonal.
Use: identify the exact matrices in the actual two-scenario output radius.
Article: main_krylov, thm:C, B^±=M±Δ.
Proof: the terminal hidden diagonal cancels in the actual last probe. The
true finite cross and old-diagonal sums have coefficients t a W and σ t γ W;
the independent terminal perturbation adds σ t w to the same old direction.
-/
theorem planarLowerScenario_output (e f : EuclideanSpace ℝ (Fin n)) (ω : ℕ → ℝ)
    (w : ℝ) (N : ℕ) (a γ σ : ℝ) :
    let W := ∑ i∈range N, ω i
    let t := 1-W
    (planarLowerScenario e f ω w N a γ σ).lastOperator N=
      (1+planarMatrix e f 0 (t*a*W) 0)+σ • planarMatrix e f (t*(γ*W+w)) 0 0 := by
  -- Only true finite source sums are combined, retaining the separate terminal perturbation.
  let W := ∑ i∈range N, ω i
  let t := 1-W
  have hsum (b : ℝ) : (∑ i∈range N, t*ω i*b)=t*b*W := by
    dsimp only [W]
    rw [mul_sum]
    exact sum_congr rfl fun i _ => by ring
  change (planarLowerScenario e f ω w N a γ σ).probe N+
    planarMatrix e f (σ*t*w) 0 0=_
  rw [planarLowerScenario_probe]
  change terminalSegments e f (fun i => t*ω i*a) (fun i => t*ω i*(σ*γ))
    (fun i => t*ω i*(-(σ*γ))) N N+planarMatrix e f (σ*t*w) 0 0=_
  simp only [terminalSegments,sub_self,hsum]
  simp only [planarMatrix,zero_smul,add_zero,zero_add,smul_add,smul_smul]
  module

/-- The true canonical inverse root transports every inverse-root-congruent physical action to the original canonical matrix action.
Use: normalize the real lower-scenario final query without assuming a model trajectory.
Article: main_krylov, thm:C, actual canonical terminal correction action.
Proof: identify the genuine inverse-root physical congruence and cancel its
left root against the actual inverse root, retaining the physical query's right root.
-/
theorem inverseRootForm_action (A M : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (u : EuclideanSpace ℝ (Fin n)) :
    cgOperator (metricRoot A)⁻¹ (cgOperator (inverseFormMap (metricRoot A)⁻¹ M) u)=
      cgOperator M (cgOperator (metricRoot A) u) := by
  rw [inverseRootForm A M hA]
  simp only [cgOperator,← mul_apply_eq_comp,← map_mul,← Matrix.mul_assoc,
    nonsing_inv_mul _ (metricRoot_det_unit A hA),Matrix.one_mul]

/-- The genuinely executed terminal outputs on the signed lower family have the exact common-correction normal form.
Use: apply an information radius to every actual globally CG-consistent method with at most one correction, without an assumed output formula.
Article: main_krylov, thm:C, actual common u and terminal residuals ρe+(M±Δ)u.
Proof: the constructed physical scenarios have the same complete actual
prefix and last probe. Nonanticipation therefore gives the same true first
correction query. The genuine one-query execution identity and the exact
physical terminal operator formula give the normalized output for both signs.
-/
theorem planarLowerScenario_terminal_form {N : ℕ}
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N)
    (hcount : referenceAtomCount A hA g=N+1)
    (m : krylov.Methods.ProbedMethod (EuclideanSpace ℝ (Fin (N+1))))
    (hm : krylov.Methods.CGConsistent m) (h1 : krylov.Methods.OneCorrectionMethod m)
    (ω : ℕ → ℝ) (w a γ : ℝ) :
    let e := canonicalCGUnitStep A g 0
    let f := canonicalCGUnitStep A g N
    let W := ∑ i∈range N, ω i
    let t := 1-W
    let ρ := t*a*W*Real.sqrt (cgEnergy A g N)
    let M := 1+planarMatrix e f 0 (t*a*W) 0
    let Δ := planarMatrix e f (t*(γ*W+w)) 0 0
    ∃ u : EuclideanSpace ℝ (Fin (N+1)), ∀ σ : ℝ,
      let S := (planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹
      cgOperator (metricRoot A)⁻¹
        (krylov.Methods.probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))=
          ρ • e+cgOperator (M+σ • Δ) u := by
  -- The actual complete observed data select one common query before its terminal answer.
  let e := canonicalCGUnitStep A g 0
  let f := canonicalCGUnitStep A g N
  let W := ∑ i∈range N, ω i
  let t := 1-W
  let H₀ := krylov.Methods.methodRun m (fun _ => cgOperator A) (fun _ => cgOperator A) g N
  obtain ⟨c,_,hd⟩ := physical_planarLowerScenario_data_fibre A hA g hN hcount m hm ω w a γ
  let z₀ := cgOperator (metricRoot A) (c • (f+(t*a*W) • e))
  let u₀ := firstCorrectionStep (m.correction H₀ z₀)
  refine ⟨cgOperator (metricRoot A) u₀,?_⟩
  intro σ
  let S := (planarLowerScenario e f ω w N a γ σ).inPhysical (metricRoot A)⁻¹
  have hdata := hd σ (S.correctionOracle N)
  have hH : krylov.Methods.methodRun m S.probeOracle (S.correctionOracle N) g N=H₀ := hdata.1
  have hz : S.probeOracle N (m.direction H₀)=z₀ := by
    have ht := hdata.2.1
    change S.probeOracle N (m.direction (krylov.Methods.methodRun m S.probeOracle (S.correctionOracle N) g N))=z₀ at ht
    rw [hH] at ht
    exact ht
  have hr : cgOperator (metricRoot A)⁻¹
      (searchedGradient H₀.gradient (m.direction H₀) (S.probeOracle N (m.direction H₀)))=
        (t*a*W*Real.sqrt (cgEnergy A g N)) • e := by
    have ht := hdata.2.2.2
    change cgOperator (metricRoot A)⁻¹
      (searchedGradient (krylov.Methods.methodRun m S.probeOracle (S.correctionOracle N) g N).gradient
        (m.direction (krylov.Methods.methodRun m S.probeOracle (S.correctionOracle N) g N))
        (S.probeOracle N (m.direction (krylov.Methods.methodRun m S.probeOracle (S.correctionOracle N) g N))))=
          (t*a*W*Real.sqrt (cgEnergy A g N)) • e at ht
    rw [hH] at ht
    exact ht
  have hgout : krylov.Methods.probedGradient m S.probeOracle (S.correctionOracle N) g (N+1)=
      searchedGradient H₀.gradient (m.direction H₀) z₀+cgOperator (S.lastOperator N) u₀ := by
    rw [krylov.Methods.probedGradient_succ]
    change (krylov.Methods.runCorrections _ _ _).gradient=_
    rw [one_correction_gradient _ (h1 _ _),hH,hz]
    simp only [Scenario.correctionOracle,ite_eq_right (by omega : ¬ N<N)]
    rfl
  change cgOperator (metricRoot A)⁻¹
    (krylov.Methods.probedGradient m S.probeOracle (S.correctionOracle N) g (N+1))=_
  rw [hgout,map_add]
  rw [hz] at hr
  rw [hr]
  congr 1
  change cgOperator (metricRoot A)⁻¹
    (cgOperator ((Scenario.mapForms _ (inverseFormMap (metricRoot A)⁻¹)).lastOperator N) u₀)=_
  rw [Scenario.mapForms_lastOperator,inverseRootForm_action A _ hA,planarLowerScenario_output]

end
end krylov.Information
