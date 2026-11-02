import krylov.Information.PreQuadraticInstance
import krylov.Information.PlanarLowerFibre

/-!
Article: main_krylov, s4:cor-Q, actual inner-subclass sharp witnesses.
Use: place the genuine signed physical lower scenarios in the original
pre-quadratic inner source class with only a uniform cubic loss.
Source: actual terminal-fibre CG probe geometry, original scaled physical
admissibility and proved sharp-coefficient homogeneity.
-/

namespace krylov.Information
noncomputable section
open Matrix Finset krylov.Reference krylov.Methods krylov.Secant krylov.Correction krylov.Stability krylov.LinearAlgebra
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator MatrixOrder
variable {N : ℕ}

/-- Every actual signed physical planar lower scenario belongs to the original pre-quadratic source class.
Use: Place the genuine attaining witnesses in the original inner subclass.
Article: main_krylov, s4:cor-Q, original instance-optimality and inner attainment.
Proof: The real probe formula is the proved physical terminal-fibre segment. True full CG orthonormality makes each of its actual preterminal reference-direction actions equal the original quadratic reference. -/
theorem physical_planarLowerScenario_preQuadratic
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1)
    (ω : ℕ → ℝ) (w a γ σ : ℝ) :
    ((planarLowerScenario (canonicalCGUnitStep A g 0) (canonicalCGUnitStep A g N)
      ω w N a γ σ).inPhysical (metricRoot A)⁻¹).PreQuadratic (cgOperator A) g N := by
  -- Keep the actual common source slack and its original physical radius margin.
  let W := ∑ i∈range N, ω i
  let t := 1-W
  have hp := terminal_reference_prefix_probes A hA g N hN (canonicalCG_frame_of_full_atoms A hA g hcount)
    (fun i => t*ω i*a) (fun i => t*ω i*(σ*γ)) (fun i => t*ω i*(-(σ*γ)))
  intro k hk
  change cgOperator (((planarLowerScenario _ _ ω w N a γ σ).inPhysical (metricRoot A)⁻¹).probe k) _=_
  rw [physical_planarLowerScenario_probe A hA]
  exact hp k hk

/-- Admissibility with the printed common scaled budgets and reduced base radius implies the original physical inner source class.
Use: Verify all original inner-class fields for the actual scaled attaining scenarios.
Article: main_krylov, s4:cor-Q, inner-class sharp attainment.
Proof: The common slack factor is at most one and the reduced radius is at most the original radius. Thus every scaled individual budget implies its original admissibility bound, while the actual same constraints give precisely the required inner margins. -/
theorem Scenario.naturalInner_of_scaled_admissible (S : Scenario (N+1))
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (r w τ : ℝ) (ω : ℕ → ℝ)
    (hr : 0≤r) (hw : 0≤w) (hω : ∀ i<N, 0≤ω i)
    (hS : S.Admissible N A (r-4*(1+r)*(∑ i∈range N, ω i))
      (fun i => (1-4*((N : ℝ)+1)*(∑ j∈range N, ω j))*ω i)
      ((1-4*((N : ℝ)+1)*(∑ j∈range N, ω j))*w) τ) :
    S.NaturalInner A r ω w τ := by
  -- The same scaled actual budgets give the inner margins and imply the original larger budgets.
  let W := ∑ i∈range N, ω i
  let θ := 1-4*((N : ℝ)+1)*W
  have hW : 0≤W := sum_nonneg fun i hi => hω i (mem_range.mp hi)
  have hθ : θ≤1 := by dsimp only [θ]; nlinarith
  have hm : r-4*(1+r)*W≤r := by nlinarith
  refine ⟨?_,fun i hi => (hS.2.2.1 i hi).2,hS.2.2.2.2.1,hS.2.1⟩
  refine ⟨hS.1,hS.2.1.trans hm,?_,hS.2.2.2.1,?_,hS.2.2.2.2.2⟩
  · intro i hi
    refine ⟨(hS.2.2.1 i hi).1,?_⟩
    exact (hS.2.2.1 i hi).2.trans ((mul_le_mul_of_nonneg_right hθ (hω i hi)).trans_eq (one_mul _))
  · exact hS.2.2.2.2.1.trans ((mul_le_mul_of_nonneg_right hθ hw).trans_eq (one_mul _))

end
end krylov.Information
