import krylov.Envelope.SelectionZeroLastWitness
import krylov.Envelope.OldPerpendicularUnit
import krylov.Envelope.FreshCrossWitness
import krylov.Envelope.CorrectionFreeFreshScenario
import krylov.Envelope.SelectionBoundary

set_option autoImplicit false
/-!
Article: main_krylov, s3:thm:cf, actual correction-free excess scenario.
Use: construct a genuine feasible scenario attaining the Pythagorean excess lower bound for every actual correction-free smooth source method.
Source: actual zero-last-budget selection attainment, the concrete symmetric planar increment and the exact executed final singleton response.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Secant krylov.Variation krylov.LinearAlgebra Matrix Set
open scoped Matrix.Norms.L2Operator NNReal
variable {n : ℕ}

/-- Every actual correction-free smooth method has a feasible scenario realizing the printed square-root excess value.
Use: Every actual correction-free smooth method has a feasible scenario realizing the printed square-root excess value.
Article: main_krylov, s3:thm:cf, actual correction-free excess scenario.
Proof: Reserve the final budget in a genuine selection witness, add an orthogonal old-direction cross increment, and apply actual response linearity and Pythagoras. -/
theorem correctionFree_excess_witness (M : SmoothProbedClass (EuclideanSpace ℝ (Fin n)))
    (hfree : Methods.CorrectionFree M.policy)
    (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef) (g : EuclideanSpace ℝ (Fin n))
    (k : ℕ) (hcount : k+2≤referenceAtomCount base hb g) (ω : Fin ((k+2)-1) → ℝ≥0) :
    ∃ Θ∈scenarioBudget (k+2) ω,
      ‖scenarioVariation M.policy base g (k+2) Θ‖=
        Real.sqrt ((selectionValue base g (k+2) ω)^2+
          cgEnergy base g (k+1)*(ω ⟨k,by omega⟩ : ℝ)^2) := by
  classical
  -- Reserve the whole final budget while keeping the genuine attained selection value.
  let l : Fin ((k+2)-1) := ⟨k,by omega⟩
  let w : ℝ := ω l
  let V := selectionValue base g (k+2) ω
  obtain ⟨Θ0,hΘ0,hzero,hν⟩ := selection_zero_last_witness M base hb g (k+2) (by omega) hcount ω
  have hz : Θ0.1 l=0 := by simpa only [show k+2-2=k by omega] using hzero
  let z := scenarioVariation M.policy base g (k+2) Θ0
  have htwo : k+2=2 → z=0 := by
    intro h
    have hk : k=0 := by omega
    subst k
    apply norm_eq_zero.mp
    exact hν.trans (selectionValue_two base hb g hcount ω)
  -- Choose a real old unit direction perpendicular to the attained variation; the two-step value is zero.
  obtain ⟨x,hx,hmem,hxz⟩ := old_flag_perpendicular_unit base hb g (k+2) (by omega) hcount z htwo
  have hmem' : x∈exploredFlag base g (k+1) := by
    simpa only [show k+2-1=k+1 by omega] using hmem
  let h := canonicalCGUnitStep base g (k+1)
  let D := w • planarMatrix x h 0 1 0
  have hw : 0≤w := (ω l).coe_nonneg
  have hdata : D.IsSymm ∧ ‖D‖≤w ∧ cgOperator D h=w • x ∧ inner ℝ h (cgOperator D h)=0 ∧
      cgOperator D h∈exploredFlag base g (k+2) :=
    fresh_cross_witness base hb g k hcount x hx hmem' w hw
  rcases hdata with ⟨hSym,hDn,hAct,hOrth,hMem⟩
  -- Exact affine execution on the last singleton identifies the actual method response, not an abstract response model.
  have hfresh : scenarioVariation M.policy base g (k+2) (Pi.single l D,0)=
      Real.sqrt (cgEnergy base g (k+1)) • (w • x) := by
    have hv := correctionFree_last_scenario_variation M hfree base hb g k hcount D hOrth hMem 0
    change scenarioVariation M.policy base g (k+2) (Pi.single l D,0)=
      Real.sqrt (cgEnergy base g (k+1)) • cgOperator D h at hv
    rw [hAct] at hv
    exact hv
  -- The baseline last increment is exactly zero, so adding the fresh witness respects every original budget.
  let Θ : CanonicalScenario n (k+2) := Θ0+(Pi.single l D,0)
  have hΘ : Θ∈scenarioBudget (k+2) ω := scenarioBudget_add_single_of_zero ω Θ0 hΘ0 l hz D hSym hDn
  have heq : scenarioVariation M.policy base g (k+2) Θ=z+Real.sqrt (cgEnergy base g (k+1)) • (w • x) := by
    exact ((scenarioVariation M.policy base g (k+2)).map_add Θ0 (Pi.single l D,0)).trans
      (congrArg (fun v => z+v) hfresh)
  have hzx : inner ℝ z x=0 := by rw [real_inner_comm];exact hxz
  have ho : inner ℝ z (Real.sqrt (cgEnergy base g (k+1)) • (w • x))=0 := by
    rw [real_inner_smul_right,real_inner_smul_right,hzx,mul_zero,mul_zero]
  have hc := cgEnergy_pos base hb g (k+1) (by omega)
  have hzn : ‖z‖=V := hν
  -- Orthogonality makes the true combined response have exactly the asserted Pythagorean norm.
  have hnorm : ‖scenarioVariation M.policy base g (k+2) Θ‖^2=V^2+cgEnergy base g (k+1)*w^2 := by
    rw [heq,norm_add_sq_real,ho,mul_zero,add_zero]
    simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,hx,mul_one,hzn,Real.sq_sqrt hc.le]
  refine ⟨Θ,hΘ,?_⟩
  rw [← hnorm,Real.sqrt_sq (norm_nonneg _)]
end
end krylov.Envelope
