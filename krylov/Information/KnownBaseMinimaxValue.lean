import krylov.Information.KnownBaseMidpointUpper
import krylov.Information.ChangedModelExecution
import krylov.Information.KnownBaseLower
import krylov.Information.MinimaxBound

/-!
Article: main_krylov, thm:C2(c), genuine known-base minimax risk.
Use: the real finite-history informed algorithm attains the sharp source
infimum of true physical scenario suprema, with derived finiteness and a
common cubic remainder including zero budgets.
Source: genuine fixed-base signed physical lower witnesses, actual informed
all-scenario upper and complete-lattice comparisons for the true method class.
-/

namespace krylov.Information
noncomputable section
open Matrix Filter Asymptotics Topology Finset krylov.Reference krylov.Secant krylov.Envelope
  krylov.Correction krylov.Methods krylov.LinearAlgebra krylov.Stability krylov.Variation
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
variable {n N : ℕ}

/-- The genuine worst normalized output over the original known-base single-first-increment spectral source class.
Use: retain the true physical oracles, zero terminal and intermediate defects and actual available prior.
Article: main_krylov, thm:C2(c), true known-base source supremum. -/
def knownBaseWorstOutputRatio (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (N : ℕ) (ω : ℝ) : ENNReal :=
  ⨆ S : {S : Scenario n // S.Admissible N A 0 (firstBudget ω) 0 0 ∧ S.base=A},
    ENNReal.ofReal (S.val.outputRatio m g N)

/-- The actual known-base minimax risk over all genuine CG-consistent span-restricted one-correction source policies.
Use: compare the concrete informed algorithm against the full nonanticipating method class.
Article: main_krylov, thm:C2(c), genuine known-base infimum–supremum. -/
def knownBaseMinimax (A : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n))
    (N : ℕ) (ω : ℝ) : ENNReal :=
  ⨅ M : OneCorrectionCGStrategy (EuclideanSpace ℝ (Fin n)), knownBaseWorstOutputRatio M.method.policy A g N ω

/-- Every genuine source policy has the sharp informed coefficient in its actual known-base worst physical output, with explicit cubic loss.
Use: the original admissible signed witnesses force the lower bound without any competing-policy smoothness or bounded-risk premise.
Article: main_krylov, thm:C2(c), actual all-method known-base supremum lower bound.
Proof: both actual known-base signed scenarios belong to the true source
supremum and their genuine terminal output maximum forces the sharp radius. -/
theorem knownBaseWorst_sharp_lower
    (A : Matrix (Fin (N+1)) (Fin (N+1)) ℝ) (hA : A.PosDef)
    (g : EuclideanSpace ℝ (Fin (N+1))) (hN : 0<N) (hcount : referenceAtomCount A hA g=N+1)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin (N+1)))) (hm : CGConsistent m) (h1 : OneCorrectionMethod m)
    (ω : ℝ) (hω : 0≤ω) (hsmall : ω≤(1/2 : ℝ)) :
    ENNReal.ofReal ((2/(3*Real.sqrt 3))*ω^2-2*ω^3)≤knownBaseWorstOutputRatio m A g N ω := by
  -- Both original physically admissible witnesses occur in the actual source supremum.
  obtain ⟨hBp,hBm,hp,hn,hl⟩ := admissible_known_base_normalized_lower A hA g hN hcount m hm h1
    ω 0 0 hω le_rfl le_rfl hsmall
  apply (ENNReal.ofReal_le_ofReal hl).trans
  rw [ENNReal.ofReal_max]
  unfold knownBaseWorstOutputRatio
  apply max_le
  · exact le_iSup_of_le (⟨_,hp,hBp⟩ : {S : Scenario (N+1) //
      S.Admissible N A 0 (firstBudget ω) 0 0 ∧ S.base=A}) le_rfl
  · exact le_iSup_of_le (⟨_,hn,hBm⟩ : {S : Scenario (N+1) //
      S.Admissible N A 0 (firstBudget ω) 0 0 ∧ S.base=A}) le_rfl



end
end krylov.Information
