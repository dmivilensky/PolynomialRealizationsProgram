import krylov.Envelope.ScenarioVariation
import krylov.Methods.FiniteOracleCharts
set_option autoImplicit false
/-!
Article: main_krylov, thm:DC and lem:U, exact original source-budget transfer.
Use: transfer one proved actual finite-scenario output remainder to all
original infinite symmetric source matrix sequences with their true budgets.
Source: exact native prefix nonanticipation, actual zero correction slots
and genuine finite-product spectral norm inequalities.
-/

namespace krylov.Stability
noncomputable section
open Matrix Finset krylov.Methods krylov.Reference krylov.Secant krylov.Envelope krylov.Variation
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A genuine uniform finite-scenario remainder transfers to the original
infinite symmetric matrix sequence budget with the same actual executor.
Use: share the exact source dictionary between fixed and compact-reference
native theorems, rather than assuming a hypothetical budget response.
Article: main_krylov, thm:DC and lem:U, true finite-source budget dictionary.
Proof: the genuine finite source tuple has norm at most the summed original
budgets. The actual method histories agree exactly on the needed prefix;
zero independent correction slots give the same real correction operators.
The supplied response respects that same finite source prefix. -/
theorem finite_scenario_budget_transfer
    (base : Matrix (Fin n) (Fin n) ℝ) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (R : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (L : (ℕ → Matrix (Fin n) (Fin n) ℝ) → EuclideanSpace ℝ (Fin n))
    (hL : ∀ D E,(∀ l<k,D l=E l) → L D=L E)
    (delta C : ℝ) (hC : 0≤C)
    (hbound : ∀ Theta : CanonicalScenario n (k+1),‖Theta‖≤delta →
      (∀ l,(Theta.1 l).IsSymm) →
      ‖R (scenarioGradient m base g (k+1) Theta)-L (matrixSequenceExtension ((k+1)-1) Theta.1)‖≤C*‖Theta‖^2) :
    ∀ omega : ℕ → ℝ,(∀ l<k,0≤omega l) → (∑ l∈range k,omega l)≤delta →
      ∀ E : ℕ → Matrix (Fin n) (Fin n) ℝ,(∀ l,(E l).IsSymm) → (∀ l<k,‖E l‖≤omega l) →
      ‖R (probedGradient m (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1))-L E‖≤
        C*(∑ l∈range k,omega l)^2 := by
  intro omega homega hsmall E hE hbudget
  let W := ∑ l∈range k,omega l
  let Theta : CanonicalScenario n (k+1) := (fun l => E l.val,0)
  let D := matrixSequenceExtension ((k+1)-1) Theta.1
  have hW : 0≤W := sum_nonneg (fun l hl => homega l (mem_range.mp hl))
  have hnorm1 : ‖Theta.1‖≤W := by
    apply (pi_norm_le_iff_of_nonneg hW).mpr
    intro i
    have hi : i.val<k := by have := i.isLt;omega
    exact (hbudget i.val hi).trans (Finset.single_le_sum (fun j hj => homega j (mem_range.mp hj)) (mem_range.mpr hi))
  have hnorm2 : ‖Theta.2‖≤W := by
    change ‖(0 : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ)‖≤W
    simpa only [norm_zero] using hW
  have hnorm : ‖Theta‖≤W := norm_prod_le_iff.mpr ⟨hnorm1,hnorm2⟩
  have hD (l : ℕ) (hl : l<k) : D l=E l := by
    dsimp only [D,matrixSequenceExtension]
    rw [dite_eq_left (by omega : l<(k+1)-1)]
  have hresponse : L D=L E := by
    exact hL D E hD
  have hprobe (j : ℕ) (hj : j<k+1) : scenarioProbe base Theta j=canonicalFCPath base E 1 j := by
    have hsum : (∑ l∈range j,D l)=∑ l∈range j,E l :=
      sum_congr rfl (fun l hl => hD l (by have := mem_range.mp hl;omega))
    change cgOperator base+(1 : ℝ) • cumulativeDrift base D j=cgOperator base+(1 : ℝ) • cumulativeDrift base E j
    simp only [cumulativeDrift,hsum]
  have hcorrection : scenarioCorrection base Theta=scenarioProbe base Theta := by
    funext j
    change scenarioProbe base Theta j+Matrix.toEuclideanCLM (𝕜 := ℝ)
      (metricRoot base*matrixSequenceExtension (k+1) (0 : Fin (k+1) → Matrix (Fin n) (Fin n) ℝ) j*metricRoot base)=_
    rw [matrixSequenceExtension_zero,Matrix.mul_zero,Matrix.zero_mul,map_zero,add_zero]
  have hhistory : methodRun m (scenarioProbe base Theta) (scenarioCorrection base Theta) g (k+1)=
      methodRun m (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1) :=
    methodRun_congr_prefix m _ _ _ _ g (k+1) hprobe
      (fun j hj => (congrFun hcorrection j).trans (hprobe j hj))
  have hgradient : probedGradient m (scenarioProbe base Theta) (scenarioCorrection base Theta) g (k+1)=
      probedGradient m (canonicalFCPath base E 1) (canonicalFCPath base E 1) g (k+1) :=
    congrArg History.gradient hhistory
  have he := hbound Theta (hnorm.trans hsmall) (fun l => hE l.val)
  change ‖R
    (probedGradient m (scenarioProbe base Theta) (scenarioCorrection base Theta) g (k+1))-
      L D‖≤C*‖Theta‖^2 at he
  rw [hgradient,hresponse] at he
  exact he.trans (mul_le_mul_of_nonneg_left ((sq_le_sq₀ (norm_nonneg Theta) hW).mpr hnorm) hC)


end
end krylov.Stability
