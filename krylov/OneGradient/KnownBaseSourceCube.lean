import krylov.OneGradient.ScenarioOperatorRegularity
import krylov.OneGradient.ScenarioCanonicalIncrements
import krylov.Correction.ScenarioExpansion
import krylov.Information.FirstIncrementScenario
set_option autoImplicit false
/-!
Article: main_krylov, thm:local(b), full known-base source parameter space.
Use: put the actual prior, all individual increments and independent
output form in one finite symmetric source space before choosing a profile.
Source: the existing original symmetric finite-scenario subspace, genuine
positive-root form transport and exact source/native operator dictionaries.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Finset Filter Topology krylov.Reference krylov.Methods krylov.Secant krylov.Information
  krylov.Stability krylov.Correction krylov.Envelope
open scoped BigOperators Matrix.Norms.L2Operator
variable {n : ℕ}

/-- A whole finite original known-base source tuple, using the existing
symmetric source space. Its first second-array slot is the genuine prior
and its final slot the independent output form; intermediate slots are unused.
Use: the uniform remainder is proved jointly before any source profile.
Article: main_krylov, thm:local(b), complete primitive known-base source cube. -/
def knownBaseSourceCube (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (Theta : symmetricScenarios (n+1) (n+1)) : Scenario (n+1) where
  base := base+metricRoot base*matrixSequenceExtension (n+1) Theta.val.2 0*metricRoot base
  increment := fun l => metricRoot base*matrixSequenceExtension n Theta.val.1 l*metricRoot base
  terminal := metricRoot base*matrixSequenceExtension (n+1) Theta.val.2 n*metricRoot base
  correction := fun _ => 0

/-- The whole original known-base source cube has C-one genuine native
operators, symmetric on every full parameter tuple and equal to the known
quadratic reference at zero. No perturbation path or policy fields are inputs.
Use: one actual full-parameter output theorem gives a common remainder tube
for all priors and independent source profiles at the fixed reference.
Article: main_krylov, thm:local(b), primitive full-source native data.
Proof: reuse the existing actual symmetric source coordinate analyticity.
Fixed physical root congruence gives genuine source fields, and the shared
primitive source-operator calculus derives their real query/output matrices. -/
theorem knownBaseSourceCube_operator_data
    (base : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hb : base.PosDef) :
    let M := fun Theta j => oneGradientScenarioMatrices (knownBaseSourceCube base Theta) n j
    (∀ j,ContDiffAt ℝ 1 (fun Theta : symmetricScenarios (n+1) (n+1) => M Theta j) 0) ∧
      (∀ Theta j,(M Theta j).IsSymm) ∧ ∀ j,M 0 j=base := by
  let S := knownBaseSourceCube base
  have hbase : ContDiffAt ℝ 1 (fun Theta => (S Theta).base) 0 := contDiffAt_const.add
    ((contDiffAt_const.mul ((symmetricScenario_correction_analytic (n := n+1) (N := n+1) 0).contDiffAt)).mul contDiffAt_const)
  have hinc (l : ℕ) : ContDiffAt ℝ 1 (fun Theta => (S Theta).increment l) 0 :=
    (contDiffAt_const.mul ((symmetricScenario_increment_analytic (n := n+1) (N := n+1) l).contDiffAt)).mul contDiffAt_const
  have hterm : ContDiffAt ℝ 1 (fun Theta => (S Theta).terminal) 0 :=
    (contDiffAt_const.mul ((symmetricScenario_correction_analytic (n := n+1) (N := n+1) n).contDiffAt)).mul contDiffAt_const
  have hs (M : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) (hM : M.IsSymm) :
      (metricRoot base*M*metricRoot base).IsSymm := by
    simp only [Matrix.IsSymm,Matrix.transpose_mul,(metricRoot_isSymm base).eq,hM.eq,Matrix.mul_assoc]
  have hc (Theta : symmetricScenarios (n+1) (n+1)) (k : ℕ) :
      (matrixSequenceExtension (n+1) Theta.val.2 k).IsSymm := by
    by_cases hk : k<n+1
    · simp only [matrixSequenceExtension,dite_eq_left hk]
      exact Theta.property.2 ⟨k,hk⟩
    · simp only [matrixSequenceExtension,dite_eq_right hk]
      exact Matrix.isSymm_zero
  refine ⟨fun j => scenario_operators_contDiffAt S hbase (fun l _ => hinc l) hterm j,?_,?_⟩
  · intro Theta j
    exact scenario_operators_isSymm (S Theta) (hb.1.isSymm.add (hs _ (hc Theta 0)))
      (fun l _ => hs _ (symmetricScenario_increment_symm Theta l)) (hs _ (hc Theta n)) j
  · intro j
    have hi : ∀ l<n,(S 0).increment l=0 := by
      intro l _
      simp only [S,knownBaseSourceCube,ZeroMemClass.coe_zero,Prod.fst_zero,matrixSequenceExtension,Pi.zero_apply,
        dite_eq_ite,ite_self,Matrix.mul_zero,Matrix.zero_mul]
    have ht : (S 0).terminal=0 := by
      simp only [S,knownBaseSourceCube,ZeroMemClass.coe_zero,Prod.snd_zero,matrixSequenceExtension,Pi.zero_apply,
        dite_eq_ite,ite_self,Matrix.mul_zero,Matrix.zero_mul]
    change oneGradientScenarioMatrices (S 0) n j=base
    rw [scenario_operators_zero (S 0) hi ht j]
    simp only [S,knownBaseSourceCube,ZeroMemClass.coe_zero,Prod.snd_zero,matrixSequenceExtension,Pi.zero_apply,
      dite_eq_ite,ite_self,Matrix.mul_zero,Matrix.zero_mul,add_zero]

end
end krylov.OneGradient
