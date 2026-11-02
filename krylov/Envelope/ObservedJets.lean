import krylov.Envelope.JetLists
import krylov.Methods.ObservedListRules

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, actual primitive observed decisions.
Use: propagate genuine coordinate first-jet coherence through real primitive
observed coefficient rules and true full-history list decisions.
Source: genuine finite observed combination differentiation, actual C-two
coefficient composition and real local finite-array observation charts.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology krylov.Methods
open scoped BigOperators
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every genuine primitive C-two observed coefficient evaluation preserves the actual first-jet subspace of its true data.
Use: Every genuine primitive C-two observed coefficient evaluation preserves the actual first-jet subspace of its true data.
Article: main_krylov, apB:lem:filtration, actual primitive observed decisions.
Proof: Compose the actual coefficients with the real data chart and apply the proved genuine observed-combination derivative theorem. -/
theorem observedRule_evaluate_jet (K : Submodule ℝ E) (L : E →ₗ[ℝ] E) {n : ℕ}
    (f : ObservedRule E n) (data : ℝ → Fin n → E)
    (hf : ContDiffAt ℝ 2 f.coefficient (data 0)) (hd : ContDiffAt ℝ 2 data 0)
    (hj : ∀ i, (data 0 i,deriv (fun t => data t i) 0)∈jetSubspace K L) :
    (f.evaluate (data 0),deriv (fun t => f.evaluate (data t)) 0)∈jetSubspace K L := by
  have hc := contDiffAt_pi.mp (hf.comp 0 hd)
  have hv := contDiffAt_pi.mp hd
  exact observed_combination_jet K L (fun i t => f.coefficient (data t) i) (fun i t => data t i)
    (fun i => deriv (fun t => f.coefficient (data t) i) 0) (fun i => deriv (fun t => data t i) 0) 0
    (fun i => ((hc i).differentiableAt (by norm_num)).hasDerivAt)
    (fun i => ((hv i).differentiableAt (by norm_num)).hasDerivAt) hj

/-- Every real locally smooth full-history list decision preserves genuine observed first-jet coherence.
Use: Every real locally smooth full-history list decision preserves genuine observed first-jet coherence.
Article: main_krylov, apB:lem:filtration, actual primitive observed decisions.
Proof: Choose an actual finite coordinate chart, transfer the true primitive coefficient regularity to it and identify the genuine list decision and its derivative by actual local equality. -/
theorem JetListAt.decision (K : Submodule ℝ E) (L : E →ₗ[ℝ] E)
    (rules : ∀ n, ObservedRule E n) (v : ℝ → List E) (hv : JetListAt (jetSubspace K L) v)
    (hrule : ContDiffAt ℝ 2 (rules (v 0).length).coefficient (observedArray (v 0).length (v 0))) :
    (listDecision rules (v 0),deriv (fun t => listDecision rules (v t)) 0)∈jetSubspace K L := by
  -- Use a chart of the genuine observation list, with real coordinate jets already verified.
  obtain ⟨n,data,hd,he,hj⟩ := hv.chart
  have hf : ContDiffAt ℝ 2 (rules n).coefficient (data 0) := by
    rw [he.self_of_nhds,List.length_ofFn,observedArray_ofFn] at hrule
    exact hrule
  have hjet := observedRule_evaluate_jet K L (rules n) data hf hd hj
  have heq : (fun t => listDecision rules (v t))=ᶠ[𝓝 (0 : ℝ)]fun t => (rules n).evaluate (data t) := by
    filter_upwards [he] with t ht
    rw [ht,listDecision_ofFn]
  rw [show listDecision rules (v 0)=(rules n).evaluate (data 0) from heq.self_of_nhds,heq.deriv_eq]
  exact hjet
end
end krylov.Envelope
