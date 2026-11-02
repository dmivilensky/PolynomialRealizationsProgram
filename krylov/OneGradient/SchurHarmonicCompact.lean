import krylov.OneGradient.SchurHarmonicExecution
import krylov.OneGradient.XRFCStepCompact
import krylov.OneGradient.XRFCDirectionCompact
set_option autoImplicit false
/-!
Article: main_krylov, cor:quant and thm:radau, native harmonic uniform remainder.
Use: one real radius and initial-error weighted remainder constant work on
an entire compact family for the actual positive observed harmonic policy.
Source: derived primitive harmonic trial charts on the physical spectral
class and the original actual compact expansions in both XRFC bases. -/

namespace krylov.OneGradient
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The genuine continued harmonic XRFC policy has the original compact
uniform expansion in either basis, including references at the physical
spectral endpoints and with collapsed feasible information intervals.
Use: no primitive policy regularity or reference determinant is assumed;
the radius and weighted constant precede every reference and perturbation.
Article: main_krylov, cor:quant, thm:radau and lem:U(d).
Proof: active full-atom physical references derive all genuine primitive
C-two harmonic trial charts in both bases. Actual policy positivity gives
all nonzero trials. Reuse the corresponding genuine native compact expansion. -/
theorem xrfc_schur_compact_expansion (directions : Bool)
    (mu upper : ℝ) (hmu : 0<mu) (hmuL : mu≤upper)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (K : Set X) (hK : IsCompact K) (hn : 0<n)
    (hb : ∀ x∈K,ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hA : ∀ x∈K,∀ k,ContDiffAt ℝ 2 (fun p => A p k) x) (hg : ∀ x∈K,ContDiffAt ℝ 2 g x)
    (hsym : ∀ p k,(A p k).IsSymm) (hAx : ∀ x∈K,∀ k,A x k=base x)
    (hc : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (hlo : ∀ x∈K,(base x-mu • 1).PosSemidef) (hhi : ∀ x∈K,(upper • 1-base x).PosSemidef) :
    let trial := xrfcSchurTrial mu upper (n := n)
    let method := xrfcBasisMethod directions trial
    let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
      (method.outputGradient (cgOperator (A p n)) (oneGradientRun method (fun k => cgOperator (A p k)) (g p) n))
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ h : X,‖h‖≤delta →
      (∀ t : ℝ,base (x+t • h)=base x) → (∀ t : ℝ,g (x+t • h)=g x) →
      let R := cgOperator (metricRoot (base x))⁻¹
      let E := fun l => R*(deriv (fun t : ℝ => cgOperator (A (x+t • h) (l+1))) 0-
        deriv (fun t : ℝ => cgOperator (A (x+t • h) l)) 0)*R
      let response := if directions then xrfcDirectionResponse trial (base x) (g x) E
        else xrfcStepResponse trial (base x) (g x) E
      ‖Phi (x+h)-response‖≤C*‖h‖^2*‖R (g x)‖ := by
  have hT (x : X) (hx : x∈K) (k : ℕ) (hk : k<n) :=
    xrfc_schur_trial_reference_contDiff directions (base x) (hpos x hx).self_of_nhds mu upper hmu hmuL
      (hlo x hx) (hhi x hx) (g x) n
      (fun i hi => cg_nonstagnation _ (hpos x hx).self_of_nhds _ i (by rw [hc x hx];exact hi)) k hk 2
  cases directions with
  | false =>
    exact xrfc_step_compact_expansion (xrfcSchurTrial mu upper) base g A K hK hn hb hpos hA hg hsym hAx hc
      (fun _ _ _ _ => (xrfc_schur_trial_positive mu upper _).ne') hT
  | true =>
    exact xrfc_direction_compact_expansion (xrfcSchurTrial mu upper) base g A K hK hn hb hpos hA hg hAx hc
      (fun _ _ _ _ => (xrfc_schur_trial_positive mu upper _).ne') hT

end
end krylov.OneGradient
