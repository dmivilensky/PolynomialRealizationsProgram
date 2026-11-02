import krylov.OneGradient.XRFCStepFrechet
import krylov.Stability.CompactSmooth
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, actual compact-uniform step-basis XRFC expansion.
Use: give one true perturbation radius and quadratic relative-error constant
across every compact family of genuine nondegenerate full-cycle references.
Source: original primitive varying-metric output C2, proved actual Frechet
step response and the reused compact weighted integral Taylor theorem.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The true varying-prefix step-basis XRFC output has its printed response
with one actual compact-uniform quadratic remainder weighted by the genuine
original initial error norm.
Use: no per-reference remainder radius or pre-assumed uniform trajectory
estimate replaces the source's original compact nondegenerate-reference assertion.
Article: main_krylov, thm:I, compact-uniform step-basis expansion.
Proof: primitive trial and operator data derive joint actual canonical-output
C2 at every true compact reference. The genuine inverse-root initial error is
continuous and positive there. Compact smooth weighted Taylor gives a common
radius and constant; actual reference termination removes the constant term
and the proved genuine Frechet derivative gives exactly the printed step response. -/
theorem xrfc_step_compact_expansion
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (K : Set X) (hK : IsCompact K) (hn : 0<n)
    (hb : ∀ x∈K,ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hA : ∀ x∈K,∀ k,ContDiffAt ℝ 2 (fun p => A p k) x) (hg : ∀ x∈K,ContDiffAt ℝ 2 g x)
    (hsym : ∀ p k,(A p k).IsSymm) (hAx : ∀ x∈K,∀ k,A x k=base x)
    (hc : ∀ x (hx : x∈K),referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x)=n)
    (ht : ∀ x∈K,∀ i<n,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator (base x)) (g x) i)≠0)
    (hT : ∀ x∈K,∀ k<n,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (fun _ => cgOperator (base x)) (g x) k)) :
    let m := xrfcMethod fullMemory trial
    let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
      (m.outputGradient (cgOperator (A p n)) (oneGradientRun m (fun k => cgOperator (A p k)) (g p) n))
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ h : X,‖h‖≤delta →
      (∀ t : ℝ,base (x+t • h)=base x) → (∀ t : ℝ,g (x+t • h)=g x) →
      let R := cgOperator (metricRoot (base x))⁻¹
      let E := fun l => R*(deriv (fun t : ℝ => cgOperator (A (x+t • h) (l+1))) 0-
        deriv (fun t : ℝ => cgOperator (A (x+t • h) l)) 0)*R
      ‖Phi (x+h)-xrfcStepResponse trial (base x) (g x) E‖≤C*‖h‖^2*‖R (g x)‖ := by
  let m := xrfcMethod fullMemory trial
  let op := fun p k => cgOperator (A p k)
  let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
    (m.outputGradient (op p n) (oneGradientRun m (op p) (g p) n))
  let e := fun p => ‖cgOperator (metricRoot (base p))⁻¹ (g p)‖
  have hOp (x : X) (hx : x∈K) (k : ℕ) : ContDiffAt ℝ 2 (fun p => op p k) x :=
    matrixOperator_contDiffAt _ x (hA x hx k)
  have hOp0 (x : X) (hx : x∈K) : op x=(fun _ => cgOperator (base x)) :=
    funext (fun k => by simp only [op,hAx x hx])
  have hPhi (x : X) (hx : x∈K) : ContDiffAt ℝ 2 Phi x :=
    xrfc_metric_output_contDiffAt trial base g op (fun p => op p n) x n (hb x hx) (hpos x hx)
      (hOp x hx) (hOp x hx n) (hg x hx) (hOp0 x hx)
      (fun i hi => cg_nonstagnation _ (hpos x hx).self_of_nhds _ i (by rw [hc x hx];exact hi))
      (ht x hx) (by rw [hOp0 x hx];exact hT x hx)
  have he : ContinuousOn e K := by
    intro x hx
    have hR := matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x (hb x hx) (hpos x hx))
    exact ((hR.clm_apply (hg x hx)).continuousAt.norm).continuousWithinAt
  have hepos (x : X) (hx : x∈K) : 0<e x := by
    have hnz : CG.gradient (cgOperator (base x)) (g x) 0≠0 :=
      cg_nonstagnation _ (hpos x hx).self_of_nhds _ 0 (by rw [hc x hx];exact hn)
    exact canonical_error_pos (base x) (hpos x hx).self_of_nhds (g x) hnz
  have hzero (x : X) (hx : x∈K) : Phi x=0 := by
    change cgOperator (metricRoot (base x))⁻¹
      (m.outputGradient (op x n) (oneGradientRun m (op x) (g x) n))=0
    rw [hOp0 x hx]
    have hterm := (xrfc_full_terminates (base x) (hpos x hx).self_of_nhds (g x) trial
      (fun i hi => ht x hx i (by rw [← hc x hx];exact hi))).2.1
    rw [hc x hx] at hterm
    change m.outputGradient (cgOperator (base x)) (oneGradientRun m (fun _ => cgOperator (base x)) (g x) n)=0 at hterm
    rw [hterm,map_zero]
  obtain ⟨delta,C,hd,hC,hrem⟩ := compact_smooth_weighted_taylor Phi e 2 K hK hPhi he hepos
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx h hh hbaseLine hgLine
  let R := cgOperator (metricRoot (base x))⁻¹
  let E := fun l => R*(deriv (fun t : ℝ => cgOperator (A (x+t • h) (l+1))) 0-
    deriv (fun t : ℝ => cgOperator (A (x+t • h) l)) 0)*R
  have hD := xrfc_step_fderiv_response trial base g A x h (hb x hx) (hpos x hx) (hA x hx) (hg x hx)
    hsym (hAx x hx) (hc x hx) hn (ht x hx) (hT x hx) hbaseLine hgLine
  have hpoly : taylorPolynomial Phi 2 x h=xrfcStepResponse trial (base x) (g x) E := by
    simp only [taylorPolynomial,Finset.sum_range_succ,Finset.sum_range_zero,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,Nat.factorial_zero,Nat.factorial_one,
      Nat.cast_one,inv_one,one_smul,hzero x hx,zero_add]
    exact hD
  have h := hrem x hx h hh 2 (by decide) le_rfl
  rw [hpoly] at h
  exact h

end
end krylov.OneGradient
