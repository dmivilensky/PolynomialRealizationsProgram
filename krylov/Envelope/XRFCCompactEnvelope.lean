import krylov.Envelope.XRFCCompactNorm
import krylov.Envelope.XRFCDirectionalPairing
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, complete actual compact-uniform virtual-launch envelope.
Use: conclude the genuine virtual frozen-response norm expansion with one actual uniform perturbation radius across every compact family of positive nonexhausted quadratic references.
Source: actual joint varying-reference XRFC output regularity, proved reference-preserving Frechet virtual pairing and genuine weighted compact norm Taylor calculus.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The actual full-memory XRFC canonical semantic output has the genuine compact-uniform virtual-launch norm envelope for every true reference-preserving finite parameter perturbation.
Use: The actual full-memory XRFC canonical semantic output has the genuine compact-uniform virtual-launch norm envelope for every true reference-preserving finite parameter perturbation.
Article: main_krylov, thm:E1, complete actual compact-uniform virtual-launch envelope.
Proof: Apply the real compact weighted output norm remainder and replace its actual Frechet pairing by the proved genuine virtual frozen response along the original perturbation line. -/
theorem xrfc_compact_virtual_envelope (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (N : ℕ) (K : Set X) (hK : IsCompact K)
    (hb : ∀ x∈K,ContDiffAt ℝ 2 base x) (hpos : ∀ x∈K,∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hA : ∀ x∈K,∀ i,ContDiffAt ℝ 2 (fun p => A p i) x)
    (hB : ∀ x∈K,ContDiffAt ℝ 2 B x) (hg : ∀ x∈K,ContDiffAt ℝ 2 g x)
    (hAx : ∀ x∈K,A x=fun _ => cgOperator (base x)) (hBx : ∀ x∈K,B x=cgOperator (base x))
    (hcount : ∀ x (hx : x∈K),N<referenceAtomCount (base x) (hpos x hx).self_of_nhds (g x))
    (ht : ∀ x∈K,∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator (base x)) (g x) i)≠0)
    (hT : ∀ x∈K,∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k)) :
    let m := xrfcMethod fullMemory trial
    let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
      (m.outputGradient (B p) (oneGradientRun m (A p) (g p) N))
    ∃ delta C : ℝ,0<delta ∧ 0≤C ∧ ∀ x∈K,∀ h : X,‖h‖≤delta →
      (∀ t : ℝ,base (x+t • h)=base x) → (∀ t : ℝ,g (x+t • h)=g x) →
      let e := cgCanonicalError (base x) (g x) N
      let e0 := ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
      |‖Phi (x+h)‖-‖e‖-inner ℝ e (xrfcEnvelopeResponse trial (fun t => A (x+t • h)) (fun t => B (x+t • h)) (base x) (g x) N)/‖e‖|≤
        C*‖h‖^2*e0*(1+e0/‖e‖) := by
  dsimp only
  -- Keep the true common compact perturbation radius before identifying the actual virtual-response pairing in each genuine direction.
  obtain ⟨delta,C,hd,hC,hbound⟩ := xrfc_compact_norm_variation trial base g A B N K hK hb hpos hA hB hg hAx hBx hcount ht hT
  dsimp only at hbound
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx h hh hbaseLine hgLine
  have hi := xrfc_fderiv_norm_pairing trial base g A B x h N (hb x hx) (hpos x hx)
    (hA x hx) (hB x hx) (hg x hx) (hAx x hx) (hBx x hx) (hcount x hx) (ht x hx) (hT x hx) hbaseLine hgLine
  dsimp only at hi
  have h := hbound x hx h hh
  rw [hi] at h
  exact h
end
end krylov.Envelope
