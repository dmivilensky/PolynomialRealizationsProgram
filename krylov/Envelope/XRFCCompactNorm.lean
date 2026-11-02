import krylov.Stability.XRFCMetricRegularity
import krylov.Methods.XRFCReferenceOutput
import krylov.Envelope.CompactNormVariation
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine compact-uniform XRFC norm remainder.
Use: derive one actual perturbation radius and weighted quadratic norm remainder for the original semantic output across every genuine compact family of varying references and finite parameter directions.
Source: primitive joint XRFC metric-output regularity, actual quadratic reference gradient identity and the proved compact weighted norm Taylor theorem.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Set Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X] {n : ℕ}

/-- The genuine semantic full-memory XRFC canonical output norm has an actual compact-uniform weighted quadratic first-order remainder under primitive C-two trial charts.
Use: The genuine semantic full-memory XRFC canonical output norm has an actual compact-uniform weighted quadratic first-order remainder under primitive C-two trial charts.
Article: main_krylov, thm:E1, genuine compact-uniform XRFC norm remainder.
Proof: Derive real joint varying-metric output regularity on the original compact family and its positive initial-error weight, then apply the genuine compact norm Taylor theorem and identify the actual CG reference. -/
theorem xrfc_compact_norm_variation (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
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
      let e := cgCanonicalError (base x) (g x) N
      let e0 := ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
      |‖Phi (x+h)‖-‖e‖-inner ℝ e (fderiv ℝ Phi x h)/‖e‖|≤
        C*‖h‖^2*e0*(1+e0/‖e‖) := by
  dsimp only
  let m := xrfcMethod fullMemory trial
  let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
    (m.outputGradient (B p) (oneGradientRun m (A p) (g p) N))
  let e0 := fun x => ‖cgOperator (metricRoot (base x))⁻¹ (g x)‖
  -- Actual active counts derive every genuine nonzero reference and initial-error domain on the original compact family.
  have hpre (x : X) (hx : x∈K) (i : ℕ) (hi : i≤N) : CG.gradient (cgOperator (base x)) (g x) i≠0 :=
    cg_nonstagnation _ (hpos x hx).self_of_nhds _ i (hi.trans_lt (hcount x hx))
  have hPhi (x : X) (hx : x∈K) : ContDiffAt ℝ 2 Phi x :=
    xrfc_metric_output_contDiffAt trial base g A B x N (hb x hx) (hpos x hx) (hA x hx) (hB x hx)
      (hg x hx) (hAx x hx) (fun i hi => hpre x hx i hi.le) (ht x hx) (hT x hx)
  have he0 : ContinuousOn e0 K := canonical_error_continuousOn base g K
    (fun x hx => (hb x hx).continuousAt.continuousWithinAt) (fun x hx => (hg x hx).continuousAt.continuousWithinAt)
    (fun x hx => (hpos x hx).self_of_nhds)
  have hepos (x : X) (hx : x∈K) : 0<e0 x := canonical_error_pos _ (hpos x hx).self_of_nhds _ (hpre x hx 0 (Nat.zero_le N))
  -- One actual compact Taylor radius controls all true finite parameter directions and retains the genuine remaining-error factor.
  obtain ⟨delta,C,hd,hC,hbound⟩ := compact_weighted_norm_variation Phi e0 K hK hPhi he0 hepos
  refine ⟨delta,C,hd,hC,?_⟩
  intro x hx h hh
  have href : Phi x=cgCanonicalError (base x) (g x) N := by
    dsimp only [Phi]
    rw [hAx x hx,hBx x hx]
    have hp := cgOperator_positive _ (hpos x hx).self_of_nhds
    rw [xrfc_reference_output_gradient trial _ hp.1 hp.2 (g x) N (fun i hi => hpre x hx i hi.le) (ht x hx)]
    rfl
  have ha : 0<‖cgCanonicalError (base x) (g x) N‖ :=
    canonical_error_pos _ (hpos x hx).self_of_nhds _ (hpre x hx N le_rfl)
  have hbound' := hbound x hx h hh (by rw [href];exact ha)
  rwa [href] at hbound'
end
end krylov.Envelope
