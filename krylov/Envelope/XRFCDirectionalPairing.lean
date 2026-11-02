import krylov.Stability.XRFCMetricRegularity
import krylov.Envelope.XRFCNormPairing
set_option autoImplicit false
/-!
Article: main_krylov, thm:E1, genuine multivariate virtual-envelope derivative identification.
Use: identify the actual compact-family Frechet derivative along every true reference-preserving perturbation with the real scalar-line virtual frozen response.
Source: primitive joint XRFC metric-output regularity, genuine affine-line chain rule and the proved actual virtual norm first-jet pairing.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- Every actual reference-preserving finite parameter direction has exactly the genuine virtual-envelope first-derivative pairing for the real semantic XRFC output.
Use: Every actual reference-preserving finite parameter direction has exactly the genuine virtual-envelope first-derivative pairing for the real semantic XRFC output.
Article: main_krylov, thm:E1, genuine multivariate virtual-envelope derivative identification.
Proof: Restrict original primitive data to the actual affine perturbation line, derive genuine output regularity there and identify its actual Frechet tangent by uniqueness of true derivatives before applying the real virtual frozen pairing. -/
theorem xrfc_fderiv_norm_pairing (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (B : X → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (x h : X) (N : ℕ)
    (hb : ContDiffAt ℝ 2 base x) (hpos : ∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hA : ∀ i,ContDiffAt ℝ 2 (fun p => A p i) x) (hB : ContDiffAt ℝ 2 B x) (hg : ContDiffAt ℝ 2 g x)
    (hAx : A x=fun _ => cgOperator (base x)) (hBx : B x=cgOperator (base x))
    (hcount : N<referenceAtomCount (base x) hpos.self_of_nhds (g x))
    (ht : ∀ i<N,trial (oneGradientRun (xrfcMethod fullMemory trial) (fun _ => cgOperator (base x)) (g x) i)≠0)
    (hT : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcMethod fullMemory trial) (A x) (g x) k))
    (hbaseLine : ∀ t : ℝ,base (x+t • h)=base x) (hgLine : ∀ t : ℝ,g (x+t • h)=g x) :
    let m := xrfcMethod fullMemory trial
    let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
      (m.outputGradient (B p) (oneGradientRun m (A p) (g p) N))
    inner ℝ (cgCanonicalError (base x) (g x) N) (fderiv ℝ Phi x h)=
      inner ℝ (cgCanonicalError (base x) (g x) N)
        (xrfcEnvelopeResponse trial (fun t => A (x+t • h)) (fun t => B (x+t • h)) (base x) (g x) N) := by
  dsimp only
  -- Restrict original primitive data to the true reference-preserving affine parameter line.
  let m := xrfcMethod fullMemory trial
  let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
    (m.outputGradient (B p) (oneGradientRun m (A p) (g p) N))
  let p := fun t : ℝ => x+t • h
  let R := cgOperator (metricRoot (base x))⁻¹
  let Q := cgOperator (base x)
  have hp0 : p 0=x := by simp [p]
  have hp : ContDiffAt ℝ 2 p 0 := by fun_prop
  have hAp (i : ℕ) : ContDiffAt ℝ 2 (fun t => A (p t) i) 0 :=
    (show ContDiffAt ℝ 2 (fun z => A z i) (p 0) by rw [hp0];exact hA i).comp 0 hp
  have hBp : ContDiffAt ℝ 2 (fun t => B (p t)) 0 :=
    (show ContDiffAt ℝ 2 B (p 0) by rw [hp0];exact hB).comp 0 hp
  have hA0 : A (p 0)=fun _ => Q := by rw [hp0];exact hAx
  have hB0 : B (p 0)=Q := by rw [hp0];exact hBx
  have hTp : ∀ k<N,ContDiffAt ℝ 2 (trialCoordinate trial k) (oneGradientData m (A (p 0)) (g x) k) := by
    rw [hp0]
    exact hT
  have hpre (i : ℕ) (hi : i<N) : CG.gradient Q (g x) i≠0 :=
    cg_nonstagnation _ hpos.self_of_nhds _ i (hi.trans hcount)
  have hPhi := xrfc_metric_output_contDiffAt trial base g A B x N hb hpos hA hB hg hAx hpre ht hT
  have hpD : HasDerivAt p h 0 := by
    simpa only [p,id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  -- The actual ambient Frechet derivative is evaluated on the original perturbation direction by the genuine chain rule.
  have hc : HasDerivAt (fun t => Phi (p t)) (fderiv ℝ Phi x h) 0 := by
    have hh : HasFDerivAt Phi (fderiv ℝ Phi x) (p 0) := by rw [hp0];exact (hPhi.differentiableAt (by norm_num)).hasFDerivAt
    exact hh.comp_hasDerivAt 0 hpD
  have hq := cgOperator_positive (base x) hpos.self_of_nhds
  have hout := (quadraticXRFC_output_contDiffAt trial (fun t => A (p t)) (fun t => B (p t)) (fun _ => g x) 0
    hAp hBp contDiffAt_const Q hA0 hq.1 hq.2 N hpre ht hTp).2
  have hr := R.hasFDerivAt.comp_hasDerivAt 0 (hout.differentiableAt (by norm_num)).hasDerivAt
  -- True reference and initial-gradient constancy identify the actual varying-metric line output before its derivative is compared.
  have he : (fun t => Phi (p t))=(fun t => R (m.outputGradient (B (p t)) (oneGradientRun m (A (p t)) (g x) N))) := by
    funext t
    dsimp only [Phi,p,R]
    rw [hbaseLine,hgLine]
  rw [he] at hc
  have hd := hc.unique hr
  change inner ℝ (cgCanonicalError (base x) (g x) N) (fderiv ℝ Phi x h)=_
  rw [hd]
  exact xrfc_norm_first_jet_pairing trial (fun t => A (p t)) (fun t => B (p t)) (base x) hpos.self_of_nhds
    (g x) N hcount hA0 hB0 hAp hBp ht hTp
end
end krylov.Envelope
