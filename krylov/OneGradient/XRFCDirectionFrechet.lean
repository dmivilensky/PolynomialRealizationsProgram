import krylov.OneGradient.XRFCDirectionVariation
import krylov.Stability.XRFCDMetricRegularity
set_option autoImplicit false
/-!
Article: main_krylov, thm:I, actual joint direction-basis output derivative.
Use: identify the real Frechet tangent of the original varying-reference
canonical XRFC output on every reference-preserving perturbation direction.
Source: primitive actual joint output regularity, real affine-line chain rule
and the proved full varying-prefix direction-basis semantic first variation.
-/

namespace krylov.OneGradient
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped BigOperators Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The actual joint canonical XRFC output's Frechet derivative is exactly
the original measured-amplitude direction response on every genuine perturbation
line that keeps the original reference and initial gradient fixed.
Use: replace the true first Taylor polynomial in compact-uniform bounds by
the printed source response, rather than assume a directional response field.
Article: main_krylov, thm:I, joint direction-basis derivative identification.
Proof: original primitive data give actual joint canonical output C2. Restrict
to the true affine perturbation line; the real chain rule evaluates its genuine
Frechet derivative. Reference constancy identifies this actual line output
with the full-cycle physical path theorem, and derivative uniqueness gives the source response. -/
theorem xrfc_direction_fderiv_response
    (trial : History (EuclideanSpace ℝ (Fin n)) → ℝ)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A : X → ℕ → Matrix (Fin n) (Fin n) ℝ) (x h : X)
    (hb : ContDiffAt ℝ 2 base x) (hpos : ∀ᶠ p in 𝓝 x,(base p).PosDef)
    (hA : ∀ k,ContDiffAt ℝ 2 (fun p => A p k) x) (hg : ContDiffAt ℝ 2 g x)
    (hAx : ∀ k,A x k=base x)
    (hc : referenceAtomCount (base x) hpos.self_of_nhds (g x)=n) (hn : 0<n)
    (ht : ∀ i<n,trial (oneGradientRun (xrfcDMethod fullMemory trial) (fun _ => cgOperator (base x)) (g x) i)≠0)
    (hT : ∀ k<n,ContDiffAt ℝ 2 (trialCoordinate trial k)
      (oneGradientData (xrfcDMethod fullMemory trial) (fun _ => cgOperator (base x)) (g x) k))
    (hbaseLine : ∀ t : ℝ,base (x+t • h)=base x) (hgLine : ∀ t : ℝ,g (x+t • h)=g x) :
    let m := xrfcDMethod fullMemory trial
    let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
      (m.outputGradient (cgOperator (A p n)) (oneGradientRun m (fun k => cgOperator (A p k)) (g p) n))
    let R := cgOperator (metricRoot (base x))⁻¹
    let E := fun l => R*(deriv (fun t : ℝ => cgOperator (A (x+t • h) (l+1))) 0-
      deriv (fun t : ℝ => cgOperator (A (x+t • h) l)) 0)*R
    fderiv ℝ Phi x h=xrfcDirectionResponse trial (base x) (g x) E := by
  let m := xrfcDMethod fullMemory trial
  let op := fun p k => cgOperator (A p k)
  let Phi := fun p => cgOperator (metricRoot (base p))⁻¹
    (m.outputGradient (op p n) (oneGradientRun m (op p) (g p) n))
  let p := fun t : ℝ => x+t • h
  let R := cgOperator (metricRoot (base x))⁻¹
  have hp0 : p 0=x := by simp [p]
  have hp : ContDiffAt ℝ 2 p 0 := by fun_prop
  have hAp (k : ℕ) : ContDiffAt ℝ 2 (fun t => A (p t) k) 0 :=
    (show ContDiffAt ℝ 2 (fun z => A z k) (p 0) by rw [hp0];exact hA k).comp 0 hp
  have hA0 (k : ℕ) : A (p 0) k=base x := by rw [hp0];exact hAx k
  have hAop (k : ℕ) : ContDiffAt ℝ 2 (fun z => op z k) x := matrixOperator_contDiffAt _ x (hA k)
  have hAop0 : op x=(fun _ => cgOperator (base x)) := funext (fun k => by simp only [op,hAx])
  have hPhi := xrfcD_metric_output_contDiffAt trial base g op (fun z => op z n) x n hb hpos hAop (hAop n) hg hAop0
    (fun i hi => cg_nonstagnation _ hpos.self_of_nhds _ i (by rw [hc];exact hi)) ht (by rw [hAop0];exact hT)
  have hpD : HasDerivAt p h 0 := by
    simpa only [p,id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  have hchain : HasDerivAt (fun t => Phi (p t)) (fderiv ℝ Phi x h) 0 := by
    have hd : HasFDerivAt Phi (fderiv ℝ Phi x) (p 0) := by
      rw [hp0]
      exact (hPhi.differentiableAt (by norm_num)).hasFDerivAt
    exact hd.comp_hasDerivAt 0 hpD
  have he : (fun t => Phi (p t))=(fun t => R (m.outputGradient (op (p t) n) (oneGradientRun m (op (p t)) (g x) n))) := by
    funext t
    dsimp only [Phi,p,R]
    rw [hbaseLine,hgLine]
  rw [he] at hchain
  have hjet := xrfc_direction_output_first_jet trial (base x) hpos.self_of_nhds (g x) hc hn
    (fun t k => cgOperator (A (p t) k))
    (fun k => matrixOperator_contDiffAt _ 0 ((hAp k).of_le (by norm_num)))
    (funext (fun k => by rw [hA0 k])) ht
    (fun k hk => (hT k hk).of_le (by norm_num))
  dsimp only
  exact hchain.unique hjet

end
end krylov.OneGradient
