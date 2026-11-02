import krylov.Envelope.CanonicalFiltration
import krylov.Stability.SmoothMetricCompact

set_option autoImplicit false
/-!
Article: main_krylov, thm:E, genuine directional common variation with reference parameters.
Use: identify the actual Frechet derivative along real perturbations fixing
the reference matrix and initial gradient, while allowing both reference
parameters and the actual physical metric to vary on the ambient data space.
Source: genuine primitive raw-method C-two regularity, actual metric-root
calculus, real line composition and the proved complete canonical filtration.
-/

namespace krylov.Envelope
noncomputable section
open Matrix Filter Topology krylov.Methods krylov.Reference krylov.Secant krylov.Stability
open scoped Matrix.Norms.L2Operator
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ}

/-- The actual Frechet derivative of a genuinely smooth raw method has the true common frozen unexplored component along every real perturbation line fixing its reference data.
Use: The actual Frechet derivative of a genuinely smooth raw method has the true common frozen unexplored component along every real perturbation line fixing its reference data.
Article: main_krylov, thm:E, genuine directional common variation with reference parameters.
Proof: Restrict the true ambient operator data to the genuine perturbation line. Real primitive regularity supplies its actual raw gradient derivative; genuine reference and initial-gradient constancy identify the true varying-metric output on that line. The actual chain rule transfers the proved one-parameter raw-method frozen filtration to the genuine ambient Frechet derivative. -/
theorem actual_fderiv_common_transverse (memory : ℕ → ℕ) (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (base : X → Matrix (Fin n) (Fin n) ℝ) (g : X → EuclideanSpace ℝ (Fin n))
    (A B : X → ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) (x h : X) (N : ℕ)
    (hb : ContDiffAt ℝ 2 base x) (hpos : ∀ᶠ p in 𝓝 x, (base p).PosDef)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun p => A p i) x)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun p => B p i) x) (hg : ContDiffAt ℝ 2 g x)
    (hAx : A x=fun _ => cgOperator (base x)) (hBx : B x=fun _ => cgOperator (base x))
    (hpre : ∀ i<N, CG.gradient (cgOperator (base x)) (g x) i≠0)
    (hsmooth : SmoothProbedCycleAt m 2 (cgOperator (base x)) (g x) N)
    (hbaseLine : ∀ t : ℝ, base (x+t • h)=base x) (hgLine : ∀ t : ℝ, g (x+t • h)=g x) :
    let Φ := fun p => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base p))⁻¹
      (probedGradient m (A p) (B p) (g p) N)
    let D := fderiv ℝ Φ x h
    D-(exploredFlag (base x) (g x) N).starProjection D=
      commonTransverseResponse (base x) (g x) (fun t => A (x+t • h)) N := by
  -- Restrict genuine primitive operator data to the actual reference-preserving perturbation line.
  let p := fun t : ℝ => x+t • h
  let Φ := fun q => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base q))⁻¹
    (probedGradient m (A q) (B q) (g q) N)
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot (base x))⁻¹
  have hp : ContDiffAt ℝ 2 p 0 := by fun_prop
  have hp0 : p 0=x := by simp [p]
  have hAp (i : ℕ) (hi : i<N) : ContDiffAt ℝ 2 (fun t => A (p t) i) 0 :=
    (show ContDiffAt ℝ 2 (fun q => A q i) (p 0) by rw [hp0];exact hA i hi).comp 0 hp
  have hBp (i : ℕ) (hi : i<N) : ContDiffAt ℝ 2 (fun t => B (p t) i) 0 :=
    (show ContDiffAt ℝ 2 (fun q => B q i) (p 0) by rw [hp0];exact hB i hi).comp 0 hp
  have hA0 : (fun i => A (p 0) i)=fun _ => cgOperator (base x) := by rw [hp0,hAx]
  have hB0 : (fun i => B (p 0) i)=fun _ => cgOperator (base x) := by rw [hp0,hBx]
  have hG := smoothProbed_gradient_regular m hm A B g x N hA hB hg (cgOperator (base x)) hAx hBx
    (cgOperator_positive _ hpos.self_of_nhds).1 (cgOperator_positive _ hpos.self_of_nhds).2 hpre hsmooth
  have hΦ : ContDiffAt ℝ 2 Φ x :=
    (matrixOperator_contDiffAt _ x (metricRoot_inverse_contDiffAt base x hb hpos)).clm_apply hG
  have hpD : HasDerivAt p h 0 := by
    simpa only [p,id_eq,one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x
  -- The actual ambient Frechet derivative is evaluated on the true perturbation direction by the genuine chain rule.
  have hchain : HasDerivAt (fun t => Φ (p t)) (fderiv ℝ Φ x h) 0 := by
    have hf : HasFDerivAt Φ (fderiv ℝ Φ x) (p 0) := by
      rw [hp0]
      exact (hΦ.differentiableAt (by norm_num)).hasFDerivAt
    exact hf.comp_hasDerivAt 0 hpD
  have hGp := smoothProbed_gradient_regular m hm (fun t => A (p t)) (fun t => B (p t)) (fun _ => g x) 0 N hAp hBp contDiffAt_const
    (cgOperator (base x)) hA0 hB0 (cgOperator_positive _ hpos.self_of_nhds).1
    (cgOperator_positive _ hpos.self_of_nhds).2 hpre hsmooth
  have hR : HasDerivAt (fun t => R (probedGradient m (A (p t)) (B (p t)) (g x) N))
      (R (deriv (fun t => probedGradient m (A (p t)) (B (p t)) (g x) N) 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) R).clm_apply
      (hGp.differentiableAt (by norm_num)).hasDerivAt using 1
    simp only [_root_.zero_apply,zero_add]
    rfl
  -- Along this true perturbation line, both the real metric and initial gradient equal their genuine reference values.
  have he : (fun t => Φ (p t))=fun t => R (probedGradient m (A (p t)) (B (p t)) (g x) N) := by
    funext t
    dsimp only [Φ,p,R]
    rw [hbaseLine,hgLine]
  rw [he] at hchain
  have hD := hchain.unique hR
  change fderiv ℝ Φ x h-_=_
  rw [hD]
  exact actual_common_transverse memory m hm hspan (fun t => A (p t)) (fun t => B (p t)) (g x) (base x) hpos.self_of_nhds
    hA0 hB0 N hAp hBp hpre hsmooth
end
end krylov.Envelope
