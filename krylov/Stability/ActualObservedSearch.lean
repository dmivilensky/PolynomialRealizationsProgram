import krylov.Stability.ObservedCanonical
import krylov.Stability.UniformObservedLine
import krylov.Stability.ObservedGradient
import krylov.Correction.GatedUniformCutoff

/-!
Article: main_krylov, thm:UCq, original observed finite-prefix dictionary.
Use: Derive true quantitative RFC search and prefix facts from the original
executed observations in their actual positive-root metric.
Source: proved actual execution identities, genuine observed conditioning
and weighted CG geometry; no final stability conclusion is assumed.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference krylov.Secant krylov.Correction
open scoped InnerProductSpace Matrix.Norms.L2Operator
variable {n : ℕ}

/-- The original full probed-history conjugacy matrix is nonsingular under its actual canonical Gram and relative observed-pair allowances.
Use: Assemble the actual uniform ordinary-RFC induction under condition (N).
Article: main_krylov, thm:UCq.
Proof: The genuine chronological determinant dictionary and exact primal/dual cross-Gram invariance transport the proved normalized observed inverse domain back to the actual history.
-/
theorem full_observed_solve_from_canonical (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (m : ProbedMethod (EuclideanSpace ℝ (Fin n)))
    (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) {η δ : ℝ} (hη : 0≤η)
    (hs : ∀ i<k, Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)≠0)
    (hy : ∀ i<k, ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedSecant m A B g i)-
      Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖≤
      η*‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i)‖)
    (hG : ‖crossGram
      (unitWindow (fun i : Fin k => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i.val)))
      (unitWindow (fun i : Fin k => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i.val)))-1‖≤δ)
    (hsmall : δ+(k : ℝ)*η≤1/2) :
    IsUnit (crossGram (windowImages (selectedWindow fullMemory (methodRun m A B g k)))
      (windowSteps (selectedWindow fullMemory (methodRun m A B g k)))).det := by
  rw [full_probed_observed_solve_chronological]
  have hu := normalized_observed_solve_unit
    (fun i : Fin k => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (probedStep m A B g i.val))
    (fun i : Fin k => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ (probedSecant m A B g i.val))
    (fun i => hs i.val i.isLt) hη (fun i => hy i.val i.isLt) hG hsmall
  change IsUnit (crossGram (dualWindow base (fun i : Fin k => probedSecant m A B g i.val))
    (primalWindow base (fun i : Fin k => probedStep m A B g i.val))).det at hu
  rw [canonical_crossGram base hb] at hu
  exact hu

/-- A true observed-list search direction is nonzero when its actual metric gradient exceeds the conditioned old projected residual.
Use: Assemble the actual uniform ordinary-RFC induction under condition (N).
Article: main_krylov, thm:UCq.
Proof: A zero actual canonical direction would put the true base-gradient action in the old observed span. The proved coercive energy bound would contradict the genuine gradient lower bound.
-/
theorem observed_canonical_direction_nonzero (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (s y : ℕ → EuclideanSpace ℝ (Fin n)) (g : EuclideanSpace ℝ (Fin n)) (k : ℕ)
    {μ κ : ℝ} (hμ : 0<μ) (hκ : 0≤κ)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i) (hH : ‖cgOperator base‖≤κ*μ)
    (hG : ‖crossGram
      (unitWindow (fun i : Fin k => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (s i.val)))
      (unitWindow (fun i : Fin k => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (s i.val)))-1‖≤(1/2 : ℝ))
    (hgrad : 4*κ*‖projectedResidual
      (unitWindow (fun i : Fin k => Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (s i.val)))
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g)‖<
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g‖) :
    Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base) (windowDirection (executedPairs s y k) g)≠0 := by
  intro hz
  have hsp := chronological_canonical_direction_span base hb s y g k
  dsimp only at hsp
  rw [hz,zero_add] at hsp
  have hbound := observed_zero_direction_gradient_bound _ (cgOperator base)
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹ g) hμ hκ
    (fun v => by simpa only [cgOperator] using krylov.LinearAlgebra.spectral_lower_form base hb.1 hspec v)
    hH hG hsp
  exact (not_lt_of_ge hbound) hgrad


/-- The original real gated-RFC next line has a uniform reference-CG error derived from its actual earlier step, Gram and observed-secant errors.
Use: Assemble the actual uniform ordinary-RFC induction under condition (N).
Article: main_krylov, thm:UCq.
Proof: Derive the actual conjugacy inverse from canonical observations, use the original chronological span and image-conjugacy equations, and derive the real gradient error by observed secant accumulation. Apply the proved weighted scale-free search comparison and identify its displacement with the original executed physical line.
-/
theorem gated_observed_next_line_bound (base : Matrix (Fin n) (Fin n) ℝ) (hb : base.PosDef)
    (γ : ℝ) (A B : ℕ → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (g : EuclideanSpace ℝ (Fin n)) (k : ℕ) {μ κ C a K δ : ℝ}
    (hμ : 0<μ) (hκ : 1≤κ) (hC : 0≤C) (ha : 0≤a) (hK : 0≤K)
    (hspec : ∀ i, μ≤hb.1.eigenvalues i ∧ hb.1.eigenvalues i≤μ*κ)
    (hinit : ‖cgCanonicalError base g 0‖≤1)
    (hpre : ∀ i≤k, CG.gradient (cgOperator base) g i≠0)
    (hδ : 0≤δ) (hδone : δ≤1) (hhalf : δ≤1/2)
    (hGramSmall : a*δ≤1/2) (hSolve : a*δ+(k : ℝ)*(K*δ)≤1/2)
    (hProj : 4*Real.sqrt k*(K*δ)≤1/2) :
    let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
    let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
    let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
    (∀ i<k, R (probedStep m A B g i)≠0) →
    (∀ i<k, ‖J (probedSecant m A B g i)-R (probedStep m A B g i)‖≤K*δ*‖R (probedStep m A B g i)‖) →
    ‖crossGram (unitWindow (fun i : Fin k => R (probedStep m A B g i.val)))
      (unitWindow (fun i : Fin k => R (probedStep m A B g i.val)))-1‖≤a*δ →
    R (m.direction (methodRun m A B g k))≠0 →
    ‖canonicalOperator base (A k)-ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖≤δ →
    (∀ i<k, ‖R (probedStep m A B g i)-canonicalCGStep base g i‖≤C*δ) →
    ‖R (gatedObservedLineStep γ A B g k)-canonicalCGStep base g k‖≤
      observedCGStepConstant k κ C ((k : ℝ)*(C+K*(C+1))) a K*δ := by
  dsimp only
  intro hs hy hGram hd hA hstep
  let m := gatedMethod fullMemory γ (E := EuclideanSpace ℝ (Fin n))
  let R := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)
  let J := Matrix.toEuclideanCLM (𝕜 := ℝ) (metricRoot base)⁻¹
  let s : Fin k → EuclideanSpace ℝ (Fin n) := fun i => R (probedStep m A B g i.val)
  let y : Fin k → EuclideanSpace ℝ (Fin n) := fun i => J (probedSecant m A B g i.val)
  let G := J (probedGradient m A B g k)
  let d := R (m.direction (methodRun m A B g k))
  have hc := full_observed_solve_from_canonical base hb m A B g k (mul_nonneg hK hδ) hs hy hGram hSolve
  have hcc : IsUnit (crossGram (fun i : Fin k => probedSecant m A B g i.val)
      (fun i : Fin k => probedStep m A B g i.val)).det := by
    rw [full_probed_observed_solve_chronological] at hc
    exact hc
  have hdid : d=R (windowDirection (executedPairs (probedStep m A B g) (probedSecant m A B g) k)
      (probedGradient m A B g k)) := by
    change R (windowDirection (selectedWindow fullMemory (methodRun m A B g k)) _)=_
    rw [fullWindow_methodRun]
    rfl
  have hspan : d+cgOperator base G∈Submodule.span ℝ (Set.range (unitWindow s)) := by
    rw [hdid]
    exact chronological_canonical_direction_span base hb _ _ _ k
  have ho (i : Fin k) : inner ℝ (y i) d=0 := by
    rw [hdid]
    exact chronological_canonical_image_conjugacy base hb _ _ _ k hcc i
  have hg := probed_canonical_gradient_bound base hb m A B g k hδ hδone hC hK hinit hstep hy
  have ht := observedCG_line_step_bound base hb g k s y (canonicalOperator base (A k)) G d
    hμ hκ hC (by positivity) ha hK hspec hinit hpre (fun i => hs i.val i.isLt) hd hspan
    hδ hδone hhalf hGram hGramSmall hProj (fun i => hy i.val i.isLt) ho hA hg (fun i => hstep i.val i.isLt)
  have hline : lineLength G d (canonicalOperator base (A k) d) • d=R (gatedObservedLineStep γ A B g k) := by
    dsimp only [G,d]
    rw [canonicalOperator_primal base hb,canonical_lineLength base hb]
    change _=R (lineLength (probedGradient m A B g k) (m.direction (methodRun m A B g k))
      (A k (m.direction (methodRun m A B g k))) • m.direction (methodRun m A B g k))
    rw [map_smul]
  rw [hline] at ht
  exact ht

end
end krylov.Stability
