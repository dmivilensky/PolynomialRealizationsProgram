import krylov.Envelope.AffineOracleJet
import krylov.Stability.AnalyticCG

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), actual CG recorded-step analytic and affine first jets.
Use: transfer true CG step derivatives from a constructed positive
quadratic shadow to the exact printed affine single-quadratic path.
Source: actual analytic CG gradients and directions, genuine positive
search curvatures and the real Frechet derivative chain rule.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The actual computed CG recorded step is jointly real analytic on its true nonstagnating positive reference domain.
Use: The actual computed CG recorded step is jointly real analytic on its true nonstagnating positive reference domain.
Article: main_krylov, apB:lem:mu(c), actual CG recorded-step analytic and affine first jets.
Proof: Derive genuine analytic gradient, direction and probe functions. The actual reference search curvature is nonzero, so the true rational step length and recorded displacement are analytic. -/
theorem referenceStep_analytic (Q : X → E →L[ℝ] E) (g : X → E) (x : X)
    (haQ : AnalyticAt ℝ Q x) (hag : AnalyticAt ℝ g x)
    (hQ : (Q x).toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q x v)) (k : ℕ)
    (hpre : ∀ i≤k, CG.gradient (Q x) (g x) i≠0) :
    AnalyticAt ℝ (fun p => referenceStep (Q p) (g p) k) x := by
  obtain ⟨hG,hD⟩ := cg_prefix_analytic Q g x haQ hag hQ hpos k (fun i hi => hpre i hi.le)
  have hi := CG.invariant (Q x) hQ hpos (g x) k (fun i hi => hpre i hi.le)
  have hd := (CG.invariant_line_pos (Q x) hpos (g x) k hi (hpre k le_rfl)).1
  have hc : inner ℝ (CG.direction (Q x) (g x) k) (Q x (CG.direction (Q x) (g x) k))≠0 := (hpos _ hd).ne'
  have hZ := analytic_operator_apply haQ hD
  have hα := (analytic_inner hD hG).neg.div (analytic_inner hD hZ) hc
  exact hα.smul hD


/-- The actual CG step derivative on any genuine operator curve equals its true derivative on the literal source affine path with the same real operator first jet.
Use: The actual CG step derivative on any genuine operator curve equals its true derivative on the literal source affine path with the same real operator first jet.
Article: main_krylov, apB:lem:mu(c), actual CG recorded-step analytic and affine first jets.
Proof: Derive actual operator-coordinate differentiability of the genuine CG step, compose its real Frechet derivative with both true operator path derivatives, and identify their equal actual tangents. -/
theorem referenceStep_affine_firstJet (Q D : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ)
    (hpre : ∀ i≤k, CG.gradient Q g i≠0)
    (T : ℝ → E →L[ℝ] E) (hT0 : T 0=Q) (hT : HasDerivAt T D 0) :
    deriv (fun t => referenceStep (T t) g k) 0=
      deriv (fun t => referenceStep (affineOracle Q D t) g k) 0 := by
  -- The genuine CG step has an actual operator-coordinate derivative; both real quadratic paths have the same true base and tangent.
  let f := fun R : E →L[ℝ] E => referenceStep R g k
  have hf : DifferentiableAt ℝ f Q :=
    (referenceStep_analytic id (fun _ => g) Q analyticAt_id analyticAt_const hQ hpos k hpre).differentiableAt
  have h1 : HasFDerivAt f (fderiv ℝ f Q) (T 0) := by rw [hT0];exact hf.hasFDerivAt
  have h2 : HasFDerivAt f (fderiv ℝ f Q) (affineOracle Q D 0) := by
    simp only [affineOracle,zero_smul,add_zero]
    exact hf.hasFDerivAt
  exact (h1.comp_hasDerivAt 0 hT).deriv.trans (h2.comp_hasDerivAt 0 (affineOracle_hasDeriv Q D)).deriv.symm
end
end krylov.Envelope
