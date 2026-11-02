import krylov.Envelope.FiniteObservationJets
import krylov.Envelope.FiniteStepJets

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:mu(c), literal affine single-quadratic information first jet.
Use: identify true observed first derivatives on a constructed positive
quadratic shadow with the exact printed affine quadratic operator path.
Source: actual finite observation derivative transfer and the genuine
Frechet chain rule on true primitive smooth operator coordinates.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Reference krylov.Methods
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The literal source affine single-quadratic operator path with its true physical perturbation direction.
Use: The literal source affine single-quadratic operator path with its true physical perturbation direction.
Article: main_krylov, apB:lem:mu(c), literal affine single-quadratic information first jet.
Proof: Add the actual real scalar times the genuine physical perturbation operator. -/
def affineOracle (Q D : E →L[ℝ] E) (t : ℝ) : E →L[ℝ] E := Q+t • D

/-- The literal affine quadratic operator path has its true supplied physical perturbation derivative.
Use: The literal affine quadratic operator path has its true supplied physical perturbation derivative.
Article: main_krylov, apB:lem:mu(c), literal affine single-quadratic information first jet.
Proof: Differentiate the actual constant plus the genuine scalar-operator product. -/
theorem affineOracle_hasDeriv (Q D : E →L[ℝ] E) : HasDerivAt (affineOracle Q D) D 0 := by
  convert! (hasDerivAt_const (0 : ℝ) Q).add ((hasDerivAt_id (0 : ℝ)).smul_const D) using 1
  simp only [zero_add,one_smul]

/-- Every genuine static-method observation coordinate on a real quadratic shadow has exactly the true first derivative on the literal source affine quadratic path with the same actual operator first jet.
Use: Every genuine static-method observation coordinate on a real quadratic shadow has exactly the true first derivative on the literal source affine quadratic path with the same actual operator first jet.
Article: main_krylov, apB:lem:mu(c), literal affine single-quadratic information first jet.
Proof: Use the actual primitive-derived full-observation first-jet transfer for constant-in-iteration real operator paths, with their genuine equal reference inputs and true tangent operators. -/
theorem static_observation_affine_firstJet (m : ProbedMethod E) (hm : CGConsistent m)
    (Q D : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (g : E) (N : ℕ) (hpre : ∀ k<N, CG.gradient Q g k≠0) (hsmooth : SmoothProbedCycleAt m 2 Q g N)
    (T : ℝ → E →L[ℝ] E) (hT0 : T 0=Q) (hT : HasDerivAt T D 0) (j : ℕ) :
    deriv (fun t => (methodRun m (fun _ => T t) (fun _ => T t) g N).observationList.getD j 0) 0=
      deriv (fun t => (methodRun m (fun _ => affineOracle Q D t) (fun _ => affineOracle Q D t) g N).observationList.getD j 0) 0 := by
  -- The two real single-quadratic paths share their actual base operator and true perturbation tangent at every genuine iteration.
  apply actual_observation_firstJet_transfer m hm Q hQ hpos g N hpre hsmooth
    (fun t _ => T t) (fun t _ => T t) (fun t _ => affineOracle Q D t) (fun t _ => affineOracle Q D t)
    (fun _ => D) (fun _ => D)
  · exact funext (fun _ => hT0)
  · exact funext (fun _ => hT0)
  · funext i
    simp only [affineOracle,zero_smul,add_zero]
  · funext i
    simp only [affineOracle,zero_smul,add_zero]
  · exact fun _ _ => hT
  · exact fun _ _ => hT
  · exact fun _ _ => affineOracle_hasDeriv Q D
  · exact fun _ _ => affineOracle_hasDeriv Q D
end
end krylov.Envelope
