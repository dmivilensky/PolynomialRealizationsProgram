import krylov.Envelope.CorrectionObservationJets
import krylov.Methods.SmoothProbedFields
import krylov.Envelope.KrylovFlags

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, genuine corrected and uncorrected search jets.
Use: recover the true post-search first jet from the actual next returned
gradient using the real zero-reference correction and its proved derivative
in the genuine reference Krylov flag.
Source: exact actual correction-gradient balance, true zero-query operator
product differentiation and genuine polynomial Krylov flag growth.
-/

namespace krylov.Envelope
noncomputable section
open krylov.Methods krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The actual post-search gradient jet lies in the genuine following Krylov jet flag whenever the real next returned gradient does and the true correction derivative lies in its proved preceding flag.
Use: The actual post-search gradient jet lies in the genuine following Krylov jet flag whenever the real next returned gradient does and the true correction derivative lies in its proved preceding flag.
Article: main_krylov, apB:lem:filtration, genuine corrected and uncorrected search jets.
Proof: Use the real correction executor balance. Genuine quadratic consistency makes the actual reference correction movement zero, so its actual operator derivative cancels. The true remaining image derivative belongs to the following polynomial Krylov flag and transfers the genuine next-gradient coherence to the actual post-search gradient. -/
theorem actual_postSearch_jet (m : ProbedMethod E) (hm : CGConsistent m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : ℝ → E) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0) (hg : ContDiffAt ℝ 2 g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<N, CG.gradient Q (g 0) i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q (g 0) N)
    (k : ℕ) (hk : k<N) (L : E →ₗ[ℝ] E)
    (hχ : deriv (fun t => (probedPhase m (A t) (B t) (g t) k).movement) 0∈CG.krylovSpace Q (g 0) (k+1))
    (hj : (probedGradient m (A 0) (B 0) (g 0) (k+1),
      deriv (fun t => probedGradient m (A t) (B t) (g t) (k+1)) 0)∈jetSubspace (CG.krylovSpace Q (g 0) (k+2)) L) :
    let gp := fun t => searchedGradient (probedGradient m (A t) (B t) (g t) k)
      (probedDirection m (A t) (B t) (g t) k) (probedProbe m (A t) (B t) (g t) k)
    (gp 0,deriv gp 0)∈jetSubspace (CG.krylovSpace Q (g 0) (k+2)) L := by
  -- Retain the actual total correction movement and true executed post-search and returned gradients.
  let χ := fun t => (probedPhase m (A t) (B t) (g t) k).movement
  let gp := fun t => searchedGradient (probedGradient m (A t) (B t) (g t) k)
    (probedDirection m (A t) (B t) (g t) k) (probedProbe m (A t) (B t) (g t) k)
  let G := fun t => probedGradient m (A t) (B t) (g t) (k+1)
  have hχreg := (smoothProbed_fields_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk).2.2.2
  have hgp : ContDiffAt ℝ 2 gp 0 :=
    (smoothProbed_search_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk).2
  have hG : ContDiffAt ℝ 2 G 0 := smoothProbed_gradient_regular m hm A B g 0 (k+1)
    (fun i hi => hA i (by omega)) (fun i hi => hB i (by omega)) hg Q hA0 hB0 hQ hpos
    (fun i hi => hpre i (by omega)) (hsmooth.mono m (by omega))
  have hz : χ 0=0 := by
    dsimp only [χ,probedPhase]
    rw [hA0,hB0]
    exact (zeroCorrections_change_operator _ Q Q _ (hm Q hQ hpos (g 0) k).choose_spec.2.2).2.1
  have he (t : ℝ) : G t=gp t+B t k (χ t) := runCorrections_gradient _ _ _
  have h0 : gp 0=G 0 := by rw [he,hz,map_zero,add_zero]
  have hdiff : (fun t => gp t-G t)=fun t => -(B t k (χ t)) := by
    funext t
    rw [he]
    abel
  -- The true correction-operator derivative vanishes on the genuine zero reference movement.
  have hd := (zero_query_jet (fun t => B t k) χ (deriv (fun t => B t k) 0) (deriv χ 0) 0
    ((hB k hk).differentiableAt (by norm_num)).hasDerivAt
    (hχreg.differentiableAt (by norm_num)).hasDerivAt hz).neg
  change HasDerivAt (fun t => -(B t k (χ t))) (-(B 0 k (deriv χ 0))) 0 at hd
  have hmem : deriv (fun t => gp t-G t) 0∈CG.krylovSpace Q (g 0) (k+2) := by
    rw [hdiff,hd.deriv,hB0]
    exact Submodule.neg_mem _ (krylovSpace_operator Q (g 0) (k+1) hχ)
  exact jetSubspace_of_difference _ L gp G hgp hG h0 hj hmem
end
end krylov.Envelope
