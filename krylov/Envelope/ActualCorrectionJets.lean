import krylov.Methods.SmoothCorrectionChart
import krylov.Methods.ProbedStepBasis
import krylov.Envelope.CorrectionObservationJets

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, genuine raw correction jet flags.
Use: derive actual correction-movement and complete intermediate-observation
first-jet flags for every smooth source-admissible globally CG-consistent
raw method, from its real executed primitive coefficient programs.
Source: actual local raw correction charts, genuine full-step basis
independence and true polynomial Krylov operator propagation.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology Matrix krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual smooth admissible globally CG-consistent raw correction phase has its genuine movement derivative in the true next Krylov flag and all real intermediate jets in the following flag whenever its actual incoming gradient jet lies there.
Use: Every actual smooth admissible globally CG-consistent raw correction phase has its genuine movement derivative in the true next Krylov flag and all real intermediate jets in the following flag whenever its actual incoming gradient jet lies there.
Article: main_krylov, apB:lem:filtration, genuine raw correction jet flags.
Proof: Extract the genuine local finite correction program on actual raw observations. Derive both actual nonsingular reference Grams from genuine CG step independence, enlarge the true retained query span and apply the real zero-reference moving-span derivative theorem. Transfer the actual complete query trace by true local execution equality. -/
theorem actual_correction_jets (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : ℝ → E) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0) (hg : ContDiffAt ℝ 2 g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<N, CG.gradient Q (g 0) i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q (g 0) N)
    (k : ℕ) (hk : k<N) :
    let gp := fun t => searchedGradient (probedGradient m (A t) (B t) (g t) k)
      (probedDirection m (A t) (B t) (g t) k) (probedProbe m (A t) (B t) (g t) k)
    deriv (fun t => (probedPhase m (A t) (B t) (g t) k).movement) 0∈CG.krylovSpace Q (g 0) (k+1) ∧
      ∀ L : E →ₗ[ℝ] E, (gp 0,deriv gp 0)∈jetSubspace (CG.krylovSpace Q (g 0) (k+2)) L →
        JetListAt (jetSubspace (CG.krylovSpace Q (g 0) (k+2)) L)
          (fun t => correctionObservations (probedPhase m (A t) (B t) (g t) k).trace) := by
  let gp := fun t => searchedGradient (probedGradient m (A t) (B t) (g t) k)
    (probedDirection m (A t) (B t) (g t) k) (probedProbe m (A t) (B t) (g t) k)
  let s := fun t => probedStepBasis m (A t) (B t) (g t) k
  -- Obtain a primitive program for the actual raw correction tree, with no assumed response formula.
  obtain ⟨n,P,data,hd,hP,he⟩ := smoothProbed_correction_chart m hm A B g N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk
  have hs := smoothProbed_stepBasis_regular m hm A B g N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk
  have hgp : ContDiffAt ℝ 2 gp 0 :=
    (smoothProbed_search_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk).2
  have hzero : ZeroCorrections (P.tree (data 0)) (B 0 k) (gp 0) := by
    rw [← he.self_of_nhds]
    dsimp only [gp,probedGradient,probedDirection,probedProbe]
    rw [hA0,hB0]
    exact (hm Q hQ hpos (g 0) k).choose_spec.2.2
  have hS : ∀ᶠ t in 𝓝 (0 : ℝ), (P.tree (data t)).InSubspace (Submodule.span ℝ (Set.range (s t))) := by
    filter_upwards [he] with t ht
    rw [← ht]
    exact correction_in_fullStepSpan memory m hspan (A t) (B t) (g t) k
  -- Genuine quadratic consistency and CG conjugacy supply both actual reference Gram domains.
  have hGr : (crossGram (s 0) (s 0)).det≠0 ∧
      (crossGram (fun i => B 0 k (s 0 i)) (fun i => B 0 k (s 0 i))).det≠0 := by
    simpa only [s,hA0,hB0] using probedStepBasis_gram m hm Q hQ hpos (g 0) k (fun i hi => hpre i (by omega))
  have hK : Submodule.span ℝ (Set.range (s 0))≤CG.krylovSpace Q (g 0) (k+1) := by
    simpa only [s,hA0,hB0] using quadratic_stepBasis_mem m hm Q hQ hpos (g 0) k (fun i hi => hpre i (by omega))
  have hBK : Submodule.span ℝ (Set.range fun i => B 0 k (s 0 i))≤CG.krylovSpace Q (g 0) (k+2) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    rw [hB0]
    exact krylovSpace_operator Q (g 0) (k+1) (hK (Submodule.subset_span ⟨i,rfl⟩))
  -- Transfer real movements and every genuine intermediate observation through the true local tree equality.
  have hR : (fun t => probedPhase m (A t) (B t) (g t) k)=ᶠ[𝓝 (0 : ℝ)]
      fun t => runCorrections (P.tree (data t)) (B t k) (gp t) := by
    filter_upwards [he] with t ht
    dsimp only [probedPhase]
    dsimp only [probedProbe,probedDirection] at ht
    rw [ht]
    rfl
  have hM : (fun t => (probedPhase m (A t) (B t) (g t) k).movement)=ᶠ[𝓝 (0 : ℝ)]
      fun t => (runCorrections (P.tree (data t)) (B t k) (gp t)).movement :=
    hR.mono fun t ht => congrArg CorrectionResult.movement ht
  have hj := correction_program_zero_jets P (fun t => B t k) gp data s (hB k hk) hgp hd
    (contDiffAt_pi.mp hs) hP hzero hS hGr.1 hGr.2
  refine ⟨?_,?_⟩
  · rw [hM.deriv_eq]
    exact hK hj.1
  · intro L hgj
    have hobs := correction_program_observation_jets (CG.krylovSpace Q (g 0) (k+2)) L P
      (fun t => B t k) gp data s (hB k hk) hgp hd (contDiffAt_pi.mp hs) hP hzero hS hGr.1 hGr.2
      (hK.trans (krylovSpace_mono Q (g 0) (by omega))) hBK hgj
    apply hobs.congr
    exact hR.mono fun t ht => congrArg (fun R : CorrectionResult E => correctionObservations R.trace) ht
end
end krylov.Envelope
