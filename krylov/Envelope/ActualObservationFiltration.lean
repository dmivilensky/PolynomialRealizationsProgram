import krylov.Envelope.ActualCorrectionJets
import krylov.Envelope.ActualSearchJets
import krylov.Envelope.ActualDirectionJets
import krylov.Envelope.ScalarJets
import krylov.Envelope.GradientJetLift

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, complete actual raw observation filtration.
Use: prove the genuine complete observed-history and actual physical-step
first-jet flags for arbitrary smooth source-admissible globally CG-consistent
raw methods before exhaustion, including every intermediate correction query.
Source: genuine primitive coefficient direction closure, actual correction
moving-span jets, real exact-search probe recovery and true CG gradient
coordinates; no method response or trajectory expansion is assumed.
-/

namespace krylov.Envelope
noncomputable section
open Filter Topology krylov.Methods krylov.Reference krylov.Stability
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual smooth source-admissible globally CG-consistent raw method has the genuine complete-history first-jet filtration and real recorded-step jet coherence before exhaustion.
Use: Every actual smooth source-admissible globally CG-consistent raw method has the genuine complete-history first-jet filtration and real recorded-step jet coherence before exhaustion.
Article: main_krylov, apB:lem:filtration, complete actual raw observation filtration.
Proof: Lift the true actual gradient derivatives on the genuine orthogonal CG gradient prefix. Induct through the complete real observed histories: primitive direction coefficients preserve actual jet flags; real zero-reference corrections have their genuine moving-span derivatives; true next gradients determine actual post-search and probe jets through the nonzero real search scalar. The actual line-plus-correction step preserves the preceding flag, and all genuine intermediate observations and older records form the true next complete history. -/
theorem actual_observation_filtration (memory : ℕ → ℕ) (m : ProbedMethod E)
    (hm : CGConsistent m) (hspan : ProbedSpanRestricted memory m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : ℝ → E) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0) (hg : ContDiffAt ℝ 2 g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i≤N, CG.gradient Q (g 0) i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q (g 0) N) :
    let δg := fun i => deriv (fun t => probedGradient m (A t) (B t) (g t) i) 0
    let L := gradientJetLift Q (g 0) δg N
    JetListAt (jetSubspace (CG.krylovSpace Q (g 0) (N+1)) L)
      (fun t => (methodRun m (A t) (B t) (g t) N).observationList) ∧
      ∀ k<N, (probedStep m (A 0) (B 0) (g 0) k,
        deriv (fun t => probedStep m (A t) (B t) (g t) k) 0)∈
          jetSubspace (CG.krylovSpace Q (g 0) (k+1)) L := by
  -- Use one actual gradient-coordinate lift for the entire true prefix; each genuine earlier flag embeds into the following one.
  let G := fun k t => probedGradient m (A t) (B t) (g t) k
  let δg := fun k => deriv (G k) 0
  let L := gradientJetLift Q (g 0) δg N
  let J := fun k => jetSubspace (CG.krylovSpace Q (g 0) (k+1)) L
  have hact (j : ℕ) : G j 0=CG.gradient Q (g 0) j := by
    dsimp only [G,probedGradient]
    rw [hA0,hB0]
    exact quadratic_gradient_eq_cg m hm Q hQ hpos (g 0) j
  have hline (j : ℕ) (hj : j≤N) : CG.length Q (g 0) j≠0 :=
    (CG.invariant_line_pos Q hpos (g 0) j (CG.invariant Q hQ hpos (g 0) j
      (fun i hi => hpre i (by omega))) (hpre j hj)).2.1.ne'
  have hgrad (j : ℕ) (hj : j≤N) : (G j 0,δg j)∈J j := by
    rw [hact]
    change CG.gradient Q (g 0) j∈CG.krylovSpace Q (g 0) (j+1) ∧
      δg j-L (CG.gradient Q (g 0) j)∈CG.krylovSpace Q (g 0) (j+1)
    constructor
    · rw [CG.krylovSpace_eq_span_gradients Q (g 0) (j+1) (fun i hi => hline i (by omega))]
      exact Submodule.subset_span ⟨j,Nat.lt_succ_self j,rfl⟩
    · rw [gradientJetLift_gradient Q hQ hpos (g 0) δg N hpre j hj,sub_self]
      exact Submodule.zero_mem _
  have hmono {i j : ℕ} (hij : i≤j) : J i≤J j :=
    jetSubspace_mono (krylovSpace_mono Q (g 0) (Nat.add_le_add_right hij 1)) (fun _ _ => rfl)
  have hGreg (j : ℕ) (hj : j≤N) : ContDiffAt ℝ 2 (G j) 0 :=
    smoothProbed_gradient_regular m hm A B g 0 j (fun i hi => hA i (by omega))
      (fun i hi => hB i (by omega)) hg Q hA0 hB0 hQ hpos (fun i hi => hpre i (by omega)) (hsmooth.mono m hj)
  have hinit (n : ℕ) (t : ℝ) : (methodRun m (A t) (B t) (g t) n).initial=g t := by
    induction n with
    | zero => rfl
    | succ n ih => exact ih
  -- Induct through the real complete observed histories while retaining every actual earlier physical-step jet.
  have hprefix (n : ℕ) (hn : n≤N) :
      JetListAt (J n) (fun t => (methodRun m (A t) (B t) (g t) n).observationList) ∧
      ∀ k<n, (probedStep m (A 0) (B 0) (g 0) k,
        deriv (fun t => probedStep m (A t) (B t) (g t) k) 0)∈J k := by
    induction n with
    | zero =>
      have hj : (g 0,deriv g 0)∈J 0 := hgrad 0 (by omega)
      exact ⟨(JetListAt.nil (J 0)).cons hg hj |>.cons hg hj,fun _ hk => (Nat.not_lt_zero _ hk).elim⟩
    | succ k ih =>
      obtain ⟨hhist,hsteps⟩ := ih (by omega)
      have hk : k<N := by omega
      let d := fun t => probedDirection m (A t) (B t) (g t) k
      let z := fun t => probedProbe m (A t) (B t) (g t) k
      let α := fun t => lineLength (G k t) (d t) (z t)
      let χ := fun t => (probedPhase m (A t) (B t) (g t) k).movement
      let gp := fun t => G k t+α t • z t
      have hfields := smoothProbed_fields_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos
        (fun i hi => hpre i hi.le) hsmooth k hk
      have hsearch := smoothProbed_search_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos
        (fun i hi => hpre i hi.le) hsmooth k hk
      have hd : ContDiffAt ℝ 2 d 0 := hfields.1
      have hz : ContDiffAt ℝ 2 z 0 := hfields.2.1
      have hα : ContDiffAt ℝ 2 α 0 := hsearch.1
      have hχ : ContDiffAt ℝ 2 χ 0 := hfields.2.2.2
      -- The actual primitive direction decision preserves the true current observed jet flag.
      have hdjet : (d 0,deriv d 0)∈J k := actual_direction_jet m hm A B g N hA hB hg Q hA0 hB0 hQ hpos
        (fun i hi => hpre i hi.le) hsmooth k hk _ L hhist
      have hcor := actual_correction_jets memory m hm hspan A B g N hA hB hg Q hA0 hB0 hQ hpos
        (fun i hi => hpre i hi.le) hsmooth k hk
      -- Real zero-reference correction derivatives transfer the true next-gradient jet to the actual post-search gradient.
      have hpost : (gp 0,deriv gp 0)∈J (k+1) := actual_postSearch_jet m hm A B g N hA hB hg Q hA0 hB0 hQ hpos
        (fun i hi => hpre i hi.le) hsmooth k hk L hcor.1 (hgrad (k+1) hn)
      have hobs := hcor.2 L hpost
      have hαpos : 0 < α 0 := by
        dsimp only [α,G,d,z,probedGradient,probedDirection,probedProbe]
        rw [hA0,hB0]
        exact (quadratic_search_positive m hm Q hQ hpos (g 0) k (hpre k (by omega))).2
      have hgpD : HasDerivAt gp (δg k+(α 0 • deriv z 0+deriv α 0 • z 0)) 0 :=
        ((hGreg k (by omega)).differentiableAt (by norm_num)).hasDerivAt.add
          ((hα.differentiableAt (by norm_num)).hasDerivAt.smul (hz.differentiableAt (by norm_num)).hasDerivAt)
      -- Recover the genuine probe jet by the actual positive reference search scalar, not by an assumed oracle expansion.
      have hzjet : (z 0,deriv z 0)∈J (k+1) := by
        rw [hgpD.deriv] at hpost
        exact jetSubspace_probe _ L hαpos.ne' (hmono (Nat.le_succ k) (hgrad k (by omega))) hpost
      have hχ0 : χ 0=0 := by
        dsimp only [χ,probedPhase]
        rw [hA0,hB0]
        exact (zeroCorrections_change_operator _ Q Q _ (hm Q hQ hpos (g 0) k).choose_spec.2.2).2.1
      have hsD : HasDerivAt (fun t => probedStep m (A t) (B t) (g t) k)
          (α 0 • deriv d 0+deriv α 0 • d 0+deriv χ 0) 0 :=
        ((hα.differentiableAt (by norm_num)).hasDerivAt.smul (hd.differentiableAt (by norm_num)).hasDerivAt).add
          (hχ.differentiableAt (by norm_num)).hasDerivAt
      have hs0 : probedStep m (A 0) (B 0) (g 0) k=α 0 • d 0 := by
        change α 0 • d 0+χ 0=_
        rw [hχ0,add_zero]
      -- The actual recorded step adds only its genuine vertical zero-reference correction derivative.
      have hsjet : (probedStep m (A 0) (B 0) (g 0) k,
          deriv (fun t => probedStep m (A t) (B t) (g t) k) 0)∈J k := by
        rw [hsD.deriv,hs0]
        exact jetSubspace_line_correction _ L hdjet hcor.1 (α 0) (deriv α 0)
      -- Rebuild the true next history from all real current observations, every intermediate correction pair and the actual old record tail.
      have htail := (hhist.mono (hmono (Nat.le_succ k))).drop 2
      have hrecord := (hobs.append htail).cons (hGreg (k+1) hn) (hgrad (k+1) hn)
      have hrecord := hrecord.cons hfields.2.2.1 (hmono (Nat.le_succ k) hsjet)
      have hrecord := hrecord.cons hz hzjet
      have hrecord := hrecord.cons hd (hmono (Nat.le_succ k) hdjet)
      have hrecord := hrecord.cons hg (hmono (by omega : 0≤k+1) (hgrad 0 (by omega)))
      have hout := hrecord.cons (hGreg (k+1) hn) (hgrad (k+1) hn)
      refine ⟨?_,?_⟩
      · convert! hout using 1
        funext t
        simp only [methodRun,methodAdvance,History.observationList,List.flatMap_cons,
          List.cons_append,List.nil_append,List.drop_succ_cons,List.drop_zero]
        rw [hinit]
        rfl
      · intro i hi
        by_cases he : i=k
        · subst i;exact hsjet
        · exact hsteps i (by omega)
  exact hprefix N le_rfl
end
end krylov.Envelope
