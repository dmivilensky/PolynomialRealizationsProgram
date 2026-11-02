import krylov.Methods.SmoothProbedDecisions

set_option autoImplicit false
/-!
Article: main_krylov, apB:lem:filtration, actual primitive raw correction charts.
Use: express a genuine raw correction phase as a true locally fixed finite
program with real C-two input observations and actual primitive regularity.
Source: proved genuine local raw-policy decision agreement, actual complete
history charts and real exact-search field regularity.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Every actual smooth CG-consistent raw correction phase admits a genuine local finite primitive C-two program on its true executed input data.
Use: Every actual smooth CG-consistent raw correction phase admits a genuine local finite primitive C-two program on its true executed input data.
Article: main_krylov, apB:lem:filtration, actual primitive raw correction charts.
Proof: Recover the actual primitive local decisions and real full-history chart. Prepend the genuine post-search gradient, probe and chosen direction; actual local decision equality identifies the entire true correction tree and transfers its primitive regularity. -/
theorem smoothProbed_correction_chart (m : ProbedMethod E) (hm : CGConsistent m)
    (A B : ℝ → ℕ → E →L[ℝ] E) (g : ℝ → E) (N : ℕ)
    (hA : ∀ i<N, ContDiffAt ℝ 2 (fun t => A t i) 0)
    (hB : ∀ i<N, ContDiffAt ℝ 2 (fun t => B t i) 0) (hg : ContDiffAt ℝ 2 g 0)
    (Q : E →L[ℝ] E) (hA0 : A 0=fun _ => Q) (hB0 : B 0=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ i<N, CG.gradient Q (g 0) i≠0) (hsmooth : SmoothProbedCycleAt m 2 Q (g 0) N)
    (k : ℕ) (hk : k<N) :
    let H := fun t => methodRun m (A t) (B t) (g t) k
    let z := fun t => probedProbe m (A t) (B t) (g t) k
    let gp := fun t => searchedGradient (H t).gradient (m.direction (H t)) (z t)
    ∃ n : ℕ, ∃ P : CorrectionProgram E n, ∃ data : ℝ → Fin n → E,
      ContDiffAt ℝ 2 data 0 ∧ P.RegularAt 2 (B 0 k) (gp 0) (data 0) ∧
      ∀ᶠ t in 𝓝 (0 : ℝ), m.correction (H t) (z t)=P.tree (data t) := by
  let H := fun t => methodRun m (A t) (B t) (g t) k
  let z := fun t => probedProbe m (A t) (B t) (g t) k
  let d := fun t => probedDirection m (A t) (B t) (g t) k
  let gp := fun t => searchedGradient (H t).gradient (d t) (z t)
  -- Primitive policy locality is applied to the true raw executed history and its actual search probe.
  obtain ⟨P,hcoef,hmatch⟩ := smoothProbed_decisions m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk
  have hf := smoothProbed_fields_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk
  have hsearch := smoothProbed_search_regular m hm A B g 0 N hA hB hg Q hA0 hB0 hQ hpos hpre hsmooth k hk
  have hgp : ContDiffAt ℝ 2 gp 0 := hsearch.2
  have ht := smoothProbed_trace_regular m hm A B g 0 k
    (fun i hi => hA i (hi.trans hk)) (fun i hi => hB i (hi.trans hk)) hg Q hA0 hB0 hQ hpos
    (fun i hi => hpre i (hi.trans hk)) (hsmooth.mono m hk.le)
  obtain ⟨n,data,hd,he⟩ := ht
  -- The true finite correction inputs retain the real post-search gradient, probe, direction and all past observations.
  let input : ℝ → Fin (n+3) → E := fun t => Fin.cons (gp t) (Fin.cons (z t) (Fin.cons (d t) (data t)))
  have hin : ContDiffAt ℝ 2 input 0 := contDiffAt_pi.mpr
    (Fin.cases hgp (Fin.cases hf.2.1 (Fin.cases hf.1 (fun i => (contDiffAt_pi.mp hd) i))))
  have hcor := hcoef.2
  have hd0 : P.method.direction (H 0)=d 0 := hmatch.self_of_nhds.1.symm
  rw [hd0] at hcor
  have hobs0 : (H 0).observationList=List.ofFn (data 0) := he.self_of_nhds
  change (P.correctionProgram (H 0).observationList.length).RegularAt 2 (B 0 k) (gp 0)
    (Fin.cons (gp 0) (Fin.cons (z 0) (Fin.cons (d 0) (observedArray (H 0).observationList.length (H 0).observationList)))) at hcor
  rw [hobs0,List.length_ofFn,observedArray_ofFn] at hcor
  refine ⟨n+3,P.correctionProgram n,input,hin,hcor,?_⟩
  filter_upwards [he,hmatch] with t ht hp
  rw [hp.2]
  have hdt : P.method.direction (H t)=d t := hp.1.symm
  change (P.correctionProgram (H t).observationList.length).tree
    (Fin.cons (searchedGradient (H t).gradient (P.method.direction (H t)) (z t))
      (Fin.cons (z t) (Fin.cons (P.method.direction (H t))
        (observedArray (H t).observationList.length (H t).observationList))))=_
  rw [hdt,ht,List.length_ofFn,observedArray_ofFn]
end
end krylov.Methods
