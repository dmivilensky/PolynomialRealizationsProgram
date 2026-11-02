import krylov.Methods.CorrectionProgram
import krylov.Methods.ObservedListRules
import krylov.Methods.QuadraticConsistency
import krylov.Methods.ExecutedProbed

/-!
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Use: compile primitive observed coefficient direction rules and finite
correction programs into the genuine ProbedMethod executor, and derive
full-cycle C-r regularity of every actual observed vector and returned gradient.
Source: real exact-search calculus, genuine finite correction compilation
and actual complete-history vector charts; trajectory regularity is a conclusion.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A genuine data-only probed policy specified by primitive observed direction coefficients and finite correction programs.
Use: A genuine data-only probed policy specified by primitive observed direction coefficients and finite correction programs.
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Proof: Each correction continuation receives only the actual observed data. -/
structure CompiledProbedPolicy (E : Type*) where
  /-- Primitive coefficients of the true direction on each possible finite observed data dimension. -/
  directionRule : ∀ m, ObservedRule E m
  /-- The actual finite correction schedule on each true observed dimension after search. -/
  correctionProgram : ∀ m, CorrectionProgram E (m+3)

/-- The actual nonanticipating probed method compiled from its primitive coefficient rules.
Use: The actual nonanticipating probed method compiled from its primitive coefficient rules.
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Proof: Perform the actual direction decision and exact search, then execute the real correction program on the true enlarged observations. -/
def CompiledProbedPolicy.method (P : CompiledProbedPolicy E) : ProbedMethod E where
  direction H := listDecision P.directionRule H.observationList
  correction H z :=
    let d := listDecision P.directionRule H.observationList
    let gp := searchedGradient H.gradient d z
    (P.correctionProgram H.observationList.length).tree
      (Fin.cons gp (Fin.cons z (Fin.cons d (observedArray H.observationList.length H.observationList))))

/-- C-r regularity of the actual primitive direction and correction coefficients at their real reached reference observations.
Use: C-r regularity of the actual primitive direction and correction coefficients at their real reached reference observations.
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Proof: This condition contains no trajectory or cycle smoothness premise. -/
def CompiledProbedPolicy.CoefficientsRegularAt (P : CompiledProbedPolicy E) (r : WithTop ℕ∞)
    (H : History E) (A B : E →L[ℝ] E) : Prop :=
  let d := P.method.direction H
  let z := A d
  let gp := searchedGradient H.gradient d z
  ContDiffAt ℝ r (P.directionRule H.observationList.length).coefficient
    (observedArray H.observationList.length H.observationList) ∧
  (P.correctionProgram H.observationList.length).RegularAt r B gp
    (Fin.cons gp (Fin.cons z (Fin.cons d (observedArray H.observationList.length H.observationList))))

/-- A real compiled probed iteration preserves a genuine C-r finite chart of its complete actual observed history.
Use: A real compiled probed iteration preserves a genuine C-r finite chart of its complete actual observed history.
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Proof: Compose the primitive direction rule with the actual history, use the true nonzero exact-search denominator, execute the compiled real correction program and retain all genuine returned observations in the new history. -/
theorem CompiledProbedPolicy.advance_regular (P : CompiledProbedPolicy E)
    (H : X → History E) (A B : X → E →L[ℝ] E) (x : X) {r : WithTop ℕ∞}
    (hH : SmoothListAt r (fun p => (H p).observationList) x)
    (hA : ContDiffAt ℝ r A x) (hB : ContDiffAt ℝ r B x)
    (hcoef : P.CoefficientsRegularAt r (H x) (A x) (B x))
    (hcurv : inner ℝ (P.method.direction (H x)) (A x (P.method.direction (H x)))≠0) :
    SmoothListAt r (fun p => (methodAdvance P.method (A p) (B p) (H p)).observationList) x := by
  -- Real observed-list charts fix the coefficient dimension before the actual next query.
  let v := fun p => (H p).observationList
  have hd : ContDiffAt ℝ r (fun p => P.method.direction (H p)) x :=
    listDecision_contDiffAt P.directionRule v x hH hcoef.1
  have hg : ContDiffAt ℝ r (fun p => (H p).gradient) x := by
    simpa only [History.observationList_gradient] using hH.getD 0
  have hinit : ContDiffAt ℝ r (fun p => (H p).initial) x := by
    simpa only [History.observationList_initial] using hH.getD 1
  have hz := hA.clm_apply hd
  have hα : ContDiffAt ℝ r (fun p => lineLength (H p).gradient (P.method.direction (H p))
      (A p (P.method.direction (H p)))) x := (hd.inner ℝ hg).neg.div (hd.inner ℝ hz) hcurv
  have hline := hα.smul hd
  have hgp := hg.add (hα.smul hz)
  obtain ⟨m,data,hdata,he⟩ := hH
  have hcor := hcoef.2
  have he0 : (H x).observationList=List.ofFn (data x) := he.self_of_nhds
  rw [he0,List.length_ofFn,observedArray_ofFn] at hcor
  let input : X → Fin (m+3) → E := fun p => Fin.cons
    (searchedGradient (H p).gradient (P.method.direction (H p)) (A p (P.method.direction (H p))))
    (Fin.cons (A p (P.method.direction (H p))) (Fin.cons (P.method.direction (H p)) (data p)))
  have hin : ContDiffAt ℝ r input x :=
    contDiffAt_pi.mpr (Fin.cases hgp (Fin.cases hz (Fin.cases hd (fun i => (contDiffAt_pi.mp hdata) i))))
  -- Regularity of every correction is derived by executing its actual finite observed program.
  have hrun := (P.correctionProgram m).run_regular B _ input x hB hgp hin hcor
  let actual := fun p => runCorrections (P.method.correction (H p) (A p (P.method.direction (H p)))) (B p)
    (searchedGradient (H p).gradient (P.method.direction (H p)) (A p (P.method.direction (H p))))
  let localRun := fun p => runCorrections ((P.correctionProgram m).tree (input p)) (B p)
    (searchedGradient (H p).gradient (P.method.direction (H p)) (A p (P.method.direction (H p))))
  have heq : actual=ᶠ[𝓝 x] localRun := by
    filter_upwards [he] with p hp
    dsimp only [actual,localRun,input,CompiledProbedPolicy.method]
    rw [hp,List.length_ofFn,observedArray_ofFn]
  have hm : ContDiffAt ℝ r (fun p => (actual p).movement) x := hrun.1.congr_of_eventuallyEq (heq.mono fun _ hp => congrArg CorrectionResult.movement hp)
  have hr : ContDiffAt ℝ r (fun p => (actual p).gradient) x := hrun.2.1.congr_of_eventuallyEq (heq.mono fun _ hp => congrArg CorrectionResult.gradient hp)
  have ht : SmoothListAt r (fun p => correctionObservations (actual p).trace) x := by
    obtain ⟨k,d,hreg,hEq⟩ := hrun.2.2
    refine ⟨k,d,hreg,?_⟩
    filter_upwards [heq,hEq] with p hp hq
    rw [hp]
    exact hq
  have htail : SmoothListAt r (fun p => (H p).observationList.drop 2) x := (show SmoothListAt r v x from ⟨m,data,hdata,he⟩).drop 2
  have hrecord := SmoothListAt.cons hd (SmoothListAt.cons hz (SmoothListAt.cons (hline.add hm)
    (SmoothListAt.cons hr (ht.append htail))))
  have hout := SmoothListAt.cons hr (SmoothListAt.cons hinit hrecord)
  convert! hout using 1

/-- Every genuinely defined finite compiled probed cycle has a C-r chart of its complete actual observation history.
Use: Every genuinely defined finite compiled probed cycle has a C-r chart of its complete actual observation history.
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Proof: Induct through the real executor using the proved actual one-iteration theorem; the initial actual data consists of the true initial gradient. -/
theorem CompiledProbedPolicy.run_regular (P : CompiledProbedPolicy E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (hcoef : ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k))
    (hcurv : ∀ k<N, inner ℝ (P.method.direction (methodRun P.method (A x) (B x) (g x) k))
      (A x k (P.method.direction (methodRun P.method (A x) (B x) (g x) k)))≠0) :
    SmoothListAt r (fun p => (methodRun P.method (A p) (B p) (g p) N).observationList) x := by
  -- The induction preserves the complete genuine history, including intermediate correction observations.
  induction N with
  | zero => exact SmoothListAt.cons hg (SmoothListAt.cons hg (SmoothListAt.nil r x))
  | succ k ih =>
    have hp := ih (fun j hj => hA j (by omega)) (fun j hj => hB j (by omega))
      (fun j hj => hcoef j (by omega)) (fun j hj => hcurv j (by omega))
    exact P.advance_regular _ _ _ x hp (hA k (by omega)) (hB k (by omega)) (hcoef k (by omega)) (hcurv k (by omega))


/-- Every CG-consistent compiled probed method with actual C-r coefficients has genuine C-r full-cycle observations near a nonstagnating quadratic reference.
Use: Every CG-consistent compiled probed method with actual C-r coefficients has genuine C-r full-cycle observations near a nonstagnating quadratic reference.
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Proof: CG consistency gives the actual positive CG direction scale. True CG positivity discharges every real search curvature; the proved actual execution induction then uses only primitive coefficient regularity. -/
theorem CompiledProbedPolicy.quadratic_run_regular (P : CompiledProbedPolicy E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hconsistent : CGConsistent P.method) (hpre : ∀ k<N, CG.gradient Q (g x) k≠0)
    (hcoef : ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k)) :
    SmoothListAt r (fun p => (methodRun P.method (A p) (B p) (g p) N).observationList) x := by
  -- The genuine quadratic reference supplies every actual search denominator.
  apply P.run_regular A B g x N hA hB hg hcoef
  intro k hk
  rw [hAx,hBx]
  obtain ⟨c,hc,hd,_⟩ := hconsistent Q hQ hpos (g x) k
  have hn : CG.direction Q (g x) k≠0 := (CG.invariant_line_pos Q hpos (g x) k
    (CG.invariant Q hQ hpos (g x) k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).1
  rw [hd,map_smul,real_inner_smul_left,real_inner_smul_right]
  exact mul_ne_zero hc.ne' (mul_ne_zero hc.ne' (hpos _ hn).ne')

/-- The actual returned gradient of a genuinely smooth compiled probed cycle is C-r.
Use: The actual returned gradient of a genuinely smooth compiled probed cycle is C-r.
Article: main_krylov, def:classes and lem:U(d), actual smooth probed-policy execution.
Proof: Read its true first observed-history coordinate. -/
theorem CompiledProbedPolicy.gradient_regular (P : CompiledProbedPolicy E)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (htrace : SmoothListAt r (fun p => (methodRun P.method (A p) (B p) (g p) N).observationList) x) :
    ContDiffAt ℝ r (fun p => probedGradient P.method (A p) (B p) (g p) N) x := by
  simpa only [History.observationList_gradient,probedGradient] using htrace.getD 0

end
end krylov.Methods
