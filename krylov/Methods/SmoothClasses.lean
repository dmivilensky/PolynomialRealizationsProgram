import krylov.Methods.LocalPolicyCharts
import krylov.Methods.Classes

/-!
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Use: define smoothness of actual raw probed policies by primitive local
observed coefficient programs, allowing optional locally fixed correction
branches, and derive true cycle regularity from CG consistency and those coefficients.
Source: genuine observed-vector local charts, actual complete-history
execution equality and positive true CG search curvatures.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [InnerProductSpace ℝ E] in
/-- Every actual finite observed list is exactly its genuine coordinate-array reconstruction.
Use: Every actual finite observed list is exactly its genuine coordinate-array reconstruction.
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Proof: Read the true finite coordinates and use the actual finite-list reconstruction identity. -/
theorem ofFn_observedArray (v : List E) : List.ofFn (observedArray v.length v)=v := by
  have hdata : observedArray v.length v=v.get := by
    funext i
    simp only [observedArray,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem i.isLt,Option.getD_some,List.get_eq_getElem]
  rw [hdata,List.ofFn_get]

omit [InnerProductSpace ℝ E] in
/-- Every true local observed-data decision property holds at the actual reference history and probe.
Use: Every true local observed-data decision property holds at the actual reference history and probe.
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Proof: The genuine finite observation array presents the actual history, and its true reference point belongs to its neighborhood. -/
theorem ObservedLocalAt.self {H : History E} {z : E} {predicate : History E → E → Prop}
    (h : ObservedLocalAt H z predicate) : predicate H z := by
  obtain ⟨V,hV,hm⟩ := h H.observationList.length (observedArray H.observationList.length H.observationList)
    (ofFn_observedArray H.observationList).symm
  exact hm _ (mem_of_mem_nhds hV) H rfl (ofFn_observedArray H.observationList).symm

/-- A raw locally compiled policy and the actual compiled finite program have identical genuine reference histories.
Use: A raw locally compiled policy and the actual compiled finite program have identical genuine reference histories.
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Proof: The real reference observed decisions coincide; finite actual execution induction preserves every true record. -/
theorem localCompiled_reference_run (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (A B : ℕ → E →L[ℝ] E) (g : E) (N : ℕ)
    (hlocal : ∀ k<N, LocalCompiledAt m P (methodRun P.method A B g k)
      (A k (P.method.direction (methodRun P.method A B g k)))) :
    methodRun m A B g N=methodRun P.method A B g N := by
  -- Compare the genuine reference decisions before advancing the actual complete histories.
  induction N with
  | zero => rfl
  | succ k ih =>
    have he := ih (fun j hj => hlocal j (by omega))
    have hmatch := (hlocal k (by omega)).self
    have hc : m.correction (methodRun P.method A B g k) (A k (P.method.direction (methodRun P.method A B g k)))=
      P.method.correction (methodRun P.method A B g k) (A k (P.method.direction (methodRun P.method A B g k))) := hmatch.2
    rw [methodRun,methodRun,he]
    dsimp only [methodAdvance]
    rw [hmatch.1,hc]

/-- CG consistency of the actual raw policy discharges every real search curvature of its genuine local compiled reference.
Use: CG consistency of the actual raw policy discharges every real search curvature of its genuine local compiled reference.
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Proof: True reference histories agree. The actual raw policy direction is a positive CG multiple, whose genuine curvature is positive; actual local direction equality transfers the result. -/
theorem localCompiled_quadratic_curvatures (m : ProbedMethod E) (P : CompiledProbedPolicy E)
    (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (N : ℕ) (hconsistent : CGConsistent m)
    (hpre : ∀ k<N, CG.gradient Q g k≠0)
    (hlocal : ∀ k<N, LocalCompiledAt m P (methodRun P.method (fun _ => Q) (fun _ => Q) g k)
      (Q (P.method.direction (methodRun P.method (fun _ => Q) (fun _ => Q) g k)))) :
    ∀ k<N, inner ℝ (P.method.direction (methodRun P.method (fun _ => Q) (fun _ => Q) g k))
      (Q (P.method.direction (methodRun P.method (fun _ => Q) (fun _ => Q) g k)))≠0 := by
  -- The actual raw CG-consistent direction fixes the true curvature of its local compiled decision.
  intro k hk
  have he := localCompiled_reference_run m P (fun _ => Q) (fun _ => Q) g k (fun j hj => hlocal j (hj.trans hk))
  have hd := (hlocal k hk).self.1
  rw [← hd,← he]
  obtain ⟨c,hc,hdir,_⟩ := hconsistent Q hQ hpos g k
  have hn : CG.direction Q g k≠0 := (CG.invariant_line_pos Q hpos g k
    (CG.invariant Q hQ hpos g k (fun i hi => hpre i (hi.trans hk))) (hpre k hk)).1
  rw [hdir,map_smul,real_inner_smul_left,real_inner_smul_right]
  exact mul_ne_zero hc.ne' (mul_ne_zero hc.ne' (hpos _ hn).ne')

/-- Primitive local observed coefficient programs represent the actual finite probed cycle near its true quadratic reference.
Use: Primitive local observed coefficient programs represent the actual finite probed cycle near its true quadratic reference.
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Proof: Only primitive coefficient C-r regularity and genuine local decision agreement are required, without a trajectory regularity assumption. -/
def SmoothProbedCycleAt (m : ProbedMethod E) (r : WithTop ℕ∞) (Q : E →L[ℝ] E) (g : E) (N : ℕ) : Prop :=
  ∃ P : CompiledProbedPolicy E,
    (∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (fun _ => Q) (fun _ => Q) g k) Q Q) ∧
    ∀ k<N, LocalCompiledAt m P (methodRun P.method (fun _ => Q) (fun _ => Q) g k)
      (Q (P.method.direction (methodRun P.method (fun _ => Q) (fun _ => Q) g k)))

/-- The actual smooth CG-consistent probed information class with primitive C-two observed coefficient charts.
Use: The actual smooth CG-consistent probed information class with primitive C-two observed coefficient charts.
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Proof: It extends the genuine nonanticipating span-restricted raw class and requires finite local primitive representations on active quadratic cycles. -/
structure SmoothProbedClass (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends ProbedClass E where
  /-- The real raw policy is globally CG-consistent on every true positive quadratic reference. -/
  consistent : CGConsistent policy
  /-- Primitive local observed C-two coefficients represent every true active finite quadratic cycle. -/
  smooth : ∀ (Q : E →L[ℝ] E), Q.toLinearMap.IsSymmetric →
    (∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) → ∀ (g : E) (N : ℕ),
      (∀ k<N, CG.gradient Q g k≠0) → SmoothProbedCycleAt policy 2 Q g N

/-- Every genuinely smooth CG-consistent raw probed policy has a real C-r returned-gradient cycle near its actual nonstagnating quadratic reference.
Use: Every genuinely smooth CG-consistent raw probed policy has a real C-r returned-gradient cycle near its actual nonstagnating quadratic reference.
Article: main_krylov, def:classes and lem:U(d), genuine smooth raw information classes.
Proof: Choose its actual primitive local coefficient chart, derive every real compiled curvature from raw CG consistency, prove the true compiled history regular and transfer the genuine local complete-history execution equality. -/
theorem smoothProbed_gradient_regular (m : ProbedMethod E) (hconsistent : CGConsistent m)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k<N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k<N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ k<N, CG.gradient Q (g x) k≠0) (hsmooth : SmoothProbedCycleAt m r Q (g x) N) :
    ContDiffAt ℝ r (fun p => (methodRun m (A p) (B p) (g p) N).gradient) x := by
  -- Primitive coefficient regularity is the input; real cycle regularity is derived after actual domain transfer.
  obtain ⟨P,hcoef,hlocal⟩ := hsmooth
  have hcurv := localCompiled_quadratic_curvatures m P Q hQ hpos (g x) N hconsistent hpre hlocal
  have hcoef' : ∀ k<N, P.CoefficientsRegularAt r (methodRun P.method (A x) (B x) (g x) k) (A x k) (B x k) := by
    simpa only [hAx,hBx] using hcoef
  have hcurv' : ∀ k<N, inner ℝ (P.method.direction (methodRun P.method (A x) (B x) (g x) k))
      (A x k (P.method.direction (methodRun P.method (A x) (B x) (g x) k)))≠0 := by
    simpa only [hAx,hBx] using hcurv
  have hlocal' : ∀ k<N, LocalCompiledAt m P (methodRun P.method (A x) (B x) (g x) k)
      (A x k (P.method.direction (methodRun P.method (A x) (B x) (g x) k))) := by
    simpa only [hAx,hBx] using hlocal
  exact localCompiled_gradient_regular m P A B g x N (P.run_regular A B g x N hA hB hg hcoef' hcurv')
    (localCompiled_methodRun m P A B g x N hA hB hg hcoef' hcurv' hlocal')
end
end krylov.Methods
