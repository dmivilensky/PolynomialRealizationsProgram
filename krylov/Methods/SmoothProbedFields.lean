import krylov.Methods.SmoothTrace
import krylov.Methods.ExecutedProbed
import krylov.Methods.ReferenceProbedSteps
import krylov.Methods.ReferenceSearch
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
Article: main_krylov, apB:lem:filtration and lem:U, genuine smooth raw-method fields.
Use: extract true direction, probe, recorded step and total correction-movement
regularity from the complete actual raw execution and its primitive local
coefficient charts; derive every actual reference search denominator.
Source: proved genuine smooth complete-history charts, actual observed record
coordinates, real global CG consistency and exact line/correction balance.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Reference krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- The real raw probed-method direction read from its actual complete observed history.
Use: The real raw probed-method direction read from its actual complete observed history.
Article: main_krylov, apB:lem:filtration and lem:U, genuine smooth raw-method fields.
Proof: The unknown operator is accessed only by the subsequent true probe. -/
def probedDirection (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  m.direction (methodRun m A B g k)

/-- The actual operator action obtained by the genuine raw method search probe.
Use: The actual operator action obtained by the genuine raw method search probe.
Article: main_krylov, apB:lem:filtration and lem:U, genuine smooth raw-method fields.
Proof: Apply the real segment oracle to the actual chosen direction. -/
def probedProbe (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) : E :=
  A k (probedDirection m A B g k)

/-- A true primitive local smooth finite-cycle representation restricts to every genuine shorter prefix.
Use: A true primitive local smooth finite-cycle representation restricts to every genuine shorter prefix.
Article: main_krylov, apB:lem:filtration and lem:U, genuine smooth raw-method fields.
Proof: Use the same actual finite coefficient programs and restrict their true reached indices. -/
theorem SmoothProbedCycleAt.mono (m : ProbedMethod E) {r : WithTop ℕ∞}
    {Q : E →L[ℝ] E} {g : E} {N M : ℕ} (h : SmoothProbedCycleAt m r Q g N) (hle : M ≤ N) :
    SmoothProbedCycleAt m r Q g M := by
  obtain ⟨P,hcoef,hlocal⟩ := h
  exact ⟨P,fun k hk => hcoef k (hk.trans_le hle),fun k hk => hlocal k (hk.trans_le hle)⟩

/-- The genuine total correction movement is exactly the actual recorded physical step minus the real search displacement.
Use: The genuine total correction movement is exactly the actual recorded physical step minus the real search displacement.
Article: main_krylov, apB:lem:filtration and lem:U, genuine smooth raw-method fields.
Proof: Unfold the actual new record and its true finite correction result. -/
theorem probedPhase_movement (m : ProbedMethod E) (A B : ℕ → E →L[ℝ] E) (g : E) (k : ℕ) :
    (probedPhase m A B g k).movement=probedStep m A B g k-
      lineLength (probedGradient m A B g k) (probedDirection m A B g k) (probedProbe m A B g k) •
        probedDirection m A B g k := by
  change _=(_+(probedPhase m A B g k).movement)-_
  dsimp only [probedGradient,probedDirection,probedProbe]
  abel

/-- Every actual primitive smooth CG-consistent raw prefix has C-r genuine directions, probes, physical recorded steps and total correction movements on its true reference domain.
Use: Every actual primitive smooth CG-consistent raw prefix has C-r genuine directions, probes, physical recorded steps and total correction movements on its true reference domain.
Article: main_krylov, apB:lem:filtration and lem:U, genuine smooth raw-method fields.
Proof: Read real direction/probe/step coordinates from the proved actual complete-history chart. Raw CG consistency gives a positive multiple of the true nonzero CG direction, so its real search denominator is nonzero. The exact actual search/correction balance then gives total correction regularity. -/
theorem smoothProbed_fields_regular (m : ProbedMethod E) (hconsistent : CGConsistent m)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k < N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k < N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ k < N, CG.gradient Q (g x) k≠0) (hsmooth : SmoothProbedCycleAt m r Q (g x) N)
    (k : ℕ) (hk : k < N) :
    ContDiffAt ℝ r (fun p => probedDirection m (A p) (B p) (g p) k) x ∧
    ContDiffAt ℝ r (fun p => probedProbe m (A p) (B p) (g p) k) x ∧
    ContDiffAt ℝ r (fun p => probedStep m (A p) (B p) (g p) k) x ∧
    ContDiffAt ℝ r (fun p => (probedPhase m (A p) (B p) (g p) k).movement) x := by
  -- Extract the actual new record; all primitive-policy and reference-domain premises are discharged by the existing full-history theorem.
  have ht := smoothProbed_trace_regular m hconsistent A B g x (k+1)
    (fun i hi => hA i (by omega)) (fun i hi => hB i (by omega)) hg Q hAx hBx hQ hpos
    (fun i hi => hpre i (by omega)) (hsmooth.mono m (by omega))
  have hd : ContDiffAt ℝ r (fun p => probedDirection m (A p) (B p) (g p) k) x := ht.getD 2
  have hz : ContDiffAt ℝ r (fun p => probedProbe m (A p) (B p) (g p) k) x := ht.getD 3
  have hs : ContDiffAt ℝ r (fun p => probedStep m (A p) (B p) (g p) k) x := ht.getD 4
  have hG := smoothProbed_gradient_regular m hconsistent A B g x k
    (fun i hi => hA i (hi.trans hk)) (fun i hi => hB i (hi.trans hk)) hg Q hAx hBx hQ hpos
    (fun i hi => hpre i (hi.trans hk)) (hsmooth.mono m hk.le)
  -- Derive the real raw search curvature from genuine CG consistency before dividing by it.
  have hcurv : inner ℝ (probedDirection m (A x) (B x) (g x) k) (probedProbe m (A x) (B x) (g x) k)≠0 := by
    dsimp only [probedDirection,probedProbe]
    rw [hAx,hBx]
    exact (quadratic_search_positive m hconsistent Q hQ hpos (g x) k (hpre k hk)).1.ne'
  have hα := (hd.inner ℝ hG).neg.div (hd.inner ℝ hz) hcurv
  refine ⟨hd,hz,hs,?_⟩
  convert! hs.sub (hα.smul hd) using 1
  funext p
  simp only [probedPhase_movement,lineLength,probedGradient,Pi.div_apply,Pi.smul_apply']

/-- The actual exact-search scalar and its real post-search gradient are C-r on every genuine smooth nonstagnating quadratic prefix.
Use: Differentiate the real search before its actual correction protocol.
Article: main_krylov, apB:lem:filtration and lem:U, genuine smooth raw-method fields.
Proof: Extract the actual direction, probe and current gradient regularity. Genuine CG consistency supplies the strictly positive reference curvature needed by the scalar quotient, and the real post-search gradient is its actual scalar-vector update. -/
theorem smoothProbed_search_regular (m : ProbedMethod E) (hconsistent : CGConsistent m)
    (A B : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ) {r : WithTop ℕ∞}
    (hA : ∀ k < N, ContDiffAt ℝ r (fun p => A p k) x)
    (hB : ∀ k < N, ContDiffAt ℝ r (fun p => B p k) x) (hg : ContDiffAt ℝ r g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hBx : B x=fun _ => Q)
    (hQ : Q.toLinearMap.IsSymmetric) (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v))
    (hpre : ∀ k < N, CG.gradient Q (g x) k≠0) (hsmooth : SmoothProbedCycleAt m r Q (g x) N)
    (k : ℕ) (hk : k < N) :
    let α := fun p => lineLength (probedGradient m (A p) (B p) (g p) k)
      (probedDirection m (A p) (B p) (g p) k) (probedProbe m (A p) (B p) (g p) k)
    ContDiffAt ℝ r α x ∧ ContDiffAt ℝ r
      (fun p => probedGradient m (A p) (B p) (g p) k+α p • probedProbe m (A p) (B p) (g p) k) x := by
  -- All three actual search inputs come from the same genuine executed-history chart.
  obtain ⟨hd,hz,_,_⟩ := smoothProbed_fields_regular m hconsistent A B g x N hA hB hg Q hAx hBx hQ hpos hpre hsmooth k hk
  have hG := smoothProbed_gradient_regular m hconsistent A B g x k
    (fun i hi => hA i (hi.trans hk)) (fun i hi => hB i (hi.trans hk)) hg Q hAx hBx hQ hpos
    (fun i hi => hpre i (hi.trans hk)) (hsmooth.mono m hk.le)
  have hcurv : inner ℝ (probedDirection m (A x) (B x) (g x) k) (probedProbe m (A x) (B x) (g x) k)≠0 := by
    dsimp only [probedDirection,probedProbe]
    rw [hAx,hBx]
    exact (quadratic_search_positive m hconsistent Q hQ hpos (g x) k (hpre k hk)).1.ne'
  have hα : ContDiffAt ℝ r (fun p => lineLength (probedGradient m (A p) (B p) (g p) k)
      (probedDirection m (A p) (B p) (g p) k) (probedProbe m (A p) (B p) (g p) k)) x :=
    (hd.inner ℝ hG).neg.div (hd.inner ℝ hz) hcurv
  exact ⟨hα,hG.add (hα.smul hz)⟩
end
end krylov.Methods
