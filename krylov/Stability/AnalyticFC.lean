import krylov.Stability.AnalyticSolve
import krylov.Methods.DirectionReindex

/-!
Article: main_krylov, lem:U(d), actual adaptive full-memory FC regularity.
Use: prove joint local analyticity of the actually executed FC gradients,
directions and steps, with true quadratic model domains discharged from CG.
Source: exact fixed-coordinate form of the actual list solve and finite analytic induction.
-/

namespace krylov.Stability
noncomputable section
open Matrix krylov.Methods krylov.Reference
open scoped InnerProductSpace
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Every genuinely defined finite adaptive FC prefix is analytic in analytic segment operators and initial data.
Use: prove actual trajectory regularity directly from the executed inverse solves and exact searches.
Article: main_krylov, lem:U(d), analytic FC cycle map.
Proof: induct through actual observed histories in their exact finite
coordinates; every model inverse and line denominator is genuinely nonzero at the parameter, and the proved analytic solve calculus propagates each real step and gradient. -/
theorem fc_prefix_analytic (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X) (N : ℕ)
    (hA : ∀ i<N, AnalyticAt ℝ (fun p => A p i) x) (hg : AnalyticAt ℝ g x)
    (hsolve : ∀ k<N, (crossGram (fun i : Fin k => fcSecant fullMemory (A x) (g x) (k-1-i.val))
      (fun i : Fin k => fcStep fullMemory (A x) (g x) (k-1-i.val))).det≠0)
    (hline : ∀ k<N, inner ℝ (fcDirection fullMemory (A x) (g x) k)
      (A x k (fcDirection fullMemory (A x) (g x) k))≠0) :
    AnalyticAt ℝ (fun p => fcGradient fullMemory (A p) (g p) N) x ∧
      ∀ i<N, AnalyticAt ℝ (fun p => fcDirection fullMemory (A p) (g p) i) x ∧
        AnalyticAt ℝ (fun p => fcStep fullMemory (A p) (g p) i) x := by
  -- The induction differentiates the actual adaptive run, with no presumed analytic trajectory field.
  induction N with
  | zero => exact ⟨hg,by intro i hi; omega⟩
  | succ k ih =>
    obtain ⟨hG,hprev⟩ := ih (fun i hi => hA i (by omega))
      (fun i hi => hsolve i (by omega)) (fun i hi => hline i (by omega))
    have hD : AnalyticAt ℝ (fun p => fcDirection fullMemory (A p) (g p) k) x := by
      simp only [fullFC_direction_array]
      apply analytic_conjugacyDirection
      · intro i; exact (hprev _ (by omega)).2
      · intro i
        exact analytic_operator_apply (hA _ (by omega)) (hprev _ (by omega)).2
      · exact hG
      · exact hsolve k (by omega)
    have hZ := analytic_operator_apply (hA k (by omega)) hD
    have hα := (analytic_inner hD hG).neg.div (analytic_inner hD hZ) (hline k (by omega))
    have hS : AnalyticAt ℝ (fun p => fcStep fullMemory (A p) (g p) k) x := hα.smul hD
    constructor
    · simp only [fcGradient_succ]
      exact hG.add (analytic_operator_apply (hA k (by omega)) hS)
    · intro i hi
      by_cases he : i=k
      · subst i; exact ⟨hD,hS⟩
      · exact hprev i (by omega)

/-- The actual full-memory FC quadratic direction and line step are the genuine computed CG quantities.
Use: discharge all real model and search denominators before the adaptive regularity induction.
Article: main_krylov, lem:U(d), nonzero reference denominators.
Proof: the proved actual quadratic transcript determines the observed
gradient and retained solve direction; their true line formula determines the actual physical step. -/
theorem fullFC_reference_step (Q : E →L[ℝ] E) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (g : E) (k : ℕ) :
    fcGradient fullMemory (fun _ => Q) g k=CG.gradient Q g k ∧
      fcDirection fullMemory (fun _ => Q) g k=CG.direction Q g k ∧
      fcStep fullMemory (fun _ => Q) g k=referenceStep Q g k := by
  -- The real quadratic history supplies both arguments of the implemented exact line scalar.
  have hs := fcMethod_static fullMemory Q hQ hpos g (fun _ _ hk => hk) k
  have hd := retainedMethod_direction fullMemory (fun _ _ => CorrectionTree.done) Q hQ hpos g k _ hs.1 hs.2
    (fun _ hk => hk)
  refine ⟨hs.1,hd,?_⟩
  change lineLength (fcGradient fullMemory (fun _ => Q) g k) (fcDirection fullMemory (fun _ => Q) g k)
    (Q (fcDirection fullMemory (fun _ => Q) g k)) • fcDirection fullMemory (fun _ => Q) g k=_
  rw [show fcGradient fullMemory (fun _ => Q) g k=CG.gradient Q g k from hs.1,
    show fcDirection fullMemory (fun _ => Q) g k=CG.direction Q g k from hd]
  rfl

/-- The actual adaptive full-memory FC cycle is jointly analytic near every nonstagnating positive quadratic reference.
Use: source FC regularity is fully discharged for the real policy; analytic operator parameters may encode every canonical increment and reference change.
Article: main_krylov, lem:U(d), r=∞ for FC.
Proof: true quadratic transcript equality supplies every actual reference
step; actual CG conjugate independence makes every real coefficient matrix positive definite, and true CG positive curvature makes every actual line denominator nonzero. The real adaptive analytic induction then applies. -/
theorem quadraticFC_prefix_analytic (A : X → ℕ → E →L[ℝ] E) (g : X → E) (x : X)
    (hA : ∀ i, AnalyticAt ℝ (fun p => A p i) x) (hg : AnalyticAt ℝ g x)
    (Q : E →L[ℝ] E) (hAx : A x=fun _ => Q) (hQ : Q.toLinearMap.IsSymmetric)
    (hpos : ∀ v : E, v≠0 → 0 < inner ℝ v (Q v)) (N : ℕ)
    (hpre : ∀ i<N, CG.gradient Q (g x) i≠0) :
    AnalyticAt ℝ (fun p => fcGradient fullMemory (A p) (g p) N) x ∧
      ∀ i<N, AnalyticAt ℝ (fun p => fcDirection fullMemory (A p) (g p) i) x ∧
        AnalyticAt ℝ (fun p => fcStep fullMemory (A p) (g p) i) x := by
  -- All domain facts below concern the actual quadratic execution and are derived from its true CG invariant.
  apply fc_prefix_analytic A g x N (fun i _ => hA i) hg
  · intro k hk
    rw [hAx]
    have hs : (fun i : Fin k => fcStep fullMemory (fun _ => Q) (g x) (k-1-i.val))=
        fun i => referenceStep Q (g x) (k-1-i.val) :=
      funext fun _ => (fullFC_reference_step Q hQ hpos (g x) _).2.2
    have hy : (fun i : Fin k => fcSecant fullMemory (fun _ => Q) (g x) (k-1-i.val))=
        fun i => Q (referenceStep Q (g x) (k-1-i.val)) := by
      funext i
      change Q (fcStep fullMemory (fun _ => Q) (g x) (k-1-i.val))=_
      rw [(fullFC_reference_step Q hQ hpos (g x) _).2.2]
    rw [hs,hy]
    have hind : LinearIndependent ℝ (fun i : Fin k => referenceStep Q (g x) (k-1-i.val)) := by
      apply reference_window_independent Q hQ hpos (g x) k (fun i hi => hpre i (by omega))
      · intro i j he
        change k-1-i.val=k-1-j.val at he
        apply Fin.ext
        have := i.isLt
        have := j.isLt
        omega
      · intro i; have := i.isLt; omega
    exact (operatorGram_posDef Q hQ hpos hind).det_pos.ne'
  · intro k hk
    rw [hAx,(fullFC_reference_step Q hQ hpos (g x) k).2.1]
    exact (hpos _ (CG.invariant_line_pos Q hpos (g x) k
      (CG.invariant Q hQ hpos (g x) k (fun i hi => hpre i (by omega))) (hpre k hk)).1).ne'

end
end krylov.Stability
