import krylov.Methods.OneGradient
import chebyshev1.Nonlinear.AveragedHessian

/-!
Article: main_krylov, thm:V, thm:LB and prop:EL, scalar one-gradient execution.
Use: execute every policy against the true function gradient, retain its
literal one-query transcript, and derive the segment-operator representation
by the fundamental theorem of calculus. The unevaluated output remains
absent from the observations and is used only in the semantic theorem.
Source: the source's one-gradient protocol and the Bochner fundamental theorem.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods chebyshev1.Nonlinear
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- One genuine gradient query at the displacement chosen from the old
observations. Article: main_krylov, def:classes(M₁), thm:V. -/
def oneGradientFunctionAdvance (m : OneGradientMethod E) (G : E → E) (x₀ : E)
    (H : History E) : History E :=
  let s := m.step H
  ⟨H.initial,⟨0,0,s,G (x₀+H.displacement+s),[]⟩::H.records⟩

/-- The actual scalar-source execution of an arbitrary one-gradient
policy. Only the gradient at each evaluated point enters the record.
Article: main_krylov, def:classes(M₁), thm:V and thm:LB. -/
def oneGradientFunctionRun (m : OneGradientMethod E) (G : E → E) (x₀ : E) : ℕ → History E
  | 0=>⟨G x₀,[]⟩
  | k+1=>oneGradientFunctionAdvance m G x₀ (oneGradientFunctionRun m G x₀ k)

/-- The true evaluated point of the scalar run. Article: thm:V. -/
def oneGradientFunctionPoint (m : OneGradientMethod E) (G : E → E) (x₀ : E) (k : ℕ) : E :=
  x₀+(oneGradientFunctionRun m G x₀ k).displacement

/-- The true unevaluated point, using only the actual final history.
Article: thm:V, thm:LB and prop:EL. -/
def oneGradientFunctionOutput (m : OneGradientMethod E) (G : E → E) (x₀ : E) (N : ℕ) : E :=
  oneGradientFunctionPoint m G x₀ N+m.output (oneGradientFunctionRun m G x₀ N)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The next true evaluated point is obtained by the one actual chosen
step. Article: main_krylov, one-gradient protocol. -/
theorem oneGradientFunctionPoint_succ (m : OneGradientMethod E) (G : E → E) (x₀ : E) (i : ℕ) :
    oneGradientFunctionPoint m G x₀ (i+1)=
      oneGradientFunctionPoint m G x₀ i+m.step (oneGradientFunctionRun m G x₀ i) := by
  simp only [oneGradientFunctionPoint,oneGradientFunctionRun,oneGradientFunctionAdvance,
    History.displacement,List.map_cons,List.sum_cons]
  abel

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Every observed gradient is the true gradient at its recorded point.
Article: thm:V; proof by the actual query recursion. -/
theorem oneGradientFunctionRun_gradient (m : OneGradientMethod E) (G : E → E) (x₀ : E) (k : ℕ) :
    (oneGradientFunctionRun m G x₀ k).gradient=G (oneGradientFunctionPoint m G x₀ k) := by
  cases k with
  | zero=>simp only [oneGradientFunctionRun,History.gradient,oneGradientFunctionPoint,
      History.displacement,List.map_nil,List.sum_nil,add_zero]
  | succ k=>simp only [oneGradientFunctionRun,oneGradientFunctionAdvance,History.gradient,
      oneGradientFunctionPoint,History.displacement,List.map_cons,List.sum_cons]
            congr 1
            abel

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Actual scalar execution contributes exactly one evaluated record per
iteration, with no output query. Article: thm:V, original counting rule. -/
theorem oneGradientFunctionRun_cost (m : OneGradientMethod E) (G : E → E) (x₀ : E) (N : ℕ) :
    oneGradientCost (oneGradientFunctionRun m G x₀ N)=N+1 := by
  have hlen : ∀ k,(oneGradientFunctionRun m G x₀ k).records.length=k := by
    intro k
    induction k with
    | zero=>rfl
    | succ k ih=>exact congrArg Nat.succ ih
  rw [oneGradientCost,hlen,Nat.add_comm]

/-- The actual Hessian average on a real evaluated step.
Article: thm:V, A_l, and prop:EL. -/
def oneGradientFunctionOperator (m : OneGradientMethod E) (G : E → E)
    (H : E → E →L[ℝ] E) (x₀ : E) (i : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (oneGradientFunctionPoint m G x₀ i)
    (m.step (oneGradientFunctionRun m G x₀ i))

/-- The true averaged Hessian on the semantic, unevaluated final segment.
This operator is never supplied to the policy. Article: thm:V and prop:EL. -/
def oneGradientFunctionOutputOperator (m : OneGradientMethod E) (G : E → E)
    (H : E → E →L[ℝ] E) (x₀ : E) (N : ℕ) : E →L[ℝ] E :=
  averagedDerivative H (oneGradientFunctionPoint m G x₀ N)
    (m.output (oneGradientFunctionRun m G x₀ N))

/-- The semantic output gradient is the true function gradient at the
unevaluated point, by a genuine segment FTC. No output is an observation.
Article: main_krylov, thm:V, thm:LB and prop:EL. -/
theorem oneGradientFunctionOutput_gradient (m : OneGradientMethod E) (G : E → E)
    (H : E → E →L[ℝ] E) (x₀ : E) (N : ℕ)
    (hH : ContinuousOn (fun t : ℝ=>H (oneGradientFunctionPoint m G x₀ N+
      t • m.output (oneGradientFunctionRun m G x₀ N))) (Icc 0 1))
    (hG : ∀ t∈Icc (0:ℝ) 1, HasFDerivAt G
      (H (oneGradientFunctionPoint m G x₀ N+t • m.output (oneGradientFunctionRun m G x₀ N)))
      (oneGradientFunctionPoint m G x₀ N+t • m.output (oneGradientFunctionRun m G x₀ N))) :
    m.outputGradient (oneGradientFunctionOutputOperator m G H x₀ N)
      (oneGradientFunctionRun m G x₀ N)=G (oneGradientFunctionOutput m G x₀ N) := by
  have hs := averagedDerivative_apply G H (oneGradientFunctionPoint m G x₀ N)
    (m.output (oneGradientFunctionRun m G x₀ N)) hH hG
  rw [←oneGradientFunctionRun_gradient m G x₀ N] at hs
  change _+_= _
  change (oneGradientFunctionRun m G x₀ N).gradient+
    averagedDerivative H (oneGradientFunctionPoint m G x₀ N)
      (m.output (oneGradientFunctionRun m G x₀ N)) (m.output (oneGradientFunctionRun m G x₀ N))=_
  rw [hs,add_sub_cancel]
  rfl

/-- True scalar-query execution equals the abstract operator protocol
with its genuine segment averages. The hypotheses concern derivatives on
the true query segments; they follow from local smoothness once those
segments have been enclosed. Article: thm:V, thm:LB and prop:EL. -/
theorem oneGradientFunctionRun_eq (m : OneGradientMethod E) (G : E → E)
    (H : E → E →L[ℝ] E) (x₀ : E) (N : ℕ)
    (hH : ∀ i<N, ContinuousOn (fun t : ℝ=>H (oneGradientFunctionPoint m G x₀ i+
      t • m.step (oneGradientFunctionRun m G x₀ i))) (Icc 0 1))
    (hG : ∀ i<N, ∀ t∈Icc (0:ℝ) 1, HasFDerivAt G
      (H (oneGradientFunctionPoint m G x₀ i+t • m.step (oneGradientFunctionRun m G x₀ i)))
      (oneGradientFunctionPoint m G x₀ i+t • m.step (oneGradientFunctionRun m G x₀ i))) :
    oneGradientFunctionRun m G x₀ N=
      oneGradientRun m (oneGradientFunctionOperator m G H x₀) (G x₀) N := by
  induction N with
  | zero=>rfl
  | succ k ih=>
    have he := ih (fun i hi=>hH i (by omega)) (fun i hi=>hG i (by omega))
    have hs := averagedDerivative_apply G H (oneGradientFunctionPoint m G x₀ k)
      (m.step (oneGradientFunctionRun m G x₀ k)) (hH k (by omega)) (hG k (by omega))
    rw [oneGradientFunctionRun,oneGradientRun,←he]
    unfold oneGradientFunctionAdvance oneGradientAdvance
    rw [←oneGradientFunctionRun_gradient m G x₀ k] at hs
    simp only [oneGradientFunctionOperator]
    congr 3
    dsimp only [oneGradientFunctionPoint] at hs
    exact (eq_sub_iff_add_eq.mp hs).symm.trans (by
      dsimp only [oneGradientFunctionPoint]
      exact add_comm _ _)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- Two true gradient oracles that agree on the real queried transcript
produce the identical final observations, for every data-only policy.
The final output itself need not be queried. Article: thm:LB. -/
theorem oneGradientFunctionRun_congr (m : OneGradientMethod E) (G F : E → E)
    (x₀ : E) (N : ℕ) (h₀ : G x₀=F x₀)
    (hquery : ∀ i<N, G (oneGradientFunctionPoint m G x₀ i+
      m.step (oneGradientFunctionRun m G x₀ i))=
      F (oneGradientFunctionPoint m G x₀ i+m.step (oneGradientFunctionRun m G x₀ i))) :
    oneGradientFunctionRun m G x₀ N=oneGradientFunctionRun m F x₀ N := by
  induction N with
  | zero=>exact congrArg (fun g=>(⟨g,[]⟩ : History E)) h₀
  | succ k ih=>
    have he := ih (fun i hi=>hquery i (by omega))
    rw [oneGradientFunctionRun,oneGradientFunctionRun,←he]
    simp only [oneGradientFunctionAdvance]
    rw [show G (x₀+(oneGradientFunctionRun m G x₀ k).displacement+
      m.step (oneGradientFunctionRun m G x₀ k))=
      F (x₀+(oneGradientFunctionRun m G x₀ k).displacement+
      m.step (oneGradientFunctionRun m G x₀ k)) from hquery k (by omega)]

end
end krylov.Convergence
