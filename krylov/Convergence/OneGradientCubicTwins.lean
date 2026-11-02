import krylov.Convergence.OneGradientCubicPrefix

/-!
Article: main_krylov, thm:LB, literal indistinguishable scalar cubic twins.
Use: retain the original last-query-dependent missing quadratic curvature
and opposite cubic coefficients for every data-only M1 policy. Equality
of the complete observed histories and unevaluated outputs is derived.
Source: actual Krylov prefix information and the exact hidden polynomial.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Original rank-one curvature/cubic fibre gradient; the scalar objective
is `oneGradientCubicObjective` with the displayed physical base.
Article: thm:LB, f_(b,t). -/
def oneGradientCubicFibreGradient (Q : E →L[ℝ] E) (g a : E) (b t : ℝ) : E → E :=
  oneGradientCubicGradient (Q+b • InnerProductSpace.rankOne ℝ a a) g a t

/-- Exact hidden scalar parameter combination in the actual gradient.
Article: main_krylov, thm:LB, b*pi+t*pi²/2. -/
theorem oneGradientCubicFibreGradient_eq
    (Q : E →L[ℝ] E) (g a : E) (b t : ℝ) (x : E) :
    oneGradientCubicFibreGradient Q g a b t x=
      g+Q x+(b*inner ℝ a x+t/2*(inner ℝ a x)^2) • a := by
  unfold oneGradientCubicFibreGradient oneGradientCubicGradient
  simp only [_root_.add_apply,_root_.smul_apply,InnerProductSpace.rankOne_apply,smul_smul]
  module

/-- Every original fibre parameter has the same genuine nonlinear
prefix before the hidden last coordinate is queried. Article: thm:LB. -/
theorem oneGradientCubicFibre_common_prefix
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g a : E) (b t : ℝ) (N : ℕ)
    (ha : ∀ x∈CG.krylovSpace Q g N,inner ℝ a x=0) :
    oneGradientFunctionRun m (oneGradientCubicFibreGradient Q g a b t) 0 N=
      oneGradientRun m (fun _=>Q) g N := by
  have hzero (x : E) (hx : inner ℝ a x=0) : oneGradientCubicFibreGradient Q g a b t x=g+Q x := by
    rw [oneGradientCubicFibreGradient_eq,hx]
    simp only [mul_zero,zero_pow (by decide : 2≠0),add_zero,zero_smul]
  have h₀ : g+Q 0=oneGradientCubicFibreGradient Q g a b t 0 := by
    rw [hzero 0 (inner_zero_right _)]
  have hquery (i : ℕ) (hi : i<N) :
      (fun x=>g+Q x) (oneGradientFunctionPoint m (fun x=>g+Q x) 0 i+
        m.step (oneGradientFunctionRun m (fun x=>g+Q x) 0 i))=
      oneGradientCubicFibreGradient Q g a b t (oneGradientFunctionPoint m (fun x=>g+Q x) 0 i+
        m.step (oneGradientFunctionRun m (fun x=>g+Q x) 0 i)) := by
    rw [←oneGradientFunctionPoint_succ,oneGradientFunctionPoint_affine]
    exact (hzero _ (ha _ (krylov_space_mono Q g (by omega)
      (one_gradient_displacement_krylov m hm Q g (i+1))))).symm
  have hh := oneGradientFunctionRun_congr m (fun x=>g+Q x) (oneGradientCubicFibreGradient Q g a b t) 0 N h₀ hquery
  exact hh.symm.trans (oneGradientFunctionRun_affine m Q g N)

/-- The next point is selected from the actual common old observations,
without seeing its hidden last returned gradient. Article: thm:LB. -/
def oneGradientLastQuery (m : OneGradientMethod E) (Q : E →L[ℝ] E) (g : E) (N : ℕ) : E :=
  (oneGradientRun m (fun _=>Q) g N).displacement+m.step (oneGradientRun m (fun _=>Q) g N)

/-- Opposite cubic twins have the identical entire scalar transcript,
including the genuine last query. Their parameters depend on that actual
query, as in the original proof. Article: main_krylov, thm:LB. -/
theorem oneGradientCubicTwins_history
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g a : E) (M : ℝ) (N : ℕ)
    (ha : ∀ x∈CG.krylovSpace Q g N,inner ℝ a x=0) :
    let p := inner ℝ a (oneGradientLastQuery m Q g N)
    ∀ sign : ℝ,oneGradientFunctionRun m
      (oneGradientCubicFibreGradient Q g a (-sign*M*p/2) (sign*M)) 0 (N+1)=
        oneGradientRun m (fun _=>Q) g (N+1) := by
  dsimp only
  intro sign
  let p := inner ℝ a (oneGradientLastQuery m Q g N)
  let F := oneGradientCubicFibreGradient Q g a (-sign*M*p/2) (sign*M)
  have hp := oneGradientCubicFibre_common_prefix m hm Q g a (-sign*M*p/2) (sign*M) N ha
  have hlast : F (oneGradientLastQuery m Q g N)=g+Q (oneGradientLastQuery m Q g N) := by
    change oneGradientCubicFibreGradient Q g a (-sign*M*p/2) (sign*M) (oneGradientLastQuery m Q g N)=_
    rw [oneGradientCubicFibreGradient_eq]
    change g+Q (oneGradientLastQuery m Q g N)+(-sign*M*p/2*p+sign*M/2*p^2) • a=_
    rw [show -sign*M*p/2*p+sign*M/2*p^2=0 by ring,zero_smul,add_zero]
  rw [oneGradientFunctionRun,hp,oneGradientRun]
  unfold oneGradientFunctionAdvance oneGradientAdvance
  simp only [zero_add]
  change _= _
  have hg := oneGradientRun_quadratic_gradient m Q g N
  have hgrad : F ((oneGradientRun m (fun _=>Q) g N).displacement+
      m.step (oneGradientRun m (fun _=>Q) g N))=
      (oneGradientRun m (fun _=>Q) g N).gradient+Q (m.step (oneGradientRun m (fun _=>Q) g N)) := by
    change F (oneGradientLastQuery m Q g N)=_
    rw [hlast]
    change g+Q ((oneGradientRun m (fun _=>Q) g N).displacement+m.step (oneGradientRun m (fun _=>Q) g N))=_
    rw [map_add,←add_assoc,←hg]
  dsimp only [F,p] at hgrad
  rw [hgrad]

/-- Every data-only final policy therefore returns exactly the same real
unevaluated point on the two genuine scalar cubic sources.
Article: main_krylov, thm:LB. -/
theorem oneGradientCubicTwins_output
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g a : E) (M : ℝ) (N : ℕ)
    (ha : ∀ x∈CG.krylovSpace Q g N,inner ℝ a x=0) :
    let p := inner ℝ a (oneGradientLastQuery m Q g N)
    ∀ sign : ℝ,oneGradientFunctionOutput m
      (oneGradientCubicFibreGradient Q g a (-sign*M*p/2) (sign*M)) 0 (N+1)=
        m.outputDisplacement (oneGradientRun m (fun _=>Q) g (N+1)) := by
  dsimp only
  intro sign
  rw [oneGradientFunctionOutput,oneGradientFunctionPoint,
    oneGradientCubicTwins_history m hm Q g a M N ha sign,zero_add]
  rfl

end
end krylov.Convergence
