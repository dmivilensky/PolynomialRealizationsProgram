import krylov.Convergence.OneGradientCubicSource

/-!
Article: main_krylov, thm:LB, genuine common scalar-source prefix.
Use: derive exact nonlinear oracle indistinguishability for every original
span-restricted one-gradient policy. No CG consistency, own-step independence,
reference trajectory or common nonlinear transcript is assumed.
Source: genuine polynomial Krylov information and actual scalar executor causality.
-/
namespace krylov.Convergence
noncomputable section
open Set krylov.Methods krylov.Reference krylov.Functions krylov.OneGradient
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- True affine-gradient scalar execution is exactly its genuine quadratic
operator protocol, for every policy and every prefix. Article: thm:LB. -/
theorem oneGradientFunctionRun_affine
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (g : E) (N : ℕ) :
    oneGradientFunctionRun m (fun x=>g+Q x) 0 N=oneGradientRun m (fun _=>Q) g N := by
  induction N with
  | zero=>simp only [oneGradientFunctionRun,oneGradientRun,map_zero,add_zero]
  | succ k ih=>
    rw [oneGradientFunctionRun,ih,oneGradientRun]
    have hg := oneGradientRun_quadratic_gradient m Q g k
    unfold oneGradientFunctionAdvance oneGradientAdvance
    simp only [zero_add,map_add]
    rw [←add_assoc,←hg]

/-- Every real queried affine point is the genuinely executed quadratic
history displacement. Article: thm:LB. -/
theorem oneGradientFunctionPoint_affine
    (m : OneGradientMethod E) (Q : E →L[ℝ] E) (g : E) (i : ℕ) :
    oneGradientFunctionPoint m (fun x=>g+Q x) 0 i=(oneGradientRun m (fun _=>Q) g i).displacement := by
  rw [oneGradientFunctionPoint,oneGradientFunctionRun_affine,zero_add]

/-- Every genuine scalar rank-one cubic has exactly the common quadratic
prefix whenever its hidden axis annihilates the actual Krylov flag. This
holds for the entire original M1 class without any consistency assumption.
Article: main_krylov, thm:LB, first n-1 common coordinate subspaces. -/
theorem oneGradientCubic_common_prefix
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g a : E) (t : ℝ) (N : ℕ)
    (ha : ∀ x∈CG.krylovSpace Q g N,inner ℝ a x=0) :
    oneGradientFunctionRun m (oneGradientCubicGradient Q g a t) 0 N=
      oneGradientRun m (fun _=>Q) g N := by
  have h₀ : g+Q 0=oneGradientCubicGradient Q g a t 0 := by
    simp only [oneGradientCubicGradient,inner_zero_right,zero_pow (by decide : 2≠0),
      mul_zero,zero_smul,add_zero]
  have hquery (i : ℕ) (hi : i<N) :
      (fun x=>g+Q x) (oneGradientFunctionPoint m (fun x=>g+Q x) 0 i+
        m.step (oneGradientFunctionRun m (fun x=>g+Q x) 0 i))=
      oneGradientCubicGradient Q g a t (oneGradientFunctionPoint m (fun x=>g+Q x) 0 i+
        m.step (oneGradientFunctionRun m (fun x=>g+Q x) 0 i)) := by
    rw [←oneGradientFunctionPoint_succ,oneGradientFunctionPoint_affine]
    symm
    apply oneGradientCubicGradient_eq_of_hidden_zero
    exact ha _ (krylov_space_mono Q g (by omega) (one_gradient_displacement_krylov m hm Q g (i+1)))
  have hh := oneGradientFunctionRun_congr m (fun x=>g+Q x) (oneGradientCubicGradient Q g a t) 0 N h₀ hquery
  exact hh.symm.trans (oneGradientFunctionRun_affine m Q g N)

/-- The next genuine query is common to every hidden cubic parameter,
although its returned gradient may reveal the missing mixed parameter.
Article: main_krylov, thm:LB, common last query. -/
theorem oneGradientCubic_next_query_common
    (m : OneGradientMethod E) (hm : OneGradientSpanRestricted m)
    (Q : E →L[ℝ] E) (g a : E) (t s : ℝ) (N : ℕ)
    (ha : ∀ x∈CG.krylovSpace Q g N,inner ℝ a x=0) :
    oneGradientFunctionPoint m (oneGradientCubicGradient Q g a t) 0 (N+1)=
      oneGradientFunctionPoint m (oneGradientCubicGradient Q g a s) 0 (N+1) := by
  rw [oneGradientFunctionPoint_succ,oneGradientFunctionPoint_succ]
  simp only [oneGradientFunctionPoint,
    oneGradientCubic_common_prefix m hm Q g a t N ha,oneGradientCubic_common_prefix m hm Q g a s N ha]

end
end krylov.Convergence
