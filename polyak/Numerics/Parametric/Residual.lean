import polyak.Numerics.Parametric.Basic
import polyak.Numerics.Parametric.MeanValue

/-!
Article: Appendix B, F(I,Z₀) ⊆ F(s₀,Z₀)+(I−s₀)F_s(I,Z₀).
Use: the parameter mean-value enclosure retains cancellation at the exact
rational midpoint. All values and derivatives refer to the actual source system.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def centerResidual {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (m : Fin n → ℚ) (cfg : EvalConfig := {}) : Fin n → IntervalRat :=
  fun i => IntervalRat.add
    (LeanCert.Internal.Rational.evalTotalCore (F i) (pointIntervalEnv (Fin.cons I.midpoint m)) cfg)
    (IntervalRat.mul (IntervalRat.sub I (IntervalRat.singleton I.midpoint))
      (Optimization.derivIntervalCoreN (F i)
        (finBoxEnv (box I (fun j => IntervalRat.singleton (m j)))) 0 cfg))

noncomputable section

theorem parameter_evalAlong {n : ℕ} (e : Expr) (s : ℝ) (x : Fin n → ℝ) :
    Expr.evalAlong e (finEnv (embed s x)) 0=(fun t => eval e t x) := by
  funext t
  rw [Expr.evalAlong_eq]
  change Expr.eval (Expr.updateVar (finEnv (embed s x)) 0 t) e=
    Expr.eval (finEnv (embed t x)) e
  congr 1
  funext i
  cases i with
  | zero => simp [Expr.updateVar,finEnv,embed]
  | succ j => simp [Expr.updateVar,finEnv_embed_succ]

theorem parameter_differentiable {n : ℕ} (e : Expr) (h : ADSupported e) (x : Fin n → ℝ) :
    Differentiable ℝ (fun s => eval e s x) := by
  rw [← parameter_evalAlong e 0 x]
  exact evalAlong_differentiable e h _ _

theorem parameter_deriv_mem {n : ℕ} (e : Expr) (h : ADSupported e)
    (I : IntervalRat) (m : Fin n → ℚ) {s : ℝ} (hs : s∈I) (cfg : EvalConfig) :
    deriv (fun t => eval e t (fun j => (m j : ℝ))) s∈
      Optimization.derivIntervalCoreN e
        (finBoxEnv (box I (fun j => IntervalRat.singleton (m j)))) 0 cfg := by
  rw [← parameter_evalAlong e s]
  apply Optimization.evalDualTotalCore_der_correct_idx e h _ _ 0
    (finEnv_mem_finBoxEnv (embed_mem_box hs (fun j => IntervalRat.mem_singleton (m j))))
  simpa [finBoxEnv,box] using hs

theorem centerResidual_mem {n : ℕ} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (I : IntervalRat) (m : Fin n → ℚ) {s : ℝ} (hs : s∈I) (cfg : EvalConfig) (i : Fin n) :
    system F s (fun j => (m j : ℝ)) i∈centerResidual F I m cfg i := by
  have hpoint : finEnv (embed (I.midpoint : ℝ) (fun j => (m j : ℝ)))=
      finEnv (fun j : Fin (n+1) => ((Fin.cons (α := fun _ : Fin (n+1) => ℚ)
        I.midpoint m j : ℚ) : ℝ)) := by
    congr 1
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [embed]
  unfold system centerResidual
  apply meanValue_enclosure (f := fun t => eval (F i) t (fun j => (m j : ℝ))) I.midpoint_mem
  · have hρ : ∀ j, finEnv (embed (I.midpoint : ℝ) (fun k => (m k : ℝ))) j∈
        pointIntervalEnv (Fin.cons I.midpoint m) j := by
      rw [hpoint]
      exact finEnv_ratCast_mem_pointIntervalEnv _
    exact evalIntervalCore_correct (F i) (h i).toCore _ _ hρ cfg
      (LeanCert.Engine.ADSupported.domainValid (h i) _ cfg)
  · exact (parameter_differentiable (F i) (h i) _).differentiableOn
  · exact fun _ hr => parameter_deriv_mem (F i) (h i) I m hr cfg
  · exact hs

end
end polyak.Numerics.Parametric
