import polyak.Numerics.Parametric.Residual
import LeanCert.Engine.AD.Dyadic

/-!
Article: Appendix B, rigorous parameter-slab enclosures.
Use: bounded-denominator outward rounding replaces rational expression growth;
all values and partial derivatives retain the original expression semantics.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def succeeded (r : EvalResult IntervalDyadic) : Bool :=
  match r with | .ok _ => true | .error _ => false

def outcome (r : EvalResult IntervalDyadic) : IntervalRat :=
  match r with | .ok I => I.toIntervalRat | .error _ => IntervalRat.singleton 0

def dyadicValue (e : Expr) (ρ : IntervalEnv) (cfg : DyadicConfig) : EvalResult IntervalDyadic :=
  evalIntervalDyadicChecked e (toDyadicEnv ρ cfg.precision) cfg

def dyadicDerivative (e : Expr) (ρ : IntervalEnv) (j : ℕ) (cfg : DyadicConfig) :
    EvalResult IntervalDyadic := derivIntervalDyadicCheckedOfRat e ρ j cfg

noncomputable section

theorem dyadicValue_mem (e : Expr) (ρ : IntervalEnv) (cfg : DyadicConfig)
    (hprec : cfg.precision≤0) (x : ℕ → ℝ) (hx : ∀ i,x i∈ρ i)
    (hok : succeeded (dyadicValue e ρ cfg)=true) :
    Expr.eval x e∈outcome (dyadicValue e ρ cfg) := by
  cases he : dyadicValue e ρ cfg with
  | error err => simp [he,succeeded] at hok
  | ok I =>
    apply IntervalDyadic.mem_toIntervalRat.mp
    apply evalIntervalDyadicChecked_correct e x (toDyadicEnv ρ cfg.precision) _ cfg hprec I he
    exact fun i => IntervalDyadic.mem_ofIntervalRat (hx i) cfg.precision hprec

theorem dyadicDerivative_mem (e : Expr) (ρ : IntervalEnv) (j : ℕ) (cfg : DyadicConfig)
    (x : ℕ → ℝ) (hx : ∀ i,x i∈ρ i) (t : ℝ) (ht : t∈ρ j)
    (hok : succeeded (dyadicDerivative e ρ j cfg)=true) :
    deriv (Expr.evalAlong e x j) t∈outcome (dyadicDerivative e ρ j cfg) := by
  cases he : dyadicDerivative e ρ j cfg with
  | error err => simp [he,succeeded] at hok
  | ok I =>
    exact IntervalDyadic.mem_toIntervalRat.mp
      (derivIntervalDyadicCheckedOfRat_correct e x ρ j cfg I t ht hx he)

end

def dyadicJacobian {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cfg : DyadicConfig) :
    Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => outcome (dyadicDerivative (F i) (finBoxEnv (box I X)) j.succ.val cfg)

def dyadicJacobianSucceeded {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cfg : DyadicConfig) : Bool :=
  decide (∀ (i j : Fin n), succeeded (dyadicDerivative (F i) (finBoxEnv (box I X)) j.succ.val cfg)=true)

noncomputable section

theorem dyadicJacobian_mem {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    (I : IntervalRat) (X : Fin n → IntervalRat) (cfg : DyadicConfig)
    (hok : dyadicJacobianSucceeded F I X cfg=true)
    {s : ℝ} {x : Fin n → ℝ} (hs : s∈I) (hx : FinBoxMem x X) (i j : Fin n) :
    jacobian F s x i j∈dyadicJacobian F I X cfg i j := by
  simp only [dyadicJacobianSucceeded,decide_eq_true_eq] at hok
  rw [jacobian_apply F hF]
  exact dyadicDerivative_mem (F i) (finBoxEnv (box I X)) j.succ.val cfg
    (finEnv (embed s x)) (finEnv_mem_finBoxEnv (embed_mem_box hs hx)) (x j)
    (by
      have hb := finEnv_mem_finBoxEnv (embed_mem_box hs hx) j.succ.val
      simpa only [Fin.val_succ,finEnv_embed_succ,dite_eq_left j.isLt] using hb) (hok i j)

end

def dyadicCenterResidual {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (m : Fin n → ℚ) (cfg : DyadicConfig) : Fin n → IntervalRat :=
  fun i => IntervalRat.add
    (outcome (dyadicValue (F i) (pointIntervalEnv (Fin.cons I.midpoint m)) cfg))
    (IntervalRat.mul (IntervalRat.sub I (IntervalRat.singleton I.midpoint))
      (outcome (dyadicDerivative (F i)
        (finBoxEnv (box I (fun j => IntervalRat.singleton (m j)))) 0 cfg)))

def dyadicResidualSucceeded {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (m : Fin n → ℚ) (cfg : DyadicConfig) : Bool :=
  decide (cfg.precision≤0) && decide (∀ i,
    succeeded (dyadicValue (F i) (pointIntervalEnv (Fin.cons I.midpoint m)) cfg)=true ∧
    succeeded (dyadicDerivative (F i)
      (finBoxEnv (box I (fun j => IntervalRat.singleton (m j)))) 0 cfg)=true)

noncomputable section

theorem dyadicCenterResidual_mem {n : ℕ} (F : Fin n → Expr) (hF : ∀ i, ADSupported (F i))
    (I : IntervalRat) (m : Fin n → ℚ) (cfg : DyadicConfig)
    (hok : dyadicResidualSucceeded F I m cfg=true) {s : ℝ} (hs : s∈I) (i : Fin n) :
    system F s (fun j => (m j : ℝ)) i∈dyadicCenterResidual F I m cfg i := by
  simp only [dyadicResidualSucceeded,Bool.and_eq_true,decide_eq_true_eq] at hok
  have hpoint : finEnv (embed (I.midpoint : ℝ) (fun j => (m j : ℝ)))=
      finEnv (fun j : Fin (n+1) => ((Fin.cons (α := fun _ : Fin (n+1) => ℚ)
        I.midpoint m j : ℚ) : ℝ)) := by
    congr 1
    funext j
    refine Fin.cases ?_ (fun k => ?_) j <;> simp [embed]
  unfold system dyadicCenterResidual
  apply meanValue_enclosure (f := fun t => eval (F i) t (fun j => (m j : ℝ))) I.midpoint_mem
  · have hρ : ∀ j, finEnv (embed (I.midpoint : ℝ) (fun k => (m k : ℝ))) j∈
        pointIntervalEnv (Fin.cons I.midpoint m) j := by
      rw [hpoint]
      exact finEnv_ratCast_mem_pointIntervalEnv _
    exact dyadicValue_mem (F i) _ cfg hok.1 _ hρ (hok.2 i).1
  · exact (parameter_differentiable (F i) (hF i) _).differentiableOn
  · intro t ht
    rw [← parameter_evalAlong (F i) t]
    apply dyadicDerivative_mem (F i) _ 0 cfg (finEnv (embed t (fun j => (m j : ℝ))))
      (finEnv_mem_finBoxEnv (embed_mem_box ht (fun j => IntervalRat.mem_singleton (m j)))) t
    · simpa [finBoxEnv,box] using ht
    · exact (hok.2 i).2
  · exact hs

end
end polyak.Numerics.Parametric
