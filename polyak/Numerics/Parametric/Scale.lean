import polyak.Numerics.Parametric.Check

/-!
Article: Appendix B, the weighted infinity norm.
Use: an exact affine substitution turns each rational coordinate radius into
a unit-box coordinate. This gives the weighted test without changing a norm instance.
-/
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def substitute (σ : ℕ → Expr) : Expr → Expr
  | .const q => .const q
  | .var i => σ i
  | .add a b => .add (substitute σ a) (substitute σ b)
  | .mul a b => .mul (substitute σ a) (substitute σ b)
  | .neg a => .neg (substitute σ a)
  | .inv a => .inv (substitute σ a)
  | .exp a => .exp (substitute σ a)
  | .sin a => .sin (substitute σ a)
  | .cos a => .cos (substitute σ a)
  | .log a => .log (substitute σ a)
  | .atan a => .atan (substitute σ a)
  | .arsinh a => .arsinh (substitute σ a)
  | .atanh a => .atanh (substitute σ a)
  | .sinc a => .sinc (substitute σ a)
  | .erf a => .erf (substitute σ a)
  | .sinh a => .sinh (substitute σ a)
  | .cosh a => .cosh (substitute σ a)
  | .tanh a => .tanh (substitute σ a)
  | .sqrt a => .sqrt (substitute σ a)
  | .namedConst c => .namedConst c

theorem substitute_supported (σ : ℕ → Expr) (hσ : ∀ i, ADSupported (σ i))
    (e : Expr) (he : ADSupported e) : ADSupported (substitute σ e) := by
  induction he with
  | const q => exact .const q
  | var i => exact hσ i
  | add _ _ ha hb => exact .add ha hb
  | mul _ _ ha hb => exact .mul ha hb
  | neg _ ha => exact .neg ha
  | exp _ ha => exact .exp ha
  | sin _ ha => exact .sin ha
  | cos _ ha => exact .cos ha

noncomputable section

theorem substitute_eval (σ : ℕ → Expr) (e : Expr) (ρ : ℕ → ℝ) :
    Expr.eval ρ (substitute σ e)=Expr.eval (fun i => Expr.eval ρ (σ i)) e := by
  induction e <;> simp_all [substitute,Expr.eval]

def chart {n : ℕ} (c r : Fin n → ℚ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun j => (c j : ℝ)+(r j : ℝ)*x j

end

def scaledVariable {n : ℕ} (c r : Fin n → ℚ) : ℕ → Expr
  | 0 => .var 0
  | j+1 => if h : j<n then .add (.const (c ⟨j,h⟩))
      (.mul (.const (r ⟨j,h⟩)) (.var (j+1))) else .const 0

def scaledSystem {n : ℕ} (F : Fin n → Expr) (c r : Fin n → ℚ) : Fin n → Expr :=
  fun i => substitute (scaledVariable c r) (F i)

theorem scaledVariable_supported {n : ℕ} (c r : Fin n → ℚ) (j : ℕ) :
    ADSupported (scaledVariable c r j) := by
  cases j with
  | zero => exact .var 0
  | succ j =>
    dsimp [scaledVariable]
    split
    · exact .add (.const _) (.mul (.const _) (.var _))
    · exact .const 0

noncomputable section

theorem scaledSystem_eval {n : ℕ} (F : Fin n → Expr) (c r : Fin n → ℚ)
    (s : ℝ) (x : Fin n → ℝ) :
    system (scaledSystem F c r) s x=system F s (chart c r x) := by
  have he : (fun i => Expr.eval (finEnv (embed s x)) (scaledVariable c r i))=
      finEnv (embed s (chart c r x)) := by
    funext i
    cases i with
    | zero => simp [scaledVariable,finEnv,embed]
    | succ j =>
      by_cases hj : j<n
      · simp [scaledVariable,hj,Expr.eval,finEnv_embed_succ,chart]
      · simp [scaledVariable,hj,finEnv_embed_succ]
  ext i
  simp only [system,eval,evalFin,scaledSystem,substitute_eval,he]

end
end polyak.Numerics.Parametric
