import polyak.CertifiedExamples.Exact313.Tuning
import polyak.CertifiedExamples.Exact313.LocationCode

/-! Extending the source evaluator by independently enclosed inverse coordinates. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels LeanCert.Core LeanCert.Engine Numerics.Parametric

private theorem eval_congr_vars (e : Expr) (ρ σ : ℕ→ℝ)
    (h : ∀i∈e.freeVars,ρ i=σ i) : Expr.eval ρ e=Expr.eval σ e := by
  induction e <;> simp_all [Expr.freeVars,Expr.eval]

theorem eval_first_two (e : Expr) (he : e.freeVars⊆{0,1}) (ρ : ℕ→ℝ)
    (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar) :
    Expr.eval ρ e=Expr.eval (Code.environment rStar) e := by
  apply eval_congr_vars
  intro i hi
  have h := he hi
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl
  · exact h0
  · exact h1

theorem quadratic_vars : Code.quadratic.freeVars⊆{0,1} := by decide +kernel
theorem linear_vars : Code.linear.freeVars⊆{0,1} := by decide +kernel
theorem constant_vars : Code.constant.freeVars⊆{0,1} := by decide +kernel

theorem eval_inverse_quadratic (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar) :
    Expr.eval ρ Code.quadratic=CStar.c2 := by
  rw [eval_first_two _ quadratic_vars ρ h0 h1,Code.eval_quadratic scalarRoot_positive.le]

theorem eval_inverse_linear (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar) :
    Expr.eval ρ Code.linear=CStar.c1 := by
  rw [eval_first_two _ linear_vars ρ h0 h1,Code.eval_linear scalarRoot_positive.le]

theorem eval_inverse_constant (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar) :
    Expr.eval ρ Code.constant=CStar.c0 := by
  rw [eval_first_two _ constant_vars ρ h0 h1,Code.eval_constant scalarRoot_positive.le]

theorem eval_secular (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar) (e : Expr) :
    Expr.eval ρ (Code.secularAt e)=
      Chart.secular (-CStar.c2) CStar.c1 (-CStar.c2-CStar.c0) (Expr.eval ρ e) := by
  simp only [Code.secularAt,Expr.eval_sub,Expr.eval_add,Expr.eval_div,Expr.eval_mul,
    Expr.eval_pow,Expr.eval_neg,Expr.eval_const,Expr.eval_inv,
    eval_inverse_quadratic ρ h0 h1,eval_inverse_linear ρ h0 h1,eval_inverse_constant ρ h0 h1]
  norm_num [Chart.secular]

theorem eval_normalizedB (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar)
    (h2 : ρ 2=Chart.stableRoot coefficientPoint) :
    Expr.eval ρ Code.normalizedB=Chart.normalizedB coefficientPoint := by
  simp only [Code.normalizedB,Expr.eval_inv,Expr.eval_add,Expr.eval_mul,
    Expr.eval_var,Expr.eval_const,eval_inverse_quadratic ρ h0 h1,h2]
  norm_num [Chart.normalizedB,coefficientPoint]

theorem eval_normalizedA (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar)
    (h2 : ρ 2=Chart.stableRoot coefficientPoint) (h3 : ρ 3=Chart.normalizedU coefficientPoint) :
    Expr.eval ρ Code.normalizedA=Chart.normalizedA coefficientPoint := by
  simp only [Code.normalizedA,Code.normalizedU,Expr.eval_div,Expr.eval_mul,
    Expr.eval_var,eval_inverse_linear ρ h0 h1,eval_normalizedB ρ h0 h1 h2,h3]
  rfl

theorem eval_beta (ρ : ℕ→ℝ) (h3 : ρ 3=Chart.normalizedU coefficientPoint) :
    Expr.eval ρ Code.beta=qStar.beta := by
  simp only [Code.beta,Code.normalizedU,Expr.eval_div,Expr.eval_sub,Expr.eval_add,
    Expr.eval_const,Expr.eval_var,h3]
  norm_num [qStar,Chart.inverseBeta]

theorem eval_sourceA (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar)
    (h2 : ρ 2=Chart.stableRoot coefficientPoint) (h3 : ρ 3=Chart.normalizedU coefficientPoint) :
    Expr.eval ρ Code.sourceA=Chart.inverseA coefficientPoint := by
  simp only [Code.sourceA,Expr.eval_mul,Expr.eval_sub,Expr.eval_const,eval_beta ρ h3,
    eval_normalizedA ρ h0 h1 h2 h3]
  norm_num [Chart.inverseA,qStar]

theorem eval_sourceB (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar)
    (h2 : ρ 2=Chart.stableRoot coefficientPoint) (h3 : ρ 3=Chart.normalizedU coefficientPoint) :
    Expr.eval ρ Code.sourceB=Chart.inverseB coefficientPoint := by
  simp only [Code.sourceB,Expr.eval_mul,Expr.eval_sub,Expr.eval_const,eval_beta ρ h3,
    eval_normalizedB ρ h0 h1 h2]
  norm_num [Chart.inverseB,qStar]

theorem eval_sourceX (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar)
    (h2 : ρ 2=Chart.stableRoot coefficientPoint) (h3 : ρ 3=Chart.normalizedU coefficientPoint) :
    Expr.eval ρ Code.sourceX=qStar.x := by
  simp only [Code.sourceX,Expr.eval_sub,Expr.eval_add,Expr.eval_const,eval_beta ρ h3,
    eval_sourceA ρ h0 h1 h2 h3,eval_sourceB ρ h0 h1 h2 h3]
  norm_num [qStar,Chart.inverseX]

theorem eval_sourceY (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar)
    (h2 : ρ 2=Chart.stableRoot coefficientPoint) (h3 : ρ 3=Chart.normalizedU coefficientPoint) :
    Expr.eval ρ Code.sourceY=qStar.y := by
  simp only [Code.sourceY,Expr.eval_sub,Expr.eval_add,Expr.eval_const,eval_beta ρ h3,
    eval_sourceA ρ h0 h1 h2 h3,eval_sourceB ρ h0 h1 h2 h3]
  norm_num [qStar,Chart.inverseY]

theorem eval_sourceKappa (ρ : ℕ→ℝ) (h0 : ρ 0=Real.pi) (h1 : ρ 1=rStar)
    (h2 : ρ 2=Chart.stableRoot coefficientPoint) (h3 : ρ 3=Chart.normalizedU coefficientPoint) :
    Expr.eval ρ Code.sourceKappa=qStar.kappa := by
  rw [Code.sourceKappa,Expr.eval_div,eval_sourceX ρ h0 h1 h2 h3,eval_sourceY ρ h0 h1 h2 h3]
  dsimp [Tuning.x]
  field_simp [qStar.kappa_pos.ne',qStar.y_pos.ne']

end polyak.CertifiedExamples.Exact313
