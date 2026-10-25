import polyak.CertifiedExamples.Exact313.GeometryCode

/-! Every finite reserve is related to its actual Hermite-quadratic formula. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open LeanCert.Core LeanCert.Engine Numerics.Parametric General Levels ModeLocking.TwoLag

namespace Code

def environment (r : ℝ) : ℕ→ℝ := finEnv (embed Real.pi ![r])

theorem eval_cosine (r : ℝ) (n : ℚ) :
    Expr.eval (environment r) (cosine n)=Real.cos ((n:ℝ)*Real.pi/13) := by
  simp only [cosine,Expr.eval_cos,Expr.eval_mul,Expr.eval_const,Expr.eval_var]
  change Real.cos (((n/13 : ℚ):ℝ)*Real.pi)=_
  push_cast
  congr 1
  ring

theorem eval_numerator (ρ : ℕ→ℝ) (r c : Expr) :
    Expr.eval ρ (numerator r c)=Exact313.numerator (Expr.eval ρ r) (Expr.eval ρ c) := by
  simp only [numerator,Expr.eval_mul,Expr.eval_add,Expr.eval_sub,Expr.eval_const,Expr.eval_pow]
  norm_num [Exact313.numerator]

theorem eval_denominator (ρ : ℕ→ℝ) (r c : Expr) :
    Expr.eval ρ (denominator r c)=Exact313.denominator (Expr.eval ρ r) (Expr.eval ρ c) := by
  simp only [denominator,Expr.eval_mul,Expr.eval_add,Expr.eval_const,Expr.eval_pow]
  norm_num [Exact313.denominator]

theorem eval_numeratorD (ρ : ℕ→ℝ) (r c : Expr) :
    Expr.eval ρ (numeratorD r c)=Exact313.numeratorD (Expr.eval ρ r) (Expr.eval ρ c) := by
  simp only [numeratorD,Expr.eval_mul,Expr.eval_add,Expr.eval_sub,Expr.eval_const,Expr.eval_pow]
  norm_num [Exact313.numeratorD]

theorem eval_denominatorD (ρ : ℕ→ℝ) (r c : Expr) :
    Expr.eval ρ (denominatorD r c)=Exact313.denominatorD (Expr.eval ρ r) (Expr.eval ρ c) := by
  simp only [denominatorD,Expr.eval_mul,Expr.eval_add,Expr.eval_const]
  norm_num [Exact313.denominatorD]

theorem eval_derivativeNumerator (ρ : ℕ→ℝ) (r c : Expr) :
    Expr.eval ρ (derivativeNumerator r c)=
      Exact313.derivativeNumerator (Expr.eval ρ r) (Expr.eval ρ c) := by
  simp only [derivativeNumerator,Expr.eval_mul,Expr.eval_sub,
    eval_numerator,eval_denominator,eval_numeratorD,eval_denominatorD]
  rfl

theorem eval_psi (ρ : ℕ→ℝ) (r c : Expr) :
    Expr.eval ρ (psi r c)=Psi 4 (Expr.eval ρ r) (Expr.eval ρ c) := by
  rw [psi,Expr.eval_div,eval_numerator,eval_denominator,psi_four]

theorem eval_psiD (ρ : ℕ→ℝ) (r c : Expr)
    (h : Exact313.denominator (Expr.eval ρ r) (Expr.eval ρ c)≠0) :
    Expr.eval ρ (psiD r c)=deriv (Psi 4 (Expr.eval ρ r)) (Expr.eval ρ c) := by
  rw [psiD,Expr.eval_div,eval_derivativeNumerator,Expr.eval_pow,eval_denominator,
    psi_four_deriv h]

theorem eval_variable (r : ℝ) : Expr.eval (environment r) (.var 1)=r := rfl

theorem eval_quadratic {r : ℝ} (hr : 0≤r) :
    Expr.eval (environment r) quadratic=(hermiteQuadratic 4 r c₁ c₂).c2 := by
  have h₁ := (Exact313.denominator_pos hr ⟨c₁_mem.1.le,c₁_mem.2.le⟩).ne'
  have harg : Expr.eval (environment r) (cosine 6)=c₁ := by
    simpa [c₁,u] using eval_cosine r 6
  simp only [quadratic,Expr.eval_div,Expr.eval_sub,Expr.eval_mul,Expr.eval_pow,
    eval_psi,eval_cosine,eval_variable]
  rw [eval_psiD _ _ _ (by simpa only [eval_variable,harg] using h₁),harg,eval_variable]
  norm_num [hermiteQuadratic,c₁,c₂,u,v]

theorem eval_psiD_first {r : ℝ} (hr : 0≤r) :
    Expr.eval (environment r) (psiD (.var 1) (cosine 6))=deriv (Psi 4 r) c₁ := by
  have harg : Expr.eval (environment r) (cosine 6)=c₁ := by
    simpa [c₁,u] using eval_cosine r 6
  rw [eval_psiD _ _ _ (by
    rw [eval_variable,harg]
    exact (Exact313.denominator_pos hr ⟨c₁_mem.1.le,c₁_mem.2.le⟩).ne'),
    eval_variable,harg]

theorem eval_linear {r : ℝ} (hr : 0≤r) :
    Expr.eval (environment r) linear=(hermiteQuadratic 4 r c₁ c₂).c1 := by
  simp only [linear,Expr.eval_sub,Expr.eval_mul,Expr.eval_const,
    eval_psiD_first hr,eval_quadratic hr,eval_cosine]
  norm_num [hermiteQuadratic,c₁,u]

theorem eval_constant {r : ℝ} (hr : 0≤r) :
    Expr.eval (environment r) constant=(hermiteQuadratic 4 r c₁ c₂).c0 := by
  simp only [constant,Expr.eval_add,Expr.eval_sub,Expr.eval_mul,Expr.eval_pow,
    eval_psi,eval_variable,eval_psiD_first hr,eval_quadratic hr,eval_cosine]
  norm_num [hermiteQuadratic,c₁,u]

theorem eval_xi {r : ℝ} (hr : 0≤r) (e : Expr) :
    Expr.eval (environment r) (xi e)=
      (hermiteQuadratic 4 r c₁ c₂).eval (Expr.eval (environment r) e) := by
  simp only [xi,Expr.eval_add,Expr.eval_mul,Expr.eval_pow,
    eval_constant hr,eval_linear hr,eval_quadratic hr]
  rfl

theorem eval_angle (r : ℝ) (j : ℚ) :
    Expr.eval (environment r) (angle j)=2*Real.pi*(j:ℝ)/13 := by
  simp only [angle,Expr.eval_mul,Expr.eval_const,Expr.eval_var]
  change (((2*j/13:ℚ):ℝ)*Real.pi)=_
  push_cast
  ring

theorem eval_sine (r : ℝ) (j : ℚ) :
    Expr.eval (environment r) (sine j)=Real.sin (2*Real.pi*(j:ℝ)/13) := by
  rw [sine,Expr.eval_sin,eval_angle]

theorem eval_cosineAt (r : ℝ) (j : ℚ) :
    Expr.eval (environment r) (cosineAt j)=Real.cos (2*Real.pi*(j:ℝ)/13) := by
  rw [cosineAt,Expr.eval_cos,eval_angle]

end Code
end polyak.CertifiedExamples.Exact313
