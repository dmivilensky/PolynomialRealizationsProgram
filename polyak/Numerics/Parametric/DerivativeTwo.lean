import polyak.Numerics.Parametric.Dyadic

/-! Actual parameter partial derivatives and the exact two-dimensional Cramer identity. -/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def parameterDerivative {n : ℕ} (F : Fin n → Expr) (s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => deriv (fun r => eval (F i) r x) s

def determinantTwo (J : Matrix (Fin 2) (Fin 2) ℝ) : ℝ := J 0 0*J 1 1-J 0 1*J 1 0

def cramerNumeratorB (J : Matrix (Fin 2) (Fin 2) ℝ) (p : Fin 2 → ℝ) : ℝ :=
  J 1 0*p 0-J 0 0*p 1

theorem cramer_B (J : Matrix (Fin 2) (Fin 2) ℝ) (p v : Fin 2 → ℝ)
    (h : J.mulVec v= -p) : determinantTwo J*v 1=cramerNumeratorB J p := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_two,Pi.neg_apply] at h0 h1
  unfold determinantTwo cramerNumeratorB
  linear_combination J 0 0*h1-J 1 0*h0

theorem parameterDerivative_mem {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cfg : DyadicConfig)
    (hok : ∀ i, succeeded (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg)=true)
    {s : ℝ} {x : Fin n → ℝ} (hs : s∈I) (hx : FinBoxMem x X) (i : Fin n) :
    parameterDerivative F s x i∈outcome (dyadicDerivative (F i) (finBoxEnv (box I X)) 0 cfg) := by
  unfold parameterDerivative
  rw [← parameter_evalAlong (F i) s x]
  apply dyadicDerivative_mem (F i) (finBoxEnv (box I X)) 0 cfg
    (finEnv (embed s x)) (finEnv_mem_finBoxEnv (embed_mem_box hs hx)) s
  · simpa [finBoxEnv,box] using hs
  · exact hok i

end polyak.Numerics.Parametric
