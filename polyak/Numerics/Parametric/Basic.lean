import LeanCert.Engine.RootFinding.Krawczyk

/-!
Article: Appendix B, parametric Krawczyk continuation.
Use: variable zero is the real parameter and the remaining variables are the
unknown coordinates.  Differentiation is with respect to the unknowns only.
-/
noncomputable section
namespace polyak.Numerics.Parametric
open LeanCert.Core LeanCert.Engine

def embed {n : ℕ} (s : ℝ) (x : Fin n → ℝ) : Fin (n+1) → ℝ := Fin.cons s x

theorem finEnv_embed_succ {n : ℕ} (s : ℝ) (x : Fin n → ℝ) (j : ℕ) :
    finEnv (embed s x) (j+1)=(if h : j<n then x ⟨j,h⟩ else 0) := by
  by_cases hj : j<n
  · have hi : j+1<n+1 := by omega
    simp only [finEnv,dite_eq_left hi,dite_eq_left hj]
    change (embed s x) (Fin.succ ⟨j,hj⟩)=x ⟨j,hj⟩
    exact Fin.cons_succ (α := fun _ : Fin (n+1) => ℝ) s x ⟨j,hj⟩
  · have hi : ¬j+1<n+1 := by omega
    simp [finEnv,hi,hj]

def inclusion {n : ℕ} : (Fin n → ℝ) →L[ℝ] (Fin (n+1) → ℝ) :=
  ContinuousLinearMap.pi (Fin.cons 0 (fun j => ContinuousLinearMap.proj j))

theorem inclusion_apply {n : ℕ} (x : Fin n → ℝ) : inclusion x=embed 0 x := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [inclusion,embed]

theorem embed_hasFDerivAt {n : ℕ} (s : ℝ) (x : Fin n → ℝ) :
    HasFDerivAt (embed s) inclusion x := by
  apply hasFDerivAt_pi.mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa [embed,inclusion] using
      (hasFDerivAt_const (𝕜 := ℝ) (c := s) (x := x))
  · have hj : HasFDerivAt (fun x : Fin n → ℝ => x j) (ContinuousLinearMap.proj j) x :=
      (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).hasFDerivAt
    simpa [embed,inclusion] using hj

def eval {n : ℕ} (e : Expr) (s : ℝ) (x : Fin n → ℝ) : ℝ := evalFin e (embed s x)

def system {n : ℕ} (F : Fin n → Expr) (s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => eval (F i) s x

theorem eval_differentiable {n : ℕ} (e : Expr) (h : ADSupported e) (s : ℝ) :
    Differentiable ℝ (eval (n := n) e s) :=
  (evalFin_differentiable e h).comp (fun x => (embed_hasFDerivAt s x).differentiableAt)

theorem system_differentiable {n : ℕ} (F : Fin n → Expr)
    (h : ∀ i, ADSupported (F i)) (s : ℝ) : Differentiable ℝ (system F s) :=
  differentiable_pi.mpr (fun i => eval_differentiable (F i) (h i) s)

theorem inclusion_single {n : ℕ} (j : Fin n) :
    inclusion (Pi.single j (1 : ℝ))=Pi.single j.succ 1 := by
  rw [inclusion_apply]
  ext i
  refine Fin.cases ?_ (fun k => ?_) i <;> simp [embed,Pi.single_apply]

theorem eval_fderiv_single {n : ℕ} (e : Expr) (h : ADSupported e)
    (s : ℝ) (x : Fin n → ℝ) (j : Fin n) :
    fderiv ℝ (eval e s) x (Pi.single j 1)=
      deriv (Expr.evalAlong e (finEnv (embed s x)) j.succ.val) (x j) := by
  have hc := ((evalFin_differentiable e h).differentiableAt.hasFDerivAt).comp x
    (embed_hasFDerivAt s x)
  change HasFDerivAt (eval e s) _ x at hc
  rw [hc.fderiv]
  change fderiv ℝ (evalFin e) (embed s x) (inclusion (Pi.single j 1))=_
  rw [inclusion_single, fderiv_single_eq_deriv_evalAlong e h]
  rfl

def jacobian {n : ℕ} (F : Fin n → Expr) (s : ℝ) (x : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ := LinearMap.toMatrix' (fderiv ℝ (system F s) x).toLinearMap

theorem jacobian_apply {n : ℕ} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (s : ℝ) (x : Fin n → ℝ) (i j : Fin n) :
    jacobian F s x i j=
      deriv (Expr.evalAlong (F i) (finEnv (embed s x)) j.succ.val) (x j) := by
  rw [jacobian,LinearMap.toMatrix'_apply]
  change fderiv ℝ (system F s) x (Pi.single j 1) i=_
  rw [show system F s=(fun x i => eval (F i) s x) from rfl]
  rw [fderiv_pi (fun i => (eval_differentiable (F i) (h i) s).differentiableAt)]
  simp only [ContinuousLinearMap.coe_pi']
  exact eval_fderiv_single (F i) (h i) s x j

def box {n : ℕ} (I : IntervalRat) (X : Fin n → IntervalRat) :
    Fin (n+1) → IntervalRat := Fin.cons I X

theorem embed_mem_box {n : ℕ} {I : IntervalRat} {X : Fin n → IntervalRat}
    {s : ℝ} {x : Fin n → ℝ} (hs : s∈I) (hx : FinBoxMem x X) :
    FinBoxMem (embed s x) (box I X) := by
  intro i
  exact Fin.cases hs (fun j => hx j) i

def intervalJacobian {n : ℕ} (F : Fin n → Expr) (I : IntervalRat)
    (X : Fin n → IntervalRat) (cfg : EvalConfig := {}) :
    Matrix (Fin n) (Fin n) IntervalRat :=
  fun i j => Optimization.derivIntervalCoreN (F i) (finBoxEnv (box I X)) j.succ.val cfg

theorem jacobian_mem {n : ℕ} (F : Fin n → Expr) (h : ∀ i, ADSupported (F i))
    (I : IntervalRat) (X : Fin n → IntervalRat) {s : ℝ} {x : Fin n → ℝ}
    (hs : s∈I) (hx : FinBoxMem x X) (cfg : EvalConfig) (i j : Fin n) :
    jacobian F s x i j∈intervalJacobian F I X cfg i j := by
  rw [jacobian_apply F h]
  exact Optimization.evalDualTotalCore_der_correct_idx (F i) (h i) (finEnv (embed s x))
    (finBoxEnv (box I X)) j.succ.val (finEnv_mem_finBoxEnv (embed_mem_box hs hx))
    (x j) (by
      have he : finBoxEnv (box I X) j.succ.val=X j := by
        unfold finBoxEnv
        rw [dite_eq_left j.succ.isLt]
        change (box I X) j.succ=X j
        simp [box]
      rw [he]
      exact hx j) cfg

end polyak.Numerics.Parametric
