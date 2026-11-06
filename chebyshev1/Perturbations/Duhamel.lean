import chebyshev1.TwoTerm.VariableHessian
import chebyshev1.TwoTerm.Quadratic

/-!
Exact variation of constants for a two-term run with arbitrary additive errors.
The errors need not be independent, centered, or chosen before the run.
-/
namespace chebyshev1
noncomputable section
open scoped BigOperators

namespace Perturbations

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A first-order linear recurrence with an unrestricted forcing sequence. -/
def forcedOrbit (A : ℕ → E →ₗ[ℝ] E) (u : ℕ → E) (x : E) : ℕ → E
  | 0 => x
  | t + 1 => A t (forcedOrbit A u x t) + u t

/-- The causal transition from time `s` to time `t`. Only `s ≤ t` is used below. -/
def transition (A : ℕ → E →ₗ[ℝ] E) (t s : ℕ) : E →ₗ[ℝ] E :=
  orderedProduct (fun i => A (s + i)) (t - s)

theorem transition_succ (A : ℕ → E →ₗ[ℝ] E) {t s : ℕ} (hst : s ≤ t) :
    transition A (t + 1) s = A t * transition A t s := by
  unfold transition
  rw [show t + 1 - s = (t - s) + 1 by omega, orderedProduct_succ]
  rw [show s + (t - s) = t by omega]

/-- Discrete variation of constants, before imposing any probabilistic assumptions. -/
theorem forcedOrbit_eq (A : ℕ → E →ₗ[ℝ] E) (u : ℕ → E) (x : E) (t : ℕ) :
    forcedOrbit A u x t = transition A t 0 x +
      ∑ s ∈ Finset.range t, transition A t (s + 1) (u s) := by
  induction t with
  | zero => simp [forcedOrbit, transition]
  | succ t ih =>
    rw [forcedOrbit, ih, map_add, map_sum, Finset.sum_range_succ]
    rw [transition_succ A (Nat.zero_le t)]
    simp only [Module.End.mul_apply]
    have hs : ∀ s ∈ Finset.range t,
        transition A (t+1) (s+1) (u s) = A t (transition A t (s+1) (u s)) := by
      intro s hs
      rw [transition_succ A (by simpa using hs : s+1 ≤ t)]
      rfl
    simp_rw [Finset.sum_congr rfl hs]
    simp [transition, add_assoc]

end Perturbations

namespace TwoTerm

/-- The prefix--insertion--tail factorization for every two-term method. -/
theorem kernel_factor (S : TwoTerm) (t s : ℕ) (lam nu : ℝ) :
    S.realization.kernel t s lam nu =
      -S.gamma s *
        orderedProduct (fun i => S.realization.scalarStep (s + 1 + i) lam)
          (t - (s + 1)) 0 0 *
        (S.realization.residualPolynomial s).eval nu := by
  simp [Realization.kernel, Realization.residualPolynomial_eval,
    Realization.scalarTransfer, Matrix.mul_apply, Fin.sum_univ_two,
    mul_comm, mul_left_comm]

variable (S : TwoTerm) {d : Type*} [Fintype d] [DecidableEq d]

/-- The two-iterate state transition. At time zero the unused memory is discarded. -/
def stateStep (H : Matrix d d ℝ) (s : ℕ) :
    ((d → ℝ) × (d → ℝ)) →ₗ[ℝ] ((d → ℝ) × (d → ℝ)) where
  toFun z :=
    ((if s = 0 then z.1 else S.a s • z.1 + S.b s • z.2) -
      S.gamma s • H.mulVec z.1, z.1)
  map_add' := by
    intro x y
    apply Prod.ext
    · ext i
      by_cases hs : s = 0 <;>
        simp [hs, Matrix.mulVec_add, smul_add, Pi.add_apply, Pi.smul_apply] <;> ring
    · rfl
  map_smul' := by
    intro c x
    apply Prod.ext
    · ext i
      by_cases hs : s = 0 <;>
        simp [hs, Matrix.mulVec_smul, smul_add, smul_sub, smul_smul, mul_comm]
    · rfl

/-- The response at time `t` to an impulse immediately after query `s`. -/
def forcingTail (H : Matrix d d ℝ) (t s : ℕ) : (d → ℝ) →ₗ[ℝ] (d → ℝ) :=
  (LinearMap.fst ℝ (d → ℝ) (d → ℝ)).comp
    ((Perturbations.transition (S.stateStep H) t (s+1)).comp
      (LinearMap.inl ℝ (d → ℝ) (d → ℝ)))

theorem stateStep_pair (H : Matrix d d ℝ) (s : ℕ) (x y : d → ℝ) :
    S.stateStep H s (x, y) =
      ((S.memoryStep s H 0 0).mulVec x + (S.memoryStep s H 0 1).mulVec y,
       (S.memoryStep s H 1 0).mulVec x + (S.memoryStep s H 1 1).mulVec y) := by
  by_cases hs : s = 0
  · subst s
    simp [stateStep, memoryStep, Matrix.sub_mulVec, Matrix.smul_mulVec]
  · simp only [stateStep, LinearMap.coe_mk, AddHom.coe_mk, hs, ↓reduceIte,
      memoryStep, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.of_apply, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
    apply Prod.ext
    · abel
    · rfl

theorem stateProduct_apply (H : Matrix d d ℝ) (a n : ℕ) (x y : d → ℝ) :
    orderedProduct (fun i => S.stateStep H (a+i)) n (x, y) =
      ((orderedProduct (fun i => S.memoryStep (a+i) H) n 0 0).mulVec x +
        (orderedProduct (fun i => S.memoryStep (a+i) H) n 0 1).mulVec y,
       (orderedProduct (fun i => S.memoryStep (a+i) H) n 1 0).mulVec x +
        (orderedProduct (fun i => S.memoryStep (a+i) H) n 1 1).mulVec y) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [orderedProduct_succ, Module.End.mul_apply, ih, S.stateStep_pair,
      orderedProduct_succ]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_mulVec,
      Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    apply Prod.ext <;> abel

/-- The impulse response is the top-left block of the ordinary memory transition. -/
theorem forcingTail_eq_memoryProduct (H : Matrix d d ℝ) (t s : ℕ) (v : d → ℝ) :
    S.forcingTail H t s v =
      (orderedProduct (fun i => S.memoryStep (s+1+i) H) (t-(s+1)) 0 0).mulVec v := by
  simp only [forcingTail, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inl_apply,
    Perturbations.transition]
  rw [S.stateProduct_apply]
  simp

/-- Both oracle error `eta` and update error `xi` may depend on the previous iterates. -/
def perturbedError (H : Matrix d d ℝ) (e0 : d → ℝ)
    (eta xi : ℕ → d → ℝ) : ℕ → d → ℝ
  | 0 => e0
  | 1 => e0 - S.gamma 0 • (H.mulVec e0 + eta 0) + xi 0
  | n+2 => S.a (n+1) • perturbedError H e0 eta xi (n+1) +
      S.b (n+1) • perturbedError H e0 eta xi n -
      S.gamma (n+1) • (H.mulVec (perturbedError H e0 eta xi (n+1)) + eta (n+1)) +
      xi (n+1)

omit [DecidableEq d] in
theorem perturbedError_eq_state (H : Matrix d d ℝ) (e0 : d → ℝ)
    (eta xi : ℕ → d → ℝ) (t : ℕ) :
    Perturbations.forcedOrbit (S.stateStep H)
        (fun s => (xi s - S.gamma s • eta s, 0)) (e0, 0) t =
      (S.perturbedError H e0 eta xi t,
        if t = 0 then 0 else S.perturbedError H e0 eta xi (t-1)) := by
  induction t with
  | zero => simp [Perturbations.forcedOrbit, perturbedError]
  | succ t ih =>
    rw [Perturbations.forcedOrbit, ih]
    cases t with
    | zero => simp [stateStep, perturbedError, smul_add]; abel
    | succ t =>
      simp [stateStep, perturbedError, smul_add]
      abel

theorem stateTransition_eq_quadraticError (H : Matrix d d ℝ) (e0 : d → ℝ) (t : ℕ) :
    (Perturbations.transition (S.stateStep H) t 0 (e0, 0)).1 =
      S.quadraticError H e0 t := by
  have hzero : ∀ t, S.perturbedError H e0 (fun _ => 0) (fun _ => 0) t =
      S.quadraticError H e0 t := by
    intro t
    induction t using Nat.twoStepInduction with
    | zero => rfl
    | one => simp [perturbedError, quadraticError]
    | more t ih0 ih1 => simp [perturbedError, quadraticError, ih0, ih1]
  have h := congrArg Prod.fst
    (S.perturbedError_eq_state H e0 (fun _ => 0) (fun _ => 0) t)
  rw [Perturbations.forcedOrbit_eq] at h
  have hsum : ∑ s ∈ Finset.range t,
      Perturbations.transition (S.stateStep H) t (s+1) (0, 0) = 0 := by
    apply Finset.sum_eq_zero
    intro s _
    exact map_zero _
  simpa only [sub_zero, smul_zero, hsum, add_zero, Prod.fst_zero, hzero] using h

/-- Exact perturbed-run formula with the ordinary quadratic residual as its mean-free part. -/
theorem perturbedError_eq_quadratic_add_forcing (H : Matrix d d ℝ) (e0 : d → ℝ)
    (eta xi : ℕ → d → ℝ) (t : ℕ) :
    S.perturbedError H e0 eta xi t = S.quadraticError H e0 t +
      ∑ s ∈ Finset.range t, S.forcingTail H t s (xi s - S.gamma s • eta s) := by
  have h := congrArg Prod.fst (S.perturbedError_eq_state H e0 eta xi t)
  rw [Perturbations.forcedOrbit_eq] at h
  simpa only [Prod.fst_add, Prod.fst_sum, S.stateTransition_eq_quadraticError,
    forcingTail, LinearMap.comp_apply, LinearMap.fst_apply, LinearMap.inl_apply] using h.symm

/-- The unforced term is the residual polynomial of this exact realization. -/
theorem perturbedError_eq_residual_add_forcing (H : Matrix d d ℝ) (e0 : d → ℝ)
    (eta xi : ℕ → d → ℝ) (t : ℕ) :
    S.perturbedError H e0 eta xi t =
      (Polynomial.aeval H (S.realization.residualPolynomial t)).mulVec e0 +
        ∑ s ∈ Finset.range t, S.forcingTail H t s (xi s - S.gamma s • eta s) := by
  rw [S.perturbedError_eq_quadratic_add_forcing, S.quadraticError_eq_transfer,
    Realization.operatorTransfer_eq_aeval]

/-- A nonlinear run is the fixed-Hessian run forced by its actual gradient defects. -/
theorem nonlinearError_eq_quadratic_add_forcing (g : (d → ℝ) → d → ℝ)
    (H : Matrix d d ℝ) (e0 : d → ℝ) (t : ℕ) :
    S.nonlinearError g e0 t = S.quadraticError H e0 t +
      ∑ s ∈ Finset.range t, S.forcingTail H t s
        (-(S.gamma s • (g (S.nonlinearError g e0 s) -
          H.mulVec (S.nonlinearError g e0 s)))) := by
  let eta : ℕ → d → ℝ := fun s =>
    g (S.nonlinearError g e0 s) - H.mulVec (S.nonlinearError g e0 s)
  have heq : ∀ n, S.perturbedError H e0 eta (fun _ => 0) n =
      S.nonlinearError g e0 n := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one => simp [perturbedError, nonlinearError, eta]
    | more n ih0 ih1 =>
      simp [perturbedError, nonlinearError, eta, ih0, ih1]
  simpa only [heq, zero_sub, eta] using
    S.perturbedError_eq_quadratic_add_forcing H e0 eta (fun _ => 0) t

end TwoTerm
end
end chebyshev1
