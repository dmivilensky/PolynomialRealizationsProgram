import chebyshev1.Algebra.OrderedProduct
import Mathlib.Data.Matrix.Mul

/-!
Article: bezout, Equation `eq:competitor-transfer`.
Use: exact propagation of physical oracle errors through finite-dimensional
momentum states, including empty products and partially completed stages.
Proof: finite variation of constants; no commutation of consecutive steps is used.
-/

namespace bezout.Comparisons.Competitors
noncomputable section
open scoped BigOperators Matrix
open chebyshev1

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- The exact inhomogeneous state recursion driven by physical answer errors. -/
def linearRun (step : ℕ → Matrix ι ι R) (forcing : ℕ → ι → R)
    (initial : ι → R) : ℕ → ι → R
  | 0 => initial
  | n+1 => step n *ᵥ linearRun step forcing initial n + forcing n

/-- Every earlier impulse propagates through precisely its remaining suffix. -/
theorem suffix_succ (step : ℕ → Matrix ι ι R) {n s : ℕ} (hs : s<n) :
    orderedProduct (fun i => step (s+1+i)) (n+1-(s+1)) =
      step n * orderedProduct (fun i => step (s+1+i)) (n-(s+1)) := by
  rw [show n+1-(s+1)=(n-(s+1))+1 by omega, orderedProduct_succ]
  rw [show s+1+(n-(s+1))=n by omega]

/-- Exact finite variation of constants, with one separate insertion for each
physical oracle answer. All suffixes are ordered and empty suffixes are identities. -/
theorem linearRun_expansion (step : ℕ → Matrix ι ι R) (forcing : ℕ → ι → R)
    (initial : ι → R) (n : ℕ) :
    linearRun step forcing initial n = orderedProduct step n *ᵥ initial +
      ∑ s ∈ Finset.range n,
        orderedProduct (fun i => step (s+1+i)) (n-(s+1)) *ᵥ forcing s := by
  induction n with
  | zero => simp [linearRun]
  | succ n ih =>
    rw [linearRun, ih, Matrix.mulVec_add,
      orderedProduct_succ, Finset.sum_range_succ]
    rw [← Matrix.mulVec_mulVec]
    have ht : step n *ᵥ (∑ s ∈ Finset.range n,
        orderedProduct (fun i => step (s+1+i)) (n-(s+1)) *ᵥ forcing s) =
        ∑ s ∈ Finset.range n,
          orderedProduct (fun i => step (s+1+i)) (n+1-(s+1)) *ᵥ forcing s := by
      rw [Matrix.mulVec_sum]
      apply Finset.sum_congr rfl
      intro s hs
      rw [suffix_succ step (Finset.mem_range.mp hs), Matrix.mulVec_mulVec]
    rw [ht]
    simp only [Nat.sub_self, orderedProduct_zero, Matrix.one_mulVec]
    simp only [add_assoc]

omit [DecidableEq ι] in
/-- Initial states and physical forcing streams superpose exactly. -/
theorem linearRun_add (step : ℕ → Matrix ι ι R) (b c : ℕ → ι → R)
    (x y : ι → R) (n : ℕ) :
    linearRun step (fun j => b j+c j) (x+y) n =
      linearRun step b x n+linearRun step c y n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [linearRun,ih,Matrix.mulVec_add,linearRun,linearRun]; abel

omit [DecidableEq ι] in
/-- Scaling both physical inputs scales their actual linear trajectory. -/
theorem linearRun_smul (step : ℕ → Matrix ι ι R) (b : ℕ → ι → R)
    (x : ι → R) (a : R) (n : ℕ) :
    linearRun step (fun j => a • b j) (a • x) n = a • linearRun step b x n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [linearRun,ih,Matrix.mulVec_smul,linearRun,smul_add]

omit [DecidableEq ι] in
/-- A finite superposition of actual physical streams is evaluated by the same finite sum. -/
theorem linearRun_forcing_sum {κ : Type*} [Fintype κ]
    (step : ℕ → Matrix ι ι R) (b : κ → ℕ → ι → R) (n : ℕ) :
    linearRun step (fun j => ∑ s, b s j) 0 n = ∑ s, linearRun step (b s) 0 n := by
  induction n with
  | zero => simp [linearRun]
  | succ n ih => rw [linearRun,ih,Matrix.mulVec_sum,← Finset.sum_add_distrib]; rfl

/-- A constant scalar propagation has the usual matrix-power product. -/
theorem orderedProduct_constant (A : Matrix ι ι R) (n : ℕ) :
    orderedProduct (fun _ => A) n = A^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [orderedProduct_succ,ih,pow_succ']

/-- A future impulse has no effect before its physical call. -/
theorem linearRun_before_impulse (step : ℕ → Matrix ι ι R) (v : ι → R)
    {n s : ℕ} (hs : n≤s) :
    linearRun step (fun j => if j=s then v else 0) 0 n = 0 := by
  rw [linearRun_expansion]
  simp only [Matrix.mulVec_zero, zero_add]
  apply Finset.sum_eq_zero
  intro j hj
  have hn : j≠s := by have := Finset.mem_range.mp hj; omega
  simp [hn]

/-- A matrix geometric sum telescopes against a fixed state difference. -/
theorem sum_power_difference (A : Matrix ι ι R) (x : ι → R) (n : ℕ) :
    (∑ j ∈ Finset.range n, A^j *ᵥ (x-A*ᵥ x)) = x-A^n*ᵥ x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Matrix.mulVec_sub,Matrix.mulVec_mulVec,← pow_succ]
    abel

/-- A single physical impulse has exactly the stated ordered suffix response. -/
theorem linearRun_single_impulse (step : ℕ → Matrix ι ι R) (v : ι → R)
    {n s : ℕ} (hs : s<n) :
    linearRun step (fun j => if j=s then v else 0) 0 n =
      orderedProduct (fun i => step (s+1+i)) (n-(s+1)) *ᵥ v := by
  rw [linearRun_expansion]
  simp only [Matrix.mulVec_zero]
  simp_rw [apply_ite, Matrix.mulVec_zero]
  simp [hs]

end
end bezout.Comparisons.Competitors
