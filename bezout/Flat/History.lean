import bezout.Flat.Tensor
import bezout.Synthesis.Theorem
import bezout.Lower.PhysicalCorners

/-!
Article: bezout, Theorem 3.1 and Equations (10)–(12).
Use: an actual Chebyshev-exact Flat history with simultaneously equal physical
response norms, for every horizon N at least two.
Proof: synthesize the explicit normalized graded queries, use the finite tensor
identity to identify their unique physical factors, and apply convexity.
-/

namespace bezout.Flat
noncomputable section
open Polynomial
open scoped BigOperators

/-- The actual Flat causal history, obtained from its explicit graded queries.
Use: realizes the additive optimum without an assumed existence certificate. -/
def history (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : bezout.History N :=
  (queries I N (by omega)).realize I (fun s => queryPolynomial_eta I N s)

/-- Flat has precisely the prescribed Chebyshev terminal.
Use: membership in the unrestricted article comparison class. -/
theorem history_exact (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) :
    (history I N hN).ChebyshevExact I :=
  (queries I N (by omega)).realize_exact I (fun s => queryPolynomial_eta I N s)

/-- The actual Flat history has the exact displayed extrapolated queries.
Use: identification with the four-vector oracle implementation. -/
theorem history_chartQuery (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (history I N hN).chartQuery I s = queryPolynomial I N s :=
  (queries I N (by omega)).realize_chartQuery I (fun s => queryPolynomial_eta I N s) s

/-- The explicit normalized response factor attached to physical call s.
Use: response equalization in the reverse Chebyshev degree order. -/
def responseFactor (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  C (unitMass I N) * factorPolynomial I N (N - 1 - s)

/-- Flat's finite factorization in chronological query order.
Use: full-plane uniqueness of the actual physical response factors. -/
theorem tensor_identity (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) (x y : ℝ) :
    (∑ s : Fin N, (responseFactor I N s).eval x * (queryPolynomial I N s).eval y) =
      chebyshevBezout N x y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  simp only [responseFactor, eval_mul, eval_C]
  rw [Fin.sum_univ_eq_sum_range (fun s : ℕ => unitMass I (n + 1) *
    (factorPolynomial I (n + 1) (n + 1 - 1 - s)).eval x *
    (queryPolynomial I (n + 1) s).eval y) (n + 1)]
  have hr := Finset.sum_range_reflect
    (fun s => unitMass I (n + 1) * (factorPolynomial I (n + 1) (n - s)).eval x *
      (queryPolynomial I (n + 1) s).eval y) (n + 1)
  simp only [Nat.add_sub_cancel] at hr ⊢
  rw [← hr]
  calc
    _ = ∑ s ∈ Finset.range (n + 1), unitMass I (n + 1) *
        (factorPolynomial I (n + 1) s).eval x * (queryPolynomial I (n + 1) (n - s)).eval y := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Nat.sub_sub_self (by have := Finset.mem_range.mp hs; omega : s ≤ n)]
    _ = _ := tensor_identity_range I n x y

/-- The actual normalized factors are exactly the explicit convex mixtures.
Use: translates the constructive tensor identity to physical oracle responses. -/
theorem history_chartFactor (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) : (history I N hN).chartFactor I s = responseFactor I N s := by
  have hf := (history I N hN).chart_factors_unique I (by omega) (history_exact I N hN)
    (fun t => responseFactor I N t) (fun x y => by
      simp only [history_chartQuery]
      exact tensor_identity I N (by omega) x y)
  exact (congrFun hf s).symm

/-- The exact physical response polynomial in chart coordinates.
Use: all scalar response bounds, including common endpoint equality. -/
theorem history_response_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (s : Fin N) (lam : ℝ) :
    ((history I N hN).response s).eval lam =
      (-4 * I.epsilon N / I.delta * unitMass I N) *
        (factorPolynomial I N (N - 1 - s.val)).eval (I.z lam) := by
  rw [bezout.History.chartFactor_physical_eval, history_chartFactor]
  simp only [responseFactor, eval_mul, eval_C]
  ring

end
end bezout.Flat
