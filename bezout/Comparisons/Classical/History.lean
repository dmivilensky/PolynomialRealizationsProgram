import bezout.Flat.Chebyshev
import bezout.Synthesis.Theorem
import bezout.Lower.PhysicalCorners
import chebyshev1.Prefix.Asymptotics

/-!
Article: bezout, classical additive comparison and Equation `eq:classical`.
Use: constructs the actual Prefix history from its normalized first-kind
queries and identifies every physical additive response, including startup.
Proof: the symmetric Hall expansion and uniqueness of separated factors.
-/

namespace bezout.Classical
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The classical normalized first-kind query basis. -/
def queryFamily (I : chebyshev1.SpectralInterval) (N : ℕ) : GradedFamily N where
  poly s := C (1 / I.den s) * T ℝ (s.val : ℤ)
  degree_eq s := by
    rw [degree_C_mul (one_div_ne_zero (I.den_ne s)), degree_T]
    simp

/-- Every classical query is normalized at the exterior spectral coordinate. -/
theorem queryFamily_eta (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) :
    ((queryFamily I N).poly s).eval I.eta = 1 := by
  simp only [queryFamily, eval_mul, eval_C]
  exact one_div_mul_cancel (I.den_ne s)

/-- The actual unrestricted causal history with the classical Prefix queries. -/
def history (I : chebyshev1.SpectralInterval) (N : ℕ) : bezout.History N :=
  (queryFamily I N).realize I (queryFamily_eta I N)

/-- The classical history has the exact prescribed Chebyshev terminal. -/
theorem history_exact (I : chebyshev1.SpectralInterval) (N : ℕ) :
    (history I N).ChebyshevExact I :=
  (queryFamily I N).realize_exact I (queryFamily_eta I N)

/-- The charted actual queries are precisely T_s/C_s. -/
theorem history_chartQuery (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) :
    (history I N).chartQuery I s = C (1 / I.den s) * T ℝ (s.val : ℤ) :=
  (queryFamily I N).realize_chartQuery I (queryFamily_eta I N) s

/-- Startup has a half weight, while every subsequent physical response has unit weight. -/
def initialWeight (s : ℕ) : ℝ := if s = 0 then 1 / 2 else 1

/-- Explicit classical response factor in the Chebyshev coordinate. -/
def responseFactor (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ[X] :=
  C (initialWeight s * I.den s) * U ℝ ((N - 1 - s : ℕ) : ℤ)

/-- The polynomially extended Bezoutian is symmetric on the entire plane. -/
theorem bezout_symm (N : ℕ) (x y : ℝ) : chebyshevBezout N x y = chebyshevBezout N y x := by
  by_cases hxy : x = y
  · subst y
    rfl
  · simp only [chebyshevBezout, bezout.History.dividedDifference, hxy, Ne.symm hxy,
      ite_false]
    congr 1
    field_simp
    ring

/-- The full-plane classical factorization is the transposed Hall expansion. -/
theorem tensor_identity (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N) (x y : ℝ) :
    (∑ s : Fin N, (responseFactor I N s).eval x *
      ((queryFamily I N).poly s).eval y) = chebyshevBezout N x y := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : N ≠ 0)
  rw [bezout_symm, hall_expansion]
  unfold hallSum
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro s _
  simp only [responseFactor, queryFamily, initialWeight, hallTerm, eval_mul, eval_C,
    Nat.succ_sub_one]
  by_cases hs : s.val = 0
  · simp only [hs, ite_true, Nat.cast_zero, T_zero, eval_one]
    have hd : I.den 0 = 1 := by simp [chebyshev1.SpectralInterval.den]
    rw [hd]
    simp only [Nat.sub_zero]
    ring
  · simp only [hs, ite_false]
    have hd := I.den_ne s
    field_simp

/-- The actual normalized physical factors are the displayed first-kind and second-kind products. -/
theorem history_chartFactor (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) : (history I N).chartFactor I s = responseFactor I N s := by
  have he := (history I N).chart_factors_unique I hN (history_exact I N)
    (fun s => responseFactor I N s) (fun x y => by
      simp only [history_chartQuery]
      exact tensor_identity I N hN x y)
  exact (congrFun he s).symm

/-- Every actual classical physical query is the normalized Chebyshev prefix residual. -/
theorem query_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (s : Fin N) (lam : ℝ) :
    ((history I N).query s).eval lam = (T ℝ (s.val : ℤ)).eval (I.z lam) / I.den s := by
  rw [← bezout.History.chartQuery_physical_eval, history_chartQuery]
  simp only [eval_mul, eval_C, one_div_mul_eq_div]

/-- Exact additive impulse response of the actual classical query history. -/
theorem response_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 0 < N)
    (s : Fin N) (lam : ℝ) :
    ((history I N).response s).eval lam = (-4 * I.epsilon N / I.delta) *
      (initialWeight s * I.den s) * (U ℝ ((N - 1 - s.val : ℕ) : ℤ)).eval (I.z lam) := by
  rw [bezout.History.chartFactor_physical_eval, history_chartFactor I N hN]
  simp only [responseFactor, eval_mul, eval_C]
  ring

end
end bezout.Classical
