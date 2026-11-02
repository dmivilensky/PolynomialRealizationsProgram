import bezout.Balanced.Bounds
import bezout.Balanced.Recurrence

/-!
Article: bezout, Algorithm 2 and Equations `eq:stopped-readout` and `eq:impulses`.
Use: identifies the coefficients of the actual synthesized history with the
scalar preparation used by the six-slot implementation.
Proof: exact raw query polynomial identities and uniqueness of graded coordinates.
-/

namespace bezout.Balanced
noncomputable section
open Polynomial Polynomial.Chebyshev
open scoped BigOperators

/-- The raw query impulse, with the physical oracle sign included. -/
def impulse (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j k : Fin N) : ℝ := -normalizer I N j * (history I N hN).a j k

/-- Raw unnormalized physical query polynomial. -/
def rawQuery (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j : Fin N) : ℝ[X] := C (normalizer I N j) * (history I N hN).query j

/-- Every raw physical query evaluates to the exact stopped-parity polynomial. -/
theorem rawQuery_eval (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j : Fin N) (lam : ℝ) : (rawQuery I N hN j).eval lam = (psi N j).eval (I.z lam) := by
  simp only [rawQuery, eval_mul, eval_C, history_query_eval]
  have hz := ne_of_gt (normalizer_pos I hN j.isLt)
  field_simp

/-- Raw impulses vanish exactly where causality makes the coefficient unavailable. -/
theorem impulse_triangular (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j k : Fin N) (hjk : j ≤ k) : impulse I N hN j k = 0 := by
  rw [impulse, (history I N hN).triangular j k hjk, mul_zero]

/-- The actual raw impulses give the complete physical raw-query recurrence. -/
theorem rawQuery_expansion (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j : Fin N) : rawQuery I N hN j = C (normalizer I N j) +
      X * ∑ k : Fin N, C (impulse I N hN j k) * (history I N hN).query k := by
  have hr := (history I N hN).query_recurrence j
  have hs : (∑ k : Fin N, if k < j then C ((history I N hN).a j k) *
      (history I N hN).query k else 0) =
      ∑ k : Fin N, C ((history I N hN).a j k) * (history I N hN).query k := by
    apply Finset.sum_congr rfl
    intro k _
    by_cases hk : k < j
    · simp [hk]
    · simp [hk, (history I N hN).triangular j k (le_of_not_gt hk)]
  rw [hs] at hr
  unfold rawQuery
  rw [hr]
  simp only [impulse, Polynomial.C_mul, Polynomial.C_neg]
  simp only [mul_assoc]
  rw [← Finset.mul_sum]
  ring

/-- The actual physical queries form a graded basis, so raw impulse rows are unique. -/
def physicalQueries (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N) : GradedFamily N where
  poly := (history I N hN).query
  degree_eq j := (history I N hN).query_degree_eq (by omega)
    ((history I N hN).exact_terminal_natDegree I (history_exact I N hN)) j

/-- Any exact raw-query expansion determines the actual impulse row uniquely. -/
theorem impulse_unique (I : chebyshev1.SpectralInterval) (N : ℕ) (hN : 2 ≤ N)
    (j : Fin N) (c : Fin N → ℝ)
    (hc : rawQuery I N hN j = C (normalizer I N j) +
      X * ∑ k : Fin N, C (c k) * (history I N hN).query k) :
    impulse I N hN j = c := by
  have he := (rawQuery_expansion I N hN j).symm.trans hc
  have hm : (∑ k : Fin N, C (impulse I N hN j k) * (history I N hN).query k) =
      ∑ k : Fin N, C (c k) * (history I N hN).query k := by
    have ha := add_left_cancel he
    exact mul_left_cancel₀ X_ne_zero ha
  apply (physicalQueries I N hN).expansion_unique
  simpa only [physicalQueries, smul_eq_C_mul] using hm

/-- The homogeneous coefficient multiplying the preceding odd-indexed raw queries. -/
def recurrenceA (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  2 * I.eta * omega N (s + 4) / omega N (s + 3)

/-- The homogeneous coefficient coupling two consecutive parity levels. -/
def recurrenceC (N s : ℕ) : ℝ := omega N (s + 4) / omega N (s + 2)

/-- The physical Hessian coefficient separated from the chart recurrence. -/
def recurrenceB (I : chebyshev1.SpectralInterval) (N s : ℕ) : ℝ :=
  4 * omega N (s + 4) / (I.delta * omega N (s + 3))

/-- Exact fourth-order raw-query polynomial identity in physical coordinates. -/
theorem rawQuery_fourth_order (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 4 < N) :
    rawQuery I N hN ⟨s + 4, hs⟩ =
      C (recurrenceA I N s) * rawQuery I N hN ⟨s + 3, by omega⟩ +
      C (1 - recurrenceC N s) * rawQuery I N hN ⟨s + 2, by omega⟩ -
      C (recurrenceA I N s) * rawQuery I N hN ⟨s + 1, by omega⟩ +
      C (recurrenceC N s) * rawQuery I N hN ⟨s, by omega⟩ -
      X * C (recurrenceB I N s) *
        (rawQuery I N hN ⟨s + 3, by omega⟩ - rawQuery I N hN ⟨s + 1, by omega⟩) := by
  apply Polynomial.funext
  intro lam
  simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, rawQuery_eval]
  have hr := psi_eval_fourth_order hN hs (I.z lam)
  have ha : 2 * I.z lam * omega N (s + 4) / omega N (s + 3) =
      recurrenceA I N s - lam * recurrenceB I N s := by
    rw [I.z_eq]
    unfold recurrenceA recurrenceB
    field_simp
    ring
  rw [ha] at hr
  simpa only [recurrenceC] using hr.trans (by ring)

/-- The actual dense impulse rows obey the printed fourth-order preparation rule. -/
theorem impulse_recurrence (I : chebyshev1.SpectralInterval) {N s : ℕ}
    (hN : 2 ≤ N) (hs : s + 4 < N) (k : Fin N) :
    impulse I N hN ⟨s + 4, hs⟩ k =
      recurrenceA I N s * impulse I N hN ⟨s + 3, by omega⟩ k +
      (1 - recurrenceC N s) * impulse I N hN ⟨s + 2, by omega⟩ k -
      recurrenceA I N s * impulse I N hN ⟨s + 1, by omega⟩ k +
      recurrenceC N s * impulse I N hN ⟨s, by omega⟩ k -
      recurrenceB I N s *
        (normalizer I N (s + 3) * (if k.val = s + 3 then 1 else 0) -
         normalizer I N (s + 1) * (if k.val = s + 1 then 1 else 0)) := by
  let j4 : Fin N := ⟨s + 4, hs⟩
  let j3 : Fin N := ⟨s + 3, by omega⟩
  let j2 : Fin N := ⟨s + 2, by omega⟩
  let j1 : Fin N := ⟨s + 1, by omega⟩
  let j0 : Fin N := ⟨s, by omega⟩
  let c : Fin N → ℝ := fun t =>
    recurrenceA I N s * impulse I N hN j3 t +
    (1 - recurrenceC N s) * impulse I N hN j2 t -
    recurrenceA I N s * impulse I N hN j1 t +
    recurrenceC N s * impulse I N hN j0 t -
    recurrenceB I N s *
      (normalizer I N (s + 3) * (if t = j3 then 1 else 0) -
       normalizer I N (s + 1) * (if t = j1 then 1 else 0))
  have hc : impulse I N hN j4 = c := by
    apply impulse_unique
    apply Polynomial.funext
    intro lam
    have hr := congrArg (fun p : ℝ[X] => p.eval lam) (rawQuery_fourth_order I hN hs)
    have hr3 := congrArg (fun p : ℝ[X] => p.eval lam) (rawQuery_expansion I N hN j3)
    have hr2 := congrArg (fun p : ℝ[X] => p.eval lam) (rawQuery_expansion I N hN j2)
    have hr1 := congrArg (fun p : ℝ[X] => p.eval lam) (rawQuery_expansion I N hN j1)
    have hr0 := congrArg (fun p : ℝ[X] => p.eval lam) (rawQuery_expansion I N hN j0)
    have hz := normalizer_fourth_order I hN hs
    change normalizer I N j4 = recurrenceA I N s * normalizer I N j3 +
      (1 - recurrenceC N s) * normalizer I N j2 - recurrenceA I N s * normalizer I N j1 +
      recurrenceC N s * normalizer I N j0 at hz
    simp only [eval_add, eval_sub, eval_mul, eval_C, eval_X, eval_finsetSum] at hr hr3 hr2 hr1 hr0 ⊢
    have hsum : (∑ t : Fin N, c t * ((history I N hN).query t).eval lam) =
        recurrenceA I N s * (∑ t : Fin N, impulse I N hN j3 t * ((history I N hN).query t).eval lam) +
        (1 - recurrenceC N s) * (∑ t : Fin N, impulse I N hN j2 t * ((history I N hN).query t).eval lam) -
        recurrenceA I N s * (∑ t : Fin N, impulse I N hN j1 t * ((history I N hN).query t).eval lam) +
        recurrenceC N s * (∑ t : Fin N, impulse I N hN j0 t * ((history I N hN).query t).eval lam) -
        recurrenceB I N s * ((rawQuery I N hN j3).eval lam - (rawQuery I N hN j1).eval lam) := by
      simp only [c, sub_mul, add_mul, mul_assoc, Finset.sum_sub_distrib,
        Finset.sum_add_distrib, ← Finset.mul_sum, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true, rawQuery, eval_mul, eval_C]
      rfl
    rw [hsum]
    linear_combination hr + recurrenceA I N s * hr3 + (1 - recurrenceC N s) * hr2 -
      recurrenceA I N s * hr1 + recurrenceC N s * hr0 - hz
  have hk := congrFun hc k
  simpa only [c, j0, j1, j2, j3, j4, Fin.ext_iff] using hk

end
end bezout.Balanced
