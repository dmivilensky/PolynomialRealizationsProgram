import krylov.Strings.DiscreteTop

/-!
Article: `main_krylov`, `apC:prop:local` and `apC:lem:topimp(c)`.
The terminal sign is obtained by testing the genuine strictly positive
shifted physical form on the actual position-polynomial solution. All
interior rows vanish by the previously proved actual eigen-equation.
-/

/-!
Article: krylov, Lemma D.18 [apC:lem:topimp].

The terminal mass inequality and strict adjacent mass-gap product follow from the true spectral
norm constraint; top recurrence identities supply the two exact impedance formulas.
The final Robin term is retained in the terminal inequality.
-/

namespace krylov.Strings.DiscreteString
noncomputable section
open Matrix Polynomial chebyshev1 chebyshev2 jacobi.Finite
open scoped BigOperators Matrix.Norms.L2Operator
variable {N : ℕ} (S : DiscreteString N)

/-- True Robin terminal residual of the physical upper solution. -/
def topTerminal (Λ : ℝ) : ℝ :=
  (Λ*S.mass N-S.robin)*S.topA Λ N-S.topB Λ (N-1)

/-- The genuine upper shifted quadratic form collapses to its physical
last-site residual, retaining the actual Robin boundary term. -/
theorem top_quadratic_terminal (Λ : ℝ) (hN : 0<N) :
    let x := S.massEmbedding (fun k ↦ (S.φPolynomial k).eval Λ)
    x ⬝ᵥ ((Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.operator) *ᵥ x) =
      S.topA Λ N*S.topTerminal Λ := by
  let x := S.massEmbedding (fun k ↦ (S.φPolynomial k).eval Λ)
  let last : Fin (N+1) := ⟨N, by omega⟩
  change (∑ i : Fin (N+1), x i *
    ((Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.operator) *ᵥ x) i) = _
  rw [Finset.sum_eq_single last]
  · have hm := S.mass_pos N le_rfl
    have hq := (Real.sqrt_pos.mpr hm).ne'
    have hf := S.polynomial_flux Λ (N-1) (by omega)
    rw [Nat.sub_add_cancel (by omega)] at hf
    have hr := S.operator_massEmbedding_action (fun k ↦ (S.φPolynomial k).eval Λ) last
    simp only [last, lt_irrefl, ite_false, hN, ite_true] at hr
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change x last*(Λ*x last-(S.operator *ᵥ x) last)=_
    rw [show (S.operator *ᵥ x) last =
        (Real.sqrt (S.mass N))⁻¹ * (S.pPolynomial (N-1)).eval Λ +
          S.robin*(Real.sqrt (S.mass N))⁻¹*(S.φPolynomial N).eval Λ by
      change (S.operator *ᵥ S.massEmbedding (fun k ↦ (S.φPolynomial k).eval Λ)) last=_
      rw [hr]
      linear_combination -(Real.sqrt (S.mass N))⁻¹ * hf]
    have hs := alternating_sq N
    simp only [x, massEmbedding, last, topA, topTerminal, topB,
      Nat.sub_add_cancel (by omega : 1≤N)]
    field_simp
    rw [Real.sq_sqrt hm.le]
    linear_combination -((Λ*S.mass N-S.robin)*(S.φPolynomial N).eval Λ^2 -
      (S.φPolynomial N).eval Λ*(S.pPolynomial (N-1)).eval Λ)*hs
  · intro i _ hi
    have hil : i.val<N := by
      have hne : i.val≠N := by intro he; apply hi; exact Fin.ext he
      omega
    have hr := S.polynomial_operator_row Λ i hil
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    change x i*(Λ*x i-(S.operator *ᵥ x) i)=0
    rw [show (S.operator *ᵥ x) i=Λ*x i from hr]
    simp
  · simp

/-- Strict positivity of the true final Robin residual follows from the
actual upper spectral gap, with no separate terminal sign hypothesis. -/
theorem topTerminal_pos {Λ : ℝ} (hΛ : S.spectralRadius<Λ) (hN : 0<N) :
    0<S.topTerminal Λ := by
  have hA : (Λ • (1 : Matrix (Fin (N+1)) (Fin (N+1)) ℝ)-S.operator).PosDef :=
    (krylov.LinearAlgebra.positive_upper_shift_iff _ S.operator_isHermitian Λ).mpr
      (fun i ↦ (S.operator_eigenvalue_le i).trans_lt hΛ)
  let x := S.massEmbedding (fun k ↦ (S.φPolynomial k).eval Λ)
  have hx : x≠0 := by
    intro he
    have h := congrFun he 0
    simp [x, massEmbedding, S.mass_zero] at h
  have hp := hA.dotProduct_mulVec_pos hx
  simp only [star_trivial] at hp
  rw [S.top_quadratic_terminal Λ hN] at hp
  exact pos_of_mul_pos_right hp (S.topA_pos hΛ N le_rfl).le

/-- The final physical incoming impedance is strictly below its full mass;
the nonnegative Robin term strengthens the actual terminal inequality. -/
theorem top_terminal_identity {Λ : ℝ} (hΛ : S.spectralRadius<Λ) (hN : 0<N) :
    S.topC' Λ N < Real.sqrt Λ*S.mass N := by
  have hΛ0 : 0<Λ := (norm_nonneg S.operator).trans_lt hΛ
  have hs := Real.sqrt_pos.mpr hΛ0
  have ha := S.topA_pos hΛ N le_rfl
  have ht := S.topTerminal_pos hΛ hN
  rw [topTerminal] at ht
  rw [topC', div_lt_iff₀ (mul_pos hs ha)]
  rw [← mul_assoc, show Real.sqrt Λ*S.mass N*Real.sqrt Λ = Λ*S.mass N by
    calc
      _ = Real.sqrt Λ^2*S.mass N := by ring
      _ = _ := by rw [Real.sq_sqrt hΛ0.le]]
  nlinarith [mul_nonneg S.robin_nonneg ha.le]

/-- Actual positive impedances with the exact bond identity and the full
site budget, ready for the finite bond/site pairing argument. -/
theorem exists_top_impedances {Λ : ℝ} (hΛ : S.spectralRadius<Λ) :
    ∃ c d : ℕ→ℝ,
      (∀ j<N, 0<c j ∧ 0<d j) ∧
      (∀ j<N, Real.sqrt Λ*S.gap j=(c j)⁻¹+(d j)⁻¹) ∧
      (∀ j<N, d j+(if j+1<N then c (j+1) else 0)≤Real.sqrt Λ*S.mass (j+1)) := by
  refine ⟨S.topC Λ, (fun j ↦ S.topC' Λ (j+1)), ?_, ?_, ?_⟩
  · intro j hj
    exact ⟨S.topC_pos hΛ j hj, S.topC'_pos hΛ (j+1) (by omega) (by omega)⟩
  · exact fun j hj ↦ S.top_bond_identity hΛ j hj
  · intro j hj
    change S.topC' Λ (j+1)+(if j+1<N then S.topC Λ (j+1) else 0)≤_
    by_cases h : j+1<N
    · rw [ite_eq_left h, add_comm, ← S.top_mass_identity hΛ (j+1) (by omega) h]
    · have he : j+1=N := by omega
      rw [ite_eq_right h, add_zero, he]
      exact (S.top_terminal_identity hΛ (by omega)).le

end
end krylov.Strings.DiscreteString
