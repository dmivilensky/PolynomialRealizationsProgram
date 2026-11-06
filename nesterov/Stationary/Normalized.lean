import nesterov.Stationary.SourceDictionary
import polyak.Functions.Normalization

/-!
Article: the normalized recurrence in the proof of Theorem A(c).
The polynomial is literal: its input is the latent history, its output is the
normalized gradient at the original query. No query polynomial is divided out.
-/
namespace nesterov.StationaryMethod
noncomputable section
open scoped BigOperators
open Polynomial
variable (M : nesterov.StationaryMethod)

/-- Query coefficients padded by zero at the final history coordinate. -/
def paddedQueryCoeff (j : Fin (M.memory+1)) : ℝ :=
  if hj : j.val<M.memory then M.queryCoeff ⟨j.val,hj⟩ else 0

@[simp] theorem paddedQueryCoeff_castSucc (j : Fin M.memory) :
    M.paddedQueryCoeff j.castSucc=M.queryCoeff j := by
  simp [paddedQueryCoeff,j.isLt]

@[simp] theorem paddedQueryCoeff_last :
    M.paddedQueryCoeff (Fin.last M.memory)=0 := by simp [paddedQueryCoeff]

/-- Coefficients of p=((L+μ)u−2v)/(L−μ). -/
def normalizedCoeff (μ L : ℝ) (j : Fin (M.memory+1)) : ℝ :=
  ((L+μ)*M.paddedQueryCoeff j-2*M.recurrenceCoeff j)/(L-μ)

/-- The actual normalized recursion polynomial from the article. -/
def normalizedPolynomial (μ L : ℝ) : Polynomial ℝ :=
  C ((L+μ)/(L-μ))*M.queryPolynomial-C (2/(L-μ))*M.recurrencePolynomial

theorem normalizedPolynomial_eq_sum (μ L : ℝ) :
    M.normalizedPolynomial μ L=
      ∑ j : Fin (M.memory+1),monomial j.val (M.normalizedCoeff μ L j) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last,normalizedCoeff,paddedQueryCoeff_castSucc,
    paddedQueryCoeff_last,mul_zero,zero_sub,neg_div]
  unfold normalizedPolynomial queryPolynomial recurrencePolynomial
  rw [Fin.sum_univ_castSucc]
  simp only [mul_add,Finset.mul_sum,C_mul_monomial,Fin.val_castSucc,Fin.val_last]
  rw [sub_add_eq_sub_sub]
  rw [← Finset.sum_sub_distrib]
  simp only [← monomial_sub]
  have he (j : Fin M.memory) :
      (L+μ)/(L-μ)*M.queryCoeff j-2/(L-μ)*M.recurrenceCoeff j.castSucc=
        ((L+μ)*M.queryCoeff j-2*M.recurrenceCoeff j.castSucc)/(L-μ) := by ring
  simp only [he]
  rw [sub_eq_add_neg,← monomial_neg]
  congr 2
  ring

theorem normalizedPolynomial_coeff (μ L : ℝ) (j : Fin (M.memory+1)) :
    (M.normalizedPolynomial μ L).coeff j.val=M.normalizedCoeff μ L j := by
  classical
  rw [M.normalizedPolynomial_eq_sum]
  simp only [finsetSum_coeff,coeff_monomial]
  rw [Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    exact ite_eq_right (fun hval => hb (Fin.ext hval))
  · simp

theorem normalizedCoeff_top (μ L : ℝ) :
    M.normalizedCoeff μ L (Fin.last M.memory)=
      -(2/(L-μ))*M.recurrenceCoeff (Fin.last M.memory) := by
  simp only [normalizedCoeff,paddedQueryCoeff_last,mul_zero,zero_sub]
  ring

theorem normalizedCoeff_top_ne {μ L : ℝ} (hμL : μ<L) :
    M.normalizedCoeff μ L (Fin.last M.memory)≠0 := by
  rw [M.normalizedCoeff_top]
  exact mul_ne_zero (neg_ne_zero.mpr (div_ne_zero (by norm_num) (sub_ne_zero.mpr hμL.ne')))
    M.leading_ne

theorem normalizedPolynomial_natDegree {μ L : ℝ} (hμL : μ<L) :
    (M.normalizedPolynomial μ L).natDegree=M.memory := by
  apply natDegree_eq_of_le_of_coeff_ne_zero
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro n hn
    rw [M.normalizedPolynomial_eq_sum]
    simp only [finsetSum_coeff,coeff_monomial]
    apply Finset.sum_eq_zero
    intro j _
    exact ite_eq_right (by omega)
  · rw [show M.memory=(Fin.last M.memory).val from rfl,M.normalizedPolynomial_coeff]
    exact M.normalizedCoeff_top_ne hμL

theorem normalizedPolynomial_ne_zero {μ L : ℝ} (hμL : μ<L) :
    M.normalizedPolynomial μ L≠0 := by
  intro hz
  have hh:=M.normalizedPolynomial_natDegree hμL
  rw [hz,natDegree_zero] at hh
  exact (Nat.ne_of_gt M.memory_pos) hh.symm

theorem normalizedPolynomial_leadingCoeff {μ L : ℝ} (hμL : μ<L) :
    (M.normalizedPolynomial μ L).leadingCoeff=
      -(2/(L-μ))*M.recurrenceCoeff (Fin.last M.memory) := by
  change (M.normalizedPolynomial μ L).coeff (M.normalizedPolynomial μ L).natDegree=_
  rw [M.normalizedPolynomial_natDegree hμL]
  exact (M.normalizedPolynomial_coeff μ L (Fin.last M.memory)).trans
    (M.normalizedCoeff_top μ L)

@[simp] theorem normalizedPolynomial_one (μ L : ℝ) :
    (M.normalizedPolynomial μ L).eval 1=(L+μ)/(L-μ) := by
  simp [normalizedPolynomial]

theorem normalizedPolynomial_complex_eval (μ L : ℝ) (z : ℂ) :
    ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=
      ((L+μ)/(L-μ):ℝ)*(M.queryPolynomial.map Complex.ofRealHom).eval z-
        (2/(L-μ):ℝ)*(M.recurrencePolynomial.map Complex.ofRealHom).eval z := by
  simp [normalizedPolynomial]

theorem normalizedPolynomial_characteristic (μ L : ℝ) (z : ℂ) :
    ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=
      -(2/(L-μ):ℝ)*M.characteristic ((L+μ)/2) z := by
  rw [M.normalizedPolynomial_complex_eval,M.characteristic_eq_polynomial_eval]
  simp only [eval_sub,eval_mul,eval_C]
  push_cast
  ring

section Trajectory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

omit [CompleteSpace E] in
/-- The padded query is exactly the same query as the finite executor. -/
theorem paddedQuery_sum (w : ℕ→E) (k : ℕ) :
    (∑ j : Fin (M.memory+1),M.paddedQueryCoeff j • w (k+j))=M.query w k := by
  rw [Fin.sum_univ_castSucc]
  simp [query]

omit [CompleteSpace E] in
theorem normalizedRecurrence_eq (μ L : ℝ) (w : ℕ→E) (k : ℕ) :
    (∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=
      ((L+μ)/(L-μ)) • M.query w k-
        (2/(L-μ)) • ∑ j : Fin (M.memory+1),M.recurrenceCoeff j • w (k+j) := by
  simp only [normalizedCoeff,sub_div,mul_div_right_comm,sub_smul,mul_smul,
    Finset.sum_sub_distrib,← Finset.smul_sum]
  rw [M.paddedQuery_sum]

/-- An actual original trajectory satisfies the normalized polynomial equation. -/
theorem IsTrajectory.normalized {μ L : ℝ} {f : E→ℝ} {w : ℕ→E}
    (hw : M.IsTrajectory (gradient f) w) (hf : Differentiable ℝ f) :
    ∀ k, (∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=
      gradient (polyak.normalizeFunction μ L f) (M.query w k) := by
  intro k
  rw [M.normalizedRecurrence_eq,hw k,(polyak.hasGradientAt_normalize hf _).gradient]

/-- Conversely, interpolation of the normalized gradient yields the literal
stationary executor on the denormalized genuine objective. -/
theorem isTrajectory_denormalize {μ L : ℝ} (hμL : μ<L) {ψ : E→ℝ}
    (hψ : Differentiable ℝ ψ) {w : ℕ→E}
    (hw : ∀ k,(∑ j : Fin (M.memory+1),M.normalizedCoeff μ L j • w (k+j))=
      gradient ψ (M.query w k)) :
    M.IsTrajectory (gradient (polyak.denormalizeFunction μ L ψ)) w := by
  intro k
  rw [(polyak.hasGradientAt_denormalize hψ _).gradient,← hw k,M.normalizedRecurrence_eq]
  have hd : L-μ≠0:=sub_ne_zero.mpr hμL.ne'
  have hc : (L-μ)/2*((L+μ)/(L-μ))=(L+μ)/2 := by field_simp
  have hv : (L-μ)/2*(2/(L-μ))=1 := by field_simp
  rw [smul_sub,smul_smul,smul_smul,hc,hv,one_smul]
  abel

end Trajectory
end
end nesterov.StationaryMethod
