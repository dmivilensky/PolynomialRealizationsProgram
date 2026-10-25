import polyak.Dynamics.QuadraticLimit
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
Article: Appendix A, Lemma startup, choice of the added scalar coordinate.
Use: choose one stable scalar recurrence whose positive-time values never equal one.
Proof: each exceptional equation is a nonconstant polynomial equation; its union is
countable, whereas every real interval meets the complement. Convergence supplies a uniform gap.
-/

namespace polyak.Realization
noncomputable section
open Polynomial Filter Set
open scoped Topology

/-- Article: scalar response polynomial. Use: exact zero-impulse initial conditions. -/
def responsePolynomial (β : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X-C β
  | k+2 => X*responsePolynomial β (k+1)-C β*responsePolynomial β k

/-- Article: pₖ. Use: the actual stable scalar position sequence, with p₋₁=p₀=1. -/
def response (a β : ℝ) (k : ℕ) : ℝ := (responsePolynomial β k).eval a

/-- Article: scalar response degree. Use: every positive-time exceptional equation has finitely many roots. -/
theorem responsePolynomial_natDegree (β : ℝ) (k : ℕ) : (responsePolynomial β k).natDegree=k := by
  suffices hh : ∀ k, (responsePolynomial β k).natDegree=k ∧
      (responsePolynomial β (k+1)).natDegree=k+1 from (hh k).1
  intro k
  induction k with
  | zero => simp [responsePolynomial]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have hn : responsePolynomial β (k+1) ≠ 0 := by
      intro hz
      rw [hz, natDegree_zero] at ih
      omega
    have hx : (X*responsePolynomial β (k+1)).natDegree=k+2 := by
      rw [natDegree_X_mul hn, ih.2]
    have hc := natDegree_C_mul_le β (responsePolynomial β k)
    rw [ih.1] at hc
    change (X*responsePolynomial β (k+1)-C β*responsePolynomial β k).natDegree=k+2
    rw [natDegree_sub_eq_left_of_natDegree_lt (by omega), hx]

/-- Article: the scalar initial value. -/
@[simp] theorem response_zero (a β : ℝ) : response a β 0=1 := by simp [response,responsePolynomial]

/-- Article: the true from-rest first scalar step. -/
@[simp] theorem response_one (a β : ℝ) : response a β 1=a-β := by simp [response,responsePolynomial]

/-- Article: the scalar second-order recurrence. -/
theorem response_recurrence (a β : ℝ) (k : ℕ) :
    response a β (k+2)=a*response a β (k+1)-β*response a β k := by
  simp [response,responsePolynomial]

/-- Article: the stable added coordinate decays. Use: no root formula or nonzero momentum is assumed. -/
theorem response_tendsto_zero {a β : ℝ} (hβ : 0  ≤  β) (hβ1 : β<1) (ha : |a|<1+β) :
    Tendsto (response a β) atTop (𝓝 0) :=
  Dynamics.scalar_recurrence_tendsto_zero _ hβ hβ1 ha (response_recurrence a β)

/-- Article: countable exceptional scalar coefficients. Use: exclude all positive-time returns at once. -/
theorem exceptional_countable (β : ℝ) :
    {a : ℝ | ∃ k : ℕ, 1  ≤  k ∧ response a β k=1}.Countable := by
  have hfin (k : ℕ) : {a : ℝ | 1  ≤  k ∧ response a β k=1}.Countable := by
    by_cases hk : 1  ≤  k
    · have hn : responsePolynomial β k-C 1 ≠ 0 := by
        intro hz
        have hh := responsePolynomial_natDegree β k
        have he : (responsePolynomial β k-C 1).natDegree=0 := by rw [hz]; rfl
        rw [natDegree_sub_C,hh] at he
        omega
      have hroots := (finite_setOfPred_isRoot hn).countable
      simpa only [IsRoot, eval_sub, eval_C, sub_eq_zero, response, hk, true_and] using hroots
    · simp only [hk, false_and, ofPred_false]
      exact countable_empty
  have hh := countable_iUnion hfin
  simpa only [mem_iUnion, mem_ofPred_eq, ofPred_exists] using hh

/-- Article: choose τ outside the countable exceptional set. Use: a single choice works for every time. -/
theorem exists_scalar_coefficient {A B β : ℝ} (hB : 0<B) :
    ∃ τ : ℝ, |τ|<1 ∧ ∀ k : ℕ, 1  ≤  k → response (A+B*τ) β k ≠ 1 := by
  obtain ⟨a,ha,hex⟩ := (exceptional_countable β).dense_compl ℝ |>.inter_open_nonempty
    (Ioo (A-B) (A+B)) isOpen_Ioo (by exact ⟨A,by constructor <;> linarith⟩)
  refine ⟨(a-A)/B, ?_, ?_⟩
  · rw [abs_lt]
    exact ⟨(lt_div_iff₀ hB).mpr (by linarith [ha.1]),
      (div_lt_iff₀ hB).mpr (by linarith [ha.2])⟩
  · intro k hk he
    apply hex
    have heq : A+B*((a-A)/B)=a := by field_simp; ring
    exact ⟨k,hk,by simpa only [heq] using he⟩

/-- Article: finitely many initial return gaps. Use: an elementary finite minimum argument. -/
theorem finite_return_gap (p : ℕ → ℝ) (hp : ∀ k, 1  ≤  k → p k ≠ 1) (N : ℕ) :
    ∃ δ : ℝ, 0<δ ∧ ∀ k, 1  ≤  k → k ≤ N → δ ≤ (1-p k)^2 := by
  induction N with
  | zero => exact ⟨1,by norm_num,by omega⟩
  | succ N ih =>
    obtain ⟨δ,hδ,hh⟩ := ih
    have he : 0<(1-p (N+1))^2 := sq_pos_of_ne_zero (sub_ne_zero.mpr (Ne.symm (hp _ (by omega))))
    refine ⟨min δ ((1-p (N+1))^2),lt_min hδ he,fun k hk hkN => ?_⟩
    rcases lt_or_eq_of_le hkN with hkN | rfl
    · exact (min_le_left _ _).trans (hh k hk (by omega))
    · exact min_le_right _ _

/-- Article: δ₀>0. Use: convergence and no returns imply one uniform interpolation reserve. -/
theorem uniform_return_gap (p : ℕ → ℝ) (hp : ∀ k, 1  ≤  k → p k ≠ 1)
    (hlim : Tendsto p atTop (𝓝 0)) :
    ∃ δ : ℝ, 0<δ ∧ ∀ k, 1  ≤  k → δ ≤ (1-p k)^2 := by
  have ht : ∀ᶠ k : ℕ in atTop, p k < 1/2 := hlim.eventually (gt_mem_nhds (by norm_num))
  obtain ⟨N,hN⟩ := eventually_atTop.mp ht
  obtain ⟨δ,hδ,hh⟩ := finite_return_gap p hp N
  refine ⟨min δ (1/4),lt_min hδ (by norm_num),fun k hk => ?_⟩
  by_cases hkN : k ≤ N
  · exact (min_le_left _ _).trans (hh k hk hkN)
  · have ht := hN k (by omega)
    have hm : min δ (1/4) ≤ 1/4 := min_le_right _ _
    nlinarith

/-- Article: Polyak initialization at τ=0. Use: an explicit decaying auxiliary response. -/
theorem response_polyak_even (q : ℝ) (k : ℕ) :
    response 0 (q^2) (2*k)=(-q^2)^k ∧ response 0 (q^2) (2*k+1)=(-q^2)^(k+1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have he := response_recurrence 0 (q^2) (2*k)
    have ho := response_recurrence 0 (q^2) (2*k+1)
    constructor
    · rw [show 2*(k+1)=2*k+2 by omega, he, ih.1]
      simp only [zero_mul, zero_sub, pow_succ]
      ring
    · rw [show 2*(k+1)+1=(2*k+1)+2 by omega, ho, ih.2]
      simp only [zero_mul, zero_sub, pow_succ]
      ring

/-- Article: leading response coefficient. Use: exact leading coefficient before the affine τ substitution. -/
theorem responsePolynomial_leadingCoeff (β : ℝ) (k : ℕ) :
    (responsePolynomial β k).leadingCoeff=1 := by
  suffices hh : ∀ k,(responsePolynomial β k).leadingCoeff=1 ∧
      (responsePolynomial β (k+1)).leadingCoeff=1 from (hh k).1
  intro k
  induction k with
  | zero => simp [responsePolynomial]
  | succ k ih =>
    refine ⟨ih.2,?_⟩
    have hn : responsePolynomial β (k+1)≠0 := by
      intro hz
      have hh := responsePolynomial_natDegree β (k+1)
      rw [hz,natDegree_zero] at hh
      omega
    have hdeg : (C β*responsePolynomial β k).degree < (X*responsePolynomial β (k+1)).degree := by
      apply degree_lt_degree
      have hh := natDegree_C_mul_le β (responsePolynomial β k)
      rw [responsePolynomial_natDegree] at hh
      rw [natDegree_X_mul hn,responsePolynomial_natDegree]
      omega
    change (X*responsePolynomial β (k+1)-C β*responsePolynomial β k).leadingCoeff=1
    rw [leadingCoeff_sub_of_degree_lt hdeg,leadingCoeff_mul,leadingCoeff_X,ih.2,one_mul]

/-- Article: pₖ as a polynomial in τ. Use: expose the degree and Bᵏ leading coefficient stated in startup. -/
def auxiliaryPolynomial (A B β : ℝ) (k : ℕ) : ℝ[X] :=
  (responsePolynomial β k).comp (C B*X+C A)

/-- Article: the scalar executor is the evaluation of its τ polynomial. -/
theorem auxiliaryPolynomial_eval (A B β τ : ℝ) (k : ℕ) :
    (auxiliaryPolynomial A B β k).eval τ=response (A+B*τ) β k := by
  simp only [auxiliaryPolynomial,eval_comp,eval_add,eval_mul,eval_C,eval_X,response]
  congr 1
  ring

/-- Article: exact degree and leading coefficient in τ. -/
theorem auxiliaryPolynomial_degree_leadingCoeff (A B β : ℝ) (hB : B≠0) (k : ℕ) :
    (auxiliaryPolynomial A B β k).natDegree=k ∧
      (auxiliaryPolynomial A B β k).leadingCoeff=B^k := by
  have hd : (C B*X+C A : ℝ[X]).natDegree=1 := by
    rw [natDegree_add_eq_left_of_natDegree_lt (by simp [natDegree_C_mul_X B hB]),natDegree_C_mul_X B hB]
  have hl : (C B*X+C A : ℝ[X]).leadingCoeff=B := by
    rw [leadingCoeff_add_of_degree_lt' (degree_lt_degree (by simp [natDegree_C_mul_X B hB])),
      leadingCoeff_mul,leadingCoeff_C,leadingCoeff_X,mul_one]
  constructor
  · rw [auxiliaryPolynomial,natDegree_comp,responsePolynomial_natDegree,hd,mul_one]
  · rw [auxiliaryPolynomial,leadingCoeff_comp (by omega),responsePolynomial_leadingCoeff,
      responsePolynomial_natDegree,hl,one_mul]

end
end polyak.Realization
