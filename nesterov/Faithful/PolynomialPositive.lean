import nesterov.Faithful.CirclePolynomial
import Mathlib.Analysis.Asymptotics.Lemmas

/-!
Finite-polynomial positivity at the two-scale corner. The nonnegative limit
polynomial is retained exactly; C¹ coefficient perturbations are absorbed by
the positive linear term, independently of the order of its zero.
-/
namespace nesterov.Faithful
noncomputable section
open Polynomial Finset Filter Set Asymptotics
open scoped Topology

def tailEval (P : Polynomial ℝ) (N : ℕ) (x : ℝ) : ℝ :=
  ∑ j∈range N,P.coeff (j+2)*x^j

theorem eval_split_tail (P : Polynomial ℝ) {N : ℕ} (hN : P.natDegree<N+2) (x : ℝ) :
    P.eval x=P.coeff 0+P.coeff 1*x+x^2*tailEval P N x := by
  rw [eval_eq_sum_range' hN,show N+2=2+N by omega,sum_range_add]
  norm_num only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_one,Nat.reduceAdd]
  unfold tailEval
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro j _
  rw [show 2+j=j+2 by omega,pow_add]
  ring

theorem tail_difference_bound (P Q : Polynomial ℝ) {N : ℕ} {K ε x : ℝ}
    (hK : 0≤K) (hε : 0≤ε) (hx : |x|≤1)
    (hcoeff : ∀ j : ℕ,j<N → |P.coeff (j+2)-Q.coeff (j+2)|≤K*ε) :
    |tailEval P N x-tailEval Q N x|≤N*K*ε := by
  unfold tailEval
  rw [←sum_sub_distrib]
  apply (abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _j∈range N,K*ε := by
      apply sum_le_sum
      intro j hj
      rw [←sub_mul,abs_mul]
      have hp : |x^j|≤1 := by simpa only [abs_pow] using pow_le_one₀ (abs_nonneg x) hx
      exact (mul_le_mul (hcoeff j (mem_range.mp hj)) hp (abs_nonneg _) (mul_nonneg hK hε)).trans_eq (mul_one _)
    _ = _ := by simp;ring

/-- The elementary corner estimate, with all coefficient and radius bounds
explicit. No Taylor remainder or positivity conclusion is assumed. -/
theorem positive_of_coefficients {P Q : Polynomial ℝ} {N : ℕ} {K ε B x : ℝ}
    (hP : P.natDegree<N+2) (hQ : Q.natDegree<N+2)
    (hQ0 : Q.coeff 0=0) (hQ1 : Q.coeff 1=0) (hQx : 0≤Q.eval x)
    (hK : 0≤K) (hε : 0<ε)
    (ha : 0<P.coeff 0) (hb : B*ε≤P.coeff 1)
    (hcoeff : ∀ j : ℕ,j<N → |P.coeff (j+2)-Q.coeff (j+2)|≤K*ε)
    (hx : 0≤x) (hx1 : x≤1) (hsmall : N*K*x≤B) : 0<P.eval x := by
  have ht := tail_difference_bound P Q (x:=x) hK hε.le (by simpa only [abs_of_nonneg hx] using hx1) hcoeff
  have hl := (abs_le.mp ht).1
  have hm := mul_le_mul_of_nonneg_left hl (sq_nonneg x)
  have heP := eval_split_tail P hP x
  have heQ := eval_split_tail Q hQ x
  rw [hQ0,hQ1,zero_mul,zero_add] at heQ
  have hbx := mul_le_mul_of_nonneg_right hb hx
  have htail := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hε.le hx)
  nlinarith only [heP,heQ,hQx,ha,hm,hbx,htail]

/-- One coefficientwise C¹ germ gives one common O(ε) bound on any finite
coefficient set, with no compactness assumption on an infinite sequence. -/
theorem coefficient_lipschitz_germ {P : ℝ→Polynomial ℝ} (N : ℕ)
    (hP : ∀ j : ℕ,ContDiffWithinAt ℝ 1 (fun ε=>(P ε).coeff j) (Ici 0) 0) :
    ∃ K : ℝ,0<K ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      ∀ j : ℕ,j<N → |(P ε).coeff j-(P 0).coeff j|≤K*ε := by
  have ho (j : Fin N) : ∃ K : ℝ,0<K ∧ ∀ᶠ ε in 𝓝[>] (0:ℝ),
      |(P ε).coeff j.val-(P 0).coeff j.val|≤K*ε := by
    have hh := ((hP j.val).differentiableWithinAt (by norm_num : (1:WithTop ℕ∞)≠0)).isBigO_sub
    have hm : 𝓝[>] (0:ℝ)≤𝓝[≥] (0:ℝ) := nhdsWithin_mono _ (Ioi_subset_Ici_self)
    obtain ⟨K,hK,hbound⟩ := (hh.mono hm).exists_pos
    refine ⟨K,hK,?_⟩
    filter_upwards [hbound.bound,self_mem_nhdsWithin] with ε he hε
    change (0:ℝ)<ε at hε
    simpa only [sub_zero,Real.norm_eq_abs,abs_of_pos hε] using he
  choose K hK he using ho
  let C := 1+∑ j : Fin N,K j
  have hC : 0<C := by
    have hs : 0≤∑ j : Fin N,K j := sum_nonneg (fun j _=>(hK j).le)
    dsimp [C]
    linarith
  have heall : ∀ᶠ ε in 𝓝[>] (0:ℝ),∀ j : Fin N,
      |(P ε).coeff j.val-(P 0).coeff j.val|≤K j*ε := by
    exact Filter.eventually_all.mpr he
  refine ⟨C,hC,?_⟩
  filter_upwards [heall,self_mem_nhdsWithin] with ε hεall hε j hj
  have hKC : K ⟨j,hj⟩≤C := by
    have hh := single_le_sum (fun i (_ : i∈Finset.univ)=>(hK i).le) (Finset.mem_univ (⟨j,hj⟩:Fin N))
    dsimp [C]
    linarith
  exact (hεall ⟨j,hj⟩).trans (mul_le_mul_of_nonneg_right hKC hε.le)

end
end nesterov.Faithful
