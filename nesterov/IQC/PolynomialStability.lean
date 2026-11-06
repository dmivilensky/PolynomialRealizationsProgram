import nesterov.IQC.Companion
import nesterov.IQC.PolynomialSymbols
import nesterov.Rates.QuadraticMaximum

/-!
Stability of the full normalized recursion, before any cancellation with u.
The scaled companion retains all common and zero modes of the article's plant.
-/
namespace nesterov.StationaryMethod
open nesterov.IQC
noncomputable section
open scoped BigOperators
open Polynomial
variable (M : nesterov.StationaryMethod)

/-- Coefficients of the normalized recursion after discounting by exp(t). -/
def discountedCoeff (μ L t : ℝ) (j : Fin (M.memory+1)) : ℝ :=
  M.normalizedCoeff μ L j*Real.exp (j.val*t)

/-- Companion coefficients for the literal, uncancelled discounted polynomial. -/
def transitionCoeff (μ L t : ℝ) (j : Fin M.memory) : ℂ :=
  -(M.discountedCoeff μ L t j.castSucc/M.discountedCoeff μ L t (Fin.last M.memory):ℝ)

theorem discountedCoeff_top_ne {μ L : ℝ} (hμL : μ<L) (t : ℝ) :
    M.discountedCoeff μ L t (Fin.last M.memory)≠0 :=
  mul_ne_zero (M.normalizedCoeff_top_ne hμL) (Real.exp_ne_zero _)

/-- Its characteristic roots are exactly the discounted roots of p. -/
theorem transition_root {μ L t : ℝ} (hμL : μ<L) {z : ℂ}
    (hz : z^M.memory=∑ j : Fin M.memory,M.transitionCoeff μ L t j*z^j.val) :
    ((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval ((Real.exp t:ℂ)*z)=0 := by
  have hd : (M.discountedCoeff μ L t (Fin.last M.memory):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (M.discountedCoeff_top_ne hμL t)
  have hmul:=congrArg (fun w : ℂ=>(M.discountedCoeff μ L t (Fin.last M.memory):ℂ)*w) hz
  simp only [transitionCoeff,Complex.ofReal_div,Finset.mul_sum] at hmul
  have hterm (j : Fin M.memory) :
      (M.discountedCoeff μ L t (Fin.last M.memory):ℂ)*
        (-((M.discountedCoeff μ L t j.castSucc:ℂ)/
          (M.discountedCoeff μ L t (Fin.last M.memory):ℂ))*z^j.val)=
      -(M.discountedCoeff μ L t j.castSucc:ℂ)*z^j.val := by field_simp
  simp_rw [hterm] at hmul
  rw [M.normalizedPolynomial_eq_sum]
  simp only [eval_map,eval₂_finsetSum,eval₂_monomial,
    mul_pow,←mul_assoc]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_castSucc,Fin.val_last]
  have hexp (j : ℕ) : (Real.exp t:ℂ)^j=(Real.exp (j*t):ℂ) := by
    rw [←Complex.ofReal_pow,←Real.exp_nat_mul]
  simp_rw [hexp]
  have he : (∑ j : Fin M.memory,(M.discountedCoeff μ L t j.castSucc:ℂ)*z^j.val)+
      (M.discountedCoeff μ L t (Fin.last M.memory):ℂ)*z^M.memory=0 := by
    rw [hmul]
    simp only [neg_mul,Finset.sum_neg_distrib]
    ring
  simpa only [discountedCoeff,Fin.val_castSucc,Fin.val_last,Complex.ofReal_mul,Complex.ofRealHom_eq_coe] using he


/-- A pointwise strict root bound yields a summable full-state impulse. -/
theorem transition_powers_summable {μ L t : ℝ} (hμL : μ<L)
    (hstable : ∀ z : ℂ,((M.normalizedPolynomial μ L).map Complex.ofRealHom).eval z=0 →
      ‖z‖<Real.exp t) :
    Summable (fun n : ℕ=>‖companion M.memory (M.transitionCoeff μ L t)^n‖) := by
  apply companion_powers_summable M.memory_pos
  intro z hz
  have hh:=hstable ((Real.exp t:ℂ)*z) (M.transition_root hμL hz)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos t)] at hh
  nlinarith [Real.exp_pos t]

/-- In particular every exponent above the actual worst quadratic factor
stabilizes the uncancelled middle-curvature recursion. -/
theorem transition_powers_summable_of_quadratic {μ L t : ℝ}
    (hμ : 0<μ) (hμL : μ<L) (ht : nesterov.Rates.quadraticRate M μ L<Real.exp t) :
    Summable (fun n : ℕ=>‖companion M.memory (M.transitionCoeff μ L t)^n‖) := by
  apply M.transition_powers_summable hμL
  intro z hz
  have hr:= (M.normalizedPolynomial_root_iff hμL z).mp hz
  have hmid : (L+μ)/2∈Set.Icc μ L:=by constructor <;> linarith
  exact (nesterov.Rates.quadraticRate_isGreatest M hμ hμL |>.2 ⟨(L+μ)/2,hmid,z,hr,rfl⟩).trans_lt ht

end
end nesterov.StationaryMethod
