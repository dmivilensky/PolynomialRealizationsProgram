import nesterov.Faithful.CirclePolynomial
import nesterov.Slow.Model
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! A fixed-degree real polynomial in ξ=1−cos ω for the actual family symbol. -/
namespace nesterov.Faithful
noncomputable section
open Polynomial Filter Set
open scoped Topology BigOperators
variable {θ y : ℝ} (F : Slow.SecondOrderFamily θ y)

def familyA (ε : ℝ) : Polynomial ℝ := (1-X)*(C (ε^2)*F.u ε-F.v ε)
def familyB (ε : ℝ) : Polynomial ℝ := F.u ε-F.v ε

def familyPolynomial (c ε : ℝ) : Polynomial ℝ :=
  circleProductPolynomial (F.memory+2) (familyA F ε) (familyB F ε) (Real.exp (-c*ε))

def familySymbol (c ε ω : ℝ) : ℝ :=
  (((1-polyak.Waves.z (-c*ε) ω)*(F.method ε).characteristic (ε^2) (polyak.Waves.z (-c*ε) ω))*
    star ((F.method ε).characteristic 1 (polyak.Waves.z (-c*ε) ω))).re

theorem familyA_natDegree (ε : ℝ) : (familyA F ε).natDegree<F.memory+2 := by
  have hu : (C (ε^2)*F.u ε).natDegree≤F.memory :=
    (natDegree_C_mul_le _ _).trans (F.u_natDegree_lt ε).le
  have hv : (F.v ε).natDegree≤F.memory := (F.v_natDegree ε).le
  have hd : (C (ε^2)*F.u ε-F.v ε).natDegree≤F.memory := (natDegree_sub_le _ _).trans (max_le hu hv)
  have hleft : (1-X : Polynomial ℝ).natDegree≤1 := by
    exact (natDegree_sub_le _ _).trans (by simp)
  exact natDegree_mul_le.trans_lt (by omega)

theorem familyB_natDegree (ε : ℝ) : (familyB F ε).natDegree<F.memory+2 := by
  exact (natDegree_sub_le _ _).trans_lt (by rw [F.v_natDegree];have := F.u_natDegree_lt ε;omega)

theorem radial_circle_eq (c ε ω : ℝ) :
    (Real.exp (-c*ε):ℂ)*circle ω=polyak.Waves.z (-c*ε) ω := by
  rw [circle,polyak.Waves.z,Complex.ofReal_exp,←Complex.exp_add]

theorem familyPolynomial_eval (c ε ω : ℝ) :
    (familyPolynomial F c ε).eval (1-Real.cos ω)=familySymbol F c ε ω := by
  rw [familyPolynomial,circleProductPolynomial_eval _ _ _ _ (familyA_natDegree F ε) (familyB_natDegree F ε),
    radial_circle_eq]
  unfold familyA familyB familySymbol evalComplex
  simp only [Polynomial.map_mul,Polynomial.map_sub,Polynomial.map_one,Polynomial.map_X,Polynomial.map_C,
    Polynomial.eval_mul,Polynomial.eval_sub,Polynomial.eval_one,Polynomial.eval_X,Polynomial.eval_C,
    StationaryMethod.characteristic_eq_polynomial_eval,Complex.ofReal_one,Polynomial.eval_sub,
    Polynomial.eval_mul,Polynomial.eval_C,one_mul]
  congr 1
  let z := polyak.Waves.z (-c*ε) ω
  let U := evalComplex (F.u ε) z
  let V := evalComplex (F.v ε) z
  let m : ℂ := (ε^2:ℝ)
  change (1-z)*(m*U-V)*star (U-V)=(1-z)*(V-m*U)*star (V-U)
  rw [show U-V= -(V-U) by ring,star_neg]
  ring

theorem circleProductPolynomial_natDegree_le (N : ℕ) (A B : Polynomial ℝ) (r : ℝ) :
    (circleProductPolynomial N A B r).natDegree≤2*N := by
  unfold circleProductPolynomial
  apply natDegree_sum_le_of_forall_le
  intro i hi
  apply natDegree_sum_le_of_forall_le
  intro j hj
  apply (natDegree_C_mul_le _ _).trans
  apply natDegree_comp_le.trans
  have hleft : (1-X : Polynomial ℝ).natDegree≤1 := (natDegree_sub_le _ _).trans (by simp)
  rw [Polynomial.Chebyshev.natDegree_T]
  have habs : ((i:ℤ)-j).natAbs ≤ i+j := by
    exact (Int.natAbs_sub_le _ _).trans_eq (by simp)
  have hi' := Finset.mem_range.mp hi
  have hj' := Finset.mem_range.mp hj
  nlinarith

theorem familyPolynomial_natDegree (c ε : ℝ) :
    (familyPolynomial F c ε).natDegree≤2*(F.memory+2) :=
  circleProductPolynomial_natDegree_le _ _ _ _

end
end nesterov.Faithful
