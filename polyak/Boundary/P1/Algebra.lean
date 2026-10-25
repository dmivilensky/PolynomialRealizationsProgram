import polyak.Boundary.P1.Source
import polyak.Boundary.P2.Chebyshev

/-!
Article: Appendix B, the one-atom quartic, active equations, and double root.
Use: contact equations and a checked positive quadratic residual imply global
nonnegativity of the actual normalized lag-three dual polynomial.
-/
noncomputable section
namespace polyak.Boundary.P1
open Spectral Polynomial

def contactD (z c : ℝ) : ℝ := 2+z*c+z^2*(c^2-1)
def contactE (z c : ℝ) : ℝ := 1+z*c+z^2*(2*c^2-1)
def chargeNumerator (z u c : ℝ) : ℝ := 2*u*(1-c^2)*contactE z c/contactD z c

def residualLinear (z u a : ℝ) : ℝ := z-2*u*z^2+2*z^2*a
def residualConstant (z u a : ℝ) : ℝ :=
  2-2*z*u+z^2*u^2-2*z^2+2*a*(z-2*u*z^2)+3*a^2*z^2
def residual (z u a c : ℝ) : ℝ := z^2*c^2+residualLinear z u a*c+residualConstant z u a

theorem quartic_double_root_identity (z u a c : ℝ) :
    quartic z u c=(c-a)^2*residual z u a c+quartic z u a+
      quarticDerivative z u a*(c-a) := by
  unfold quartic residual residualLinear residualConstant quarticDerivative
  ring

theorem quartic_factor {z u a : ℝ} (h0 : quartic z u a=0)
    (h1 : quarticDerivative z u a=0) (c : ℝ) :
    quartic z u c=(c-a)^2*residual z u a c := by
  rw [quartic_double_root_identity,h0,h1]
  ring

theorem contact_gap_identity {z u a : ℝ} (h0 : quartic z u a=0) :
    (1-a^2-u^2)*contactD z a=2*u*z*(1-a^2)*(1+z*a) := by
  unfold quartic at h0
  unfold contactD
  linarith

theorem regularSystem_contacts {z : ℝ} {Z : Coordinates}
    (h : regularSystem (z,Z)=0) :
    quartic z (branchU z (Z 0)) (branchAtom z (Z 1))=0 ∧
      quarticDerivative z (branchU z (Z 0)) (branchAtom z (Z 1))=0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  change regularEquation0 z (Z 0) (Z 1)=0 at h0
  change regularEquation1 z (Z 0) (Z 1)=0 at h1
  rw [← quartic_division,← derivative_division,h0,h1]
  simp

theorem residual_pos {z u a : ℝ}
    (hq : |residualLinear z u a|<residualConstant z u a) (c : Frequency) :
    0<residual z u a c := by
  have hab : |residualLinear z u a*(c : ℝ)|≤|residualLinear z u a| := by
    rw [abs_mul]
    simpa using mul_le_mul_of_nonneg_left (abs_le.mpr c.property)
      (abs_nonneg (residualLinear z u a))
  have ha := (abs_le.mp hab).1
  unfold residual
  nlinarith [sq_nonneg (z*(c : ℝ))]

theorem quartic_nonneg {z u a : ℝ} (h0 : quartic z u a=0)
    (h1 : quarticDerivative z u a=0)
    (hq : |residualLinear z u a|<residualConstant z u a) (c : Frequency) :
    0≤quartic z u c := by
  rw [quartic_factor h0 h1]
  exact mul_nonneg (sq_nonneg _) (residual_pos hq c).le

def weights : DualWeights where
  lags := {3}
  positive_lag n hn := by have he := Finset.mem_singleton.mp hn; omega
  weight n := if n=3 then 1 else 0
  nonneg n _ := by split_ifs <;> norm_num
  sum_one := by simp

theorem chebT_three (x : ℝ) : chebT 3 x=4*x^3-3*x := by
  simp [chebT,P2.Tpoly3]
  ring

theorem chebU_two (x : ℝ) : chebU 2 x=4*x^2-1 := by
  simp [chebU,P2.Upoly2]
  ring

theorem dualSymbol_quartic {z : ℝ} (hz : z≠0) (hd : 4-z^2≠0) (u c : ℝ) :
    (4-z^2)*dualSymbol weights u (1/z) c= -4*(1/z-c)*quartic z u c := by
  have hU : 4*(1/z)^2-1≠0 := by
    intro he
    have hh : (4*(1/z)^2-1)*z^2=4-z^2 := by field_simp [hz]
    rw [he,zero_mul] at hh
    exact hd hh.symm
  simp only [dualSymbol,weights,Finset.sum_singleton,ite_true,one_mul,
    normalizedLower_one,normalizedUpper,lagDenominator]
  norm_num only [Nat.reduceSub]
  simp only [chebT_three,chebU_two]
  unfold g lagB quartic
  norm_num only [Nat.reduceSub]
  simp only [chebU_two]
  field_simp [hz,hU]
  ring

theorem dualPolynomial_nonneg {z u a : ℝ} (hz : 0<z) (hd : 0<4-z^2)
    (hG : 1<1/z) (h0 : quartic z u a=0) (h1 : quarticDerivative z u a=0)
    (hq : |residualLinear z u a|<residualConstant z u a) (c : Frequency) :
    0≤(dualPolynomial weights u (1/z)).eval (c : ℝ) := by
  have hquad := quartic_nonneg h0 h1 hq c
  have hg : 0<1/z-(c : ℝ) := by linarith [c.property.2]
  have he := dualSymbol_quartic hz.ne' hd.ne' u (c : ℝ)
  have hs : dualSymbol weights u (1/z) c≤0 := by nlinarith
  rw [dualPolynomial_factor weights u hG.le] at hs
  nlinarith

end polyak.Boundary.P1
