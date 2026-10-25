import polyak.Boundary.P5.System
import polyak.Boundary.P5.RealChebyshev

/-!
Article: the central P5 dual polynomial and its exact source interpretation.
Use: double-root equations, positivity and dual optimality all refer to the
same independently defined polynomial source.
-/
noncomputable section
namespace polyak.Boundary.P5
open Polynomial Spectral

/-- Article: the expanded polynomial form of the positive-denominator central dual. -/
def dualClosed (u G w₂ w₃ : ℝ) : ℝ[X] := by
  let c : ℝ[X] := Polynomial.X
  let g := Polynomial.C G
  let v := Polynomial.C u
  let den := Polynomial.C (G*(4*G^2-1)*(16*G^4-12*G^2+1))
  let a₂ := Polynomial.C (w₂*((4*G^2-1)*(16*G^4-12*G^2+1)*(1/2)))
  let a₃ := Polynomial.C (w₃*(G*(16*G^4-12*G^2+1)))
  let a₅ := Polynomial.C ((1-w₂-w₃)*(G*(4*G^2-1)))
  exact -(1-c^2-v^2)*(den+a₂*(2*(g+c))+a₃*(4*(g^2+g*c+c^2)-3)+
      a₅*(16*(g^4+g^3*c+g^2*c^2+g*c^3+c^4)-20*(g^2+g*c+c^2)+5))+
    2*v*(1-c^2)*(a₂*2+a₃*(4*(g+c))+
      a₅*(16*(g^3+g^2*c+g*c^2+c^3)-12*(g+c)))

/-- Article: the real central dual numerator, with its positive common denominator retained. -/
def dualReal (h : ℝ) (Z : Coordinates) : ℝ[X] :=
  dualSource.map (sourceEval (arguments h Z))

/-- Article: source interpretation gives precisely the expanded real polynomial. -/
theorem dualReal_closed (h : ℝ) (Z : Coordinates) :
    dualReal h Z=dualClosed (1/2+h*Z 0) (1+h) (Z 5) (Z 6) := by
  have hg : sourceEval (arguments h Z) G=1+h := by norm_num [sourceEval,G,H,sourceVar]
  have hu : sourceEval (arguments h Z) U=1/2+h*Z 0 := by norm_num [sourceEval,U,H,sourceVar]
  have hw2 : sourceEval (arguments h Z) W₂=Z 5 := by norm_num [sourceEval,W₂,sourceVar]
  have hw3 : sourceEval (arguments h Z) W₃=Z 6 := by norm_num [sourceEval,W₃,sourceVar]
  have hhalf : sourceEval (arguments h Z) (MvPolynomial.C (1/2))=(1/2 : ℝ) := by
    norm_num [sourceEval]
  simp only [dualReal,dualSource,Polynomial.map_add,Polynomial.map_sub,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_neg,Polynomial.map_one,
    Polynomial.map_C,Polynomial.map_X,Polynomial.map_ofNat]
  simp only [dualDenominator,sourceU_two,sourceU_four,map_add,map_sub,map_mul,map_pow,
    map_one,map_ofNat,hg,hu,hw2,hw3,hhalf,W₅]
  dsimp only [dualClosed]
  simp only [map_add,map_sub,map_mul,map_pow,map_one,Polynomial.C_ofNat]

/-- Article: the actual central dual numerator has degree at most six. -/
theorem dualReal_natDegree (h : ℝ) (Z : Coordinates) : (dualReal h Z).natDegree≤6 := by
  rw [dualReal_closed]
  generalize (1/2+h*Z 0) = u
  generalize (1+h) = g
  generalize Z 5 = w2
  generalize Z 6 = w3
  dsimp only [dualClosed]
  compute_degree!

/-- Article: every source coefficient is real analytic in h and the original unknowns. -/
theorem sourceValue_analyticAt (P : SourcePolynomial) (p : ℝ × Coordinates) :
    AnalyticAt ℝ (fun q : ℝ × Coordinates => sourceEval (arguments q.1 q.2) P) p := by
  have hc : ∀ j : Fin 8, AnalyticAt ℝ (fun x : ℝ × Coordinates => arguments x.1 x.2 j) p := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [arguments,Fin.cons_zero] using
        (analyticAt_fst : AnalyticAt ℝ (Prod.fst : ℝ × Coordinates → ℝ) p)
    · simpa only [arguments,Fin.cons_succ,Function.comp_def,ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj k : Coordinates →L[ℝ] ℝ).analyticAt p.2).comp analyticAt_snd
  exact AnalyticAt.aeval_mvPolynomial hc P

/-- Article: all true dual polynomial coefficients vary analytically in the source data. -/
theorem dualReal_coeff_analyticAt (i : ℕ) (p : ℝ × Coordinates) :
    AnalyticAt ℝ (fun q : ℝ × Coordinates => (dualReal q.1 q.2).coeff i) p := by
  simpa only [dualReal,Polynomial.coeff_map] using sourceValue_analyticAt (dualSource.coeff i) p

/-- Article: interpretation commutes with source frequency evaluation. -/
theorem dualReal_eval (h : ℝ) (Z : Coordinates) (a : SourcePolynomial) :
    (dualReal h Z).eval (sourceEval (arguments h Z) a)=
      sourceEval (arguments h Z) (dualSource.eval a) := by
  exact Polynomial.eval_map_apply _ _

/-- Article: the real source derivative is the derivative of the real dual polynomial. -/
theorem dualReal_derivative_eval (h : ℝ) (Z : Coordinates) (a : SourcePolynomial) :
    (dualReal h Z).derivative.eval (sourceEval (arguments h Z) a)=
      sourceEval (arguments h Z) (dualSource.derivative.eval a) := by
  rw [dualReal,Polynomial.derivative_map]
  exact Polynomial.eval_map_apply _ _

/-- Article: every zero of the actual system supplies Q(y)=Q′(x)=Q′(y)=0. -/
theorem regularSystem_dual_exact (h : ℝ) (Z : Coordinates) :
    regularSystem (h,Z) 4=(dualReal h Z).eval (Z 2) ∧
    regularSystem (h,Z) 5=(dualReal h Z).derivative.eval (-1/2+h*Z 1) ∧
    regularSystem (h,Z) 6=(dualReal h Z).derivative.eval (Z 2) := by
  have h0 := Certificates.P5.dual_source_0 (arguments h Z)
  have h1 := Certificates.P5.dual_source_1 (arguments h Z)
  have h2 := Certificates.P5.dual_source_2 (arguments h Z)
  have hy : sourceEval (arguments h Z) Y=Z 2 := by norm_num [sourceEval,Y,sourceVar]
  have hx : sourceEval (arguments h Z) X=-1/2+h*Z 1 := by norm_num [sourceEval,X,H,sourceVar]
  norm_num only [dualNumerator,Fin.reduceEq,ite_true,ite_false] at h0 h1 h2
  rw [← dualReal_eval,hy] at h0
  rw [← dualReal_derivative_eval,hx] at h1
  rw [← dualReal_derivative_eval,hy] at h2
  exact ⟨h0,h1,h2⟩

end polyak.Boundary.P5
