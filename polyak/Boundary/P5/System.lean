import polyak.Certificates.P5System
import polyak.Boundary.P5.CriticalAlgebra

/-!
Article: (p5system), (blowup), the regularized seven-variable analytic system.
Use: its first four equations are exact h-divisions of the actual normalized
primal slacks; its remaining equations are the actual dual double-root equations.
The mathematical source and the finite coefficient certificates remain separate.
-/

noncomputable section
namespace polyak.Boundary.P5
open Spectral Certificates.P5

/-- Article: A,B,y,P,D,w₂,w₃, the original blown-up unknowns. -/
abbrev Coordinates := Fin 7 → ℝ

/-- Article: the source parameter and unknowns in one polynomial evaluation vector. -/
def arguments (h : ℝ) (Z : Coordinates) : Fin 8 → ℝ := Fin.cons h Z

/-- Article: exact coordinate 0 of the source evaluation vector. -/
@[simp] theorem arguments_0 (h : ℝ) (Z : Coordinates) : arguments h Z 0=h := rfl

/-- Article: exact coordinate 1 of the source evaluation vector. -/
@[simp] theorem arguments_1 (h : ℝ) (Z : Coordinates) : arguments h Z 1=Z 0 := rfl

/-- Article: exact coordinate 2 of the source evaluation vector. -/
@[simp] theorem arguments_2 (h : ℝ) (Z : Coordinates) : arguments h Z 2=Z 1 := rfl

/-- Article: exact coordinate 3 of the source evaluation vector. -/
@[simp] theorem arguments_3 (h : ℝ) (Z : Coordinates) : arguments h Z 3=Z 2 := rfl

/-- Article: exact coordinate 4 of the source evaluation vector. -/
@[simp] theorem arguments_4 (h : ℝ) (Z : Coordinates) : arguments h Z 4=Z 3 := rfl

/-- Article: exact coordinate 5 of the source evaluation vector. -/
@[simp] theorem arguments_5 (h : ℝ) (Z : Coordinates) : arguments h Z 5=Z 4 := rfl

/-- Article: exact coordinate 6 of the source evaluation vector. -/
@[simp] theorem arguments_6 (h : ℝ) (Z : Coordinates) : arguments h Z 6=Z 5 := rfl

/-- Article: exact coordinate 7 of the source evaluation vector. -/
@[simp] theorem arguments_7 (h : ℝ) (Z : Coordinates) : arguments h Z 7=Z 6 := rfl

/-- Article: all seven exact regularized equation polynomials, in source order. -/
def regularizedPolynomial : Fin 7 → SourcePolynomial := ![F0,F1,F2,F3,F4,F5,F6]

/-- Article: exact polynomial in equation slot 0. -/
@[simp] theorem regularizedPolynomial_0 : regularizedPolynomial 0=F0 := rfl

/-- Article: exact polynomial in equation slot 1. -/
@[simp] theorem regularizedPolynomial_1 : regularizedPolynomial 1=F1 := rfl

/-- Article: exact polynomial in equation slot 2. -/
@[simp] theorem regularizedPolynomial_2 : regularizedPolynomial 2=F2 := rfl

/-- Article: exact polynomial in equation slot 3. -/
@[simp] theorem regularizedPolynomial_3 : regularizedPolynomial 3=F3 := rfl

/-- Article: exact polynomial in equation slot 4. -/
@[simp] theorem regularizedPolynomial_4 : regularizedPolynomial 4=F4 := rfl

/-- Article: exact polynomial in equation slot 5. -/
@[simp] theorem regularizedPolynomial_5 : regularizedPolynomial 5=F5 := rfl

/-- Article: exact polynomial in equation slot 6. -/
@[simp] theorem regularizedPolynomial_6 : regularizedPolynomial 6=F6 := rfl

/-- Article: the actual regularized central-family system. -/
def regularSystem (p : ℝ × Coordinates) : Coordinates :=
  fun i => sourceEval (arguments p.1 p.2) (regularizedPolynomial i)

/-- Article: the exact critical seven-tuple in the original variable order. -/
def criticalPoint : Coordinates := ![A₀,B₀,y₀,P₀,D₀,w2₀,w3₀]

/-- Article: critical coordinate 0 in the original unknown order. -/
@[simp] theorem criticalPoint_0 : criticalPoint 0=A₀ := rfl

/-- Article: critical coordinate 1 in the original unknown order. -/
@[simp] theorem criticalPoint_1 : criticalPoint 1=B₀ := rfl

/-- Article: critical coordinate 2 in the original unknown order. -/
@[simp] theorem criticalPoint_2 : criticalPoint 2=y₀ := rfl

/-- Article: critical coordinate 3 in the original unknown order. -/
@[simp] theorem criticalPoint_3 : criticalPoint 3=P₀ := rfl

/-- Article: critical coordinate 4 in the original unknown order. -/
@[simp] theorem criticalPoint_4 : criticalPoint 4=D₀ := rfl

/-- Article: critical coordinate 5 in the original unknown order. -/
@[simp] theorem criticalPoint_5 : criticalPoint 5=w2₀ := rfl

/-- Article: critical coordinate 6 in the original unknown order. -/
@[simp] theorem criticalPoint_6 : criticalPoint 6=w3₀ := rfl

/-- Article: source Chebyshev evaluation commutes with interpretation in ℝ. -/
theorem sourceEval_T (z : Fin 8 → ℝ) (n : ℕ) (a : SourcePolynomial) :
    sourceEval z (sourceT n a)=chebT n (sourceEval z a) := by
  rw [sourceT,Polynomial.hom_eval₂]
  have he : (sourceEval z).comp MvPolynomial.C=algebraMap ℚ ℝ := by
    ext q
    simp [sourceEval]
  rw [he]
  change Polynomial.aeval (sourceEval z a) (Polynomial.Chebyshev.T ℚ (n : ℤ))=_
  rw [Polynomial.Chebyshev.aeval_T]
  rfl

/-- Article: the same source interpretation for the positive lag denominator. -/
theorem sourceEval_U (z : Fin 8 → ℝ) (n : ℕ) (a : SourcePolynomial) :
    sourceEval z (sourceU n a)=chebU n (sourceEval z a) := by
  rw [sourceU,Polynomial.hom_eval₂]
  have he : (sourceEval z).comp MvPolynomial.C=algebraMap ℚ ℝ := by
    ext q
    simp [sourceEval]
  rw [he]
  change Polynomial.aeval (sourceEval z a) (Polynomial.Chebyshev.U ℚ (n : ℤ))=_
  rw [Polynomial.Chebyshev.aeval_U]
  rfl

/-- Article: raw signed lag at an atom, expressed directly in the source quantities. -/
def actualRaw (u G : ℝ) (n : ℕ) (σ : ℝ) (c : ℝ) : ℝ :=
  g u c*(chebT n G-chebT n c)+σ*lagB u n c

/-- Article: the actual normalized two-atom primal equation, including its value charge. -/
def actualPrimal (h : ℝ) (Z : Coordinates) (n : ℕ) (σ : ℝ) : ℝ :=
  let u := 1/2+h*Z 0
  let x := -1/2+h*Z 1
  let p := h*Z 3
  ((1-p)*actualRaw u (1+h) n σ x+p*actualRaw u (1+h) n σ (Z 2))/
      lagDenominator (1+h) n-σ*h*Z 4

/-- Article: the separately defined source numerator is the true primal equation
multiplied by its nonzero Chebyshev denominator. -/
theorem sourceEval_primalNumerator {h : ℝ} (hh : 0 ≤ h) (Z : Coordinates)
    (n : ℕ) (hn : 1 ≤ n) (σ : ℚ) :
    sourceEval (arguments h Z) (primalNumerator n σ)=
      lagDenominator (1+h) n*actualPrimal h Z n σ := by
  have hden := (lagDenominator_pos (by linarith : (1 : ℝ) ≤ 1+h) n hn).ne'
  simp only [primalNumerator,sourceRaw,map_add,map_sub,map_mul,map_pow,map_one,
    sourceEval_T,sourceEval_U]
  norm_num [sourceEval,H,U,X,Y,Probability,Charge,G,sourceVar,
    actualPrimal,actualRaw,g,lagB,lagDenominator]
  dsimp only [lagDenominator] at hden
  field_simp [hden]

/-- Article: the four primal regularization identities at every nonnegative h.
No limiting or approximate division is used. -/
theorem regularSystem_primal_exact {h : ℝ} (hh : 0 ≤ h) (Z : Coordinates) :
    h*regularSystem (h,Z) 0=lagDenominator (1+h) 1*actualPrimal h Z 1 (-1) ∧
    h*regularSystem (h,Z) 1=2*lagDenominator (1+h) 2*actualPrimal h Z 2 1 ∧
    h*regularSystem (h,Z) 2=4*lagDenominator (1+h) 3*actualPrimal h Z 3 1 ∧
    h*regularSystem (h,Z) 3=4*lagDenominator (1+h) 5*actualPrimal h Z 5 1 := by
  have h0 := primal_division_0 (arguments h Z)
  have h1 := primal_division_1 (arguments h Z)
  have h2 := primal_division_2 (arguments h Z)
  have h3 := primal_division_3 (arguments h Z)
  rw [sourceEval_primalNumerator hh Z 1 (by omega),sourceEval_primalNumerator hh Z 2 (by omega),
    sourceEval_primalNumerator hh Z 3 (by omega),sourceEval_primalNumerator hh Z 5 (by omega)] at *
  norm_num [sourceEval,H,sourceVar] at h0 h1 h2 h3
  refine ⟨?_,?_,?_,?_⟩
  · simpa only [regularSystem,regularizedPolynomial_0,sourceEval,MvPolynomial.coe_eval₂Hom] using h0
  · simpa only [regularSystem,regularizedPolynomial_1,sourceEval,MvPolynomial.coe_eval₂Hom,mul_assoc] using h1
  · simpa only [regularSystem,regularizedPolynomial_2,sourceEval,MvPolynomial.coe_eval₂Hom,mul_assoc] using h2
  · simpa only [regularSystem,regularizedPolynomial_3,sourceEval,MvPolynomial.coe_eval₂Hom,mul_assoc] using h3

/-- Article: polynomial regularization makes the actual system real analytic at every point. -/
theorem regularSystem_analyticAt (p : ℝ × Coordinates) : AnalyticAt ℝ regularSystem p := by
  apply AnalyticAt.pi
  intro i
  have hc : ∀ j : Fin 8, AnalyticAt ℝ (fun x : ℝ × Coordinates => arguments x.1 x.2 j) p := by
    intro j
    refine Fin.cases ?_ (fun k => ?_) j
    · simpa only [arguments,Fin.cons_zero] using (analyticAt_fst : AnalyticAt ℝ (Prod.fst : ℝ × Coordinates → ℝ) p)
    · simpa only [arguments,Fin.cons_succ,Function.comp_def,ContinuousLinearMap.proj_apply] using
        ((ContinuousLinearMap.proj k : Coordinates →L[ℝ] ℝ).analyticAt p.2).comp analyticAt_snd
  exact AnalyticAt.aeval_mvPolynomial hc (regularizedPolynomial i)

end polyak.Boundary.P5
