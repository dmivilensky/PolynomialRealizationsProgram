import polyak.Numerics.Root
import polyak.Numerics.Taylor
import polyak.Numerics.Modular

/-!
Article: Appendix B, Lemma p2ends and the positive denominator q₊ in Definition p2data.
Use: small literal certificates prove concrete source-polynomial theorems end to end.
Proof: exact endpoint evaluation, a Bernstein derivative certificate, independent
Taylor dominance and an annotated integer arithmetic graph with a source identity.
The later P₂ arc proof reuses these data; no experiment or graph plotting code is changed.
-/

noncomputable section
open scoped Polynomial
namespace polyak.Numerics
open Polynomial LeanCert.Core LeanCert.Engine

/-- Article: the defining cubic of the spiral-to-P₂ transition parameter ζ₁. -/
def transitionCubic : ℚ[X] := X^3-X^2-C 2

/-- Article: four exact rational coefficients encode the independent source cubic. -/
def transitionCubicCode : PolynomialCode transitionCubic where
  code := ⟨#[-2,0,-1,1]⟩
  exact := by
    change C (-2)+X*(C 0+X*(C (-1)+X*(C 1+X*0)))=X^3-X^2-C 2
    norm_num
    ring

/-- Article: the exact source derivative, obtained by the proved coefficient derivative engine. -/
def transitionDerivativeCode : PolynomialCode transitionCubic.derivative where
  code := ⟨#[0,-2,3]⟩
  exact := by
    change C 0+X*(C (-2)+X*(C 3+X*0))=(X^3-X^2-C (2 : ℚ)).derivative
    simp
    norm_num
    simp only [Polynomial.C_ofNat]
    ring

/-- Article: J=[1.6955,1.699], the exact rational parameter interval of the P₂ sign checks. -/
def transitionInterval : IntervalRat := ⟨3391/2000,1699/1000,by norm_num⟩

/-- Article: the narrow exact interval [1.6956,1.6957] isolating ζ₁. -/
def transitionRootInterval : IntervalRat := ⟨4239/2500,16957/10000,by norm_num⟩

/-- Article: the cubic is strictly increasing throughout the actual transition interval.
Proof: its exact Bernstein certificate has depth zero. -/
theorem transition_derivative_positive :
    ∀ x ∈ transitionInterval, 0 < Polynomial.aeval x transitionCubic.derivative := by
  apply transitionDerivativeCode.positive transitionInterval 0
  change QPoly.bernsteinCheck .strictLower ⟨#[0,-2,3]⟩ 0 ⟨3391/2000,1699/1000,by norm_num⟩ 0=true
  decide +kernel

/-- Article: the same concrete derivative sign is independently certified by Taylor dominance. -/
theorem transition_derivative_taylor : ∀ x : ℝ,
    |x-(6789/4000 : ℝ)| ≤ (7/4000 : ℝ) → 0 < Polynomial.aeval x transitionCubic.derivative := by
  have hc : taylorPositiveCheck transitionDerivativeCode.code (6789/4000) (7/4000)=true := by
    change taylorPositiveCheck ⟨#[0,-2,3]⟩ (6789/4000) (7/4000)=true
    decide +kernel
  have h := transitionDerivativeCode.positive_of_taylor (6789/4000) (7/4000) hc
  norm_num at h
  exact h

/-- Article: an actual algebraic transition root, proved unique in its rational enclosure. -/
theorem transition_root_exists : Nonempty (IsolatedRoot transitionCubic transitionRootInterval) := by
  apply exists_isolatedRoot transitionRootInterval
  · norm_num [transitionRootInterval,transitionCubic]
  · norm_num [transitionRootInterval,transitionCubic]
  · intro x hx
    apply transition_derivative_positive x
    rw [IntervalRat.mem_def] at hx ⊢
    norm_num [transitionRootInterval,transitionInterval] at hx ⊢
    constructor <;> linarith [hx.1,hx.2]

/-- Article: canonical name for the exactly isolated source transition parameter. -/
def transitionRoot : IsolatedRoot transitionCubic transitionRootInterval :=
  Classical.choice transition_root_exists

/-- Article: an exact modular coefficient certificate reduces the cube at ζ₁.
Use: demonstrates that finite array identities yield a theorem about the actual isolated root. -/
theorem transition_root_reduced_cube : transitionRoot.value^3=transitionRoot.value^2+2 := by
  have hc : remainderCodeCheck ⟨#[0,0,0,1]⟩ transitionCubicCode.code ⟨#[1]⟩ ⟨#[2,0,1]⟩=true := by
    decide +kernel
  have hr : Polynomial.aeval transitionRoot.value transitionCubicCode.code.toPoly=0 := by
    rw [transitionCubicCode.exact]
    exact transitionRoot.root
  have h := eval_at_root_of_code hc hr
  change Polynomial.aeval transitionRoot.value
    (C 0+X*(C 0+X*(C 0+X*(C 1+X*0)))) = Polynomial.aeval transitionRoot.value
    (C 2+X*(C 0+X*(C 1+X*0))) at h
  norm_num at h
  nlinarith

/-- Article: q₊=(ζ+1)²+1, retained as a mathematical polynomial source. -/
def qPlus : ℚ[X] := X^2+2*X+2

/-- Article: the arithmetic expression is independent of the proposed graph enclosures. -/
def qPlusExpression : chebyshev2.Numerics.IntegerCertificate.Expr :=
  .add (.mul (.add (.literal 1 1) (.input 0)) (.add (.literal 1 1) (.input 0))) (.literal 1 1)

open chebyshev2.Numerics.IntegerCertificate

/-- Article: four exact arithmetic nodes propose integer-scaled bounds for q₊ on [1,2]. -/
def qPlusGraph : List Node :=
  [⟨.literal 1 1,⟨1,1⟩⟩,⟨.add 0 1,⟨2,3⟩⟩,
    ⟨.mul 0 0,⟨4,9⟩⟩,⟨.add 0 2,⟨5,10⟩⟩]

/-- Article: concrete source polynomial positivity obtained from a checked annotated arithmetic graph. -/
theorem qPlus_positive_graph (x : ℝ) (hx : x ∈ Set.Icc (1 : ℝ) 2) :
    0 < Polynomial.aeval x qPlus := by
  let v : ℕ → ℝ := fun _ => x
  have hv : Encloses 1 [⟨1,2⟩] v := by
    intro i I hi
    cases i with
    | zero => simp only [List.getElem?_cons_zero,Option.some.injEq] at hi; subst I; simpa [Bounds.Mem,v] using hx
    | succ i => simp at hi
  have hsource : qPlusExpression.value v=Polynomial.aeval x qPlus := by
    simp [qPlusExpression,Expr.value,v,qPlus]
    have htwo : Polynomial.aeval x (2 : ℚ[X])=(2 : ℝ) := by norm_num [Polynomial.aeval_def]
    rw [htwo]
    ring
  have h := graph_source_enclosed (s := 1) (by norm_num) qPlusGraph hv (by decide)
    (source := qPlusExpression) (by decide) (i := 0) (I := ⟨5,10⟩) (by decide) hsource
  have hlow := h.1
  norm_num [Bounds.Mem] at hlow
  linarith

end polyak.Numerics
