import polyak.Boundary.Optimality
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-!
Article: Appendix B, (p1quartic) and (p1blowup).
Use: the actual one-atom quartic and its regularized contact equations are
specified independently of interval certificates and polynomial coefficient tables.
-/
noncomputable section
namespace polyak.Boundary.P1

abbrev Coordinates := Fin 2 → ℝ

def branchU (z A : ℝ) : ℝ := 1-z/2+z^2*A
def branchAtom (z B : ℝ) : ℝ := z^2*B

def quartic (z u c : ℝ) : ℝ :=
  -((1-c^2-u^2)*(2+z*c+z^2*(c^2-1))-2*u*z*(1-c^2)*(1+z*c))

def quarticDerivative (z u c : ℝ) : ℝ :=
  2*c*(2+z*c+z^2*(c^2-1))-(1-c^2-u^2)*(z+2*z^2*c)+
    2*u*z*(-2*c*(1+z*c)+z*(1-c^2))

def uLinear (z A : ℝ) : ℝ := -1/2+z*A
def gapLinear (z A B : ℝ) : ℝ := -(1/4+2*A)+z*A-z^2*(A^2+B^2)
def atomProductLinear (z B : ℝ) : ℝ := z^2*B-z^3*B^2-z^6*B^3
def contactQuadratic (z B : ℝ) : ℝ := -1+z*B+z^4*B^2

def regularEquation0 (z A B : ℝ) : ℝ :=
  2*uLinear z A+2*atomProductLinear z B+2*z*uLinear z A*atomProductLinear z B-
    2*gapLinear z A B-z*contactQuadratic z B-z^2*gapLinear z A B*contactQuadratic z B

def regularEquation1 (z A B : ℝ) : ℝ :=
  2*B*(2+z^3*B-z^2+z^6*B^2)-(1+z*gapLinear z A B)*(1+2*z^3*B)-
    4*branchU z A*z*B*(1+z^3*B)+2*branchU z A*(1-z^4*B^2)

def regularSystem (p : ℝ×Coordinates) : Coordinates :=
  ![regularEquation0 p.1 (p.2 0) (p.2 1),regularEquation1 p.1 (p.2 0) (p.2 1)]

theorem quartic_hasDerivAt (z u c : ℝ) :
    HasDerivAt (quartic z u) (quarticDerivative z u c) c := by
  have hc := hasDerivAt_id c
  have hg := ((hasDerivAt_const c (1 : ℝ)).sub (hc.pow 2)).sub (hasDerivAt_const c (u^2))
  have hD := ((hasDerivAt_const c (2 : ℝ)).add (hc.const_mul z)).add
    (((hc.pow 2).sub_const 1).const_mul (z^2))
  have hH := (((hasDerivAt_const c (1 : ℝ)).sub (hc.pow 2)).mul
    ((hasDerivAt_const c (1 : ℝ)).add (hc.const_mul z))).const_mul (2*u*z)
  convert (hg.mul hD).neg.add hH using 1
  · funext y
    dsimp [quartic]
    ring
  · dsimp [quarticDerivative]
    ring

theorem quartic_division (z A B : ℝ) :
    z^2*regularEquation0 z A B=quartic z (branchU z A) (branchAtom z B) := by
  unfold regularEquation0 uLinear gapLinear atomProductLinear contactQuadratic
    quartic branchU branchAtom
  ring

theorem derivative_division (z A B : ℝ) :
    z^2*regularEquation1 z A B=quarticDerivative z (branchU z A) (branchAtom z B) := by
  unfold regularEquation1 gapLinear quarticDerivative branchU branchAtom
  ring

def criticalPoint : Coordinates := ![1/8,-1/4]

theorem regularSystem_zero (Z : Coordinates) :
    regularSystem (0,Z)=![4*Z 0-1/2,4*Z 1+1] := by
  ext i
  fin_cases i <;> simp [regularSystem,regularEquation0,regularEquation1,uLinear,gapLinear,
    atomProductLinear,contactQuadratic,branchU] <;> ring

theorem regularSystem_criticalPoint : regularSystem (0,criticalPoint)=0 := by
  rw [regularSystem_zero]
  ext i
  fin_cases i <;> norm_num [criticalPoint]

theorem criticalPoint_unique (Z : Coordinates) (h : regularSystem (0,Z)=0) :
    Z=criticalPoint := by
  rw [regularSystem_zero] at h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  norm_num at h0 h1
  ext i
  fin_cases i
  · change Z 0=1/8
    linarith
  · change Z 1= -1/4
    linarith

end polyak.Boundary.P1
