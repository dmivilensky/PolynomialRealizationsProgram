import Mathlib.Analysis.InnerProductSpace.LaxMilgram
import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
The sole functional-analytic ingredient of the finite-state KYP proof.
A bounded symmetric quadratic form with coercively negative input block has
an attained maximum over inputs, and its maximizing input depends linearly
and continuously on the initial state. Consequently its value is a quadratic
form on the finite state, with no optimization oracle or assumed storage.
-/
namespace nesterov.IQC.KYP
noncomputable section
open scoped InnerProductSpace
variable {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup U] [InnerProductSpace ℝ U]

abbrev Bilinear (Y : Type*) [NormedAddCommGroup Y] [NormedSpace ℝ Y]:=
  Y→L[ℝ]Y→L[ℝ]ℝ

def stateIn : X→L[ℝ]X×U:=(ContinuousLinearMap.id ℝ X).prod 0
def inputIn : U→L[ℝ]X×U:=(0:U→L[ℝ]X).prod (ContinuousLinearMap.id ℝ U)

@[simp] theorem stateIn_apply (x : X) : (stateIn (U:=U)) x=(x,0):=rfl
@[simp] theorem inputIn_apply (u : U) : (inputIn (X:=X)) u=(0,u):=rfl

def inputForm (Q : Bilinear (X×U)) : Bilinear U:=
  -(Q.bilinearComp inputIn inputIn)

def crossForm (Q : Bilinear (X×U)) : X→L[ℝ]U→L[ℝ]ℝ:=
  Q.bilinearComp stateIn inputIn

@[simp] theorem inputForm_apply (Q : Bilinear (X×U)) (u v : U) :
    inputForm Q u v= -Q (0,u) (0,v):=rfl
@[simp] theorem crossForm_apply (Q : Bilinear (X×U)) (x : X) (u : U) :
    crossForm Q x u=Q (x,0) (0,u):=rfl

variable [CompleteSpace U]

/-- The maximizing input, constructed through the proved Lax-Milgram isomorphism. -/
def optimizer (Q : Bilinear (X×U)) (hQ : IsCoercive (inputForm Q)) : X→L[ℝ]U:=
  hQ.continuousLinearEquivOfBilin.symm.toContinuousLinearMap.comp
    (((InnerProductSpace.toDual ℝ U).symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (crossForm Q))

theorem optimizer_equation (Q : Bilinear (X×U)) (hQ : IsCoercive (inputForm Q))
    (x : X) (v : U) : inputForm Q (optimizer Q hQ x) v=crossForm Q x v := by
  have hh:=hQ.continuousLinearEquivOfBilin_apply (optimizer Q hQ x) v
  dsimp [optimizer] at hh
  simpa [optimizer] using hh.symm

def optimizerGraph (Q : Bilinear (X×U)) (hQ : IsCoercive (inputForm Q)) : X→L[ℝ]X×U:=
  (ContinuousLinearMap.id ℝ X).prod (optimizer Q hQ)

/-- Actual quadratic value, expressed by a bounded bilinear form on states. -/
def valueForm (Q : Bilinear (X×U)) (hQ : IsCoercive (inputForm Q)) : Bilinear X:=
  Q.bilinearComp (optimizerGraph Q hQ) (optimizerGraph Q hQ)

@[simp] theorem valueForm_apply (Q : Bilinear (X×U)) (hQ : IsCoercive (inputForm Q)) (x y : X) :
    valueForm Q hQ x y=Q (x,optimizer Q hQ x) (y,optimizer Q hQ y):=rfl

/-- Completion of squares: the cost loss is the coercive input form. -/
theorem value_identity (Q : Bilinear (X×U))
    (hsymm : ∀ a b,Q a b=Q b a) (hQ : IsCoercive (inputForm Q)) (x : X) (u : U) :
    Q (x,u) (x,u)=valueForm Q hQ x x-
      inputForm Q (u-optimizer Q hQ x) (u-optimizer Q hQ x) := by
  let v:=optimizer Q hQ x
  let d:=u-v
  have hp : (x,u)=(x,v)+(0,d) := by dsimp [d]; ext <;> simp
  have hsplit : (x,v)=(x,0)+(0,v) := by ext <;> simp
  have hc : Q (x,v) (0,d)=0 := by
    rw [hsplit,map_add,add_apply]
    have he:=optimizer_equation Q hQ x d
    change -Q (0,v) (0,d)=Q (x,0) (0,d) at he
    linarith
  have hc' : Q (0,d) (x,v)=0:=by rw [hsymm]; exact hc
  simp only [hp,map_add,add_apply,hc,hc',add_zero,zero_add,valueForm_apply,inputForm_apply]
  dsimp [v,d]
  ring

/-- The maximum is attained at the constructed linear optimizer. -/
theorem le_value (Q : Bilinear (X×U)) (hsymm : ∀ a b,Q a b=Q b a)
    (hQ : IsCoercive (inputForm Q)) (x : X) (u : U) : Q (x,u) (x,u)≤valueForm Q hQ x x := by
  rw [value_identity Q hsymm hQ]
  have hcQ:=hQ
  obtain ⟨c,hc,hbound⟩:=hcQ
  have hn:=hbound (u-optimizer Q hQ x)
  have hz : 0 ≤ inputForm Q (u-optimizer Q hQ x) (u-optimizer Q hQ x):=
    (by positivity : 0≤c*‖u-optimizer Q hQ x‖*‖u-optimizer Q hQ x‖).trans hn
  linarith

end
end nesterov.IQC.KYP
