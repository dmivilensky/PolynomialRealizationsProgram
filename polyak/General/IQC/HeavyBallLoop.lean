import polyak.General.IQC.BoundedLoop
import polyak.General.IQC.Nonlinearity
import polyak.General.IQC.FreePlant
import polyak.Growth.Extension

/-! Appendix D, Theorem one exponent: exact identification of the causal
feedback execution with every actual normalized heavy-ball trajectory. -/
noncomputable section
namespace polyak.General.IQC
open polyak Growth
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def plantGain (A B β t : ℝ) : ℝ := ∑' n,|plantImpulse A B β (Real.exp t) n|

theorem plantGain_nonneg (A B β t : ℝ) : 0≤plantGain A B β t:=
  tsum_nonneg (fun _ => abs_nonneg _)

def heavyBallFeedback {A B β t : ℝ} (hβ : 0≤β) (hr : rootRadius A β<Real.exp t)
    {ψ : E → ℝ} (hψ : NormalizedSmooth ψ) : Feedback E where
  plant:=stablePlant A B β (Real.exp t)
  strictlyCausal:=stablePlant_strictCausal _ _ _ _
  gain:=plantGain A B β t
  gain_nonneg:=plantGain_nonneg _ _ _ _
  prefix_gain:=stablePlant_prefix_gain hβ hr
  delta:=scaledGradient ψ t
  delta_causal:=scaledGradient_causal ψ t
  delta_zero:=scaledGradient_zero hψ t
  delta_nonexpansive:=scaledGradient_nonexpansive hψ t

def discountSequence (t : ℝ) (x : ℕ → E) (k : ℕ) : E := Real.exp (-((k:ℝ)*t)) • x k

omit [CompleteSpace E] in
@[simp] theorem discountSequence_zero (t : ℝ) (x : ℕ → E) : discountSequence t x 0=x 0:=by
  simp [discountSequence]

theorem scaledGradient_discount {ψ : E → ℝ} (t : ℝ) (x : ℕ → E) (k : ℕ) :
    scaledGradient ψ t (discountSequence t x) k=
      Real.exp (-((k:ℝ)*t)) • gradient ψ (x k) := by
  simp only [scaledGradient,discountSequence,smul_smul]
  rw [mul_comm (Real.exp _) (Real.exp _),exp_cancel,one_smul]

theorem discount_ratio (t : ℝ) (n : ℕ) :
    Real.exp (-(((n+1:ℕ):ℝ)*t))=(1/Real.exp t)*Real.exp (-((n:ℝ)*t)) := by
  rw [one_div,←Real.exp_neg,←Real.exp_add]
  congr 1
  push_cast
  ring

theorem discount_two_ratio (t : ℝ) (n : ℕ) :
    Real.exp (-(((n+2:ℕ):ℝ)*t))=(1/(Real.exp t)^2)*Real.exp (-((n:ℝ)*t)) := by
  rw [show n+2=(n+1)+1 by omega,discount_ratio,discount_ratio]
  ring

theorem discountSequence_recurrence {A B β t : ℝ} {ψ : E → ℝ} {x : ℕ → E}
    (hrec : ∀ k,x (k+2)=A • x (k+1)+B • gradient ψ (x (k+1))-β • x k) (n : ℕ) :
    discountSequence t x (n+2)=
      (A/Real.exp t) • discountSequence t x (n+1)-
      (β/(Real.exp t)^2) • discountSequence t x n+
      (B/Real.exp t) • scaledGradient ψ t (discountSequence t x) (n+1) := by
  rw [scaledGradient_discount]
  simp only [discountSequence,hrec,smul_add,smul_sub,smul_smul]
  have hA : Real.exp (-(((n+2:ℕ):ℝ)*t))*A=
      (A/Real.exp t)*Real.exp (-(((n+1:ℕ):ℝ)*t)):=by
    rw [show n+2=(n+1)+1 by omega,discount_ratio]
    ring
  have hB : Real.exp (-(((n+2:ℕ):ℝ)*t))*B=
      (B/Real.exp t)*Real.exp (-(((n+1:ℕ):ℝ)*t)):=by
    rw [show n+2=(n+1)+1 by omega,discount_ratio]
    ring
  have hβ : Real.exp (-(((n+2:ℕ):ℝ)*t))*β=
      (β/(Real.exp t)^2)*Real.exp (-((n:ℝ)*t)):=by
    rw [discount_two_ratio]
    ring
  rw [hA,hB,hβ]
  module

theorem run_feedback_equation {A B β t : ℝ} (r : Run E A B β) :
    discountSequence t (fun k => r.x (k+1))=
      stablePlant A B β (Real.exp t)
        (scaledGradient r.ψ t (discountSequence t (fun k => r.x (k+1))))+
      originalFreeResponse A β (Real.exp t) (r.x 0) (r.x 1) := by
  apply forced_decomposition
  · simp
  · rw [discountSequence,show (1:ℕ)+1=2 by omega,r.recurrence 0]
    simp only [Nat.zero_add,Nat.cast_one,scaledGradient_discount,
      Nat.cast_zero,zero_mul,neg_zero,Real.exp_zero,one_smul,smul_add,smul_sub,smul_smul]
    rw [Real.exp_neg]
    have he : (β/Real.exp t^2)*Real.exp t=β/Real.exp t:=by
      field_simp
    rw [he]
    module
  · intro n
    apply discountSequence_recurrence
    intro k
    simpa only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using r.recurrence (k+1)

theorem run_eq_feedback_execution {A B β t : ℝ} (hβ : 0≤β)
    (hr : rootRadius A β<Real.exp t) (r : Run E A B β) :
    discountSequence t (fun k => r.x (k+1))=
      (heavyBallFeedback (B:=B) hβ hr r.normalized).run 1
        (originalFreeResponse A β (Real.exp t) (r.x 0) (r.x 1)) := by
  apply causalSolve_unique
    ((heavyBallFeedback (B:=B) hβ hr r.normalized).loop_strictCausal 1)
  intro n
  have he:=congrFun (run_feedback_equation (t:=t) r) n
  simpa only [Feedback.loop,heavyBallFeedback,one_smul,Pi.add_apply] using he

end polyak.General.IQC
