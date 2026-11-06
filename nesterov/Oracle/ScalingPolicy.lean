import nesterov.Oracle.ResistingOracleHard
import polyak.Functions.Normalization

/-! Exact objective and adaptive-policy scaling between arbitrary smoothness
L>0 and the normalized oracle model. -/
namespace nesterov.Oracle
noncomputable section
open Set
open scoped RealInnerProductSpace

section Objectives
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def scaleObjective (L : ℝ) (g : E→ℝ) : E→ℝ := fun x=>L*g x

theorem scaleObjective_hasGradientAt {g : E→ℝ} (hg : Differentiable ℝ g) (L : ℝ) (x : E) :
    HasGradientAt (scaleObjective L g) (L • gradient g x) x := by
  change HasGradientAt (fun y=>L*g y) (L • gradient g x) x
  simpa only [zero_div,zero_mul,zero_smul,zero_add] using
    polyak.hasGradientAt_quadratic_add (hg x).hasGradientAt 0 L

theorem scaleObjective_gradient {g : E→ℝ} (hg : Differentiable ℝ g) (L : ℝ) (x : E) :
    gradient (scaleObjective L g) x=L • gradient g x := (scaleObjective_hasGradientAt hg L x).gradient

theorem scaleObjective_class {g : E→ℝ} {q L : ℝ} (hL : 0<L)
    (hg : polyak.SmoothStronglyConvex q 1 g) :
    polyak.SmoothStronglyConvex (L*q) L (scaleObjective L g) := by
  refine ⟨mul_pos hL hg.mu_pos,?_,?_,?_,?_⟩
  · nlinarith [hg.mu_lt_L]
  · exact hg.differentiable.const_mul L
  · intro x y
    rw [scaleObjective_gradient hg.differentiable,real_inner_smul_left]
    have h := mul_le_mul_of_nonneg_left (hg.tangent_lower x y) hL.le
    unfold scaleObjective
    nlinarith only [h]
  · intro x y
    rw [scaleObjective_gradient hg.differentiable,scaleObjective_gradient hg.differentiable,
      ←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hL]
    have h := mul_le_mul_of_nonneg_left (hg.grad_lipschitz x y) hL.le
    simpa only [one_mul] using h

end Objectives

section Policies
variable {E : Type*}

def scaleReply [SMul ℝ E] (L : ℝ) (r : Reply E) : Reply E := (L*r.1,L • r.2)

def scaleTranscript [SMul ℝ E] (L : ℝ) {n : ℕ} (t : Transcript E n) : Transcript E n :=
  fun i=>((t i).1,scaleReply L (t i).2)

namespace Policy
variable [SMul ℝ E]

def rescale (A : Policy E) (L : ℝ) : Policy E where
  query := fun n t=>A.query n (scaleTranscript L t)
  output := fun n t=>A.output n (scaleTranscript L t)

theorem scaleTranscript_snoc (L : ℝ) {n : ℕ} (t : Transcript E n) (x : E) (r : Reply E) :
    scaleTranscript L (Fin.snoc t (x,r))=Fin.snoc (scaleTranscript L t) (x,scaleReply L r) := by
  funext i
  refine Fin.lastCases ?_ (fun i=>?_) i
  · simp only [scaleTranscript,Fin.snoc_last]
  · simp only [scaleTranscript,Fin.snoc_castSucc]

theorem rescale_run (A : Policy E) (L : ℝ) (O : E→Reply E) (n : ℕ) :
    scaleTranscript L ((A.rescale L).run O n)=A.run (fun x=>scaleReply L (O x)) n := by
  induction n with
  | zero => funext i;exact Fin.elim0 i
  | succ n ih =>
    change scaleTranscript L (Fin.snoc ((A.rescale L).run O n)
      (A.query n (scaleTranscript L ((A.rescale L).run O n)),
        O (A.query n (scaleTranscript L ((A.rescale L).run O n)))))=
      Fin.snoc (A.run (fun x=>scaleReply L (O x)) n)
        (A.query n (A.run (fun x=>scaleReply L (O x)) n),
          scaleReply L (O (A.query n (A.run (fun x=>scaleReply L (O x)) n))))
    rw [scaleTranscript_snoc,ih]

theorem rescale_result (A : Policy E) (L : ℝ) (O : E→Reply E) (n : ℕ) :
    (A.rescale L).result O n=A.result (fun x=>scaleReply L (O x)) n := by
  change A.output n (scaleTranscript L ((A.rescale L).run O n))=A.output n _
  rw [A.rescale_run]

end Policy
end Policies

section ActualPolicies
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem firstOrderOracle_scaleObjective {g : E→ℝ} (hg : Differentiable ℝ g) (L : ℝ) :
    firstOrderOracle (scaleObjective L g)=fun x=>scaleReply L (firstOrderOracle g x) := by
  funext x
  simp only [firstOrderOracle,scaleObjective_gradient hg,scaleReply,scaleObjective]

theorem Policy.rescale_result_actual (A : Policy E) {g : E→ℝ} (hg : Differentiable ℝ g)
    (L : ℝ) (n : ℕ) :
    (A.rescale L).result (firstOrderOracle g) n=A.result (firstOrderOracle (scaleObjective L g)) n := by
  rw [A.rescale_result,firstOrderOracle_scaleObjective hg]

end ActualPolicies
end
end nesterov.Oracle
