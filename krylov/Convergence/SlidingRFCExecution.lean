import krylov.Convergence.SS1Execution
import krylov.Convergence.WindowNormalization
import krylov.Convergence.SecantWindowGates

/-!
Article: main_krylov, thm:Ip, literal sliding RFC with an evaluated probe.
Use: construct the actual observed direction, genuine current probe and
one model-correction query before proving any convergence properties.
Source: the original RFC observed-data coefficient rule. Probe lengths
are an arbitrary observed policy, covering the article's bounded probes;
the latest model contains its true evaluated current gradient secant.
-/

namespace krylov.Convergence
noncomputable section
open Matrix krylov.Methods krylov.Secant
open scoped InnerProductSpace BigOperators Matrix.Norms.L2Operator
variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Current true observed RFC direction on its chronological retained
window, independent of any unknown Hessian. -/
def slidingRFCWindowDirection (G : E → E) (q : Fin (n+2) → E) : E :=
  conjugacyDirection (fun i : Fin (n+1)=>q i.succ-q i.castSucc)
    (fun i=>G (q i.succ)-G (q i.castSucc)) (G (q (Fin.last (n+1))))

/-- Actual RFC evaluated probe displacement. -/
def slidingRFCWindowProbe (G : E → E) (probe : (Fin (n+2) → E) → E → ℝ)
    (q : Fin (n+2) → E) : E :=
  probe q (slidingRFCWindowDirection G q) • slidingRFCWindowDirection G q

/-- A complete actual RFC iteration: true current gradient probe, the
original observed skew-defect gate, then one real correction query. -/
def evaluatedRFCPoint (G : E → E) (s y : Fin (n+1) → E) (x v : E) (γ : ℝ) : E := by
  classical
  let U : Fin (n+2) → E := Fin.snoc s v
  let Z : Fin (n+2) → E := Fin.snoc y (G (x+v)-G x)
  exact if ‖pairDefect s y‖<γ then
    x+v+combine U (modelCoefficients U (ss1Model U Z) (G (x+v))) else x+v

/-- The window rule uses exactly its retained genuine secants and chosen
observed-direction probe in the actual evaluated RFC point. -/
def slidingRFCWindowRule (G : E → E) (probe : (Fin (n+2) → E) → E → ℝ)
    (γ : ℝ) (q : Fin (n+2) → E) : E :=
  evaluatedRFCPoint G (fun i=>q i.succ-q i.castSucc)
    (fun i=>G (q i.succ)-G (q i.castSucc)) (q (Fin.last (n+1))) (slidingRFCWindowProbe G probe q) γ

/-- The actual observed conjugacy matrix for the retained chronological
RFC window. Its nonsingularity is the article's defined-solve condition. -/
def slidingRFCSolveMatrix (G : E → E) (x : ℕ → E) (k : ℕ) : Matrix (Fin (n+1)) (Fin (n+1)) ℝ :=
  crossGram (windowImage G x k) (windowStep x k)

/-- The actual evaluated displacement chosen from the observed window. -/
def slidingRFCProbe (G : E → E) (probe : (Fin (n+2) → E) → E → ℝ)
    (x : ℕ → E) (k : ℕ) : E :=
  slidingRFCWindowProbe G probe (fun i=>x (k+i.val))

/-- Every genuine evaluated RFC probe has the measured conjugacy enforced
by the actual old observed coefficient inverse. -/
theorem slidingRFCProbe_conjugate (G : E → E) (probe : (Fin (n+2) → E) → E → ℝ)
    (x : ℕ → E) (k : ℕ) (hsolve : IsUnit (slidingRFCSolveMatrix (n:=n) G x k).det)
    (i : Fin (n+1)) : inner ℝ (windowImage G x k i) (slidingRFCProbe G probe x k)=0 := by
  let Q : Fin (n+2) → E := fun j=>x (k+j.val)
  have hsQ : (fun i : Fin (n+1)=>Q i.succ-Q i.castSucc)=windowStep x k := by
    funext i
    simp only [Q,windowStep,Fin.val_succ,Fin.val_castSucc,Nat.add_assoc]
  have hyQ : (fun i : Fin (n+1)=>G (Q i.succ)-G (Q i.castSucc))=windowImage G x k := by
    funext i
    simp only [Q,windowImage,Fin.val_succ,Fin.val_castSucc,Nat.add_assoc]
  have hc := congrFun (conjugacyDirection_conjugate (windowStep (n:=n+1) x k)
    (windowImage G x k) (G (x (k+n+1))) hsolve) i
  have hd : slidingRFCWindowDirection G Q=
      conjugacyDirection (windowStep (n:=n+1) x k) (windowImage G x k) (G (x (k+n+1))) := by
    rw [slidingRFCWindowDirection,hsQ,hyQ]
    rfl
  change inner ℝ (windowImage G x k i)
    (probe Q (slidingRFCWindowDirection G Q) • slidingRFCWindowDirection G Q)=0
  rw [real_inner_smul_right,hd]
  change probe Q _*coordinates (windowImage G x k)
    (conjugacyDirection (windowStep (n:=n+1) x k) (windowImage G x k) (G (x (k+n+1)))) i=0
  simp only [hc,Pi.zero_apply,mul_zero]

/-- Literal earlier-point recursive execution of sliding RFC. -/
def slidingRFCSequence (G : E → E) (probe : (Fin (n+2) → E) → E → ℝ)
    (γ : ℝ) (seed : Fin (n+2) → E) : ℕ → E :=
  slidingSequence (slidingRFCWindowRule G probe γ) seed

theorem slidingRFCSequence_step (G : E → E) (probe : (Fin (n+2) → E) → E → ℝ)
    (γ : ℝ) (seed : Fin (n+2) → E) (k : ℕ) :
    slidingRFCSequence G probe γ seed (k+n+2)=
      slidingRFCWindowRule G probe γ (fun i=>slidingRFCSequence G probe γ seed (k+i.val)) :=
  slidingSequence_step _ _ _

/-- The real recursive query uses exactly the genuine sliding stored
secants, current point and observed-direction evaluated probe. -/
theorem slidingRFCSequence_step_eq_evaluated (G : E → E)
    (probe : (Fin (n+2) → E) → E → ℝ) (γ : ℝ) (seed : Fin (n+2) → E) (k : ℕ) :
    slidingRFCSequence G probe γ seed (k+n+2)=
      evaluatedRFCPoint G (windowStep (n:=n+1) (slidingRFCSequence G probe γ seed) k)
        (windowImage G (slidingRFCSequence G probe γ seed) k)
        (slidingRFCSequence G probe γ seed (k+n+1))
        (slidingRFCProbe G probe (slidingRFCSequence G probe γ seed) k) γ := by
  rw [slidingRFCSequence_step]
  change slidingRFCWindowRule G probe γ _=evaluatedRFCPoint G
    (fun i : Fin (n+1)=>slidingRFCSequence G probe γ seed (k+i.val+1)-
      slidingRFCSequence G probe γ seed (k+i.val))
    (fun i=>G (slidingRFCSequence G probe γ seed (k+i.val+1))-
      G (slidingRFCSequence G probe γ seed (k+i.val))) _ _ _
  simp only [slidingRFCWindowRule,slidingRFCProbe,Fin.val_succ,Fin.val_castSucc,Fin.val_last,Nat.add_assoc]

/-- The exact chronological latest model keeps the actually evaluated
current probe image in its final column. -/
theorem ss1Model_snoc_current_column (s y : Fin (n+1) → E) (v z : E) :
    ss1Model (Fin.snoc s v) (Fin.snoc y z)*ᵥPi.single (Fin.last (n+1)) 1=
      coordinates (Fin.snoc s v) z := by
  ext i
  simp only [mulVec_single_one,Matrix.col_apply,ss1Model,latest,crossGram,Fin.le_last,min_eq_left,max_eq_right,
    Fin.snoc_last,coordinates]

/-- A current genuine probe followed by the actual latest-model solve is
exactly the anchored Newton-model step. The probe length cancels; this is
an identity of computed data, rather than an assumed output formula. -/
theorem ss1Probe_anchor (s y : Fin (n+1) → E) (x v g z : E)
    (hM : IsUnit (ss1Model (Fin.snoc s v) (Fin.snoc y z)).det) :
    x+v+combine (Fin.snoc s v) (modelCoefficients (Fin.snoc s v)
      (ss1Model (Fin.snoc s v) (Fin.snoc y z)) (g+z))=
      ss1Point (Fin.snoc s v) (Fin.snoc y z) g x := by
  let U : Fin (n+2) → E := Fin.snoc s v
  let M := ss1Model U (Fin.snoc y z)
  let e : Fin (n+2) → ℝ := Pi.single (Fin.last (n+1)) 1
  have he : M⁻¹*ᵥcoordinates U z=e := by
    rw [←ss1Model_snoc_current_column s y v z,mulVec_mulVec,nonsing_inv_mul _ hM,one_mulVec]
  have hc : modelCoefficients U M (g+z)=modelCoefficients U M g-e := by
    have hcoords : coordinates U (g+z)=coordinates U g+coordinates U z := by
      funext i
      exact inner_add_right (U i) g z
    rw [modelCoefficients,modelCoefficients,hcoords,mulVec_add,he]
    abel
  have hcombine (c : Fin (n+2) → ℝ) : combine U (c-e)=combine U c-v := by
    simp only [combine,Pi.sub_apply,sub_smul,Finset.sum_sub_distrib]
    have hu : ∑ i,e i • U i=v := by simp [e,Pi.single_apply,U]
    rw [hu]
  rw [hc,hcombine,ss1Point]
  abel

/-- Once its genuine observed gate accepts and its actual coefficient
inverse is defined, evaluated RFC is the anchored actual secant query. -/
theorem evaluatedRFCPoint_eq_ss1Point (G : E → E) (s y : Fin (n+1) → E) (x v : E) (γ : ℝ)
    (hgate : ‖pairDefect s y‖<γ)
    (hM : IsUnit (ss1Model (Fin.snoc s v) (Fin.snoc y (G (x+v)-G x))).det) :
    evaluatedRFCPoint G s y x v γ=
      ss1Point (Fin.snoc s v) (Fin.snoc y (G (x+v)-G x)) (G x) x := by
  classical
  rw [evaluatedRFCPoint,ite_eq_left hgate]
  have hh := ss1Probe_anchor s y x v (G x) (G (x+v)-G x) hM
  simpa only [add_sub_cancel] using hh

end
end krylov.Convergence
