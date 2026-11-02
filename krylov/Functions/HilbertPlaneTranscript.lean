import krylov.Functions.HilbertPlaneObjective

/-!
Article: main_krylov, prop:Fcycle(iii), exact full-space function information.
Use: retain all actual sampled values and gradients, and even the complete
objective restrictions of every observed line. Equal binary observations
give exactly equal rich transcripts; every trapezoid defect is computed
from these observations. Source: the genuine invisible cubic data fibre.
-/
namespace krylov.Functions
noncomputable section
open krylov.Tensor.BinaryCubic
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The full actual finite search information, including complete search
line objectives. It permits every data-only final output, without a size
or continuity restriction on that output. Article: main_krylov, prop:Fcycle(iii). -/
@[ext] structure FunctionSearchTranscript (E : Type*) (N : ℕ) where
  /-- All actual sampled points, already known to the method. -/
  points : Fin (N+1) → E
  /-- The actual evaluated line steps, already known to the method. -/
  lineSteps : Fin N → E
  /-- All actual sampled scalar values. -/
  values : Fin (N+1) → ℝ
  /-- All actual sampled Riesz gradients. -/
  gradients : Fin (N+1) → E
  /-- The entire true objective on every observed search line. -/
  lineObjectives : Fin N → ℝ → ℝ

/-- Build the rich transcript by actual scalar/gradient evaluations.
Article: main_krylov, prop:Fcycle(iii). -/
def functionSearchTranscript (f : E → ℝ) (x s : ℕ → E) (N : ℕ) : FunctionSearchTranscript E N :=
  ⟨fun i=>x i.val,fun i=>s i.val,fun i => f (x i.val),fun i => gradient f (x i.val),fun i α => f (x i.val+α • s i.val)⟩

omit [CompleteSpace E] in
/-- The exact difference of the full-space scalar sources is the original
invisible cubic, with true inner-product coordinates. Article: prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_difference (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (x : E) :
    hilbertPlaneObjective e h m p r u x-hilbertPlaneObjective e h m p r t x=
      valueFibreCubic (innerSL ℝ e) (innerSL ℝ h) (u.t2-t.t2) p r x := by
  have hf (v : krylov.Tensor.BinaryCubic) :
      planarValueFamily (ContinuousLinearMap.fst ℝ ℝ ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ)
        p r v (pairOfPlane (hilbertPlaneProject e h x))=
      planarValueFamily (innerSL ℝ e) (innerSL ℝ h) p r v x := rfl
  have hd := planarValueFamily_difference (innerSL ℝ e) (innerSL ℝ h) p r t u hobs x
  simp only [hilbertPlaneObjective,planeCubicObjective,planarCubicObjective,hf]
  linear_combination hd

omit [CompleteSpace E] in
/-- The full scalar equality holds before any policy is chosen.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_eq_add_fibre (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) :
    hilbertPlaneObjective e h m p r u=fun x => hilbertPlaneObjective e h m p r t x+
      valueFibreCubic (innerSL ℝ e) (innerSL ℝ h) (u.t2-t.t2) p r x := by
  funext x
  have hh := hilbertPlaneObjective_difference e h m p r t u hobs x
  linarith only [hh]

/-- True full-space values and true full-space gradients coincide at all
three observed planar samples. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_sample_equal (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (x : E)
    (hx : (inner ℝ e x=0 ∧ inner ℝ h x=0) ∨
      (inner ℝ e x=p ∧ inner ℝ h x=0) ∨ (inner ℝ e x=p ∧ inner ℝ h x=r*p)) :
    hilbertPlaneObjective e h m p r u x=hilbertPlaneObjective e h m p r t x ∧
      gradient (hilbertPlaneObjective e h m p r u) x=gradient (hilbertPlaneObjective e h m p r t) x := by
  have hf := hilbertPlaneObjective_eq_add_fibre e h m p r t u hobs
  rw [hf]
  exact ⟨(add_valueFibreCubic_sample _ _ _ _ _ p r x
      (hilbertPlaneObjective_hasFDerivAt e h m p r t x) hx).1,
    add_valueFibreCubic_gradient _ _ _ _ _ p r x
      (hilbertPlaneObjective_hasFDerivAt e h m p r t x) hx⟩

omit [CompleteSpace E] in
/-- The entire full-space objective restrictions coincide on every actual
first, intermediate or last observed line. Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_search_equal (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u) (x s : E)
    (hline : (inner ℝ h x=0 ∧ inner ℝ h s=0) ∨
      (inner ℝ e x=p ∧ inner ℝ e s=0)) :
    (fun α : ℝ => hilbertPlaneObjective e h m p r u (x+α • s))=
      (fun α : ℝ => hilbertPlaneObjective e h m p r t (x+α • s)) := by
  rw [hilbertPlaneObjective_eq_add_fibre e h m p r t u hobs]
  exact add_valueFibreCubic_search_line _ _ _ _ p r x s hline

/-- Equal actual binary observations force equality of all actual rich
function information, for every observed reference line and node.
Article: main_krylov, prop:Fcycle(iii). -/
theorem hilbertPlaneObjective_transcript_equal (e h m : E) (p r : ℝ)
    (t u : krylov.Tensor.BinaryCubic) (hobs : observe r t=observe r u)
    (x s : ℕ → E) (N : ℕ)
    (hpoints : ∀ i≤N, (inner ℝ e (x i)=0 ∧ inner ℝ h (x i)=0) ∨
      (inner ℝ e (x i)=p ∧ inner ℝ h (x i)=0) ∨ (inner ℝ e (x i)=p ∧ inner ℝ h (x i)=r*p))
    (hlines : ∀ i<N, (inner ℝ h (x i)=0 ∧ inner ℝ h (s i)=0) ∨
      (inner ℝ e (x i)=p ∧ inner ℝ e (s i)=0)) :
    functionSearchTranscript (hilbertPlaneObjective e h m p r u) x s N=
      functionSearchTranscript (hilbertPlaneObjective e h m p r t) x s N := by
  apply FunctionSearchTranscript.ext
  · rfl
  · rfl
  · funext i
    exact (hilbertPlaneObjective_sample_equal e h m p r t u hobs _ (hpoints i.val (by omega))).1
  · funext i
    exact (hilbertPlaneObjective_sample_equal e h m p r t u hobs _ (hpoints i.val (by omega))).2
  · funext i
    exact hilbertPlaneObjective_search_equal e h m p r t u hobs _ _ (hlines i.val i.isLt)

end
end krylov.Functions
