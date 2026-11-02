import krylov.Methods.InformationSpan
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
Article: main_krylov, def:classes and lem:U(d), smooth observed coefficients.
Use: represent data-only coefficient decisions and their finite oracle programs;
regularity is imposed on the actual coefficient functions, not on a presumed
cycle map. The only access to unknown operators is the explicit query executor.
Source: finite linear combinations and the standard composition and bounded
bilinear evaluation rules for C^r maps in mathlib.
-/

namespace krylov.Methods
noncomputable section
open scoped BigOperators
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Coefficients chosen solely from a fixed finite list of actually observed vectors.
Use: fixed prior parameters may be captured in this function; unknown operator actions cannot be arguments.
Article: main_krylov, def:classes, smooth coefficients in observed vectors. -/
structure ObservedRule (E : Type*) (m : ℕ) where
  /-- The real coefficient of each available observed vector, as a function of those observations. -/
  coefficient : (Fin m → E) → Fin m → ℝ

/-- Execute the actual observed-data linear combination.
Use: the resulting physical decision automatically satisfies its exact information-span restriction.
Article: main_krylov, def:classes, span of observed data. -/
def ObservedRule.evaluate {m : ℕ} (f : ObservedRule E m) (data : Fin m → E) : E :=
  combine data (f.coefficient data)

/-- The coefficients themselves are unchanged by positive scaling of the actual data.
Use: this is the source's degree-zero coefficient condition, independent of trajectory regularity.
Article: main_krylov, lem:U(c,d). -/
def ObservedRule.Homogeneous {m : ℕ} (f : ObservedRule E m) : Prop :=
  ∀ (data : Fin m → E) (c : ℝ), 0<c → f.coefficient (fun i => c • data i)=f.coefficient data

/-- Every finite observed-coefficient decision lies in the genuine span of its actual inputs.
Use: finite-program representations enforce nonanticipation and span admissibility by construction.
Article: main_krylov, def:classes.
Proof: each actual summand is a multiple of an actual observed input vector. -/
theorem ObservedRule.evaluate_mem {m : ℕ} (f : ObservedRule E m) (data : Fin m → E) :
    f.evaluate data∈Submodule.span ℝ (Set.range data) := combine_mem_span _ _

/-- Genuine C^r observed coefficient functions give a genuine C^r physical decision after actual smooth observations.
Use: derive cycle regularity from the source's coefficient hypothesis, without assuming a regular cycle map.
Article: main_krylov, def:classes and lem:U(d).
Proof: compose the real coefficient function with the actual observation map,
then sum its scalar products with the actual smooth observed vectors. -/
theorem ObservedRule.evaluate_contDiffAt {m : ℕ} {r : WithTop ℕ∞} (f : ObservedRule E m)
    (data : X → Fin m → E) (x : X) (hf : ContDiffAt ℝ r f.coefficient (data x))
    (hd : ContDiffAt ℝ r data x) : ContDiffAt ℝ r (fun p => f.evaluate (data p)) x := by
  -- Coefficient smoothness is a hypothesis on data space, so it is composed before evaluating the true sum.
  have hc := hf.comp x hd
  convert! ContDiffAt.sum (s := Finset.univ) (fun i _ =>
    ((contDiffAt_pi.mp hc) i).smul ((contDiffAt_pi.mp hd) i)) using 1

/-- Degree-zero actual observed coefficients make the actual vector decision positively homogeneous of degree one.
Use: homogeneous-cone Taylor constants apply to actual decision outputs.
Article: main_krylov, lem:U(c).
Proof: the coefficients stay fixed, so commute the common positive scalar through the finite physical sum. -/
theorem ObservedRule.evaluate_homogeneous {m : ℕ} (f : ObservedRule E m)
    (hf : f.Homogeneous) (data : Fin m → E) (c : ℝ) (hc : 0<c) :
    f.evaluate (fun i => c • data i)=c • f.evaluate data := by
  simp only [ObservedRule.evaluate,hf data c hc,combine,Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

/-- A finite data-only oracle program chooses observed-span queries and finally an unevaluated vector output.
Use: each query makes exactly one unknown operator action available to the continuation; fixed finite correction phases and finite method cycles have this form.
Article: main_krylov, def:classes, smooth finite observation programs. -/
inductive ObservedProgram (E : Type*) : ℕ → Type _ where
  /-- Return a decision from already observed data, without evaluating it. -/
  | output {m : ℕ} (rule : ObservedRule E m) : ObservedProgram E m
  /-- Query the chosen vector, then append its observed image and the queried vector to the actual data. -/
  | query {m : ℕ} (rule : ObservedRule E m) (next : ObservedProgram E (m+2)) : ObservedProgram E m

/-- Execute the finite program against actual query operators.
Use: the continuation sees only its real new observed image and real chosen vector; terminal outputs cause no query.
Article: main_krylov, def:classes, actual finite execution. -/
def ObservedProgram.run {m : ℕ} (P : ObservedProgram E m) (A : ℕ → E →L[ℝ] E)
    (data : Fin m → E) (offset : ℕ) : E :=
  match P with
  | .output f => f.evaluate data
  | .query f next =>
      let step := f.evaluate data
      next.run A (Fin.cons (A offset step) (Fin.cons step data)) (offset+1)

/-- Every coefficient decision encountered on the true reference execution is C^r at its true observed data.
Use: this local condition is on primitive coefficient rules only; it does not assume smoothness of the trajectory or of any operator action.
Article: main_krylov, lem:U(d), smooth coefficients near reference data. -/
def ObservedProgram.RegularAt {m : ℕ} (P : ObservedProgram E m) (r : WithTop ℕ∞)
    (A : ℕ → E →L[ℝ] E) (data : Fin m → E) (offset : ℕ) : Prop :=
  match P with
  | .output f => ContDiffAt ℝ r f.coefficient data
  | .query f next => ContDiffAt ℝ r f.coefficient data ∧
      next.RegularAt r A (Fin.cons (A offset (f.evaluate data)) (Fin.cons (f.evaluate data) data)) (offset+1)

/-- A finite observed program with actual smooth coefficients has a genuine smooth output under smooth primitive operators and initial observations.
Use: closes the finite smooth-policy regularity implication used by the compact-reference Taylor calculus.
Article: main_krylov, def:classes and lem:U(d).
Proof: induct over real queries. The current coefficient rule is composed
with actual smooth data, bounded bilinear operator evaluation gives the actual
new image, and the induction applies to the genuine enlarged observation list. -/
theorem ObservedProgram.run_contDiffAt {m : ℕ} (P : ObservedProgram E m) {r : WithTop ℕ∞}
    (A : X → ℕ → E →L[ℝ] E) (data : X → Fin m → E) (x : X) (offset : ℕ)
    (hA : ∀ j, ContDiffAt ℝ r (fun p => A p j) x) (hd : ContDiffAt ℝ r data x)
    (hP : P.RegularAt r (A x) (data x) offset) :
    ContDiffAt ℝ r (fun p => P.run (A p) (data p) offset) x := by
  -- Each induction step adds only the actual query and its one true oracle image.
  induction P generalizing offset with
  | output f => exact f.evaluate_contDiffAt data x hP hd
  | query f next ih =>
    have hs := f.evaluate_contDiffAt data x hP.1 hd
    have hz := (hA offset).clm_apply hs
    apply ih _ (offset+1) ?_ hP.2
    apply contDiffAt_pi.mpr
    exact Fin.cases hz (Fin.cases hs (fun i => (contDiffAt_pi.mp hd) i))

/-- All coefficient decisions in the finite program are homogeneous of degree zero.
Use: a coefficient-level condition suffices for actual vector-output homogeneity.
Article: main_krylov, lem:U(c,d). -/
def ObservedProgram.Homogeneous {m : ℕ} : ObservedProgram E m → Prop
  | .output f => f.Homogeneous
  | .query f next => f.Homogeneous ∧ next.Homogeneous

/-- The actual finite oracle program is positively homogeneous when its primitive coefficients are degree zero.
Use: cone remainder transfer applies to real outputs, with no assumed trajectory homogeneity.
Article: main_krylov, lem:U(c,d).
Proof: a scaled query has the scaled image under its actual linear operator;
the next real observation list is therefore the scaled unperturbed list, and induction reaches the actual unevaluated output. -/
theorem ObservedProgram.run_homogeneous {m : ℕ} (P : ObservedProgram E m)
    (hP : P.Homogeneous) (A : ℕ → E →L[ℝ] E) (data : Fin m → E) (offset : ℕ)
    (c : ℝ) (hc : 0<c) :
    P.run A (fun i => c • data i) offset=c • P.run A data offset := by
  -- The same actual operator is used on each side; only the physical observed vectors scale.
  induction P generalizing offset with
  | output f => exact f.evaluate_homogeneous hP data c hc
  | query f next ih =>
    simp only [ObservedProgram.run,f.evaluate_homogeneous hP.1 data c hc,map_smul]
    have he : Fin.cons (c • A offset (f.evaluate data))
        (Fin.cons (c • f.evaluate data) (fun i => c • data i))=
        fun i => c • ((Fin.cons (A offset (f.evaluate data))
          (Fin.cons (f.evaluate data) data) : Fin (_+2) → E) i) := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i
    rw [he]
    exact ih hP.2 _ (offset+1)

end
end krylov.Methods
