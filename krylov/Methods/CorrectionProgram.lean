import krylov.Methods.ObservedRules
import krylov.Stability.SmoothLists

/-!
Article: main_krylov, def:classes and lem:U(d), finite smooth correction compilation.
Use: compile primitive observed coefficient rules into the actual adaptive
correction decision tree and prove regularity of its true movement, returned
gradient and complete actual observed trace directly from those coefficients.
Source: genuine runCorrections execution, observed coefficient composition
and actual finite-vector charts for variable-length protocol traces.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability
variable {E X : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A finite correction query program built from primitive actual observed coefficient rules.
Use: compiles the source finite correction schedule into a genuine nonanticipating tree.
Article: main_krylov, def:classes and lem:U(d). -/
inductive CorrectionProgram (E : Type*) : ℕ → Type _ where
  /-- End the actual finite correction phase without another oracle query. -/
  | done {m : ℕ} : CorrectionProgram E m
  /-- Query the real observed-span decision and retain both the returned gradient and chosen vector. -/
  | query {m : ℕ} (rule : ObservedRule E m) (next : CorrectionProgram E (m+2)) : CorrectionProgram E m

/-- Compile a finite observed-coefficient correction program into the actual nonanticipating correction tree.
Use: Compile a finite observed-coefficient correction program into the actual nonanticipating correction tree.
Article: main_krylov, def:classes and lem:U(d), finite smooth correction compilation.
Proof: Only the true new returned gradient selects the continuation data. -/
def CorrectionProgram.tree {m : ℕ} (P : CorrectionProgram E m) (data : Fin m → E) : CorrectionTree E :=
  match P with
  | .done => .done
  | .query f next => .query (f.evaluate data) (fun gnew => next.tree (Fin.cons gnew (Fin.cons (f.evaluate data) data)))

/-- Primitive coefficient functions are C-r at the actual data reached by the genuine reference execution.
Use: Primitive coefficient functions are C-r at the actual data reached by the genuine reference execution.
Article: main_krylov, def:classes and lem:U(d), finite smooth correction compilation.
Proof: The condition is recursive on coefficient rules and actual oracle observations, without a trajectory regularity premise. -/
def CorrectionProgram.RegularAt {m : ℕ} (P : CorrectionProgram E m) (r : WithTop ℕ∞)
    (B : E →L[ℝ] E) (g : E) (data : Fin m → E) : Prop :=
  match P with
  | .done => True
  | .query f next => ContDiffAt ℝ r f.coefficient data ∧
      next.RegularAt r B (g+B (f.evaluate data)) (Fin.cons (g+B (f.evaluate data)) (Fin.cons (f.evaluate data) data))

/-- The actual correction trace flattened into its genuinely observed displacement/gradient list.
Use: The actual correction trace flattened into its genuinely observed displacement/gradient list.
Article: main_krylov, def:classes and lem:U(d), finite smooth correction compilation.
Proof: Both coordinates of every actual query remain available. -/
def correctionObservations (trace : List (E × E)) : List E := trace.flatMap fun p => [p.1,p.2]

/-- The actual compiled correction executor has C-r movement and returned gradient and a genuine smooth chart of every intermediate observation.
Use: The actual compiled correction executor has C-r movement and returned gradient and a genuine smooth chart of every intermediate observation.
Article: main_krylov, def:classes and lem:U(d), finite smooth correction compilation.
Proof: Induct on the actual finite correction program. Compose its primitive coefficient rule, apply the true operator to the actual chosen displacement and add the real returned gradient to the true continuation chart. -/
theorem CorrectionProgram.run_regular {m : ℕ} (P : CorrectionProgram E m) {r : WithTop ℕ∞}
    (B : X → E →L[ℝ] E) (g : X → E) (data : X → Fin m → E) (x : X)
    (hB : ContDiffAt ℝ r B x) (hg : ContDiffAt ℝ r g x) (hd : ContDiffAt ℝ r data x)
    (hP : P.RegularAt r (B x) (g x) (data x)) :
    ContDiffAt ℝ r (fun p => (runCorrections (P.tree (data p)) (B p) (g p)).movement) x ∧
    ContDiffAt ℝ r (fun p => (runCorrections (P.tree (data p)) (B p) (g p)).gradient) x ∧
    SmoothListAt r (fun p => correctionObservations (runCorrections (P.tree (data p)) (B p) (g p)).trace) x := by
  -- Propagate the genuine returned gradient and every true queried displacement through the finite continuation.
  induction P generalizing g with
  | done => exact ⟨contDiffAt_const,hg,SmoothListAt.nil r x⟩
  | @query k f next ih =>
    have hu := f.evaluate_contDiffAt data x hP.1 hd
    have hnew := hg.add (hB.clm_apply hu)
    have hdata : ContDiffAt ℝ r (fun p => (Fin.cons (g p+B p (f.evaluate (data p)))
        (Fin.cons (f.evaluate (data p)) (data p)) : Fin (k+2) → E)) x :=
      contDiffAt_pi.mpr (Fin.cases hnew (Fin.cases hu (fun i => (contDiffAt_pi.mp hd) i)))
    obtain ⟨hm,hr,ht⟩ := ih (fun p => g p+B p (f.evaluate (data p))) _ hnew hdata hP.2
    exact ⟨hu.add hm,hr,SmoothListAt.cons hu (SmoothListAt.cons hnew ht)⟩

/-- Every actual primitive correction coefficient rule has degree zero in its genuine observed data.
Use: Every actual primitive correction coefficient rule has degree zero in its genuine observed data.
Article: main_krylov, def:classes and lem:U(d), finite smooth correction compilation.
Proof: The recursive condition is imposed before the program is executed. -/
def CorrectionProgram.Homogeneous {m : ℕ} : CorrectionProgram E m → Prop
  | .done => True
  | .query f next => f.Homogeneous ∧ next.Homogeneous

/-- The actual compiled correction movement, returned gradient and full query trace scale with the genuine input data.
Use: The actual compiled correction movement, returned gradient and full query trace scale with the genuine input data.
Article: main_krylov, def:classes and lem:U(d), finite smooth correction compilation.
Proof: Actual primitive coefficients stay unchanged; linear operator observations scale and the true finite continuation induction preserves every recorded query. -/
theorem CorrectionProgram.run_scalar {m : ℕ} (P : CorrectionProgram E m) (hP : P.Homogeneous)
    (B : E →L[ℝ] E) (g : E) (data : Fin m → E) (c : ℝ) (hc : 0<c) :
    (runCorrections (P.tree (fun i => c • data i)) B (c • g)).movement=
        c • (runCorrections (P.tree data) B g).movement ∧
    (runCorrections (P.tree (fun i => c • data i)) B (c • g)).gradient=
        c • (runCorrections (P.tree data) B g).gradient ∧
    (runCorrections (P.tree (fun i => c • data i)) B (c • g)).trace=
        (runCorrections (P.tree data) B g).trace.map (fun p => (c • p.1,c • p.2)) := by
  -- Scaling is proved for the real execution and complete trace, rather than a hypothetical output map.
  induction P generalizing g with
  | done => exact ⟨(smul_zero c).symm,rfl,rfl⟩
  | @query k f next ih =>
    simp only [CorrectionProgram.tree,runCorrections,f.evaluate_homogeneous hP.1 data c hc,map_smul,← smul_add]
    have hdata : Fin.cons (c • (g+B (f.evaluate data))) (Fin.cons (c • f.evaluate data) (fun i => c • data i))=
        fun i => c • ((Fin.cons (g+B (f.evaluate data)) (Fin.cons (f.evaluate data) data) : Fin (k+2) → E) i) := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (fun _ => rfl)) i
    rw [hdata]
    obtain ⟨hm,hg,ht⟩ := ih hP.2 (g+B (f.evaluate data)) _
    exact ⟨by rw [hm,smul_add],hg,by rw [ht,List.map_cons]⟩
end
end krylov.Methods
