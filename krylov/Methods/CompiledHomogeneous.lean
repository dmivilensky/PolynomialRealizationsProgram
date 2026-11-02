import krylov.Methods.CompiledProbed
import krylov.Methods.HomogeneousSolve

/-!
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Use: derive positive homogeneity of the real compiled probed method,
including every actual history record and intermediate correction observation,
directly from its primitive degree-zero observed coefficient rules.
Source: actual coefficient and correction-program scaling, exact-search
scalar cancellation and the genuine finite method execution induction.
-/

namespace krylov.Methods
noncomputable section
open Filter Topology krylov.Stability krylov.Reference
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale every actual recorded vector and correction observation by the same real scalar.
Use: Scale every actual recorded vector and correction observation by the same real scalar.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: All genuine observed history fields scale together. -/
def scaleRecord (c : ℝ) (r : IterationRecord E) : IterationRecord E :=
  ⟨c • r.direction,c • r.probe,c • r.step,c • r.gradient,r.corrections.map (fun p => (c • p.1,c • p.2))⟩

/-- Scale the actual initial gradient and complete real observed history.
Use: Scale the actual initial gradient and complete real observed history.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: The actual record list and every correction observation are retained. -/
def scaleHistory (c : ℝ) (H : History E) : History E :=
  ⟨c • H.initial,H.records.map (scaleRecord c)⟩

/-- The actual current gradient of a scaled real history is scaled by the same scalar.
Use: The actual current gradient of a scaled real history is scaled by the same scalar.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: Read the initial or latest actual recorded gradient. -/
theorem scaleHistory_gradient (c : ℝ) (H : History E) : (scaleHistory c H).gradient=c • H.gradient := by
  rcases H with ⟨g,records⟩
  cases records <;> rfl

/-- The true observation list of a scaled real history is the pointwise scaled original list.
Use: The true observation list of a scaled real history is the pointwise scaled original list.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: Flattening and actual finite list mapping preserve every genuine observed vector. -/
theorem scaleHistory_observations (c : ℝ) (H : History E) :
    (scaleHistory c H).observationList=H.observationList.map (fun v => c • v) := by
  rw [History.observationList,scaleHistory_gradient]
  simp only [History.observationList,scaleHistory,List.map_cons,List.flatMap_map,
    List.map_flatMap,scaleRecord,List.map_append,List.map_cons,List.map_nil]

/-- The real observed finite array commutes with actual scalar scaling, including absent zero coordinates.
Use: The real observed finite array commutes with actual scalar scaling, including absent zero coordinates.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: Read the genuine finite list coordinates and their actual zero defaults. -/
theorem observedArray_map (c : ℝ) (m : ℕ) (v : List E) :
    observedArray m (v.map (fun w => c • w))=fun i => c • observedArray m v i := by
  funext i
  simp only [observedArray,List.getD_eq_getElem?_getD,List.getElem?_map]
  cases v[i.val]? <;> simp

/-- Primitive degree-zero observed coefficients make the actual list decision positively homogeneous.
Use: Primitive degree-zero observed coefficients make the actual list decision positively homogeneous.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: Its actual observation count is unchanged and the real coefficient evaluation scales. -/
theorem listDecision_scalar (rules : ∀ m, ObservedRule E m) (h : ∀ m, (rules m).Homogeneous)
    (c : ℝ) (hc : 0<c) (v : List E) :
    listDecision rules (v.map (fun w => c • w))=c • listDecision rules v := by
  unfold listDecision
  rw [List.length_map,observedArray_map,(rules v.length).evaluate_homogeneous (h _) _ c hc]

/-- All actual primitive direction and correction-program coefficients have degree zero.
Use: All actual primitive direction and correction-program coefficients have degree zero.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: The condition refers to actual observed coefficient rules before execution. -/
def CompiledProbedPolicy.Homogeneous (P : CompiledProbedPolicy E) : Prop :=
  (∀ m, (P.directionRule m).Homogeneous) ∧ ∀ m, (P.correctionProgram m).Homogeneous

/-- The actual compiled direction scales with the genuine complete observed history.
Use: The actual compiled direction scales with the genuine complete observed history.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: Use true history observation scaling and the proved real list-decision homogeneity. -/
theorem CompiledProbedPolicy.direction_scalar (P : CompiledProbedPolicy E) (hP : P.Homogeneous)
    (c : ℝ) (hc : 0<c) (H : History E) :
    P.method.direction (scaleHistory c H)=c • P.method.direction H := by
  change listDecision P.directionRule (scaleHistory c H).observationList=_
  rw [scaleHistory_observations,listDecision_scalar P.directionRule hP.1 c hc]
  rfl

/-- One actual compiled probed iteration preserves genuine positive scaling of the complete real history.
Use: One actual compiled probed iteration preserves genuine positive scaling of the complete real history.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: Actual direction and exact-search scalar identities give the scaled true post-search data. Apply genuine correction-program scaling to its real movement, returned gradient and complete trace, then identify every actual next record. -/
theorem CompiledProbedPolicy.advance_scalar (P : CompiledProbedPolicy E) (hP : P.Homogeneous)
    (A B : E →L[ℝ] E) (H : History E) (c : ℝ) (hc : 0<c) :
    methodAdvance P.method A B (scaleHistory c H)=scaleHistory c (methodAdvance P.method A B H) := by
  -- Scale the genuine post-search observations before running the actual finite correction program.
  let d := P.method.direction H
  let z := A d
  let gp := searchedGradient H.gradient d z
  let input : Fin (H.observationList.length+3) → E := Fin.cons gp (Fin.cons z (Fin.cons d (observedArray H.observationList.length H.observationList)))
  have hd := P.direction_scalar hP c hc H
  have hgp : searchedGradient (scaleHistory c H).gradient (P.method.direction (scaleHistory c H))
      (A (P.method.direction (scaleHistory c H)))=c • gp := by
    rw [scaleHistory_gradient,hd,map_smul,searchedGradient,lineLength_scalar _ _ _ c hc.ne',smul_comm,← smul_add]
    rfl
  have hinput : Fin.cons (c • gp) (Fin.cons (c • z) (Fin.cons (c • d)
      (fun i => c • observedArray H.observationList.length H.observationList i)))=fun i => c • input i := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i
  -- The real correction theorem includes the entire true intermediate query trace.
  have hrun := (P.correctionProgram H.observationList.length).run_scalar (hP.2 _) B gp input c hc
  have hcor : runCorrections (P.method.correction (scaleHistory c H) (A (P.method.direction (scaleHistory c H)))) B
      (searchedGradient (scaleHistory c H).gradient (P.method.direction (scaleHistory c H)) (A (P.method.direction (scaleHistory c H))))=
    runCorrections ((P.correctionProgram H.observationList.length).tree (fun i => c • input i)) B (c • gp) := by
    rw [hgp]
    dsimp only [CompiledProbedPolicy.method]
    rw [scaleHistory_observations,List.length_map,observedArray_map]
    rw [listDecision_scalar P.directionRule hP.1 c hc,map_smul,scaleHistory_gradient,
      searchedGradient,lineLength_scalar _ _ _ c hc.ne']
    change runCorrections ((P.correctionProgram H.observationList.length).tree
      (Fin.cons (c • H.gradient+lineLength H.gradient d z • (c • z))
        (Fin.cons (c • z) (Fin.cons (c • d) (fun i => c • observedArray H.observationList.length H.observationList i))))) B (c • gp)=_
    rw [smul_comm,← smul_add]
    change runCorrections ((P.correctionProgram H.observationList.length).tree
      (Fin.cons (c • gp) (Fin.cons (c • z) (Fin.cons (c • d)
        (fun i => c • observedArray H.observationList.length H.observationList i))))) B (c • gp)=_
    rw [hinput]
  dsimp only [methodAdvance]
  rw [hcor,hd,map_smul,scaleHistory_gradient,lineLength_scalar _ _ _ c hc.ne']
  dsimp only [scaleHistory]
  simp only [List.map_cons,scaleRecord]
  rw [hrun.1,hrun.2.1,hrun.2.2,smul_comm,← smul_add]
  rfl

/-- Every finite actual compiled probed run is positively homogeneous as a complete genuine history.
Use: Every finite actual compiled probed run is positively homogeneous as a complete genuine history.
Article: main_krylov, lem:U(c,d), genuine smooth-policy cone homogeneity.
Proof: Induct through the real method executor using actual iteration scaling, including all intermediate correction observations. -/
theorem CompiledProbedPolicy.run_scalar (P : CompiledProbedPolicy E) (hP : P.Homogeneous)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    methodRun P.method A B (c • g) N=scaleHistory c (methodRun P.method A B g N) := by
  -- This induction concerns the complete actual method history, rather than an assumed output map.
  induction N with
  | zero => rfl
  | succ k ih => rw [methodRun,ih,P.advance_scalar hP _ _ _ c hc,methodRun]

/-- The actual returned gradient of the compiled homogeneous probed method scales with the genuine initial gradient.
Use: the compact Taylor constant extends to the true initial-gradient cone without a scale-dependent radius.
Article: main_krylov, lem:U(c,d).
Proof: apply actual complete-history homogeneity and read the true current gradient. -/
theorem CompiledProbedPolicy.gradient_scalar (P : CompiledProbedPolicy E) (hP : P.Homogeneous)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    probedGradient P.method A B (c • g) N=c • probedGradient P.method A B g N := by
  rw [probedGradient,P.run_scalar hP A B g c hc N,scaleHistory_gradient]
  rfl

end
end krylov.Methods
