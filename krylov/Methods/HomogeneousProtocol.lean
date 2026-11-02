import krylov.Methods.CompiledHomogeneous
import krylov.Methods.SmoothClasses

/-!
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Use: formulate homogeneity on the true primitive direction and correction-tree
decisions, then derive actual full-history and returned-gradient cone scaling
for arbitrary raw policies, including locally compiled smooth branches.
Source: actual tree execution under rescaled observations, real exact-search
scalar cancellation and genuine complete-history execution induction.
-/

namespace krylov.Methods
noncomputable section
open krylov.Reference
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale actual correction displacements and rescale each true returned-gradient argument before its genuine continuation decision.
Use: Scale actual correction displacements and rescale each true returned-gradient argument before its genuine continuation decision.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: The actual finite tree shape and observations transform consistently. -/
def CorrectionTree.scaled (c : ℝ) : CorrectionTree E → CorrectionTree E
  | .done => .done
  | .query u next => .query (c • u) (fun g => (next (c⁻¹ • g)).scaled c)

/-- The genuinely scaled raw correction tree has the actual scaled movement, returned gradient and complete real trace.
Use: The genuinely scaled raw correction tree has the actual scaled movement, returned gradient and complete real trace.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: Induct on the true tree; actual linear oracle observations scale and their genuine inverse scalar cancels before each real continuation. -/
theorem runCorrections_scaled (q : CorrectionTree E) (B : E →L[ℝ] E) (g : E) (c : ℝ) (hc : c≠0) :
    (runCorrections (q.scaled c) B (c • g)).movement=c • (runCorrections q B g).movement ∧
    (runCorrections (q.scaled c) B (c • g)).gradient=c • (runCorrections q B g).gradient ∧
    (runCorrections (q.scaled c) B (c • g)).trace=
      (runCorrections q B g).trace.map (fun p => (c • p.1,c • p.2)) := by
  -- The real inverse observation scale cancels before the actual next subtree is selected.
  induction q generalizing g with
  | done => exact ⟨(smul_zero c).symm,rfl,rfl⟩
  | query u next ih =>
    simp only [CorrectionTree.scaled,runCorrections,map_smul,← smul_add,smul_smul,inv_mul_cancel₀ hc,one_smul]
    obtain ⟨hm,hg,ht⟩ := ih (g+B u) (g+B u)
    exact ⟨by rw [hm,smul_add],hg,by rw [ht,List.map_cons]⟩

/-- Primitive actual direction and correction-tree decisions commute with positive scaling of their true observed data.
Use: Primitive actual direction and correction-tree decisions commute with positive scaling of their true observed data.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: This condition is on the real decision rules and contains no trajectory or cycle homogeneity premise. -/
def ProbedMethod.Homogeneous (m : ProbedMethod E) : Prop :=
  ∀ (c : ℝ), 0<c → ∀ H : History E,
    m.direction (scaleHistory c H)=c • m.direction H ∧
    ∀ z : E, m.correction (scaleHistory c H) (c • z)=(m.correction H z).scaled c

/-- Every actual raw probed iteration with homogeneous primitive decisions scales its genuine complete history.
Use: Every actual raw probed iteration with homogeneous primitive decisions scales its genuine complete history.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: True direction and line scalar cancellation give the actual scaled post-search data; the real scaled correction tree supplies every true next-record field. -/
theorem methodAdvance_scalar (m : ProbedMethod E) (hm : m.Homogeneous)
    (A B : E →L[ℝ] E) (H : History E) (c : ℝ) (hc : 0<c) :
    methodAdvance m A B (scaleHistory c H)=scaleHistory c (methodAdvance m A B H) := by
  -- Track the actual search and real correction trace before assembling the next genuine history.
  let d := m.direction H
  let z := A d
  let gp := searchedGradient H.gradient d z
  have hd := (hm c hc H).1
  have hgp : searchedGradient (scaleHistory c H).gradient (m.direction (scaleHistory c H))
      (A (m.direction (scaleHistory c H)))=c • gp := by
    rw [scaleHistory_gradient,hd,map_smul,searchedGradient,lineLength_scalar _ _ _ c hc.ne',smul_comm,← smul_add]
    rfl
  have hcor : runCorrections (m.correction (scaleHistory c H) (A (m.direction (scaleHistory c H)))) B
      (searchedGradient (scaleHistory c H).gradient (m.direction (scaleHistory c H)) (A (m.direction (scaleHistory c H))))=
    runCorrections ((m.correction H z).scaled c) B (c • gp) := by
    rw [hgp,hd,map_smul,(hm c hc H).2]
  have hrun := runCorrections_scaled (m.correction H z) B gp c hc.ne'
  dsimp only [methodAdvance]
  rw [hcor,hd,map_smul,scaleHistory_gradient,lineLength_scalar _ _ _ c hc.ne']
  dsimp only [scaleHistory]
  simp only [List.map_cons,scaleRecord]
  rw [hrun.1,hrun.2.1,hrun.2.2,smul_comm,← smul_add]

/-- Every finite actual raw probed method run with homogeneous primitive decisions scales its complete genuine history.
Use: Every finite actual raw probed method run with homogeneous primitive decisions scales its complete genuine history.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: Induct through real iterations using the proved actual decision-tree and search scaling. -/
theorem methodRun_scalar (m : ProbedMethod E) (hm : m.Homogeneous)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    methodRun m A B (c • g) N=scaleHistory c (methodRun m A B g N) := by
  -- Scale the genuine complete method history rather than assuming vector-output homogeneity.
  induction N with
  | zero => rfl
  | succ k ih => rw [methodRun,ih,methodAdvance_scalar m hm _ _ _ c hc,methodRun]

/-- The actual raw probed returned gradient is positively homogeneous under primitive homogeneous decisions.
Use: The actual raw probed returned gradient is positively homogeneous under primitive homogeneous decisions.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: Read its true current-gradient coordinate from the genuine scaled complete history. -/
theorem probedGradient_scalar (m : ProbedMethod E) (hm : m.Homogeneous)
    (A B : ℕ → E →L[ℝ] E) (g : E) (c : ℝ) (hc : 0<c) (N : ℕ) :
    probedGradient m A B (c • g) N=c • probedGradient m A B g N := by
  rw [probedGradient,methodRun_scalar m hm A B g c hc N,scaleHistory_gradient]
  rfl


/-- Primitive degree-zero finite correction coefficients compile into a genuinely homogeneous raw correction tree.
Use: Primitive degree-zero finite correction coefficients compile into a genuinely homogeneous raw correction tree.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: Coefficient evaluation scales each actual query; rescale the true continuation observation and use real nonzero scalar cancellation in the exact finite data list. -/
theorem CorrectionProgram.tree_scalar {m : ℕ} (P : CorrectionProgram E m) (hP : P.Homogeneous)
    (data : Fin m → E) (c : ℝ) (hc : c≠0) (hp : 0<c) :
    P.tree (fun i => c • data i)=(P.tree data).scaled c := by
  -- The actual finite continuation sees the correctly rescaled true observation.
  induction P with
  | done => rfl
  | @query k f next ih =>
    simp only [CorrectionProgram.tree,CorrectionTree.scaled,f.evaluate_homogeneous hP.1 data c hp]
    congr 1
    funext v
    have h := ih hP.2 (Fin.cons (c⁻¹ • v) (Fin.cons (f.evaluate data) data))
    rw [← h]
    congr 1
    funext i
    refine Fin.cases ?_ (Fin.cases ?_ (fun _ => rfl)) i
    · simp only [Fin.cons_zero,smul_smul,mul_inv_cancel₀ hc,one_smul]
    · rfl

/-- Every actual compiled policy with primitive degree-zero coefficients satisfies the genuine raw primitive homogeneity condition.
Use: Every actual compiled policy with primitive degree-zero coefficients satisfies the genuine raw primitive homogeneity condition.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: The real observed list and exact-search post-data scale; apply the actual finite coefficient program tree-scaling theorem. -/
theorem CompiledProbedPolicy.method_homogeneous (P : CompiledProbedPolicy E) (hP : P.Homogeneous) :
    P.method.Homogeneous := by
  -- Primitive degree-zero observed coefficients give genuine raw decision homogeneity.
  intro c hc H
  refine ⟨P.direction_scalar hP c hc H,?_⟩
  intro z
  let d := P.method.direction H
  let gp := searchedGradient H.gradient d z
  let input : Fin (H.observationList.length+3) → E :=
    Fin.cons gp (Fin.cons z (Fin.cons d (observedArray H.observationList.length H.observationList)))
  have he : Fin.cons (c • gp) (Fin.cons (c • z) (Fin.cons (c • d)
      (fun i => c • observedArray H.observationList.length H.observationList i)))=fun i => c • input i := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun _ => rfl))) i
  dsimp only [CompiledProbedPolicy.method]
  rw [scaleHistory_observations,List.length_map,observedArray_map,listDecision_scalar P.directionRule hP.1 c hc,
    scaleHistory_gradient,searchedGradient,lineLength_scalar _ _ _ c hc.ne',smul_comm,← smul_add]
  change (P.correctionProgram H.observationList.length).tree
      (Fin.cons (c • gp) (Fin.cons (c • z) (Fin.cons (c • d)
        (fun i => c • observedArray H.observationList.length H.observationList i))))=
    ((P.correctionProgram H.observationList.length).tree input).scaled c
  rw [he]
  exact (P.correctionProgram H.observationList.length).tree_scalar (hP.2 _) input c hc.ne' hc

/-- The actual smooth raw probed information class with homogeneous genuine primitive decisions.
Use: The actual smooth raw probed information class with homogeneous genuine primitive decisions.
Article: main_krylov, lem:U(c,d), actual homogeneous raw probed information classes.
Proof: It extends the genuine local coefficient-chart smooth information class and imposes scaling on real direction and correction decisions before execution. -/
structure HomogeneousSmoothProbedClass (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    extends SmoothProbedClass E where
  /-- Positive scaling commutes with the actual raw direction and correction-tree decisions. -/
  homogeneous : policy.Homogeneous
end
end krylov.Methods
