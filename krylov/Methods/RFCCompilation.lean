import krylov.Methods.RFCObservedProgram
import krylov.Methods.HistoryShapeSelection
import krylov.Methods.ObservedGateCharts

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, true local RFC primitive compilation.
Use: represent the actual gated repeated RFC policy by genuine primitive
observed coefficients on its true reference-data branch, preserving every
actual history boundary and all possible real correction continuations.
Source: real dimension-selected reference shapes, actual complete-history
reconstruction, true repeated model programs and strict observed gate neighborhoods.
-/

namespace krylov.Methods
noncomputable section
open krylov.Stability krylov.Reference Filter Topology
open scoped Matrix.Norms.L2Operator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The genuine primitive local observed-coefficient compiler for actual repeated RFC at a prescribed real reference history family.
Use: The genuine primitive local observed-coefficient compiler for actual repeated RFC at a prescribed real reference history family.
Article: main_krylov, def:classes and cor:lm, true local RFC primitive compilation.
Proof: The true observed dimension selects the actual query shape; the actual empty initial phase and genuine finite repeated correction programs are kept explicitly. -/
def rfcCompiledPolicy (memory : ℕ → ℕ) (count : ℕ) (reference : ℕ → History E) : CompiledProbedPolicy E where
  directionRule n := fcObservedRule memory (selectedHistoryShape reference n) n
  correctionProgram n := if selectedHistoryShape reference n=[] then .done else
    rfcObservedProgram memory (selectedHistoryShape reference n) n count

/-- The compiled real primitive direction equals the true RFC retained-window direction on every actual history with its genuine selected query shape.
Use: The compiled real primitive direction equals the true RFC retained-window direction on every actual history with its genuine selected query shape.
Article: main_krylov, def:classes and cor:lm, true local RFC primitive compilation.
Proof: Use the exact actual complete-history observation reconstruction in the genuine primitive FC coefficient rule. -/
theorem rfcCompiled_direction (memory : ℕ → ℕ) (count : ℕ) (reference : ℕ → History E) (H : History E)
    (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape) :
    (rfcCompiledPolicy memory count reference).method.direction H=(rfcMethod memory count).direction H := by
  change (fcObservedRule memory (selectedHistoryShape reference H.observationList.length) H.observationList.length).evaluate
    (observedArray H.observationList.length H.observationList)=_
  rw [hshape]
  exact fcObservedRule_of_array memory H _ (ofFn_observedArray H.observationList).symm

/-- The genuine compiled and actual RFC correction decisions agree on every true empty reference-history shape.
Use: The genuine compiled and actual RFC correction decisions agree on every true empty reference-history shape.
Article: main_krylov, def:classes and cor:lm, true local RFC primitive compilation.
Proof: The real window is empty, so the actual gate and genuine primitive program both stop immediately. -/
theorem rfcCompiled_correction_empty (memory : ℕ → ℕ) (count : ℕ) (reference : ℕ → History E)
    (H : History E) (z : E) (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hempty : H.queryShape=[]) :
    (rfcCompiledPolicy memory count reference).method.correction H z=(rfcMethod memory count).correction H z := by
  -- Genuine empty query shape forces the actual record list, and hence its true retained window, to be empty.
  have hrecords : H.records=[] := by
    have hl := congrArg List.length hempty
    simp only [History.queryShape,List.length_map,List.length_nil] at hl
    exact List.length_eq_zero_iff.mp hl
  have hW : selectedWindow memory H=[] := by
    rcases H with ⟨initial,records⟩
    simp only at hrecords
    subst records
    simp only [selectedWindow,History.pairs,recordPairs,List.take_nil]
  change (if selectedHistoryShape reference H.observationList.length=[] then CorrectionProgram.done else _).tree _=rfcCorrection memory count H z
  rw [hshape,hempty,ite_eq_left rfl]
  simp only [CorrectionProgram.tree,rfcCorrection,hW,ne_eq,not_true_eq_false,false_and,ite_false]

/-- The genuine compiled and actual repeated RFC trees agree exactly on every true accepted fixed-shape observed history.
Use: The genuine compiled and actual repeated RFC trees agree exactly on every true accepted fixed-shape observed history.
Article: main_krylov, def:classes and cor:lm, true local RFC primitive compilation.
Proof: Identify the real direction and actual retained observations; the genuine compiled repeated-query tree is exactly the actual accepted RFC tree for every true continuation answer. -/
theorem rfcCompiled_correction_gate (memory : ℕ → ℕ) (count : ℕ) (reference : ℕ → History E)
    (H : History E) (z : E) (hshape : selectedHistoryShape reference H.observationList.length=H.queryShape)
    (hne : H.queryShape≠[]) (hgate : selectedWindow memory H≠[] ∧ ‖windowDefect (selectedWindow memory H)‖<1) :
    (rfcCompiledPolicy memory count reference).method.correction H z=(rfcMethod memory count).correction H z := by
  -- Identify the real direction before matching the actual repeated physical correction decision tree.
  let d := (rfcMethod memory count).direction H
  have hd := rfcCompiled_direction memory count reference H hshape
  change ((rfcCompiledPolicy memory count reference).correctionProgram H.observationList.length).tree
    (Fin.cons (searchedGradient H.gradient ((rfcCompiledPolicy memory count reference).method.direction H) z)
      (Fin.cons z (Fin.cons ((rfcCompiledPolicy memory count reference).method.direction H)
        (observedArray H.observationList.length H.observationList))))=rfcCorrection memory count H z
  rw [hd]
  change (if selectedHistoryShape reference H.observationList.length=[] then CorrectionProgram.done else _).tree _=_
  rw [hshape,ite_eq_right hne,rfcObservedProgram_tree,chartWindow_of_array memory H _ (ofFn_observedArray H.observationList).symm]
  simp only [rfcCorrection,ite_eq_left hgate]
  rfl

/-- The actual gated RFC policy and its genuine primitive compiler agree on a true observed-data neighborhood at every positive-model reference with strict accepted nonempty gate.
Use: The actual gated RFC policy and its genuine primitive compiler agree on a true observed-data neighborhood at every positive-model reference with strict accepted nonempty gate.
Article: main_krylov, def:classes and cor:lm, true local RFC primitive compilation.
Proof: Preserve the real query boundaries and reconstruct every true local history. The actual empty initial phase agrees everywhere on its genuine shape; positive real retained energies keep the actual nonempty gate strictly accepted. Both true direction and entire finite correction decisions therefore agree locally. -/
theorem rfcCompiled_local (memory : ℕ → ℕ) (count : ℕ) (reference : ℕ → History E)
    (H₀ : History E) (z₀ : E) (hshape : selectedHistoryShape reference H₀.observationList.length=H₀.queryShape)
    (hC : (crossGram (windowImages (selectedWindow memory H₀)) (windowSteps (selectedWindow memory H₀))).PosDef)
    (hgate : H₀.queryShape≠[] → selectedWindow memory H₀≠[] ∧ ‖windowDefect (selectedWindow memory H₀)‖<1) :
    LocalCompiledAt (rfcMethod memory count) (rfcCompiledPolicy memory count reference) H₀ z₀ := by
  -- Work on the true primitive observed-data neighborhood with actual correction-query boundaries preserved.
  apply ObservedLocalAt.of_chart
  intro n data hdata
  have hn : H₀.observationList.length=n := by rw [hdata,List.length_ofFn]
  have hselect : selectedHistoryShape reference n=H₀.queryShape := by rw [← hn,hshape]
  have heq (p : Fin n → E) : (historyFromObservations H₀.queryShape (List.ofFn p)).observationList.length=n := by
    rw [History.observationList_length_shape,historyFromObservations_shape,← History.observationList_length_shape H₀,hn]
  have hshape' (p : Fin n → E) : selectedHistoryShape reference
      (historyFromObservations H₀.queryShape (List.ofFn p)).observationList.length=
      (historyFromObservations H₀.queryShape (List.ofFn p)).queryShape := by
    rw [heq,hselect,historyFromObservations_shape]
  by_cases hempty : H₀.queryShape=[]
  · exact Eventually.of_forall fun q => ⟨(rfcCompiled_direction memory count reference _ (hshape' q.1)).symm,
      (rfcCompiled_correction_empty memory count reference _ q.2 (hshape' q.1) (by rw [historyFromObservations_shape,hempty])).symm⟩
  · have hg : chartWindow memory H₀.queryShape data≠[] ∧ ‖windowDefect (chartWindow memory H₀.queryShape data)‖<1 := by
      rw [chartWindow_of_array memory H₀ data hdata]
      exact hgate hempty
    have he := chartWindow_positive_energy memory H₀ data hdata hC
    have hnb := (continuousAt_fst : ContinuousAt (Prod.fst : (Fin n → E) × E → Fin n → E) (data,z₀)).tendsto.eventually
      (chartWindow_gate_eventually memory H₀.queryShape data he hg)
    filter_upwards [hnb] with q hq
    exact ⟨(rfcCompiled_direction memory count reference _ (hshape' q.1)).symm,
      (rfcCompiled_correction_gate memory count reference _ q.2 (hshape' q.1)
        (by rwa [historyFromObservations_shape]) hq).symm⟩
end
end krylov.Methods
