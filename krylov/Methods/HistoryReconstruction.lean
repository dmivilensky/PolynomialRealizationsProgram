import krylov.Methods.CorrectionTraceGeometry

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Use: construct primitive observed-coefficient charts of the named real
implementations using exactly their actual finite observations and true
fixed iteration/correction-query boundaries.
Source: actual complete-history observation layout, real finite query
counts and exact list-coordinate reconstruction, including empty histories.
-/

namespace krylov.Methods
variable {E : Type*} [Zero E]

/-- Reconstruct a genuine fixed-count correction trace from its actual displacement/gradient observation coordinates.
Use: Reconstruct a genuine fixed-count correction trace from its actual displacement/gradient observation coordinates.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Read the true two coordinates of each real query and advance by exactly two actual observations. -/
def readCorrectionTrace : ℕ → List E → List (E × E)
  | 0,_ => []
  | q+1,v => (v.getD 0 0,v.getD 1 0)::readCorrectionTrace q (v.drop 2)

/-- The genuine finite observed-vector list contributed by one actual iteration record.
Use: The genuine finite observed-vector list contributed by one actual iteration record.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Retain its real direction, probe, total step, gradient and all actual correction pairs. -/
def recordObservationList (r : IterationRecord E) : List E :=
  [r.direction,r.probe,r.step,r.gradient]++correctionObservations r.corrections

/-- Read a fixed-shape genuine iteration record from its finite actual observation coordinates.
Use: Read a fixed-shape genuine iteration record from its finite actual observation coordinates.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Read exactly the four real iteration fields and its prescribed true finite correction trace. -/
def readIterationRecord (q : ℕ) (v : List E) : IterationRecord E :=
  ⟨v.getD 0 0,v.getD 1 0,v.getD 2 0,v.getD 3 0,readCorrectionTrace q (v.drop 4)⟩

/-- Reconstruct genuine iteration records from their true discrete query shape and finite observed-vector list.
Use: Reconstruct genuine iteration records from their true discrete query shape and finite observed-vector list.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Each real record advances by its actual four fields plus two observations per true correction query. -/
def readHistoryRecords : List ℕ → List E → List (IterationRecord E)
  | [],_ => []
  | q::qs,v => readIterationRecord q v::readHistoryRecords qs (v.drop (4+2*q))

/-- Reconstruct the true complete observed history from its genuine query shape and actual finite observations.
Use: Reconstruct the true complete observed history from its genuine query shape and actual finite observations.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Retain the actual initial-gradient coordinate and reconstruct all real iteration records after the current/initial prefix. -/
def historyFromObservations (shape : List ℕ) (v : List E) : History E :=
  ⟨v.getD 1 0,readHistoryRecords shape (v.drop 2)⟩

/-- Reading the true finite query count recovers every actual correction pair independently of later real observations.
Use: Reading the true finite query count recovers every actual correction pair independently of later real observations.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Induct on the genuine trace, reading each true displacement/gradient pair before advancing its actual finite tail. -/
theorem readCorrectionTrace_append (trace : List (E × E)) (tail : List E) :
    readCorrectionTrace trace.length (correctionObservations trace++tail)=trace := by
  induction trace with
  | nil => rfl
  | cons p trace ih =>
    simpa only [List.length_cons,correctionObservations,List.flatMap_cons,List.cons_append,List.nil_append,
      readCorrectionTrace,List.getD_cons_zero,List.getD_cons_succ,List.drop_succ_cons,List.drop_zero] using congrArg (List.cons p) ih

omit [Zero E] in
/-- The genuine iteration-record observation count is four plus twice its actual correction-query count.
Use: The genuine iteration-record observation count is four plus twice its actual correction-query count.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Use the true finite correction-observation length identity. -/
theorem recordObservationList_length (r : IterationRecord E) :
    (recordObservationList r).length=4+2*r.corrections.length := by
  simp only [recordObservationList,List.length_append,List.length_cons,List.length_nil,correctionObservations_length]

/-- Every actual iteration record is reconstructed exactly from its true finite observations independently of later real data.
Use: Every actual iteration record is reconstructed exactly from its true finite observations independently of later real data.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Read the genuine four actual fields and use true finite correction-trace reconstruction. -/
theorem readIterationRecord_append (r : IterationRecord E) (tail : List E) :
    readIterationRecord r.corrections.length (recordObservationList r++tail)=r := by
  cases r
  simp only [readIterationRecord,recordObservationList,List.cons_append,List.nil_append,
    List.getD_cons_zero,List.getD_cons_succ,List.drop_succ_cons,List.drop_zero,readCorrectionTrace_append]

/-- The actual record list is reconstructed exactly from its genuine query counts and complete observed-vector flattening.
Use: The actual record list is reconstructed exactly from its genuine query counts and complete observed-vector flattening.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Induct through true records; their actual observation lengths identify each genuine next tail exactly. -/
theorem readHistoryRecords_flatMap (records : List (IterationRecord E)) :
    readHistoryRecords (records.map fun r => r.corrections.length)
      (records.flatMap recordObservationList)=records := by
  induction records with
  | nil => rfl
  | cons r rs ih =>
    rw [List.map_cons,List.flatMap_cons,readHistoryRecords,readIterationRecord_append r (rs.flatMap recordObservationList)]
    have hlen : 4+2*r.corrections.length=(recordObservationList r).length := (recordObservationList_length r).symm
    rw [hlen,List.drop_left,ih]

/-- Every genuine complete observed history is reconstructed exactly from its true query shape and actual observation list.
Use: Every genuine complete observed history is reconstructed exactly from its true query shape and actual observation list.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: The actual current/initial prefix yields the true initial field and the proved real record reconstruction recovers the complete genuine transcript. -/
theorem historyFromObservations_actual (H : History E) :
    historyFromObservations H.queryShape H.observationList=H := by
  rcases H with ⟨g,records⟩
  simp only [historyFromObservations,History.queryShape,History.observationList,
    List.getD_cons_succ,List.getD_cons_zero,List.drop_succ_cons,List.drop_zero]
  rw [show records.flatMap (fun r => [r.direction,r.probe,r.step,r.gradient]++r.corrections.flatMap (fun p => [p.1,p.2]))=
    records.flatMap recordObservationList from rfl,readHistoryRecords_flatMap]

/-- A genuine fixed-count observation reader produces exactly its prescribed true query count.
Use: A genuine fixed-count observation reader produces exactly its prescribed true query count.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Each actual recursive read contributes one genuine pair. -/
theorem readCorrectionTrace_length (q : ℕ) (v : List E) : (readCorrectionTrace q v).length=q := by
  induction q generalizing v with
  | zero => rfl
  | succ q ih => exact congrArg Nat.succ (ih (v.drop 2))

/-- Reconstructed genuine records retain exactly the supplied true discrete correction-query shape.
Use: Reconstructed genuine records retain exactly the supplied true discrete correction-query shape.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Actual record reconstruction preserves each true finite query count. -/
theorem readHistoryRecords_shape (shape : List ℕ) (v : List E) :
    (readHistoryRecords shape v).map (fun r => r.corrections.length)=shape := by
  induction shape generalizing v with
  | nil => rfl
  | cons q qs ih =>
    simp only [readHistoryRecords,List.map_cons,readIterationRecord,readCorrectionTrace_length,ih]

/-- Genuine observed-history reconstruction preserves the supplied true query shape.
Use: Genuine observed-history reconstruction preserves the supplied true query shape.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Apply the actual fixed-count record-shape identity. -/
theorem historyFromObservations_shape (shape : List ℕ) (v : List E) :
    (historyFromObservations shape v).queryShape=shape := readHistoryRecords_shape shape (v.drop 2)

/-- Actual histories with the stated true query shape and real observation list equal their genuine finite reconstruction.
Use: Actual histories with the stated true query shape and real observation list equal their genuine finite reconstruction.
Article: main_krylov, def:classes and cor:lm, genuine structured observed-history reconstruction.
Proof: Substitute the actual observed data in the proved true complete-history reconstruction identity. -/
theorem historyFromObservations_of_shape (H : History E) (shape : List ℕ) (v : List E)
    (hshape : H.queryShape=shape) (hv : H.observationList=v) : H=historyFromObservations shape v := by
  rw [← hshape,← hv,historyFromObservations_actual]
end krylov.Methods
