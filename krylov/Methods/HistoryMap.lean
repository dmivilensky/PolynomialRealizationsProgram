import krylov.Methods.HistoryReconstruction
import Mathlib.Data.List.GetD

set_option autoImplicit false
/-!
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Use: express the actual reconstructed data of named methods as true linear
images of fixed finite coefficient histories, preserving every real record
and correction boundary and every genuine stored secant difference.
Source: exact finite observed-history readers and standard linear-map
compatibility with actual zero defaults and true gradient subtraction.
-/

namespace krylov.Methods
variable {E F : Type*}

/-- Map every genuine observed vector of an actual iteration record while preserving all real correction-query pairs.
Use: Map every genuine observed vector of an actual iteration record while preserving all real correction-query pairs.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Apply the supplied true data map to the actual four record fields and each genuine query observation. -/
def IterationRecord.map (f : E → F) (r : IterationRecord E) : IterationRecord F :=
  ⟨f r.direction,f r.probe,f r.step,f r.gradient,r.corrections.map fun p => (f p.1,f p.2)⟩

/-- Map all genuine complete-history observations while preserving the true record structure.
Use: Map all genuine complete-history observations while preserving the true record structure.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Map the actual initial gradient and every real observed iteration record. -/
def History.map (f : E → F) (H : History E) : History F :=
  ⟨f H.initial,H.records.map (IterationRecord.map f)⟩

/-- Reading a genuine current gradient commutes with the true complete-history data map.
Use: Reading a genuine current gradient commutes with the true complete-history data map.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: The actual current gradient is either the true initial field or the genuine newest returned-gradient field. -/
theorem History.gradient_map (f : E → F) (H : History E) : (H.map f).gradient=f H.gradient := by
  rcases H with ⟨initial,records⟩
  cases records <;> rfl

section Zero
variable [Zero E] [Zero F] (f : E → F) (h0 : f 0=0)
include h0

/-- Zero-preserving actual data maps commute with every genuine finite observation coordinate including real absent defaults.
Use: Zero-preserving actual data maps commute with every genuine finite observation coordinate including real absent defaults.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Use the true finite-list coordinate map identity with its actual zero default. -/
theorem getD_map_zero (v : List E) (i : ℕ) : (v.map f).getD i 0=f (v.getD i 0) := by
  simpa only [h0] using List.getD_map v (0 : E) f (n := i)

/-- Genuine fixed-count correction-trace reconstruction commutes with each real zero-preserving observation map.
Use: Genuine fixed-count correction-trace reconstruction commutes with each real zero-preserving observation map.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Induct through the true finite query reads and their actual two-coordinate tails. -/
theorem readCorrectionTrace_map (q : ℕ) (v : List E) :
    readCorrectionTrace q (v.map f)=(readCorrectionTrace q v).map (fun p => (f p.1,f p.2)) := by
  induction q generalizing v with
  | zero => rfl
  | succ q ih =>
    simp only [readCorrectionTrace,List.map_cons,getD_map_zero f h0,← List.map_drop,ih]

/-- Genuine iteration-record reconstruction commutes with each real zero-preserving observation map.
Use: Genuine iteration-record reconstruction commutes with each real zero-preserving observation map.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Read the actual four fields and use true correction-trace map compatibility. -/
theorem readIterationRecord_map (q : ℕ) (v : List E) :
    readIterationRecord q (v.map f)=(readIterationRecord q v).map f := by
  simp only [readIterationRecord,IterationRecord.map,getD_map_zero f h0,← List.map_drop,readCorrectionTrace_map f h0]

/-- The true fixed-shape record reader commutes with actual zero-preserving observation maps.
Use: The true fixed-shape record reader commutes with actual zero-preserving observation maps.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Induct on the genuine finite query shape and advance the true observed tail by its actual record length. -/
theorem readHistoryRecords_map (shape : List ℕ) (v : List E) :
    readHistoryRecords shape (v.map f)=(readHistoryRecords shape v).map (IterationRecord.map f) := by
  induction shape generalizing v with
  | nil => rfl
  | cons q qs ih =>
    simp only [readHistoryRecords,List.map_cons,readIterationRecord_map f h0,← List.map_drop,ih]

/-- Genuine complete-history reconstruction commutes with every true zero-preserving observation map.
Use: Genuine complete-history reconstruction commutes with every true zero-preserving observation map.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Map the actual initial coordinate and all genuinely reconstructed record observations. -/
theorem historyFromObservations_map (shape : List ℕ) (v : List E) :
    historyFromObservations shape (v.map f)=(historyFromObservations shape v).map f := by
  simp only [historyFromObservations,History.map,getD_map_zero f h0,← List.map_drop,readHistoryRecords_map f h0]
end Zero

section Linear
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A true linear data map preserves the actual complete-history stored step and gradient-difference pairs.
Use: A true linear data map preserves the actual complete-history stored step and gradient-difference pairs.
Article: main_krylov, def:classes and cor:lm, genuine linear observed-history synthesis.
Proof: Induct over genuine records. Actual current gradients map correctly and true linearity preserves every real observed secant subtraction. -/
theorem History.pairs_map (f : E →ₗ[ℝ] F) (H : History E) :
    (H.map f).pairs=H.pairs.map (fun p => (f p.1,f p.2)) := by
  -- Each genuine stored secant uses the real preceding gradient, so true linear subtraction is essential.
  rcases H with ⟨initial,records⟩
  induction records with
  | nil => rfl
  | cons r rs ih =>
    change (f r.step,f r.gradient-(History.mk (f initial) (rs.map (IterationRecord.map f))).gradient)::
      (History.mk (f initial) (rs.map (IterationRecord.map f))).pairs=_
    have hg : (History.mk (f initial) (rs.map (IterationRecord.map f))).gradient=f (History.mk initial rs).gradient :=
      History.gradient_map f (History.mk initial rs)
    change (History.mk (f initial) (rs.map (IterationRecord.map f))).pairs=
      (History.mk initial rs).pairs.map (fun p => (f p.1,f p.2)) at ih
    rw [hg,← map_sub,ih]
    rfl
end Linear
end krylov.Methods
