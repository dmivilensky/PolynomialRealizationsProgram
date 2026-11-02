import krylov.Correction.DeepStage0
import krylov.Correction.DeepStage1
import krylov.Correction.DeepStage2
import krylov.Correction.DeepStage3
import krylov.Correction.DeepExecution

/-!
Article: main_krylov, prop:deep, complete checked source-block interfaces.
Use: Independently decode the original exact arithmetic outputs, propagate
actual interval enclosures and derive genuine spectral RFC gate acceptance.
Source: original observed-array RFC; unchanged earlier-package integer
checker soundness and the reused spectral versus Hilbert--Schmidt estimate.
-/

namespace krylov.Correction.Certificate
noncomputable section
open chebyshev2.Numerics.IntegerCertificate
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator
set_option maxRecDepth 30000
set_option maxHeartbeats 20000000

/-- The actual independently decoded original arithmetic program at each of the four true source phases.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
-/
def deepProgram : (k : Fin 4) → SourceProgram k
  | ⟨0,_⟩ => deepStage0Program
  | ⟨1,_⟩ => deepStage1Program
  | ⟨2,_⟩ => deepStage2Program
  | ⟨3,_⟩ => deepStage3Program

/-- The completely accepted original interval or endpoint enclosure at each actual source phase.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
-/
def deepEnclosure (d : Fin 3) : (k : Fin 4) → SourceEnclosure (deepProgram k) deepScale
  | ⟨0,_⟩ => if d=0 then deepStage0Interval else if d=1 then deepStage0Left else deepStage0Right
  | ⟨1,_⟩ => if d=0 then deepStage1Interval else if d=1 then deepStage1Left else deepStage1Right
  | ⟨2,_⟩ => if d=0 then deepStage2Interval else if d=1 then deepStage2Left else deepStage2Right
  | ⟨3,_⟩ => if d=0 then deepStage3Interval else if d=1 then deepStage3Left else deepStage3Right

/-- The independent output inventory has exactly its original phase-dependent finite length.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem sourceOutputs_length (k : Fin 4) : (sourceOutputs k).length=if k.val<3 then 31+9*k.val else 31 := by
  fin_cases k <;> decide +kernel

/-- The actual final inventory index of each genuine next-input coordinate.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
-/
def sourceNextIndex (k : Fin 3) (j : Fin (5+8*(k.val+1))) : Fin (sourceOutputs k.castSucc).length :=
  ⟨18+k.val+j.val,by rw [sourceOutputs_length]; simp only [Fin.val_castSucc,ite_eq_left k.isLt]; have := j.isLt; omega⟩

/-- Each original next-state output is exactly its independently specified true next-input expression.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem sourceOutputs_next (k : Fin 3) (j : Fin (5+8*(k.val+1))) :
    (sourceOutputs k.castSucc).get (sourceNextIndex k j)=
      (sourceNextInputs k.val).get ⟨j.val,by rw [sourceNextInputs_length]; exact j.isLt⟩ := by
  fin_cases k <;> fin_cases j <;> decide +kernel

/-- The exact integer output intervals of one source block are precisely the original input intervals of the next block.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem deep_next_inputs (d : Fin 3) (k : Fin 3) (j : Fin (5+8*(k.val+1))) :
    (deepEnclosure d k.succ).inputs[j.val]?=some ((deepEnclosure d k.castSucc).outputs (sourceNextIndex k j)) := by
  fin_cases d <;> fin_cases k <;> fin_cases j <;> decide +kernel

/-- Every original input stack has exactly the actual finite prefix layout length.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem deep_inputs_length (d : Fin 3) (k : Fin 4) :
    (deepEnclosure d k).inputs.length=if k.val=0 then 1 else 5+8*k.val := by
  fin_cases d <;> fin_cases k <;> decide +kernel

/-- Every actual enclosed source prefix gives the genuine enclosure of its next recursively evaluated prefix.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem deep_next_enclosed (d : Fin 3) (k : Fin 3) (s : ℝ)
    (h : Encloses deepScale (deepEnclosure d k.castSucc).inputs (sourceData k.val s)) :
    Encloses deepScale (deepEnclosure d k.succ).inputs (sourceData (k.val+1) s) := by
  -- Select the genuine next-input coordinate and recover its identical certified interval from the preceding true output.
  intro j I hj
  have hjl : j<(deepEnclosure d k.succ).inputs.length := (List.getElem?_eq_some_iff.mp hj).choose
  rw [deep_inputs_length] at hjl
  simp only [Fin.val_succ] at hjl
  have hne : ¬k.val+1=0 := by omega
  rw [ite_eq_right hne] at hjl
  let j' : Fin (5+8*(k.val+1)) := ⟨j,hjl⟩
  have hi := deep_next_inputs d k j'
  have hI : I=(deepEnclosure d k.castSucc).outputs (sourceNextIndex k j') := by
    rw [hj] at hi
    exact Option.some.inj hi
  rw [hI]
  have he := (deepEnclosure d k.castSucc).enclosed deepScale_pos h (sourceNextIndex k j')
  rw [sourceOutputs_next,sourceNextInputs_value] at he
  exact he

/-- The exact finite output-inventory index of a primary original phase feature.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
-/
def sourcePrimaryIndex (k : Fin 4) (i : Fin 5) : Fin (sourceOutputs k).length :=
  ⟨i.val,by rw [sourceOutputs_length]; have := i.isLt; split_ifs <;> omega⟩

/-- The exact output-inventory index of an actual augmented source pair energy.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
-/
def sourceEnergyIndex (k : Fin 4) (i : Fin (k.val+1)) : Fin (sourceOutputs k).length :=
  ⟨5+i.val,by rw [sourceOutputs_length]; have := i.isLt; have := k.isLt; split_ifs <;> omega⟩

/-- The exact output-inventory index of an actual previously observed pair energy.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
-/
def sourceOldEnergyIndex (k : Fin 4) (i : Fin k.val) : Fin (sourceOutputs k).length :=
  ⟨6+i.val,by rw [sourceOutputs_length]; have := i.isLt; have := k.isLt; split_ifs <;> omega⟩

/-- The original old-defect output is exactly the true rational observed-pair squared-defect expression.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem sourceOutputs_oldDefect (k : Fin 4) :
    (sourceOutputs k).get (sourcePrimaryIndex k 3)=
      termDefectSquare (sourceInputPrefix k.val).steps (sourceInputPrefix k.val).images := by
  fin_cases k <;> decide +kernel

/-- Each augmented-energy output is exactly the genuine observed step-image pairing expression.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem sourceOutputs_energy (k : Fin 4) (i : Fin (k.val+1)) :
    (sourceOutputs k).get (sourceEnergyIndex k i)=termDot (sourceAugSteps k.val i) (sourceAugImages k.val i) := by
  fin_cases k <;> fin_cases i <;> decide +kernel

/-- Each old-energy output is exactly the pairing of its true recorded total step and measured secant.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem sourceOutputs_oldEnergy (k : Fin 4) (i : Fin k.val) :
    (sourceOutputs k).get (sourceOldEnergyIndex k i)=
      termDot ((sourceInputPrefix k.val).steps i) ((sourceInputPrefix k.val).images i) := by
  fin_cases k <;> fin_cases i <;> decide +kernel

/-- Every original augmented source energy has a strictly positive certified integer lower bound.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem deep_energy_checked (d : Fin 3) (k : Fin 4) (i : Fin (k.val+1)) :
    0<((deepEnclosure d k).outputs (sourceEnergyIndex k i)).lo := by
  fin_cases d <;> fin_cases k <;> fin_cases i <;> decide +kernel

/-- Every original recorded source pair energy has a strictly positive certified integer lower bound.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem deep_old_energy_checked (d : Fin 3) (k : Fin 4) (i : Fin k.val) :
    0<((deepEnclosure d k).outputs (sourceOldEnergyIndex k i)).lo := by
  fin_cases d <;> fin_cases k <;> fin_cases i <;> decide +kernel

/-- Every original recorded-pair squared defect has a certified strict unit upper bound.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem deep_old_defect_checked (d : Fin 3) (k : Fin 4) :
    ((deepEnclosure d k).outputs (sourcePrimaryIndex k 3)).hi<(deepScale : ℤ) := by
  fin_cases d <;> fin_cases k <;> decide +kernel

/-- A genuine positive scaled integer lower bound implies strict positivity of its actual enclosed real value.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem Bounds.mem_pos {scale : ℕ} (hs : 0<scale) {I : Bounds} {x : ℝ}
    (hx : I.Mem scale x) (hi : 0<I.lo) : 0<x := by
  have hscale : (0 : ℝ)<scale := by exact_mod_cast hs
  have hlo : (0 : ℝ)<I.lo := by exact_mod_cast hi
  have := hx.1
  nlinarith

/-- A genuine strict scaled integer unit upper bound implies a strict unit bound for its real value.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem Bounds.mem_lt_one {scale : ℕ} (hs : 0<scale) {I : Bounds} {x : ℝ}
    (hx : I.Mem scale x) (hi : I.hi<(scale : ℤ)) : x<1 := by
  have hscale : (0 : ℝ)<scale := by exact_mod_cast hs
  have hhi : (I.hi : ℝ)<scale := by exact_mod_cast hi
  have := hx.2
  nlinarith

/-- Every original enclosed source block passes the true spectral RFC observed-data gate.
Use: Connect the complete original numerical certificate with the actual observed RFC executor.
Article: main_krylov, prop:deep, complete original checked source interfaces.
Proof: Use exact checked integer data, independent original source decoding and the proved real enclosure semantics.
-/
theorem deep_gate_of_enclosed (d : Fin 3) (k : Fin 4) {x : ℕ → ℝ}
    (hx : Encloses deepScale (deepEnclosure d k).inputs x) :
    ‖krylov.Methods.pairDefect
      (fun i => euclideanValue ((sourceInputPrefix k.val).steps i) x)
      (fun i => euclideanValue ((sourceInputPrefix k.val).images i) x)‖<1 := by
  -- Positive real pair energies and the actual rational squared-defect estimate imply the true spectral gate.
  apply pairDefect_gate_of_squared_bound
  · intro i
    have hi := (deepEnclosure d k).enclosed deepScale_pos hx (sourceOldEnergyIndex k i)
    rw [sourceOutputs_oldEnergy,termDot_inner] at hi
    exact Bounds.mem_pos deepScale_pos hi (deep_old_energy_checked d k i)
  · have hi := (deepEnclosure d k).enclosed deepScale_pos hx (sourcePrimaryIndex k 3)
    rw [sourceOutputs_oldDefect,termDefectSquare_value] at hi
    exact Bounds.mem_lt_one deepScale_pos hi (deep_old_defect_checked d k)

end
end krylov.Correction.Certificate
