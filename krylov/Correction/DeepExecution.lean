import krylov.Correction.DeepExpressions

/-!
Article: main_krylov, prop:deep, genuine finite certificate execution.
Use: Propagate actual gradients, recorded total steps and measured secants
through the original independent source input layout and actual RFC gates.
Source: original array-phase execution, exact finite input decoding and
independently proved physical source oracle semantics.
-/

namespace krylov.Correction.Certificate
noncomputable section
open Matrix Finset chebyshev2.Numerics.IntegerCertificate krylov.Methods krylov.Reference
open scoped BigOperators InnerProductSpace Matrix.Norms.L2Operator

/-- The genuine recursively evaluated original source inputs, with no assumed target trajectory.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
-/
def sourceData : ℕ → ℝ → ℕ → ℝ
  | 0,s => fun j => if j=0 then s else 0
  | k+1,s =>
    let x := sourceData k s
    let h := (sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)
    encodeInput (k+1) s (vectorValue h.gradient x)
      (fun i => vectorValue (h.steps i) x) (fun i => vectorValue (h.images i) x) 0

/-- Every genuine source input prefix preserves exactly the original affine parameter.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_parameter (k : ℕ) (s : ℝ) : sourceData k s 0=s := by
  cases k with
  | zero => rfl
  | succ k => simp only [sourceData,encodeInput_parameter]

/-- The newly decoded source gradient is exactly the preceding actual arithmetic phase output.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_gradient (k : ℕ) (s : ℝ) :
    euclideanValue (sourceInputPrefix (k+1)).gradient (sourceData (k+1) s)=
      euclideanValue ((sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)).gradient (sourceData k s) := by
  ext i
  change sourceData (k+1) s (1+i.val)=_
  rw [sourceData,encodeInput_gradient]
  rfl

/-- Every newly decoded total step is exactly the true preceding arithmetic phase record.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_steps (k : ℕ) (s : ℝ) (i : Fin (k+1)) :
    euclideanValue ((sourceInputPrefix (k+1)).steps i) (sourceData (k+1) s)=
      euclideanValue (((sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)).steps i) (sourceData k s) := by
  ext j
  change sourceData (k+1) s (5+4*i.val+j.val)=_
  rw [sourceData,encodeInput_step]
  rfl

/-- Every newly decoded measured secant is exactly the true preceding arithmetic phase record.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_images (k : ℕ) (s : ℝ) (i : Fin (k+1)) :
    euclideanValue ((sourceInputPrefix (k+1)).images i) (sourceData (k+1) s)=
      euclideanValue (((sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)).images i) (sourceData k s) := by
  ext j
  change sourceData (k+1) s (5+4*(k+1)+4*i.val+j.val)=_
  rw [sourceData,encodeInput_image]
  rfl

/-- The interpreted source probes on every genuine input prefix are the actual original physical scenario probes.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_probes (k j : ℕ) (s : ℝ) :
    cgOperator (matrixValue (sourceProbe j) (sourceData k s))=(deepScenario s).probeOracle j := by
  rw [sourceProbe_value,sourceData_parameter]
  rfl

/-- The interpreted source corrections on every genuine input prefix are the actual original physical scenario correction oracles.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_corrections (k j : ℕ) (s : ℝ) :
    cgOperator (matrixValue (sourceCorrection j) (sourceData k s))=(deepScenario s).correctionOracle 3 j := by
  rw [sourceCorrection_value,sourceData_parameter]

/-- An actual accepted gate propagates equality of the independently compiled source data with the genuine RFC executor.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_realizes_next (k : ℕ) (s : ℝ)
    (hh : (sourceInputPrefix k).Realizes sourceProbe sourceCorrection sourceInitial (sourceData k s))
    (hgate : k=0 ∨ 0<k ∧ ‖pairDefect
      (fun i => euclideanValue ((sourceInputPrefix k).steps i) (sourceData k s))
      (fun i => euclideanValue ((sourceInputPrefix k).images i) (sourceData k s))‖<1) :
    (sourceInputPrefix (k+1)).Realizes sourceProbe sourceCorrection sourceInitial (sourceData (k+1) s) := by
  -- Propagate the genuine array phase, then identify both copies of the same actual physical source oracle.
  have hn := hh.advance hgate
  unfold TermPrefix.Realizes at hn ⊢
  simp only [sourceData_probes,sourceData_corrections,sourceInitial_value] at hn ⊢
  exact ⟨(sourceData_gradient k s).trans hn.1,
    fun i => (sourceData_steps k s i).trans (hn.2.1 i),
    fun i => (sourceData_images k s i).trans (hn.2.2 i)⟩

/-- The initial independently compiled source data agrees with the actual original empty RFC history.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceData_realizes_zero (s : ℝ) :
    (sourceInputPrefix 0).Realizes sourceProbe sourceCorrection sourceInitial (sourceData 0 s) := by
  refine ⟨rfl,?_,?_⟩ <;> intro i <;> exact Fin.elim0 i

/-- The complete original next-input inventory has precisely its genuine finite coordinate length.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceNextInputs_length (k : ℕ) : (sourceNextInputs k).length=5+8*(k+1) := by
  simp only [sourceNextInputs,List.length_ofFn]

/-- Every next-input source expression evaluates to exactly the next genuine source-data coordinate.
Use: Close the exact original numerical certificate on the real observed RFC execution.
Article: main_krylov, prop:deep, genuine original source execution.
Proof: Use exact finite input decoding and the independently proved original source semantics.
-/
theorem sourceNextInputs_value (k : ℕ) (s : ℝ) (j : Fin (5+8*(k+1))) :
    ((sourceNextInputs k).get ⟨j.val,by rw [sourceNextInputs_length]; exact j.isLt⟩).value (sourceData k s)=sourceData (k+1) s j.val := by
  -- Interpret the original complete next-input encoding coordinatewise before identifying the genuine next data.
  have he := encodeInput_map (fun t : Term => t.value (sourceData k s)) (k+1) sourceParameter
    ((sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)).gradient
    ((sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)).steps
    ((sourceInputPrefix k).advance (sourceProbe k) (sourceCorrection k)).images (.literal 0 1) j.val
  simp only [sourceParameter,Expr.value,sourceData_parameter] at he
  simp only [sourceNextInputs,List.get_eq_getElem,List.getElem_ofFn]
  dsimp only [sourceData]
  unfold vectorValue
  simpa only [sourceParameter,Function.comp_def,Int.cast_zero,Nat.cast_one,zero_div] using he

end
end krylov.Correction.Certificate
