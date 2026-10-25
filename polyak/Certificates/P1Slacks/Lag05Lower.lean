import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 5, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate05Lower : Certificate where
  degree0 := 12
  degree1 := 6
  coefficient := ![
    ![32,192,480,640,480,192,32],
    ![384,2304,5760,7680,5760,2304,384],
    ![2085,12501,31230,41610,31185,12465,2076],
    ![6770,40530,101100,134500,100650,40170,6680],
    ![(234081/16),(1398087/16),(6958521/32),288612,(861867/4),(1372653/16),(455445/32)],
    ![(44289/2),(263655/2),(1307961/4),432576,321894,(255501/2),(84501/4)],
    ![(96159/4),(569961/4),(2815407/8),463596,343539,(543123/4),(178899/8)],
    ![(37647/2),(221913/2),(1090287/4),357192,263358,(207171/2),(67923/4)],
    ![(84195/8),(492885/8),(2463568479/16384),(3208609755/16384),(4704459021/32768),(115043679/2048),(300316635/32768)],
    ![(8167/2),(47409/2),(235151967/4096),(304185307/4096),(443373837/8192),(10789215/512),(28055515/8192)],
    ![(4155/4),(23877/4),(117419805/8192),(150847377/8192),(13999898043/1048576),(5432591007/1048576),(220356537/262144)],
    ![(309/2),(1755/2),(8555103/4096),(10928091/4096),(1011414843/524288),(392415903/524288),(15950937/131072)],
    ![(161/16),(903/16),(2185311/16384),(2785243/16384),(129095067/1048576),(50334879/1048576),(263890063/33554432)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row05Lower_00 : Expr := (.add (.literal (32)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_00 :
    (certificate05Lower.rowExpression ⟨0,by decide⟩).check row05Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row05Lower_01 : Expr := (.add (.literal (384)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_01 :
    (certificate05Lower.rowExpression ⟨1,by decide⟩).check row05Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row05Lower_02 : Expr := (.add (.literal (2085)) (.mul .y (.add (.literal (-9)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_02 :
    (certificate05Lower.rowExpression ⟨2,by decide⟩).check row05Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row05Lower_03 : Expr := (.add (.literal (6770)) (.mul .y (.add (.literal (-90)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_03 :
    (certificate05Lower.rowExpression ⟨3,by decide⟩).check row05Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row05Lower_04 : Expr := (.add (.literal ((234081/16))) (.mul .y (.add (.literal ((-6399/16))) (.mul .y (.add (.literal ((81/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_04 :
    (certificate05Lower.rowExpression ⟨4,by decide⟩).check row05Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row05Lower_05 : Expr := (.add (.literal ((44289/2))) (.mul .y (.add (.literal ((-2079/2))) (.mul .y (.add (.literal ((81/4))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_05 :
    (certificate05Lower.rowExpression ⟨5,by decide⟩).check row05Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row05Lower_06 : Expr := (.add (.literal ((96159/4))) (.mul .y (.add (.literal ((-6993/4))) (.mul .y (.add (.literal ((567/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_06 :
    (certificate05Lower.rowExpression ⟨6,by decide⟩).check row05Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row05Lower_07 : Expr := (.add (.literal ((37647/2))) (.mul .y (.add (.literal ((-3969/2))) (.mul .y (.add (.literal ((567/4))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_07 :
    (certificate05Lower.rowExpression ⟨7,by decide⟩).check row05Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row05Lower_08 : Expr := (.add (.literal ((84195/8))) (.mul .y (.add (.literal ((-12285/8))) (.mul .y (.add (.literal ((2896479/16384))) (.mul .y (.add (.literal ((-6561/16384))) (.mul .y (.add (.literal ((-6561/32768))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_08 :
    (certificate05Lower.rowExpression ⟨8,by decide⟩).check row05Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row05Lower_09 : Expr := (.add (.literal ((8167/2))) (.mul .y (.add (.literal ((-1593/2))) (.mul .y (.add (.literal ((574047/4096))) (.mul .y (.add (.literal ((-6561/4096))) (.mul .y (.add (.literal ((-6561/8192))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_09 :
    (certificate05Lower.rowExpression ⟨9,by decide⟩).check row05Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row05Lower_10 : Expr := (.add (.literal ((4155/4))) (.mul .y (.add (.literal ((-1053/4))) (.mul .y (.add (.literal ((560925/8192))) (.mul .y (.add (.literal ((-19683/8192))) (.mul .y (.add (.literal ((-1082565/1048576))) (.mul .y (.add (.literal ((59049/1048576))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_10 :
    (certificate05Lower.rowExpression ⟨10,by decide⟩).check row05Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row05Lower_11 : Expr := (.add (.literal ((309/2))) (.mul .y (.add (.literal ((-99/2))) (.mul .y (.add (.literal ((76383/4096))) (.mul .y (.add (.literal ((-6561/4096))) (.mul .y (.add (.literal ((-242757/524288))) (.mul .y (.add (.literal ((59049/524288))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_11 :
    (certificate05Lower.rowExpression ⟨11,by decide⟩).check row05Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row05Lower_12 : Expr := (.add (.literal ((161/16))) (.mul .y (.add (.literal ((-63/16))) (.mul .y (.add (.literal ((34911/16384))) (.mul .y (.add (.literal ((-6561/16384))) (.mul .y (.add (.literal ((-32805/1048576))) (.mul .y (.add (.literal ((59049/1048576))) (.mul .y (.add (.literal ((-531441/33554432))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked05Lower_12 :
    (certificate05Lower.rowExpression ⟨12,by decide⟩).check row05Lower_12=true := by kernel_decide

def rows05Lower : Fin (certificate05Lower.degree0+1) → Expr := ![row05Lower_00,row05Lower_01,row05Lower_02,row05Lower_03,row05Lower_04,row05Lower_05,row05Lower_06,row05Lower_07,row05Lower_08,row05Lower_09,row05Lower_10,row05Lower_11,row05Lower_12]

theorem rowsChecked05Lower : ∀ i, (certificate05Lower.rowExpression i).check (rows05Lower i)=true := by
  intro i
  fin_cases i
  · exact checked05Lower_00
  · exact checked05Lower_01
  · exact checked05Lower_02
  · exact checked05Lower_03
  · exact checked05Lower_04
  · exact checked05Lower_05
  · exact checked05Lower_06
  · exact checked05Lower_07
  · exact checked05Lower_08
  · exact checked05Lower_09
  · exact checked05Lower_10
  · exact checked05Lower_11
  · exact checked05Lower_12


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity05Lower : slackRowsIdentityCheck 5 (-1) certificate05Lower rows05Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted05Lower : certificate05Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive05Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 5 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate05Lower rows05Lower rowsChecked05Lower identity05Lower accepted05Lower hz hz1 ha

end polyak.Certificates.P1Slacks
