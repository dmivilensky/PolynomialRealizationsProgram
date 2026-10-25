import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 7, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate07Upper : Certificate where
  degree0 := 12
  degree1 := 6
  coefficient := ![
    ![32,192,480,640,480,192,32],
    ![384,2304,5760,7680,5760,2304,384],
    ![2085,12519,31302,41718,31257,12483,2076],
    ![6770,40710,101820,135580,101370,40350,6680],
    ![(234081/16),(1410885/16),(7060905/32),(1173645/4),(874665/4),(1385451/16),(455445/32)],
    ![(44289/2),(267813/2),(1341225/4),445050,330210,(259659/2),(84501/4)],
    ![(96159/4),(583947/4),(2927295/8),484575,357525,(557109/4),(178899/8)],
    ![(37647/2),(229851/2),(1153791/4),381006,279234,(215109/2),(67923/4)],
    ![(84195/8),(517455/8),(2664845919/16384),(3510539037/16384),(5107066389/32768),(485340957/8192),(300316635/32768)],
    ![(8167/2),(50595/2),(261251679/4096),(343347997/4096),(495625749/8192),(46425885/2048),(28055515/8192)],
    ![(4155/4),(25983/4),(134672157/8192),(176765271/8192),(16218276795/1048576),(5989587021/1048576),(220356537/262144)],
    ![(309/2),(1953/2),(10177119/4096),(13374237/4096),(1222392123/524288),(445881933/524288),(15950937/131072)],
    ![(161/16),(1029/16),(2701407/16384),(3572509/16384),(163804827/1048576),(59314125/1048576),(263890063/33554432)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row07Upper_00 : Expr := (.add (.literal (32)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_00 :
    (certificate07Upper.rowExpression ⟨0,by decide⟩).check row07Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row07Upper_01 : Expr := (.add (.literal (384)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_01 :
    (certificate07Upper.rowExpression ⟨1,by decide⟩).check row07Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row07Upper_02 : Expr := (.add (.literal (2085)) (.mul .y (.add (.literal (9)) (.mul .y (.add (.literal (-18)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_02 :
    (certificate07Upper.rowExpression ⟨2,by decide⟩).check row07Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row07Upper_03 : Expr := (.add (.literal (6770)) (.mul .y (.add (.literal (90)) (.mul .y (.add (.literal (-180)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_03 :
    (certificate07Upper.rowExpression ⟨3,by decide⟩).check row07Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row07Upper_04 : Expr := (.add (.literal ((234081/16))) (.mul .y (.add (.literal ((6399/16))) (.mul .y (.add (.literal ((-25515/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_04 :
    (certificate07Upper.rowExpression ⟨4,by decide⟩).check row07Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row07Upper_05 : Expr := (.add (.literal ((44289/2))) (.mul .y (.add (.literal ((2079/2))) (.mul .y (.add (.literal ((-8235/4))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_05 :
    (certificate07Upper.rowExpression ⟨5,by decide⟩).check row07Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row07Upper_06 : Expr := (.add (.literal ((96159/4))) (.mul .y (.add (.literal ((6993/4))) (.mul .y (.add (.literal ((-27405/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_06 :
    (certificate07Upper.rowExpression ⟨6,by decide⟩).check row07Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row07Upper_07 : Expr := (.add (.literal ((37647/2))) (.mul .y (.add (.literal ((3969/2))) (.mul .y (.add (.literal ((-15309/4))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_07 :
    (certificate07Upper.rowExpression ⟨7,by decide⟩).check row07Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row07Upper_08 : Expr := (.add (.literal ((84195/8))) (.mul .y (.add (.literal ((12285/8))) (.mul .y (.add (.literal ((-47422881/16384))) (.mul .y (.add (.literal ((6561/16384))) (.mul .y (.add (.literal ((-32805/32768))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_08 :
    (certificate07Upper.rowExpression ⟨8,by decide⟩).check row07Upper_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row07Upper_09 : Expr := (.add (.literal ((8167/2))) (.mul .y (.add (.literal ((1593/2))) (.mul .y (.add (.literal ((-5950881/4096))) (.mul .y (.add (.literal ((6561/4096))) (.mul .y (.add (.literal ((-32805/8192))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_09 :
    (certificate07Upper.rowExpression ⟨9,by decide⟩).check row07Upper_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row07Upper_10 : Expr := (.add (.literal ((4155/4))) (.mul .y (.add (.literal ((1053/4))) (.mul .y (.add (.literal ((-3752163/8192))) (.mul .y (.add (.literal ((19683/8192))) (.mul .y (.add (.literal ((-6121413/1048576))) (.mul .y (.add (.literal ((-59049/1048576))) (.mul .y (.add (.literal ((59049/524288))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_10 :
    (certificate07Upper.rowExpression ⟨10,by decide⟩).check row07Upper_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row07Upper_11 : Expr := (.add (.literal ((309/2))) (.mul .y (.add (.literal ((99/2))) (.mul .y (.add (.literal ((-329121/4096))) (.mul .y (.add (.literal ((6561/4096))) (.mul .y (.add (.literal ((-1922373/524288))) (.mul .y (.add (.literal ((-59049/524288))) (.mul .y (.add (.literal ((59049/262144))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_11 :
    (certificate07Upper.rowExpression ⟨11,by decide⟩).check row07Upper_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row07Upper_12 : Expr := (.add (.literal ((161/16))) (.mul .y (.add (.literal ((63/16))) (.mul .y (.add (.literal ((-94113/16384))) (.mul .y (.add (.literal ((6561/16384))) (.mul .y (.add (.literal ((-872613/1048576))) (.mul .y (.add (.literal ((-59049/1048576))) (.mul .y (.add (.literal ((3247695/33554432))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Upper_12 :
    (certificate07Upper.rowExpression ⟨12,by decide⟩).check row07Upper_12=true := by kernel_decide

def rows07Upper : Fin (certificate07Upper.degree0+1) → Expr := ![row07Upper_00,row07Upper_01,row07Upper_02,row07Upper_03,row07Upper_04,row07Upper_05,row07Upper_06,row07Upper_07,row07Upper_08,row07Upper_09,row07Upper_10,row07Upper_11,row07Upper_12]

theorem rowsChecked07Upper : ∀ i, (certificate07Upper.rowExpression i).check (rows07Upper i)=true := by
  intro i
  fin_cases i
  · exact checked07Upper_00
  · exact checked07Upper_01
  · exact checked07Upper_02
  · exact checked07Upper_03
  · exact checked07Upper_04
  · exact checked07Upper_05
  · exact checked07Upper_06
  · exact checked07Upper_07
  · exact checked07Upper_08
  · exact checked07Upper_09
  · exact checked07Upper_10
  · exact checked07Upper_11
  · exact checked07Upper_12


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity07Upper : slackRowsIdentityCheck 7 (1) certificate07Upper rows07Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted07Upper : certificate07Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive07Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 7 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate07Upper rows07Upper rowsChecked07Upper identity07Upper accepted07Upper hz hz1 ha

end polyak.Certificates.P1Slacks
