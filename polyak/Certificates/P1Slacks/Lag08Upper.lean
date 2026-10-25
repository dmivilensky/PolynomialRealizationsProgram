import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 8, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate08Upper : Certificate where
  degree0 := 14
  degree1 := 7
  coefficient := ![
    ![64,448,1344,2240,2240,1344,448,64],
    ![896,6272,18816,31360,31360,18816,6272,896],
    ![5761,40345,121053,201725,201635,120891,40255,5743],
    ![22540,157996,474204,789980,788900,472260,156916,22324],
    ![(1917559/32),(3365131/8),(40419345/32),(33651715/16),(67116185/32),1252572,(13273279/32),(940055/16)],
    ![(1831123/16),(3219799/4),(38699733/16),(32200015/8),(64097405/16),2384688,(12576571/16),(885299/8)],
    ![(82843095/512),(1168347615/1024),(1756910205/512),(5842904475/1024),(2900674725/512),(3439021365/1024),(563396295/512),(157375185/1024)],
    ![(10999479/64),(155626719/128),(234295965/64),(778522395/128),(385370565/64),(454585653/128),(73922727/64),(20442705/128)],
    ![(17620617/128),(16018652319/16384),(96607915929/32768),(160360672785/32768),(79114448145/16384),(11596334859/4096),(29905462533/32768),(4084496409/32768)],
    ![(5287513/64),(4829882717/8192),(29184760011/16384),(48403238195/16384),(23792272435/8192),(3463874241/2048),(8840875279/16384),(1189785931/16384)],
    ![(9344069/256),(4292562737/16384),(26003150967/32768),(1379178579583/1048576),(1350620285167/1048576),(780677607615/1048576),(246135467981/1048576),(16274844175/524288)],
    ![(734881/64),(340009723/4096),(2066633853/8192),(109594538303/262144),(106914930287/262144),(61303292607/262144),(19071756685/262144),(1235294831/131072)],
    ![(310205/128),(289611217/16384),(1768565751/32768),(46928358349/524288),(45622217581/524288),(1660051172265/33554432),(127188675485/8388608),(64314330887/33554432)],
    ![(19571/64),(18481885/8192),(113632971/16384),(3022295503/262144),(2930319247/262144),(105678392361/16777216),(7958962685/4194304),(3908534279/16777216)],
    ![(8855/512),(2122831/16384),(13188057/32768),(705211583/1048576),(682870127/1048576),(12192945225/33554432),(899687573/8388608),(6822166505/536870912)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row08Upper_00 : Expr := (.add (.literal (64)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_00 :
    (certificate08Upper.rowExpression ⟨0,by decide⟩).check row08Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row08Upper_01 : Expr := (.add (.literal (896)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_01 :
    (certificate08Upper.rowExpression ⟨1,by decide⟩).check row08Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row08Upper_02 : Expr := (.add (.literal (5761)) (.mul .y (.add (.literal (18)) (.mul .y (.add (.literal (-36)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_02 :
    (certificate08Upper.rowExpression ⟨2,by decide⟩).check row08Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row08Upper_03 : Expr := (.add (.literal (22540)) (.mul .y (.add (.literal (216)) (.mul .y (.add (.literal (-432)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_03 :
    (certificate08Upper.rowExpression ⟨3,by decide⟩).check row08Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row08Upper_04 : Expr := (.add (.literal ((1917559/32))) (.mul .y (.add (.literal ((37611/32))) (.mul .y (.add (.literal ((-18765/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_04 :
    (certificate08Upper.rowExpression ⟨4,by decide⟩).check row08Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row08Upper_05 : Expr := (.add (.literal ((1831123/16))) (.mul .y (.add (.literal ((61335/16))) (.mul .y (.add (.literal ((-30465/4))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_05 :
    (certificate08Upper.rowExpression ⟨5,by decide⟩).check row08Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row08Upper_06 : Expr := (.add (.literal ((82843095/512))) (.mul .y (.add (.literal ((8544285/1024))) (.mul .y (.add (.literal ((-8427645/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_06 :
    (certificate08Upper.rowExpression ⟨6,by decide⟩).check row08Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row08Upper_07 : Expr := (.add (.literal ((10999479/64))) (.mul .y (.add (.literal ((1634013/128))) (.mul .y (.add (.literal ((-1595133/64))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_07 :
    (certificate08Upper.rowExpression ⟨7,by decide⟩).check row08Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row08Upper_08 : Expr := (.add (.literal ((17620617/128))) (.mul .y (.add (.literal ((230579487/16384))) (.mul .y (.add (.literal ((-887474907/32768))) (.mul .y (.add (.literal ((-32805/16384))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_08 :
    (certificate08Upper.rowExpression ⟨8,by decide⟩).check row08Upper_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row08Upper_09 : Expr := (.add (.literal ((5287513/64))) (.mul .y (.add (.literal ((92271069/8192))) (.mul .y (.add (.literal ((-348162705/16384))) (.mul .y (.add (.literal ((-98415/8192))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_09 :
    (certificate08Upper.rowExpression ⟨9,by decide⟩).check row08Upper_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row08Upper_10 : Expr := (.add (.literal ((9344069/256))) (.mul .y (.add (.literal ((106419825/16384))) (.mul .y (.add (.literal ((-390744405/32768))) (.mul .y (.add (.literal ((-31079457/1048576))) (.mul .y (.add (.literal ((-295245/1048576))) (.mul .y (.add (.literal ((177147/262144))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_10 :
    (certificate08Upper.rowExpression ⟨10,by decide⟩).check row08Upper_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row08Upper_11 : Expr := (.add (.literal ((734881/64))) (.mul .y (.add (.literal ((10783035/4096))) (.mul .y (.add (.literal ((-38122695/8192))) (.mul .y (.add (.literal ((-10084257/262144))) (.mul .y (.add (.literal ((-295245/262144))) (.mul .y (.add (.literal ((177147/65536))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_11 :
    (certificate08Upper.rowExpression ⟨11,by decide⟩).check row08Upper_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row08Upper_12 : Expr := (.add (.literal ((310205/128))) (.mul .y (.add (.literal ((11667537/16384))) (.mul .y (.add (.literal ((-39106773/32768))) (.mul .y (.add (.literal ((-14506371/524288))) (.mul .y (.add (.literal ((-885735/524288))) (.mul .y (.add (.literal ((132328809/33554432))) (.mul .y (.add (.literal ((531441/16777216))) (.mul .y (.add (.literal ((-531441/8388608))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_12 :
    (certificate08Upper.rowExpression ⟨12,by decide⟩).check row08Upper_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row08Upper_13 : Expr := (.add (.literal ((19571/64))) (.mul .y (.add (.literal ((946269/8192))) (.mul .y (.add (.literal ((-2935953/16384))) (.mul .y (.add (.literal ((-2735937/262144))) (.mul .y (.add (.literal ((-295245/262144))) (.mul .y (.add (.literal ((41629545/16777216))) (.mul .y (.add (.literal ((531441/8388608))) (.mul .y (.add (.literal ((-531441/4194304))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_13 :
    (certificate08Upper.rowExpression ⟨13,by decide⟩).check row08Upper_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row08Upper_14 : Expr := (.add (.literal ((8855/512))) (.mul .y (.add (.literal ((139311/16384))) (.mul .y (.add (.literal ((-384795/32768))) (.mul .y (.add (.literal ((-1686177/1048576))) (.mul .y (.add (.literal ((-295245/1048576))) (.mul .y (.add (.literal ((18954729/33554432))) (.mul .y (.add (.literal ((531441/16777216))) (.mul .y (.add (.literal ((-29229255/536870912))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Upper_14 :
    (certificate08Upper.rowExpression ⟨14,by decide⟩).check row08Upper_14=true := by kernel_decide

def rows08Upper : Fin (certificate08Upper.degree0+1) → Expr := ![row08Upper_00,row08Upper_01,row08Upper_02,row08Upper_03,row08Upper_04,row08Upper_05,row08Upper_06,row08Upper_07,row08Upper_08,row08Upper_09,row08Upper_10,row08Upper_11,row08Upper_12,row08Upper_13,row08Upper_14]

theorem rowsChecked08Upper : ∀ i, (certificate08Upper.rowExpression i).check (rows08Upper i)=true := by
  intro i
  fin_cases i
  · exact checked08Upper_00
  · exact checked08Upper_01
  · exact checked08Upper_02
  · exact checked08Upper_03
  · exact checked08Upper_04
  · exact checked08Upper_05
  · exact checked08Upper_06
  · exact checked08Upper_07
  · exact checked08Upper_08
  · exact checked08Upper_09
  · exact checked08Upper_10
  · exact checked08Upper_11
  · exact checked08Upper_12
  · exact checked08Upper_13
  · exact checked08Upper_14


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity08Upper : slackRowsIdentityCheck 8 (1) certificate08Upper rows08Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted08Upper : certificate08Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive08Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 8 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate08Upper rows08Upper rowsChecked08Upper identity08Upper accepted08Upper hz hz1 ha

end polyak.Certificates.P1Slacks
