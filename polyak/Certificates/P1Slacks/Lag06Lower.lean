import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 6, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate06Lower : Certificate where
  degree0 := 14
  degree1 := 7
  coefficient := ![
    ![64,448,1344,2240,2240,1344,448,64],
    ![896,6272,18816,31360,31360,18816,6272,896],
    ![5761,40309,120873,201365,201275,120711,40219,5743],
    ![22540,157564,472044,785660,784580,470100,156484,22324],
    ![(1917559/32),(6692651/16),(40043235/32),(33275605/16),(66363965/32),(19853097/16),(13198057/32),(940055/16)],
    ![(1831123/16),(6378263/8),(38086383/16),(31586665/8),(62870705/16),(18770829/8),(12453901/16),(885299/8)],
    ![(331373109/2048),(287816037/256),(6856795215/2048),(5672055225/1024),(11260996755/2048),(1676797641/512),(2219414601/2048),(157375185/1024)],
    ![(43998645/256),(38090949/32),(904543695/256),(745878585/128),(1476190995/256),(219131145/64),(289161417/256),(20442705/128)],
    ![(70487571/512),(62239072029/65536),(184028269131/65536),(75584882703/16384),(149036277219/32768),(176347680165/65536),(57972043167/65536),(4084496409/32768)],
    ![(21155155/256),(18590369111/32768),(54713677281/32768),(22371946669/8192),(43923330857/16384),(51759557871/32768),(16949086685/32768),(1189785931/16384)],
    ![(37401791/1024),(16341064883/65536),(47834696229/65536),(1245388132063/1048576),(1216661999977/1048576),(713641264035/1048576),(232719548951/1048576),(16274844175/524288)],
    ![(2944627/256),(1278117265/16384),(3718367031/16384),(96252864863/262144),(93535122857/262144),(54600137859/262144),(17729175223/262144),(1235294831/131072)],
    ![(1245923/512),(1073560243/65536),(3101729637/65536),(39890778109/524288),(38541385771/524288),(1432528308393/33554432),(28945513091/2097152),(64314330887/33554432)],
    ![(79013/256),(67525975/32768),(193622241/32768),(2472752191/262144),(2373854809/262144),(87735621417/16777216),(1764631499/1048576),(3908534279/16777216)],
    ![(36149/2048),(7657501/65536),(21778347/65536),(551831135/1048576),(525694505/1048576),(9648252105/33554432),(193035773/2097152),(6822166505/536870912)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row06Lower_00 : Expr := (.add (.literal (64)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_00 :
    (certificate06Lower.rowExpression ⟨0,by decide⟩).check row06Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row06Lower_01 : Expr := (.add (.literal (896)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_01 :
    (certificate06Lower.rowExpression ⟨1,by decide⟩).check row06Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row06Lower_02 : Expr := (.add (.literal (5761)) (.mul .y (.add (.literal (-18)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_02 :
    (certificate06Lower.rowExpression ⟨2,by decide⟩).check row06Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row06Lower_03 : Expr := (.add (.literal (22540)) (.mul .y (.add (.literal (-216)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_03 :
    (certificate06Lower.rowExpression ⟨3,by decide⟩).check row06Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row06Lower_04 : Expr := (.add (.literal ((1917559/32))) (.mul .y (.add (.literal ((-37611/32))) (.mul .y (.add (.literal ((81/16))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_04 :
    (certificate06Lower.rowExpression ⟨4,by decide⟩).check row06Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row06Lower_05 : Expr := (.add (.literal ((1831123/16))) (.mul .y (.add (.literal ((-61335/16))) (.mul .y (.add (.literal ((405/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_05 :
    (certificate06Lower.rowExpression ⟨5,by decide⟩).check row06Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row06Lower_06 : Expr := (.add (.literal ((331373109/2048))) (.mul .y (.add (.literal ((-17083467/2048))) (.mul .y (.add (.literal ((57591/256))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_06 :
    (certificate06Lower.rowExpression ⟨6,by decide⟩).check row06Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row06Lower_07 : Expr := (.add (.literal ((43998645/256))) (.mul .y (.add (.literal ((-3262923/256))) (.mul .y (.add (.literal ((18711/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_07 :
    (certificate06Lower.rowExpression ⟨7,by decide⟩).check row06Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row06Lower_08 : Expr := (.add (.literal ((70487571/512))) (.mul .y (.add (.literal ((-917791587/65536))) (.mul .y (.add (.literal ((64427805/65536))) (.mul .y (.add (.literal ((-6561/8192))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_08 :
    (certificate06Lower.rowExpression ⟨8,by decide⟩).check row06Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row06Lower_09 : Expr := (.add (.literal ((21155155/256))) (.mul .y (.add (.literal ((-364649769/32768))) (.mul .y (.add (.literal ((36519255/32768))) (.mul .y (.add (.literal ((-19683/4096))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_09 :
    (certificate06Lower.rowExpression ⟨9,by decide⟩).check row06Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row06Lower_10 : Expr := (.add (.literal ((37401791/1024))) (.mul .y (.add (.literal ((-414937485/65536))) (.mul .y (.add (.literal ((56314035/65536))) (.mul .y (.add (.literal ((-12183777/1048576))) (.mul .y (.add (.literal ((295245/1048576))) (.mul .y (.add (.literal ((59049/524288))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_10 :
    (certificate06Lower.rowExpression ⟨10,by decide⟩).check row06Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row06Lower_11 : Expr := (.add (.literal ((2944627/256))) (.mul .y (.add (.literal ((-41075631/16384))) (.mul .y (.add (.literal ((7242129/16384))) (.mul .y (.add (.literal ((-3785697/262144))) (.mul .y (.add (.literal ((295245/262144))) (.mul .y (.add (.literal ((59049/131072))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_11 :
    (certificate06Lower.rowExpression ⟨11,by decide⟩).check row06Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row06Lower_12 : Expr := (.add (.literal ((1245923/512))) (.mul .y (.add (.literal ((-42786765/65536))) (.mul .y (.add (.literal ((9409203/65536))) (.mul .y (.add (.literal ((-5058531/524288))) (.mul .y (.add (.literal ((885735/524288))) (.mul .y (.add (.literal ((18954729/33554432))) (.mul .y (.add (.literal ((-531441/16777216))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_12 :
    (certificate06Lower.rowExpression ⟨12,by decide⟩).check row06Lower_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row06Lower_13 : Expr := (.add (.literal ((79013/256))) (.mul .y (.add (.literal ((-3269673/32768))) (.mul .y (.add (.literal ((853335/32768))) (.mul .y (.add (.literal ((-846369/262144))) (.mul .y (.add (.literal ((295245/262144))) (.mul .y (.add (.literal ((3838185/16777216))) (.mul .y (.add (.literal ((-531441/8388608))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_13 :
    (certificate06Lower.rowExpression ⟨13,by decide⟩).check row06Lower_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row06Lower_14 : Expr := (.add (.literal ((36149/2048))) (.mul .y (.add (.literal ((-439875/65536))) (.mul .y (.add (.literal ((125469/65536))) (.mul .y (.add (.literal ((-426465/1048576))) (.mul .y (.add (.literal ((295245/1048576))) (.mul .y (.add (.literal ((59049/33554432))) (.mul .y (.add (.literal ((-531441/16777216))) (.mul .y (.add (.literal ((4782969/536870912))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked06Lower_14 :
    (certificate06Lower.rowExpression ⟨14,by decide⟩).check row06Lower_14=true := by kernel_decide

def rows06Lower : Fin (certificate06Lower.degree0+1) → Expr := ![row06Lower_00,row06Lower_01,row06Lower_02,row06Lower_03,row06Lower_04,row06Lower_05,row06Lower_06,row06Lower_07,row06Lower_08,row06Lower_09,row06Lower_10,row06Lower_11,row06Lower_12,row06Lower_13,row06Lower_14]

theorem rowsChecked06Lower : ∀ i, (certificate06Lower.rowExpression i).check (rows06Lower i)=true := by
  intro i
  fin_cases i
  · exact checked06Lower_00
  · exact checked06Lower_01
  · exact checked06Lower_02
  · exact checked06Lower_03
  · exact checked06Lower_04
  · exact checked06Lower_05
  · exact checked06Lower_06
  · exact checked06Lower_07
  · exact checked06Lower_08
  · exact checked06Lower_09
  · exact checked06Lower_10
  · exact checked06Lower_11
  · exact checked06Lower_12
  · exact checked06Lower_13
  · exact checked06Lower_14


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity06Lower : slackRowsIdentityCheck 6 (-1) certificate06Lower rows06Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted06Lower : certificate06Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive06Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 6 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate06Lower rows06Lower rowsChecked06Lower identity06Lower accepted06Lower hz hz1 ha

end polyak.Certificates.P1Slacks
