import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 7, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate07Lower : Certificate where
  degree0 := 16
  degree1 := 8
  coefficient := ![
    ![128,1024,3584,7168,8960,7168,3584,1024,128],
    ![2048,16384,57344,114688,143360,114688,57344,16384,2048],
    ![15216,121692,425796,851340,1063860,850836,425292,121476,15180],
    ![69664,556808,1947064,3890600,4858840,3883544,1940008,553784,69160],
    ![(1759253/8),(14048059/8),(24538705/4),(97973389/8),(61120075/4),(97611013/8),(24357517/4),(13892755/8),(1733369/8)],
    ![(1014591/2),(8091249/2),14115219,(56283495/2),35066625,(55930191/2),13938567,(7939833/2),(989355/2)],
    ![(1810874185/2048),(3604320725/512),(12554464279/512),(24988289039/512),(62170816295/1024),(24749040995/512),(12315216235/512),(3501785849/512),(1742517601/2048)],
    ![(1215606893/1024),(2414455849/256),(8392494707/256),(16669891915/256),(41389746115/512),(16443009007/256),(8165611799/256),(2317220317/256),(1150783205/1024)],
    ![(2539002069/2048),(5030187057/512),(17440696971/512),(34556282595/512),(85589938395/1024),(33920472231/512),(16804886607/512),(4757696901/512),(2357341965/2048)],
    ![(258448967/256),(510475579/64),(1764644825/64),(3486167329/64),(8609905225/128),(3402673933/64),(1681151429/64),(474692695/64),(234593711/256)],
    ![(653566193/1024),(1286259037/256),(36297623954407/2097152),(35732114898511/1048576),(87957732510145/2097152),(17325279903161/524288),(34134517312969/2097152),(4804995429151/1048576),(1183996958287/2097152)],
    ![(158497527/512),(310619499/128),(8729812380597/1048576),(8560074275565/524288),(20992177872195/1048576),(4120103803179/262144),(8090089671003/1048576),(1135217826141/524288),(278911492845/1048576)],
    ![(115460209/1024),(225161597/256),(6298105059977/2097152),(6147774334625/1048576),(60048568106375/8388608),(46954998291145/8388608),(5741356848989/2097152),(6423814181977/8388608),(786836586251/8388608)],
    ![(7618759/256),(14771867/64),(410912207747/524288),(399012779915/262144),(3878457358175/2097152),(3019344168745/2097152),(367738146179/524288),(410075110057/2097152),(50094408371/2097152)],
    ![(10971093/2048),(21127281/512),(291941083785/2097152),(281753185953/1048576),(1361656779135/4194304),(1054776952515/4194304),(8187613758681/67108864),(9101115262209/268435456),(1109485002525/268435456)],
    ![(600173/1024),(1146409/256),(15717088181/1048576),(15056437997/524288),(72278130385/2097152),(55671187121/2097152),(430274137177/33554432),(477002049665/134217728),(58104578461/134217728)],
    ![(59977/2048),(113429/512),(1539765223/2097152),(1461192271/1048576),(13911964495/8388608),(10644658409/8388608),(40959330137/67108864),(45341454433/268435456),(177037598815/8589934592)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row07Lower_00 : Expr := (.add (.literal (128)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_00 :
    (certificate07Lower.rowExpression ⟨0,by decide⟩).check row07Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row07Lower_01 : Expr := (.add (.literal (2048)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_01 :
    (certificate07Lower.rowExpression ⟨1,by decide⟩).check row07Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row07Lower_02 : Expr := (.add (.literal (15216)) (.mul .y (.add (.literal (-36)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_02 :
    (certificate07Lower.rowExpression ⟨2,by decide⟩).check row07Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row07Lower_03 : Expr := (.add (.literal (69664)) (.mul .y (.add (.literal (-504)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_03 :
    (certificate07Lower.rowExpression ⟨3,by decide⟩).check row07Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row07Lower_04 : Expr := (.add (.literal ((1759253/8))) (.mul .y (.add (.literal ((-25965/8))) (.mul .y (.add (.literal ((81/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_04 :
    (certificate07Lower.rowExpression ⟨4,by decide⟩).check row07Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row07Lower_05 : Expr := (.add (.literal ((1014591/2))) (.mul .y (.add (.literal ((-25479/2))) (.mul .y (.add (.literal ((243/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_05 :
    (certificate07Lower.rowExpression ⟨5,by decide⟩).check row07Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row07Lower_06 : Expr := (.add (.literal ((1810874185/2048))) (.mul .y (.add (.literal ((-17427645/512))) (.mul .y (.add (.literal ((338499/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_06 :
    (certificate07Lower.rowExpression ⟨6,by decide⟩).check row07Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row07Lower_07 : Expr := (.add (.literal ((1215606893/1024))) (.mul .y (.add (.literal ((-16757937/256))) (.mul .y (.add (.literal ((552015/256))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_07 :
    (certificate07Lower.rowExpression ⟨7,by decide⟩).check row07Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row07Lower_08 : Expr := (.add (.literal ((2539002069/2048))) (.mul .y (.add (.literal ((-47817081/512))) (.mul .y (.add (.literal ((2402055/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_08 :
    (certificate07Lower.rowExpression ⟨8,by decide⟩).check row07Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row07Lower_09 : Expr := (.add (.literal ((258448967/256))) (.mul .y (.add (.literal ((-6422355/64))) (.mul .y (.add (.literal ((458541/64))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_09 :
    (certificate07Lower.rowExpression ⟨9,by decide⟩).check row07Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row07Lower_10 : Expr := (.add (.literal ((653566193/1024))) (.mul .y (.add (.literal ((-20873349/256))) (.mul .y (.add (.literal ((16485508071/2097152))) (.mul .y (.add (.literal ((295245/524288))) (.mul .y (.add (.literal ((295245/524288))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_10 :
    (certificate07Lower.rowExpression ⟨10,by decide⟩).check row07Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row07Lower_11 : Expr := (.add (.literal ((158497527/512))) (.mul .y (.add (.literal ((-6375555/128))) (.mul .y (.add (.literal ((6530018229/1048576))) (.mul .y (.add (.literal ((885735/262144))) (.mul .y (.add (.literal ((885735/262144))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_11 :
    (certificate07Lower.rowExpression ⟨11,by decide⟩).check row07Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row07Lower_12 : Expr := (.add (.literal ((115460209/1024))) (.mul .y (.add (.literal ((-5758821/256))) (.mul .y (.add (.literal ((7388666505/2097152))) (.mul .y (.add (.literal ((4428675/524288))) (.mul .y (.add (.literal ((68201595/8388608))) (.mul .y (.add (.literal ((-1594323/8388608))) (.mul .y (.add (.literal ((-531441/8388608))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_12 :
    (certificate07Lower.rowExpression ⟨12,by decide⟩).check row07Lower_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row07Lower_13 : Expr := (.add (.literal ((7618759/256))) (.mul .y (.add (.literal ((-465651/64))) (.mul .y (.add (.literal ((724382595/524288))) (.mul .y (.add (.literal ((1476225/131072))) (.mul .y (.add (.literal ((20962395/2097152))) (.mul .y (.add (.literal ((-1594323/2097152))) (.mul .y (.add (.literal ((-531441/2097152))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_13 :
    (certificate07Lower.rowExpression ⟨13,by decide⟩).check row07Lower_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row07Lower_14 : Expr := (.add (.literal ((10971093/2048))) (.mul .y (.add (.literal ((-814905/512))) (.mul .y (.add (.literal ((742861449/2097152))) (.mul .y (.add (.literal ((4428675/524288))) (.mul .y (.add (.literal ((27457785/4194304))) (.mul .y (.add (.literal ((-4782969/4194304))) (.mul .y (.add (.literal ((-20726199/67108864))) (.mul .y (.add (.literal ((4782969/268435456))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_14 :
    (certificate07Lower.rowExpression ⟨14,by decide⟩).check row07Lower_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row07Lower_15 : Expr := (.add (.literal ((600173/1024))) (.mul .y (.add (.literal ((-53937/256))) (.mul .y (.add (.literal ((55409589/1048576))) (.mul .y (.add (.literal ((885735/262144))) (.mul .y (.add (.literal ((4428675/2097152))) (.mul .y (.add (.literal ((-1594323/2097152))) (.mul .y (.add (.literal ((-3720087/33554432))) (.mul .y (.add (.literal ((4782969/134217728))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_15 :
    (certificate07Lower.rowExpression ⟨15,by decide⟩).check row07Lower_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row07Lower_16 : Expr := (.add (.literal ((59977/2048))) (.mul .y (.add (.literal ((-6525/512))) (.mul .y (.add (.literal ((7189479/2097152))) (.mul .y (.add (.literal ((295245/524288))) (.mul .y (.add (.literal ((2066715/8388608))) (.mul .y (.add (.literal ((-1594323/8388608))) (.mul .y (.add (.literal ((531441/67108864))) (.mul .y (.add (.literal ((4782969/268435456))) (.mul .y (.add (.literal ((-43046721/8589934592))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked07Lower_16 :
    (certificate07Lower.rowExpression ⟨16,by decide⟩).check row07Lower_16=true := by kernel_decide

def rows07Lower : Fin (certificate07Lower.degree0+1) → Expr := ![row07Lower_00,row07Lower_01,row07Lower_02,row07Lower_03,row07Lower_04,row07Lower_05,row07Lower_06,row07Lower_07,row07Lower_08,row07Lower_09,row07Lower_10,row07Lower_11,row07Lower_12,row07Lower_13,row07Lower_14,row07Lower_15,row07Lower_16]

theorem rowsChecked07Lower : ∀ i, (certificate07Lower.rowExpression i).check (rows07Lower i)=true := by
  intro i
  fin_cases i
  · exact checked07Lower_00
  · exact checked07Lower_01
  · exact checked07Lower_02
  · exact checked07Lower_03
  · exact checked07Lower_04
  · exact checked07Lower_05
  · exact checked07Lower_06
  · exact checked07Lower_07
  · exact checked07Lower_08
  · exact checked07Lower_09
  · exact checked07Lower_10
  · exact checked07Lower_11
  · exact checked07Lower_12
  · exact checked07Lower_13
  · exact checked07Lower_14
  · exact checked07Lower_15
  · exact checked07Lower_16


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity07Lower : slackRowsIdentityCheck 7 (-1) certificate07Lower rows07Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted07Lower : certificate07Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive07Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 7 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate07Lower rows07Lower rowsChecked07Lower identity07Lower accepted07Lower hz hz1 ha

end polyak.Certificates.P1Slacks
