import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 9, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate09Upper : Certificate where
  degree0 := 16
  degree1 := 8
  coefficient := ![
    ![128,1024,3584,7168,8960,7168,3584,1024,128],
    ![2048,16384,57344,114688,143360,114688,57344,16384,2048],
    ![15216,121764,426228,852420,1065300,851916,425724,121548,15180],
    ![69664,557816,1953112,3905720,4879000,3898664,1946056,554792,69160],
    ![(1759253/8),(14099989/8),(24694495/4),(98752339/8),(61639375/4),(98389963/8),(24513307/4),(13944685/8),(1733369/8)],
    ![(1014591/2),(8142207/2),14268093,(57047865/2),35576205,(56694561/2),14091441,(7990791/2),(989355/2)],
    ![(1810874185/2048),(3639176015/512),(12763596019/512),(25511118389/512),(63565027895/1024),(25271870345/512),(12524347975/512),(3536641139/512),(1742517601/2048)],
    ![(1215606893/1024),(2447971723/256),(8593589951/256),(17172630025/256),(42730381075/512),(16945747117/256),(8366707043/256),(2350736191/256),(1150783205/1024)],
    ![(2539002069/2048),(5125821219/512),(18014501943/512),(35990795025/512),(89415304875/1024),(35354984661/512),(17378691579/512),(4853331063/512),(2357341965/2048)],
    ![(258448967/256),(523320289/64),(1841713085/64),(3678837979/64),(9123693625/128),(3595344583/64),(1758219689/64),(487537405/64),(234593711/256)],
    ![(653566193/1024),(1328005735/256),(38349557654503/2097152),(38297030842651/1048576),(94797502062625/2097152),(18607734922781/524288),(36186441565225/2097152),(4975988723179/1048576),(1183996958287/2097152)],
    ![(158497527/512),(323370609/128),(9356554939317/1048576),(9343498931025/524288),(23081291391075/1048576),(4511807273559/262144),(8716803886203/1048576),(1187442829761/524288),(278911492845/1048576)],
    ![(115460209/1024),(236679239/256),(6864220199561/2097152),(6855400544405/1048576),(67596203097095/8388608),(52615302570031/8388608),(394208241581/131072),(6801085746079/8388608),(786836586251/8388608)],
    ![(7618759/256),(15703169/64),(456687563651/524288),(456226069895/262144),(4488606480095/2097152),(3476817481231/2097152),(206733928603/262144),(440547963439/2097152),(50094408371/2097152)],
    ![(10971093/2048),(22757091/512),(331995294345/2097152),(331803234453/1048576),(1628401414335/4194304),(1254632418453/4194304),(9465119643417/67108864),(9951672778383/268435456),(1109485002525/268435456)],
    ![(600173/1024),(1254283/256),(18368199605/1048576),(18366784337/524288),(89895519505/2097152),(68844902327/2097152),(514304746777/33554432),(532846608143/134217728),(58104578461/134217728)],
    ![(59977/2048),(126479/512),(1860482023/2097152),(1860907291/1048576),(18150397135/8388608),(13798328015/8388608),(50970955193/67108864),(51973552687/268435456),(177037598815/8589934592)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row09Upper_00 : Expr := (.add (.literal (128)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_00 :
    (certificate09Upper.rowExpression ⟨0,by decide⟩).check row09Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row09Upper_01 : Expr := (.add (.literal (2048)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_01 :
    (certificate09Upper.rowExpression ⟨1,by decide⟩).check row09Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row09Upper_02 : Expr := (.add (.literal (15216)) (.mul .y (.add (.literal (36)) (.mul .y (.add (.literal (-72)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_02 :
    (certificate09Upper.rowExpression ⟨2,by decide⟩).check row09Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row09Upper_03 : Expr := (.add (.literal (69664)) (.mul .y (.add (.literal (504)) (.mul .y (.add (.literal (-1008)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_03 :
    (certificate09Upper.rowExpression ⟨3,by decide⟩).check row09Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row09Upper_04 : Expr := (.add (.literal ((1759253/8))) (.mul .y (.add (.literal ((25965/8))) (.mul .y (.add (.literal ((-51849/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_04 :
    (certificate09Upper.rowExpression ⟨4,by decide⟩).check row09Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row09Upper_05 : Expr := (.add (.literal ((1014591/2))) (.mul .y (.add (.literal ((25479/2))) (.mul .y (.add (.literal ((-50715/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_05 :
    (certificate09Upper.rowExpression ⟨5,by decide⟩).check row09Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row09Upper_06 : Expr := (.add (.literal ((1810874185/2048))) (.mul .y (.add (.literal ((17427645/512))) (.mul .y (.add (.literal ((-34516791/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_06 :
    (certificate09Upper.rowExpression ⟨6,by decide⟩).check row09Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row09Upper_07 : Expr := (.add (.literal ((1215606893/1024))) (.mul .y (.add (.literal ((16757937/256))) (.mul .y (.add (.literal ((-32963859/256))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_07 :
    (certificate09Upper.rowExpression ⟨7,by decide⟩).check row09Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row09Upper_08 : Expr := (.add (.literal ((2539002069/2048))) (.mul .y (.add (.literal ((47817081/512))) (.mul .y (.add (.literal ((-93232107/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_08 :
    (certificate09Upper.rowExpression ⟨8,by decide⟩).check row09Upper_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row09Upper_09 : Expr := (.add (.literal ((258448967/256))) (.mul .y (.add (.literal ((6422355/64))) (.mul .y (.add (.literal ((-12386169/64))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_09 :
    (certificate09Upper.rowExpression ⟨9,by decide⟩).check row09Upper_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row09Upper_10 : Expr := (.add (.literal ((653566193/1024))) (.mul .y (.add (.literal ((20873349/256))) (.mul .y (.add (.literal ((-325503441945/2097152))) (.mul .y (.add (.literal ((-295245/524288))) (.mul .y (.add (.literal ((885735/524288))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_10 :
    (certificate09Upper.rowExpression ⟨10,by decide⟩).check row09Upper_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row09Upper_11 : Expr := (.add (.literal ((158497527/512))) (.mul .y (.add (.literal ((6375555/128))) (.mul .y (.add (.literal ((-97927074891/1048576))) (.mul .y (.add (.literal ((-885735/262144))) (.mul .y (.add (.literal ((2657205/262144))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_11 :
    (certificate09Upper.rowExpression ⟨11,by decide⟩).check row09Upper_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row09Upper_12 : Expr := (.add (.literal ((115460209/1024))) (.mul .y (.add (.literal ((5758821/256))) (.mul .y (.add (.literal ((-86963856759/2097152))) (.mul .y (.add (.literal ((-4428675/524288))) (.mul .y (.add (.literal ((209919195/8388608))) (.mul .y (.add (.literal ((1594323/8388608))) (.mul .y (.add (.literal ((-3720087/8388608))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_12 :
    (certificate09Upper.rowExpression ⟨12,by decide⟩).check row09Upper_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row09Upper_13 : Expr := (.add (.literal ((7618759/256))) (.mul .y (.add (.literal ((465651/64))) (.mul .y (.add (.literal ((-6904843389/524288))) (.mul .y (.add (.literal ((-1476225/131072))) (.mul .y (.add (.literal ((68201595/2097152))) (.mul .y (.add (.literal ((1594323/2097152))) (.mul .y (.add (.literal ((-3720087/2097152))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_13 :
    (certificate09Upper.rowExpression ⟨13,by decide⟩).check row09Upper_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row09Upper_14 : Expr := (.add (.literal ((10971093/2048))) (.mul .y (.add (.literal ((814905/512))) (.mul .y (.add (.literal ((-5932840311/2097152))) (.mul .y (.add (.literal ((-4428675/524288))) (.mul .y (.add (.literal ((98316585/4194304))) (.mul .y (.add (.literal ((4782969/4194304))) (.mul .y (.add (.literal ((-173781207/67108864))) (.mul .y (.add (.literal ((-4782969/268435456))) (.mul .y (.add (.literal ((4782969/134217728))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_14 :
    (certificate09Upper.rowExpression ⟨14,by decide⟩).check row09Upper_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row09Upper_15 : Expr := (.add (.literal ((600173/1024))) (.mul .y (.add (.literal ((53937/256))) (.mul .y (.add (.literal ((-386442315/1048576))) (.mul .y (.add (.literal ((-885735/262144))) (.mul .y (.add (.literal ((18600435/2097152))) (.mul .y (.add (.literal ((1594323/2097152))) (.mul .y (.add (.literal ((-54738423/33554432))) (.mul .y (.add (.literal ((-4782969/134217728))) (.mul .y (.add (.literal ((4782969/67108864))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_15 :
    (certificate09Upper.rowExpression ⟨15,by decide⟩).check row09Upper_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row09Upper_16 : Expr := (.add (.literal ((59977/2048))) (.mul .y (.add (.literal ((6525/512))) (.mul .y (.add (.literal ((-46263321/2097152))) (.mul .y (.add (.literal ((-295245/524288))) (.mul .y (.add (.literal ((11514555/8388608))) (.mul .y (.add (.literal ((1594323/8388608))) (.mul .y (.add (.literal ((-24977727/67108864))) (.mul .y (.add (.literal ((-4782969/268435456))) (.mul .y (.add (.literal ((263063295/8589934592))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Upper_16 :
    (certificate09Upper.rowExpression ⟨16,by decide⟩).check row09Upper_16=true := by kernel_decide

def rows09Upper : Fin (certificate09Upper.degree0+1) → Expr := ![row09Upper_00,row09Upper_01,row09Upper_02,row09Upper_03,row09Upper_04,row09Upper_05,row09Upper_06,row09Upper_07,row09Upper_08,row09Upper_09,row09Upper_10,row09Upper_11,row09Upper_12,row09Upper_13,row09Upper_14,row09Upper_15,row09Upper_16]

theorem rowsChecked09Upper : ∀ i, (certificate09Upper.rowExpression i).check (rows09Upper i)=true := by
  intro i
  fin_cases i
  · exact checked09Upper_00
  · exact checked09Upper_01
  · exact checked09Upper_02
  · exact checked09Upper_03
  · exact checked09Upper_04
  · exact checked09Upper_05
  · exact checked09Upper_06
  · exact checked09Upper_07
  · exact checked09Upper_08
  · exact checked09Upper_09
  · exact checked09Upper_10
  · exact checked09Upper_11
  · exact checked09Upper_12
  · exact checked09Upper_13
  · exact checked09Upper_14
  · exact checked09Upper_15
  · exact checked09Upper_16


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity09Upper : slackRowsIdentityCheck 9 (1) certificate09Upper rows09Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted09Upper : certificate09Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive09Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 9 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate09Upper rows09Upper rowsChecked09Upper identity09Upper accepted09Upper hz hz1 ha

end polyak.Certificates.P1Slacks
