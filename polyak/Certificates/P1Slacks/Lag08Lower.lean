import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 8, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate08Lower : Certificate where
  degree0 := 18
  degree1 := 9
  coefficient := ![
    ![256,2304,9216,21504,32256,32256,21504,9216,2304,256],
    ![4608,41472,165888,387072,580608,580608,387072,165888,41472,4608],
    ![38844,349524,1397808,3260880,4890312,4889304,3258864,1396368,349020,38772],
    ![203712,1832256,7324416,17079552,25603200,25587072,17047296,7301376,1824192,202560],
    ![(11913867/16),(107087697/16),26737668,62308008,(746738055/8),(745780581/8),(124137279/2),(53133381/2),(106130223/16),(11777085/16)],
    ![(16111053/8),(144684855/8),72185400,168066864,(1006210737/4),(1004024259/4),166973625,71404515,(142498377/8),(15798699/8)],
    ![(2137662057/512),(9587578653/256),(2388948723/16),(44445930543/128),(132896090565/256),(8278501581/16),(22002932637/64),(18797257449/128),(18735092037/512),(1037397795/256)],
    ![(867994875/128),(3887483895/64),(967276377/4),(17970594957/32),(53657697807/64),(3337825995/4),(8859056535/16),(7557866811/32),(7522485903/128),(415963017/64)],
    ![(71621602497/8192),(1280881525941/16384),(2545305262677/8192),(5901010085313/8192),(8795010807387/8192),(4369527728811/4096),(5789099385783/8192),(2465369048727/8192),(76557886011/1024),(135249583599/16384)],
    ![(36901346309/4096),(658600631433/8192),(1306104880041/4096),(3022038410181/4096),(4495276025415/4096),(2229011155287/2048),(2947530980499/4096),(1252885287411/4096),(38834182287/512),(68480733355/8192)],
    ![(60883801533/8192),(17344658696121/262144),(137265803221707/524288),(316871053201071/524288),(470279249954019/524288),(465348322618947/524288),(307009199121417/524288),(130221622579797/524288),(32223854610441/524288),(3544354413639/524288)],
    ![(5010100767/1024),(1423339770969/32768),(11233863621963/65536),(25864320493359/65536),(38287388662371/65536),(37791247329603/65536),(24872038418313/65536),(10525091554773/65536),(2598609761289/65536),(285207993351/65536)],
    ![(10439469033/4096),(1478169225351/65536),(11630452044141/131072),(3417214018711905/16777216),(5043894814225575/16777216),(620583079198617/2097152),(1629377074924119/8388608),(1375512942653361/16777216),(338796966797307/16777216),(18550470518139/8388608)],
    ![(2119907583/2048),(299066856183/32768),(2344773563181/65536),(686590275291939/8388608),(1010136916289781/8388608),(123901719643179/1048576),(324372188036997/4194304),(273098824137747/8388608),(67100154650865/8388608),(3665816401905/4194304)],
    ![(1311131457/4096),(368378653419/131072),(2876534858817/262144),(419532859640943/16777216),(615002675296905/16777216),(19246574073418947/536870912),(6279026743292661/268435456),(329493382147683/33554432),(646079722224039/268435456),(140895893027205/536870912)],
    ![(74350311/1024),(20788221519/32768),(161577882765/65536),(23463395639973/4194304),(34257733287939/4194304),(1068211029711555/134217728),(347379356436021/67108864),(18179096218767/8388608),(35567207890119/67108864),(7743556699653/134217728)],
    ![(93003885/8192),(6464308707/65536),(49977287901/131072),(14443538996655/16777216),(20995027634889/16777216),(326068577000649/268435456),(105696766979343/134217728),(2824980977158839/8589934592),(172421232203403/2147483648),(75008067841557/8589934592)],
    ![(4461957/4096),(308080845/32768),(2367150363/65536),(680294282787/8388608),(984089520117/8388608),(15223140191043/134217728),(4919949347877/67108864),(131242330480311/4294967296),(8003504335275/1073741824),(3482615221461/4294967296)],
    ![(394289/8192),(108035577/262144),(824062923/524288),(58831590081/16777216),(84665304711/16777216),(2609501035203/536870912),(841394966709/268435456),(11212707280311/8589934592),(684178631667/2147483648),(4772717566361/137438953472)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row08Lower_00 : Expr := (.add (.literal (256)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_00 :
    (certificate08Lower.rowExpression ⟨0,by decide⟩).check row08Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row08Lower_01 : Expr := (.add (.literal (4608)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_01 :
    (certificate08Lower.rowExpression ⟨1,by decide⟩).check row08Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row08Lower_02 : Expr := (.add (.literal (38844)) (.mul .y (.add (.literal (-72)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_02 :
    (certificate08Lower.rowExpression ⟨2,by decide⟩).check row08Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row08Lower_03 : Expr := (.add (.literal (203712)) (.mul .y (.add (.literal (-1152)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_03 :
    (certificate08Lower.rowExpression ⟨3,by decide⟩).check row08Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row08Lower_04 : Expr := (.add (.literal ((11913867/16))) (.mul .y (.add (.literal ((-68553/8))) (.mul .y (.add (.literal ((81/4))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_04 :
    (certificate08Lower.rowExpression ⟨4,by decide⟩).check row08Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row08Lower_05 : Expr := (.add (.literal ((16111053/8))) (.mul .y (.add (.literal ((-157311/4))) (.mul .y (.add (.literal ((567/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_05 :
    (certificate08Lower.rowExpression ⟨5,by decide⟩).check row08Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row08Lower_06 : Expr := (.add (.literal ((2137662057/512))) (.mul .y (.add (.literal ((-63801207/512))) (.mul .y (.add (.literal ((233685/128))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_06 :
    (certificate08Lower.rowExpression ⟨6,by decide⟩).check row08Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row08Lower_07 : Expr := (.add (.literal ((867994875/128))) (.mul .y (.add (.literal ((-36986085/128))) (.mul .y (.add (.literal ((229311/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_07 :
    (certificate08Lower.rowExpression ⟨7,by decide⟩).check row08Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row08Lower_08 : Expr := (.add (.literal ((71621602497/8192))) (.mul .y (.add (.literal ((-8307319005/16384))) (.mul .y (.add (.literal ((156848805/8192))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_08 :
    (certificate08Lower.rowExpression ⟨8,by decide⟩).check row08Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row08Lower_09 : Expr := (.add (.literal ((36901346309/4096))) (.mul .y (.add (.literal ((-5623602129/8192))) (.mul .y (.add (.literal ((150821433/4096))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_09 :
    (certificate08Lower.rowExpression ⟨9,by decide⟩).check row08Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row08Lower_10 : Expr := (.add (.literal ((60883801533/8192))) (.mul .y (.add (.literal ((-189876145383/262144))) (.mul .y (.add (.literal ((27542815803/524288))) (.mul .y (.add (.literal ((295245/262144))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_10 :
    (certificate08Lower.rowExpression ⟨10,by decide⟩).check row08Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row08Lower_11 : Expr := (.add (.literal ((5010100767/1024))) (.mul .y (.add (.literal ((-19569249927/32768))) (.mul .y (.add (.literal ((3699453627/65536))) (.mul .y (.add (.literal ((295245/32768))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_11 :
    (certificate08Lower.rowExpression ⟨11,by decide⟩).check row08Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row08Lower_12 : Expr := (.add (.literal ((10439469033/4096))) (.mul .y (.add (.literal ((-25114315401/65536))) (.mul .y (.add (.literal ((6012764541/131072))) (.mul .y (.add (.literal ((521107425/16777216))) (.mul .y (.add (.literal ((-7971615/16777216))) (.mul .y (.add (.literal ((-1594323/4194304))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_12 :
    (certificate08Lower.rowExpression ⟨12,by decide⟩).check row08Lower_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row08Lower_13 : Expr := (.add (.literal ((2119907583/2048))) (.mul .y (.add (.literal ((-6199835769/32768))) (.mul .y (.add (.literal ((1837399869/65536))) (.mul .y (.add (.literal ((505164195/8388608))) (.mul .y (.add (.literal ((-23914845/8388608))) (.mul .y (.add (.literal ((-4782969/2097152))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_13 :
    (certificate08Lower.rowExpression ⟨13,by decide⟩).check row08Lower_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row08Lower_14 : Expr := (.add (.literal ((1311131457/4096))) (.mul .y (.add (.literal ((-9227206197/131072))) (.mul .y (.add (.literal ((3323281041/262144))) (.mul .y (.add (.literal ((1203123375/16777216))) (.mul .y (.add (.literal ((-119574225/16777216))) (.mul .y (.add (.literal ((-2931959997/536870912))) (.mul .y (.add (.literal ((33480783/268435456))) (.mul .y (.add (.literal ((4782969/134217728))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_14 :
    (certificate08Lower.rowExpression ⟨14,by decide⟩).check row08Lower_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row08Lower_15 : Expr := (.add (.literal ((74350311/1024))) (.mul .y (.add (.literal ((-624668049/32768))) (.mul .y (.add (.literal ((269455005/65536))) (.mul .y (.add (.literal ((224681445/4194304))) (.mul .y (.add (.literal ((-39858075/4194304))) (.mul .y (.add (.literal ((-891226557/134217728))) (.mul .y (.add (.literal ((33480783/67108864))) (.mul .y (.add (.literal ((4782969/33554432))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_15 :
    (certificate08Lower.rowExpression ⟨15,by decide⟩).check row08Lower_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row08Lower_16 : Expr := (.add (.literal ((93003885/8192))) (.mul .y (.add (.literal ((-231971013/65536))) (.mul .y (.add (.literal ((118586349/131072))) (.mul .y (.add (.literal ((409504815/16777216))) (.mul .y (.add (.literal ((-119574225/16777216))) (.mul .y (.add (.literal ((-1143129591/268435456))) (.mul .y (.add (.literal ((100442349/134217728))) (.mul .y (.add (.literal ((1449239607/8589934592))) (.mul .y (.add (.literal ((-43046721/4294967296))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_16 :
    (certificate08Lower.rowExpression ⟨16,by decide⟩).check row08Lower_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row08Lower_17 : Expr := (.add (.literal ((4461957/4096))) (.mul .y (.add (.literal ((-13180059/32768))) (.mul .y (.add (.literal ((7944075/65536))) (.mul .y (.add (.literal ((51667875/8388608))) (.mul .y (.add (.literal ((-23914845/8388608))) (.mul .y (.add (.literal ((-176969853/134217728))) (.mul .y (.add (.literal ((33480783/67108864))) (.mul .y (.add (.literal ((224799543/4294967296))) (.mul .y (.add (.literal ((-43046721/2147483648))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_17 :
    (certificate08Lower.rowExpression ⟨17,by decide⟩).check row08Lower_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row08Lower_18 : Expr := (.add (.literal ((394289/8192))) (.mul .y (.add (.literal ((-5519655/262144))) (.mul .y (.add (.literal ((3935547/524288))) (.mul .y (.add (.literal ((10924065/16777216))) (.mul .y (.add (.literal ((-7971615/16777216))) (.mul .y (.add (.literal ((-74933181/536870912))) (.mul .y (.add (.literal ((33480783/268435456))) (.mul .y (.add (.literal ((-81310473/8589934592))) (.mul .y (.add (.literal ((-43046721/4294967296))) (.mul .y (.add (.literal ((387420489/137438953472))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked08Lower_18 :
    (certificate08Lower.rowExpression ⟨18,by decide⟩).check row08Lower_18=true := by kernel_decide

def rows08Lower : Fin (certificate08Lower.degree0+1) → Expr := ![row08Lower_00,row08Lower_01,row08Lower_02,row08Lower_03,row08Lower_04,row08Lower_05,row08Lower_06,row08Lower_07,row08Lower_08,row08Lower_09,row08Lower_10,row08Lower_11,row08Lower_12,row08Lower_13,row08Lower_14,row08Lower_15,row08Lower_16,row08Lower_17,row08Lower_18]

theorem rowsChecked08Lower : ∀ i, (certificate08Lower.rowExpression i).check (rows08Lower i)=true := by
  intro i
  fin_cases i
  · exact checked08Lower_00
  · exact checked08Lower_01
  · exact checked08Lower_02
  · exact checked08Lower_03
  · exact checked08Lower_04
  · exact checked08Lower_05
  · exact checked08Lower_06
  · exact checked08Lower_07
  · exact checked08Lower_08
  · exact checked08Lower_09
  · exact checked08Lower_10
  · exact checked08Lower_11
  · exact checked08Lower_12
  · exact checked08Lower_13
  · exact checked08Lower_14
  · exact checked08Lower_15
  · exact checked08Lower_16
  · exact checked08Lower_17
  · exact checked08Lower_18


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity08Lower : slackRowsIdentityCheck 8 (-1) certificate08Lower rows08Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted08Lower : certificate08Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive08Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 8 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate08Lower rows08Lower rowsChecked08Lower identity08Lower accepted08Lower hz hz1 ha

end polyak.Certificates.P1Slacks
