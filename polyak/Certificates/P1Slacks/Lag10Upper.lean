import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 10, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate10Upper : Certificate where
  degree0 := 18
  degree1 := 9
  coefficient := ![
    ![256,2304,9216,21504,32256,32256,21504,9216,2304,256],
    ![4608,41472,165888,387072,580608,580608,387072,165888,41472,4608],
    ![38844,349668,1398816,3263904,4895352,4894344,3261888,1397376,349164,38772],
    ![203712,1834560,7340544,17127936,25683840,25667712,17095680,7317504,1826496,202560],
    ![(11913867/16),(107361909/16),(107430543/4),(250671645/4),(751536765/8),(750579291/8),(249714171/4),(106746633/4),(106404435/16),(11777085/16)],
    ![(16111053/8),(145314099/8),(145471977/2),(339437259/2),(1017222507/4),(1015036029/4),(337250781/2),(143910207/2),(143127621/8),(15798699/8)],
    ![(2137662057/512),(2412844965/64),(38669788017/256),(90231686433/256),(67564566405/128),(134689067541/256),(89351555895/256),(38041123347/256),(18862694451/512),(1037397795/256)],
    ![(867994875/128),(981117495/16),(15735324627/64),(36717897699/64),(27476105391/32),(54699728895/64),(36212933925/64),(15374636217/64),(7596458073/128),(415963017/64)],
    ![(286486416549/32768),(1297496163951/16384),(2603456449785/8192),(3037731800355/4096),(18171533256219/16384),(9029811255381/8192),(5963552855253/8192),(1261760101515/4096),(2483081582445/32768),(135249583599/16384)],
    ![(147605418041/16384),(669847835691/8192),(1345469865309/4096),(1570066568175/2048),(9384200755335/8192),(4654846548009/4096),(3065625477033/4096),(646125054327/2048),(1265188012065/16384),(68480733355/8192)],
    ![(243535501377/32768),(70897644478989/1048576),(285164408584449/1048576),(665640244742787/1048576),(993721837454613/1048576),(983859844609809/1048576),(645916261415139/1048576),(271075852438929/1048576),(65966651599527/1048576),(3544354413639/524288)],
    ![(20040501483/4096),(5849913614733/131072),(23563519599105/131072),(55015926329475/131072),(82053506841237/131072),(81061174180881/131072),(53031263370723/131072),(22145906574225/131072),(5353750827495/131072),(285207993351/65536)],
    ![(41758565037/16384),(6113595144699/262144),(24667014895047/262144),(3687165954089505/16777216),(5493795616832805/16777216),(21150597509721/65536),(1764340833444849/8388608),(1465487343889641/16777216),(351650283161337/16777216),(18550470518139/8388608)],
    ![(8480043675/8192),(1245869830971/131072),(5036570525511/131072),(753205329320931/8388608),(1121149532630511/8388608),(8611077702303/65536),(357671551999635/4194304),(295297402342203/8388608),(70271264558187/8388608),(3665816401905/4194304)],
    ![(5245214733/16384),(1547350863687/524288),(6269264874531/524288),(469063874326095/16777216),(697531531862475/16777216),(21886992773605827/536870912),(7071039364543767/268435456),(724980648222999/67108864),(683787469345065/268435456),(140895893027205/536870912)],
    ![(297499659/4096),(88153950555/131072),(358066770183/131072),(26811236713221/4194304),(39833873966169/4194304),(1246567709764035/134217728),(400869157627863/67108864),(40814690063535/16777216),(38113441748361/67108864),(7743556699653/134217728)],
    ![(372310785/32768),(27716723019/262144),(112896591399/262144),(16922586121839/16777216),(25120839403179/16777216),(392016857037129/268435456),(125468467472277/134217728),(3246626630577591/8589934592),(46869608251467/536870912),(75008067841557/8589934592)],
    ![(17880633/16384),(1338295293/131072),(5467574817/131072),(820385867619/8388608),(1216853500527/8388608),(18939850745283/134217728),(6033706594407/67108864),(154994155577271/4294967296),(2212999040259/268435456),(3482615221461/4294967296)],
    ![(1583717/32768),(476830989/1048576),(1953886977/1048576),(73357378833/16777216),(108718035381/16777216),(3376190721987/536870912),(1071045261399/268435456),(13663097183799/8589934592),(192955154769/536870912),(4772717566361/137438953472)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row10Upper_00 : Expr := (.add (.literal (256)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_00 :
    (certificate10Upper.rowExpression ⟨0,by decide⟩).check row10Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row10Upper_01 : Expr := (.add (.literal (4608)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_01 :
    (certificate10Upper.rowExpression ⟨1,by decide⟩).check row10Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row10Upper_02 : Expr := (.add (.literal (38844)) (.mul .y (.add (.literal (72)) (.mul .y (.add (.literal (-144)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_02 :
    (certificate10Upper.rowExpression ⟨2,by decide⟩).check row10Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row10Upper_03 : Expr := (.add (.literal (203712)) (.mul .y (.add (.literal (1152)) (.mul .y (.add (.literal (-2304)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_03 :
    (certificate10Upper.rowExpression ⟨3,by decide⟩).check row10Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row10Upper_04 : Expr := (.add (.literal ((11913867/16))) (.mul .y (.add (.literal ((68553/8))) (.mul .y (.add (.literal (-17118)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_04 :
    (certificate10Upper.rowExpression ⟨4,by decide⟩).check row10Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row10Upper_05 : Expr := (.add (.literal ((16111053/8))) (.mul .y (.add (.literal ((157311/4))) (.mul .y (.add (.literal (-78372)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_05 :
    (certificate10Upper.rowExpression ⟨5,by decide⟩).check row10Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row10Upper_06 : Expr := (.add (.literal ((2137662057/512))) (.mul .y (.add (.literal ((63801207/512))) (.mul .y (.add (.literal ((-63333837/256))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_06 :
    (certificate10Upper.rowExpression ⟨6,by decide⟩).check row10Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row10Upper_07 : Expr := (.add (.literal ((867994875/128))) (.mul .y (.add (.literal ((36986085/128))) (.mul .y (.add (.literal ((-36527463/64))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_07 :
    (certificate10Upper.rowExpression ⟨7,by decide⟩).check row10Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row10Upper_08 : Expr := (.add (.literal ((286486416549/32768))) (.mul .y (.add (.literal ((16614578961/32768))) (.mul .y (.add (.literal ((-4075228539/4096))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_08 :
    (certificate10Upper.rowExpression ⟨8,by decide⟩).check row10Upper_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row10Upper_09 : Expr := (.add (.literal ((147605418041/16384))) (.mul .y (.add (.literal ((11246909013/16384))) (.mul .y (.add (.literal ((-2736357543/2048))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_09 :
    (certificate10Upper.rowExpression ⟨9,by decide⟩).check row10Upper_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row10Upper_10 : Expr := (.add (.literal ((243535501377/32768))) (.mul .y (.add (.literal ((759420082413/1048576))) (.mul .y (.add (.literal ((-1463849661159/1048576))) (.mul .y (.add (.literal ((295245/131072))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_10 :
    (certificate10Upper.rowExpression ⟨10,by decide⟩).check row10Upper_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row10Upper_11 : Expr := (.add (.literal ((20040501483/4096))) (.mul .y (.add (.literal ((78249187629/131072))) (.mul .y (.add (.literal ((-149131610343/131072))) (.mul .y (.add (.literal ((295245/16384))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_11 :
    (certificate10Upper.rowExpression ⟨11,by decide⟩).check row10Upper_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row10Upper_12 : Expr := (.add (.literal ((41758565037/16384))) (.mul .y (.add (.literal ((100361779371/262144))) (.mul .y (.add (.literal ((-188812801233/262144))) (.mul .y (.add (.literal ((1050186465/16777216))) (.mul .y (.add (.literal ((7971615/16777216))) (.mul .y (.add (.literal ((-11160261/8388608))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_12 :
    (certificate10Upper.rowExpression ⟨12,by decide⟩).check row10Upper_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row10Upper_13 : Expr := (.add (.literal ((8480043675/8192))) (.mul .y (.add (.literal ((24743541771/131072))) (.mul .y (.add (.literal ((-45882965457/131072))) (.mul .y (.add (.literal ((1034243235/8388608))) (.mul .y (.add (.literal ((23914845/8388608))) (.mul .y (.add (.literal ((-33480783/4194304))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_13 :
    (certificate10Upper.rowExpression ⟨13,by decide⟩).check row10Upper_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row10Upper_14 : Expr := (.add (.literal ((5245214733/16384))) (.mul .y (.add (.literal ((36729020583/524288))) (.mul .y (.add (.literal ((-67054662549/524288))) (.mul .y (.add (.literal ((2525820975/16777216))) (.mul .y (.add (.literal ((119574225/16777216))) (.mul .y (.add (.literal ((-10584710397/536870912))) (.mul .y (.add (.literal ((-33480783/268435456))) (.mul .y (.add (.literal ((4782969/16777216))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_14 :
    (certificate10Upper.rowExpression ⟨14,by decide⟩).check row10Upper_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row10Upper_15 : Expr := (.add (.literal ((297499659/4096))) (.mul .y (.add (.literal ((2474048763/131072))) (.mul .y (.add (.literal ((-4445227089/131072))) (.mul .y (.add (.literal ((489220965/4194304))) (.mul .y (.add (.literal ((39858075/4194304))) (.mul .y (.add (.literal ((-3442143357/134217728))) (.mul .y (.add (.literal ((-33480783/67108864))) (.mul .y (.add (.literal ((4782969/4194304))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_15 :
    (certificate10Upper.rowExpression ⟨15,by decide⟩).check row10Upper_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row10Upper_16 : Expr := (.add (.literal ((372310785/32768))) (.mul .y (.add (.literal ((910346499/262144))) (.mul .y (.add (.literal ((-1611686673/262144))) (.mul .y (.add (.literal ((938583855/16777216))) (.mul .y (.add (.literal ((119574225/16777216))) (.mul .y (.add (.literal ((-4969504791/268435456))) (.mul .y (.add (.literal ((-100442349/134217728))) (.mul .y (.add (.literal ((14305860279/8589934592))) (.mul .y (.add (.literal ((43046721/4294967296))) (.mul .y (.add (.literal ((-43046721/2147483648))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_16 :
    (certificate10Upper.rowExpression ⟨16,by decide⟩).check row10Upper_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row10Upper_17 : Expr := (.add (.literal ((17880633/16384))) (.mul .y (.add (.literal ((50889717/131072))) (.mul .y (.add (.literal ((-89165223/131072))) (.mul .y (.add (.literal ((127250595/8388608))) (.mul .y (.add (.literal ((23914845/8388608))) (.mul .y (.add (.literal ((-942244893/134217728))) (.mul .y (.add (.literal ((-33480783/67108864))) (.mul .y (.add (.literal ((4510339767/4294967296))) (.mul .y (.add (.literal ((43046721/2147483648))) (.mul .y (.add (.literal ((-43046721/1073741824))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_17 :
    (certificate10Upper.rowExpression ⟨17,by decide⟩).check row10Upper_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row10Upper_18 : Expr := (.add (.literal ((1583717/32768))) (.mul .y (.add (.literal ((20720493/1048576))) (.mul .y (.add (.literal ((-36318951/1048576))) (.mul .y (.add (.literal ((29819745/16777216))) (.mul .y (.add (.literal ((7971615/16777216))) (.mul .y (.add (.literal ((-585116541/536870912))) (.mul .y (.add (.literal ((-33480783/268435456))) (.mul .y (.add (.literal ((2061459639/8589934592))) (.mul .y (.add (.literal ((43046721/4294967296))) (.mul .y (.add (.literal ((-2367569655/137438953472))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Upper_18 :
    (certificate10Upper.rowExpression ⟨18,by decide⟩).check row10Upper_18=true := by kernel_decide

def rows10Upper : Fin (certificate10Upper.degree0+1) → Expr := ![row10Upper_00,row10Upper_01,row10Upper_02,row10Upper_03,row10Upper_04,row10Upper_05,row10Upper_06,row10Upper_07,row10Upper_08,row10Upper_09,row10Upper_10,row10Upper_11,row10Upper_12,row10Upper_13,row10Upper_14,row10Upper_15,row10Upper_16,row10Upper_17,row10Upper_18]

theorem rowsChecked10Upper : ∀ i, (certificate10Upper.rowExpression i).check (rows10Upper i)=true := by
  intro i
  fin_cases i
  · exact checked10Upper_00
  · exact checked10Upper_01
  · exact checked10Upper_02
  · exact checked10Upper_03
  · exact checked10Upper_04
  · exact checked10Upper_05
  · exact checked10Upper_06
  · exact checked10Upper_07
  · exact checked10Upper_08
  · exact checked10Upper_09
  · exact checked10Upper_10
  · exact checked10Upper_11
  · exact checked10Upper_12
  · exact checked10Upper_13
  · exact checked10Upper_14
  · exact checked10Upper_15
  · exact checked10Upper_16
  · exact checked10Upper_17
  · exact checked10Upper_18


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity10Upper : slackRowsIdentityCheck 10 (1) certificate10Upper rows10Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted10Upper : certificate10Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive10Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 10 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate10Upper rows10Upper rowsChecked10Upper identity10Upper accepted10Upper hz hz1 ha

end polyak.Certificates.P1Slacks
