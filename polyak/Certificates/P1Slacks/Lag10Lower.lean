import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 10, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate10Lower : Certificate where
  degree0 := 22
  degree1 := 11
  coefficient := ![
    ![1024,11264,56320,168960,337920,473088,473088,337920,168960,56320,11264,1024],
    ![22528,247808,1239040,3717120,7434240,10407936,10407936,7434240,3717120,1239040,247808,22528],
    ![234960,2584272,12919920,38755440,77502240,108491040,108478944,77476320,38733840,12909840,2581680,234672],
    ![1545280,16992320,84932800,254712000,509251200,712709760,712467840,508732800,254280000,84731200,16940480,1539520],
    ![7190491,(158082091/2),394933531,(2367971493/2),2366342286,3310598991,3308319462,2361457581,1179915159,(786067847/2),78552575,(14272433/2)],
    ![25176294,276617475,1381480038,4139622477,8269618428,11564000910,11550548268,8240791338,4115599902,1370269503,273734766,24855993],
    ![(17629525947/256),(193581809169/256),(966197313885/256),(2893466193615/256),(2888349893415/128),(4036540257477/128),(4029403891149/128),(2873057679855/128),(2867979171015/256),(954303370005/256),(190523366457/256),(17289698979/256)],
    ![(2412836283/16),(26474474769/16),(132039786333/16),(395124699087/16),(394133141799/8),(550402561989/8),(549023069133/8),(391177085679/8),(390197938887/16),(129740631573/16),(25883263545/16),(2347146147/16)],
    ![(4403180497815/16384),(48270054003075/16384),(240529494981249/16384),(719137806832341/16384),(716698775711907/8192),(999979948215423/8192),(996597916221537/8192),(709451564296437/8192),(707059121139891/16384),(234892774991439/16384),(46820611719981/16384),(4242131355249/16384)],
    ![(3228287020321/8192),(35353120157333/8192),(175980686589319/8192),(525603130576851/8192),(523280014786677/4096),(729361797356409/4096),(726153712772775/4096),(516405547821747/4096),(514145685635301/8192),(170633878949929/8192),(33978226764347/8192),(3075521087767/8192)],
    ![(251014666597459/524288),(2745537306181943/524288),(13650269413093225/524288),(40720665928232325/524288),(40492632659587095/262144),(56373391806681579/262144),(56060050549304193/262144),(39821187108064125/262144),(39601590009027375/524288),(13128033984130915/524288),(2611248195877349/524288),(236093654341393/524288)],
    ![(63402036818361/131072),(692512578756453/131072),(3438301059291003/131072),(10242979564608207/131072),(10171917841552389/65536),(14142405212187777/65536),(14045332092494787/65536),(9963904013638839/65536),(9896289851418957/131072),(3276512526469353/131072),(650909813173743/131072),(58779507309171/131072)],
    ![(106631391423491/262144),(74422426127097355/16777216),(92232386422904945/4194304),(1097384228916004365/16777216),(17001924490759965/131072),(1510607633544102639/8388608),(374510879492168685/2097152),(1061200062582891765/8388608),(32891012108403195/524288),(347989352966704295/16777216),(17259451280921101/4194304),(6226117826140025/16777216)],
    ![(37246125526885/131072),(25949322569952695/8388608),(32102927932790869/2097152),(381304975390217409/8388608),(5897646234893487/65536),(523135600422539307/4194304),(129486614681437377/1048576),(366329769576631113/4194304),(11336635185677187/262144),(119763141740502211/8388608),(5931351121830881/2097152),(2136650012729821/8388608)],
    ![(86056758662589/524288),(29917875360097359/16777216),(36940076154157509/4194304),(14013377124332352543/536870912),(13845743786073805191/268435456),(19154924877971679993/268435456),(18931378665288988647/268435456),(3341679039662662449/67108864),(6607498824689644269/268435456),(2177876296224002511/268435456),(430783217212732965/268435456),(77477053584861801/536870912)],
    ![(5096555139225/65536),(1767867504568581/2097152),(2178048061938183/524288),(824496107156882271/67108864),(812953346537578887/33554432),(1122439030249663161/33554432),(1107207572699698407/33554432),(195078625130114433/8388608),(385049001285828333/33554432),(126702175216351407/33554432),(25021988031476901/33554432),(4493562223797417/67108864)],
    ![(3913561650669/131072),(2708253214868739/8388608),(3328524859799481/2097152),(628523347164651081/134217728),(618320461118384817/67108864),(109037480724639682803/8589934592),(53667370588212723069/4294967296),(75496288433201325189/8589934592),(9296220118575453939/2147483648),(12214681369564540749/8589934592),(1204187824927749453/4294967296),(215937287844128475/8589934592)],
    ![(598189435569/65536),(412806010473909/4194304),(505985463486351/1048576),(95297366874403881/67108864),(93517897754380977/33554432),(16452492732146869209/4294967296),(8079771065305190391/2147483648),(11342538420474679695/4294967296),(1393975611218961945/1073741824),(1828388258449941735/4294967296),(179968552858918503/2147483648),(32227749295752465/4294967296)],
    ![(1135208073725/524288),(195243668406355/8388608),(238601185706597/2097152),(89619999278681469/268435456),(87708336377777013/134217728),(7695548723578882173/8589934592),(3770297226275769651/4294967296),(21125151088604803407/34359738368),(20729070183301451337/68719476736),(6785439956606118145/68719476736),(1333794164370467615/68719476736),(119277970005019153/68719476736)],
    ![(50247527957/131072),(8612345991541/2097152),(10490187683435/524288),(3927820783081305/67108864),(3832685023469745/33554432),(335356635487296255/2147483648),(163888344133109841/1073741824),(916196546697821319/8589934592),(897237984609681033/17179869184),(293210309479907569/17179869184),(57558520791399167/17179869184),(5142311937086881/17179869184)],
    ![(12468027363/262144),(8515459101423/16777216),(10334431052061/4194304),(964044006800193/134217728),(937666330097841/67108864),(163604154150025533/8589934592),(79739836329072339/4294967296),(222366824978420223/17179869184),(217337608254993867/34359738368),(4538499501994967685/2199023255552),(111243978941187189/274877906944),(79461022089264483/2199023255552)],
    ![(482250281/131072),(327985326775/8388608),(396450666773/2097152),(36842990888199/67108864),(35709000008583/33554432),(6210557146938585/4294967296),(3018400921193847/2147483648),(8396949337350465/8589934592),(8191233990480441/17179869184),(170817196361282053/1099511627776),(4183793016811141/137438953472),(2988242582291683/1099511627776)],
    ![(69831059/524288),(23637287723/16777216),(28445949481/4194304),(10530278028447/536870912),(10166748612999/268435456),(440502428061843/8589934592),(213431733082029/4294967296),(1184495326059063/34359738368),(1153305706884105/68719476736),(12011870211234533/2199023255552),(294127045544009/274877906944),(3363480470950985/35184372088832)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row10Lower_00 : Expr := (.add (.literal (1024)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_00 :
    (certificate10Lower.rowExpression ⟨0,by decide⟩).check row10Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row10Lower_01 : Expr := (.add (.literal (22528)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_01 :
    (certificate10Lower.rowExpression ⟨1,by decide⟩).check row10Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row10Lower_02 : Expr := (.add (.literal (234960)) (.mul .y (.add (.literal (-288)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_02 :
    (certificate10Lower.rowExpression ⟨2,by decide⟩).check row10Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row10Lower_03 : Expr := (.add (.literal (1545280)) (.mul .y (.add (.literal (-5760)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_03 :
    (certificate10Lower.rowExpression ⟨3,by decide⟩).check row10Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row10Lower_04 : Expr := (.add (.literal (7190491)) (.mul .y (.add (.literal ((-108711/2))) (.mul .y (.add (.literal (81)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_04 :
    (certificate10Lower.rowExpression ⟨4,by decide⟩).check row10Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row10Lower_05 : Expr := (.add (.literal (25176294)) (.mul .y (.add (.literal (-321759)) (.mul .y (.add (.literal (1458)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_05 :
    (certificate10Lower.rowExpression ⟨5,by decide⟩).check row10Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row10Lower_06 : Expr := (.add (.literal ((17629525947/256))) (.mul .y (.add (.literal ((-42872031/32))) (.mul .y (.add (.literal ((98415/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_06 :
    (certificate10Lower.rowExpression ⟨6,by decide⟩).check row10Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row10Lower_07 : Expr := (.add (.literal ((2412836283/16))) (.mul .y (.add (.literal ((-8340543/2))) (.mul .y (.add (.literal (64638)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_07 :
    (certificate10Lower.rowExpression ⟨7,by decide⟩).check row10Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row10Lower_08 : Expr := (.add (.literal ((4403180497815/16384))) (.mul .y (.add (.literal ((-82465736445/8192))) (.mul .y (.add (.literal ((970582581/4096))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_08 :
    (certificate10Lower.rowExpression ⟨8,by decide⟩).check row10Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row10Lower_09 : Expr := (.add (.literal ((3228287020321/8192))) (.mul .y (.add (.literal ((-79018533099/4096))) (.mul .y (.add (.literal ((1317783411/2048))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_09 :
    (certificate10Lower.rowExpression ⟨9,by decide⟩).check row10Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row10Lower_10 : Expr := (.add (.literal ((251014666597459/524288))) (.mul .y (.add (.literal ((-7812013195053/262144))) (.mul .y (.add (.literal ((87876766755/65536))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_10 :
    (certificate10Lower.rowExpression ⟨10,by decide⟩).check row10Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row10Lower_11 : Expr := (.add (.literal ((63402036818361/131072))) (.mul .y (.add (.literal ((-2454913122759/65536))) (.mul .y (.add (.literal ((35912092041/16384))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_11 :
    (certificate10Lower.rowExpression ⟨11,by decide⟩).check row10Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row10Lower_12 : Expr := (.add (.literal ((106631391423491/262144))) (.mul .y (.add (.literal ((-646073435040309/16777216))) (.mul .y (.add (.literal ((23891115667275/8388608))) (.mul .y (.add (.literal ((-2657205/2097152))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_12 :
    (certificate10Lower.rowExpression ⟨12,by decide⟩).check row10Lower_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row10Lower_13 : Expr := (.add (.literal ((37246125526885/131072))) (.mul .y (.add (.literal ((-271949800974345/8388608))) (.mul .y (.add (.literal ((12423943135863/4194304))) (.mul .y (.add (.literal ((-13286025/1048576))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_13 :
    (certificate10Lower.rowExpression ⟨13,by decide⟩).check row10Lower_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row10Lower_14 : Expr := (.add (.literal ((86056758662589/524288))) (.mul .y (.add (.literal ((-374103689133969/16777216))) (.mul .y (.add (.literal ((20723130906543/8388608))) (.mul .y (.add (.literal ((-30347938305/536870912))) (.mul .y (.add (.literal ((167403915/268435456))) (.mul .y (.add (.literal ((100442349/134217728))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_14 :
    (certificate10Lower.rowExpression ⟨14,by decide⟩).check row10Lower_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row10Lower_15 : Expr := (.add (.literal ((5096555139225/65536))) (.mul .y (.add (.literal ((-26119904438619/2097152))) (.mul .y (.add (.literal ((1727123551461/1048576))) (.mul .y (.add (.literal ((-9940603905/67108864))) (.mul .y (.add (.literal ((167403915/33554432))) (.mul .y (.add (.literal ((100442349/16777216))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_15 :
    (certificate10Lower.rowExpression ⟨15,by decide⟩).check row10Lower_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row10Lower_16 : Expr := (.add (.literal ((3913561650669/131072))) (.mul .y (.add (.literal ((-46894187202237/8388608))) (.mul .y (.add (.literal ((3652150432707/4194304))) (.mul .y (.add (.literal ((-33871392135/134217728))) (.mul .y (.add (.literal ((1171827405/67108864))) (.mul .y (.add (.literal ((176678091891/8589934592))) (.mul .y (.add (.literal ((-301327047/1073741824))) (.mul .y (.add (.literal ((-43046721/268435456))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_16 :
    (certificate10Lower.rowExpression ⟨16,by decide⟩).check row10Lower_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row10Lower_17 : Expr := (.add (.literal ((598189435569/65536))) (.mul .y (.add (.literal ((-8319352166667/4194304))) (.mul .y (.add (.literal ((754281204597/2097152))) (.mul .y (.add (.literal ((-19586258055/67108864))) (.mul .y (.add (.literal ((1171827405/33554432))) (.mul .y (.add (.literal ((170048896857/4294967296))) (.mul .y (.add (.literal ((-903981141/536870912))) (.mul .y (.add (.literal ((-129140163/134217728))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_17 :
    (certificate10Lower.rowExpression ⟨17,by decide⟩).check row10Lower_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row10Lower_18 : Expr := (.add (.literal ((1135208073725/524288))) (.mul .y (.add (.literal ((-4552952569245/8388608))) (.mul .y (.add (.literal ((475581820419/4194304))) (.mul .y (.add (.literal ((-62218455075/268435456))) (.mul .y (.add (.literal ((5859137025/134217728))) (.mul .y (.add (.literal ((400262760765/8589934592))) (.mul .y (.add (.literal ((-4519905705/1073741824))) (.mul .y (.add (.literal ((-78388078941/34359738368))) (.mul .y (.add (.literal ((3486784401/68719476736))) (.mul .y (.add (.literal ((387420489/34359738368))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_18 :
    (certificate10Lower.rowExpression ⟨18,by decide⟩).check row10Lower_18=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 19. -/
private def row10Lower_19 : Expr := (.add (.literal ((50247527957/131072))) (.mul .y (.add (.literal ((-231218928891/2097152))) (.mul .y (.add (.literal ((27557710245/1048576))) (.mul .y (.add (.literal ((-8362224135/67108864))) (.mul .y (.add (.literal ((1171827405/33554432))) (.mul .y (.add (.literal ((73423357119/2147483648))) (.mul .y (.add (.literal ((-1506635235/268435456))) (.mul .y (.add (.literal ((-23288276061/8589934592))) (.mul .y (.add (.literal ((3486784401/17179869184))) (.mul .y (.add (.literal ((387420489/8589934592))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_19 :
    (certificate10Lower.rowExpression ⟨19,by decide⟩).check row10Lower_19=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 20. -/
private def row10Lower_20 : Expr := (.add (.literal ((12468027363/262144))) (.mul .y (.add (.literal ((-262032162129/16777216))) (.mul .y (.add (.literal ((35294755887/8388608))) (.mul .y (.add (.literal ((-5811307335/134217728))) (.mul .y (.add (.literal ((1171827405/67108864))) (.mul .y (.add (.literal ((130273726653/8589934592))) (.mul .y (.add (.literal ((-4519905705/1073741824))) (.mul .y (.add (.literal ((-28539976023/17179869184))) (.mul .y (.add (.literal ((10460353203/34359738368))) (.mul .y (.add (.literal ((110414839365/2199023255552))) (.mul .y (.add (.literal ((-3486784401/1099511627776))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_20 :
    (certificate10Lower.rowExpression ⟨20,by decide⟩).check row10Lower_20=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 21. -/
private def row10Lower_21 : Expr := (.add (.literal ((482250281/131072))) (.mul .y (.add (.literal ((-11518871049/8388608))) (.mul .y (.add (.literal ((1735194231/4194304))) (.mul .y (.add (.literal ((-587242305/67108864))) (.mul .y (.add (.literal ((167403915/33554432))) (.mul .y (.add (.literal ((15769448793/4294967296))) (.mul .y (.add (.literal ((-903981141/536870912))) (.mul .y (.add (.literal ((-4003345053/8589934592))) (.mul .y (.add (.literal ((3486784401/17179869184))) (.mul .y (.add (.literal ((11235194181/1099511627776))) (.mul .y (.add (.literal ((-3486784401/549755813888))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_21 :
    (certificate10Lower.rowExpression ⟨21,by decide⟩).check row10Lower_21=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 22. -/
private def row10Lower_22 : Expr := (.add (.literal ((69831059/524288))) (.mul .y (.add (.literal ((-943245045/16777216))) (.mul .y (.add (.literal ((156792267/8388608))) (.mul .y (.add (.literal ((-417181185/536870912))) (.mul .y (.add (.literal ((167403915/268435456))) (.mul .y (.add (.literal ((3113712819/8589934592))) (.mul .y (.add (.literal ((-301327047/1073741824))) (.mul .y (.add (.literal ((-1248354909/34359738368))) (.mul .y (.add (.literal ((3486784401/68719476736))) (.mul .y (.add (.literal ((-13559717115/2199023255552))) (.mul .y (.add (.literal ((-3486784401/1099511627776))) (.mul .y (.add (.literal ((31381059609/35184372088832))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked10Lower_22 :
    (certificate10Lower.rowExpression ⟨22,by decide⟩).check row10Lower_22=true := by kernel_decide

def rows10Lower : Fin (certificate10Lower.degree0+1) → Expr := ![row10Lower_00,row10Lower_01,row10Lower_02,row10Lower_03,row10Lower_04,row10Lower_05,row10Lower_06,row10Lower_07,row10Lower_08,row10Lower_09,row10Lower_10,row10Lower_11,row10Lower_12,row10Lower_13,row10Lower_14,row10Lower_15,row10Lower_16,row10Lower_17,row10Lower_18,row10Lower_19,row10Lower_20,row10Lower_21,row10Lower_22]

theorem rowsChecked10Lower : ∀ i, (certificate10Lower.rowExpression i).check (rows10Lower i)=true := by
  intro i
  fin_cases i
  · exact checked10Lower_00
  · exact checked10Lower_01
  · exact checked10Lower_02
  · exact checked10Lower_03
  · exact checked10Lower_04
  · exact checked10Lower_05
  · exact checked10Lower_06
  · exact checked10Lower_07
  · exact checked10Lower_08
  · exact checked10Lower_09
  · exact checked10Lower_10
  · exact checked10Lower_11
  · exact checked10Lower_12
  · exact checked10Lower_13
  · exact checked10Lower_14
  · exact checked10Lower_15
  · exact checked10Lower_16
  · exact checked10Lower_17
  · exact checked10Lower_18
  · exact checked10Lower_19
  · exact checked10Lower_20
  · exact checked10Lower_21
  · exact checked10Lower_22


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity10Lower : slackRowsIdentityCheck 10 (-1) certificate10Lower rows10Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted10Lower : certificate10Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive10Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 10 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate10Lower rows10Lower rowsChecked10Lower identity10Lower accepted10Lower hz hz1 ha

end polyak.Certificates.P1Slacks
