import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 11, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate11Upper : Certificate where
  degree0 := 20
  degree1 := 10
  coefficient := ![
    ![512,5120,23040,61440,107520,129024,107520,61440,23040,5120,512],
    ![10240,102400,460800,1228800,2150400,2580480,2150400,1228800,460800,102400,10240],
    ![96560,965744,4346208,11590080,20281632,24335136,20275584,11583168,4342320,964592,96416],
    ![570720,5709792,25700544,68538240,119923776,143857728,119814912,68413824,25630560,5689056,568128],
    ![(18966675/8),(94920855/4),(854725419/8),284937849,(1993954851/4),(1195517421/2),(1990287495/4),283890033,(850010247/8),(94222311/4),(18792039/8)],
    ![7356198,73676892,331833942,885047184,1548037260,1855406952,1543238172,879562512,328748814,72762780,7241934],
    ![(4527199695/256),(45379839459/256),(6390003681/8),(136357671303/64),(476883038457/128),(571216609845/128),(237322129401/64),(135078368643/64),(201601686807/256),(44526971019/256),(1105147785/64)],
    ![(4315997865/128),(43306399029/128),(6101489943/4),(130217701041/32),(455269303503/64),(544919958387/64),(226126969551/32),(128494635669/32),(191370781089/128),(42157688781/128),(1043102271/32)],
    ![(212046024243/4096),(2130224327625/4096),(19221413585463/8192),(200336730129/32),(11202774607143/1024),(26794186603065/2048),(44413065278505/4096),(3148525803483/512),(9354828339117/4096),(2054408489517/4096),(405138088959/8192)],
    ![(66154797049/1024),(665538202939/1024),(6010127863461/2048),(31326999195/4),(3502223533893/256),(8368096302027/512),(13848294742779/1024),(979521203841/128),(2901821464935/1024),(634947842407/1024),(124662003965/2048)],
    ![(134873500795/2048),(1359104416945/2048),(12284955016983/4096),(512402536041/64),(7157533422963/512),(17083002036177/1024),(28219151123625/2048),(1990898348703/256),(5878274428917/2048),(1280822022997/2048),(250176403103/4096)],
    ![(56219342845/1024),(567585770647/1024),(5136024479697/2048),(214291603653/32),(2992029809853/256),(7132455254295/512),(11758248357807/1024),(827184860097/128),(2433095244531/1024),(527610364627/1024),(102444834185/2048)],
    ![(152945775165/4096),(1547446684359/4096),(7178395001052717/4194304),(19176062291143965/4194304),(66906181019147211/8388608),(4977618173676603/524288),(65502401862125277/8388608),(18373902740959257/4194304),(13454360448360525/8388608),(725446062580929/2097152),(279809623646673/8388608)],
    ![(10542329337/512),(106922567163/512),(496713495098925/524288),(1327555876482333/524288),(4629884599540683/1048576),(343973226643515/65536),(4515720788305629/1048576),(1262319381032985/524288),(920035873030221/1048576),(49307969137857/262144),(18872493871569/1048576)],
    ![(9326108073/1024),(94846336563/1024),(441336344016699/1048576),(1180267579685835/1048576),(526661521019884881/268435456),(625145676124364793/268435456),(255819730830500043/134217728),(142490188116708345/134217728),(103324981668950349/268435456),(22002006807464997/268435456),(521776480998135/67108864)],
    ![(1627278693/512),(16600238583/512),(77388055985979/524288),(207113277160395/524288),(92386155680690931/134217728),(109501354668527595/134217728),(44690813629258977/67108864),(24793598741820651/67108864),(17879778476783847/134217728),(3779317235140719/134217728),(88759047342885/33554432)],
    ![(3496012125/4096),(35786268519/4096),(83592336433959/2097152),(223921268091639/2097152),(49928672995937919/268435456),(59092026753223575/268435456),(1539274027846398813/8589934592),(212596187234094225/2147483648),(152408612497026573/4294967296),(15978454409658351/2147483648),(5939513814746505/8589934592)],
    ![(173827605/1024),(1786188495/1024),(4182363309627/524288),(11215866788811/524288),(2500516495977813/67108864),(2955288360651741/67108864),(76768210308331485/2147483648),(10556759917531377/536870912),(7520806181559789/1073741824),(781643739133023/536870912),(287087740695177/2147483648)],
    ![(48094699/2048),(496317793/2048),(1165303008315/1048576),(3129251412939/1048576),(1395382058853567/268435456),(1647069925060503/268435456),(21334351257035511/4294967296),(2920810477724187/1073741824),(66151665700768845/68719476736),(13622525848926161/68719476736),(617199553822387/34359738368)],
    ![(2059249/1024),(21351379/1024),(50286055725/524288),(135262743837/524288),(60336999207411/134217728),(71147807440875/134217728),(919220964867645/2147483648),(125293530529401/536870912),(2818521044089101/34359738368),(574652924702801/34359738368),(25659387774499/17179869184)],
    ![(327635/4096),(3414761/4096),(16140999213/4194304),(43508690205/4194304),(4855991896113/268435456),(5722916204025/268435456),(147556111059165/8589934592),(20026973055153/2147483648),(223690980548925/68719476736),(45123297842033/68719476736),(126895495144495/2199023255552)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row11Upper_00 : Expr := (.add (.literal (512)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_00 :
    (certificate11Upper.rowExpression ⟨0,by decide⟩).check row11Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row11Upper_01 : Expr := (.add (.literal (10240)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_01 :
    (certificate11Upper.rowExpression ⟨1,by decide⟩).check row11Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row11Upper_02 : Expr := (.add (.literal (96560)) (.mul .y (.add (.literal (144)) (.mul .y (.add (.literal (-288)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_02 :
    (certificate11Upper.rowExpression ⟨2,by decide⟩).check row11Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row11Upper_03 : Expr := (.add (.literal (570720)) (.mul .y (.add (.literal (2592)) (.mul .y (.add (.literal (-5184)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_03 :
    (certificate11Upper.rowExpression ⟨3,by decide⟩).check row11Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row11Upper_04 : Expr := (.add (.literal ((18966675/8))) (.mul .y (.add (.literal (21870)) (.mul .y (.add (.literal ((-87399/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_04 :
    (certificate11Upper.rowExpression ⟨4,by decide⟩).check row11Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row11Upper_05 : Expr := (.add (.literal (7356198)) (.mul .y (.add (.literal (114912)) (.mul .y (.add (.literal (-229176)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_05 :
    (certificate11Upper.rowExpression ⟨5,by decide⟩).check row11Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row11Upper_06 : Expr := (.add (.literal ((4527199695/256))) (.mul .y (.add (.literal ((107842509/256))) (.mul .y (.add (.literal ((-26806383/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_06 :
    (certificate11Upper.rowExpression ⟨6,by decide⟩).check row11Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row11Upper_07 : Expr := (.add (.literal ((4315997865/128))) (.mul .y (.add (.literal ((146420379/128))) (.mul .y (.add (.literal ((-36251145/16))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_07 :
    (certificate11Upper.rowExpression ⟨7,by decide⟩).check row11Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row11Upper_08 : Expr := (.add (.literal ((212046024243/4096))) (.mul .y (.add (.literal ((9764085195/4096))) (.mul .y (.add (.literal ((-38482129917/8192))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_08 :
    (certificate11Upper.rowExpression ⟨8,by decide⟩).check row11Upper_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row11Upper_09 : Expr := (.add (.literal ((66154797049/1024))) (.mul .y (.add (.literal ((3990232449/1024))) (.mul .y (.add (.literal ((-15628055031/2048))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_09 :
    (certificate11Upper.rowExpression ⟨9,by decide⟩).check row11Upper_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row11Upper_10 : Expr := (.add (.literal ((134873500795/2048))) (.mul .y (.add (.literal ((10369408995/2048))) (.mul .y (.add (.literal ((-40309416477/4096))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_10 :
    (certificate11Upper.rowExpression ⟨10,by decide⟩).check row11Upper_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row11Upper_11 : Expr := (.add (.literal ((56219342845/1024))) (.mul .y (.add (.literal ((5392342197/1024))) (.mul .y (.add (.literal ((-20778535899/2048))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_11 :
    (certificate11Upper.rowExpression ⟨11,by decide⟩).check row11Upper_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row11Upper_12 : Expr := (.add (.literal ((152945775165/4096))) (.mul .y (.add (.literal ((17988932709/4096))) (.mul .y (.add (.literal ((-35132322396627/4194304))) (.mul .y (.add (.literal ((2657205/4194304))) (.mul .y (.add (.literal ((-18600435/8388608))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_12 :
    (certificate11Upper.rowExpression ⟨12,by decide⟩).check row11Upper_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row11Upper_13 : Expr := (.add (.literal ((10542329337/512))) (.mul .y (.add (.literal ((1499273793/512))) (.mul .y (.add (.literal ((-2894348026323/524288))) (.mul .y (.add (.literal ((2657205/524288))) (.mul .y (.add (.literal ((-18600435/1048576))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_13 :
    (certificate11Upper.rowExpression ⟨13,by decide⟩).check row11Upper_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row11Upper_14 : Expr := (.add (.literal ((9326108073/1024))) (.mul .y (.add (.literal ((1585255833/1024))) (.mul .y (.add (.literal ((-3020433744069/1048576))) (.mul .y (.add (.literal ((18600435/1048576))) (.mul .y (.add (.literal ((-16546415535/268435456))) (.mul .y (.add (.literal ((-100442349/268435456))) (.mul .y (.add (.literal ((33480783/33554432))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_14 :
    (certificate11Upper.rowExpression ⟨14,by decide⟩).check row11Upper_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row11Upper_15 : Expr := (.add (.literal ((1627278693/512))) (.mul .y (.add (.literal ((327451653/512))) (.mul .y (.add (.literal ((-614740621509/524288))) (.mul .y (.add (.literal ((18600435/524288))) (.mul .y (.add (.literal ((-16307267085/134217728))) (.mul .y (.add (.literal ((-301327047/134217728))) (.mul .y (.add (.literal ((100442349/16777216))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_15 :
    (certificate11Upper.rowExpression ⟨15,by decide⟩).check row11Upper_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row11Upper_16 : Expr := (.add (.literal ((3496012125/4096))) (.mul .y (.add (.literal ((826147269/4096))) (.mul .y (.add (.literal ((-762669541593/2097152))) (.mul .y (.add (.literal ((93002175/2097152))) (.mul .y (.add (.literal ((-39871361025/268435456))) (.mul .y (.add (.literal ((-1506635235/268435456))) (.mul .y (.add (.literal ((127059571485/8589934592))) (.mul .y (.add (.literal ((43046721/536870912))) (.mul .y (.add (.literal ((-387420489/2147483648))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_16 :
    (certificate11Upper.rowExpression ⟨16,by decide⟩).check row11Upper_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row11Upper_17 : Expr := (.add (.literal ((173827605/1024))) (.mul .y (.add (.literal ((47912445/1024))) (.mul .y (.add (.literal ((-43405256133/524288))) (.mul .y (.add (.literal ((18600435/524288))) (.mul .y (.add (.literal ((-7735123755/67108864))) (.mul .y (.add (.literal ((-502211745/67108864))) (.mul .y (.add (.literal ((41348767005/2147483648))) (.mul .y (.add (.literal ((43046721/134217728))) (.mul .y (.add (.literal ((-387420489/536870912))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_17 :
    (certificate11Upper.rowExpression ⟨17,by decide⟩).check row11Upper_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row11Upper_18 : Expr := (.add (.literal ((48094699/2048))) (.mul .y (.add (.literal ((15370803/2048))) (.mul .y (.add (.literal ((-13627516869/1048576))) (.mul .y (.add (.literal ((18600435/1048576))) (.mul .y (.add (.literal ((-14872376385/268435456))) (.mul .y (.add (.literal ((-1506635235/268435456))) (.mul .y (.add (.literal ((59763197655/4294967296))) (.mul .y (.add (.literal ((129140163/268435456))) (.mul .y (.add (.literal ((-72447631443/68719476736))) (.mul .y (.add (.literal ((-387420489/68719476736))) (.mul .y (.add (.literal ((387420489/34359738368))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_18 :
    (certificate11Upper.rowExpression ⟨18,by decide⟩).check row11Upper_18=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 19. -/
private def row11Upper_19 : Expr := (.add (.literal ((2059249/1024))) (.mul .y (.add (.literal ((758889/1024))) (.mul .y (.add (.literal ((-656001747/524288))) (.mul .y (.add (.literal ((2657205/524288))) (.mul .y (.add (.literal ((-2022133005/134217728))) (.mul .y (.add (.literal ((-301327047/134217728))) (.mul .y (.add (.literal ((11349985437/2147483648))) (.mul .y (.add (.literal ((43046721/134217728))) (.mul .y (.add (.literal ((-22857808851/34359738368))) (.mul .y (.add (.literal ((-387420489/34359738368))) (.mul .y (.add (.literal ((387420489/17179869184))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_19 :
    (certificate11Upper.rowExpression ⟨19,by decide⟩).check row11Upper_19=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 20. -/
private def row11Upper_20 : Expr := (.add (.literal ((327635/4096))) (.mul .y (.add (.literal ((138411/4096))) (.mul .y (.add (.literal ((-232017363/4194304))) (.mul .y (.add (.literal ((2657205/4194304))) (.mul .y (.add (.literal ((-475639695/268435456))) (.mul .y (.add (.literal ((-100442349/268435456))) (.mul .y (.add (.literal ((7064445213/8589934592))) (.mul .y (.add (.literal ((43046721/536870912))) (.mul .y (.add (.literal ((-10460353203/68719476736))) (.mul .y (.add (.literal ((-387420489/68719476736))) (.mul .y (.add (.literal ((21308126895/2199023255552))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Upper_20 :
    (certificate11Upper.rowExpression ⟨20,by decide⟩).check row11Upper_20=true := by kernel_decide

def rows11Upper : Fin (certificate11Upper.degree0+1) → Expr := ![row11Upper_00,row11Upper_01,row11Upper_02,row11Upper_03,row11Upper_04,row11Upper_05,row11Upper_06,row11Upper_07,row11Upper_08,row11Upper_09,row11Upper_10,row11Upper_11,row11Upper_12,row11Upper_13,row11Upper_14,row11Upper_15,row11Upper_16,row11Upper_17,row11Upper_18,row11Upper_19,row11Upper_20]

theorem rowsChecked11Upper : ∀ i, (certificate11Upper.rowExpression i).check (rows11Upper i)=true := by
  intro i
  fin_cases i
  · exact checked11Upper_00
  · exact checked11Upper_01
  · exact checked11Upper_02
  · exact checked11Upper_03
  · exact checked11Upper_04
  · exact checked11Upper_05
  · exact checked11Upper_06
  · exact checked11Upper_07
  · exact checked11Upper_08
  · exact checked11Upper_09
  · exact checked11Upper_10
  · exact checked11Upper_11
  · exact checked11Upper_12
  · exact checked11Upper_13
  · exact checked11Upper_14
  · exact checked11Upper_15
  · exact checked11Upper_16
  · exact checked11Upper_17
  · exact checked11Upper_18
  · exact checked11Upper_19
  · exact checked11Upper_20


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity11Upper : slackRowsIdentityCheck 11 (1) certificate11Upper rows11Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted11Upper : certificate11Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive11Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 11 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate11Upper rows11Upper rowsChecked11Upper identity11Upper accepted11Upper hz hz1 ha

end polyak.Certificates.P1Slacks
