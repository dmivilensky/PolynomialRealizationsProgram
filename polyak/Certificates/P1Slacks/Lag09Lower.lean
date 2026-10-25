import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 9, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate09Lower : Certificate where
  degree0 := 20
  degree1 := 10
  coefficient := ![
    ![512,5120,23040,61440,107520,129024,107520,61440,23040,5120,512],
    ![10240,102400,460800,1228800,2150400,2580480,2150400,1228800,460800,102400,10240],
    ![96560,965456,4343904,11582016,20265504,24314976,20259456,11575104,4340016,964304,96416],
    ![570720,5704608,25659072,68393088,119633472,143494848,119524608,68268672,25589088,5683872,568128],
    ![(18966675/8),(94745895/4),(851926059/8),283713129,(1984157091/4),(1189393821/2),(1980489735/4),282665313,(847210887/8),(94047351/4),(18792039/8)],
    ![7356198,73447068,329995350,878612112,1535167116,1839319272,1530368028,873127440,326910222,72532956,7241934],
    ![(4527199695/256),(45164154441/256),(12672164853/16),(134847876177/64),(470843857953/128),(563667634215/128),(234302539149/64),(133568573517/64),(199876206663/256),(44311286001/256),(1105147785/64)],
    ![(4315997865/128),(43013558271/128),(12056559507/8),(128167815735/32),(447069762279/64),(534670531857/64),(222027198939/32),(126444750363/32),(189028055025/128),(41864848023/128),(1043102271/32)],
    ![(212046024243/4096),(2110696157235/4096),(18908962859223/8192),(3137039085699/512),(10929380221683/1024),(26110700639415/2048),(43319487736665/4096),(1540088603559/256),(9198602975997/4096),(2034880319127/4096),(405138088959/8192)],
    ![(66154797049/1024),(657557738041/1024),(5882440425093/2048),(974532347097/128),(3390497025321/256),(8088780030597/512),(13401388708491/1024),(475794788349/64),(2837977745751/1024),(626967377509/1024),(124662003965/2048)],
    ![(134873500795/2048),(1338365598955/2048),(11953133929143/4096),(1977024281199/256),(6867189971103/512),(16357143406527/1024),(27057777316185/2048),(959156242869/128),(5712363884997/2048),(1260083205007/2048),(250176403103/4096)],
    ![(56219342845/1024),(556801086253/1024),(4963469529393/2048),(819420019233/128),(2841044228337/256),(6754991300505/512),(11154306031743/1024),(394719232359/64),(2346817769379/1024),(516825680233/1024),(102444834185/2048)],
    ![(152945775165/4096),(1511468818941/4096),(6883664327548461/4194304),(18144504928564659/4194304),(62779951526314707/8388608),(18621025958267217/2097152),(61376172220489293/8388608),(17342345303978211/4194304),(12864899037579093/8388608),(176756348207427/524288),(279809623646673/8388608)],
    ![(10542329337/512),(103924019577/512),(472149393274413/524288),(1241581514782131/524288),(4285987110224595/1048576),(1268424921233745/262144),(4171823150186061/1048576),(1176344944931043/524288),(870907605608277/1048576),(11943177529155/65536),(18872493871569/1048576)],
    ![(9326108073/1024),(91675824897/1024),(415363512448827/1048576),(1089362631997413/1048576),(480118149709721937/268435456),(566966390761875411/268435456),(232547978913228927/134217728),(130854288751285383/134217728),(96675880450577589/268435456),(21170866874755071/268435456),(521776480998135/67108864)],
    ![(1627278693/512),(15945335277/512),(72023088103227/524288),(188335852369893/524288),(82772076094263027/134217728),(97483684362476409/134217728),(39883708377394173/67108864),(22390023512639637/67108864),(16506291968879391/134217728),(3607629342124029/134217728),(88759047342885/33554432)],
    ![(3496012125/4096),(34133973981/4096),(76824538006311/2097152),(200233787590521/2097152),(43864582753424511/268435456),(51511738399176285/268435456),(1345212859551143517/8589934592),(188337684935196585/2147483648),(138546067167565677/4294967296),(15112009504254999/2147483648),(5939513814746505/8589934592)],
    ![(173827605/1024),(1690363605/1024),(3789864560187/524288),(9842083964901/524288),(2148809046211413/67108864),(2515619340032031/67108864),(65511567235324125/2147483648),(9149520862128969/536870912),(6716574524024397/1073741824),(731373496527975/536870912),(287087740695177/2147483648)],
    ![(48094699/2048),(465576187/2048),(1039385390139/1048576),(2688502548453/1048576),(1169680546545855/268435456),(1364874622275933/268435456),(17721186662732919/4294967296),(2469021614188179/1073741824),(57887854048122957/68719476736),(12589276776929891/68719476736),(617199553822387/34359738368)],
    ![(2059249/1024),(19833601/1024),(44069237037/524288),(113498564019/524288),(49188297184755/134217728),(57202328899449/134217728),(740575552840125/2147483648),(102944942338497/536870912),(2409578941459725/34359738368),(523509475204835/34359738368),(25659387774499/17179869184)],
    ![(327635/4096),(3137939/4096),(13873273389/4194304),(35566335411/4194304),(3838009993521/268435456),(4448088793683/268435456),(114854028654045/8589934592),(15931691801481/2147483648),(186197798897469/68719476736),(40433105424131/68719476736),(126895495144495/2199023255552)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row09Lower_00 : Expr := (.add (.literal (512)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_00 :
    (certificate09Lower.rowExpression ⟨0,by decide⟩).check row09Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row09Lower_01 : Expr := (.add (.literal (10240)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_01 :
    (certificate09Lower.rowExpression ⟨1,by decide⟩).check row09Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row09Lower_02 : Expr := (.add (.literal (96560)) (.mul .y (.add (.literal (-144)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_02 :
    (certificate09Lower.rowExpression ⟨2,by decide⟩).check row09Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row09Lower_03 : Expr := (.add (.literal (570720)) (.mul .y (.add (.literal (-2592)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_03 :
    (certificate09Lower.rowExpression ⟨3,by decide⟩).check row09Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row09Lower_04 : Expr := (.add (.literal ((18966675/8))) (.mul .y (.add (.literal (-21870)) (.mul .y (.add (.literal ((81/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_04 :
    (certificate09Lower.rowExpression ⟨4,by decide⟩).check row09Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row09Lower_05 : Expr := (.add (.literal (7356198)) (.mul .y (.add (.literal (-114912)) (.mul .y (.add (.literal (648)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_05 :
    (certificate09Lower.rowExpression ⟨5,by decide⟩).check row09Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row09Lower_06 : Expr := (.add (.literal ((4527199695/256))) (.mul .y (.add (.literal ((-107842509/256))) (.mul .y (.add (.literal ((616977/128))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_06 :
    (certificate09Lower.rowExpression ⟨6,by decide⟩).check row09Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row09Lower_07 : Expr := (.add (.literal ((4315997865/128))) (.mul .y (.add (.literal ((-146420379/128))) (.mul .y (.add (.literal ((1415799/64))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_07 :
    (certificate09Lower.rowExpression ⟨7,by decide⟩).check row09Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row09Lower_08 : Expr := (.add (.literal ((212046024243/4096))) (.mul .y (.add (.literal ((-9764085195/4096))) (.mul .y (.add (.literal ((574210863/8192))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_08 :
    (certificate09Lower.rowExpression ⟨8,by decide⟩).check row09Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row09Lower_09 : Expr := (.add (.literal ((66154797049/1024))) (.mul .y (.add (.literal ((-3990232449/1024))) (.mul .y (.add (.literal ((332874765/2048))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_09 :
    (certificate09Lower.rowExpression ⟨9,by decide⟩).check row09Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row09Lower_10 : Expr := (.add (.literal ((134873500795/2048))) (.mul .y (.add (.literal ((-10369408995/2048))) (.mul .y (.add (.literal ((1168219503/4096))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_10 :
    (certificate09Lower.rowExpression ⟨10,by decide⟩).check row09Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row09Lower_11 : Expr := (.add (.literal ((56219342845/1024))) (.mul .y (.add (.literal ((-5392342197/1024))) (.mul .y (.add (.literal ((790832889/2048))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_11 :
    (certificate09Lower.rowExpression ⟨11,by decide⟩).check row09Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row09Lower_12 : Expr := (.add (.literal ((152945775165/4096))) (.mul .y (.add (.literal ((-17988932709/4096))) (.mul .y (.add (.literal ((1709011791405/4194304))) (.mul .y (.add (.literal ((-2657205/4194304))) (.mul .y (.add (.literal ((-7971615/8388608))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_12 :
    (certificate09Lower.rowExpression ⟨12,by decide⟩).check row09Lower_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row09Lower_13 : Expr := (.add (.literal ((10542329337/512))) (.mul .y (.add (.literal ((-1499273793/512))) (.mul .y (.add (.literal ((176164701741/524288))) (.mul .y (.add (.literal ((-2657205/524288))) (.mul .y (.add (.literal ((-7971615/1048576))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_13 :
    (certificate09Lower.rowExpression ⟨13,by decide⟩).check row09Lower_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row09Lower_14 : Expr := (.add (.literal ((9326108073/1024))) (.mul .y (.add (.literal ((-1585255833/1024))) (.mul .y (.add (.literal ((226170201915/1048576))) (.mul .y (.add (.literal ((-18600435/1048576))) (.mul .y (.add (.literal ((-7022992815/268435456))) (.mul .y (.add (.literal ((100442349/268435456))) (.mul .y (.add (.literal ((33480783/134217728))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_14 :
    (certificate09Lower.rowExpression ⟨14,by decide⟩).check row09Lower_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row09Lower_15 : Expr := (.add (.literal ((1627278693/512))) (.mul .y (.add (.literal ((-327451653/512))) (.mul .y (.add (.literal ((55880363835/524288))) (.mul .y (.add (.literal ((-18600435/524288))) (.mul .y (.add (.literal ((-6783844365/134217728))) (.mul .y (.add (.literal ((301327047/134217728))) (.mul .y (.add (.literal ((100442349/67108864))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_15 :
    (certificate09Lower.rowExpression ⟨15,by decide⟩).check row09Lower_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row09Lower_16 : Expr := (.add (.literal ((3496012125/4096))) (.mul .y (.add (.literal ((-826147269/4096))) (.mul .y (.add (.literal ((83305261863/2097152))) (.mul .y (.add (.literal ((-93002175/2097152))) (.mul .y (.add (.literal ((-16062804225/268435456))) (.mul .y (.add (.literal ((1506635235/268435456))) (.mul .y (.add (.literal ((30634916445/8589934592))) (.mul .y (.add (.literal ((-43046721/536870912))) (.mul .y (.add (.literal ((-43046721/2147483648))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_16 :
    (certificate09Lower.rowExpression ⟨16,by decide⟩).check row09Lower_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row09Lower_17 : Expr := (.add (.literal ((173827605/1024))) (.mul .y (.add (.literal ((-47912445/1024))) (.mul .y (.add (.literal ((5657087547/524288))) (.mul .y (.add (.literal ((-18600435/524288))) (.mul .y (.add (.literal ((-2973412395/67108864))) (.mul .y (.add (.literal ((502211745/67108864))) (.mul .y (.add (.literal ((9207215325/2147483648))) (.mul .y (.add (.literal ((-43046721/134217728))) (.mul .y (.add (.literal ((-43046721/536870912))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_17 :
    (certificate09Lower.rowExpression ⟨17,by decide⟩).check row09Lower_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row09Lower_18 : Expr := (.add (.literal ((48094699/2048))) (.mul .y (.add (.literal ((-15370803/2048))) (.mul .y (.add (.literal ((2112185403/1048576))) (.mul .y (.add (.literal ((-18600435/1048576))) (.mul .y (.add (.literal ((-5348953665/268435456))) (.mul .y (.add (.literal ((1506635235/268435456))) (.mul .y (.add (.literal ((11550870135/4294967296))) (.mul .y (.add (.literal ((-129140163/268435456))) (.mul .y (.add (.literal ((-6327867987/68719476736))) (.mul .y (.add (.literal ((387420489/68719476736))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_18 :
    (certificate09Lower.rowExpression ⟨18,by decide⟩).check row09Lower_18=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 19. -/
private def row09Lower_19 : Expr := (.add (.literal ((2059249/1024))) (.mul .y (.add (.literal ((-758889/1024))) (.mul .y (.add (.literal ((121100589/524288))) (.mul .y (.add (.literal ((-2657205/524288))) (.mul .y (.add (.literal ((-661644045/134217728))) (.mul .y (.add (.literal ((301327047/134217728))) (.mul .y (.add (.literal ((1707519933/2147483648))) (.mul .y (.add (.literal ((-43046721/134217728))) (.mul .y (.add (.literal ((-817887699/34359738368))) (.mul .y (.add (.literal ((387420489/34359738368))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_19 :
    (certificate09Lower.rowExpression ⟨19,by decide⟩).check row09Lower_19=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 20. -/
private def row09Lower_20 : Expr := (.add (.literal ((327635/4096))) (.mul .y (.add (.literal ((-138411/4096))) (.mul .y (.add (.literal ((51448365/4194304))) (.mul .y (.add (.literal ((-2657205/4194304))) (.mul .y (.add (.literal ((-135517455/268435456))) (.mul .y (.add (.literal ((100442349/268435456))) (.mul .y (.add (.literal ((636134877/8589934592))) (.mul .y (.add (.literal ((-43046721/536870912))) (.mul .y (.add (.literal ((559607373/68719476736))) (.mul .y (.add (.literal ((387420489/68719476736))) (.mul .y (.add (.literal ((-3486784401/2199023255552))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked09Lower_20 :
    (certificate09Lower.rowExpression ⟨20,by decide⟩).check row09Lower_20=true := by kernel_decide

def rows09Lower : Fin (certificate09Lower.degree0+1) → Expr := ![row09Lower_00,row09Lower_01,row09Lower_02,row09Lower_03,row09Lower_04,row09Lower_05,row09Lower_06,row09Lower_07,row09Lower_08,row09Lower_09,row09Lower_10,row09Lower_11,row09Lower_12,row09Lower_13,row09Lower_14,row09Lower_15,row09Lower_16,row09Lower_17,row09Lower_18,row09Lower_19,row09Lower_20]

theorem rowsChecked09Lower : ∀ i, (certificate09Lower.rowExpression i).check (rows09Lower i)=true := by
  intro i
  fin_cases i
  · exact checked09Lower_00
  · exact checked09Lower_01
  · exact checked09Lower_02
  · exact checked09Lower_03
  · exact checked09Lower_04
  · exact checked09Lower_05
  · exact checked09Lower_06
  · exact checked09Lower_07
  · exact checked09Lower_08
  · exact checked09Lower_09
  · exact checked09Lower_10
  · exact checked09Lower_11
  · exact checked09Lower_12
  · exact checked09Lower_13
  · exact checked09Lower_14
  · exact checked09Lower_15
  · exact checked09Lower_16
  · exact checked09Lower_17
  · exact checked09Lower_18
  · exact checked09Lower_19
  · exact checked09Lower_20


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity09Lower : slackRowsIdentityCheck 9 (-1) certificate09Lower rows09Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted09Lower : certificate09Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive09Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 9 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate09Lower rows09Lower rowsChecked09Lower identity09Lower accepted09Lower hz hz1 ha

end polyak.Certificates.P1Slacks
