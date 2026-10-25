import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 12, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate12Lower : Certificate where
  degree0 := 26
  degree1 := 13
  coefficient := ![
    ![4096,53248,319488,1171456,2928640,5271552,7028736,7028736,5271552,2928640,1171456,319488,53248,4096],
    ![106496,1384448,8306688,30457856,76144640,137060352,182747136,182747136,137060352,76144640,30457856,8306688,1384448,106496],
    ![1323712,17207104,103235712,378505600,946200640,1703047104,2270577408,2270425344,1702704960,945883840,378328192,103173504,17194432,1322560],
    ![10469888,136080896,816319488,2992563200,7479887360,13461060096,17944430592,17940781056,13452848640,7472284160,2988305408,814826496,135776768,10442240],
    ![59173777,768942931,4611760890,16902836566,42239710975,76000200309,101291901612,101250209940,75906394047,42152853325,16854196282,4594705206,765468625,58857931],
    ![254394998,3304842530,19815307644,72605746532,181388477930,326272778766,434728553160,434426891448,325594039914,180760016030,72253807868,19691900580,3279704054,252109682],
    ![(13834704481/16),(359323739381/32),(538418338491/8),(3944245528795/16),(9850235681935/16),(35423526427839/32),(5897707279629/4),(11783000068257/8),(17655898004415/16),(19597017272195/32),(1957639191563/8),(1066679366163/16),(177592787857/16),(27293212265/32)],
    ![(9536605637/4),(247581819913/8),(370818819591/2),(2715283186055/4),(6778088865515/4),(24364755817083/8),4054742729697,(8097407199717/2),(12128025739995/4),(13455525567055/8),(1343550290071/2),(731755426719/4),(121777866677/4),(18707203405/8)],
    ![(11119410586427/2048),(144261083817299/2048),(431911828564377/1024),(1580490062096341/1024),(7886559970355825/2048),(14167282505944689/2048),(4712944745593227/512),(4703487713048487/512),(14082169213042029/2048),(7807751365816325/2048),(1558423652825281/1024),(424174256482317/1024),(141108739635719/2048),(10832833842647/2048)],
    ![(10591393891091/1024),(137326701367019/1024),(410899951130721/512),(1502687643752317/512),(7493785919281145/1024),(13453575970119417/1024),(4472824246670307/256),(4461168321460191/256),(13348672643228373/1024),(7396653209196845/1024),(1475490484928713/512),(401363285049717/512),(133441392963647/1024),(10238184036239/1024)],
    ![(4360485595571053/262144),(56497771446313501/262144),(168930574342553379/131072),(617359300206402215/131072),(3076585343802839935/262144),(5519568704266737351/262144),(1833792986040832113/65536),(1827761460137462949/65536),(5465284971136414875/262144),(3026322627941430235/262144),(603285739765207499/131072),(163995689512524063/131072),(54487262811857113/262144),(4177712083347745/262144)],
    ![(372348739396205/16384),(4820577734039837/16384),(14402261893940259/8192),(52591685343685543/8192),(261882651360759935/16384),(469465455568622535/16384),(155851739150311281/4096),(155219352698767269/4096),(463773977504726427/16384),(256612764264559835/16384),(51116116956749515/8192),(13884854797222431/8192),(4609782250191833/16384),(353185513591841/16384)],
    ![(111097293436921171/4194304),(2874030321786493325/8388608),(8578956459051580407/4194304),(15649673176786279829/2097152),(9732453609625537835/524288),(278907203473889511609/8388608),(92510578577391700935/2097152),(23014021727672688603/524288),(137408389236790496451/4194304),(151931827198167384335/8388608),(30238865797937017771/4194304),(4103549820420857535/2097152),(680633274888211121/2097152),(208422112125328811/8388608)],
    ![(55350941771537989/2097152),(1430457638300140763/4194304),(4265640371147002305/2097152),(7773655682686122515/1048576),(4829663760875393165/262144),(138271674322434429711/4194304),(45819292105339841649/1048576),(11387743524497217405/262144),(67928406128137840725/2097152),(75038636779414857065/4194304),(14921236014886643629/2097152),(2023053728020830777/1048576),(335254575629120855/1048576),(102571034835470765/4194304)],
    ![(94352311798479553/4194304),(38970440566445870171/134217728),(464325791912680261983/268435456),(1690510271428332565183/268435456),(4196616220423669772725/268435456),(7501214492566058100699/268435456),(4966141405892907138627/134217728),(4931934697056013365243/134217728),(3673642151400771377853/134217728),(1013522066735199370375/67108864),(1610694617480267736907/268435456),(436338484685233784187/268435456),(72239762994246464353/268435456),(5520264487983557923/268435456)],
    ![(17175736075819841/1048576),(7085304265448849713/33554432),(84316708587735823773/67108864),(306608304558656692541/67108864),(760236267229074567455/67108864),(1357289423197298312913/67108864),(897553198048911531081/33554432),(890364268430040718833/33554432),(662469619958449781751/33554432),(182570598457417035845/16777216),(289834135462020059489/67108864),(78434857089604987761/67108864),(12972453596930289443/67108864),(990323933128561961/67108864)],
    ![(42613566210731659/4194304),(8777392005016932979/67108864),(104312069939527160799/134217728),(24244248489226701444005/8589934592),(30017730146351815834195/4294967296),(107047676835312871290165/8589934592),(17675110521660345770949/1073741824),(70048524942584858070645/4294967296),(26028512422518057797889/2147483648),(28659569433750435900505/4294967296),(2840388561973646140261/1073741824),(6142585727365389174225/8589934592),(507426660483101906467/4294967296),(77395051325601419321/8589934592)],
    ![(11202921221180299/2097152),(2304058563284498341/33554432),(27341308532418738825/67108864),(6345459106393781624249/4294967296),(7845406284643230362335/2147483648),(27939111753123551986569/4294967296),(4606918894817274938937/536870912),(18233778317843273781705/2147483648),(6766643520292308837957/1073741824),(7441453662856450948285/2147483648),(736629022109165604649/536870912),(1591200540214594676373/4294967296),(131301644152056559855/2147483648),(20005745675316547229/4294967296)],
    ![(9915812107987201/4194304),(4071935137208735957/134217728),(48241652433060548913/268435456),(5589176436381819507041/8589934592),(6899690413645809373735/4294967296),(196274936660337621732987/68719476736),(64633970038112007294579/17179869184),(31932000737241823739451/8589934592),(47336304929679903846591/17179869184),(51989321141818665162635/34359738368),(10280056315866775997017/17179869184),(1386239337150299853519/8589934592),(457043668170901995385/17179869184),(139128293674699668631/68719476736)],
    ![(457143710844535/524288),(187385658843422705/16777216),(2216090812320430269/33554432),(256308815449634176523/1073741824),(315876861286754286445/536870912),(8971176370200117984459/8589934592),(2949628560144716219667/2147483648),(1455063593335006453455/1073741824),(2153916006904560990159/2147483648),(2362425859858768421915/4294967296),(466532709367475433721/2147483648),(62835083667135874641/1073741824),(20693585632542747409/2147483648),(6292832438057867047/8589934592)],
    ![(1108888048273057/4194304),(113408961697559177/33554432),(1338621135868001481/67108864),(309063765138021220141/4294967296),(380202070235862600395/2147483648),(5389621863420153855897/17179869184),(1769094661780622169501/4294967296),(223056905328573905090793/549755813888),(329693349543310920337263/1099511627776),(180550083275701828189705/1099511627776),(35608417536341597506715/549755813888),(4790154100880940869085/274877906944),(3151650346209152615467/1099511627776),(239367049889723186497/1099511627776)],
    ![(135628782125707/2097152),(13840958851999925/16777216),(163026780422675181/33554432),(37563222558886575259/2147483648),(46118695136268643565/1073741824),(652538758303917975249/8589934592),(213808890082499701773/2147483648),(26912979469741336862907/274877906944),(39716967497974792397901/549755813888),(21718778409337501781275/549755813888),(4277774310958841280209/274877906944),(574779826058090218647/137438953472),(377780785725515746945/549755813888),(28667019173547759427/549755813888)],
    ![(52122938290891/4194304),(21226045354732085/134217728),(249437060010015153/268435456),(14336449212558599677/4294967296),(17564453741120493635/2147483648),(496043414580834719649/34359738368),(162224548578554224665/8589934592),(10191935323150305076263/549755813888),(15016427528933241559809/1099511627776),(262384509660365229287225/35184372088832),(51612458443359902830693/17592186044416),(6927054646403554382235/8796093022208),(2274305284975710103711/17592186044416),(344904840449747568323/35184372088832)],
    ![(1890400257473/1048576),(767825802497773/33554432),(9000415828505577/67108864),(516055507818373883/1073741824),(630803627886803605/536870912),(17776321812460720125/8589934592),(5801844098515617573/2147483648),(363835190463837840141/137438953472),(535169399082077509803/274877906944),(9337362090327678344185/8796093022208),(1834396833102710492837/4398046511104),(245944970896187211099/2199023255552),(80684998557933096383/4398046511104),(12229484186128971139/8796093022208)],
    ![(777152517505/4194304),(157379090839747/67108864),(1839732372149151/134217728),(420833551189802753/8589934592),(513136257176513815/4294967296),(3606754246773052743/17179869184),(1174673900801140665/4294967296),(147045604127622379815/549755813888),(215925057946684923777/1099511627776),(1880950906284443460475/17592186044416),(369091099353142629023/8796093022208),(6328473418613153729811/562949953421312),(259361916298396189481/140737488355328),(78601895702200655345/562949953421312)],
    ![(25166076229/2097152),(5080420167193/33554432),(59211212380797/67108864),(13505824137939641/4294967296),(16424093415395935/2147483648),(115157370743168517/8589934592),(37421343145375431/2147483648),(4675121450807206971/274877906944),(6853395273607063629/549755813888),(59617793053601837065/8796093022208),(11686161499929232085/4398046511104),(200231026504263266835/281474976710656),(8203452400594270025/70368744177664),(2486306765709757745/281474976710656)],
    ![(1541294755/4194304),(620169368891/134217728),(7204223732703/268435456),(819077630571461/8589934592),(993186243980035/4294967296),(27781577653818267/68719476736),(9006706422419379/17179869184),(280737500918459817/549755813888),(410852944583383599/1099511627776),(7138779357652966265/35184372088832),(1398085430938447141/17592186044416),(11971962851457717075/562949953421312),(490493650091141585/140737488355328),(2379724323003052025/9007199254740992)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row12Lower_00 : Expr := (.add (.literal (4096)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_00 :
    (certificate12Lower.rowExpression ⟨0,by decide⟩).check row12Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row12Lower_01 : Expr := (.add (.literal (106496)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_01 :
    (certificate12Lower.rowExpression ⟨1,by decide⟩).check row12Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row12Lower_02 : Expr := (.add (.literal (1323712)) (.mul .y (.add (.literal (-1152)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_02 :
    (certificate12Lower.rowExpression ⟨2,by decide⟩).check row12Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row12Lower_03 : Expr := (.add (.literal (10469888)) (.mul .y (.add (.literal (-27648)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_03 :
    (certificate12Lower.rowExpression ⟨3,by decide⟩).check row12Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row12Lower_04 : Expr := (.add (.literal (59173777)) (.mul .y (.add (.literal (-316170)) (.mul .y (.add (.literal (324)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_04 :
    (certificate12Lower.rowExpression ⟨4,by decide⟩).check row12Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row12Lower_05 : Expr := (.add (.literal (254394998)) (.mul .y (.add (.literal (-2292444)) (.mul .y (.add (.literal (7128)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_05 :
    (certificate12Lower.rowExpression ⟨5,by decide⟩).check row12Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row12Lower_06 : Expr := (.add (.literal ((13834704481/16))) (.mul .y (.add (.literal ((-378577125/32))) (.mul .y (.add (.literal ((595107/8))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_06 :
    (certificate12Lower.rowExpression ⟨6,by decide⟩).check row12Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row12Lower_07 : Expr := (.add (.literal ((9536605637/4))) (.mul .y (.add (.literal ((-369926649/8))) (.mul .y (.add (.literal ((979695/2))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_07 :
    (certificate12Lower.rowExpression ⟨7,by decide⟩).check row12Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row12Lower_08 : Expr := (.add (.literal ((11119410586427/2048))) (.mul .y (.add (.literal ((-72813451563/512))) (.mul .y (.add (.literal ((584632809/256))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_08 :
    (certificate12Lower.rowExpression ⟨8,by decide⟩).check row12Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row12Lower_09 : Expr := (.add (.literal ((10591393891091/1024))) (.mul .y (.add (.literal ((-90354804291/256))) (.mul .y (.add (.literal ((1026170289/128))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_09 :
    (certificate12Lower.rowExpression ⟨9,by decide⟩).check row12Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row12Lower_10 : Expr := (.add (.literal ((4360485595571053/262144))) (.mul .y (.add (.literal ((-47135324027547/65536))) (.mul .y (.add (.literal ((180243246465/8192))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_10 :
    (certificate12Lower.rowExpression ⟨10,by decide⟩).check row12Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row12Lower_11 : Expr := (.add (.literal ((372348739396205/16384))) (.mul .y (.add (.literal ((-4988969527707/4096))) (.mul .y (.add (.literal ((24770384577/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_11 :
    (certificate12Lower.rowExpression ⟨11,by decide⟩).check row12Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row12Lower_12 : Expr := (.add (.literal ((111097293436921171/4194304))) (.mul .y (.add (.literal ((-14499307573457121/8388608))) (.mul .y (.add (.literal ((363416412471795/4194304))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_12 :
    (certificate12Lower.rowExpression ⟨12,by decide⟩).check row12Lower_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row12Lower_13 : Expr := (.add (.literal ((55350941771537989/2097152))) (.mul .y (.add (.literal ((-8666847759846951/4194304))) (.mul .y (.add (.literal ((267999526120869/2097152))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_13 :
    (certificate12Lower.rowExpression ⟨13,by decide⟩).check row12Lower_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row12Lower_14 : Expr := (.add (.literal ((94352311798479553/4194304))) (.mul .y (.add (.literal ((-280121141721623877/134217728))) (.mul .y (.add (.literal ((41958815989306455/268435456))) (.mul .y (.add (.literal ((167403915/134217728))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_14 :
    (certificate12Lower.rowExpression ⟨14,by decide⟩).check row12Lower_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row12Lower_15 : Expr := (.add (.literal ((17175736075819841/1048576))) (.mul .y (.add (.literal ((-59801942092204143/33554432))) (.mul .y (.add (.literal ((10680707456076933/67108864))) (.mul .y (.add (.literal ((502211745/33554432))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_15 :
    (certificate12Lower.rowExpression ⟨15,by decide⟩).check row12Lower_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row12Lower_16 : Expr := (.add (.literal ((42613566210731659/4194304))) (.mul .y (.add (.literal ((-86229766815252093/67108864))) (.mul .y (.add (.literal ((18123081106990167/134217728))) (.mul .y (.add (.literal ((703196885349/8589934592))) (.mul .y (.add (.literal ((-1506635235/2147483648))) (.mul .y (.add (.literal ((-301327047/268435456))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_16 :
    (certificate12Lower.rowExpression ⟨16,by decide⟩).check row12Lower_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row12Lower_17 : Expr := (.add (.literal ((11202921221180299/2097152))) (.mul .y (.add (.literal ((-26149050721003851/33554432))) (.mul .y (.add (.literal ((6394381656804945/67108864))) (.mul .y (.add (.literal ((1158937303545/4294967296))) (.mul .y (.add (.literal ((-7533176175/1073741824))) (.mul .y (.add (.literal ((-1506635235/134217728))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_17 :
    (certificate12Lower.rowExpression ⟨17,by decide⟩).check row12Lower_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row12Lower_18 : Expr := (.add (.literal ((9915812107987201/4194304))) (.mul .y (.add (.literal ((-53042699713939659/134217728))) (.mul .y (.add (.literal ((14943183122993337/268435456))) (.mul .y (.add (.literal ((5127079704705/8589934592))) (.mul .y (.add (.literal ((-67798585575/2147483648))) (.mul .y (.add (.literal ((-3436032316941/68719476736))) (.mul .y (.add (.literal ((8135830269/17179869184))) (.mul .y (.add (.literal ((3486784401/8589934592))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_18 :
    (certificate12Lower.rowExpression ⟨18,by decide⟩).check row12Lower_18=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 19. -/
private def row12Lower_19 : Expr := (.add (.literal ((457143710844535/524288))) (.mul .y (.add (.literal ((-2786124867903855/16777216))) (.mul .y (.add (.literal ((896404614204069/33554432))) (.mul .y (.add (.literal ((1001912431275/1073741824))) (.mul .y (.add (.literal ((-22599528525/268435456))) (.mul .y (.add (.literal ((-1121840595981/8589934592))) (.mul .y (.add (.literal ((8135830269/2147483648))) (.mul .y (.add (.literal ((3486784401/1073741824))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_19 :
    (certificate12Lower.rowExpression ⟨19,by decide⟩).check row12Lower_19=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 20. -/
private def row12Lower_20 : Expr := (.add (.literal ((1108888048273057/4194304))) (.mul .y (.add (.literal ((-1915395322838751/33554432))) (.mul .y (.add (.literal ((698339371356369/67108864))) (.mul .y (.add (.literal ((4538487539565/4294967296))) (.mul .y (.add (.literal ((-158196699675/1073741824))) (.mul .y (.add (.literal ((-3803048660187/17179869184))) (.mul .y (.add (.literal ((56950811883/4294967296))) (.mul .y (.add (.literal ((6112333054953/549755813888))) (.mul .y (.add (.literal ((-156905298045/1099511627776))) (.mul .y (.add (.literal ((-17433922005/274877906944))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_20 :
    (certificate12Lower.rowExpression ⟨20,by decide⟩).check row12Lower_20=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 21. -/
private def row12Lower_21 : Expr := (.add (.literal ((135628782125707/2097152))) (.mul .y (.add (.literal ((-264434489073603/16777216))) (.mul .y (.add (.literal ((108488067559317/33554432))) (.mul .y (.add (.literal ((1874555559387/2147483648))) (.mul .y (.add (.literal ((-94918019805/536870912))) (.mul .y (.add (.literal ((-2183114455515/8589934592))) (.mul .y (.add (.literal ((56950811883/2147483648))) (.mul .y (.add (.literal ((5840363871675/274877906944))) (.mul .y (.add (.literal ((-470715894135/549755813888))) (.mul .y (.add (.literal ((-52301766015/137438953472))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_21 :
    (certificate12Lower.rowExpression ⟨21,by decide⟩).check row12Lower_21=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 22. -/
private def row12Lower_22 : Expr := (.add (.literal ((52122938290891/4194304))) (.mul .y (.add (.literal ((-457096974278571/134217728))) (.mul .y (.add (.literal ((209679444572985/268435456))) (.mul .y (.add (.literal ((2240366594445/4294967296))) (.mul .y (.add (.literal ((-158196699675/1073741824))) (.mul .y (.add (.literal ((-6865736765895/34359738368))) (.mul .y (.add (.literal ((284754059415/8589934592))) (.mul .y (.add (.literal ((13581025241895/549755813888))) (.mul .y (.add (.literal ((-2353579470675/1099511627776))) (.mul .y (.add (.literal ((-31433361375015/35184372088832))) (.mul .y (.add (.literal ((345191655699/17592186044416))) (.mul .y (.add (.literal ((31381059609/8796093022208))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_22 :
    (certificate12Lower.rowExpression ⟨22,by decide⟩).check row12Lower_22=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 23. -/
private def row12Lower_23 : Expr := (.add (.literal ((1890400257473/1048576))) (.mul .y (.add (.literal ((-18580704610995/33554432))) (.mul .y (.add (.literal ((9474653864241/67108864))) (.mul .y (.add (.literal ((235872116235/1073741824))) (.mul .y (.add (.literal ((-22599528525/268435456))) (.mul .y (.add (.literal ((-910309008987/8589934592))) (.mul .y (.add (.literal ((56950811883/2147483648))) (.mul .y (.add (.literal ((2444235865101/137438953472))) (.mul .y (.add (.literal ((-784526490225/274877906944))) (.mul .y (.add (.literal ((-9117941208615/8796093022208))) (.mul .y (.add (.literal ((345191655699/4398046511104))) (.mul .y (.add (.literal ((31381059609/2199023255552))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_23 :
    (certificate12Lower.rowExpression ⟨23,by decide⟩).check row12Lower_23=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 24. -/
private def row12Lower_24 : Expr := (.add (.literal ((777152517505/4194304))) (.mul .y (.add (.literal ((-4268632801293/67108864))) (.mul .y (.add (.literal ((2406875687703/134217728))) (.mul .y (.add (.literal ((530837814465/8589934592))) (.mul .y (.add (.literal ((-67798585575/2147483648))) (.mul .y (.add (.literal ((-621035043867/17179869184))) (.mul .y (.add (.literal ((56950811883/4294967296))) (.mul .y (.add (.literal ((4208548772007/549755813888))) (.mul .y (.add (.literal ((-2353579470675/1099511627776))) (.mul .y (.add (.literal ((-10617258501045/17592186044416))) (.mul .y (.add (.literal ((1035574967097/8796093022208))) (.mul .y (.add (.literal ((8378742915603/562949953421312))) (.mul .y (.add (.literal ((-282429536481/281474976710656))) (.mul .y (.literal 0)))))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_24 :
    (certificate12Lower.rowExpression ⟨24,by decide⟩).check row12Lower_24=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 25. -/
private def row12Lower_25 : Expr := (.add (.literal ((25166076229/2097152))) (.mul .y (.add (.literal ((-154123688439/33554432))) (.mul .y (.add (.literal ((95654635749/67108864))) (.mul .y (.add (.literal ((44696845305/4294967296))) (.mul .y (.add (.literal ((-7533176175/1073741824))) (.mul .y (.add (.literal ((-61169390541/8589934592))) (.mul .y (.add (.literal ((8135830269/2147483648))) (.mul .y (.add (.literal ((484663031739/274877906944))) (.mul .y (.add (.literal ((-470715894135/549755813888))) (.mul .y (.add (.literal ((-1307544150375/8796093022208))) (.mul .y (.add (.literal ((345191655699/4398046511104))) (.mul .y (.add (.literal ((345191655699/281474976710656))) (.mul .y (.add (.literal ((-282429536481/140737488355328))) (.mul .y (.literal 0)))))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_25 :
    (certificate12Lower.rowExpression ⟨25,by decide⟩).check row12Lower_25=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 26. -/
private def row12Lower_26 : Expr := (.add (.literal ((1541294755/4194304))) (.mul .y (.add (.literal ((-21009249189/134217728))) (.mul .y (.add (.literal ((14302296279/268435456))) (.mul .y (.add (.literal ((6796598949/8589934592))) (.mul .y (.add (.literal ((-1506635235/2147483648))) (.mul .y (.add (.literal ((-41884459533/68719476736))) (.mul .y (.add (.literal ((8135830269/17179869184))) (.mul .y (.add (.literal ((87169610025/549755813888))) (.mul .y (.add (.literal ((-156905298045/1099511627776))) (.mul .y (.add (.literal ((-191773142055/35184372088832))) (.mul .y (.add (.literal ((345191655699/17592186044416))) (.mul .y (.add (.literal ((-1663196159277/562949953421312))) (.mul .y (.add (.literal ((-282429536481/281474976710656))) (.mul .y (.add (.literal ((2541865828329/9007199254740992))) (.mul .y (.literal 0)))))))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Lower_26 :
    (certificate12Lower.rowExpression ⟨26,by decide⟩).check row12Lower_26=true := by kernel_decide

def rows12Lower : Fin (certificate12Lower.degree0+1) → Expr := ![row12Lower_00,row12Lower_01,row12Lower_02,row12Lower_03,row12Lower_04,row12Lower_05,row12Lower_06,row12Lower_07,row12Lower_08,row12Lower_09,row12Lower_10,row12Lower_11,row12Lower_12,row12Lower_13,row12Lower_14,row12Lower_15,row12Lower_16,row12Lower_17,row12Lower_18,row12Lower_19,row12Lower_20,row12Lower_21,row12Lower_22,row12Lower_23,row12Lower_24,row12Lower_25,row12Lower_26]

theorem rowsChecked12Lower : ∀ i, (certificate12Lower.rowExpression i).check (rows12Lower i)=true := by
  intro i
  fin_cases i
  · exact checked12Lower_00
  · exact checked12Lower_01
  · exact checked12Lower_02
  · exact checked12Lower_03
  · exact checked12Lower_04
  · exact checked12Lower_05
  · exact checked12Lower_06
  · exact checked12Lower_07
  · exact checked12Lower_08
  · exact checked12Lower_09
  · exact checked12Lower_10
  · exact checked12Lower_11
  · exact checked12Lower_12
  · exact checked12Lower_13
  · exact checked12Lower_14
  · exact checked12Lower_15
  · exact checked12Lower_16
  · exact checked12Lower_17
  · exact checked12Lower_18
  · exact checked12Lower_19
  · exact checked12Lower_20
  · exact checked12Lower_21
  · exact checked12Lower_22
  · exact checked12Lower_23
  · exact checked12Lower_24
  · exact checked12Lower_25
  · exact checked12Lower_26


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity12Lower : slackRowsIdentityCheck 12 (-1) certificate12Lower rows12Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted12Lower : certificate12Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive12Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 12 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate12Lower rows12Lower rowsChecked12Lower identity12Lower accepted12Lower hz hz1 ha

end polyak.Certificates.P1Slacks
