import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 11, sign -1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate11Lower : Certificate where
  degree0 := 24
  degree1 := 12
  coefficient := ![
    ![2048,24576,135168,450560,1013760,1622016,1892352,1622016,1013760,450560,135168,24576,2048],
    ![49152,589824,3244032,10813440,24330240,38928384,45416448,38928384,24330240,10813440,3244032,589824,49152],
    ![561792,6740928,37071936,123562560,277992000,444749184,518829696,444673152,277896960,123499200,37046592,6735168,561216],
    ![4069120,48816768,268422528,894509440,2012123520,3218561280,3754012416,3216888576,2010032640,893115520,267864960,48690048,4056448],
    ![20965899,251458542,1382294790,4605225870,10356306705,16561370268,19311427044,16543935180,10334512845,4590696630,1376483094,250137702,20833815],
    ![81769692,980365464,5387223672,17941468440,40332454740,64474607664,75153547728,64360084464,40189300740,17846032440,5349049272,971689464,80902092],
    ![(2006294881/8),(48086117943/16),(528233724561/32),(219800470895/4),(3951071356005/32),(1578296629557/8),(3677724521121/16),(787020804729/4),(1964898127755/16),(872110183415/16),(522560364429/32),(5930177241/2),(7896239521/32)],
    ![(2481169545/4),(59434050159/8),(652523239449/16),(271364509575/2),(4875219767565/16),(1946360032605/4),(4532828639913/8),(969465173121/2),(2419035667875/8),(1073075227695/8),(642616990965/16),7288542513,(9699536169/16)],
    ![(10312749745929/8192),(30858141128247/2048),(338561449992009/4096),(562810723932555/2048),(5052217582699335/8192),(1007836990359831/1024),(2345559357256479/2048),(1002651719075847/1024),(5000364869859495/8192),(554168605125915/2048),(331647754946697/4096),(30072493964007/2048),(9998490880233/8192)],
    ![(1086339182345/512),(3248008487223/128),(35607594220617/256),(59146159334795/128),(530525962503495/512),(105749099756055/64),(245921219993631/128),(105042318938631/64),(523458154329255/512),(57968191305755/128),(34665219797385/256),(3140920484583/128),(1043503981289/512)],
    ![(1569903596242149/524288),(9379041976067139/262144),(25682063722001811/131072),(170483361342979965/262144),(763910606175605505/524288),(304267340822656527/131072),(11046121970428377/4096),(301700256426093357/131072),(751075184192789655/524288),(166204887348708015/262144),(24826368923147421/131072),(8990089794769689/262144),(1492113159982659/524288)],
    ![(932482215294531/262144),(5565115566642645/131072),(15222890230972677/65536),(100949492136506475/131072),(451880057303314695/262144),(179803493998514793/65536),(6521065070525775/2048),(177932038157616699/65536),(442522778098824225/262144),(97830399068342985/131072),(14599071617339979/65536),(5281561651355055/131072),(875771432237013/262144)],
    ![(1870193221648999/524288),(11148314163370449/262144),(30459736869957057/131072),(201758712795156335/262144),(902102222916537435/524288),(358542460845485397/131072),(12989024929558587/4096),(354024700833836799/131072),(879513422858294445/524288),(194229112775742005/262144),(28953816866074191/131072),(10463805070696419/262144),(1733291403114193/524288)],
    ![(396037272034407/131072),(2357680737691089/65536),(6433319512799937/32768),(42558049606773615/65536),(190043574398964315/131072),(75438655555778901/32768),(2729568576903147/1024),(74305963134565119/32768),(184380112292895405/131072),(40670228904750645/65536),(6055755372395343/32768),(2186060673870819/65536),(361713259270353/131072)],
    ![(1131760810936173/524288),(6727637508882939/262144),(75082924453306765707/536870912),(61997807755132317345/134217728),(552925825941023959905/536870912),(27397930091819630157/16777216),(506873357652721687047/268435456),(107657162578090956393/67108864),(266790124028340746865/268435456),(459168318566415015/1048576),(69924103692184162647/536870912),(3151435588917606693/134217728),(1041677144313861837/536870912)],
    ![(339726529407853/262144),(2016156476062203/131072),(22464790388830934967/268435456),(18520407742834491685/67108864),(164918124412684814565/268435456),(8159464605410896257/8388608),(150730694600192541219/134217728),(31968353292590336013/33554432),(79111536579909102645/134217728),(135973170920464595/524288),(20679443428243445427/268435456),(930831949240735161/67108864),(307303900349415937/268435456)],
    ![(340668819328455/524288),(2018069951370993/262144),(22446052082416170351/536870912),(18472748283778436685/134217728),(2627433301811599193895/8589934592),(519119779645407105801/1073741824),(1196800520567857364313/2147483648),(506870848355364826551/1073741824),(1252471997105006261445/4294967296),(137574544704705500895/1073741824),(81618255897760636317/2147483648),(7338065500268423721/1073741824),(4839158835691650567/8589934592)],
    ![(17668895559489/65536),(104457127677255/32768),(1159545661222102821/67108864),(952463636829706095/16777216),(135220463746252136775/1073741824),(26668515993026875785/134217728),(61376519399002068681/268435456),(25951212724314106071/134217728),(64023716371017998565/536870912),(7021956743351455455/134217728),(4159981021895851221/268435456),(373515338705983353/134217728),(246014375736720807/1073741824)],
    ![(47908536914503/524288),(282601757609457/262144),(1565144869086497283/268435456),(1282933833876198665/67108864),(90884418776701723305/2147483648),(17889648406281125919/268435456),(657534886008023660847/8589934592),(1110116084274966764997/17179869184),(1367097253460866955871/34359738368),(74853323441738640953/4294967296),(88562190907385488095/17179869184),(15882623414399816619/17179869184),(2612142581366203711/34359738368)],
    ![(6511462324077/262144),(38315433910779/131072),(211699401243777333/134217728),(173129977964906655/33554432),(12237735129189389145/1073741824),(2403819038409612255/134217728),(88177150648485175725/4294967296),(148592261368135563471/8589934592),(182673416416670615133/17179869184),(9986129523292194699/2147483648),(11798073074882820573/8589934592),(2113160394911325057/8589934592),(347160118966141341/17179869184)],
    ![(2765426386029/524288),(16228593158139/262144),(89431466417871363/268435456),(72954490197363465/67108864),(10288946487155194485/4294967296),(2016455751994695867/536870912),(36905669460151542729/8589934592),(62070117937250620779/17179869184),(2437455183183198278613/1099511627776),(532139313782205615381/549755813888),(156954719126223577647/549755813888),(28079241797379309417/549755813888),(4608640848817482249/1099511627776)],
    ![(110263565927/131072),(645139194321/65536),(3544975845998373/67108864),(2883903030989935/16777216),(405665987782788945/1073741824),(79309874664138303/134217728),(1448282017845623667/2147483648),(2430825173258259897/4294967296),(95283484005518621973/274877906944),(20769400198363197461/137438953472),(6117968391015574383/137438953472),(1093396162360207785/137438953472),(179331817963285321/274877906944)],
    ![(49587048807/524288),(289173306321/262144),(3167904649917807/536870912),(2569387674193485/134217728),(90100118480936085/2147483648),(17568783682936335/268435456),(640114962170939073/8589934592),(1072098927403883019/17179869184),(20973650593421059119/549755813888),(4564857600151441023/274877906944),(42979452364287381483/8796093022208),(15350620453968593925/17592186044416),(1258387622625329679/17592186044416)],
    ![(1748128323/262144),(10157383125/131072),(110885919274935/268435456),(89637895048485/67108864),(3133566774852075/1073741824),(609283007092953/134217728),(22142699817756525/4294967296),(37004408982928719/8589934592),(722616746061248901/274877906944),(157059054802214997/137438953472),(1477405145516155947/4398046511104),(527450017161891717/8796093022208),(43242431304687567/8796093022208)],
    ![(116013349/524288),(671374275/262144),(7300831351179/536870912),(5880134311585/134217728),(819420163239015/8589934592),(158832731390985/1073741824),(1439181869336547/8589934592),(2399729192834805/17179869184),(93561099320851605/1099511627776),(20311620294129685/549755813888),(95478835973003067/8796093022208),(34089250471403109/17592186044416),(89496239762632447/562949953421312)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row11Lower_00 : Expr := (.add (.literal (2048)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_00 :
    (certificate11Lower.rowExpression ⟨0,by decide⟩).check row11Lower_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row11Lower_01 : Expr := (.add (.literal (49152)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_01 :
    (certificate11Lower.rowExpression ⟨1,by decide⟩).check row11Lower_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row11Lower_02 : Expr := (.add (.literal (561792)) (.mul .y (.add (.literal (-576)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_02 :
    (certificate11Lower.rowExpression ⟨2,by decide⟩).check row11Lower_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row11Lower_03 : Expr := (.add (.literal (4069120)) (.mul .y (.add (.literal (-12672)) (.mul .y (.literal 0)))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_03 :
    (certificate11Lower.rowExpression ⟨3,by decide⟩).check row11Lower_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row11Lower_04 : Expr := (.add (.literal (20965899)) (.mul .y (.add (.literal (-132246)) (.mul .y (.add (.literal (162)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_04 :
    (certificate11Lower.rowExpression ⟨4,by decide⟩).check row11Lower_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row11Lower_05 : Expr := (.add (.literal (81769692)) (.mul .y (.add (.literal (-870840)) (.mul .y (.add (.literal (3240)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_05 :
    (certificate11Lower.rowExpression ⟨5,by decide⟩).check row11Lower_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row11Lower_06 : Expr := (.add (.literal ((2006294881/8))) (.mul .y (.add (.literal ((-64959201/16))) (.mul .y (.add (.literal ((978399/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_06 :
    (certificate11Lower.rowExpression ⟨6,by decide⟩).check row11Lower_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row11Lower_07 : Expr := (.add (.literal ((2481169545/4))) (.mul .y (.add (.literal ((-114018921/8))) (.mul .y (.add (.literal ((2895831/16))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_07 :
    (certificate11Lower.rowExpression ⟨7,by decide⟩).check row11Lower_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row11Lower_08 : Expr := (.add (.literal ((10312749745929/8192))) (.mul .y (.add (.literal ((-20027027385/512))) (.mul .y (.add (.literal ((385848279/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_08 :
    (certificate11Lower.rowExpression ⟨8,by decide⟩).check row11Lower_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row11Lower_09 : Expr := (.add (.literal ((1086339182345/512))) (.mul .y (.add (.literal ((-2752264953/32))) (.mul .y (.add (.literal ((75064887/32))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_09 :
    (certificate11Lower.rowExpression ⟨9,by decide⟩).check row11Lower_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row11Lower_10 : Expr := (.add (.literal ((1569903596242149/524288))) (.mul .y (.add (.literal ((-40379601385755/262144))) (.mul .y (.add (.literal ((742191628005/131072))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_10 :
    (certificate11Lower.rowExpression ⟨10,by decide⟩).check row11Lower_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row11Lower_11 : Expr := (.add (.literal ((932482215294531/262144))) (.mul .y (.add (.literal ((-29777725124541/131072))) (.mul .y (.add (.literal ((711166797891/65536))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_11 :
    (certificate11Lower.rowExpression ⟨11,by decide⟩).check row11Lower_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row11Lower_12 : Expr := (.add (.literal ((1870193221648999/524288))) (.mul .y (.add (.literal ((-72845166523545/262144))) (.mul .y (.add (.literal ((2197128628071/131072))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_12 :
    (certificate11Lower.rowExpression ⟨12,by decide⟩).check row11Lower_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row11Lower_13 : Expr := (.add (.literal ((396037272034407/131072))) (.mul .y (.add (.literal ((-18542894515353/65536))) (.mul .y (.add (.literal ((690444066663/32768))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_13 :
    (certificate11Lower.rowExpression ⟨13,by decide⟩).check row11Lower_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row11Lower_14 : Expr := (.add (.literal ((1131760810936173/524288))) (.mul .y (.add (.literal ((-62927356734099/262144))) (.mul .y (.add (.literal ((11629299502231947/536870912))) (.mul .y (.add (.literal ((167403915/268435456))) (.mul .y (.add (.literal ((167403915/134217728))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_14 :
    (certificate11Lower.rowExpression ⟨14,by decide⟩).check row11Lower_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row11Lower_15 : Expr := (.add (.literal ((339726529407853/262144))) (.mul .y (.add (.literal ((-22202700384915/131072))) (.mul .y (.add (.literal ((4895059601962935/268435456))) (.mul .y (.add (.literal ((837019575/134217728))) (.mul .y (.add (.literal ((837019575/67108864))) (.mul .y (.literal 0)))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_15 :
    (certificate11Lower.rowExpression ⟨15,by decide⟩).check row11Lower_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row11Lower_16 : Expr := (.add (.literal ((340668819328455/524288))) (.mul .y (.add (.literal ((-25942964599737/262144))) (.mul .y (.add (.literal ((6733703424742767/536870912))) (.mul .y (.add (.literal ((7533176175/268435456))) (.mul .y (.add (.literal ((477603369495/8589934592))) (.mul .y (.add (.literal ((-301327047/536870912))) (.mul .y (.add (.literal ((-301327047/536870912))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_16 :
    (certificate11Lower.rowExpression ⟨16,by decide⟩).check row11Lower_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row11Lower_17 : Expr := (.add (.literal ((17668895559489/65536))) (.mul .y (.add (.literal ((-1556245679679/32768))) (.mul .y (.add (.literal ((470126401406757/67108864))) (.mul .y (.add (.literal ((2511058725/33554432))) (.mul .y (.add (.literal ((156187852695/1073741824))) (.mul .y (.add (.literal ((-301327047/67108864))) (.mul .y (.add (.literal ((-301327047/67108864))) (.mul .y (.literal 0)))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_17 :
    (certificate11Lower.rowExpression ⟨17,by decide⟩).check row11Lower_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row11Lower_18 : Expr := (.add (.literal ((47908536914503/524288))) (.mul .y (.add (.literal ((-4849463877561/262144))) (.mul .y (.add (.literal ((843950788459011/268435456))) (.mul .y (.add (.literal ((17577411075/134217728))) (.mul .y (.add (.literal ((530837814465/2147483648))) (.mul .y (.add (.literal ((-2109289329/134217728))) (.mul .y (.add (.literal ((-132282573633/8589934592))) (.mul .y (.add (.literal ((3486784401/17179869184))) (.mul .y (.add (.literal ((3486784401/34359738368))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_18 :
    (certificate11Lower.rowExpression ⟨18,by decide⟩).check row11Lower_18=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 19. -/
private def row11Lower_19 : Expr := (.add (.literal ((6511462324077/262144))) (.mul .y (.add (.literal ((-753340033683/131072))) (.mul .y (.add (.literal ((149688527972661/134217728))) (.mul .y (.add (.literal ((10546446645/67108864))) (.mul .y (.add (.literal ((305846952705/1073741824))) (.mul .y (.add (.literal ((-2109289329/67108864))) (.mul .y (.add (.literal ((-126858686787/4294967296))) (.mul .y (.add (.literal ((10460353203/8589934592))) (.mul .y (.add (.literal ((10460353203/17179869184))) (.mul .y (.literal 0)))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_19 :
    (certificate11Lower.rowExpression ⟨19,by decide⟩).check row11Lower_19=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 20. -/
private def row11Lower_20 : Expr := (.add (.literal ((2765426386029/524288))) (.mul .y (.add (.literal ((-363965158035/262144))) (.mul .y (.add (.literal ((81881521285635/268435456))) (.mul .y (.add (.literal ((17577411075/134217728))) (.mul .y (.add (.literal ((966757609125/4294967296))) (.mul .y (.add (.literal ((-10546446645/268435456))) (.mul .y (.add (.literal ((-296807141295/8589934592))) (.mul .y (.add (.literal ((52301766015/17179869184))) (.mul .y (.add (.literal ((1579513333653/1099511627776))) (.mul .y (.add (.literal ((-17433922005/549755813888))) (.mul .y (.add (.literal ((-3486784401/549755813888))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_20 :
    (certificate11Lower.rowExpression ⟨20,by decide⟩).check row11Lower_20=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 21. -/
private def row11Lower_21 : Expr := (.add (.literal ((110263565927/131072))) (.mul .y (.add (.literal ((-16442201241/65536))) (.mul .y (.add (.literal ((4154380971813/67108864))) (.mul .y (.add (.literal ((2511058725/33554432))) (.mul .y (.add (.literal ((129068418465/1073741824))) (.mul .y (.add (.literal ((-2109289329/67108864))) (.mul .y (.add (.literal ((-53937541413/2147483648))) (.mul .y (.add (.literal ((17433922005/4294967296))) (.mul .y (.add (.literal ((463742325333/274877906944))) (.mul .y (.add (.literal ((-17433922005/137438953472))) (.mul .y (.add (.literal ((-3486784401/137438953472))) (.mul .y (.literal 0)))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_21 :
    (certificate11Lower.rowExpression ⟨21,by decide⟩).check row11Lower_21=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 22. -/
private def row11Lower_22 : Expr := (.add (.literal ((49587048807/524288))) (.mul .y (.add (.literal ((-8348986521/262144))) (.mul .y (.add (.literal ((4699511690607/536870912))) (.mul .y (.add (.literal ((7533176175/268435456))) (.mul .y (.add (.literal ((88891478865/2147483648))) (.mul .y (.add (.literal ((-2109289329/134217728))) (.mul .y (.add (.literal ((-94315365711/8589934592))) (.mul .y (.add (.literal ((52301766015/17179869184))) (.mul .y (.add (.literal ((554398719759/549755813888))) (.mul .y (.add (.literal ((-52301766015/274877906944))) (.mul .y (.add (.literal ((-240588123669/8796093022208))) (.mul .y (.add (.literal ((31381059609/17592186044416))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_22 :
    (certificate11Lower.rowExpression ⟨22,by decide⟩).check row11Lower_22=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 23. -/
private def row11Lower_23 : Expr := (.add (.literal ((1748128323/262144))) (.mul .y (.add (.literal ((-331386813/131072))) (.mul .y (.add (.literal ((205896816567/268435456))) (.mul .y (.add (.literal ((837019575/134217728))) (.mul .y (.add (.literal ((8872407495/1073741824))) (.mul .y (.add (.literal ((-301327047/67108864))) (.mul .y (.add (.literal ((-11149100739/4294967296))) (.mul .y (.add (.literal ((10460353203/8589934592))) (.mul .y (.add (.literal ((73222472421/274877906944))) (.mul .y (.add (.literal ((-17433922005/137438953472))) (.mul .y (.add (.literal ((-17433922005/4398046511104))) (.mul .y (.add (.literal ((31381059609/8796093022208))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_23 :
    (certificate11Lower.rowExpression ⟨23,by decide⟩).check row11Lower_23=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 24. -/
private def row11Lower_24 : Expr := (.add (.literal ((116013349/524288))) (.mul .y (.add (.literal ((-24705819/262144))) (.mul .y (.add (.literal ((16757862795/536870912))) (.mul .y (.add (.literal ((167403915/268435456))) (.mul .y (.add (.literal ((6193944855/8589934592))) (.mul .y (.add (.literal ((-301327047/536870912))) (.mul .y (.add (.literal ((-2109289329/8589934592))) (.mul .y (.add (.literal ((3486784401/17179869184))) (.mul .y (.add (.literal ((17433922005/1099511627776))) (.mul .y (.add (.literal ((-17433922005/549755813888))) (.mul .y (.add (.literal ((38354628411/8796093022208))) (.mul .y (.add (.literal ((31381059609/17592186044416))) (.mul .y (.add (.literal ((-282429536481/562949953421312))) (.mul .y (.literal 0)))))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked11Lower_24 :
    (certificate11Lower.rowExpression ⟨24,by decide⟩).check row11Lower_24=true := by kernel_decide

def rows11Lower : Fin (certificate11Lower.degree0+1) → Expr := ![row11Lower_00,row11Lower_01,row11Lower_02,row11Lower_03,row11Lower_04,row11Lower_05,row11Lower_06,row11Lower_07,row11Lower_08,row11Lower_09,row11Lower_10,row11Lower_11,row11Lower_12,row11Lower_13,row11Lower_14,row11Lower_15,row11Lower_16,row11Lower_17,row11Lower_18,row11Lower_19,row11Lower_20,row11Lower_21,row11Lower_22,row11Lower_23,row11Lower_24]

theorem rowsChecked11Lower : ∀ i, (certificate11Lower.rowExpression i).check (rows11Lower i)=true := by
  intro i
  fin_cases i
  · exact checked11Lower_00
  · exact checked11Lower_01
  · exact checked11Lower_02
  · exact checked11Lower_03
  · exact checked11Lower_04
  · exact checked11Lower_05
  · exact checked11Lower_06
  · exact checked11Lower_07
  · exact checked11Lower_08
  · exact checked11Lower_09
  · exact checked11Lower_10
  · exact checked11Lower_11
  · exact checked11Lower_12
  · exact checked11Lower_13
  · exact checked11Lower_14
  · exact checked11Lower_15
  · exact checked11Lower_16
  · exact checked11Lower_17
  · exact checked11Lower_18
  · exact checked11Lower_19
  · exact checked11Lower_20
  · exact checked11Lower_21
  · exact checked11Lower_22
  · exact checked11Lower_23
  · exact checked11Lower_24


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity11Lower : slackRowsIdentityCheck 11 (-1) certificate11Lower rows11Lower=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted11Lower : certificate11Lower.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive11Lower {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 11 (-1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate11Lower rows11Lower rowsChecked11Lower identity11Lower accepted11Lower hz hz1 ha

end polyak.Certificates.P1Slacks
