import polyak.Boundary.P1.FiniteRows
import polyak.Numerics.KernelDecide

/-! Article: (p1slackpoly), exact tensor Bernstein annotation for lag 12, sign 1.
Generated from the pinned archive's Chebyshev coefficients; the independent
source recurrence, polynomial identity, and all signs are checked below. -/
namespace polyak.Certificates.P1Slacks
open Boundary.P1 Numerics.TensorBernstein Numerics.BivariateIdentity

/-- Exact positive tensor coefficients, including binomial factors. -/
def certificate12Upper : Certificate where
  degree0 := 22
  degree1 := 11
  coefficient := ![
    ![1024,11264,56320,168960,337920,473088,473088,337920,168960,56320,11264,1024],
    ![22528,247808,1239040,3717120,7434240,10407936,10407936,7434240,3717120,1239040,247808,22528],
    ![234960,2584848,12925104,38776176,77550624,108563616,108551520,77524704,38754576,12915024,2582256,234672],
    ![1545280,17003840,85036480,255126720,510218880,714161280,713919360,509700480,254694720,84834880,16952000,1539520],
    ![7190491,(158299513/2),395911930,(2375798685/2),2375474010,3324296577,3322017048,2370589305,1183828755,(788024645/2),78661286,(14272433/2)],
    ![25176294,277260993,1387271700,4162789125,8323673940,11645084178,11631631536,8294846850,4138766550,1376061165,274378284,24855993],
    ![(17629525947/256),(194267761665/256),(972370886349/256),(2918160483471/256),(2917159898247/128),(4079755264725/128),(4072618898397/128),(2901867684687/128),(2892673460871/256),(960476942469/256),(191209318953/256),(17289698979/256)],
    ![(2412836283/16),(26607923457/16),(133240824525/16),(399928851855/16),(399737986695/8),(558809829333/8),(557430336477/8),(396781930575/8),(395002091655/16),(130941669765/16),(26016712233/16),(2347146147/16)],
    ![(4403180497815/16384),(48599916948855/16384),(243498261493269/16384),(731012872880421/16384),(730553019434667/8192),(1020761313799563/8192),(1017379281805677/8192),(723305808019197/8192),(718934187187971/16384),(237861541503459/16384),(47150474665761/16384),(4242131355249/16384)],
    ![(3228287020321/8192),(35669194289729/8192),(178825353780883/8192),(536981799343107/8192),(536555128347309/4096),(749274467697357/4096),(746066383113723/4096),(529680661382379/4096),(525524354401557/8192),(173478546141493/8192),(34294300896743/8192),(3075521087767/8192)],
    ![(125507333269205/262144),(2776785358962155/524288),(6965750945386169/262144),(41845595842491717/524288),(20902525447478217/131072),(58342019161595631/262144),(29014338952729137/131072),(41133605346090669/262144),(20363259963857721/262144),(13409266463876743/524288),(1321248124594501/262144),(236093654341393/524288)],
    ![(31701018320607/65536),(702332231247489/131072),(1763338969840971/65536),(10596487096800783/131072),(5292171650988603/32768),(14761043408405133/65536),(7331985146216115/32768),(10376329482035271/65536),(5124898698448779/65536),(3364889413060437/131072),(330364733629551/65536),(58779507309171/131072)],
    ![(53315694737437/131072),(37857286495666061/8388608),(380558873097692873/16777216),(1143901546086758937/16777216),(571196687606910957/4194304),(199001618661486669/1048576),(1579448836447009311/8388608),(1115470276223298099/8388608),(274757428577970753/4194304),(179809342424641039/8388608),(70329953126265793/16777216),(6226117826140025/16777216)],
    ![(18623061139595/65536),(13246611071336065/4194304),(133306817318716141/8388608),(400885410530441469/8388608),(200146603838478369/2097152),(69675172561695729/524288),(552212243719691163/4194304),(389173628689792383/4194304),(95588194566288261/2097152),(62329127580452363/4194304),(24269306010431429/8388608),(2136650012729821/8388608)],
    ![(43028364716667/262144),(15333041237651001/8388608),(154494211461044373/16777216),(14875319088095819679/536870912),(14851343898178047153/268435456),(20663326148148015381/268435456),(20439780721705711485/268435456),(3593079483173282547/67108864),(7038471153535164387/268435456),(2285619407867913723/268435456),(442754676888732063/268435456),(77477053584861801/536870912)],
    ![(2548274646687/32768),(910053612879027/1048576),(9182358395631879/2097152),(884677763865500127/67108864),(883165524257626929/33554432),(1227757537456122645/33554432),(1212526256171320125/33554432),(212631762098619171/8388608),(415140125626202211/33554432),(134224963115847099/33554432),(25857853999757247/33554432),(4493562223797417/67108864)],
    ![(1956774005175/65536),(1401020487729429/4194304),(14158230242666865/8388608),(682548663786368265/134217728),(681350608697356215/67108864),(121139348026594872051/8589934592),(59718333663739256373/4294967296),(83564270094751744581/8589934592),(10160649399104904411/2147483648),(13079112818805509901/8589934592),(1252211890568400645/4294967296),(215937287844128475/8589934592)],
    ![(299091794859/32768),(214722173259315/2097152),(2173704718822263/4194304),(104882613678711657/67108864),(104700967861338999/33554432),(18599679378315333081/4294967296),(9153378290771191071/2147483648),(12774029031314109135/4294967296),(1547350782859102545/1073741824),(1981764298698510375/4294967296),(188489476428193935/2147483648),(32227749295752465/4294967296)],
    ![(567589422235/262144),(102174479865245/4194304),(1036375083846353/8388608),(100113315128961789/268435456),(99951300262926003/134217728),(8870924050918690173/8589934592),(4358003607489012411/4294967296),(24259658395976872527/34359738368),(23415834118785209895/68719476736),(7457137377841288381/68719476736),(1408427476676748413/68719476736),(119277970005019153/68719476736)],
    ![(25122140131/65536),(4537348080779/1048576),(46124479752743/2097152),(4460908477705689/67108864),(4454712235072983/33554432),(395077353505598463/2147483648),(193750871853779625/1073741824),(1075471082171864967/8589934592),(1033762693509850215/17179869184),(327341747940589741/17179869184),(61350869549670749/17179869184),(5142311937086881/17179869184)],
    ![(6233039373/131072),(4519630181193/8388608),(46058265019221/16777216),(1115184132516897/134217728),(1114055836955559/67108864),(197478754863562557/8589934592),(96679735121969307/4294967296),(267543781748739711/17179869184),(256061738138706405/34359738368),(5158071197594947461/2199023255552),(239697263683908123/549755813888),(79461022089264483/2199023255552)],
    ![(241036567/65536),(175496919809/4194304),(1793469182189/8388608),(43496312243943/67108864),(43477023992961/33554432),(7702762007424729/4294967296),(3764725336468383/2147483648),(10387381158626241/8589934592),(9897259687978647/17179869184),(198109704612880645/1099511627776),(9125559499561595/274877906944),(2988242582291683/1099511627776)],
    ![(34886005/262144),(12758965981/8388608),(130810569865/16777216),(12715373540895/536870912),(12720189074865/268435456),(563194588881939/8589934592),(274809468952389/4294967296),(1511861126014263/34359738368),(1433823260704743/68719476736),(14254933830849125/2199023255552),(650529296244499/549755813888),(3363480470950985/35184372088832)]]

/-- Exact reduced polynomial annotation for tensor row 0. -/
private def row12Upper_00 : Expr := (.add (.literal (1024)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_00 :
    (certificate12Upper.rowExpression ⟨0,by decide⟩).check row12Upper_00=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 1. -/
private def row12Upper_01 : Expr := (.add (.literal (22528)) (.mul .y (.literal 0)))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_01 :
    (certificate12Upper.rowExpression ⟨1,by decide⟩).check row12Upper_01=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 2. -/
private def row12Upper_02 : Expr := (.add (.literal (234960)) (.mul .y (.add (.literal (288)) (.mul .y (.add (.literal (-576)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_02 :
    (certificate12Upper.rowExpression ⟨2,by decide⟩).check row12Upper_02=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 3. -/
private def row12Upper_03 : Expr := (.add (.literal (1545280)) (.mul .y (.add (.literal (5760)) (.mul .y (.add (.literal (-11520)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_03 :
    (certificate12Upper.rowExpression ⟨3,by decide⟩).check row12Upper_03=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 4. -/
private def row12Upper_04 : Expr := (.add (.literal (7190491)) (.mul .y (.add (.literal ((108711/2))) (.mul .y (.add (.literal (-108630)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_04 :
    (certificate12Upper.rowExpression ⟨4,by decide⟩).check row12Upper_04=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 5. -/
private def row12Upper_05 : Expr := (.add (.literal (25176294)) (.mul .y (.add (.literal (321759)) (.mul .y (.add (.literal (-642060)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_05 :
    (certificate12Upper.rowExpression ⟨5,by decide⟩).check row12Upper_05=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 6. -/
private def row12Upper_06 : Expr := (.add (.literal ((17629525947/256))) (.mul .y (.add (.literal ((42872031/32))) (.mul .y (.add (.literal ((-42675201/16))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_06 :
    (certificate12Upper.rowExpression ⟨6,by decide⟩).check row12Upper_06=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 7. -/
private def row12Upper_07 : Expr := (.add (.literal ((2412836283/16))) (.mul .y (.add (.literal ((8340543/2))) (.mul .y (.add (.literal (-8275905)) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_07 :
    (certificate12Upper.rowExpression ⟨7,by decide⟩).check row12Upper_07=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 8. -/
private def row12Upper_08 : Expr := (.add (.literal ((4403180497815/16384))) (.mul .y (.add (.literal ((82465736445/8192))) (.mul .y (.add (.literal ((-10186894233/512))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_08 :
    (certificate12Upper.rowExpression ⟨8,by decide⟩).check row12Upper_08=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 9. -/
private def row12Upper_09 : Expr := (.add (.literal ((3228287020321/8192))) (.mul .y (.add (.literal ((79018533099/4096))) (.mul .y (.add (.literal ((-9712593711/256))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_09 :
    (certificate12Upper.rowExpression ⟨9,by decide⟩).check row12Upper_09=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 10. -/
private def row12Upper_10 : Expr := (.add (.literal ((125507333269205/262144))) (.mul .y (.add (.literal ((15624027039645/524288))) (.mul .y (.add (.literal ((-15272519618331/262144))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_10 :
    (certificate12Upper.rowExpression ⟨10,by decide⟩).check row12Upper_10=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 11. -/
private def row12Upper_11 : Expr := (.add (.literal ((31701018320607/65536))) (.mul .y (.add (.literal ((4909828194135/131072))) (.mul .y (.add (.literal ((-4766178763089/65536))) (.mul .y (.literal 0)))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_11 :
    (certificate12Upper.rowExpression ⟨11,by decide⟩).check row12Upper_11=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 12. -/
private def row12Upper_12 : Expr := (.add (.literal ((53315694737437/131072))) (.mul .y (.add (.literal ((323037400510413/8388608))) (.mul .y (.add (.literal ((-1244365864071867/16777216))) (.mul .y (.add (.literal ((-18600435/8388608))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_12 :
    (certificate12Upper.rowExpression ⟨12,by decide⟩).check row12Upper_12=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 13. -/
private def row12Upper_13 : Expr := (.add (.literal ((18623061139595/65536))) (.mul .y (.add (.literal ((135976029061185/4194304))) (.mul .y (.add (.literal ((-519053685256359/8388608))) (.mul .y (.add (.literal ((-93002175/4194304))) (.mul .y (.literal 0)))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_13 :
    (certificate12Upper.rowExpression ⟨13,by decide⟩).check row12Upper_13=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 14. -/
private def row12Upper_14 : Expr := (.add (.literal ((43028364716667/262144))) (.mul .y (.add (.literal ((187056857384217/8388608))) (.mul .y (.add (.literal ((-706769489307807/16777216))) (.mul .y (.add (.literal ((-53306189505/536870912))) (.mul .y (.add (.literal ((-167403915/268435456))) (.mul .y (.add (.literal ((33480783/16777216))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_14 :
    (certificate12Upper.rowExpression ⟨14,by decide⟩).check row12Upper_14=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 15. -/
private def row12Upper_15 : Expr := (.add (.literal ((2548274646687/32768))) (.mul .y (.add (.literal ((13060937245203/1048576))) (.mul .y (.add (.literal ((-48787105610421/2097152))) (.mul .y (.add (.literal ((-17593354305/67108864))) (.mul .y (.add (.literal ((-167403915/33554432))) (.mul .y (.add (.literal ((33480783/2097152))) (.mul .y (.literal 0)))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_15 :
    (certificate12Upper.rowExpression ⟨15,by decide⟩).check row12Upper_15=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 16. -/
private def row12Upper_16 : Expr := (.add (.literal ((1956774005175/65536))) (.mul .y (.add (.literal ((23451588086229/4194304))) (.mul .y (.add (.literal ((-86490515489715/8388608))) (.mul .y (.add (.literal ((-60656018535/134217728))) (.mul .y (.add (.literal ((-1171827405/67108864))) (.mul .y (.add (.literal ((476665907571/8589934592))) (.mul .y (.add (.literal ((301327047/1073741824))) (.mul .y (.add (.literal ((-387420489/536870912))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_16 :
    (certificate12Upper.rowExpression ⟨16,by decide⟩).check row12Upper_16=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 17. -/
private def row12Upper_17 : Expr := (.add (.literal ((299091794859/32768))) (.mul .y (.add (.literal ((4161549678579/2097152))) (.mul .y (.add (.literal ((-15132510556677/4194304))) (.mul .y (.add (.literal ((-35657033895/67108864))) (.mul .y (.add (.literal ((-1171827405/33554432))) (.mul .y (.add (.literal ((470036712537/4294967296))) (.mul .y (.add (.literal ((903981141/536870912))) (.mul .y (.add (.literal ((-1162261467/268435456))) (.mul .y (.literal 0)))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_17 :
    (certificate12Upper.rowExpression ⟨17,by decide⟩).check row12Upper_17=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 18. -/
private def row12Upper_18 : Expr := (.add (.literal ((567589422235/262144))) (.mul .y (.add (.literal ((2278741551885/4194304))) (.mul .y (.add (.literal ((-8157130324947/8388608))) (.mul .y (.add (.literal ((-115787707875/268435456))) (.mul .y (.add (.literal ((-5859137025/134217728))) (.mul .y (.add (.literal ((1150232299965/8589934592))) (.mul .y (.add (.literal ((4519905705/1073741824))) (.mul .y (.add (.literal ((-367662044061/34359738368))) (.mul .y (.add (.literal ((-3486784401/68719476736))) (.mul .y (.add (.literal ((1937102445/17179869184))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_18 :
    (certificate12Upper.rowExpression ⟨18,by decide⟩).check row12Upper_18=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 19. -/
private def row12Upper_19 : Expr := (.add (.literal ((25122140131/65536))) (.mul .y (.add (.literal ((115851417723/1048576))) (.mul .y (.add (.literal ((-407515232277/2097152))) (.mul .y (.add (.literal ((-16014974535/67108864))) (.mul .y (.add (.literal ((-1171827405/33554432))) (.mul .y (.add (.literal ((223417264959/2147483648))) (.mul .y (.add (.literal ((1506635235/268435456))) (.mul .y (.add (.literal ((-119712931101/8589934592))) (.mul .y (.add (.literal ((-3486784401/17179869184))) (.mul .y (.add (.literal ((1937102445/4294967296))) (.mul .y (.literal 0)))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_19 :
    (certificate12Upper.rowExpression ⟨19,by decide⟩).check row12Upper_19=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 20. -/
private def row12Upper_20 : Expr := (.add (.literal ((6233039373/131072))) (.mul .y (.add (.literal ((131570462601/8388608))) (.mul .y (.add (.literal ((-453741418719/16777216))) (.mul .y (.add (.literal ((-11550870135/134217728))) (.mul .y (.add (.literal ((-1171827405/67108864))) (.mul .y (.add (.literal ((430261542333/8589934592))) (.mul .y (.add (.literal ((4519905705/1073741824))) (.mul .y (.add (.literal ((-173176958583/17179869184))) (.mul .y (.add (.literal ((-10460353203/34359738368))) (.mul .y (.add (.literal ((1449340049349/2199023255552))) (.mul .y (.add (.literal ((3486784401/1099511627776))) (.mul .y (.add (.literal ((-3486784401/549755813888))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_20 :
    (certificate12Upper.rowExpression ⟨20,by decide⟩).check row12Upper_20=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 21. -/
private def row12Upper_21 : Expr := (.add (.literal ((241036567/65536))) (.mul .y (.add (.literal ((5807176641/4194304))) (.mul .y (.add (.literal ((-19571782311/8388608))) (.mul .y (.add (.literal ((-1224971505/67108864))) (.mul .y (.add (.literal ((-167403915/33554432))) (.mul .y (.add (.literal ((58624851033/4294967296))) (.mul .y (.add (.literal ((903981141/536870912))) (.mul .y (.add (.literal ((-32930741565/8589934592))) (.mul .y (.add (.literal ((-3486784401/17179869184))) (.mul .y (.add (.literal ((457543597509/1099511627776))) (.mul .y (.add (.literal ((3486784401/549755813888))) (.mul .y (.add (.literal ((-3486784401/274877906944))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_21 :
    (certificate12Upper.rowExpression ⟨21,by decide⟩).check row12Upper_21=true := by kernel_decide

/-- Exact reduced polynomial annotation for tensor row 22. -/
private def row12Upper_22 : Expr := (.add (.literal ((34886005/262144))) (.mul .y (.add (.literal ((479092221/8388608))) (.mul .y (.add (.literal ((-1570012155/16777216))) (.mul .y (.add (.literal ((-927364545/536870912))) (.mul .y (.add (.literal ((-167403915/268435456))) (.mul .y (.add (.literal ((13827563379/8589934592))) (.mul .y (.add (.literal ((301327047/1073741824))) (.mul .y (.add (.literal ((-20533285917/34359738368))) (.mul .y (.add (.literal ((-3486784401/68719476736))) (.mul .y (.add (.literal ((209594484549/2199023255552))) (.mul .y (.add (.literal ((3486784401/1099511627776))) (.mul .y (.add (.literal ((-191773142055/35184372088832))) (.mul .y (.literal 0)))))))))))))))))))))))))

/-- This row reduction is checked independently of the outer polynomial identity. -/
private theorem checked12Upper_22 :
    (certificate12Upper.rowExpression ⟨22,by decide⟩).check row12Upper_22=true := by kernel_decide

def rows12Upper : Fin (certificate12Upper.degree0+1) → Expr := ![row12Upper_00,row12Upper_01,row12Upper_02,row12Upper_03,row12Upper_04,row12Upper_05,row12Upper_06,row12Upper_07,row12Upper_08,row12Upper_09,row12Upper_10,row12Upper_11,row12Upper_12,row12Upper_13,row12Upper_14,row12Upper_15,row12Upper_16,row12Upper_17,row12Upper_18,row12Upper_19,row12Upper_20,row12Upper_21,row12Upper_22]

theorem rowsChecked12Upper : ∀ i, (certificate12Upper.rowExpression i).check (rows12Upper i)=true := by
  intro i
  fin_cases i
  · exact checked12Upper_00
  · exact checked12Upper_01
  · exact checked12Upper_02
  · exact checked12Upper_03
  · exact checked12Upper_04
  · exact checked12Upper_05
  · exact checked12Upper_06
  · exact checked12Upper_07
  · exact checked12Upper_08
  · exact checked12Upper_09
  · exact checked12Upper_10
  · exact checked12Upper_11
  · exact checked12Upper_12
  · exact checked12Upper_13
  · exact checked12Upper_14
  · exact checked12Upper_15
  · exact checked12Upper_16
  · exact checked12Upper_17
  · exact checked12Upper_18
  · exact checked12Upper_19
  · exact checked12Upper_20
  · exact checked12Upper_21
  · exact checked12Upper_22


/-- The reduced annotation expands to the independently specified lag source. -/
theorem identity12Upper : slackRowsIdentityCheck 12 (1) certificate12Upper rows12Upper=true := by kernel_decide

/-- Every tensor coefficient is strictly positive. -/
theorem accepted12Upper : certificate12Upper.check=true := by kernel_decide

/-- The actual scaled lag is positive on the entire physical rectangle. -/
theorem positive12Upper {z a : ℝ} (hz : 0<z) (hz1 : z≤3/4)
    (ha : -z/2≤a ∧ a≤0) : 0<scaledSlack 12 (1) z a :=
  by simpa using scaledSlack_pos_of_rows certificate12Upper rows12Upper rowsChecked12Upper identity12Upper accepted12Upper hz hz1 ha

end polyak.Certificates.P1Slacks
