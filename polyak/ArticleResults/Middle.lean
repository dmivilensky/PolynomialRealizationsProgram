import polyak.Boundary.P5.Results
import polyak.Boundary.P2.Results
import polyak.Realization.ExplicitSpiral.CertifiedExecution
import polyak.General.CubicSource
import polyak.General.Regions.Quotients
import polyak.General.Multipliers.Results

/-!
Direct statement-level bridges for the middle portion of the article.
The comments record the PDF theorem number and the stable TeX label.
-/
noncomputable section

namespace polyak.ArticleResults
open Set
open scoped Topology

namespace P2Data
open Boundary.P2

/-- Definition B.9 (Data of the arc), TeX `def:p2data`: affine lower remainder. -/
def lowerConstant (z : ℝ) : ℝ :=
  atomA z * atomB z - (2 * u z - G z) * atomB z + G z * (1 - u z ^ 2) - 2 * u z
def lowerLinear (z : ℝ) : ℝ :=
  atomA z ^ 2 - atomB z - (2 * u z - G z) * atomA z + u z ^ 2 - 1
def upperConstant (z : ℝ) : ℝ :=
  (-atomA z ^ 2 * atomB z + atomB z ^ 2 - 2 * u z * atomA z * atomB z -
    (u z ^ 2 - 1 - G z ^ 2) * atomB z + G z ^ 2 * (1 - u z ^ 2)) / G z
def upperLinear (z : ℝ) : ℝ :=
  (-atomA z ^ 3 + 2 * atomA z * atomB z - 2 * u z * (atomA z ^ 2 - atomB z) -
    (u z ^ 2 - 1 - G z ^ 2) * atomA z + 2 * u z) / G z

/-- Definition B.9, TeX `def:p2data`: the lower remainder is an actual division identity. -/
theorem lower_remainder (z c : ℝ) :
    Boundary.normalizedLower (u z) (G z) 1 c = lowerConstant z + lowerLinear z * c +
      (c + 2 * u z - G z - atomA z) * atomPolynomial z c := by
  rw [Boundary.normalizedLower_one]
  unfold lowerConstant lowerLinear atomPolynomial Spectral.g
  ring

/-- Definition B.9, TeX `def:p2data`: the upper remainder is an actual division identity. -/
theorem upper_remainder {z : ℝ} (hz : z ∈ parameterInterval) (c : ℝ) :
    Boundary.normalizedUpper (u z) (G z) 2 c = upperConstant z + upperLinear z * c +
      (c ^ 2 + (-2 * u z - atomA z) * c +
        (u z ^ 2 - 1 - G z ^ 2 + atomA z ^ 2 + 2 * u z * atomA z - atomB z)) /
          G z * atomPolynomial z c := by
  have hg : G z ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_G hz))
  rw [Boundary.normalizedUpper_two]
  unfold upperConstant upperLinear atomPolynomial
  field_simp
  ring

/-- Definition B.9, TeX `def:p2data`: the two affine remainders have a nonzero combined slope. -/
theorem remainder_denominator_nonzero {z : ℝ} (hz : z ∈ parameterInterval) :
    lowerLinear z + upperLinear z ≠ 0 := by
  have hM : M10 z ≠ 0 := by
    have hh := signedPolynomialCheck_ne_zero
      (p := (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : LeanCert.Engine.QPoly))
      (sg := -1) (by kernel_decide) z hz
    have hpoly :
        (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : LeanCert.Engine.QPoly).toPoly =
          M10 (Polynomial.X : Polynomial ℚ) := by
      change (Polynomial.C 160 + Polynomial.X * (Polynomial.C (-704) + Polynomial.X *
        (Polynomial.C 1360 + Polynomial.X * (Polynomial.C (-1472) + Polynomial.X *
        (Polynomial.C 1488 + Polynomial.X * (Polynomial.C (-1376) + Polynomial.X *
        (Polynomial.C 744 + Polynomial.X * (Polynomial.C (-368) + Polynomial.X *
        (Polynomial.C 170 + Polynomial.X * (Polynomial.C (-44) + Polynomial.X *
        (Polynomial.C 5 + Polynomial.X * 0))))))))))) = M10 (Polynomial.X : Polynomial ℚ)
      norm_num [M10]
      simp only [Polynomial.C_ofNat]
      ring
    rw [hpoly] at hh
    simpa [M10, Polynomial.aeval_def] using hh
  have h0 := (parameter_pos hz).ne'
  have hr := (rMinus_pos hz).ne'
  have hp := (rPlus_pos z).ne'
  have hqm := (qMinus_pos z).ne'
  have hqp := (qPlus_pos z).ne'
  have hid : lowerLinear z + upperLinear z =
      -(qMinus z ^ 2 * M10 z) /
        (8 * z ^ 2 * rMinus z ^ 2 * rPlus z ^ 2 * qPlus z) := by
    have h4 : z ^ 4 - 4 = rMinus z * rPlus z := by unfold rMinus rPlus; ring
    have h4' : z ^ 4 + 4 = qMinus z * qPlus z := by unfold qMinus qPlus; ring
    unfold lowerLinear upperLinear atomA atomB G u
    rw [h4, h4']
    field_simp
    unfold qMinus qPlus rMinus rPlus M10
    ring
  rw [hid]
  exact div_ne_zero (neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ hqm) hM))
    (by positivity)

/-- Definition B.9, TeX `def:p2data`: closed rational data are exactly the article's remainder data. -/
theorem remainder_data {z : ℝ} (hz : z ∈ parameterInterval) :
    meanCosine z = -(lowerConstant z + upperConstant z) / (lowerLinear z + upperLinear z) ∧
      d z = -lowerConstant z - lowerLinear z * meanCosine z := by
  have hl := lower1_zero hz
  have hu := upper2_zero hz
  rw [lower1_source] at hl
  rw [upper2_source] at hu
  simp only [moment] at hl hu
  have hG : G z ≠ 0 := ne_of_gt (lt_trans zero_lt_one (one_lt_G hz))
  have hl' : lowerConstant z + lowerLinear z * meanCosine z + d z = 0 := by
    unfold lowerConstant lowerLinear
    linear_combination hl
  have hu' : upperConstant z + upperLinear z * meanCosine z - d z = 0 := by
    unfold upperConstant upperLinear
    field_simp [hG]
    linear_combination hu / 2
  refine ⟨(eq_div_iff (remainder_denominator_nonzero hz)).mpr (by nlinarith [hl', hu']), ?_⟩
  linarith


/-- Lemma B.12 (Sign certificates), TeX `lem:p2certs`: the actual source-linked
parameter, atom, mass, weight, minimizer, slope and endpoint-factor tests
pass the stated single-center Taylor criterion, without invoking a fallback. -/
theorem displayed_taylor_tests :
    (signedTaylorCheck G_lowerCode.numerator (1) = true ∧
      signedTaylorCheck G_lowerCode.denominator (1) = true) ∧
    (signedTaylorCheck G_upperCode.numerator (1) = true ∧
      signedTaylorCheck G_upperCode.denominator (1) = true) ∧
    (signedTaylorCheck u_lowerCode.numerator (1) = true ∧
      signedTaylorCheck u_lowerCode.denominator (1) = true) ∧
    (signedTaylorCheck u_upperCode.numerator (1) = true ∧
      signedTaylorCheck u_upperCode.denominator (1) = true) ∧
    (signedTaylorCheck W_lowerCode.numerator (1) = true ∧
      signedTaylorCheck W_lowerCode.denominator (1) = true) ∧
    (signedTaylorCheck W_upperCode.numerator (1) = true ∧
      signedTaylorCheck W_upperCode.denominator (1) = true) ∧
    (signedTaylorCheck b_negativeCode.numerator (1) = true ∧
      signedTaylorCheck b_negativeCode.denominator (1) = true) ∧
    (signedTaylorCheck midpointCode.numerator (-1) = true ∧
      signedTaylorCheck midpointCode.denominator (-1) = true) ∧
    (signedTaylorCheck mean_root_factorCode.numerator (1) = true ∧
      signedTaylorCheck mean_root_factorCode.denominator (1) = true) ∧
    (signedTaylorCheck d_positiveCode.numerator (-1) = true ∧
      signedTaylorCheck d_positiveCode.denominator (-1) = true) ∧
    (signedTaylorCheck gap_lowerCode.numerator (-1) = true ∧
      signedTaylorCheck gap_lowerCode.denominator (-1) = true) ∧
    (signedTaylorCheck gap_squareCode.numerator (1) = true ∧
      signedTaylorCheck gap_squareCode.denominator (1) = true) ∧
    (signedTaylorCheck tail_gapCode.numerator (-1) = true ∧
      signedTaylorCheck tail_gapCode.denominator (-1) = true) ∧
    (signedTaylorCheck slope_positiveCode.numerator (-1) = true ∧
      signedTaylorCheck slope_positiveCode.denominator (-1) = true) ∧
    (signedTaylorCheck slope_lt_oneCode.numerator (-1) = true ∧
      signedTaylorCheck slope_lt_oneCode.denominator (-1) = true) ∧
    (signedTaylorCheck root_minus_outerCode.numerator (1) = true ∧
      signedTaylorCheck root_minus_outerCode.denominator (1) = true) ∧
    (signedTaylorCheck root_minus_innerCode.numerator (1) = true ∧
      signedTaylorCheck root_minus_innerCode.denominator (1) = true) ∧
    (signedTaylorCheck root_plus_innerCode.numerator (1) = true ∧
      signedTaylorCheck root_plus_innerCode.denominator (1) = true) ∧
    (signedTaylorCheck root_plus_outerCode.numerator (1) = true ∧
      signedTaylorCheck root_plus_outerCode.denominator (1) = true) ∧
    (signedTaylorCheck upper_five_factorCode.numerator (-1) = true ∧
      signedTaylorCheck upper_five_factorCode.denominator (-1) = true) := by
  repeat' constructor
  all_goals kernel_decide

/-- Lemma B.12 (Sign certificates), TeX `lem:p2certs`: the remaining finite-lag
source numerators and denominators satisfy the literal Taylor criterion. -/
theorem finite_lag_taylor_tests :
    (signedTaylorCheck upper1ActualCode.numerator (-1) = true ∧
      signedTaylorCheck upper1ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower2ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower2ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower3ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower3ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower4ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower4ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck upper4ActualCode.numerator (-1) = true ∧
      signedTaylorCheck upper4ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower5ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower5ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower6ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower6ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck upper6ActualCode.numerator (-1) = true ∧
      signedTaylorCheck upper6ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower7ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower7ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck upper7ActualCode.numerator (-1) = true ∧
      signedTaylorCheck upper7ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower8ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower8ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck upper8ActualCode.numerator (-1) = true ∧
      signedTaylorCheck upper8ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck lower9ActualCode.numerator (-1) = true ∧
      signedTaylorCheck lower9ActualCode.denominator (-1) = true) ∧
    (signedTaylorCheck upper9ActualCode.numerator (-1) = true ∧
      signedTaylorCheck upper9ActualCode.denominator (-1) = true) := by
  repeat' constructor
  all_goals kernel_decide

/-- The complete forty-four polynomial factors in the rational sign tests
of Lemma B.12, TeX `lem:p2certs`. Signs are witnesses checked below. -/
def factoredSignPolynomials : List (LeanCert.Engine.QPoly × ℚ) :=
  [
    ((⟨#[5000,20466,0,-10233,1250]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[0,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[12,-20,16,-10,3]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[1280,-9472,33536,-67200,98048,-124352,128576,-114656,89824,-57328,32144,-15544,6128,-2100,524,-74,5]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[-2,-2,1]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[-2,2,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[-4,2,0,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[2,-2,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[640,-2176,1344,10368,-27680,33184,-29968,23616,-14984,8296,-3460,648,42,-34,5]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[17920,-334848,1790720,-5284864,10756096,-16601088,20666368,-21616384,19264832,-14697600,9632416,-5404096,2583296,-1037568,336128,-82576,13990,-1308,35]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[-2,0,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[5138022400,-192015237120,1690057048064,-5724344156160,-9127649607680,169912999870464,-808704314179584,2411264265420800,-5695199097651200,13355397462097920,-34970066875056128,92444264561639424,-218025975729029120,438939049869180928,-754561566856708096,1122759752254750720,-1468424134459228160,1711321427347374080,-1797070344874459136,1714952769559396352,-1496379675829084160,1198583941546639360,-883279070731714560,599291970773319680,-374094918957271040,214369096194924544,-112316896554653696,53478794604605440,-22944127100925440,8771560564490240,-2947506120534016,857302831775744,-212915991922880,45138801055488,-8537613983168,1630297541760,-347607366800,73585945600,-12339848544,1296333312,-34819220,-10918320,1611764,-91560,1225]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[48640,-418816,1724160,-4461568,8108032,-11739136,14345216,-14818048,13171264,-10093440,6585632,-3704512,1793152,-733696,253376,-69712,13470,-1636,95]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[4,-4,0,-2,1]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[2,-4,1]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[16,32,-80,80,-24,40,-20,4,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[-5024,28224,-73104,119904,-143680,134496,-100576,59952,-27414,8820,-1727,150]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[-161600,403192,313600,-1155196,1280000,-981598,401600,-70801,10100]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[-1200,3024,2700,-9212,10000,-7606,3075,-522,75]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[-32,104,-512,716,-512,278,-64,-11,2]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[-91200,299592,-1324800,1815004,-1280000,679502,-148800,-30951,5700]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[5000,20674,0,-10337,1250]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[2,2,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[4,4,-8,2,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[64,-64,192,-608,1712,-2496,2144,-1248,428,-76,12,-2,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[256,0,-9472,43264,-97280,168832,-226496,233984,-188448,116992,-56624,21104,-6080,1352,-148,0,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[224,-384,-80,480,-464,352,-232,120,-10,-24,7]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[4096,4096,352256,-3414016,11651072,-21695488,24623104,-11664896,-18587904,56688128,-85517312,90809088,-73074944,45404544,-21379328,7086016,-1161744,-364528,384736,-169496,45512,-6668,344,2,1]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[16384,0,-7012352,81412096,-463343616,1697456128,-4572446720,9722007552,-17015016448,25178572800,-32065212416,35539916800,-34515057920,29485788160,-22201778176,14742894080,-8628764480,4442489600,-2004075776,786830400,-265859632,75953184,-17861120,3315344,-452484,39752,-1712,0,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[13184,-105984,397248,-911488,1454112,-1748224,1668240,-1299776,834120,-437056,181764,-56968,12414,-1656,103]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[262144,-262144,423886848,-6905790464,53893464064,-271445524480,1001430188032,-2906528088064,6939551989760,-14040725159936,24575824953344,-37766752911360,51509748858880,-62849318985728,69002278846464,-68451197579264,61531745429504,-50213979242496,37239868053504,-25106989621248,15382936357376,-8556399697408,4312642427904,-1964041218304,804839825920,-295052757120,95999316224,-27423291328,6776906240,-1419203168,244489792,-33135440,3289396,-210748,6468,-2,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[418816,-4238336,19221504,-49461760,75740416,-57796096,-24599552,139721472,-226244480,243377664,-196253568,121688832,-56561120,17465184,-1537472,-1806128,1183444,-386420,75084,-8278,409]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[6044,-8000,8000,-4000,489]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[4194304,0,-27602714624,497582866432,-4324416552960,24011029348352,-95803878146048,293387231035392,-717753768214528,1434597856903168,-2357354272391168,3132547236102144,-3132870676381696,1642569047998464,1791244376735744,-7008932834312192,13116080222273536,-18717441175846912,22429665581694976,-23418273953054720,21683544313159680,-17970417778245632,13391308740575232,-8985208889122816,5420886078289920,-2927284244131840,1401854098855936,-584920036745216,204938753473024,-54757287768064,6997048346624,3208142671872,-3059444019904,1529564080128,-575525945408,175121808704,-43808213392,8953467744,-1461851168,183189616,-16496340,949064,-26324,0,1]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[6713344,-94617600,643936256,-2786652160,8617474048,-20392085504,38648466432,-60557144064,80205412608,-91189292032,89933517312,-77452279808,58464168192,-38726139904,22483379328,-11398661504,5012838288,-1892410752,603882288,-159313168,33662008,-5442680,628844,-46200,1639]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[4194304,4194304,109832044544,-2210085732352,21695619399680,-138446477721600,647513753255936,-2376557340393472,7157693321838592,-18248119938187264,40273271161618432,-78231545202475008,135447138239053824,-211043486106386432,298154747480768512,-384167187345309696,453518328718589952,-492280550102892544,492679342637514752,-455560938982653952,389770785114677248,-308881705321611264,226855261186523136,-154440852660805632,97442696278669312,-56945117372831744,30792458914844672,-15383767190715392,7086223886227968,-3001306151135232,1164666982346752,-412194308801536,132272595936576,-38198996680896,9832341592192,-2227553703392,436870930288,-72526774304,9880275776,-1056262800,82762220,-4215404,104744,2,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[429457408,-7773945856,68767580160,-393349332992,1633522876416,-5258030465024,13693209706496,-29742835425280,55105021296640,-88561582624768,125050366058496,-156642912757760,175342506422272,-176343301610496,159958310365184,-131207387905536,97467907032576,-65603693952768,39989577591296,-22042912701312,10958906651392,-4895091023680,1953911969664,-691887364256,215253989440,-58091475440,13372275104,-2567397688,398809296,-48016276,4197240,-237242,6553]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[2,0,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[6068,-8000,8000,-4000,483]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ)),
    ((⟨#[8208,-20416,23312,-10208,1208,-5104,5828,-2552,513]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[8,-16,8,0,4,-4,1]⟩ : LeanCert.Engine.QPoly), (1 : ℚ)),
    ((⟨#[8144,-20288,23216,-10144,1144,-5072,5804,-2536,509]⟩ : LeanCert.Engine.QPoly), (-1 : ℚ))]

/-- Lemma B.12 (Sign certificates), TeX `lem:p2certs`: every one of the
forty-four factored polynomials passes the exact stated Taylor comparison. -/
theorem all_factored_taylor_tests :
    factoredSignPolynomials.all (fun p => signedTaylorCheck p.1 p.2) = true := by
  kernel_decide

/-- Lemma B.11 (Endpoints), TeX `lem:p2ends`: the printed spiral-switch
composition identity, without replacing it by a root-only consequence. -/
theorem switch_composition_identity {z : ℝ} (hz : z ∈ parameterInterval) :
    32 * G z ^ 3 - 36 * G z ^ 2 + 4 * G z - 1 =
      (z ^ 3 + 2 * z + 4) * endpointCubic z *
        (z ^ 6 - 8 * z ^ 5 - 2 * z ^ 4 + 16 * z ^ 3 + 4 * z ^ 2 - 32 * z - 8) /
          (16 * z ^ 3 * rMinus z ^ 3) := by
  have h0 := (parameter_pos hz).ne'
  have hr := (rMinus_pos hz).ne'
  unfold G
  field_simp
  unfold rMinus endpointCubic
  ring

/-- Lemma B.11 (Endpoints), TeX `lem:p2ends`: actual polynomial divisibility
of the numerator of the source-linked composition Hₐ(G(ζ)). -/
theorem endpoint_numerator_divisibility :
    endpointPolynomial ∣ haCompositionCode.numerator.toPoly := by
  let quotient : LeanCert.Engine.QPoly :=
    ⟨#[203161600,1275854848,-345112576,-18485084160,-48511287296,-29594845184,
      65077313536,101223776256,-38432956416,-177722195968,-81128030208,128052953088,
      166693517312,40873752576,-45469732864,-28856390656,10926922240,23742022656,
      19578573824,11871011328,2731730560,-3607048832,-2841858304,1277304768,
      2604586208,1000413696,-316906368,-347113664,-37532184,49425672,15888016,
      -3612652,-2960894,-564120,-5266,9734,775]⟩
  have hc : Numerics.remainderCodeCheck haCompositionCode.numerator
      endpointPolynomialCode.code quotient LeanCert.Engine.QPoly.zero = true := by kernel_decide
  refine ⟨quotient.toPoly, ?_⟩
  simpa only [endpointPolynomialCode.exact, LeanCert.Engine.QPoly.toPoly_zero, add_zero] using
    Numerics.remainderCodeCheck_sound hc

/-- Lemma B.11 (Endpoints), TeX `lem:p2ends`: uniqueness is on all of J,
not merely the smaller root-isolation interval. -/
theorem unique_arc_endpoint : ∃! z : ℝ, z ∈ parameterInterval ∧ N12 z = 0 := by
  refine ⟨zetaA, ⟨zetaA_mem, N12_zetaA⟩, ?_⟩
  intro z hz
  exact N12_strictAntiOn.injOn hz.1 zetaA_mem (hz.2.trans N12_zetaA.symm)

end P2Data

/-- Theorem B.18 (Central family near κc), TeX `thm:p5local`:
the analytic branch exists on a neighborhood of the closed parameter interval.
Uniqueness is local at the specified critical point, as in the implicit function theorem. -/
theorem central_branch_closed_neighborhood :
    ∃ hstar : ℝ, 0 < hstar ∧
      Boundary.P5.localBranch 0 = Boundary.P5.criticalPoint ∧
      AnalyticOnNhd ℝ Boundary.P5.localBranch (Icc (-hstar) hstar) ∧
      (∀ h : ℝ, |h| ≤ hstar →
        Boundary.P5.regularSystem (h, Boundary.P5.localBranch h) = 0) ∧
      (∀ᶠ p in 𝓝 ((0 : ℝ), Boundary.P5.criticalPoint),
        Boundary.P5.regularSystem p = 0 ↔ Boundary.P5.localBranch p.1 = p.2) ∧
      (∀ t : ℝ, Real.cosh t ≤ 1 + hstar →
        Spectral.V t = Boundary.P5.localValue t) ∧
      (∀ h : ℝ, 0 ≤ h → h ≤ hstar → ∃ ν : Spectral.Spectrum,
        Spectral.FeasibleU (Boundary.P5.branchU h (Boundary.P5.localBranch h))
          (Real.arcosh (1 + h)) ν
          (h * Boundary.P5.localBranch h 4 / Real.sinh (Real.arcosh (1 + h)))) ∧
      (∀ t : ℝ, Spectral.V (-t) = Spectral.V t) ∧
        AnalyticAt ℝ Spectral.V 0 ∧ Spectral.V 0 = Real.log ((1 + Real.sqrt 5) / 2) := by
  obtain ⟨h, hh, hzero, han, heq, huniq, hV, hfeasible, heven, hanalytic, hvalue⟩ :=
    Boundary.P5.p5local
  refine ⟨h / 2, half_pos hh, hzero, ?_, ?_, huniq, ?_, ?_, heven, hanalytic, ?_⟩
  · intro z hz
    exact han z ⟨by linarith [hz.1], by linarith [hz.2]⟩
  · intro z hz
    exact heq z (hz.trans (by linarith))
  · intro t ht
    exact hV t (by linarith)
  · intro z hz hmax
    exact hfeasible z hz (hmax.trans (by linarith))
  · simpa only [Real.goldenRatio] using hvalue

namespace Startup
open Realization.ExplicitSpiral

/-- Lemma C.1 (Slacks of the initial pairs), TeX `lem:startupslack`:
the displayed rational norm formula is the norm of the actual complex defect. -/
theorem defect_norm_formula {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    Complex.normSq (defect (radialWave r) q) =
      q ^ 2 / 4 * (r ^ 4 + 4 * r ^ 2 + 1) / (r ^ 2 * (r ^ 2 + 1)) := by
  obtain ⟨_, hn, hz⟩ := radial_wave_coordinates hr
  obtain ⟨_, _, hreal, himag⟩ := multiplier_defect_coordinates hr hq hn hz
  have hisq := imaginarySquare_eq hn hz
  simp only [Complex.normSq_apply, ← pow_two, hreal, himag, mul_pow, hisq]
  unfold Source.defectReal Source.defectImag Source.imaginarySquare Source.lambdaReal
  field_simp
  ring

/-- Lemma C.1 (Slacks of the initial pairs), TeX `lem:startupslack`:
the exact real defect formula includes its uniform upper bound. -/
theorem defect_real_formula {r q : ℝ} (hr : 0 < r) (hq : 0 < q) :
    (defect (radialWave r) q).re = q / 2 * (r ^ 2 + 2) / (r ^ 2 + 1) ∧
      (defect (radialWave r) q).re ≤ q := by
  obtain ⟨_, hn, hz⟩ := radial_wave_coordinates hr
  have hreal := (multiplier_defect_coordinates hr hq hn hz).2.2.1
  refine ⟨?_, ?_⟩
  · rw [hreal]
    unfold Source.defectReal
    field_simp
  · rw [hreal]
    unfold Source.defectReal
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (r ^ 2 + 1))).mpr
    nlinarith [sq_nonneg r]

/-- Lemma C.1 (Slacks of the initial pairs), TeX `lem:startupslack`:
both source bounds hold, with the strict inequality on the value constant. -/
theorem source_gap_and_charge_bounds {r : ℝ} (hr : 0 < r) :
    (0 < Source.gap r ∧ Source.gap r ≤ 1 / 2) ∧ |physicalValueConstant r| < 1 / 2 := by
  have hg := source_gap_pos hr
  have hu : Source.gap r ≤ 1 / 2 := by
    rw [source_gap_half]
    exact sub_le_self _ (by positivity)
  refine ⟨⟨hg, hu⟩, ?_⟩
  have hratio : |(r ^ 2 - 1) / (r ^ 2 + 1)| < 1 := by
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < r ^ 2 + 1)]
    apply (div_lt_one (by positivity : (0 : ℝ) < r ^ 2 + 1)).mpr
    exact abs_lt.mpr ⟨by nlinarith [sq_pos_of_pos hr], by linarith⟩
  have hid : physicalValueConstant r = Source.gap r * ((r ^ 2 - 1) / (r ^ 2 + 1)) := by
    unfold physicalValueConstant
    ring
  rw [hid, abs_mul, abs_of_pos hg]
  exact (mul_lt_mul_of_pos_left hratio hg).trans_le (by simpa using hu)

end Startup

/-- Lemma D.3 (The lag-one cubic), TeX `lem:cubic`:
the Chebyshev expression and the expanded source polynomial are identical. -/
theorem cubic_chebyshev_formula (q : General.Tuning) (r c : ℝ) :
    let P := 1 + q.beta - q.x
    let Q := 1 + q.beta - q.y
    let C := Q * r ^ 2 + P * q.beta
    let D := P * r ^ 2 + Q * q.beta
    let E := r ^ 4 + P * Q * r ^ 2 + q.beta ^ 2
    q.H r c = E + r ^ 2 * D - r * (C + D + E + q.beta * r ^ 2) * c +
      r ^ 2 * (C + 2 * q.beta) * (2 * c ^ 2 - 1) -
      q.beta * r ^ 3 * (4 * c ^ 3 - 3 * c) := by
  dsimp [General.Tuning.H]
  ring

namespace MultiplierSymbols
open General.Multipliers

private theorem lower_factor_at_every_point (q : General.Tuning) {z : ℂ} (hz : z ≠ 0)
    (M : ℂ) :
    (((1 - q.m z) * (1 + star (q.m z))) * M).re =
      -(Complex.normSq (q.b z) / (q.B ^ 2 * Complex.normSq z)) * (M * q.a z / q.b z).re := by
  by_cases hb : q.b z = 0
  · rw [q.factor hz]
    simp [hb]
  · exact factor_re_lower q hz hb M

private theorem upper_factor_at_every_point (q : General.Tuning) {z : ℂ} (hz : z ≠ 0)
    (M : ℂ) :
    ((star ((1 - q.m z) * (1 + star (q.m z)))) * M).re =
      -(Complex.normSq (q.a z) / (q.B ^ 2 * Complex.normSq z)) * (M * q.b z / q.a z).re := by
  by_cases ha : q.a z = 0
  · rw [q.factor hz]
    simp [ha]
  · exact factor_re_upper q hz ha M

/-- Lemma D.8 (Symbols of one-sided certificates), TeX `lem:symbols`:
the lower-lag identity holds on every radius, including removable zeros of b.
At a zero of b both sides are zero; away from zeros this is literal division. -/
theorem lower_negative_source_symbol (q : General.Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (t : ℝ) (c : Spectral.Frequency) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun n => lam n * Real.exp (n * t)) (fun _ => 0)
      (-(∑ n ∈ s, lam n * Real.exp (n * t) * Real.sinh (n * t))) 0 c =
      -(Complex.normSq (q.b (Waves.z t (Real.arccos c))) / (q.B ^ 2 * Real.exp (2 * t))) *
        (polynomial s lam (Waves.z t (Real.arccos c)) * q.a (Waves.z t (Real.arccos c)) /
          q.b (Waves.z t (Real.arccos c))).re := by
  rw [lower_negative_symbol]
  dsimp only [Duality.g, Waves.multiplierMap, ContinuousMap.coe_mk]
  rw [← q.m_wave, General.Tuning.real_im_factor,
    lower_factor_at_every_point q (Waves.z_ne_zero _ _), normSq_wave]

/-- Lemma D.8 (Symbols of one-sided certificates), TeX `lem:symbols`:
the reflected upper-lag identity has no extra radial exclusion. -/
theorem upper_negative_source_symbol (q : General.Tuning) (s : Finset ℕ) (lam : ℕ → ℝ)
    (t : ℝ) (c : Spectral.Frequency) :
    Duality.symbol (Waves.multiplierMap q.A q.B q.beta t) t s
      (fun _ => 0) (fun n => lam n * Real.exp (n * t))
      0 (-(∑ n ∈ s, lam n * Real.exp (n * t) * Real.sinh (n * t))) c =
      -(Complex.normSq (q.a (Waves.z t (Real.arccos c))) / (q.B ^ 2 * Real.exp (2 * t))) *
        (polynomial s lam (Waves.z t (Real.arccos c)) * q.b (Waves.z t (Real.arccos c)) /
          q.a (Waves.z t (Real.arccos c))).re := by
  rw [upper_negative_symbol]
  dsimp only [Duality.g, Waves.multiplierMap, ContinuousMap.coe_mk]
  rw [← q.m_wave, General.Tuning.real_im_factor,
    upper_factor_at_every_point q (Waves.z_ne_zero _ _), normSq_wave]

end MultiplierSymbols

end polyak.ArticleResults
