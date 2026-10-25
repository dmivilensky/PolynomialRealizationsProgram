import polyak.Certificates.P2SlacksData00

namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
/-- Article: exact source arithmetic node 81. -/
def formula81 (z : ℝ) : ℝ := (formula80 z)*(u z)
theorem node80Denominator : ∀ z∈parameterInterval, aeval z (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
theorem node80Cross : polynomialCheck
    (((⟨#[0,0,8192,-12288,12288,-104448,223232,-226304,156672,-72192,28672,-36096,39168,-28288,13952,-3264,192,-96,32]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩)
    ((⟨#[0,0,32768,-114688,212992,-647168,1884160,-3588096,4653056,-4349952,3074048,-1804288,1120256,-902144,768512,-543744,290816,-112128,29440,-5056,832,-224,32]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node80 : RationalCode parameterInterval formula81 :=
  (node79.mul uCode)
  |>.recode ⟨#[0,0,32768,-114688,212992,-647168,1884160,-3588096,4653056,-4349952,3074048,-1804288,1120256,-902144,768512,-543744,290816,-112128,29440,-5056,832,-224,32]⟩ ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ node80Denominator node80Cross

/-- Article: exact source arithmetic node 82. -/
def formula82 (z : ℝ) : ℝ := (formula79 z)+(formula81 z)
theorem node81Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly).toPoly≠0 :=
  node75Denominator
theorem node81Cross : polynomialCheck
    ((((⟨#[40960,-262144,585728,-989184,1413120,1353728,-13731840,39625216,-73608704,101427200,-110976256,101593344,-81680384,59973376,-40840192,25398336,-13872032,6339200,-2300272,619144,-107280,5288,2760,-966,286,-64,5]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,32768,-114688,212992,-647168,1884160,-3588096,4653056,-4349952,3074048,-1804288,1120256,-902144,768512,-543744,290816,-112128,29440,-5056,832,-224,32]⟩ : QPoly).mul (⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly)) : QPoly).mul ⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩)
    ((⟨#[40960,-262144,585728,-727040,495616,3057664,-18909184,54698496,-102313472,138651648,-145775872,126185728,-96114688,68935424,-48057344,31546432,-18221984,8665728,-3197296,854664,-147728,11944,968,-710,286,-64,5]⟩ : QPoly).mul ((⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node81 : RationalCode parameterInterval formula82 :=
  (node78.add node80)
  |>.recode ⟨#[40960,-262144,585728,-727040,495616,3057664,-18909184,54698496,-102313472,138651648,-145775872,126185728,-96114688,68935424,-48057344,31546432,-18221984,8665728,-3197296,854664,-147728,11944,968,-710,286,-64,5]⟩ ⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ node81Denominator node81Cross

/-- Article: exact source arithmetic node 83. -/
def formula83 (z : ℝ) : ℝ := ((fun z : ℝ => moment z 0) z)*(formula70 z)
theorem node82Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).toPoly≠0 :=
  node69Denominator
theorem node82Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,256,0,-256,0,64]⟩)
    ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
def node82 : RationalCode parameterInterval formula83 :=
  (moment0Code.mul node69)
  |>.recode ⟨#[16,0,0,0,8,0,0,0,1]⟩ ⟨#[0,0,256,0,-256,0,64]⟩ node82Denominator node82Cross

/-- Article: exact source arithmetic node 84. -/
def formula84 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(formula45 z)
theorem node83Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node44Denominator
theorem node83Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[-16,64,-128,160,-136,80,-32,8,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node83 : RationalCode parameterInterval formula84 :=
  ((RationalCode.constant parameterInterval (-1)).mul node44)
  |>.recode ⟨#[-16,64,-128,160,-136,80,-32,8,-1]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node83Denominator node83Cross

/-- Article: exact source arithmetic node 85. -/
def formula85 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1 : ℚ) : ℝ)) z)+(formula84 z)
theorem node84Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node44Denominator
theorem node84Cross : polynomialCheck
    ((((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)).add ((⟨#[-16,64,-128,160,-136,80,-32,8,-1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[0,64,-128,160,-144,80,-32,8]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node84 : RationalCode parameterInterval formula85 :=
  ((RationalCode.constant parameterInterval (1)).add node83)
  |>.recode ⟨#[0,64,-128,160,-144,80,-32,8]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node84Denominator node84Cross

/-- Article: exact source arithmetic node 86. -/
def formula86 (z : ℝ) : ℝ := (formula83 z)*(formula85 z)
theorem node85Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
theorem node85Cross : polynomialCheck
    (((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (⟨#[0,64,-128,160,-144,80,-32,8]⟩ : QPoly) : QPoly).mul ⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩)
    ((⟨#[128,-256,320,-288,224,-192,176,-144,88,-48,28,-18,10,-4,1]⟩ : QPoly).mul ((⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node85 : RationalCode parameterInterval formula86 :=
  (node82.mul node84)
  |>.recode ⟨#[128,-256,320,-288,224,-192,176,-144,88,-48,28,-18,10,-4,1]⟩ ⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ node85Denominator node85Cross

/-- Article: exact source arithmetic node 87. -/
def formula87 (z : ℝ) : ℝ := (formula82 z)+(formula86 z)
theorem node86Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
theorem node86Cross : polynomialCheck
    ((((⟨#[40960,-262144,585728,-727040,495616,3057664,-18909184,54698496,-102313472,138651648,-145775872,126185728,-96114688,68935424,-48057344,31546432,-18221984,8665728,-3197296,854664,-147728,11944,968,-710,286,-64,5]⟩ : QPoly).mul (⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly)).add ((⟨#[128,-256,320,-288,224,-192,176,-144,88,-48,28,-18,10,-4,1]⟩ : QPoly).mul (⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly)) : QPoly).mul ⟨#[0,81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩)
    ((⟨#[40960,-262144,708608,-1236992,1691648,-483328,-7018496,24700928,-48527872,66904064,-70792448,61379584,-46733824,33504256,-23366912,15344896,-8849056,4181504,-1516496,385952,-54832,-1888,3304,-1208,346,-64,5]⟩ : QPoly).mul ((⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly).mul (⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly)))=true := by kernel_decide
def node86 : RationalCode parameterInterval formula87 :=
  (node81.add node85)
  |>.recode ⟨#[40960,-262144,708608,-1236992,1691648,-483328,-7018496,24700928,-48527872,66904064,-70792448,61379584,-46733824,33504256,-23366912,15344896,-8849056,4181504,-1516496,385952,-54832,-1888,3304,-1208,346,-64,5]⟩ ⟨#[0,81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ node86Denominator node86Cross

/-- Article: exact source arithmetic node 88. -/
def formula88 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(formula87 z)
theorem node87Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,40960,-180224,327680,-286720,176128,-28672,-245760,296960,-199168,124928,40960,-109568,76288,-54784,10240,15616,-12448,9280,-3840,-224,688,-560,320,-88,10]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
theorem node87Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[40960,-262144,708608,-1236992,1691648,-483328,-7018496,24700928,-48527872,66904064,-70792448,61379584,-46733824,33504256,-23366912,15344896,-8849056,4181504,-1516496,385952,-54832,-1888,3304,-1208,346,-64,5]⟩ : QPoly) : QPoly).mul ⟨#[0,40960,-180224,327680,-286720,176128,-28672,-245760,296960,-199168,124928,40960,-109568,76288,-54784,10240,15616,-12448,9280,-3840,-224,688,-560,320,-88,10]⟩)
    ((⟨#[40960,-262144,708608,-1236992,1691648,-483328,-7018496,24700928,-48527872,66904064,-70792448,61379584,-46733824,33504256,-23366912,15344896,-8849056,4181504,-1516496,385952,-54832,-1888,3304,-1208,346,-64,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ : QPoly)))=true := by kernel_decide
def node87 : RationalCode parameterInterval formula88 :=
  ((RationalCode.constant parameterInterval (2)).mul node86)
  |>.recode ⟨#[40960,-262144,708608,-1236992,1691648,-483328,-7018496,24700928,-48527872,66904064,-70792448,61379584,-46733824,33504256,-23366912,15344896,-8849056,4181504,-1516496,385952,-54832,-1888,3304,-1208,346,-64,5]⟩ ⟨#[0,40960,-180224,327680,-286720,176128,-28672,-245760,296960,-199168,124928,40960,-109568,76288,-54784,10240,15616,-12448,9280,-3840,-224,688,-560,320,-88,10]⟩ node87Denominator node87Cross

/-- Article: exact coefficient representation of the independently specified lower2Expression source. -/
def lower2ExpressionCode : RationalCode parameterInterval (fun z : ℝ => ((2*(moment z 4))+((moment z 0)*((2*((G z))^2)+(-2*((G z))^2*((u z))^2)))+((moment z 2)*(-2+(-2*((G z))^2)+(2*((u z))^2)))+(-4*(moment z 1)*(u z))+(2*(G z)*(d z))+(4*(moment z 3)*(u z)))) where
  numerator := node87.numerator
  denominator := node87.denominator
  denominator_ne := node87.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((2*(moment z 4))+((moment z 0)*((2*((G z))^2)+(-2*((G z))^2*((u z))^2)))+((moment z 2)*(-2+(-2*((G z))^2)+(2*((u z))^2)))+(-4*(moment z 1)*(u z))+(2*(G z)*(d z))+(4*(moment z 3)*(u z)))) z=formula88 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node87.exact z hz)

/-- Article: compact exact representation of the actual raw lower2 source. -/
def lower2ActualCode : RationalCode parameterInterval (fun z => reducedSlack z 2 (-1 : ℝ)) where
  numerator := lower2ExpressionCode.numerator
  denominator := lower2ExpressionCode.denominator
  denominator_ne := lower2ExpressionCode.denominator_ne
  exact z hz := (lower2_source z).trans (lower2ExpressionCode.exact z hz)

/-- Article: the actual raw lower2 is strictly positive throughout J. -/
theorem lower2_positive : ∀ z∈parameterInterval,0<reducedSlack z 2 (-1 : ℝ) :=
  lower2ActualCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 89. -/
def formula89 (z : ℝ) : ℝ := ((fun z : ℝ => moment z 4) z)+(formula73 z)
theorem node88Denominator : ∀ z∈parameterInterval, aeval z (⟨#[81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ : QPoly).toPoly≠0 :=
  node72Denominator
theorem node88Cross : polynomialCheck
    ((((⟨#[0,-16384,73728,-172032,409600,-757760,976896,-829440,-61440,1554432,-2796544,3165184,-2605056,1582592,-699136,194304,-3840,-25920,15264,-5920,1600,-336,72,-8]⟩ : QPoly).mul (⟨#[81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ : QPoly)).add ((⟨#[0,4096,-39936,90112,132096,-2914304,11091200,-23575040,36119552,-43709440,43589248,-37351168,28135808,-18675584,10897312,-5463680,2257472,-736720,173300,-22768,516,176,-39,2]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩)
    ((⟨#[0,-61440,254976,-598016,1770496,-5945344,14998784,-26892800,35873792,-37491712,32403072,-24690432,17715584,-12345216,8100768,-4686464,2242112,-840400,234356,-46448,6916,-1168,249,-30]⟩ : QPoly).mul ((⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).mul (⟨#[81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ : QPoly)))=true := by kernel_decide
def node88 : RationalCode parameterInterval formula89 :=
  (moment4Code.add node72)
  |>.recode ⟨#[0,-61440,254976,-598016,1770496,-5945344,14998784,-26892800,35873792,-37491712,32403072,-24690432,17715584,-12345216,8100768,-4686464,2242112,-840400,234356,-46448,6916,-1168,249,-30]⟩ ⟨#[81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ node88Denominator node88Cross

/-- Article: exact source arithmetic node 90. -/
def formula90 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(G z)
theorem node89Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  node43Denominator
theorem node89Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node89 : RationalCode parameterInterval formula90 :=
  ((RationalCode.constant parameterInterval (-1)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-16,0,8]⟩ node89Denominator node89Cross

/-- Article: exact source arithmetic node 91. -/
def formula91 (z : ℝ) : ℝ := (formula90 z)*(d z)
theorem node90Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ : QPoly).toPoly≠0 :=
  node74Denominator
theorem node90Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ : QPoly) : QPoly).mul ⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩)
    ((⟨#[-20480,131072,-344064,192512,1357824,-4835328,9220096,-12611584,13886720,-13252608,11479040,-9182720,6772992,-4591360,2869760,-1656576,867920,-394112,144064,-37776,5304,376,-336,64,-5]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node90 : RationalCode parameterInterval formula91 :=
  (node89.mul dCode)
  |>.recode ⟨#[-20480,131072,-344064,192512,1357824,-4835328,9220096,-12611584,13886720,-13252608,11479040,-9182720,6772992,-4591360,2869760,-1656576,867920,-394112,144064,-37776,5304,376,-336,64,-5]⟩ ⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ node90Denominator node90Cross

/-- Article: exact source arithmetic node 92. -/
def formula92 (z : ℝ) : ℝ := (formula89 z)+(formula91 z)
theorem node91Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly).toPoly≠0 :=
  node75Denominator
theorem node91Cross : polynomialCheck
    ((((⟨#[0,-61440,254976,-598016,1770496,-5945344,14998784,-26892800,35873792,-37491712,32403072,-24690432,17715584,-12345216,8100768,-4686464,2242112,-840400,234356,-46448,6916,-1168,249,-30]⟩ : QPoly).mul (⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ : QPoly)).add ((⟨#[-20480,131072,-344064,192512,1357824,-4835328,9220096,-12611584,13886720,-13252608,11479040,-9182720,6772992,-4591360,2869760,-1656576,867920,-394112,144064,-37776,5304,376,-336,64,-5]⟩ : QPoly).mul (⟨#[81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ : QPoly)) : QPoly).mul ⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩)
    ((⟨#[-40960,262144,-831488,1026048,1175552,-5937152,7907328,-60928,-16792064,32630784,-38138624,33188096,-24355840,17065728,-12177920,8297024,-4767328,2039424,-524752,-952,61776,-23192,2296,1002,-406,64,-5]⟩ : QPoly).mul ((⟨#[81920,-360448,655360,-573440,352256,-57344,-491520,593920,-398336,249856,81920,-219136,152576,-109568,20480,31232,-24896,18560,-7680,-448,1376,-1120,640,-176,20]⟩ : QPoly).mul (⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ : QPoly)))=true := by kernel_decide
def node91 : RationalCode parameterInterval formula92 :=
  (node88.add node90)
  |>.recode ⟨#[-40960,262144,-831488,1026048,1175552,-5937152,7907328,-60928,-16792064,32630784,-38138624,33188096,-24355840,17065728,-12177920,8297024,-4767328,2039424,-524752,-952,61776,-23192,2296,1002,-406,64,-5]⟩ ⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ node91Denominator node91Cross

/-- Article: exact source arithmetic node 93. -/
def formula93 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 3) z)
theorem node92Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node5Denominator
theorem node92Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[0,0,4096,-6144,6144,-52224,111616,-113152,78336,-36096,14336,-18048,19584,-14144,6976,-1632,96,-48,16]⟩ : QPoly) : QPoly).mul ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩)
    ((⟨#[0,0,-8192,12288,-12288,104448,-223232,226304,-156672,72192,-28672,36096,-39168,28288,-13952,3264,-192,96,-32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node92 : RationalCode parameterInterval formula93 :=
  ((RationalCode.constant parameterInterval (-2)).mul moment3Code)
  |>.recode ⟨#[0,0,-8192,12288,-12288,104448,-223232,226304,-156672,72192,-28672,36096,-39168,28288,-13952,3264,-192,96,-32]⟩ ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ node92Denominator node92Cross

/-- Article: exact source arithmetic node 94. -/
def formula94 (z : ℝ) : ℝ := (formula93 z)*(u z)
theorem node93Denominator : ∀ z∈parameterInterval, aeval z (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
theorem node93Cross : polynomialCheck
    (((⟨#[0,0,-8192,12288,-12288,104448,-223232,226304,-156672,72192,-28672,36096,-39168,28288,-13952,3264,-192,96,-32]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩)
    ((⟨#[0,0,-32768,114688,-212992,647168,-1884160,3588096,-4653056,4349952,-3074048,1804288,-1120256,902144,-768512,543744,-290816,112128,-29440,5056,-832,224,-32]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node93 : RationalCode parameterInterval formula94 :=
  (node92.mul uCode)
  |>.recode ⟨#[0,0,-32768,114688,-212992,647168,-1884160,3588096,-4653056,4349952,-3074048,1804288,-1120256,902144,-768512,543744,-290816,112128,-29440,5056,-832,224,-32]⟩ ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ node93Denominator node93Cross

/-- Article: exact source arithmetic node 95. -/
def formula95 (z : ℝ) : ℝ := (formula92 z)+(formula94 z)
theorem node94Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ : QPoly).toPoly≠0 :=
  node74Denominator
theorem node94Cross : polynomialCheck
    ((((⟨#[-40960,262144,-831488,1026048,1175552,-5937152,7907328,-60928,-16792064,32630784,-38138624,33188096,-24355840,17065728,-12177920,8297024,-4767328,2039424,-524752,-952,61776,-23192,2296,1002,-406,64,-5]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,-32768,114688,-212992,647168,-1884160,3588096,-4653056,4349952,-3074048,1804288,-1120256,902144,-768512,543744,-290816,112128,-29440,5056,-832,224,-32]⟩ : QPoly).mul (⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly)) : QPoly).mul ⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩)
    ((⟨#[-20480,131072,-405504,316416,1249280,-3978752,5917696,-5577728,2997504,492032,-3168256,4051840,-3376640,2025920,-792064,61504,187344,-174304,92464,-31084,4880,618,-396,64,-5]⟩ : QPoly).mul ((⟨#[0,163840,-720896,1310720,-1146880,704512,-114688,-983040,1187840,-796672,499712,163840,-438272,305152,-219136,40960,62464,-49792,37120,-15360,-896,2752,-2240,1280,-352,40]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node94 : RationalCode parameterInterval formula95 :=
  (node91.add node93)
  |>.recode ⟨#[-20480,131072,-405504,316416,1249280,-3978752,5917696,-5577728,2997504,492032,-3168256,4051840,-3376640,2025920,-792064,61504,187344,-174304,92464,-31084,4880,618,-396,64,-5]⟩ ⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ node94Denominator node94Cross

/-- Article: exact source arithmetic node 96. -/
def formula96 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 1) z)
theorem node95Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node76Denominator
theorem node95Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ : QPoly) : QPoly).mul ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩)
    ((⟨#[0,0,1920,-5888,7168,-7040,6080,-3520,1792,-736,120]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node95 : RationalCode parameterInterval formula96 :=
  ((RationalCode.constant parameterInterval (2)).mul moment1Code)
  |>.recode ⟨#[0,0,1920,-5888,7168,-7040,6080,-3520,1792,-736,120]⟩ ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ node95Denominator node95Cross

/-- Article: exact source arithmetic node 97. -/
def formula97 (z : ℝ) : ℝ := (formula96 z)*(u z)
theorem node96Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
theorem node96Cross : polynomialCheck
    (((⟨#[0,0,1920,-5888,7168,-7040,6080,-3520,1792,-736,120]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩)
    ((⟨#[0,0,7680,-38912,91136,-140288,163456,-153600,119296,-76800,40864,-17536,5696,-1216,120]⟩ : QPoly).mul ((⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node96 : RationalCode parameterInterval formula97 :=
  (node95.mul uCode)
  |>.recode ⟨#[0,0,7680,-38912,91136,-140288,163456,-153600,119296,-76800,40864,-17536,5696,-1216,120]⟩ ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ node96Denominator node96Cross

/-- Article: exact source arithmetic node 98. -/
def formula98 (z : ℝ) : ℝ := (formula95 z)+(formula97 z)
theorem node97Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly).toPoly≠0 :=
  node85Denominator
theorem node97Cross : polynomialCheck
    ((((⟨#[-20480,131072,-405504,316416,1249280,-3978752,5917696,-5577728,2997504,492032,-3168256,4051840,-3376640,2025920,-792064,61504,187344,-174304,92464,-31084,4880,618,-396,64,-5]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,7680,-38912,91136,-140288,163456,-153600,119296,-76800,40864,-17536,5696,-1216,120]⟩ : QPoly).mul (⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ : QPoly)) : QPoly).mul ⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩)
    ((⟨#[-128,256,-320,288,-224,192,-176,144,-88,48,-28,18,-10,4,-1]⟩ : QPoly).mul ((⟨#[0,81920,-360448,614400,-393216,45056,139264,-514048,524288,-141312,-12288,152576,-212992,76288,-3072,-17664,32768,-16064,2176,352,-1536,1200,-352,40]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node97 : RationalCode parameterInterval formula98 :=
  (node94.add node96)
  |>.recode ⟨#[-128,256,-320,288,-224,192,-176,144,-88,48,-28,18,-10,4,-1]⟩ ⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ node97Denominator node97Cross

/-- Article: exact source arithmetic node 99. -/
def formula99 (z : ℝ) : ℝ := (formula98 z)+(formula86 z)
theorem node98Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node98Cross : polynomialCheck
    ((((⟨#[-128,256,-320,288,-224,192,-176,144,-88,48,-28,18,-10,4,-1]⟩ : QPoly).mul (⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly)).add ((⟨#[128,-256,320,-288,224,-192,176,-144,88,-48,28,-18,10,-4,1]⟩ : QPoly).mul (⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly).mul (⟨#[0,512,0,-512,0,-128,0,256,0,-32,0,-32,0,8]⟩ : QPoly)))=true := by kernel_decide
def node98 : RationalCode parameterInterval formula99 :=
  (node97.add node85)
  |>.recode QPoly.zero ⟨#[1]⟩ node98Denominator node98Cross

/-- Article: exact source arithmetic node 100. -/
def formula100 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(formula99 z)
theorem node99Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node99Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (QPoly.zero : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node99 : RationalCode parameterInterval formula100 :=
  ((RationalCode.constant parameterInterval (2)).mul node98)
  |>.recode QPoly.zero ⟨#[1]⟩ node99Denominator node99Cross

/-- Article: exact coefficient representation of the independently specified upper2Expression source. -/
def upper2ExpressionCode : RationalCode parameterInterval (fun z : ℝ => ((2*(moment z 4))+((moment z 0)*((2*((G z))^2)+(-2*((G z))^2*((u z))^2)))+((moment z 2)*(-2+(-2*((G z))^2)+(2*((u z))^2)))+(-4*(moment z 3)*(u z))+(-2*(G z)*(d z))+(4*(moment z 1)*(u z)))) where
  numerator := node99.numerator
  denominator := node99.denominator
  denominator_ne := node99.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((2*(moment z 4))+((moment z 0)*((2*((G z))^2)+(-2*((G z))^2*((u z))^2)))+((moment z 2)*(-2+(-2*((G z))^2)+(2*((u z))^2)))+(-4*(moment z 3)*(u z))+(-2*(G z)*(d z))+(4*(moment z 1)*(u z)))) z=formula100 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node99.exact z hz)

/-- Article: compact exact representation of the actual raw upper2 source. -/
def upper2ActualCode : RationalCode parameterInterval (fun z => reducedSlack z 2 (1 : ℝ)) where
  numerator := upper2ExpressionCode.numerator
  denominator := upper2ExpressionCode.denominator
  denominator_ne := upper2ExpressionCode.denominator_ne
  exact z hz := (upper2_source z).trans (upper2ExpressionCode.exact z hz)

/-- Article: the active raw upper2 is exactly zero. -/
theorem upper2_zero {z : ℝ} (hz : z∈parameterInterval) : reducedSlack z 2 (1 : ℝ)=0 :=
  upper2ActualCode.eq_zero (by kernel_decide) hz

/-- Article: exact source arithmetic node 101. -/
def formula101 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 5) z)
theorem node100Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
theorem node100Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[65536,-491520,1867776,-5095424,11747328,-22691840,33144832,-32907264,11939840,33634304,-93751296,146701312,-172049408,162097152,-125802496,81048576,-43012352,18337664,-5859456,1051072,186560,-257088,129472,-44320,11472,-2488,456,-60,4]⟩ : QPoly) : QPoly).mul ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩)
    ((⟨#[262144,-1966080,7471104,-20381696,46989312,-90767360,132579328,-131629056,47759360,134537216,-375005184,586805248,-688197632,648388608,-503209984,324194304,-172049408,73350656,-23437824,4204288,746240,-1028352,517888,-177280,45888,-9952,1824,-240,16]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node100 : RationalCode parameterInterval formula101 :=
  ((RationalCode.constant parameterInterval (4)).mul moment5Code)
  |>.recode ⟨#[262144,-1966080,7471104,-20381696,46989312,-90767360,132579328,-131629056,47759360,134537216,-375005184,586805248,-688197632,648388608,-503209984,324194304,-172049408,73350656,-23437824,4204288,746240,-1028352,517888,-177280,45888,-9952,1824,-240,16]⟩ ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ node100Denominator node100Cross

/-- Article: exact source arithmetic node 102. -/
def formula102 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-3 : ℚ) : ℝ)) z)*(G z)
theorem node101Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  node43Denominator
theorem node101Cross : polynomialCheck
    (((⟨#[-3]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[-12,0,0,0,-3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node101 : RationalCode parameterInterval formula102 :=
  ((RationalCode.constant parameterInterval (-3)).mul GCode)
  |>.recode ⟨#[-12,0,0,0,-3]⟩ ⟨#[0,-16,0,8]⟩ node101Denominator node101Cross

/-- Article: exact source arithmetic node 103. -/
def formula103 (z : ℝ) : ℝ := (formula102 z)+(formula54 z)
theorem node102Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-32,0,0,0,8]⟩ : QPoly).toPoly≠0 :=
  node42Denominator
theorem node102Cross : polynomialCheck
    ((((⟨#[-12,0,0,0,-3]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)).add ((⟨#[8,-16,16,-8,2]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,-32,0,0,0,8]⟩)
    ((⟨#[-24,64,-140,128,-70,16,-3]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node102 : RationalCode parameterInterval formula103 :=
  (node101.add node53)
  |>.recode ⟨#[-24,64,-140,128,-70,16,-3]⟩ ⟨#[0,-32,0,0,0,8]⟩ node102Denominator node102Cross

/-- Article: exact source arithmetic node 104. -/
def formula104 (z : ℝ) : ℝ := (G z)^3
theorem node103Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
theorem node103Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 3 : QPoly).mul ⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩)
    ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 3))=true := by kernel_decide
def node103 : RationalCode parameterInterval formula104 :=
  (GCode.pow 3)
  |>.recode ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ ⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ node103Denominator node103Cross

/-- Article: exact source arithmetic node 105. -/
def formula105 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula104 z)
theorem node104Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
theorem node104Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly)))=true := by kernel_decide
def node104 : RationalCode parameterInterval formula105 :=
  ((RationalCode.constant parameterInterval (4)).mul node103)
  |>.recode ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node104Denominator node104Cross

/-- Article: exact source arithmetic node 106. -/
def formula106 (z : ℝ) : ℝ := (formula103 z)+(formula105 z)
theorem node105Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
theorem node105Cross : polynomialCheck
    ((((⟨#[-24,64,-140,128,-70,16,-3]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)).add ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (⟨#[0,-32,0,0,0,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩)
    ((⟨#[128,0,-1472,4096,-7328,4096,4144,-6144,2072,1024,-916,256,-46,0,1]⟩ : QPoly).mul ((⟨#[0,-32,0,0,0,8]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)))=true := by kernel_decide
def node105 : RationalCode parameterInterval formula106 :=
  (node102.add node104)
  |>.recode ⟨#[128,0,-1472,4096,-7328,4096,4144,-6144,2072,1024,-916,256,-46,0,1]⟩ ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ node105Denominator node105Cross

/-- Article: exact source arithmetic node 107. -/
def formula107 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(formula104 z)
theorem node106Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  node104Denominator
theorem node106Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly)))=true := by kernel_decide
def node106 : RationalCode parameterInterval formula107 :=
  ((RationalCode.constant parameterInterval (-4)).mul node103)
  |>.recode ⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node106Denominator node106Cross

/-- Article: exact source arithmetic node 108. -/
def formula108 (z : ℝ) : ℝ := (formula107 z)*(formula45 z)
theorem node107Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
theorem node107Cross : polynomialCheck
    (((⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩)
    ((⟨#[-1024,4096,-8192,10240,-9472,8192,-8192,8192,-6784,4608,-3072,2304,-1696,1024,-512,256,-148,80,-32,8,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node107 : RationalCode parameterInterval formula108 :=
  (node106.mul node44)
  |>.recode ⟨#[-1024,4096,-8192,10240,-9472,8192,-8192,8192,-6784,4608,-3072,2304,-1696,1024,-512,256,-148,80,-32,8,-1]⟩ ⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ node107Denominator node107Cross

/-- Article: exact source arithmetic node 109. -/
def formula109 (z : ℝ) : ℝ := (formula106 z)+(formula108 z)
theorem node108Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
theorem node108Cross : polynomialCheck
    ((((⟨#[128,0,-1472,4096,-7328,4096,4144,-6144,2072,1024,-916,256,-46,0,1]⟩ : QPoly).mul (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly)).add ((⟨#[-1024,4096,-8192,10240,-9472,8192,-8192,8192,-6784,4608,-3072,2304,-1696,1024,-512,256,-148,80,-32,8,-1]⟩ : QPoly).mul (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩)
    ((⟨#[512,-2560,5376,-7808,3072,7168,-8192,800,4160,-4288,2080,200,-1024,448,96,-122,42,-10,1]⟩ : QPoly).mul ((⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).mul (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly)))=true := by kernel_decide
def node108 : RationalCode parameterInterval formula109 :=
  (node105.add node107)
  |>.recode ⟨#[512,-2560,5376,-7808,3072,7168,-8192,800,4160,-4288,2080,200,-1024,448,96,-122,42,-10,1]⟩ ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ node108Denominator node108Cross

/-- Article: exact source arithmetic node 110. -/
def formula110 (z : ℝ) : ℝ := ((fun _ : ℝ => ((3 : ℚ) : ℝ)) z)*(G z)
theorem node109Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  node43Denominator
theorem node109Cross : polynomialCheck
    (((⟨#[3]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[12,0,0,0,3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node109 : RationalCode parameterInterval formula110 :=
  ((RationalCode.constant parameterInterval (3)).mul GCode)
  |>.recode ⟨#[12,0,0,0,3]⟩ ⟨#[0,-16,0,8]⟩ node109Denominator node109Cross

/-- Article: exact source arithmetic node 111. -/
def formula111 (z : ℝ) : ℝ := (formula110 z)*(formula45 z)
theorem node110Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-256,0,128,0,128,0,-64,0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  node45Denominator
theorem node110Cross : polynomialCheck
    (((⟨#[12,0,0,0,3]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-256,0,128,0,128,0,-64,0,-16,0,8]⟩)
    ((⟨#[192,-768,1536,-1920,1680,-1152,768,-576,420,-240,96,-24,3]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node110 : RationalCode parameterInterval formula111 :=
  (node109.mul node44)
  |>.recode ⟨#[192,-768,1536,-1920,1680,-1152,768,-576,420,-240,96,-24,3]⟩ ⟨#[0,-256,0,128,0,128,0,-64,0,-16,0,8]⟩ node110Denominator node110Cross

/-- Article: exact source arithmetic node 112. -/
def formula112 (z : ℝ) : ℝ := (formula109 z)+(formula111 z)
theorem node111Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  node108Denominator
theorem node111Cross : polynomialCheck
    ((((⟨#[512,-2560,5376,-7808,3072,7168,-8192,800,4160,-4288,2080,200,-1024,448,96,-122,42,-10,1]⟩ : QPoly).mul (⟨#[0,-256,0,128,0,128,0,-64,0,-16,0,8]⟩ : QPoly)).add ((⟨#[192,-768,1536,-1920,1680,-1152,768,-576,420,-240,96,-24,3]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩)
    ((⟨#[512,-1024,-768,2944,-6144,8704,-3584,-3424,4928,-3712,2464,-856,-448,544,-192,46,-6,-4,1]⟩ : QPoly).mul ((⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).mul (⟨#[0,-256,0,128,0,128,0,-64,0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node111 : RationalCode parameterInterval formula112 :=
  (node108.add node110)
  |>.recode ⟨#[512,-1024,-768,2944,-6144,8704,-3584,-3424,4928,-3712,2464,-856,-448,544,-192,46,-6,-4,1]⟩ ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ node111Denominator node111Cross

/-- Article: exact source arithmetic node 113. -/
def formula113 (z : ℝ) : ℝ := ((fun z : ℝ => moment z 0) z)*(formula112 z)
theorem node112Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  node108Denominator
theorem node112Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[512,-1024,-768,2944,-6144,8704,-3584,-3424,4928,-3712,2464,-856,-448,544,-192,46,-6,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩)
    ((⟨#[512,-1024,-768,2944,-6144,8704,-3584,-3424,4928,-3712,2464,-856,-448,544,-192,46,-6,-4,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)))=true := by kernel_decide
def node112 : RationalCode parameterInterval formula113 :=
  (moment0Code.mul node111)
  |>.recode ⟨#[512,-1024,-768,2944,-6144,8704,-3584,-3424,4928,-3712,2464,-856,-448,544,-192,46,-6,-4,1]⟩ ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ node112Denominator node112Cross

/-- Article: exact source arithmetic node 114. -/
def formula114 (z : ℝ) : ℝ := (formula101 z)+(formula113 z)
theorem node113Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
theorem node113Cross : polynomialCheck
    ((((⟨#[262144,-1966080,7471104,-20381696,46989312,-90767360,132579328,-131629056,47759360,134537216,-375005184,586805248,-688197632,648388608,-503209984,324194304,-172049408,73350656,-23437824,4204288,746240,-1028352,517888,-177280,45888,-9952,1824,-240,16]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)).add ((⟨#[512,-1024,-768,2944,-6144,8704,-3584,-3424,4928,-3712,2464,-856,-448,544,-192,46,-6,-4,1]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩)
    ((⟨#[327680,-2097152,9699328,-38092800,117473280,-296673280,670826496,-1309540352,1933312000,-1907113984,601063424,2240605184,-6003689472,9324208640,-10910429184,10272204800,-7971015168,5136102400,-2727607296,1165526080,-375230592,70018912,9391616,-14899328,7552000,-2557696,655104,-144860,28680,-4650,592,-64,5]⟩ : QPoly).mul ((⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)))=true := by kernel_decide
def node113 : RationalCode parameterInterval formula114 :=
  (node100.add node112)
  |>.recode ⟨#[327680,-2097152,9699328,-38092800,117473280,-296673280,670826496,-1309540352,1933312000,-1907113984,601063424,2240605184,-6003689472,9324208640,-10910429184,10272204800,-7971015168,5136102400,-2727607296,1165526080,-375230592,70018912,9391616,-14899328,7552000,-2557696,655104,-144860,28680,-4650,592,-64,5]⟩ ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ node113Denominator node113Cross

/-- Article: exact source arithmetic node 115. -/
def formula115 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-10 : ℚ) : ℝ)) z)*(u z)
theorem node114Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node41Denominator
theorem node114Cross : polynomialCheck
    (((⟨#[-10]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-4,0,0,0,1]⟩)
    ((⟨#[-40,80,-80,40,-10]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node114 : RationalCode parameterInterval formula115 :=
  ((RationalCode.constant parameterInterval (-10)).mul uCode)
  |>.recode ⟨#[-40,80,-80,40,-10]⟩ ⟨#[-4,0,0,0,1]⟩ node114Denominator node114Cross

/-- Article: exact source arithmetic node 116. -/
def formula116 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(formula104 z)
theorem node115Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  node104Denominator
theorem node115Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly)))=true := by kernel_decide
def node115 : RationalCode parameterInterval formula116 :=
  ((RationalCode.constant parameterInterval (-4)).mul node103)
  |>.recode ⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node115Denominator node115Cross

/-- Article: exact source arithmetic node 117. -/
def formula117 (z : ℝ) : ℝ := (formula115 z)+(formula116 z)
theorem node116Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).toPoly≠0 :=
  node105Denominator
theorem node116Cross : polynomialCheck
    ((((⟨#[-40,80,-80,40,-10]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)).add ((⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩)
    ((⟨#[-128,0,-64,-20480,40864,-20480,-20528,30720,-10264,-5120,5108,-1280,-2,0,-1]⟩ : QPoly).mul ((⟨#[-4,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)))=true := by kernel_decide
def node116 : RationalCode parameterInterval formula117 :=
  (node114.add node115)
  |>.recode ⟨#[-128,0,-64,-20480,40864,-20480,-20528,30720,-10264,-5120,5108,-1280,-2,0,-1]⟩ ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ node116Denominator node116Cross

/-- Article: exact source arithmetic node 118. -/
def formula118 (z : ℝ) : ℝ := ((fun _ : ℝ => ((3 : ℚ) : ℝ)) z)*(G z)
theorem node117Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  node43Denominator
theorem node117Cross : polynomialCheck
    (((⟨#[3]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[12,0,0,0,3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node117 : RationalCode parameterInterval formula118 :=
  ((RationalCode.constant parameterInterval (3)).mul GCode)
  |>.recode ⟨#[12,0,0,0,3]⟩ ⟨#[0,-16,0,8]⟩ node117Denominator node117Cross

/-- Article: exact source arithmetic node 119. -/
def formula119 (z : ℝ) : ℝ := (formula117 z)+(formula118 z)
theorem node118Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).toPoly≠0 :=
  node105Denominator
theorem node118Cross : polynomialCheck
    ((((⟨#[-128,0,-64,-20480,40864,-20480,-20528,30720,-10264,-5120,5108,-1280,-2,0,-1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)).add ((⟨#[12,0,0,0,3]⟩ : QPoly).mul (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩)
    ((⟨#[-128,0,1472,-20480,40096,-20480,-20528,30720,-10264,-5120,5012,-1280,46,0,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node118 : RationalCode parameterInterval formula119 :=
  (node116.add node117)
  |>.recode ⟨#[-128,0,1472,-20480,40096,-20480,-20528,30720,-10264,-5120,5012,-1280,46,0,-1]⟩ ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ node118Denominator node118Cross

/-- Article: exact source arithmetic node 120. -/
def formula120 (z : ℝ) : ℝ := ((fun z : ℝ => moment z 2) z)*(formula119 z)
theorem node119Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
theorem node119Cross : polynomialCheck
    (((⟨#[0,0,0,-1024,9984,-21504,22528,-19200,15232,-9600,5632,-2688,624,-32]⟩ : QPoly).mul (⟨#[-128,0,1472,-20480,40096,-20480,-20528,30720,-10264,-5120,5012,-1280,46,0,-1]⟩ : QPoly) : QPoly).mul ⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩)
    ((⟨#[8192,-79872,77824,2049024,-17170432,55806464,-95880192,95137024,-49893888,-719616,27155968,-30867840,24385536,-15433920,6788992,-89952,-3118368,2973032,-1498128,435988,-67072,4002,76,-39,2]⟩ : QPoly).mul ((⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly).mul (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly)))=true := by kernel_decide
def node119 : RationalCode parameterInterval formula120 :=
  (moment2Code.mul node118)
  |>.recode ⟨#[8192,-79872,77824,2049024,-17170432,55806464,-95880192,95137024,-49893888,-719616,27155968,-30867840,24385536,-15433920,6788992,-89952,-3118368,2973032,-1498128,435988,-67072,4002,76,-39,2]⟩ ⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ node119Denominator node119Cross

/-- Article: exact source arithmetic node 121. -/
def formula121 (z : ℝ) : ℝ := (formula114 z)+(formula120 z)
theorem node120Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
theorem node120Cross : polynomialCheck
    ((((⟨#[327680,-2097152,9699328,-38092800,117473280,-296673280,670826496,-1309540352,1933312000,-1907113984,601063424,2240605184,-6003689472,9324208640,-10910429184,10272204800,-7971015168,5136102400,-2727607296,1165526080,-375230592,70018912,9391616,-14899328,7552000,-2557696,655104,-144860,28680,-4650,592,-64,5]⟩ : QPoly).mul (⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ : QPoly)).add ((⟨#[8192,-79872,77824,2049024,-17170432,55806464,-95880192,95137024,-49893888,-719616,27155968,-30867840,24385536,-15433920,6788992,-89952,-3118368,2973032,-1498128,435988,-67072,4002,76,-39,2]⟩ : QPoly).mul (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩)
    ((⟨#[327680,-2097152,9764864,-38731776,118161408,-280920064,534102016,-846856192,1029062656,-695468032,-599470080,3107557376,-6377353216,9261783040,-10597884928,9900351488,-7667307008,4950175744,-2649471232,1157722880,-398584576,97111168,-9366720,-5433344,4019776,-1654016,521584,-137168,28848,-4728,596,-64,5]⟩ : QPoly).mul ((⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).mul (⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ : QPoly)))=true := by kernel_decide
def node120 : RationalCode parameterInterval formula121 :=
  (node113.add node119)
  |>.recode ⟨#[327680,-2097152,9764864,-38731776,118161408,-280920064,534102016,-846856192,1029062656,-695468032,-599470080,3107557376,-6377353216,9261783040,-10597884928,9900351488,-7667307008,4950175744,-2649471232,1157722880,-398584576,97111168,-9366720,-5433344,4019776,-1654016,521584,-137168,28848,-4728,596,-64,5]⟩ ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ node120Denominator node120Cross

/-- Article: exact source arithmetic node 122. -/
def formula122 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula45 z)
theorem node121Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node44Denominator
theorem node121Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[64,-256,512,-640,544,-320,128,-32,4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node121 : RationalCode parameterInterval formula122 :=
  ((RationalCode.constant parameterInterval (4)).mul node44)
  |>.recode ⟨#[64,-256,512,-640,544,-320,128,-32,4]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node121Denominator node121Cross

/-- Article: exact source arithmetic node 123. -/
def formula123 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-7 : ℚ) : ℝ)) z)+(formula122 z)
theorem node122Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node44Denominator
theorem node122Cross : polynomialCheck
    ((((⟨#[-7]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)).add ((⟨#[64,-256,512,-640,544,-320,128,-32,4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[-48,-256,512,-640,600,-320,128,-32,-3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node122 : RationalCode parameterInterval formula123 :=
  ((RationalCode.constant parameterInterval (-7)).add node121)
  |>.recode ⟨#[-48,-256,512,-640,600,-320,128,-32,-3]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node122Denominator node122Cross

/-- Article: exact source arithmetic node 124. -/
def formula124 (z : ℝ) : ℝ := ((fun z : ℝ => moment z 3) z)*(formula123 z)
theorem node123Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
theorem node123Cross : polynomialCheck
    (((⟨#[0,0,4096,-6144,6144,-52224,111616,-113152,78336,-36096,14336,-18048,19584,-14144,6976,-1632,96,-48,16]⟩ : QPoly).mul (⟨#[-48,-256,512,-640,600,-320,128,-32,-3]⟩ : QPoly) : QPoly).mul ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩)
    ((⟨#[0,0,-196608,-753664,3375104,-4833280,17547264,-58810368,121954304,-181907456,205729792,-181891072,133271552,-87373824,58329088,-43686912,33317888,-22736384,12858112,-5684608,1905536,-459456,68544,-9440,3296,-368,-48]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node123 : RationalCode parameterInterval formula124 :=
  (moment3Code.mul node122)
  |>.recode ⟨#[0,0,-196608,-753664,3375104,-4833280,17547264,-58810368,121954304,-181907456,205729792,-181891072,133271552,-87373824,58329088,-43686912,33317888,-22736384,12858112,-5684608,1905536,-459456,68544,-9440,3296,-368,-48]⟩ ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ node123Denominator node123Cross

/-- Article: exact source arithmetic node 125. -/
def formula125 (z : ℝ) : ℝ := (formula121 z)+(formula124 z)
theorem node124Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
theorem node124Cross : polynomialCheck
    ((((⟨#[327680,-2097152,9764864,-38731776,118161408,-280920064,534102016,-846856192,1029062656,-695468032,-599470080,3107557376,-6377353216,9261783040,-10597884928,9900351488,-7667307008,4950175744,-2649471232,1157722880,-398584576,97111168,-9366720,-5433344,4019776,-1654016,521584,-137168,28848,-4728,596,-64,5]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,-196608,-753664,3375104,-4833280,17547264,-58810368,121954304,-181907456,205729792,-181891072,133271552,-87373824,58329088,-43686912,33317888,-22736384,12858112,-5684608,1905536,-459456,68544,-9440,3296,-368,-48]⟩ : QPoly).mul (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩)
    ((⟨#[327680,-2097152,9764864,-38731776,115015680,-292978688,588103680,-924188672,1309818880,-1636433920,1351798784,197038080,-3085676544,6351525888,-8465540096,8502370304,-6734041600,4251185152,-2116385024,793940736,-192854784,6157440,21121856,-12784640,5116480,-1805056,574320,-143056,28080,-4728,596,-64,5]⟩ : QPoly).mul ((⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node124 : RationalCode parameterInterval formula125 :=
  (node120.add node123)
  |>.recode ⟨#[327680,-2097152,9764864,-38731776,115015680,-292978688,588103680,-924188672,1309818880,-1636433920,1351798784,197038080,-3085676544,6351525888,-8465540096,8502370304,-6734041600,4251185152,-2116385024,793940736,-192854784,6157440,21121856,-12784640,5116480,-1805056,574320,-143056,28080,-4728,596,-64,5]⟩ ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ node124Denominator node124Cross

/-- Article: exact source arithmetic node 126. -/
def formula126 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula70 z)
theorem node125Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
theorem node125Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
def node125 : RationalCode parameterInterval formula126 :=
  ((RationalCode.constant parameterInterval (4)).mul node69)
  |>.recode ⟨#[16,0,0,0,8,0,0,0,1]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node125Denominator node125Cross

/-- Article: exact source arithmetic node 127. -/
def formula127 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)+(formula126 z)
theorem node126Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  node125Denominator
theorem node126Cross : polynomialCheck
    ((((⟨#[-1]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)).add ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[16,0,-64,0,72,0,-16,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
def node126 : RationalCode parameterInterval formula127 :=
  ((RationalCode.constant parameterInterval (-1)).add node125)
  |>.recode ⟨#[16,0,-64,0,72,0,-16,0,1]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node126Denominator node126Cross

/-- Article: exact source arithmetic node 128. -/
def formula128 (z : ℝ) : ℝ := (d z)*(formula127 z)
theorem node127Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
theorem node127Cross : polynomialCheck
    (((⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ : QPoly).mul (⟨#[16,0,-64,0,72,0,-16,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩)
    ((⟨#[81920,-524288,1048576,1327104,-10588160,20193280,-9306112,-30191616,68809728,-66050048,18153472,39856128,-74049792,77263872,-61030400,38631936,-18512448,4982016,1134592,-2064064,1075152,-235872,-36352,39440,-10340,648,256,-64,5]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
def node127 : RationalCode parameterInterval formula128 :=
  (dCode.mul node126)
  |>.recode ⟨#[81920,-524288,1048576,1327104,-10588160,20193280,-9306112,-30191616,68809728,-66050048,18153472,39856128,-74049792,77263872,-61030400,38631936,-18512448,4982016,1134592,-2064064,1075152,-235872,-36352,39440,-10340,648,256,-64,5]⟩ ⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ node127Denominator node127Cross

/-- Article: exact source arithmetic node 129. -/
def formula129 (z : ℝ) : ℝ := (formula125 z)+(formula128 z)
theorem node128Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
theorem node128Cross : polynomialCheck
    ((((⟨#[327680,-2097152,9764864,-38731776,115015680,-292978688,588103680,-924188672,1309818880,-1636433920,1351798784,197038080,-3085676544,6351525888,-8465540096,8502370304,-6734041600,4251185152,-2116385024,793940736,-192854784,6157440,21121856,-12784640,5116480,-1805056,574320,-143056,28080,-4728,596,-64,5]⟩ : QPoly).mul (⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ : QPoly)).add ((⟨#[81920,-524288,1048576,1327104,-10588160,20193280,-9306112,-30191616,68809728,-66050048,18153472,39856128,-74049792,77263872,-61030400,38631936,-18512448,4982016,1134592,-2064064,1075152,-235872,-36352,39440,-10340,648,256,-64,5]⟩ : QPoly).mul (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩)
    ((⟨#[327680,-2097152,7143424,-17760256,38469632,-103710720,254787584,-481427456,768622592,-1000603648,845172736,31035392,-1620226048,3376977920,-4493853696,4502904832,-3563131392,2251452416,-1123463424,422122240,-101264128,969856,13205824,-7817216,3002432,-940288,248816,-50640,9392,-2168,436,-64,5]⟩ : QPoly).mul ((⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).mul (⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ : QPoly)))=true := by kernel_decide
def node128 : RationalCode parameterInterval formula129 :=
  (node124.add node127)
  |>.recode ⟨#[327680,-2097152,7143424,-17760256,38469632,-103710720,254787584,-481427456,768622592,-1000603648,845172736,31035392,-1620226048,3376977920,-4493853696,4502904832,-3563131392,2251452416,-1123463424,422122240,-101264128,969856,13205824,-7817216,3002432,-940288,248816,-50640,9392,-2168,436,-64,5]⟩ ⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ node128Denominator node128Cross

/-- Article: exact source arithmetic node 130. -/
def formula130 (z : ℝ) : ℝ := ((fun _ : ℝ => ((3 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 1) z)
theorem node129Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node76Denominator
theorem node129Cross : polynomialCheck
    (((⟨#[3]⟩ : QPoly).mul (⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ : QPoly) : QPoly).mul ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩)
    ((⟨#[0,0,2880,-8832,10752,-10560,9120,-5280,2688,-1104,180]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node129 : RationalCode parameterInterval formula130 :=
  ((RationalCode.constant parameterInterval (3)).mul moment1Code)
  |>.recode ⟨#[0,0,2880,-8832,10752,-10560,9120,-5280,2688,-1104,180]⟩ ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ node129Denominator node129Cross

/-- Article: exact source arithmetic node 131. -/
def formula131 (z : ℝ) : ℝ := (formula130 z)*(formula85 z)
theorem node130Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node5Denominator
theorem node130Cross : polynomialCheck
    (((⟨#[0,0,2880,-8832,10752,-10560,9120,-5280,2688,-1104,180]⟩ : QPoly).mul (⟨#[0,64,-128,160,-144,80,-32,8]⟩ : QPoly) : QPoly).mul ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩)
    ((⟨#[0,0,0,184320,-933888,2279424,-3879936,5157888,-5541888,4993536,-3832320,2496768,-1385472,644736,-242496,71232,-14592,1440]⟩ : QPoly).mul ((⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node130 : RationalCode parameterInterval formula131 :=
  (node129.mul node84)
  |>.recode ⟨#[0,0,0,184320,-933888,2279424,-3879936,5157888,-5541888,4993536,-3832320,2496768,-1385472,644736,-242496,71232,-14592,1440]⟩ ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ node130Denominator node130Cross

/-- Article: exact source arithmetic node 132. -/
def formula132 (z : ℝ) : ℝ := (formula129 z)+(formula131 z)
theorem node131Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ : QPoly).toPoly≠0 :=
  node128Denominator
theorem node131Cross : polynomialCheck
    ((((⟨#[327680,-2097152,7143424,-17760256,38469632,-103710720,254787584,-481427456,768622592,-1000603648,845172736,31035392,-1620226048,3376977920,-4493853696,4502904832,-3563131392,2251452416,-1123463424,422122240,-101264128,969856,13205824,-7817216,3002432,-940288,248816,-50640,9392,-2168,436,-64,5]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,0,184320,-933888,2279424,-3879936,5157888,-5541888,4993536,-3832320,2496768,-1385472,644736,-242496,71232,-14592,1440]⟩ : QPoly).mul (⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩)
    ((⟨#[327680,-2097152,7143424,-17760256,38469632,-80117760,135249920,-189661184,271990784,-352190464,195579904,524324864,-1862447104,3367933952,-4323984384,4284080128,-3379941888,2142040064,-1080996096,420991744,-116402944,16385152,3055936,-2751488,1062464,-370432,132080,-39120,9392,-2168,436,-64,5]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node131 : RationalCode parameterInterval formula132 :=
  (node128.add node130)
  |>.recode ⟨#[327680,-2097152,7143424,-17760256,38469632,-80117760,135249920,-189661184,271990784,-352190464,195579904,524324864,-1862447104,3367933952,-4323984384,4284080128,-3379941888,2142040064,-1080996096,420991744,-116402944,16385152,3055936,-2751488,1062464,-370432,132080,-39120,9392,-2168,436,-64,5]⟩ ⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ node131Denominator node131Cross

/-- Article: exact source arithmetic node 133. -/
def formula133 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 4) z)
theorem node132Denominator : ∀ z∈parameterInterval, aeval z (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
theorem node132Cross : polynomialCheck
    (((⟨#[8]⟩ : QPoly).mul (⟨#[0,-16384,73728,-172032,409600,-757760,976896,-829440,-61440,1554432,-2796544,3165184,-2605056,1582592,-699136,194304,-3840,-25920,15264,-5920,1600,-336,72,-8]⟩ : QPoly) : QPoly).mul ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩)
    ((⟨#[0,-131072,589824,-1376256,3276800,-6062080,7815168,-6635520,-491520,12435456,-22372352,25321472,-20840448,12660736,-5593088,1554432,-30720,-207360,122112,-47360,12800,-2688,576,-64]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node132 : RationalCode parameterInterval formula133 :=
  ((RationalCode.constant parameterInterval (8)).mul moment4Code)
  |>.recode ⟨#[0,-131072,589824,-1376256,3276800,-6062080,7815168,-6635520,-491520,12435456,-22372352,25321472,-20840448,12660736,-5593088,1554432,-30720,-207360,122112,-47360,12800,-2688,576,-64]⟩ ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ node132Denominator node132Cross

/-- Article: exact source arithmetic node 134. -/
def formula134 (z : ℝ) : ℝ := (formula133 z)*(u z)
theorem node133Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
theorem node133Cross : polynomialCheck
    (((⟨#[0,-131072,589824,-1376256,3276800,-6062080,7815168,-6635520,-491520,12435456,-22372352,25321472,-20840448,12660736,-5593088,1554432,-30720,-207360,122112,-47360,12800,-2688,576,-64]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩)
    ((⟨#[0,-524288,3407872,-11272192,29360128,-63963136,112066560,-152043520,141164544,-36732928,-158547968,375078912,-515145728,521863168,-414040064,260931584,-128786432,46884864,-9909248,-1147904,2205696,-1187840,437760,-124928,28672,-5504,832,-64]⟩ : QPoly).mul ((⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node133 : RationalCode parameterInterval formula134 :=
  (node132.mul uCode)
  |>.recode ⟨#[0,-524288,3407872,-11272192,29360128,-63963136,112066560,-152043520,141164544,-36732928,-158547968,375078912,-515145728,521863168,-414040064,260931584,-128786432,46884864,-9909248,-1147904,2205696,-1187840,437760,-124928,28672,-5504,832,-64]⟩ ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ node133Denominator node133Cross

/-- Article: exact source arithmetic node 135. -/
def formula135 (z : ℝ) : ℝ := (formula132 z)+(formula134 z)
theorem node134Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ : QPoly).toPoly≠0 :=
  node128Denominator
theorem node134Cross : polynomialCheck
    ((((⟨#[327680,-2097152,7143424,-17760256,38469632,-80117760,135249920,-189661184,271990784,-352190464,195579904,524324864,-1862447104,3367933952,-4323984384,4284080128,-3379941888,2142040064,-1080996096,420991744,-116402944,16385152,3055936,-2751488,1062464,-370432,132080,-39120,9392,-2168,436,-64,5]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,-524288,3407872,-11272192,29360128,-63963136,112066560,-152043520,141164544,-36732928,-158547968,375078912,-515145728,521863168,-414040064,260931584,-128786432,46884864,-9909248,-1147904,2205696,-1187840,437760,-124928,28672,-5504,832,-64]⟩ : QPoly).mul (⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩)
    ((⟨#[327680,-2097152,7143424,-21954560,65732608,-170295296,370130944,-701366272,1168523264,-1568538624,1324896256,230461440,-3130830848,6368565248,-8445150208,8458985472,-6692262400,4229492736,-2111287552,796070656,-195676928,7201920,20701504,-12254208,4564544,-1369856,361456,-83152,16048,-2680,436,-64,5]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node134 : RationalCode parameterInterval formula135 :=
  (node131.add node133)
  |>.recode ⟨#[327680,-2097152,7143424,-21954560,65732608,-170295296,370130944,-701366272,1168523264,-1568538624,1324896256,230461440,-3130830848,6368565248,-8445150208,8458985472,-6692262400,4229492736,-2111287552,796070656,-195676928,7201920,20701504,-12254208,4564544,-1369856,361456,-83152,16048,-2680,436,-64,5]⟩ ⟨#[0,0,-655360,2883584,-5242880,4587520,-2654208,-262144,5242880,-5898240,3891200,-2113536,-1638400,2940928,-2017280,1376256,0,-688128,504320,-367616,102400,66048,-60800,46080,-20480,512,2592,-2240,1280,-352,40]⟩ node134Denominator node134Cross

/-- Article: exact coefficient representation of the independently specified lower3Expression source. -/
def lower3ExpressionCode : RationalCode parameterInterval (fun z : ℝ => ((4*(moment z 5))+((moment z 0)*((-3*(G z))+(2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2)))+((moment z 1)*(3+(-3*((u z))^2)))+((moment z 2)*((-10*(u z))+(-4*((G z))^3)+(3*(G z))))+((moment z 3)*(-7+(4*((u z))^2)))+((d z)*(-1+(4*((G z))^2)))+(8*(moment z 4)*(u z)))) where
  numerator := node134.numerator
  denominator := node134.denominator
  denominator_ne := node134.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((4*(moment z 5))+((moment z 0)*((-3*(G z))+(2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2)))+((moment z 1)*(3+(-3*((u z))^2)))+((moment z 2)*((-10*(u z))+(-4*((G z))^3)+(3*(G z))))+((moment z 3)*(-7+(4*((u z))^2)))+((d z)*(-1+(4*((G z))^2)))+(8*(moment z 4)*(u z)))) z=formula135 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node134.exact z hz)

/-- Article: compact exact representation of the actual raw lower3 source. -/
def lower3ActualCode : RationalCode parameterInterval (fun z => reducedSlack z 3 (-1 : ℝ)) where
  numerator := lower3ExpressionCode.numerator
  denominator := lower3ExpressionCode.denominator
  denominator_ne := lower3ExpressionCode.denominator_ne
  exact z hz := (lower3_source z).trans (lower3ExpressionCode.exact z hz)

/-- Article: the actual raw lower3 is strictly positive throughout J. -/
theorem lower3_positive : ∀ z∈parameterInterval,0<reducedSlack z 3 (-1 : ℝ) :=
  lower3ActualCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 136. -/
def formula136 (z : ℝ) : ℝ := (formula102 z)+(formula42 z)
theorem node135Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-32,0,0,0,8]⟩ : QPoly).toPoly≠0 :=
  node42Denominator
theorem node135Cross : polynomialCheck
    ((((⟨#[-12,0,0,0,-3]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)).add ((⟨#[-8,16,-16,8,-2]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,-32,0,0,0,8]⟩)
    ((⟨#[-24,-64,116,-128,58,-16,-3]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node135 : RationalCode parameterInterval formula136 :=
  (node101.add node41)
  |>.recode ⟨#[-24,-64,116,-128,58,-16,-3]⟩ ⟨#[0,-32,0,0,0,8]⟩ node135Denominator node135Cross

/-- Article: exact source arithmetic node 137. -/
def formula137 (z : ℝ) : ℝ := (formula136 z)+(formula105 z)
theorem node136Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).toPoly≠0 :=
  node105Denominator
theorem node136Cross : polynomialCheck
    ((((⟨#[-24,-64,116,-128,58,-16,-3]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)).add ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (⟨#[0,-32,0,0,0,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩)
    ((⟨#[128,0,-1472,-4096,9056,-4096,-4048,6144,-2024,-1024,1132,-256,-46,0,1]⟩ : QPoly).mul ((⟨#[0,-32,0,0,0,8]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)))=true := by kernel_decide
def node136 : RationalCode parameterInterval formula137 :=
  (node135.add node104)
  |>.recode ⟨#[128,0,-1472,-4096,9056,-4096,-4048,6144,-2024,-1024,1132,-256,-46,0,1]⟩ ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ node136Denominator node136Cross

/-- Article: exact source arithmetic node 138. -/
def formula138 (z : ℝ) : ℝ := (formula137 z)+(formula108 z)
theorem node137Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  node108Denominator
theorem node137Cross : polynomialCheck
    ((((⟨#[128,0,-1472,-4096,9056,-4096,-4048,6144,-2024,-1024,1132,-256,-46,0,1]⟩ : QPoly).mul (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly)).add ((⟨#[-1024,4096,-8192,10240,-9472,8192,-8192,8192,-6784,4608,-3072,2304,-1696,1024,-512,256,-148,80,-32,8,-1]⟩ : QPoly).mul (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩)
    ((⟨#[512,-2560,-2816,8576,-1024,-9216,10240,-3296,-3008,3904,-1504,-824,1280,-576,-32,134,-22,-10,1]⟩ : QPoly).mul ((⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).mul (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly)))=true := by kernel_decide
def node137 : RationalCode parameterInterval formula138 :=
  (node136.add node107)
  |>.recode ⟨#[512,-2560,-2816,8576,-1024,-9216,10240,-3296,-3008,3904,-1504,-824,1280,-576,-32,134,-22,-10,1]⟩ ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ node137Denominator node137Cross

/-- Article: exact source arithmetic node 139. -/
def formula139 (z : ℝ) : ℝ := (formula138 z)+(formula111 z)
theorem node138Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  node108Denominator
theorem node138Cross : polynomialCheck
    ((((⟨#[512,-2560,-2816,8576,-1024,-9216,10240,-3296,-3008,3904,-1504,-824,1280,-576,-32,134,-22,-10,1]⟩ : QPoly).mul (⟨#[0,-256,0,128,0,128,0,-64,0,-16,0,8]⟩ : QPoly)).add ((⟨#[192,-768,1536,-1920,1680,-1152,768,-576,420,-240,96,-24,3]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩)
    ((⟨#[512,-1024,-8960,19328,-10240,-7680,14848,-7520,-2240,4480,-1120,-1880,1856,-480,-320,302,-70,-4,1]⟩ : QPoly).mul ((⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).mul (⟨#[0,-256,0,128,0,128,0,-64,0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node138 : RationalCode parameterInterval formula139 :=
  (node137.add node110)
  |>.recode ⟨#[512,-1024,-8960,19328,-10240,-7680,14848,-7520,-2240,4480,-1120,-1880,1856,-480,-320,302,-70,-4,1]⟩ ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ node138Denominator node138Cross

/-- Article: exact source arithmetic node 140. -/
def formula140 (z : ℝ) : ℝ := ((fun z : ℝ => moment z 0) z)*(formula139 z)
theorem node139Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  node108Denominator
theorem node139Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[512,-1024,-8960,19328,-10240,-7680,14848,-7520,-2240,4480,-1120,-1880,1856,-480,-320,302,-70,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩)
    ((⟨#[512,-1024,-8960,19328,-10240,-7680,14848,-7520,-2240,4480,-1120,-1880,1856,-480,-320,302,-70,-4,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)))=true := by kernel_decide
def node139 : RationalCode parameterInterval formula140 :=
  (moment0Code.mul node138)
  |>.recode ⟨#[512,-1024,-8960,19328,-10240,-7680,14848,-7520,-2240,4480,-1120,-1880,1856,-480,-320,302,-70,-4,1]⟩ ⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ node139Denominator node139Cross

/-- Article: exact source arithmetic node 141. -/
def formula141 (z : ℝ) : ℝ := (formula101 z)+(formula140 z)
theorem node140Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
theorem node140Cross : polynomialCheck
    ((((⟨#[262144,-1966080,7471104,-20381696,46989312,-90767360,132579328,-131629056,47759360,134537216,-375005184,586805248,-688197632,648388608,-503209984,324194304,-172049408,73350656,-23437824,4204288,746240,-1028352,517888,-177280,45888,-9952,1824,-240,16]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)).add ((⟨#[512,-1024,-8960,19328,-10240,-7680,14848,-7520,-2240,4480,-1120,-1880,1856,-480,-320,302,-70,-4,1]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩)
    ((⟨#[327680,-2097152,4456448,-4538368,18907136,-124706816,466616320,-1139671040,1865154560,-1968979968,756187136,2067065856,-5880088576,9281741312,-10936365056,10328041472,-8021215744,5164020736,-2734091264,1160217664,-367505536,64595808,11815424,-15382656,7285760,-2225920,455680,-60892,4616,-554,272,-64,5]⟩ : QPoly).mul ((⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).mul (⟨#[0,0,-2048,0,3072,0,-512,0,-1280,0,640,0,64,0,-96,0,16]⟩ : QPoly)))=true := by kernel_decide
def node140 : RationalCode parameterInterval formula141 :=
  (node100.add node139)
  |>.recode ⟨#[327680,-2097152,4456448,-4538368,18907136,-124706816,466616320,-1139671040,1865154560,-1968979968,756187136,2067065856,-5880088576,9281741312,-10936365056,10328041472,-8021215744,5164020736,-2734091264,1160217664,-367505536,64595808,11815424,-15382656,7285760,-2225920,455680,-60892,4616,-554,272,-64,5]⟩ ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ node140Denominator node140Cross

/-- Article: exact source arithmetic node 142. -/
def formula142 (z : ℝ) : ℝ := (formula116 z)+(formula118 z)
theorem node141Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  node104Denominator
theorem node141Cross : polynomialCheck
    ((((⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)).add ((⟨#[12,0,0,0,3]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[-64,0,768,0,-816,0,384,0,-204,0,48,0,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
def node141 : RationalCode parameterInterval formula142 :=
  (node115.add node117)
  |>.recode ⟨#[-64,0,768,0,-816,0,384,0,-204,0,48,0,-1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node141Denominator node141Cross

/-- Article: exact source arithmetic node 143. -/
def formula143 (z : ℝ) : ℝ := ((fun _ : ℝ => ((10 : ℚ) : ℝ)) z)*(u z)
theorem node142Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node41Denominator
theorem node142Cross : polynomialCheck
    (((⟨#[10]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-4,0,0,0,1]⟩)
    ((⟨#[40,-80,80,-40,10]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node142 : RationalCode parameterInterval formula143 :=
  ((RationalCode.constant parameterInterval (10)).mul uCode)
  |>.recode ⟨#[40,-80,80,-40,10]⟩ ⟨#[-4,0,0,0,1]⟩ node142Denominator node142Cross

/-- Article: exact source arithmetic node 144. -/
def formula144 (z : ℝ) : ℝ := (formula142 z)+(formula143 z)
theorem node143Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly).toPoly≠0 :=
  node105Denominator
theorem node143Cross : polynomialCheck
    ((((⟨#[-64,0,768,0,-816,0,384,0,-204,0,48,0,-1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)).add ((⟨#[40,-80,80,-40,10]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩)
    ((⟨#[-128,0,1472,20480,-41824,20480,20432,-30720,10216,5120,-5228,1280,46,0,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node143 : RationalCode parameterInterval formula144 :=
  (node141.add node142)
  |>.recode ⟨#[-128,0,1472,20480,-41824,20480,20432,-30720,10216,5120,-5228,1280,46,0,-1]⟩ ⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ node143Denominator node143Cross

/-- Article: exact source arithmetic node 145. -/
def formula145 (z : ℝ) : ℝ := ((fun z : ℝ => moment z 2) z)*(formula144 z)
theorem node144Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ : QPoly).toPoly≠0 :=
  node119Denominator
theorem node144Cross : polynomialCheck
    (((⟨#[0,0,0,-1024,9984,-21504,22528,-19200,15232,-9600,5632,-2688,624,-32]⟩ : QPoly).mul (⟨#[-128,0,1472,20480,-41824,20480,20432,-30720,10216,5120,-5228,1280,46,0,-1]⟩ : QPoly) : QPoly).mul ⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩)
    ((⟨#[8192,-79872,77824,-572416,13631488,-52983296,94829568,-94917376,50376192,-64256,-26419712,30080640,-23701504,15040320,-6604928,-8032,3148512,-2966168,1481712,-413932,53248,-1118,76,-39,2]⟩ : QPoly).mul ((⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly).mul (⟨#[0,0,0,-2048,0,2048,0,0,0,-512,0,128]⟩ : QPoly)))=true := by kernel_decide
def node144 : RationalCode parameterInterval formula145 :=
  (moment2Code.mul node143)
  |>.recode ⟨#[8192,-79872,77824,-572416,13631488,-52983296,94829568,-94917376,50376192,-64256,-26419712,30080640,-23701504,15040320,-6604928,-8032,3148512,-2966168,1481712,-413932,53248,-1118,76,-39,2]⟩ ⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ node144Denominator node144Cross

/-- Article: exact source arithmetic node 146. -/
def formula146 (z : ℝ) : ℝ := (formula141 z)+(formula145 z)
theorem node145Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
theorem node145Cross : polynomialCheck
    ((((⟨#[327680,-2097152,4456448,-4538368,18907136,-124706816,466616320,-1139671040,1865154560,-1968979968,756187136,2067065856,-5880088576,9281741312,-10936365056,10328041472,-8021215744,5164020736,-2734091264,1160217664,-367505536,64595808,11815424,-15382656,7285760,-2225920,455680,-60892,4616,-554,272,-64,5]⟩ : QPoly).mul (⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ : QPoly)).add ((⟨#[8192,-79872,77824,-572416,13631488,-52983296,94829568,-94917376,50376192,-64256,-26419712,30080640,-23701504,15040320,-6604928,-8032,3148512,-2966168,1481712,-413932,53248,-1118,76,-39,2]⟩ : QPoly).mul (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩)
    ((⟨#[327680,-2097152,4521984,-5177344,19595264,-129925120,576307200,-1568276480,2732998656,-3153330176,1945096192,1201246208,-5498777600,9332037632,-11236582400,10688880640,-8316506624,5344440320,-2809145600,1166504704,-343673600,37538944,30392128,-24635392,10675776,-3063040,562800,-63440,4784,-632,276,-64,5]⟩ : QPoly).mul ((⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).mul (⟨#[-163840,720896,-1146880,425984,524288,-671744,1073152,-909312,-231424,548864,-446464,413696,0,-206848,111616,-68608,14464,28416,-16768,5248,-2048,-832,1120,-352,40]⟩ : QPoly)))=true := by kernel_decide
def node145 : RationalCode parameterInterval formula146 :=
  (node140.add node144)
  |>.recode ⟨#[327680,-2097152,4521984,-5177344,19595264,-129925120,576307200,-1568276480,2732998656,-3153330176,1945096192,1201246208,-5498777600,9332037632,-11236582400,10688880640,-8316506624,5344440320,-2809145600,1166504704,-343673600,37538944,30392128,-24635392,10675776,-3063040,562800,-63440,4784,-632,276,-64,5]⟩ ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ node145Denominator node145Cross

/-- Article: exact source arithmetic node 147. -/
def formula147 (z : ℝ) : ℝ := (formula146 z)+(formula124 z)
theorem node146Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
theorem node146Cross : polynomialCheck
    ((((⟨#[327680,-2097152,4521984,-5177344,19595264,-129925120,576307200,-1568276480,2732998656,-3153330176,1945096192,1201246208,-5498777600,9332037632,-11236582400,10688880640,-8316506624,5344440320,-2809145600,1166504704,-343673600,37538944,30392128,-24635392,10675776,-3063040,562800,-63440,4784,-632,276,-64,5]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,-196608,-753664,3375104,-4833280,17547264,-58810368,121954304,-181907456,205729792,-181891072,133271552,-87373824,58329088,-43686912,33317888,-22736384,12858112,-5684608,1905536,-459456,68544,-9440,3296,-368,-48]⟩ : QPoly).mul (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩)
    ((⟨#[327680,-2097152,4521984,-5177344,16449536,-141983744,630308864,-1645608960,3013754880,-4094296064,3896365056,-1709273088,-2207100928,6421780480,-9104237568,9290899456,-7383241216,4645449728,-2276059392,802722560,-137943808,-53414784,60880704,-31986688,11772480,-3214080,615536,-69328,4016,-632,276,-64,5]⟩ : QPoly).mul ((⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node146 : RationalCode parameterInterval formula147 :=
  (node145.add node123)
  |>.recode ⟨#[327680,-2097152,4521984,-5177344,16449536,-141983744,630308864,-1645608960,3013754880,-4094296064,3896365056,-1709273088,-2207100928,6421780480,-9104237568,9290899456,-7383241216,4645449728,-2276059392,802722560,-137943808,-53414784,60880704,-31986688,11772480,-3214080,615536,-69328,4016,-632,276,-64,5]⟩ ⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ node146Denominator node146Cross

/-- Article: exact source arithmetic node 148. -/
def formula148 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(d z)
theorem node147Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node5Denominator
theorem node147Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ : QPoly) : QPoly).mul ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩)
    ((⟨#[-5120,32768,-86016,48128,340736,-1217024,2326528,-3164928,3386496,-3008896,2288128,-1504448,846624,-395616,145408,-38032,5324,376,-336,64,-5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node147 : RationalCode parameterInterval formula148 :=
  ((RationalCode.constant parameterInterval (-1)).mul dCode)
  |>.recode ⟨#[-5120,32768,-86016,48128,340736,-1217024,2326528,-3164928,3386496,-3008896,2288128,-1504448,846624,-395616,145408,-38032,5324,376,-336,64,-5]⟩ ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ node147Denominator node147Cross

/-- Article: exact source arithmetic node 149. -/
def formula149 (z : ℝ) : ℝ := (formula148 z)*(formula127 z)
theorem node148Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ : QPoly).toPoly≠0 :=
  node127Denominator
theorem node148Cross : polynomialCheck
    (((⟨#[-5120,32768,-86016,48128,340736,-1217024,2326528,-3164928,3386496,-3008896,2288128,-1504448,846624,-395616,145408,-38032,5324,376,-336,64,-5]⟩ : QPoly).mul (⟨#[16,0,-64,0,72,0,-16,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩)
    ((⟨#[-81920,524288,-1048576,-1327104,10588160,-20193280,9306112,30191616,-68809728,66050048,-18153472,-39856128,74049792,-77263872,61030400,-38631936,18512448,-4982016,-1134592,2064064,-1075152,235872,36352,-39440,10340,-648,-256,64,-5]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
def node148 : RationalCode parameterInterval formula149 :=
  (node147.mul node126)
  |>.recode ⟨#[-81920,524288,-1048576,-1327104,10588160,-20193280,9306112,30191616,-68809728,66050048,-18153472,-39856128,74049792,-77263872,61030400,-38631936,18512448,-4982016,-1134592,2064064,-1075152,235872,36352,-39440,10340,-648,-256,64,-5]⟩ ⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ node148Denominator node148Cross

/-- Article: exact source arithmetic node 150. -/
def formula150 (z : ℝ) : ℝ := (formula147 z)+(formula149 z)
theorem node149Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
theorem node149Cross : polynomialCheck
    ((((⟨#[327680,-2097152,4521984,-5177344,16449536,-141983744,630308864,-1645608960,3013754880,-4094296064,3896365056,-1709273088,-2207100928,6421780480,-9104237568,9290899456,-7383241216,4645449728,-2276059392,802722560,-137943808,-53414784,60880704,-31986688,11772480,-3214080,615536,-69328,4016,-632,276,-64,5]⟩ : QPoly).mul (⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ : QPoly)).add ((⟨#[-81920,524288,-1048576,-1327104,10588160,-20193280,9306112,30191616,-68809728,66050048,-18153472,-39856128,74049792,-77263872,61030400,-38631936,18512448,-4982016,-1134592,2064064,-1075152,235872,36352,-39440,10340,-648,-256,64,-5]⟩ : QPoly).mul (⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly)) : QPoly).mul ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩)
    ((⟨#[0,-524288,3407872,-14221312,44302336,-100433920,174145536,-233095168,222363648,-98394112,-128270336,376209408,-536379392,549216256,-436938752,274608128,-134094848,47026176,-8016896,-3074816,3474432,-1821056,680256,-196160,43264,-6944,832,-64]⟩ : QPoly).mul ((⟨#[0,0,-1310720,5767168,-10485760,9175040,-5308416,-524288,10485760,-11796480,7782400,-4227072,-3276800,5881856,-4034560,2752512,0,-1376256,1008640,-735232,204800,132096,-121600,92160,-40960,1024,5184,-4480,2560,-704,80]⟩ : QPoly).mul (⟨#[0,0,-327680,1441792,-2293760,851968,1048576,-1343488,2146304,-1818624,-462848,1097728,-892928,827392,0,-413696,223232,-137216,28928,56832,-33536,10496,-4096,-1664,2240,-704,80]⟩ : QPoly)))=true := by kernel_decide
def node149 : RationalCode parameterInterval formula150 :=
  (node146.add node148)
  |>.recode ⟨#[0,-524288,3407872,-14221312,44302336,-100433920,174145536,-233095168,222363648,-98394112,-128270336,376209408,-536379392,549216256,-436938752,274608128,-134094848,47026176,-8016896,-3074816,3474432,-1821056,680256,-196160,43264,-6944,832,-64]⟩ ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ node149Denominator node149Cross

/-- Article: exact source arithmetic node 151. -/
def formula151 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-8 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 4) z)
theorem node150Denominator : ∀ z∈parameterInterval, aeval z (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
theorem node150Cross : polynomialCheck
    (((⟨#[-8]⟩ : QPoly).mul (⟨#[0,-16384,73728,-172032,409600,-757760,976896,-829440,-61440,1554432,-2796544,3165184,-2605056,1582592,-699136,194304,-3840,-25920,15264,-5920,1600,-336,72,-8]⟩ : QPoly) : QPoly).mul ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩)
    ((⟨#[0,131072,-589824,1376256,-3276800,6062080,-7815168,6635520,491520,-12435456,22372352,-25321472,20840448,-12660736,5593088,-1554432,30720,207360,-122112,47360,-12800,2688,-576,64]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node150 : RationalCode parameterInterval formula151 :=
  ((RationalCode.constant parameterInterval (-8)).mul moment4Code)
  |>.recode ⟨#[0,131072,-589824,1376256,-3276800,6062080,-7815168,6635520,491520,-12435456,22372352,-25321472,20840448,-12660736,5593088,-1554432,30720,207360,-122112,47360,-12800,2688,-576,64]⟩ ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ node150Denominator node150Cross

/-- Article: exact source arithmetic node 152. -/
def formula152 (z : ℝ) : ℝ := (formula151 z)*(u z)
theorem node151Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
theorem node151Cross : polynomialCheck
    (((⟨#[0,131072,-589824,1376256,-3276800,6062080,-7815168,6635520,491520,-12435456,22372352,-25321472,20840448,-12660736,5593088,-1554432,30720,207360,-122112,47360,-12800,2688,-576,64]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩)
    ((⟨#[0,524288,-3407872,11272192,-29360128,63963136,-112066560,152043520,-141164544,36732928,158547968,-375078912,515145728,-521863168,414040064,-260931584,128786432,-46884864,9909248,1147904,-2205696,1187840,-437760,124928,-28672,5504,-832,64]⟩ : QPoly).mul ((⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node151 : RationalCode parameterInterval formula152 :=
  (node150.mul uCode)
  |>.recode ⟨#[0,524288,-3407872,11272192,-29360128,63963136,-112066560,152043520,-141164544,36732928,158547968,-375078912,515145728,-521863168,414040064,-260931584,128786432,-46884864,9909248,1147904,-2205696,1187840,-437760,124928,-28672,5504,-832,64]⟩ ⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ node151Denominator node151Cross

/-- Article: exact source arithmetic node 153. -/
def formula153 (z : ℝ) : ℝ := (formula150 z)+(formula152 z)
theorem node152Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node5Denominator
theorem node152Cross : polynomialCheck
    ((((⟨#[0,-524288,3407872,-14221312,44302336,-100433920,174145536,-233095168,222363648,-98394112,-128270336,376209408,-536379392,549216256,-436938752,274608128,-134094848,47026176,-8016896,-3074816,3474432,-1821056,680256,-196160,43264,-6944,832,-64]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,524288,-3407872,11272192,-29360128,63963136,-112066560,152043520,-141164544,36732928,158547968,-375078912,515145728,-521863168,414040064,-260931584,128786432,-46884864,9909248,1147904,-2205696,1187840,-437760,124928,-28672,5504,-832,64]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩)
    ((⟨#[0,0,0,-184320,933888,-2279424,3879936,-5157888,5541888,-4993536,3832320,-2496768,1385472,-644736,242496,-71232,14592,-1440]⟩ : QPoly).mul ((⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-81920,360448,-655360,573440,-331776,-32768,655360,-737280,486400,-264192,-204800,367616,-252160,172032,0,-86016,63040,-45952,12800,8256,-7600,5760,-2560,64,324,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node152 : RationalCode parameterInterval formula153 :=
  (node149.add node151)
  |>.recode ⟨#[0,0,0,-184320,933888,-2279424,3879936,-5157888,5541888,-4993536,3832320,-2496768,1385472,-644736,242496,-71232,14592,-1440]⟩ ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ node152Denominator node152Cross

/-- Article: exact source arithmetic node 154. -/
def formula154 (z : ℝ) : ℝ := (formula153 z)+(formula131 z)
theorem node153Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node153Cross : polynomialCheck
    ((((⟨#[0,0,0,-184320,933888,-2279424,3879936,-5157888,5541888,-4993536,3832320,-2496768,1385472,-644736,242496,-71232,14592,-1440]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,0,184320,-933888,2279424,-3879936,5157888,-5541888,4993536,-3832320,2496768,-1385472,644736,-242496,71232,-14592,1440]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node153 : RationalCode parameterInterval formula154 :=
  (node152.add node130)
  |>.recode QPoly.zero ⟨#[1]⟩ node153Denominator node153Cross

/-- Article: exact coefficient representation of the independently specified upper3Expression source. -/
def upper3ExpressionCode : RationalCode parameterInterval (fun z : ℝ => ((4*(moment z 5))+((moment z 0)*((-3*(G z))+(-2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2)))+((moment z 1)*(3+(-3*((u z))^2)))+((moment z 2)*((-4*((G z))^3)+(3*(G z))+(10*(u z))))+((moment z 3)*(-7+(4*((u z))^2)))+(-1*(d z)*(-1+(4*((G z))^2)))+(-8*(moment z 4)*(u z)))) where
  numerator := node153.numerator
  denominator := node153.denominator
  denominator_ne := node153.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((4*(moment z 5))+((moment z 0)*((-3*(G z))+(-2*(u z))+(4*((G z))^3)+(-4*((G z))^3*((u z))^2)+(3*(G z)*((u z))^2)))+((moment z 1)*(3+(-3*((u z))^2)))+((moment z 2)*((-4*((G z))^3)+(3*(G z))+(10*(u z))))+((moment z 3)*(-7+(4*((u z))^2)))+(-1*(d z)*(-1+(4*((G z))^2)))+(-8*(moment z 4)*(u z)))) z=formula154 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node153.exact z hz)

/-- Article: compact exact representation of the actual raw upper3 source. -/
def upper3ActualCode : RationalCode parameterInterval (fun z => reducedSlack z 3 (1 : ℝ)) where
  numerator := upper3ExpressionCode.numerator
  denominator := upper3ExpressionCode.denominator
  denominator_ne := upper3ExpressionCode.denominator_ne
  exact z hz := (upper3_source z).trans (upper3ExpressionCode.exact z hz)

/-- Article: the active raw upper3 is exactly zero. -/
theorem upper3_zero {z : ℝ} (hz : z∈parameterInterval) : reducedSlack z 3 (1 : ℝ)=0 :=
  upper3ActualCode.eq_zero (by kernel_decide) hz

/-- Article: exact source arithmetic node 155. -/
def formula155 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 6) z)
theorem node154Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node17Denominator
theorem node154Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[-262144,2752512,-14548992,51904512,-145358848,342360064,-674955264,1086586880,-1363378176,1146847232,-103170048,-1833435136,4314488832,-6647283712,8102219776,-8271470592,7240925184,-5492130816,3620462592,-2067867648,1012777472,-415455232,134827776,-28647424,-806016,4479872,-2662848,1061120,-329568,83584,-17744,3168,-444,42,-2]⟩ : QPoly) : QPoly).mul ⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩)
    ((⟨#[-524288,5505024,-29097984,103809024,-290717696,684720128,-1349910528,2173173760,-2726756352,2293694464,-206340096,-3666870272,8628977664,-13294567424,16204439552,-16542941184,14481850368,-10984261632,7240925184,-4135735296,2025554944,-830910464,269655552,-57294848,-1612032,8959744,-5325696,2122240,-659136,167168,-35488,6336,-888,84,-4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node154 : RationalCode parameterInterval formula155 :=
  ((RationalCode.constant parameterInterval (2)).mul moment6Code)
  |>.recode ⟨#[-524288,5505024,-29097984,103809024,-290717696,684720128,-1349910528,2173173760,-2726756352,2293694464,-206340096,-3666870272,8628977664,-13294567424,16204439552,-16542941184,14481850368,-10984261632,7240925184,-4135735296,2025554944,-830910464,269655552,-57294848,-1612032,8959744,-5325696,2122240,-659136,167168,-35488,6336,-888,84,-4]⟩ ⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ node154Denominator node154Cross

/-- Article: exact source arithmetic node 156. -/
def formula156 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-6 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 3) z)
theorem node155Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node5Denominator
theorem node155Cross : polynomialCheck
    (((⟨#[-6]⟩ : QPoly).mul (⟨#[0,0,4096,-6144,6144,-52224,111616,-113152,78336,-36096,14336,-18048,19584,-14144,6976,-1632,96,-48,16]⟩ : QPoly) : QPoly).mul ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩)
    ((⟨#[0,0,-24576,36864,-36864,313344,-669696,678912,-470016,216576,-86016,108288,-117504,84864,-41856,9792,-576,288,-96]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node155 : RationalCode parameterInterval formula156 :=
  ((RationalCode.constant parameterInterval (-6)).mul moment3Code)
  |>.recode ⟨#[0,0,-24576,36864,-36864,313344,-669696,678912,-470016,216576,-86016,108288,-117504,84864,-41856,9792,-576,288,-96]⟩ ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ node155Denominator node155Cross

/-- Article: exact source arithmetic node 157. -/
def formula157 (z : ℝ) : ℝ := (formula156 z)*(u z)
theorem node156Denominator : ∀ z∈parameterInterval, aeval z (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
theorem node156Cross : polynomialCheck
    (((⟨#[0,0,-24576,36864,-36864,313344,-669696,678912,-470016,216576,-86016,108288,-117504,84864,-41856,9792,-576,288,-96]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩)
    ((⟨#[0,0,-98304,344064,-638976,1941504,-5652480,10764288,-13959168,13049856,-9222144,5412864,-3360768,2706432,-2305536,1631232,-872448,336384,-88320,15168,-2496,672,-96]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
def node156 : RationalCode parameterInterval formula157 :=
  (node155.mul uCode)
  |>.recode ⟨#[0,0,-98304,344064,-638976,1941504,-5652480,10764288,-13959168,13049856,-9222144,5412864,-3360768,2706432,-2305536,1631232,-872448,336384,-88320,15168,-2496,672,-96]⟩ ⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ node156Denominator node156Cross

/-- Article: exact source arithmetic node 158. -/
def formula158 (z : ℝ) : ℝ := (formula155 z)+(formula157 z)
theorem node157Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node17Denominator
theorem node157Cross : polynomialCheck
    ((((⟨#[-524288,5505024,-29097984,103809024,-290717696,684720128,-1349910528,2173173760,-2726756352,2293694464,-206340096,-3666870272,8628977664,-13294567424,16204439552,-16542941184,14481850368,-10984261632,7240925184,-4135735296,2025554944,-830910464,269655552,-57294848,-1612032,8959744,-5325696,2122240,-659136,167168,-35488,6336,-888,84,-4]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,-98304,344064,-638976,1941504,-5652480,10764288,-13959168,13049856,-9222144,5412864,-3360768,2706432,-2305536,1631232,-872448,336384,-88320,15168,-2496,672,-96]⟩ : QPoly).mul (⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩)
    ((⟨#[-524288,5505024,-29097984,102236160,-285212672,674496512,-1318846464,2083520512,-2557280256,2075459584,-13074432,-3769303040,8629813248,-13237305344,16145285120,-16511705088,14475411456,-10985293824,7237705728,-4127926272,2018160640,-827331584,269681664,-58895360,-102144,8107264,-4994688,2034688,-643968,164672,-34816,6240,-888,84,-4]⟩ : QPoly).mul ((⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly).mul (⟨#[20480,-90112,163840,-143360,88064,-14336,-122880,148480,-99584,62464,20480,-54784,38144,-27392,5120,7808,-6224,4640,-1920,-112,344,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node157 : RationalCode parameterInterval formula158 :=
  (node154.add node156)
  |>.recode ⟨#[-524288,5505024,-29097984,102236160,-285212672,674496512,-1318846464,2083520512,-2557280256,2075459584,-13074432,-3769303040,8629813248,-13237305344,16145285120,-16511705088,14475411456,-10985293824,7237705728,-4127926272,2018160640,-827331584,269681664,-58895360,-102144,8107264,-4994688,2034688,-643968,164672,-34816,6240,-888,84,-4]⟩ ⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ node157Denominator node157Cross

/-- Article: exact source arithmetic node 159. -/
def formula159 (z : ℝ) : ℝ := (formula158 z)+(formula97 z)
theorem node158Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node17Denominator
theorem node158Cross : polynomialCheck
    ((((⟨#[-524288,5505024,-29097984,102236160,-285212672,674496512,-1318846464,2083520512,-2557280256,2075459584,-13074432,-3769303040,8629813248,-13237305344,16145285120,-16511705088,14475411456,-10985293824,7237705728,-4127926272,2018160640,-827331584,269681664,-58895360,-102144,8107264,-4994688,2034688,-643968,164672,-34816,6240,-888,84,-4]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,0,7680,-38912,91136,-140288,163456,-153600,119296,-76800,40864,-17536,5696,-1216,120]⟩ : QPoly).mul (⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩)
    ((⟨#[-524288,5505024,-29097984,104202240,-295174144,697827328,-1354760192,2123399168,-2586640384,2082668544,3178496,-3799949312,8660910080,-13257637888,16151166976,-16506566656,14465777664,-10976757760,7232888832,-4126641664,2018895872,-828602368,270653440,-59374208,24832,8135424,-5052032,2073632,-661504,170368,-36032,6360,-888,84,-4]⟩ : QPoly).mul ((⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node158 : RationalCode parameterInterval formula159 :=
  (node157.add node96)
  |>.recode ⟨#[-524288,5505024,-29097984,104202240,-295174144,697827328,-1354760192,2123399168,-2586640384,2082668544,3178496,-3799949312,8660910080,-13257637888,16151166976,-16506566656,14465777664,-10976757760,7232888832,-4126641664,2018895872,-828602368,270653440,-59374208,24832,8135424,-5052032,2073632,-661504,170368,-36032,6360,-888,84,-4]⟩ ⟨#[0,327680,-1441792,2621440,-2293760,1245184,491520,-3276800,3522560,-2277376,1024000,1474560,-2207744,1495040,-952320,-204800,711680,-504320,355840,-51200,-119040,93440,-68992,23040,8000,-8896,6880,-3200,240,304,-280,160,-44,5]⟩ node158Denominator node158Cross

/-- Article: exact source arithmetic node 160. -/
def formula160 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*((fun z : ℝ => moment z 2) z)
theorem node159Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
theorem node159Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[0,0,0,-1024,9984,-21504,22528,-19200,15232,-9600,5632,-2688,624,-32]⟩ : QPoly) : QPoly).mul ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩)
    ((⟨#[0,0,0,-2048,19968,-43008,45056,-38400,30464,-19200,11264,-5376,1248,-64]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node159 : RationalCode parameterInterval formula160 :=
  ((RationalCode.constant parameterInterval (2)).mul moment2Code)
  |>.recode ⟨#[0,0,0,-2048,19968,-43008,45056,-38400,30464,-19200,11264,-5376,1248,-64]⟩ ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ node159Denominator node159Cross


end
end polyak.Boundary.P2
