import polyak.Numerics.KernelDecide
import polyak.Certificates.P2Codes

/-! Article: Lemma p2certs. Literal exact data certify actual P₂ source signs on J. -/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
/-- Article: exact source arithmetic node 1. -/
private def formula1 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-10233/10000) : ℚ) : ℝ)) z)+(G z)
private theorem node0Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-20000,0,10000]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node0Cross : polynomialCheck
    ((((⟨#[(-10233/10000)]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)).add ((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,-20000,0,10000]⟩)
    ((⟨#[5000,20466,0,-10233,1250]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node0 : RationalCode parameterInterval formula1 :=
  ((RationalCode.constant parameterInterval ((-10233/10000))).add GCode)
  |>.recode ⟨#[5000,20466,0,-10233,1250]⟩ ⟨#[0,-20000,0,10000]⟩ node0Denominator node0Cross

/-- Article: exact coefficient representation of the independently specified G_lower source. -/
def G_lowerCode : RationalCode parameterInterval (fun z : ℝ => G z-(10233/10000)) where
  numerator := node0.numerator
  denominator := node0.denominator
  denominator_ne := node0.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => G z-(10233/10000)) z=formula1 z := by
      try dsimp only [formula1,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node0.exact z hz)

/-- Article: exact uniform P₂ source sign G_lower, with no numerical premise. -/
theorem G_lower_positive : ∀ z∈parameterInterval, 0 < (G z-(10233/10000)) :=
  G_lowerCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 2. -/
private def formula2 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(G z)
private theorem node1Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node1Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node1 : RationalCode parameterInterval formula2 :=
  ((RationalCode.constant parameterInterval (-1)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-16,0,8]⟩ node1Denominator node1Cross

/-- Article: exact source arithmetic node 3. -/
private def formula3 (z : ℝ) : ℝ := ((fun _ : ℝ => (((10337/10000) : ℚ) : ℝ)) z)+(formula2 z)
private theorem node2Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-20000,0,10000]⟩ : QPoly).toPoly≠0 :=
  node0Denominator
private theorem node2Cross : polynomialCheck
    ((((⟨#[(10337/10000)]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)).add ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,-20000,0,10000]⟩)
    ((⟨#[-5000,-20674,0,10337,-1250]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node2 : RationalCode parameterInterval formula3 :=
  ((RationalCode.constant parameterInterval ((10337/10000))).add node1)
  |>.recode ⟨#[-5000,-20674,0,10337,-1250]⟩ ⟨#[0,-20000,0,10000]⟩ node2Denominator node2Cross

/-- Article: exact coefficient representation of the independently specified G_upper source. -/
def G_upperCode : RationalCode parameterInterval (fun z : ℝ => (10337/10000)-G z) where
  numerator := node2.numerator
  denominator := node2.denominator
  denominator_ne := node2.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => (10337/10000)-G z) z=formula3 z := by
      try dsimp only [formula1,formula2,formula3,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node2.exact z hz)

/-- Article: exact uniform P₂ source sign G_upper, with no numerical premise. -/
theorem G_upper_positive : ∀ z∈parameterInterval, 0 < ((10337/10000)-G z) :=
  G_upperCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 4. -/
private def formula4 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-511/1000) : ℚ) : ℝ)) z)+(u z)
private theorem node3Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4000,0,0,0,1000]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node3Cross : polynomialCheck
    ((((⟨#[(-511/1000)]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)).add ((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[-4000,0,0,0,1000]⟩)
    ((⟨#[6044,-8000,8000,-4000,489]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node3 : RationalCode parameterInterval formula4 :=
  ((RationalCode.constant parameterInterval ((-511/1000))).add uCode)
  |>.recode ⟨#[6044,-8000,8000,-4000,489]⟩ ⟨#[-4000,0,0,0,1000]⟩ node3Denominator node3Cross

/-- Article: exact coefficient representation of the independently specified u_lower source. -/
def u_lowerCode : RationalCode parameterInterval (fun z : ℝ => u z-(511/1000)) where
  numerator := node3.numerator
  denominator := node3.denominator
  denominator_ne := node3.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => u z-(511/1000)) z=formula4 z := by
      try dsimp only [formula1,formula2,formula3,formula4,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node3.exact z hz)

/-- Article: exact uniform P₂ source sign u_lower, with no numerical premise. -/
theorem u_lower_positive : ∀ z∈parameterInterval, 0 < (u z-(511/1000)) :=
  u_lowerCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 5. -/
private def formula5 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(u z)
private theorem node4Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node4Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-4,0,0,0,1]⟩)
    ((⟨#[-4,8,-8,4,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node4 : RationalCode parameterInterval formula5 :=
  ((RationalCode.constant parameterInterval (-1)).mul uCode)
  |>.recode ⟨#[-4,8,-8,4,-1]⟩ ⟨#[-4,0,0,0,1]⟩ node4Denominator node4Cross

/-- Article: exact source arithmetic node 6. -/
private def formula6 (z : ℝ) : ℝ := ((fun _ : ℝ => (((517/1000) : ℚ) : ℝ)) z)+(formula5 z)
private theorem node5Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4000,0,0,0,1000]⟩ : QPoly).toPoly≠0 :=
  node3Denominator
private theorem node5Cross : polynomialCheck
    ((((⟨#[(517/1000)]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)).add ((⟨#[-4,8,-8,4,-1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[-4000,0,0,0,1000]⟩)
    ((⟨#[-6068,8000,-8000,4000,-483]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node5 : RationalCode parameterInterval formula6 :=
  ((RationalCode.constant parameterInterval ((517/1000))).add node4)
  |>.recode ⟨#[-6068,8000,-8000,4000,-483]⟩ ⟨#[-4000,0,0,0,1000]⟩ node5Denominator node5Cross

/-- Article: exact coefficient representation of the independently specified u_upper source. -/
def u_upperCode : RationalCode parameterInterval (fun z : ℝ => (517/1000)-u z) where
  numerator := node5.numerator
  denominator := node5.denominator
  denominator_ne := node5.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => (517/1000)-u z) z=formula6 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node5.exact z hz)

/-- Article: exact uniform P₂ source sign u_upper, with no numerical premise. -/
theorem u_upper_positive : ∀ z∈parameterInterval, 0 < ((517/1000)-u z) :=
  u_upperCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 7. -/
private def formula7 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-181/500) : ℚ) : ℝ)) z)+(W z)
private theorem node6Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16000,-32000,24000,-16000,16000,-8000,6000,-4000,1000]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node6Cross : polynomialCheck
    ((((⟨#[(-181/500)]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)).add ((⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[16000,-32000,24000,-16000,16000,-8000,6000,-4000,1000]⟩)
    ((⟨#[8208,-20416,23312,-10208,1208,-5104,5828,-2552,513]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node6 : RationalCode parameterInterval formula7 :=
  ((RationalCode.constant parameterInterval ((-181/500))).add WCode)
  |>.recode ⟨#[8208,-20416,23312,-10208,1208,-5104,5828,-2552,513]⟩ ⟨#[16000,-32000,24000,-16000,16000,-8000,6000,-4000,1000]⟩ node6Denominator node6Cross

/-- Article: exact coefficient representation of the independently specified W_lower source. -/
def W_lowerCode : RationalCode parameterInterval (fun z : ℝ => W z-(181/500)) where
  numerator := node6.numerator
  denominator := node6.denominator
  denominator_ne := node6.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => W z-(181/500)) z=formula7 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node6.exact z hz)

/-- Article: exact uniform P₂ source sign W_lower, with no numerical premise. -/
theorem W_lower_positive : ∀ z∈parameterInterval, 0 < (W z-(181/500)) :=
  W_lowerCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 8. -/
private def formula8 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(W z)
private theorem node7Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node7Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩)
    ((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node7 : RationalCode parameterInterval formula8 :=
  ((RationalCode.constant parameterInterval (-1)).mul WCode)
  |>.recode ⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ node7Denominator node7Cross

/-- Article: exact source arithmetic node 9. -/
private def formula9 (z : ℝ) : ℝ := ((fun _ : ℝ => (((183/500) : ℚ) : ℝ)) z)+(formula8 z)
private theorem node8Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16000,-32000,24000,-16000,16000,-8000,6000,-4000,1000]⟩ : QPoly).toPoly≠0 :=
  node6Denominator
private theorem node8Cross : polynomialCheck
    ((((⟨#[(183/500)]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)).add ((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[16000,-32000,24000,-16000,16000,-8000,6000,-4000,1000]⟩)
    ((⟨#[-8144,20288,-23216,10144,-1144,5072,-5804,2536,-509]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node8 : RationalCode parameterInterval formula9 :=
  ((RationalCode.constant parameterInterval ((183/500))).add node7)
  |>.recode ⟨#[-8144,20288,-23216,10144,-1144,5072,-5804,2536,-509]⟩ ⟨#[16000,-32000,24000,-16000,16000,-8000,6000,-4000,1000]⟩ node8Denominator node8Cross

/-- Article: exact coefficient representation of the independently specified W_upper source. -/
def W_upperCode : RationalCode parameterInterval (fun z : ℝ => (183/500)-W z) where
  numerator := node8.numerator
  denominator := node8.denominator
  denominator_ne := node8.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => (183/500)-W z) z=formula9 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node8.exact z hz)

/-- Article: exact uniform P₂ source sign W_upper, with no numerical premise. -/
theorem W_upper_positive : ∀ z∈parameterInterval, 0 < ((183/500)-W z) :=
  W_upperCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 10. -/
private def formula10 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(atomB z)
private theorem node9Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node9Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[0,-24,40,-32,20,-6]⟩ : QPoly) : QPoly).mul ⟨#[8,0,-4,0,-2,0,1]⟩)
    ((⟨#[0,24,-40,32,-20,6]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node9 : RationalCode parameterInterval formula10 :=
  ((RationalCode.constant parameterInterval (-1)).mul atomBCode)
  |>.recode ⟨#[0,24,-40,32,-20,6]⟩ ⟨#[8,0,-4,0,-2,0,1]⟩ node9Denominator node9Cross

/-- Article: exact coefficient representation of the independently specified b_negative source. -/
def b_negativeCode : RationalCode parameterInterval (fun z : ℝ => -atomB z) where
  numerator := node9.numerator
  denominator := node9.denominator
  denominator_ne := node9.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => -atomB z) z=formula10 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node9.exact z hz)

/-- Article: exact uniform P₂ source sign b_negative, with no numerical premise. -/
theorem b_negative_positive : ∀ z∈parameterInterval, 0 < (-atomB z) :=
  b_negativeCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 11. -/
private def formula11 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/2) : ℚ) : ℝ)) z)*(atomA z)
private theorem node10Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,0,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node10Cross : polynomialCheck
    (((⟨#[(1/2)]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,0,0,4]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node10 : RationalCode parameterInterval formula11 :=
  ((RationalCode.constant parameterInterval ((1/2))).mul atomACode)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[0,-16,0,0,0,4]⟩ node10Denominator node10Cross

/-- Article: exact source arithmetic node 12. -/
private def formula12 (z : ℝ) : ℝ := (meanCosine z)+(formula11 z)
private theorem node11Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2560,11264,-21760,23552,-23168,19200,-6464,0,3232,-4800,2896,-1472,680,-176,20]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node11Cross : polynomialCheck
    ((((⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ : QPoly).mul (⟨#[0,-16,0,0,0,4]⟩ : QPoly)).add ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[0,-2560,11264,-21760,23552,-23168,19200,-6464,0,3232,-4800,2896,-1472,680,-176,20]⟩)
    ((⟨#[1280,-9472,33536,-67200,98048,-124352,128576,-114656,89824,-57328,32144,-15544,6128,-2100,524,-74,5]⟩ : QPoly).mul ((⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).mul (⟨#[0,-16,0,0,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node11 : RationalCode parameterInterval formula12 :=
  (meanCosineCode.add node10)
  |>.recode ⟨#[1280,-9472,33536,-67200,98048,-124352,128576,-114656,89824,-57328,32144,-15544,6128,-2100,524,-74,5]⟩ ⟨#[0,-2560,11264,-21760,23552,-23168,19200,-6464,0,3232,-4800,2896,-1472,680,-176,20]⟩ node11Denominator node11Cross

/-- Article: exact source arithmetic node 13. -/
private def formula13 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(formula12 z)
private theorem node12Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2560,11264,-21760,23552,-23168,19200,-6464,0,3232,-4800,2896,-1472,680,-176,20]⟩ : QPoly).toPoly≠0 :=
  node11Denominator
private theorem node12Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[1280,-9472,33536,-67200,98048,-124352,128576,-114656,89824,-57328,32144,-15544,6128,-2100,524,-74,5]⟩ : QPoly) : QPoly).mul ⟨#[0,-2560,11264,-21760,23552,-23168,19200,-6464,0,3232,-4800,2896,-1472,680,-176,20]⟩)
    ((⟨#[-1280,9472,-33536,67200,-98048,124352,-128576,114656,-89824,57328,-32144,15544,-6128,2100,-524,74,-5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-2560,11264,-21760,23552,-23168,19200,-6464,0,3232,-4800,2896,-1472,680,-176,20]⟩ : QPoly)))=true := by kernel_decide
private def node12 : RationalCode parameterInterval formula13 :=
  ((RationalCode.constant parameterInterval (-1)).mul node11)
  |>.recode ⟨#[-1280,9472,-33536,67200,-98048,124352,-128576,114656,-89824,57328,-32144,15544,-6128,2100,-524,74,-5]⟩ ⟨#[0,-2560,11264,-21760,23552,-23168,19200,-6464,0,3232,-4800,2896,-1472,680,-176,20]⟩ node12Denominator node12Cross

/-- Article: exact coefficient representation of the independently specified midpoint source. -/
def midpointCode : RationalCode parameterInterval (fun z : ℝ => -meanCosine z-atomA z/2) where
  numerator := node12.numerator
  denominator := node12.denominator
  denominator_ne := node12.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => -meanCosine z-atomA z/2) z=formula13 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node12.exact z hz)

/-- Article: exact uniform P₂ source sign midpoint, with no numerical premise. -/
theorem midpoint_positive : ∀ z∈parameterInterval, 0 < (-meanCosine z-atomA z/2) :=
  midpointCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 14. -/
private def formula14 (z : ℝ) : ℝ := (id z)^3
private theorem node13Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node13Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 3 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 3))=true := by kernel_decide
private def node13 : RationalCode parameterInterval formula14 :=
  ((RationalCode.variable parameterInterval).pow 3)
  |>.recode ⟨#[0,0,0,1]⟩ ⟨#[1]⟩ node13Denominator node13Cross

/-- Article: exact source arithmetic node 15. -/
private def formula15 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-32 : ℚ) : ℝ)) z)*(formula14 z)
private theorem node14Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node14Cross : polynomialCheck
    (((⟨#[-32]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node14 : RationalCode parameterInterval formula15 :=
  ((RationalCode.constant parameterInterval (-32)).mul node13)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[1]⟩ node14Denominator node14Cross

/-- Article: exact source arithmetic node 16. -/
private def formula16 (z : ℝ) : ℝ := (id z)^2
private theorem node15Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node15Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 2 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 2))=true := by kernel_decide
private def node15 : RationalCode parameterInterval formula16 :=
  ((RationalCode.variable parameterInterval).pow 2)
  |>.recode ⟨#[0,0,1]⟩ ⟨#[1]⟩ node15Denominator node15Cross

/-- Article: exact source arithmetic node 17. -/
private def formula17 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula16 z)
private theorem node16Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node16Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node16 : RationalCode parameterInterval formula17 :=
  ((RationalCode.constant parameterInterval (-2)).add node15)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node16Denominator node16Cross

/-- Article: exact source arithmetic node 18. -/
private def formula18 (z : ℝ) : ℝ := (formula17 z)⁻¹
private theorem node17Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node17Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,0,1]⟩))=true := by kernel_decide
private def node17 : RationalCode parameterInterval formula18 :=
  (node16.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,0,1]⟩ node17Denominator node17Cross

/-- Article: exact source arithmetic node 19. -/
private def formula19 (z : ℝ) : ℝ := (formula18 z)^2
private theorem node18Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node18Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[4,0,-4,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[-2,0,1]⟩ 2))=true := by kernel_decide
private def node18 : RationalCode parameterInterval formula19 :=
  (node17.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[4,0,-4,0,1]⟩ node18Denominator node18Cross

/-- Article: exact source arithmetic node 20. -/
private def formula20 (z : ℝ) : ℝ := (formula15 z)*(formula19 z)
private theorem node19Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  node18Denominator
private theorem node19Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[4,0,-4,0,1]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[4,0,-4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node19 : RationalCode parameterInterval formula20 :=
  (node14.mul node18)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[4,0,-4,0,1]⟩ node19Denominator node19Cross

/-- Article: exact source arithmetic node 21. -/
private def formula21 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)+(formula16 z)
private theorem node20Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node20Cross : polynomialCheck
    ((((⟨#[2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node20 : RationalCode parameterInterval formula21 :=
  ((RationalCode.constant parameterInterval (2)).add node15)
  |>.recode ⟨#[2,0,1]⟩ ⟨#[1]⟩ node20Denominator node20Cross

/-- Article: exact source arithmetic node 22. -/
private def formula22 (z : ℝ) : ℝ := (formula21 z)⁻¹
private theorem node21Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node21Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[2,0,1]⟩))=true := by kernel_decide
private def node21 : RationalCode parameterInterval formula22 :=
  (node20.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[2,0,1]⟩ node21Denominator node21Cross

/-- Article: exact source arithmetic node 23. -/
private def formula23 (z : ℝ) : ℝ := (formula20 z)*(formula22 z)
private theorem node22Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
private theorem node22Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[8,0,-4,0,-2,0,1]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[4,0,-4,0,1]⟩ : QPoly).mul (⟨#[2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node22 : RationalCode parameterInterval formula23 :=
  (node19.mul node21)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[8,0,-4,0,-2,0,1]⟩ node22Denominator node22Cross

/-- Article: exact source arithmetic node 24. -/
private def formula24 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1472 : ℚ) : ℝ)) z)*(formula14 z)
private theorem node23Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node23Cross : polynomialCheck
    (((⟨#[-1472]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-1472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node23 : RationalCode parameterInterval formula24 :=
  ((RationalCode.constant parameterInterval (-1472)).mul node13)
  |>.recode ⟨#[0,0,0,-1472]⟩ ⟨#[1]⟩ node23Denominator node23Cross

/-- Article: exact source arithmetic node 25. -/
private def formula25 (z : ℝ) : ℝ := ((fun _ : ℝ => ((160 : ℚ) : ℝ)) z)+(formula24 z)
private theorem node24Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node24Cross : polynomialCheck
    ((((⟨#[160]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-1472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-1472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node24 : RationalCode parameterInterval formula25 :=
  ((RationalCode.constant parameterInterval (160)).add node23)
  |>.recode ⟨#[160,0,0,-1472]⟩ ⟨#[1]⟩ node24Denominator node24Cross

/-- Article: exact source arithmetic node 26. -/
private def formula26 (z : ℝ) : ℝ := (id z)^5
private theorem node25Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node25Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 5 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 5))=true := by kernel_decide
private def node25 : RationalCode parameterInterval formula26 :=
  ((RationalCode.variable parameterInterval).pow 5)
  |>.recode ⟨#[0,0,0,0,0,1]⟩ ⟨#[1]⟩ node25Denominator node25Cross

/-- Article: exact source arithmetic node 27. -/
private def formula27 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1376 : ℚ) : ℝ)) z)*(formula26 z)
private theorem node26Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node26Cross : polynomialCheck
    (((⟨#[-1376]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node26 : RationalCode parameterInterval formula27 :=
  ((RationalCode.constant parameterInterval (-1376)).mul node25)
  |>.recode ⟨#[0,0,0,0,0,-1376]⟩ ⟨#[1]⟩ node26Denominator node26Cross

/-- Article: exact source arithmetic node 28. -/
private def formula28 (z : ℝ) : ℝ := (formula25 z)+(formula27 z)
private theorem node27Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node27Cross : polynomialCheck
    ((((⟨#[160,0,0,-1472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-1472,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node27 : RationalCode parameterInterval formula28 :=
  (node24.add node26)
  |>.recode ⟨#[160,0,0,-1472,0,-1376]⟩ ⟨#[1]⟩ node27Denominator node27Cross

/-- Article: exact source arithmetic node 29. -/
private def formula29 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-704 : ℚ) : ℝ)) z)*(id z)
private theorem node28Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node28Cross : polynomialCheck
    (((⟨#[-704]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-704]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node28 : RationalCode parameterInterval formula29 :=
  ((RationalCode.constant parameterInterval (-704)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-704]⟩ ⟨#[1]⟩ node28Denominator node28Cross

/-- Article: exact source arithmetic node 30. -/
private def formula30 (z : ℝ) : ℝ := (formula28 z)+(formula29 z)
private theorem node29Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node29Cross : polynomialCheck
    ((((⟨#[160,0,0,-1472,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-704]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node29 : RationalCode parameterInterval formula30 :=
  (node27.add node28)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376]⟩ ⟨#[1]⟩ node29Denominator node29Cross

/-- Article: exact source arithmetic node 31. -/
private def formula31 (z : ℝ) : ℝ := (id z)^7
private theorem node30Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node30Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 7 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 7))=true := by kernel_decide
private def node30 : RationalCode parameterInterval formula31 :=
  ((RationalCode.variable parameterInterval).pow 7)
  |>.recode ⟨#[0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node30Denominator node30Cross

/-- Article: exact source arithmetic node 32. -/
private def formula32 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-368 : ℚ) : ℝ)) z)*(formula31 z)
private theorem node31Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node31Cross : polynomialCheck
    (((⟨#[-368]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-368]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node31 : RationalCode parameterInterval formula32 :=
  ((RationalCode.constant parameterInterval (-368)).mul node30)
  |>.recode ⟨#[0,0,0,0,0,0,0,-368]⟩ ⟨#[1]⟩ node31Denominator node31Cross

/-- Article: exact source arithmetic node 33. -/
private def formula33 (z : ℝ) : ℝ := (formula30 z)+(formula32 z)
private theorem node32Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node32Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-368]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node32 : RationalCode parameterInterval formula33 :=
  (node29.add node31)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ ⟨#[1]⟩ node32Denominator node32Cross

/-- Article: exact source arithmetic node 34. -/
private def formula34 (z : ℝ) : ℝ := (id z)^9
private theorem node33Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node33Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 9 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 9))=true := by kernel_decide
private def node33 : RationalCode parameterInterval formula34 :=
  ((RationalCode.variable parameterInterval).pow 9)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node33Denominator node33Cross

/-- Article: exact source arithmetic node 35. -/
private def formula35 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-44 : ℚ) : ℝ)) z)*(formula34 z)
private theorem node34Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node34Cross : polynomialCheck
    (((⟨#[-44]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node34 : RationalCode parameterInterval formula35 :=
  ((RationalCode.constant parameterInterval (-44)).mul node33)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ ⟨#[1]⟩ node34Denominator node34Cross

/-- Article: exact source arithmetic node 36. -/
private def formula36 (z : ℝ) : ℝ := (formula33 z)+(formula35 z)
private theorem node35Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node35Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node35 : RationalCode parameterInterval formula36 :=
  (node32.add node34)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ ⟨#[1]⟩ node35Denominator node35Cross

/-- Article: exact source arithmetic node 37. -/
private def formula37 (z : ℝ) : ℝ := (id z)^10
private theorem node36Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node36Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 10 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 10))=true := by kernel_decide
private def node36 : RationalCode parameterInterval formula37 :=
  ((RationalCode.variable parameterInterval).pow 10)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node36Denominator node36Cross

/-- Article: exact source arithmetic node 38. -/
private def formula38 (z : ℝ) : ℝ := ((fun _ : ℝ => ((5 : ℚ) : ℝ)) z)*(formula37 z)
private theorem node37Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node37Cross : polynomialCheck
    (((⟨#[5]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node37 : RationalCode parameterInterval formula38 :=
  ((RationalCode.constant parameterInterval (5)).mul node36)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ ⟨#[1]⟩ node37Denominator node37Cross

/-- Article: exact source arithmetic node 39. -/
private def formula39 (z : ℝ) : ℝ := (formula36 z)+(formula38 z)
private theorem node38Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node38Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node38 : RationalCode parameterInterval formula39 :=
  (node35.add node37)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ ⟨#[1]⟩ node38Denominator node38Cross

/-- Article: exact source arithmetic node 40. -/
private def formula40 (z : ℝ) : ℝ := (id z)^8
private theorem node39Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node39Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 8 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 8))=true := by kernel_decide
private def node39 : RationalCode parameterInterval formula40 :=
  ((RationalCode.variable parameterInterval).pow 8)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node39Denominator node39Cross

/-- Article: exact source arithmetic node 41. -/
private def formula41 (z : ℝ) : ℝ := ((fun _ : ℝ => ((170 : ℚ) : ℝ)) z)*(formula40 z)
private theorem node40Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node40Cross : polynomialCheck
    (((⟨#[170]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node40 : RationalCode parameterInterval formula41 :=
  ((RationalCode.constant parameterInterval (170)).mul node39)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,170]⟩ ⟨#[1]⟩ node40Denominator node40Cross

/-- Article: exact source arithmetic node 42. -/
private def formula42 (z : ℝ) : ℝ := (formula39 z)+(formula41 z)
private theorem node41Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node41Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node41 : RationalCode parameterInterval formula42 :=
  (node38.add node40)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ ⟨#[1]⟩ node41Denominator node41Cross

/-- Article: exact source arithmetic node 43. -/
private def formula43 (z : ℝ) : ℝ := (id z)^6
private theorem node42Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node42Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 6 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 6))=true := by kernel_decide
private def node42 : RationalCode parameterInterval formula43 :=
  ((RationalCode.variable parameterInterval).pow 6)
  |>.recode ⟨#[0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node42Denominator node42Cross

/-- Article: exact source arithmetic node 44. -/
private def formula44 (z : ℝ) : ℝ := ((fun _ : ℝ => ((744 : ℚ) : ℝ)) z)*(formula43 z)
private theorem node43Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node43Cross : polynomialCheck
    (((⟨#[744]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node43 : RationalCode parameterInterval formula44 :=
  ((RationalCode.constant parameterInterval (744)).mul node42)
  |>.recode ⟨#[0,0,0,0,0,0,744]⟩ ⟨#[1]⟩ node43Denominator node43Cross

/-- Article: exact source arithmetic node 45. -/
private def formula45 (z : ℝ) : ℝ := (formula42 z)+(formula44 z)
private theorem node44Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node44Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node44 : RationalCode parameterInterval formula45 :=
  (node41.add node43)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node44Denominator node44Cross

/-- Article: exact source arithmetic node 46. -/
private def formula46 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1360 : ℚ) : ℝ)) z)*(formula16 z)
private theorem node45Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node45Cross : polynomialCheck
    (((⟨#[1360]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1360]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node45 : RationalCode parameterInterval formula46 :=
  ((RationalCode.constant parameterInterval (1360)).mul node15)
  |>.recode ⟨#[0,0,1360]⟩ ⟨#[1]⟩ node45Denominator node45Cross

/-- Article: exact source arithmetic node 47. -/
private def formula47 (z : ℝ) : ℝ := (formula45 z)+(formula46 z)
private theorem node46Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node46Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1360]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node46 : RationalCode parameterInterval formula47 :=
  (node44.add node45)
  |>.recode ⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node46Denominator node46Cross

/-- Article: exact source arithmetic node 48. -/
private def formula48 (z : ℝ) : ℝ := (id z)^4
private theorem node47Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node47Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 4 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 4))=true := by kernel_decide
private def node47 : RationalCode parameterInterval formula48 :=
  ((RationalCode.variable parameterInterval).pow 4)
  |>.recode ⟨#[0,0,0,0,1]⟩ ⟨#[1]⟩ node47Denominator node47Cross

/-- Article: exact source arithmetic node 49. -/
private def formula49 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1488 : ℚ) : ℝ)) z)*(formula48 z)
private theorem node48Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node48Cross : polynomialCheck
    (((⟨#[1488]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node48 : RationalCode parameterInterval formula49 :=
  ((RationalCode.constant parameterInterval (1488)).mul node47)
  |>.recode ⟨#[0,0,0,0,1488]⟩ ⟨#[1]⟩ node48Denominator node48Cross

/-- Article: exact source arithmetic node 50. -/
private def formula50 (z : ℝ) : ℝ := (formula47 z)+(formula49 z)
private theorem node49Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node49Cross : polynomialCheck
    ((((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node49 : RationalCode parameterInterval formula50 :=
  (node46.add node48)
  |>.recode ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node49Denominator node49Cross

/-- Article: exact source arithmetic node 51. -/
private def formula51 (z : ℝ) : ℝ := (formula50 z)⁻¹
private theorem node50Denominator : ∀ z∈parameterInterval, aeval z (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node50Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩))=true := by kernel_decide
private def node50 : RationalCode parameterInterval formula51 :=
  (node49.inv (signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ node50Denominator node50Cross

/-- Article: exact source arithmetic node 52. -/
private def formula52 (z : ℝ) : ℝ := (formula51 z)^2
private theorem node51Denominator : ∀ z∈parameterInterval, aeval z (⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node51Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ 2))=true := by kernel_decide
private def node51 : RationalCode parameterInterval formula52 :=
  (node50.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩ node51Denominator node51Cross

/-- Article: exact source arithmetic node 53. -/
private def formula53 (z : ℝ) : ℝ := (formula23 z)*(formula52 z)
private theorem node52Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node52Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).mul (⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩ : QPoly)))=true := by kernel_decide
private def node52 : RationalCode parameterInterval formula53 :=
  (node22.mul node51)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node52Denominator node52Cross

/-- Article: exact source arithmetic node 54. -/
private def formula54 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)+(formula14 z)
private theorem node53Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node53Cross : polynomialCheck
    ((((⟨#[-4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-4,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node53 : RationalCode parameterInterval formula54 :=
  ((RationalCode.constant parameterInterval (-4)).add node13)
  |>.recode ⟨#[-4,0,0,1]⟩ ⟨#[1]⟩ node53Denominator node53Cross

/-- Article: exact source arithmetic node 55. -/
private def formula55 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(id z)
private theorem node54Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node54Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node54 : RationalCode parameterInterval formula55 :=
  ((RationalCode.constant parameterInterval (2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,2]⟩ ⟨#[1]⟩ node54Denominator node54Cross

/-- Article: exact source arithmetic node 56. -/
private def formula56 (z : ℝ) : ℝ := (formula54 z)+(formula55 z)
private theorem node55Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node55Cross : polynomialCheck
    ((((⟨#[-4,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-4,2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node55 : RationalCode parameterInterval formula56 :=
  (node53.add node54)
  |>.recode ⟨#[-4,2,0,1]⟩ ⟨#[1]⟩ node55Denominator node55Cross

/-- Article: exact source arithmetic node 57. -/
private def formula57 (z : ℝ) : ℝ := (formula53 z)*(formula56 z)
private theorem node56Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node52Denominator
private theorem node56Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[-4,2,0,1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,128,-64,0,-32]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node56 : RationalCode parameterInterval formula57 :=
  (node52.mul node55)
  |>.recode ⟨#[0,0,0,128,-64,0,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node56Denominator node56Cross

/-- Article: exact source arithmetic node 58. -/
private def formula58 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula16 z)
private theorem node57Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node57Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node57 : RationalCode parameterInterval formula58 :=
  ((RationalCode.constant parameterInterval (-2)).add node15)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node57Denominator node57Cross

/-- Article: exact source arithmetic node 59. -/
private def formula59 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(id z)
private theorem node58Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node58Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node58 : RationalCode parameterInterval formula59 :=
  ((RationalCode.constant parameterInterval (-2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-2]⟩ ⟨#[1]⟩ node58Denominator node58Cross

/-- Article: exact source arithmetic node 60. -/
private def formula60 (z : ℝ) : ℝ := (formula58 z)+(formula59 z)
private theorem node59Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node59Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,-2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node59 : RationalCode parameterInterval formula60 :=
  (node57.add node58)
  |>.recode ⟨#[-2,-2,1]⟩ ⟨#[1]⟩ node59Denominator node59Cross

/-- Article: exact source arithmetic node 61. -/
private def formula61 (z : ℝ) : ℝ := (formula57 z)*(formula60 z)
private theorem node60Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node52Denominator
private theorem node60Cross : polynomialCheck
    (((⟨#[0,0,0,128,-64,0,-32]⟩ : QPoly).mul (⟨#[-2,-2,1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,-256,-128,256,0,64,-32]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node60 : RationalCode parameterInterval formula61 :=
  (node56.mul node59)
  |>.recode ⟨#[0,0,0,-256,-128,256,0,64,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node60Denominator node60Cross

/-- Article: exact source arithmetic node 62. -/
private def formula62 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula16 z)
private theorem node61Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node61Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node61 : RationalCode parameterInterval formula62 :=
  ((RationalCode.constant parameterInterval (-2)).add node15)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node61Denominator node61Cross

/-- Article: exact source arithmetic node 63. -/
private def formula63 (z : ℝ) : ℝ := (formula62 z)+(formula55 z)
private theorem node62Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node62Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node62 : RationalCode parameterInterval formula63 :=
  (node61.add node54)
  |>.recode ⟨#[-2,2,1]⟩ ⟨#[1]⟩ node62Denominator node62Cross

/-- Article: exact source arithmetic node 64. -/
private def formula64 (z : ℝ) : ℝ := (formula61 z)*(formula63 z)
private theorem node63Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node52Denominator
private theorem node63Cross : polynomialCheck
    (((⟨#[0,0,0,-256,-128,256,0,64,-32]⟩ : QPoly).mul (⟨#[-2,2,1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,512,-256,-1024,384,128,192,0,-32]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node63 : RationalCode parameterInterval formula64 :=
  (node60.mul node62)
  |>.recode ⟨#[0,0,0,512,-256,-1024,384,128,192,0,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node63Denominator node63Cross

/-- Article: exact source arithmetic node 65. -/
private def formula65 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2240 : ℚ) : ℝ)) z)*(formula26 z)
private theorem node64Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node64Cross : polynomialCheck
    (((⟨#[-2240]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node64 : RationalCode parameterInterval formula65 :=
  ((RationalCode.constant parameterInterval (-2240)).mul node25)
  |>.recode ⟨#[0,0,0,0,0,-2240]⟩ ⟨#[1]⟩ node64Denominator node64Cross

/-- Article: exact source arithmetic node 66. -/
private def formula66 (z : ℝ) : ℝ := ((fun _ : ℝ => ((160 : ℚ) : ℝ)) z)+(formula65 z)
private theorem node65Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node65Cross : polynomialCheck
    ((((⟨#[160]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,0,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node65 : RationalCode parameterInterval formula66 :=
  ((RationalCode.constant parameterInterval (160)).add node64)
  |>.recode ⟨#[160,0,0,0,0,-2240]⟩ ⟨#[1]⟩ node65Denominator node65Cross

/-- Article: exact source arithmetic node 67. -/
private def formula67 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2048 : ℚ) : ℝ)) z)*(formula14 z)
private theorem node66Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node66Cross : polynomialCheck
    (((⟨#[-2048]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-2048]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node66 : RationalCode parameterInterval formula67 :=
  ((RationalCode.constant parameterInterval (-2048)).mul node13)
  |>.recode ⟨#[0,0,0,-2048]⟩ ⟨#[1]⟩ node66Denominator node66Cross

/-- Article: exact source arithmetic node 68. -/
private def formula68 (z : ℝ) : ℝ := (formula66 z)+(formula67 z)
private theorem node67Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node67Cross : polynomialCheck
    ((((⟨#[160,0,0,0,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-2048]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-2048,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node67 : RationalCode parameterInterval formula68 :=
  (node65.add node66)
  |>.recode ⟨#[160,0,0,-2048,0,-2240]⟩ ⟨#[1]⟩ node67Denominator node67Cross

/-- Article: exact source arithmetic node 69. -/
private def formula69 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-512 : ℚ) : ℝ)) z)*(formula31 z)
private theorem node68Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node68Cross : polynomialCheck
    (((⟨#[-512]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node68 : RationalCode parameterInterval formula69 :=
  ((RationalCode.constant parameterInterval (-512)).mul node30)
  |>.recode ⟨#[0,0,0,0,0,0,0,-512]⟩ ⟨#[1]⟩ node68Denominator node68Cross

/-- Article: exact source arithmetic node 70. -/
private def formula70 (z : ℝ) : ℝ := (formula68 z)+(formula69 z)
private theorem node69Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node69Cross : polynomialCheck
    ((((⟨#[160,0,0,-2048,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node69 : RationalCode parameterInterval formula70 :=
  (node67.add node68)
  |>.recode ⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ ⟨#[1]⟩ node69Denominator node69Cross

/-- Article: exact source arithmetic node 71. -/
private def formula71 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-384 : ℚ) : ℝ)) z)*(id z)
private theorem node70Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node70Cross : polynomialCheck
    (((⟨#[-384]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-384]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node70 : RationalCode parameterInterval formula71 :=
  ((RationalCode.constant parameterInterval (-384)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-384]⟩ ⟨#[1]⟩ node70Denominator node70Cross

/-- Article: exact source arithmetic node 72. -/
private def formula72 (z : ℝ) : ℝ := (formula70 z)+(formula71 z)
private theorem node71Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node71Cross : polynomialCheck
    ((((⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-384]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node71 : RationalCode parameterInterval formula72 :=
  (node69.add node70)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ ⟨#[1]⟩ node71Denominator node71Cross

/-- Article: exact source arithmetic node 73. -/
private def formula73 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-24 : ℚ) : ℝ)) z)*(formula34 z)
private theorem node72Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node72Cross : polynomialCheck
    (((⟨#[-24]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node72 : RationalCode parameterInterval formula73 :=
  ((RationalCode.constant parameterInterval (-24)).mul node33)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ ⟨#[1]⟩ node72Denominator node72Cross

/-- Article: exact source arithmetic node 74. -/
private def formula74 (z : ℝ) : ℝ := (formula72 z)+(formula73 z)
private theorem node73Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node73Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node73 : RationalCode parameterInterval formula74 :=
  (node71.add node72)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ ⟨#[1]⟩ node73Denominator node73Cross

/-- Article: exact source arithmetic node 75. -/
private def formula75 (z : ℝ) : ℝ := (formula74 z)+(formula38 z)
private theorem node74Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node74Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node74 : RationalCode parameterInterval formula75 :=
  (node73.add node37)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ ⟨#[1]⟩ node74Denominator node74Cross

/-- Article: exact source arithmetic node 76. -/
private def formula76 (z : ℝ) : ℝ := ((fun _ : ℝ => ((74 : ℚ) : ℝ)) z)*(formula40 z)
private theorem node75Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node75Cross : polynomialCheck
    (((⟨#[74]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,74]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node75 : RationalCode parameterInterval formula76 :=
  ((RationalCode.constant parameterInterval (74)).mul node39)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,74]⟩ ⟨#[1]⟩ node75Denominator node75Cross

/-- Article: exact source arithmetic node 77. -/
private def formula77 (z : ℝ) : ℝ := (formula75 z)+(formula76 z)
private theorem node76Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node76Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,74]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node76 : RationalCode parameterInterval formula77 :=
  (node74.add node75)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ ⟨#[1]⟩ node76Denominator node76Cross

/-- Article: exact source arithmetic node 78. -/
private def formula78 (z : ℝ) : ℝ := ((fun _ : ℝ => ((592 : ℚ) : ℝ)) z)*(formula16 z)
private theorem node77Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node77Cross : polynomialCheck
    (((⟨#[592]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,592]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node77 : RationalCode parameterInterval formula78 :=
  ((RationalCode.constant parameterInterval (592)).mul node15)
  |>.recode ⟨#[0,0,592]⟩ ⟨#[1]⟩ node77Denominator node77Cross

/-- Article: exact source arithmetic node 79. -/
private def formula79 (z : ℝ) : ℝ := (formula77 z)+(formula78 z)
private theorem node78Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node78Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,592]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node78 : RationalCode parameterInterval formula79 :=
  (node76.add node77)
  |>.recode ⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ ⟨#[1]⟩ node78Denominator node78Cross

/-- Article: exact source arithmetic node 80. -/
private def formula80 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1448 : ℚ) : ℝ)) z)*(formula43 z)
private theorem node79Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node79Cross : polynomialCheck
    (((⟨#[1448]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,1448]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node79 : RationalCode parameterInterval formula80 :=
  ((RationalCode.constant parameterInterval (1448)).mul node42)
  |>.recode ⟨#[0,0,0,0,0,0,1448]⟩ ⟨#[1]⟩ node79Denominator node79Cross

/-- Article: exact source arithmetic node 81. -/
private def formula81 (z : ℝ) : ℝ := (formula79 z)+(formula80 z)
private theorem node80Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node80Cross : polynomialCheck
    ((((⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,1448]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node80 : RationalCode parameterInterval formula81 :=
  (node78.add node79)
  |>.recode ⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ ⟨#[1]⟩ node80Denominator node80Cross

/-- Article: exact source arithmetic node 82. -/
private def formula82 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2896 : ℚ) : ℝ)) z)*(formula48 z)
private theorem node81Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node81Cross : polynomialCheck
    (((⟨#[2896]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,2896]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node81 : RationalCode parameterInterval formula82 :=
  ((RationalCode.constant parameterInterval (2896)).mul node47)
  |>.recode ⟨#[0,0,0,0,2896]⟩ ⟨#[1]⟩ node81Denominator node81Cross

/-- Article: exact source arithmetic node 83. -/
private def formula83 (z : ℝ) : ℝ := (formula81 z)+(formula82 z)
private theorem node82Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node82Cross : polynomialCheck
    ((((⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,2896]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node82 : RationalCode parameterInterval formula83 :=
  (node80.add node81)
  |>.recode ⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ ⟨#[1]⟩ node82Denominator node82Cross

/-- Article: exact source arithmetic node 84. -/
private def formula84 (z : ℝ) : ℝ := (formula64 z)*(formula83 z)
private theorem node83Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node52Denominator
private theorem node83Cross : polynomialCheck
    (((⟨#[0,0,0,512,-256,-1024,384,128,192,0,-32]⟩ : QPoly).mul (⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,81920,-237568,237568,-745472,1273856,417792,-2435072,2619392,-2184192,1299456,-442880,171520,-31488,-33280,12416,-1408,768,-160]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node83 : RationalCode parameterInterval formula84 :=
  (node63.mul node82)
  |>.recode ⟨#[0,0,0,81920,-237568,237568,-745472,1273856,417792,-2435072,2619392,-2184192,1299456,-442880,171520,-31488,-33280,12416,-1408,768,-160]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node83Denominator node83Cross

/-- Article: exact coefficient representation of the independently specified mean_root_factor source. -/
def mean_root_factorCode : RationalCode parameterInterval (fun z : ℝ => -meanRootFactor z) where
  numerator := node83.numerator
  denominator := node83.denominator
  denominator_ne := node83.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => -meanRootFactor z) z=formula84 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node83.exact z hz)

/-- Article: exact uniform P₂ source sign mean_root_factor, with no numerical premise. -/
theorem mean_root_factor_positive : ∀ z∈parameterInterval, 0 < (-meanRootFactor z) :=
  mean_root_factorCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact coefficient representation of the independently specified d_positive source. -/
def d_positiveCode : RationalCode parameterInterval (fun z : ℝ => d z) where
  numerator := dCode.numerator
  denominator := dCode.denominator
  denominator_ne := dCode.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => d z) z=d z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (dCode.exact z hz)

/-- Article: exact uniform P₂ source sign d_positive, with no numerical premise. -/
theorem d_positive_positive : ∀ z∈parameterInterval, 0 < (d z) :=
  d_positiveCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 85. -/
private def formula85 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-7/25) : ℚ) : ℝ)) z)+(meanGap z)
private theorem node84Denominator : ∀ z∈parameterInterval, aeval z (⟨#[64000,-281600,544000,-588800,563200,-409600,25600,147200,-225600,240000,-112800,36800,3200,-25600,17600,-9200,4250,-1100,125]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node84Cross : polynomialCheck
    ((((⟨#[(-7/25)]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)).add ((⟨#[0,10240,-65536,204800,-423936,659456,-826368,866304,-773120,590592,-386560,216576,-103296,41216,-13248,3200,-512,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[64000,-281600,544000,-588800,563200,-409600,25600,147200,-225600,240000,-112800,36800,3200,-25600,17600,-9200,4250,-1100,125]⟩)
    ((⟨#[-17920,334848,-1790720,5284864,-10756096,16601088,-20666368,21616384,-19264832,14697600,-9632416,5404096,-2583296,1037568,-336128,82576,-13990,1308,-35]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node84 : RationalCode parameterInterval formula85 :=
  ((RationalCode.constant parameterInterval ((-7/25))).add meanGapCode)
  |>.recode ⟨#[-17920,334848,-1790720,5284864,-10756096,16601088,-20666368,21616384,-19264832,14697600,-9632416,5404096,-2583296,1037568,-336128,82576,-13990,1308,-35]⟩ ⟨#[64000,-281600,544000,-588800,563200,-409600,25600,147200,-225600,240000,-112800,36800,3200,-25600,17600,-9200,4250,-1100,125]⟩ node84Denominator node84Cross

/-- Article: exact coefficient representation of the independently specified gap_lower source. -/
def gap_lowerCode : RationalCode parameterInterval (fun z : ℝ => meanGap z-(7/25)) where
  numerator := node84.numerator
  denominator := node84.denominator
  denominator_ne := node84.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => meanGap z-(7/25)) z=formula85 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node84.exact z hz)

/-- Article: exact uniform P₂ source sign gap_lower, with no numerical premise. -/
theorem gap_lower_positive : ∀ z∈parameterInterval, 0 < (meanGap z-(7/25)) :=
  gap_lowerCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 86. -/
private def formula86 (z : ℝ) : ℝ := (d z)^2
private theorem node85Denominator : ∀ z∈parameterInterval, aeval z (⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node85Cross : polynomialCheck
    ((polynomialPower ⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ 2 : QPoly).mul ⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩)
    ((⟨#[26214400,-335544320,1954545664,-6129975296,7063732224,26513244160,-159883722752,427045158912,-643376545792,191791890432,1958760677376,-6810733379584,14633600942080,-24481364705280,34339542597632,-41871776022528,45334228246528,-44172470583296,39070747049984,-31538346737664,23300244451328,-15769173368832,9767686762496,-5521558822912,2833389265408,-1308493000704,536555353088,-191260661760,57162503680,-13302213632,1912852224,93648384,-157074352,52129536,-9758528,809120,107784,-46768,7456,-640,25]⟩ : QPoly).mul (polynomialPower ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ 2))=true := by kernel_decide
private def node85 : RationalCode parameterInterval formula86 :=
  (dCode.pow 2)
  |>.recode ⟨#[26214400,-335544320,1954545664,-6129975296,7063732224,26513244160,-159883722752,427045158912,-643376545792,191791890432,1958760677376,-6810733379584,14633600942080,-24481364705280,34339542597632,-41871776022528,45334228246528,-44172470583296,39070747049984,-31538346737664,23300244451328,-15769173368832,9767686762496,-5521558822912,2833389265408,-1308493000704,536555353088,-191260661760,57162503680,-13302213632,1912852224,93648384,-157074352,52129536,-9758528,809120,107784,-46768,7456,-640,25]⟩ ⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩ node85Denominator node85Cross

/-- Article: exact source arithmetic node 87. -/
private def formula87 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(formula86 z)
private theorem node86Denominator : ∀ z∈parameterInterval, aeval z (⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩ : QPoly).toPoly≠0 :=
  node85Denominator
private theorem node86Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[26214400,-335544320,1954545664,-6129975296,7063732224,26513244160,-159883722752,427045158912,-643376545792,191791890432,1958760677376,-6810733379584,14633600942080,-24481364705280,34339542597632,-41871776022528,45334228246528,-44172470583296,39070747049984,-31538346737664,23300244451328,-15769173368832,9767686762496,-5521558822912,2833389265408,-1308493000704,536555353088,-191260661760,57162503680,-13302213632,1912852224,93648384,-157074352,52129536,-9758528,809120,107784,-46768,7456,-640,25]⟩ : QPoly) : QPoly).mul ⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩)
    ((⟨#[-26214400,335544320,-1954545664,6129975296,-7063732224,-26513244160,159883722752,-427045158912,643376545792,-191791890432,-1958760677376,6810733379584,-14633600942080,24481364705280,-34339542597632,41871776022528,-45334228246528,44172470583296,-39070747049984,31538346737664,-23300244451328,15769173368832,-9767686762496,5521558822912,-2833389265408,1308493000704,-536555353088,191260661760,-57162503680,13302213632,-1912852224,-93648384,157074352,-52129536,9758528,-809120,-107784,46768,-7456,640,-25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩ : QPoly)))=true := by kernel_decide
private def node86 : RationalCode parameterInterval formula87 :=
  ((RationalCode.constant parameterInterval (-1)).mul node85)
  |>.recode ⟨#[-26214400,335544320,-1954545664,6129975296,-7063732224,-26513244160,159883722752,-427045158912,643376545792,-191791890432,-1958760677376,6810733379584,-14633600942080,24481364705280,-34339542597632,41871776022528,-45334228246528,44172470583296,-39070747049984,31538346737664,-23300244451328,15769173368832,-9767686762496,5521558822912,-2833389265408,1308493000704,-536555353088,191260661760,-57162503680,13302213632,-1912852224,-93648384,157074352,-52129536,9758528,-809120,-107784,46768,-7456,640,-25]⟩ ⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩ node86Denominator node86Cross

/-- Article: exact source arithmetic node 88. -/
private def formula88 (z : ℝ) : ℝ := ((fun _ : ℝ => ((25 : ℚ) : ℝ)) z)*(meanGap z)
private theorem node87Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node87Cross : polynomialCheck
    (((⟨#[25]⟩ : QPoly).mul (⟨#[0,10240,-65536,204800,-423936,659456,-826368,866304,-773120,590592,-386560,216576,-103296,41216,-13248,3200,-512,40]⟩ : QPoly) : QPoly).mul ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩)
    ((⟨#[0,256000,-1638400,5120000,-10598400,16486400,-20659200,21657600,-19328000,14764800,-9664000,5414400,-2582400,1030400,-331200,80000,-12800,1000]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node87 : RationalCode parameterInterval formula88 :=
  ((RationalCode.constant parameterInterval (25)).mul meanGapCode)
  |>.recode ⟨#[0,256000,-1638400,5120000,-10598400,16486400,-20659200,21657600,-19328000,14764800,-9664000,5414400,-2582400,1030400,-331200,80000,-12800,1000]⟩ ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ node87Denominator node87Cross

/-- Article: exact source arithmetic node 89. -/
private def formula89 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-7 : ℚ) : ℝ)) z)+(formula88 z)
private theorem node88Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  node87Denominator
private theorem node88Cross : polynomialCheck
    ((((⟨#[-7]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)).add ((⟨#[0,256000,-1638400,5120000,-10598400,16486400,-20659200,21657600,-19328000,14764800,-9664000,5414400,-2582400,1030400,-331200,80000,-12800,1000]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩)
    ((⟨#[-17920,334848,-1790720,5284864,-10756096,16601088,-20666368,21616384,-19264832,14697600,-9632416,5404096,-2583296,1037568,-336128,82576,-13990,1308,-35]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node88 : RationalCode parameterInterval formula89 :=
  ((RationalCode.constant parameterInterval (-7)).add node87)
  |>.recode ⟨#[-17920,334848,-1790720,5284864,-10756096,16601088,-20666368,21616384,-19264832,14697600,-9632416,5404096,-2583296,1037568,-336128,82576,-13990,1308,-35]⟩ ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ node88Denominator node88Cross

/-- Article: exact source arithmetic node 90. -/
private def formula90 (z : ℝ) : ℝ := (formula89 z)^2
private theorem node89Denominator : ∀ z∈parameterInterval, aeval z (⟨#[6553600,-57671680,238288896,-610795520,1119420416,-1616379904,1909456896,-1767112704,1144979456,-277741568,-594870272,1183776768,-1279541248,1008762880,-538771456,59228160,230807552,-326942720,282212352,-163471360,57701888,7403520,-33673216,31523840,-19992832,9248256,-2323712,-542464,1118144,-862848,466176,-197312,68324,-18640,3636,-440,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node89Cross : polynomialCheck
    ((polynomialPower ⟨#[-17920,334848,-1790720,5284864,-10756096,16601088,-20666368,21616384,-19264832,14697600,-9632416,5404096,-2583296,1037568,-336128,82576,-13990,1308,-35]⟩ 2 : QPoly).mul ⟨#[6553600,-57671680,238288896,-610795520,1119420416,-1616379904,1909456896,-1767112704,1144979456,-277741568,-594870272,1183776768,-1279541248,1008762880,-538771456,59228160,230807552,-326942720,282212352,-163471360,57701888,7403520,-33673216,31523840,-19992832,9248256,-2323712,-542464,1118144,-862848,466176,-197312,68324,-18640,3636,-440,25]⟩)
    ((⟨#[321126400,-12000952320,176302587904,-1388647546880,7131428880384,-26725720784896,78310464815104,-187759724855296,380344800313344,-666409806200832,1027838288003072,-1414091270586368,1752797758210048,-1972209901076480,2025821603168256,-1907683941826560,1651912332597248,-1318045018030080,970166070786048,-659022509015040,412978083149312,-238460492728320,126613850198016,-61631559408640,27387464972032,-11047588051456,4014993312512,-1301581652736,371430469056,-91679553152,19118765824,-3262417088,435267876,-42378160,2690164,-91560,1225]⟩ : QPoly).mul (polynomialPower ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ 2))=true := by kernel_decide
private def node89 : RationalCode parameterInterval formula90 :=
  (node88.pow 2)
  |>.recode ⟨#[321126400,-12000952320,176302587904,-1388647546880,7131428880384,-26725720784896,78310464815104,-187759724855296,380344800313344,-666409806200832,1027838288003072,-1414091270586368,1752797758210048,-1972209901076480,2025821603168256,-1907683941826560,1651912332597248,-1318045018030080,970166070786048,-659022509015040,412978083149312,-238460492728320,126613850198016,-61631559408640,27387464972032,-11047588051456,4014993312512,-1301581652736,371430469056,-91679553152,19118765824,-3262417088,435267876,-42378160,2690164,-91560,1225]⟩ ⟨#[6553600,-57671680,238288896,-610795520,1119420416,-1616379904,1909456896,-1767112704,1144979456,-277741568,-594870272,1183776768,-1279541248,1008762880,-538771456,59228160,230807552,-326942720,282212352,-163471360,57701888,7403520,-33673216,31523840,-19992832,9248256,-2323712,-542464,1118144,-862848,466176,-197312,68324,-18640,3636,-440,25]⟩ node89Denominator node89Cross

/-- Article: exact source arithmetic node 91. -/
private def formula91 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/625) : ℚ) : ℝ)) z)*(formula90 z)
private theorem node90Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4096000000,-36044800000,148930560000,-381747200000,699637760000,-1010237440000,1193410560000,-1104445440000,715612160000,-173588480000,-371793920000,739860480000,-799713280000,630476800000,-336732160000,37017600000,144254720000,-204339200000,176382720000,-102169600000,36063680000,4627200000,-21045760000,19702400000,-12495520000,5780160000,-1452320000,-339040000,698840000,-539280000,291360000,-123320000,42702500,-11650000,2272500,-275000,15625]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node90Cross : polynomialCheck
    (((⟨#[(1/625)]⟩ : QPoly).mul (⟨#[321126400,-12000952320,176302587904,-1388647546880,7131428880384,-26725720784896,78310464815104,-187759724855296,380344800313344,-666409806200832,1027838288003072,-1414091270586368,1752797758210048,-1972209901076480,2025821603168256,-1907683941826560,1651912332597248,-1318045018030080,970166070786048,-659022509015040,412978083149312,-238460492728320,126613850198016,-61631559408640,27387464972032,-11047588051456,4014993312512,-1301581652736,371430469056,-91679553152,19118765824,-3262417088,435267876,-42378160,2690164,-91560,1225]⟩ : QPoly) : QPoly).mul ⟨#[4096000000,-36044800000,148930560000,-381747200000,699637760000,-1010237440000,1193410560000,-1104445440000,715612160000,-173588480000,-371793920000,739860480000,-799713280000,630476800000,-336732160000,37017600000,144254720000,-204339200000,176382720000,-102169600000,36063680000,4627200000,-21045760000,19702400000,-12495520000,5780160000,-1452320000,-339040000,698840000,-539280000,291360000,-123320000,42702500,-11650000,2272500,-275000,15625]⟩)
    ((⟨#[321126400,-12000952320,176302587904,-1388647546880,7131428880384,-26725720784896,78310464815104,-187759724855296,380344800313344,-666409806200832,1027838288003072,-1414091270586368,1752797758210048,-1972209901076480,2025821603168256,-1907683941826560,1651912332597248,-1318045018030080,970166070786048,-659022509015040,412978083149312,-238460492728320,126613850198016,-61631559408640,27387464972032,-11047588051456,4014993312512,-1301581652736,371430469056,-91679553152,19118765824,-3262417088,435267876,-42378160,2690164,-91560,1225]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[6553600,-57671680,238288896,-610795520,1119420416,-1616379904,1909456896,-1767112704,1144979456,-277741568,-594870272,1183776768,-1279541248,1008762880,-538771456,59228160,230807552,-326942720,282212352,-163471360,57701888,7403520,-33673216,31523840,-19992832,9248256,-2323712,-542464,1118144,-862848,466176,-197312,68324,-18640,3636,-440,25]⟩ : QPoly)))=true := by kernel_decide
private def node90 : RationalCode parameterInterval formula91 :=
  ((RationalCode.constant parameterInterval ((1/625))).mul node89)
  |>.recode ⟨#[321126400,-12000952320,176302587904,-1388647546880,7131428880384,-26725720784896,78310464815104,-187759724855296,380344800313344,-666409806200832,1027838288003072,-1414091270586368,1752797758210048,-1972209901076480,2025821603168256,-1907683941826560,1651912332597248,-1318045018030080,970166070786048,-659022509015040,412978083149312,-238460492728320,126613850198016,-61631559408640,27387464972032,-11047588051456,4014993312512,-1301581652736,371430469056,-91679553152,19118765824,-3262417088,435267876,-42378160,2690164,-91560,1225]⟩ ⟨#[4096000000,-36044800000,148930560000,-381747200000,699637760000,-1010237440000,1193410560000,-1104445440000,715612160000,-173588480000,-371793920000,739860480000,-799713280000,630476800000,-336732160000,37017600000,144254720000,-204339200000,176382720000,-102169600000,36063680000,4627200000,-21045760000,19702400000,-12495520000,5780160000,-1452320000,-339040000,698840000,-539280000,291360000,-123320000,42702500,-11650000,2272500,-275000,15625]⟩ node90Denominator node90Cross

/-- Article: exact source arithmetic node 92. -/
private def formula92 (z : ℝ) : ℝ := (G z)^2
private theorem node91Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node91Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 2 : QPoly).mul ⟨#[0,0,256,0,-256,0,64]⟩)
    ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 2))=true := by kernel_decide
private def node91 : RationalCode parameterInterval formula92 :=
  (GCode.pow 2)
  |>.recode ⟨#[16,0,0,0,8,0,0,0,1]⟩ ⟨#[0,0,256,0,-256,0,64]⟩ node91Denominator node91Cross

/-- Article: exact source arithmetic node 93. -/
private def formula93 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)+(formula92 z)
private theorem node92Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).toPoly≠0 :=
  node91Denominator
private theorem node92Cross : polynomialCheck
    ((((⟨#[-1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)).add ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,256,0,-256,0,64]⟩)
    ((⟨#[16,0,-256,0,264,0,-64,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node92 : RationalCode parameterInterval formula93 :=
  ((RationalCode.constant parameterInterval (-1)).add node91)
  |>.recode ⟨#[16,0,-256,0,264,0,-64,0,1]⟩ ⟨#[0,0,256,0,-256,0,64]⟩ node92Denominator node92Cross

/-- Article: exact source arithmetic node 94. -/
private def formula94 (z : ℝ) : ℝ := (formula91 z)*(formula93 z)
private theorem node93Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node93Cross : polynomialCheck
    (((⟨#[321126400,-12000952320,176302587904,-1388647546880,7131428880384,-26725720784896,78310464815104,-187759724855296,380344800313344,-666409806200832,1027838288003072,-1414091270586368,1752797758210048,-1972209901076480,2025821603168256,-1907683941826560,1651912332597248,-1318045018030080,970166070786048,-659022509015040,412978083149312,-238460492728320,126613850198016,-61631559408640,27387464972032,-11047588051456,4014993312512,-1301581652736,371430469056,-91679553152,19118765824,-3262417088,435267876,-42378160,2690164,-91560,1225]⟩ : QPoly).mul (⟨#[16,0,-256,0,264,0,-64,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩)
    ((⟨#[5138022400,-192015237120,2738633048064,-19146116956160,69054176952320,-75286011969536,-526155025219584,3471794031820800,-12090548007731200,30437203818577920,-60705128706736128,100115940178919424,-139675548633989120,166509714685820928,-169217529173508096,143505164043550720,-94842430553948160,36450386446254080,16298784986660864,-51946053772443648,66450206170275840,-62949927959920640,48730707321405440,-31474963979960320,16612551542568960,-6493256721555456,1018674061666304,1139074576445440,-1481912977405440,1121134094090240,-661005973334016,325214286495744,-136401902962880,48884736415488,-14820588063168,3715478981760,-737948486800,105950745600,-8028488544,-574386688,263420780,-36518320,2611764,-91560,1225]⟩ : QPoly).mul ((⟨#[4096000000,-36044800000,148930560000,-381747200000,699637760000,-1010237440000,1193410560000,-1104445440000,715612160000,-173588480000,-371793920000,739860480000,-799713280000,630476800000,-336732160000,37017600000,144254720000,-204339200000,176382720000,-102169600000,36063680000,4627200000,-21045760000,19702400000,-12495520000,5780160000,-1452320000,-339040000,698840000,-539280000,291360000,-123320000,42702500,-11650000,2272500,-275000,15625]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node93 : RationalCode parameterInterval formula94 :=
  (node90.mul node92)
  |>.recode ⟨#[5138022400,-192015237120,2738633048064,-19146116956160,69054176952320,-75286011969536,-526155025219584,3471794031820800,-12090548007731200,30437203818577920,-60705128706736128,100115940178919424,-139675548633989120,166509714685820928,-169217529173508096,143505164043550720,-94842430553948160,36450386446254080,16298784986660864,-51946053772443648,66450206170275840,-62949927959920640,48730707321405440,-31474963979960320,16612551542568960,-6493256721555456,1018674061666304,1139074576445440,-1481912977405440,1121134094090240,-661005973334016,325214286495744,-136401902962880,48884736415488,-14820588063168,3715478981760,-737948486800,105950745600,-8028488544,-574386688,263420780,-36518320,2611764,-91560,1225]⟩ ⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩ node93Denominator node93Cross

/-- Article: exact source arithmetic node 95. -/
private def formula95 (z : ℝ) : ℝ := (formula87 z)+(formula94 z)
private theorem node94Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩ : QPoly).toPoly≠0 :=
  node93Denominator
private theorem node94Cross : polynomialCheck
    ((((⟨#[-26214400,335544320,-1954545664,6129975296,-7063732224,-26513244160,159883722752,-427045158912,643376545792,-191791890432,-1958760677376,6810733379584,-14633600942080,24481364705280,-34339542597632,41871776022528,-45334228246528,44172470583296,-39070747049984,31538346737664,-23300244451328,15769173368832,-9767686762496,5521558822912,-2833389265408,1308493000704,-536555353088,191260661760,-57162503680,13302213632,-1912852224,-93648384,157074352,-52129536,9758528,-809120,-107784,46768,-7456,640,-25]⟩ : QPoly).mul (⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩ : QPoly)).add ((⟨#[5138022400,-192015237120,2738633048064,-19146116956160,69054176952320,-75286011969536,-526155025219584,3471794031820800,-12090548007731200,30437203818577920,-60705128706736128,100115940178919424,-139675548633989120,166509714685820928,-169217529173508096,143505164043550720,-94842430553948160,36450386446254080,16298784986660864,-51946053772443648,66450206170275840,-62949927959920640,48730707321405440,-31474963979960320,16612551542568960,-6493256721555456,1018674061666304,1139074576445440,-1481912977405440,1121134094090240,-661005973334016,325214286495744,-136401902962880,48884736415488,-14820588063168,3715478981760,-737948486800,105950745600,-8028488544,-574386688,263420780,-36518320,2611764,-91560,1225]⟩ : QPoly).mul (⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩)
    ((⟨#[5138022400,-192015237120,1690057048064,-5724344156160,-9127649607680,169912999870464,-808704314179584,2411264265420800,-5695199097651200,13355397462097920,-34970066875056128,92444264561639424,-218025975729029120,438939049869180928,-754561566856708096,1122759752254750720,-1468424134459228160,1711321427347374080,-1797070344874459136,1714952769559396352,-1496379675829084160,1198583941546639360,-883279070731714560,599291970773319680,-374094918957271040,214369096194924544,-112316896554653696,53478794604605440,-22944127100925440,8771560564490240,-2947506120534016,857302831775744,-212915991922880,45138801055488,-8537613983168,1630297541760,-347607366800,73585945600,-12339848544,1296333312,-34819220,-10918320,1611764,-91560,1225]⟩ : QPoly).mul ((⟨#[26214400,-230686720,926941184,-2212495360,3531079680,-4080009216,3398434816,-1213726720,-1938489344,4341104640,-5049942016,4078960640,-1593704448,-977797120,2368208896,-2614362112,1798774784,-535920640,-333152256,713113600,-667234304,356556800,-83288064,-66990080,112423424,-81698816,37003264,-7639040,-6225408,7966720,-4931584,2119680,-473264,-148160,207424,-124512,53880,-16880,3536,-440,25]⟩ : QPoly).mul (⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩ : QPoly)))=true := by kernel_decide
private def node94 : RationalCode parameterInterval formula95 :=
  (node86.add node93)
  |>.recode ⟨#[5138022400,-192015237120,1690057048064,-5724344156160,-9127649607680,169912999870464,-808704314179584,2411264265420800,-5695199097651200,13355397462097920,-34970066875056128,92444264561639424,-218025975729029120,438939049869180928,-754561566856708096,1122759752254750720,-1468424134459228160,1711321427347374080,-1797070344874459136,1714952769559396352,-1496379675829084160,1198583941546639360,-883279070731714560,599291970773319680,-374094918957271040,214369096194924544,-112316896554653696,53478794604605440,-22944127100925440,8771560564490240,-2947506120534016,857302831775744,-212915991922880,45138801055488,-8537613983168,1630297541760,-347607366800,73585945600,-12339848544,1296333312,-34819220,-10918320,1611764,-91560,1225]⟩ ⟨#[0,0,1048576000000,-9227468800000,37077647360000,-88499814400000,141243187200000,-163200368640000,135937392640000,-48549068800000,-77539573760000,173644185600000,-201997680640000,163158425600000,-63748177920000,-39111884800000,94728355840000,-104574484480000,71950991360000,-21436825600000,-13326090240000,28524544000000,-26689372160000,14262272000000,-3331522560000,-2679603200000,4496936960000,-3267952640000,1480130560000,-305561600000,-249016320000,318668800000,-197263360000,84787200000,-18930560000,-5926400000,8296960000,-4980480000,2155200000,-675200000,141440000,-17600000,1000000]⟩ node94Denominator node94Cross

/-- Article: exact coefficient representation of the independently specified gap_square source. -/
def gap_squareCode : RationalCode parameterInterval (fun z : ℝ => (meanGap z-(7/25))^2*(G z^2-1)-d z^2) where
  numerator := node94.numerator
  denominator := node94.denominator
  denominator_ne := node94.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => (meanGap z-(7/25))^2*(G z^2-1)-d z^2) z=formula95 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node94.exact z hz)

/-- Article: exact uniform P₂ source sign gap_square, with no numerical premise. -/
theorem gap_square_positive : ∀ z∈parameterInterval, 0 < ((meanGap z-(7/25))^2*(G z^2-1)-d z^2) :=
  gap_squareCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 96. -/
private def formula96 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(meanGap z)
private theorem node95Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  node87Denominator
private theorem node95Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[0,10240,-65536,204800,-423936,659456,-826368,866304,-773120,590592,-386560,216576,-103296,41216,-13248,3200,-512,40]⟩ : QPoly) : QPoly).mul ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩)
    ((⟨#[0,-10240,65536,-204800,423936,-659456,826368,-866304,773120,-590592,386560,-216576,103296,-41216,13248,-3200,512,-40]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node95 : RationalCode parameterInterval formula96 :=
  ((RationalCode.constant parameterInterval (-1)).mul meanGapCode)
  |>.recode ⟨#[0,-10240,65536,-204800,423936,-659456,826368,-866304,773120,-590592,386560,-216576,103296,-41216,13248,-3200,512,-40]⟩ ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ node95Denominator node95Cross

/-- Article: exact source arithmetic node 97. -/
private def formula97 (z : ℝ) : ℝ := ((fun _ : ℝ => (((21/20) : ℚ) : ℝ)) z)+(formula96 z)
private theorem node96Denominator : ∀ z∈parameterInterval, aeval z (⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node96Cross : polynomialCheck
    ((((⟨#[(21/20)]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)).add ((⟨#[0,-10240,65536,-204800,423936,-659456,826368,-866304,773120,-590592,386560,-216576,103296,-41216,13248,-3200,512,-40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩)
    ((⟨#[53760,-441344,1767680,-4590592,8951808,-13533184,16548864,-17202432,15272896,-11610240,7636448,-4300608,2068608,-845824,279744,-71728,13810,-1724,105]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node96 : RationalCode parameterInterval formula97 :=
  ((RationalCode.constant parameterInterval ((21/20))).add node95)
  |>.recode ⟨#[53760,-441344,1767680,-4590592,8951808,-13533184,16548864,-17202432,15272896,-11610240,7636448,-4300608,2068608,-845824,279744,-71728,13810,-1724,105]⟩ ⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩ node96Denominator node96Cross

/-- Article: exact source arithmetic node 98. -/
private def formula98 (z : ℝ) : ℝ := (u z)^2
private theorem node97Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node97Cross : polynomialCheck
    ((polynomialPower ⟨#[4,-8,8,-4,1]⟩ 2 : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly).mul (polynomialPower ⟨#[-4,0,0,0,1]⟩ 2))=true := by kernel_decide
private def node97 : RationalCode parameterInterval formula98 :=
  (uCode.pow 2)
  |>.recode ⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node97Denominator node97Cross

/-- Article: exact source arithmetic node 99. -/
private def formula99 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(formula98 z)
private theorem node98Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node97Denominator
private theorem node98Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[-32,128,-256,320,-272,160,-64,16,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node98 : RationalCode parameterInterval formula99 :=
  ((RationalCode.constant parameterInterval (-2)).mul node97)
  |>.recode ⟨#[-32,128,-256,320,-272,160,-64,16,-2]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node98Denominator node98Cross

/-- Article: exact source arithmetic node 100. -/
private def formula100 (z : ℝ) : ℝ := (formula97 z)+(formula99 z)
private theorem node99Denominator : ∀ z∈parameterInterval, aeval z (⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩ : QPoly).toPoly≠0 :=
  node96Denominator
private theorem node99Cross : polynomialCheck
    ((((⟨#[53760,-441344,1767680,-4590592,8951808,-13533184,16548864,-17202432,15272896,-11610240,7636448,-4300608,2068608,-845824,279744,-71728,13810,-1724,105]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)).add ((⟨#[-32,128,-256,320,-272,160,-64,16,-2]⟩ : QPoly).mul (⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩ : QPoly)) : QPoly).mul ⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩)
    ((⟨#[-48640,418816,-1724160,4461568,-8108032,11739136,-14345216,14818048,-13171264,10093440,-6585632,3704512,-1793152,733696,-253376,69712,-13470,1636,-95]⟩ : QPoly).mul ((⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node99 : RationalCode parameterInterval formula100 :=
  (node96.add node98)
  |>.recode ⟨#[-48640,418816,-1724160,4461568,-8108032,11739136,-14345216,14818048,-13171264,10093440,-6585632,3704512,-1793152,733696,-253376,69712,-13470,1636,-95]⟩ ⟨#[51200,-225280,435200,-471040,450560,-327680,20480,117760,-180480,192000,-90240,29440,2560,-20480,14080,-7360,3400,-880,100]⟩ node99Denominator node99Cross

/-- Article: exact coefficient representation of the independently specified tail_gap source. -/
def tail_gapCode : RationalCode parameterInterval (fun z : ℝ => (21/20)-meanGap z-2*u z^2) where
  numerator := node99.numerator
  denominator := node99.denominator
  denominator_ne := node99.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => (21/20)-meanGap z-2*u z^2) z=formula100 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node99.exact z hz)

/-- Article: exact uniform P₂ source sign tail_gap, with no numerical premise. -/
theorem tail_gap_positive : ∀ z∈parameterInterval, 0 < ((21/20)-meanGap z-2*u z^2) :=
  tail_gapCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact coefficient representation of the independently specified slope_positive source. -/
def slope_positiveCode : RationalCode parameterInterval (fun z : ℝ => slope z) where
  numerator := slopeCode.numerator
  denominator := slopeCode.denominator
  denominator_ne := slopeCode.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => slope z) z=slope z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (slopeCode.exact z hz)

/-- Article: exact uniform P₂ source sign slope_positive, with no numerical premise. -/
theorem slope_positive_positive : ∀ z∈parameterInterval, 0 < (slope z) :=
  slope_positiveCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 101. -/
private def formula101 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(slope z)
private theorem node100Denominator : ∀ z∈parameterInterval, aeval z (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node100Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[0,0,256,-512,384,-256,192,-128,32]⟩ : QPoly) : QPoly).mul ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩)
    ((⟨#[0,0,-256,512,-384,256,-192,128,-32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node100 : RationalCode parameterInterval formula101 :=
  ((RationalCode.constant parameterInterval (-1)).mul slopeCode)
  |>.recode ⟨#[0,0,-256,512,-384,256,-192,128,-32]⟩ ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ node100Denominator node100Cross

/-- Article: exact source arithmetic node 102. -/
private def formula102 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1 : ℚ) : ℝ)) z)+(formula101 z)
private theorem node101Denominator : ∀ z∈parameterInterval, aeval z (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node100Denominator
private theorem node101Cross : polynomialCheck
    ((((⟨#[1]⟩ : QPoly).mul (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly)).add ((⟨#[0,0,-256,512,-384,256,-192,128,-32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩)
    ((⟨#[32,0,-272,512,-448,256,-224,128,-34,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node101 : RationalCode parameterInterval formula102 :=
  ((RationalCode.constant parameterInterval (1)).add node100)
  |>.recode ⟨#[32,0,-272,512,-448,256,-224,128,-34,0,1]⟩ ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ node101Denominator node101Cross

/-- Article: exact coefficient representation of the independently specified slope_lt_one source. -/
def slope_lt_oneCode : RationalCode parameterInterval (fun z : ℝ => 1-slope z) where
  numerator := node101.numerator
  denominator := node101.denominator
  denominator_ne := node101.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => 1-slope z) z=formula102 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node101.exact z hz)

/-- Article: exact uniform P₂ source sign slope_lt_one, with no numerical premise. -/
theorem slope_lt_one_positive : ∀ z∈parameterInterval, 0 < (1-slope z) :=
  slope_lt_oneCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 103. -/
private def formula103 (z : ℝ) : ℝ := ((fun _ : ℝ => (((10201/40000) : ℚ) : ℝ)) z)+(atomB z)
private theorem node102Denominator : ∀ z∈parameterInterval, aeval z (⟨#[320000,0,-160000,0,-80000,0,40000]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node102Cross : polynomialCheck
    ((((⟨#[(10201/40000)]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)).add ((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[320000,0,-160000,0,-80000,0,40000]⟩)
    ((⟨#[81608,-960000,1559196,-1280000,779598,-240000,10201]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node102 : RationalCode parameterInterval formula103 :=
  ((RationalCode.constant parameterInterval ((10201/40000))).add atomBCode)
  |>.recode ⟨#[81608,-960000,1559196,-1280000,779598,-240000,10201]⟩ ⟨#[320000,0,-160000,0,-80000,0,40000]⟩ node102Denominator node102Cross

/-- Article: exact source arithmetic node 104. -/
private def formula104 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-101/200) : ℚ) : ℝ)) z)*(atomA z)
private theorem node103Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-1600,0,0,0,400]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node103Cross : polynomialCheck
    (((⟨#[(-101/200)]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-1600,0,0,0,400]⟩)
    ((⟨#[-808,2424,-3636,3232,-1818,606,-101]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node103 : RationalCode parameterInterval formula104 :=
  ((RationalCode.constant parameterInterval ((-101/200))).mul atomACode)
  |>.recode ⟨#[-808,2424,-3636,3232,-1818,606,-101]⟩ ⟨#[0,-1600,0,0,0,400]⟩ node103Denominator node103Cross

/-- Article: exact source arithmetic node 105. -/
private def formula105 (z : ℝ) : ℝ := (formula103 z)+(formula104 z)
private theorem node104Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,320000,0,-160000,0,-80000,0,40000]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node104Cross : polynomialCheck
    ((((⟨#[81608,-960000,1559196,-1280000,779598,-240000,10201]⟩ : QPoly).mul (⟨#[0,-1600,0,0,0,400]⟩ : QPoly)).add ((⟨#[-808,2424,-3636,3232,-1818,606,-101]⟩ : QPoly).mul (⟨#[320000,0,-160000,0,-80000,0,40000]⟩ : QPoly)) : QPoly).mul ⟨#[0,320000,0,-160000,0,-80000,0,40000]⟩)
    ((⟨#[161600,-403192,-313600,1155196,-1280000,981598,-401600,70801,-10100]⟩ : QPoly).mul ((⟨#[320000,0,-160000,0,-80000,0,40000]⟩ : QPoly).mul (⟨#[0,-1600,0,0,0,400]⟩ : QPoly)))=true := by kernel_decide
private def node104 : RationalCode parameterInterval formula105 :=
  (node102.add node103)
  |>.recode ⟨#[161600,-403192,-313600,1155196,-1280000,981598,-401600,70801,-10100]⟩ ⟨#[0,320000,0,-160000,0,-80000,0,40000]⟩ node104Denominator node104Cross

/-- Article: exact coefficient representation of the independently specified root_minus_outer source. -/
def root_minus_outerCode : RationalCode parameterInterval (fun z : ℝ => atomPolynomial z (-101/200)) where
  numerator := node104.numerator
  denominator := node104.denominator
  denominator_ne := node104.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => atomPolynomial z (-101/200)) z=formula105 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node104.exact z hz)

/-- Article: exact uniform P₂ source sign root_minus_outer, with no numerical premise. -/
theorem root_minus_outer_positive : ∀ z∈parameterInterval, 0 < (atomPolynomial z (-101/200)) :=
  root_minus_outerCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 106. -/
private def formula106 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-144/625) : ℚ) : ℝ)) z)+(formula10 z)
private theorem node105Denominator : ∀ z∈parameterInterval, aeval z (⟨#[5000,0,-2500,0,-1250,0,625]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node105Cross : polynomialCheck
    ((((⟨#[(-144/625)]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)).add ((⟨#[0,24,-40,32,-20,6]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[5000,0,-2500,0,-1250,0,625]⟩)
    ((⟨#[-1152,15000,-24424,20000,-12212,3750,-144]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node105 : RationalCode parameterInterval formula106 :=
  ((RationalCode.constant parameterInterval ((-144/625))).add node9)
  |>.recode ⟨#[-1152,15000,-24424,20000,-12212,3750,-144]⟩ ⟨#[5000,0,-2500,0,-1250,0,625]⟩ node105Denominator node105Cross

/-- Article: exact source arithmetic node 107. -/
private def formula107 (z : ℝ) : ℝ := ((fun _ : ℝ => (((12/25) : ℚ) : ℝ)) z)*(atomA z)
private theorem node106Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-100,0,0,0,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node106Cross : polynomialCheck
    (((⟨#[(12/25)]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-100,0,0,0,25]⟩)
    ((⟨#[48,-144,216,-192,108,-36,6]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node106 : RationalCode parameterInterval formula107 :=
  ((RationalCode.constant parameterInterval ((12/25))).mul atomACode)
  |>.recode ⟨#[48,-144,216,-192,108,-36,6]⟩ ⟨#[0,-100,0,0,0,25]⟩ node106Denominator node106Cross

/-- Article: exact source arithmetic node 108. -/
private def formula108 (z : ℝ) : ℝ := (formula106 z)+(formula107 z)
private theorem node107Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,5000,0,-2500,0,-1250,0,625]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node107Cross : polynomialCheck
    ((((⟨#[-1152,15000,-24424,20000,-12212,3750,-144]⟩ : QPoly).mul (⟨#[0,-100,0,0,0,25]⟩ : QPoly)).add ((⟨#[48,-144,216,-192,108,-36,6]⟩ : QPoly).mul (⟨#[5000,0,-2500,0,-1250,0,625]⟩ : QPoly)) : QPoly).mul ⟨#[0,5000,0,-2500,0,-1250,0,625]⟩)
    ((⟨#[-2400,6048,5400,-18424,20000,-15212,6150,-1044,150]⟩ : QPoly).mul ((⟨#[5000,0,-2500,0,-1250,0,625]⟩ : QPoly).mul (⟨#[0,-100,0,0,0,25]⟩ : QPoly)))=true := by kernel_decide
private def node107 : RationalCode parameterInterval formula108 :=
  (node105.add node106)
  |>.recode ⟨#[-2400,6048,5400,-18424,20000,-15212,6150,-1044,150]⟩ ⟨#[0,5000,0,-2500,0,-1250,0,625]⟩ node107Denominator node107Cross

/-- Article: exact coefficient representation of the independently specified root_minus_inner source. -/
def root_minus_innerCode : RationalCode parameterInterval (fun z : ℝ => -atomPolynomial z (-12/25)) where
  numerator := node107.numerator
  denominator := node107.denominator
  denominator_ne := node107.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => -atomPolynomial z (-12/25)) z=formula108 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node107.exact z hz)

/-- Article: exact uniform P₂ source sign root_minus_inner, with no numerical premise. -/
theorem root_minus_inner_positive : ∀ z∈parameterInterval, 0 < (-atomPolynomial z (-12/25)) :=
  root_minus_innerCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 109. -/
private def formula109 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/16) : ℚ) : ℝ)) z)+(atomB z)
private theorem node108Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,0,-64,0,-32,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node108Cross : polynomialCheck
    ((((⟨#[(1/16)]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)).add ((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[128,0,-64,0,-32,0,16]⟩)
    ((⟨#[8,-384,636,-512,318,-96,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node108 : RationalCode parameterInterval formula109 :=
  ((RationalCode.constant parameterInterval ((1/16))).add atomBCode)
  |>.recode ⟨#[8,-384,636,-512,318,-96,1]⟩ ⟨#[128,0,-64,0,-32,0,16]⟩ node108Denominator node108Cross

/-- Article: exact source arithmetic node 110. -/
private def formula110 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/4) : ℚ) : ℝ)) z)*(atomA z)
private theorem node109Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-32,0,0,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node109Cross : polynomialCheck
    (((⟨#[(1/4)]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-32,0,0,0,8]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node109 : RationalCode parameterInterval formula110 :=
  ((RationalCode.constant parameterInterval ((1/4))).mul atomACode)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[0,-32,0,0,0,8]⟩ node109Denominator node109Cross

/-- Article: exact source arithmetic node 111. -/
private def formula111 (z : ℝ) : ℝ := (formula109 z)+(formula110 z)
private theorem node110Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,128,0,-64,0,-32,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node110Cross : polynomialCheck
    ((((⟨#[8,-384,636,-512,318,-96,1]⟩ : QPoly).mul (⟨#[0,-32,0,0,0,8]⟩ : QPoly)).add ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[128,0,-64,0,-32,0,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,128,0,-64,0,-32,0,16]⟩)
    ((⟨#[-32,104,-512,716,-512,278,-64,-11,2]⟩ : QPoly).mul ((⟨#[128,0,-64,0,-32,0,16]⟩ : QPoly).mul (⟨#[0,-32,0,0,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node110 : RationalCode parameterInterval formula111 :=
  (node108.add node109)
  |>.recode ⟨#[-32,104,-512,716,-512,278,-64,-11,2]⟩ ⟨#[0,128,0,-64,0,-32,0,16]⟩ node110Denominator node110Cross

/-- Article: exact source arithmetic node 112. -/
private def formula112 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(formula111 z)
private theorem node111Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,128,0,-64,0,-32,0,16]⟩ : QPoly).toPoly≠0 :=
  node110Denominator
private theorem node111Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[-32,104,-512,716,-512,278,-64,-11,2]⟩ : QPoly) : QPoly).mul ⟨#[0,128,0,-64,0,-32,0,16]⟩)
    ((⟨#[32,-104,512,-716,512,-278,64,11,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,128,0,-64,0,-32,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node111 : RationalCode parameterInterval formula112 :=
  ((RationalCode.constant parameterInterval (-1)).mul node110)
  |>.recode ⟨#[32,-104,512,-716,512,-278,64,11,-2]⟩ ⟨#[0,128,0,-64,0,-32,0,16]⟩ node111Denominator node111Cross

/-- Article: exact coefficient representation of the independently specified root_plus_inner source. -/
def root_plus_innerCode : RationalCode parameterInterval (fun z : ℝ => -atomPolynomial z (1/4)) where
  numerator := node111.numerator
  denominator := node111.denominator
  denominator_ne := node111.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => -atomPolynomial z (1/4)) z=formula112 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node111.exact z hz)

/-- Article: exact uniform P₂ source sign root_plus_inner, with no numerical premise. -/
theorem root_plus_inner_positive : ∀ z∈parameterInterval, 0 < (-atomPolynomial z (1/4)) :=
  root_plus_innerCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 113. -/
private def formula113 (z : ℝ) : ℝ := ((fun _ : ℝ => (((3249/40000) : ℚ) : ℝ)) z)+(atomB z)
private theorem node112Denominator : ∀ z∈parameterInterval, aeval z (⟨#[320000,0,-160000,0,-80000,0,40000]⟩ : QPoly).toPoly≠0 :=
  node102Denominator
private theorem node112Cross : polynomialCheck
    ((((⟨#[(3249/40000)]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)).add ((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[320000,0,-160000,0,-80000,0,40000]⟩)
    ((⟨#[25992,-960000,1587004,-1280000,793502,-240000,3249]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node112 : RationalCode parameterInterval formula113 :=
  ((RationalCode.constant parameterInterval ((3249/40000))).add atomBCode)
  |>.recode ⟨#[25992,-960000,1587004,-1280000,793502,-240000,3249]⟩ ⟨#[320000,0,-160000,0,-80000,0,40000]⟩ node112Denominator node112Cross

/-- Article: exact source arithmetic node 114. -/
private def formula114 (z : ℝ) : ℝ := ((fun _ : ℝ => (((57/200) : ℚ) : ℝ)) z)*(atomA z)
private theorem node113Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-1600,0,0,0,400]⟩ : QPoly).toPoly≠0 :=
  node103Denominator
private theorem node113Cross : polynomialCheck
    (((⟨#[(57/200)]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-1600,0,0,0,400]⟩)
    ((⟨#[456,-1368,2052,-1824,1026,-342,57]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node113 : RationalCode parameterInterval formula114 :=
  ((RationalCode.constant parameterInterval ((57/200))).mul atomACode)
  |>.recode ⟨#[456,-1368,2052,-1824,1026,-342,57]⟩ ⟨#[0,-1600,0,0,0,400]⟩ node113Denominator node113Cross

/-- Article: exact source arithmetic node 115. -/
private def formula115 (z : ℝ) : ℝ := (formula113 z)+(formula114 z)
private theorem node114Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,320000,0,-160000,0,-80000,0,40000]⟩ : QPoly).toPoly≠0 :=
  node104Denominator
private theorem node114Cross : polynomialCheck
    ((((⟨#[25992,-960000,1587004,-1280000,793502,-240000,3249]⟩ : QPoly).mul (⟨#[0,-1600,0,0,0,400]⟩ : QPoly)).add ((⟨#[456,-1368,2052,-1824,1026,-342,57]⟩ : QPoly).mul (⟨#[320000,0,-160000,0,-80000,0,40000]⟩ : QPoly)) : QPoly).mul ⟨#[0,320000,0,-160000,0,-80000,0,40000]⟩)
    ((⟨#[-91200,299592,-1324800,1815004,-1280000,679502,-148800,-30951,5700]⟩ : QPoly).mul ((⟨#[320000,0,-160000,0,-80000,0,40000]⟩ : QPoly).mul (⟨#[0,-1600,0,0,0,400]⟩ : QPoly)))=true := by kernel_decide
private def node114 : RationalCode parameterInterval formula115 :=
  (node112.add node113)
  |>.recode ⟨#[-91200,299592,-1324800,1815004,-1280000,679502,-148800,-30951,5700]⟩ ⟨#[0,320000,0,-160000,0,-80000,0,40000]⟩ node114Denominator node114Cross

/-- Article: exact coefficient representation of the independently specified root_plus_outer source. -/
def root_plus_outerCode : RationalCode parameterInterval (fun z : ℝ => atomPolynomial z (57/200)) where
  numerator := node114.numerator
  denominator := node114.denominator
  denominator_ne := node114.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => atomPolynomial z (57/200)) z=formula115 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node114.exact z hz)

/-- Article: exact uniform P₂ source sign root_plus_outer, with no numerical premise. -/
theorem root_plus_outer_positive : ∀ z∈parameterInterval, 0 < (atomPolynomial z (57/200)) :=
  root_plus_outerCode.positive_check (sg := 1) (Or.inl rfl) (by kernel_decide) (by kernel_decide)

/-- Article: exact source arithmetic node 116. -/
private def formula116 (z : ℝ) : ℝ := (id z)⁻¹
private theorem node115Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node115Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[0,1]⟩))=true := by kernel_decide
private def node115 : RationalCode parameterInterval formula116 :=
  ((RationalCode.variable parameterInterval).inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[0,1]⟩ node115Denominator node115Cross

/-- Article: exact source arithmetic node 117. -/
private def formula117 (z : ℝ) : ℝ := (formula116 z)^2
private theorem node116Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node116Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[0,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[0,1]⟩ 2))=true := by kernel_decide
private def node116 : RationalCode parameterInterval formula117 :=
  (node115.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[0,0,1]⟩ node116Denominator node116Cross

/-- Article: exact source arithmetic node 118. -/
private def formula118 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/8) : ℚ) : ℝ)) z)*(formula117 z)
private theorem node117Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node117Cross : polynomialCheck
    (((⟨#[(1/8)]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,8]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node117 : RationalCode parameterInterval formula118 :=
  ((RationalCode.constant parameterInterval ((1/8))).mul node116)
  |>.recode ⟨#[1]⟩ ⟨#[0,0,8]⟩ node117Denominator node117Cross

/-- Article: exact source arithmetic node 119. -/
private def formula119 (z : ℝ) : ℝ := (formula17 z)⁻¹
private theorem node118Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node17Denominator
private theorem node118Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,0,1]⟩))=true := by kernel_decide
private def node118 : RationalCode parameterInterval formula119 :=
  (node16.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,0,1]⟩ node118Denominator node118Cross

/-- Article: exact source arithmetic node 120. -/
private def formula120 (z : ℝ) : ℝ := (formula119 z)^7
private theorem node119Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-128,0,448,0,-672,0,560,0,-280,0,84,0,-14,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node119Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 7 : QPoly).mul ⟨#[-128,0,448,0,-672,0,560,0,-280,0,84,0,-14,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[-2,0,1]⟩ 7))=true := by kernel_decide
private def node119 : RationalCode parameterInterval formula120 :=
  (node118.pow 7)
  |>.recode ⟨#[1]⟩ ⟨#[-128,0,448,0,-672,0,560,0,-280,0,84,0,-14,0,1]⟩ node119Denominator node119Cross

/-- Article: exact source arithmetic node 121. -/
private def formula121 (z : ℝ) : ℝ := (formula118 z)*(formula120 z)
private theorem node120Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-1024,0,3584,0,-5376,0,4480,0,-2240,0,672,0,-112,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node120Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-1024,0,3584,0,-5376,0,4480,0,-2240,0,672,0,-112,0,8]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[0,0,8]⟩ : QPoly).mul (⟨#[-128,0,448,0,-672,0,560,0,-280,0,84,0,-14,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node120 : RationalCode parameterInterval formula121 :=
  (node117.mul node119)
  |>.recode ⟨#[1]⟩ ⟨#[0,0,-1024,0,3584,0,-5376,0,4480,0,-2240,0,672,0,-112,0,8]⟩ node120Denominator node120Cross

/-- Article: exact source arithmetic node 122. -/
private def formula122 (z : ℝ) : ℝ := (formula21 z)⁻¹
private theorem node121Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2,0,1]⟩ : QPoly).toPoly≠0 :=
  node21Denominator
private theorem node121Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[2,0,1]⟩))=true := by kernel_decide
private def node121 : RationalCode parameterInterval formula122 :=
  (node20.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[2,0,1]⟩ node121Denominator node121Cross

/-- Article: exact source arithmetic node 123. -/
private def formula123 (z : ℝ) : ℝ := (formula122 z)^2
private theorem node122Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node122Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[4,0,4,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[2,0,1]⟩ 2))=true := by kernel_decide
private def node122 : RationalCode parameterInterval formula123 :=
  (node121.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[4,0,4,0,1]⟩ node122Denominator node122Cross

/-- Article: exact source arithmetic node 124. -/
private def formula124 (z : ℝ) : ℝ := (formula121 z)*(formula123 z)
private theorem node123Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node123Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[0,0,-1024,0,3584,0,-5376,0,4480,0,-2240,0,672,0,-112,0,8]⟩ : QPoly).mul (⟨#[4,0,4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node123 : RationalCode parameterInterval formula124 :=
  (node120.mul node122)
  |>.recode ⟨#[1]⟩ ⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩ node123Denominator node123Cross

/-- Article: exact source arithmetic node 125. -/
private def formula125 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)+(formula16 z)
private theorem node124Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node124Cross : polynomialCheck
    ((((⟨#[2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node124 : RationalCode parameterInterval formula125 :=
  ((RationalCode.constant parameterInterval (2)).add node15)
  |>.recode ⟨#[2,0,1]⟩ ⟨#[1]⟩ node124Denominator node124Cross

/-- Article: exact source arithmetic node 126. -/
private def formula126 (z : ℝ) : ℝ := (formula125 z)+(formula59 z)
private theorem node125Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node125Cross : polynomialCheck
    ((((⟨#[2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,-2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node125 : RationalCode parameterInterval formula126 :=
  (node124.add node58)
  |>.recode ⟨#[2,-2,1]⟩ ⟨#[1]⟩ node125Denominator node125Cross

/-- Article: exact source arithmetic node 127. -/
private def formula127 (z : ℝ) : ℝ := (formula126 z)^3
private theorem node126Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node13Denominator
private theorem node126Cross : polynomialCheck
    ((polynomialPower ⟨#[2,-2,1]⟩ 3 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 3))=true := by kernel_decide
private def node126 : RationalCode parameterInterval formula127 :=
  (node125.pow 3)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[1]⟩ node126Denominator node126Cross

/-- Article: exact source arithmetic node 128. -/
private def formula128 (z : ℝ) : ℝ := (formula124 z)*(formula127 z)
private theorem node127Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩ : QPoly).toPoly≠0 :=
  node123Denominator
private theorem node127Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node127 : RationalCode parameterInterval formula128 :=
  (node123.mul node126)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩ node127Denominator node127Cross

/-- Article: exact source arithmetic node 129. -/
private def formula129 (z : ℝ) : ℝ := (formula50 z)⁻¹
private theorem node128Denominator : ∀ z∈parameterInterval, aeval z (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  node50Denominator
private theorem node128Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩))=true := by kernel_decide
private def node128 : RationalCode parameterInterval formula129 :=
  (node49.inv (signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ node128Denominator node128Cross

/-- Article: exact source arithmetic node 130. -/
private def formula130 (z : ℝ) : ℝ := (formula128 z)*(formula129 z)
private theorem node129Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node129Cross : polynomialCheck
    (((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node129 : RationalCode parameterInterval formula130 :=
  (node127.mul node128)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node129Denominator node129Cross

/-- Article: exact source arithmetic node 131. -/
private def formula131 (z : ℝ) : ℝ := (formula130 z)*(formula60 z)
private theorem node130Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node129Denominator
private theorem node130Cross : polynomialCheck
    (((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[-2,-2,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[-16,32,-16,-32,64,-56,28,-8,1]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node130 : RationalCode parameterInterval formula131 :=
  (node129.mul node59)
  |>.recode ⟨#[-16,32,-16,-32,64,-56,28,-8,1]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node130Denominator node130Cross

/-- Article: exact source arithmetic node 132. -/
private def formula132 (z : ℝ) : ℝ := (formula131 z)*(formula63 z)
private theorem node131Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node129Denominator
private theorem node131Cross : polynomialCheck
    (((⟨#[-16,32,-16,-32,64,-56,28,-8,1]⟩ : QPoly).mul (⟨#[-2,2,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[32,-96,80,64,-208,208,-104,16,10,-6,1]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node131 : RationalCode parameterInterval formula132 :=
  (node130.mul node62)
  |>.recode ⟨#[32,-96,80,64,-208,208,-104,16,10,-6,1]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node131Denominator node131Cross

/-- Article: exact source arithmetic node 133. -/
private def formula133 (z : ℝ) : ℝ := (formula132 z)*(formula83 z)
private theorem node132Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node129Denominator
private theorem node132Cross : polynomialCheck
    (((⟨#[32,-96,80,64,-208,208,-104,16,10,-6,1]⟩ : QPoly).mul (⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[5120,-27648,68608,-142848,278784,-362496,142336,442368,-1070464,1329792,-1117056,664896,-267616,55296,8896,-11328,4356,-1116,268,-54,5]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node132 : RationalCode parameterInterval formula133 :=
  (node131.mul node82)
  |>.recode ⟨#[5120,-27648,68608,-142848,278784,-362496,142336,442368,-1070464,1329792,-1117056,664896,-267616,55296,8896,-11328,4356,-1116,268,-54,5]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node132Denominator node132Cross

/-- Article: exact coefficient representation of the independently specified upper_five_factor source. -/
def upper_five_factorCode : RationalCode parameterInterval (fun z : ℝ => upperFiveFactor z) where
  numerator := node132.numerator
  denominator := node132.denominator
  denominator_ne := node132.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => upperFiveFactor z) z=formula133 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,upperFiveFactor,atomPolynomial,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node132.exact z hz)

/-- Article: exact uniform P₂ source sign upper_five_factor, with no numerical premise. -/
theorem upper_five_factor_positive : ∀ z∈parameterInterval, 0 < (upperFiveFactor z) :=
  upper_five_factorCode.positive_check (sg := -1) (Or.inr rfl) (by kernel_decide) (by kernel_decide)

end
end polyak.Boundary.P2
