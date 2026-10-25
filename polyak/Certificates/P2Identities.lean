import polyak.Numerics.KernelDecide
import polyak.Certificates.P2Codes
import polyak.Boundary.P2.Roots

/-! Article: Lemmas p2ids and p2ends. Exact source-linked polynomial identities. -/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
/-- Article: exact source arithmetic node 1. -/
private def formula1 (z : ℝ) : ℝ := (meanCosine z)^2
private theorem node0Denominator : ∀ z∈parameterInterval, aeval z (⟨#[102400,-901120,3620864,-8642560,13895680,-16838656,16896000,-13383680,6285056,456704,-4188160,5790720,-5144832,2895360,-1047040,57088,392816,-418240,264000,-131552,54280,-16880,3536,-440,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node0Cross : polynomialCheck
    ((polynomialPower ⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ 2 : QPoly).mul ⟨#[102400,-901120,3620864,-8642560,13895680,-16838656,16896000,-13383680,6285056,456704,-4188160,5790720,-5144832,2895360,-1047040,57088,392816,-418240,264000,-131552,54280,-16880,3536,-440,25]⟩)
    ((⟨#[0,0,0,0,921600,-5652480,15548416,-27860992,39407616,-46510080,46264320,-39999488,30336512,-19999744,11566080,-5813760,2462976,-870656,242944,-44160,3600]⟩ : QPoly).mul (polynomialPower ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ 2))=true := by kernel_decide
private def node0 : RationalCode parameterInterval formula1 :=
  (meanCosineCode.pow 2)
  |>.recode ⟨#[0,0,0,0,921600,-5652480,15548416,-27860992,39407616,-46510080,46264320,-39999488,30336512,-19999744,11566080,-5813760,2462976,-870656,242944,-44160,3600]⟩ ⟨#[102400,-901120,3620864,-8642560,13895680,-16838656,16896000,-13383680,6285056,456704,-4188160,5790720,-5144832,2895360,-1047040,57088,392816,-418240,264000,-131552,54280,-16880,3536,-440,25]⟩ node0Denominator node0Cross

/-- Article: exact source arithmetic node 2. -/
private def formula2 (z : ℝ) : ℝ := (atomB z)+(formula1 z)
private theorem node1Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node1Cross : polynomialCheck
    ((((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul (⟨#[102400,-901120,3620864,-8642560,13895680,-16838656,16896000,-13383680,6285056,456704,-4188160,5790720,-5144832,2895360,-1047040,57088,392816,-418240,264000,-131552,54280,-16880,3536,-440,25]⟩ : QPoly)).add ((⟨#[0,0,0,0,921600,-5652480,15548416,-27860992,39407616,-46510080,46264320,-39999488,30336512,-19999744,11566080,-5813760,2462976,-870656,242944,-44160,3600]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,-614400,6430720,-32169984,104058880,-246747136,461211648,-718346240,964416512,-1130744320,1171608576,-1084976128,900317696,-670862848,450158848,-271244032,146451072,-70671520,30138016,-11224160,3603216,-963856,203240,-31416,3140,-150]⟩ : QPoly).mul ((⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).mul (⟨#[102400,-901120,3620864,-8642560,13895680,-16838656,16896000,-13383680,6285056,456704,-4188160,5790720,-5144832,2895360,-1047040,57088,392816,-418240,264000,-131552,54280,-16880,3536,-440,25]⟩ : QPoly)))=true := by kernel_decide
private def node1 : RationalCode parameterInterval formula2 :=
  (atomBCode.add node0)
  |>.recode ⟨#[0,-614400,6430720,-32169984,104058880,-246747136,461211648,-718346240,964416512,-1130744320,1171608576,-1084976128,900317696,-670862848,450158848,-271244032,146451072,-70671520,30138016,-11224160,3603216,-963856,203240,-31416,3140,-150]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node1Denominator node1Cross

/-- Article: exact source arithmetic node 3. -/
private def formula3 (z : ℝ) : ℝ := (atomA z)*(meanCosine z)
private theorem node2Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node2Cross : polynomialCheck
    (((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ : QPoly) : QPoly).mul ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩)
    ((⟨#[0,3840,-23296,66944,-125440,174656,-193600,177312,-136448,88656,-48400,21832,-7840,2092,-364,30]⟩ : QPoly).mul ((⟨#[0,-8,0,0,0,2]⟩ : QPoly).mul (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node2 : RationalCode parameterInterval formula3 :=
  (atomACode.mul meanCosineCode)
  |>.recode ⟨#[0,3840,-23296,66944,-125440,174656,-193600,177312,-136448,88656,-48400,21832,-7840,2092,-364,30]⟩ ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ node2Denominator node2Cross

/-- Article: exact source arithmetic node 4. -/
private def formula4 (z : ℝ) : ℝ := (formula2 z)+(formula3 z)
private theorem node3Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node3Cross : polynomialCheck
    ((((⟨#[0,-614400,6430720,-32169984,104058880,-246747136,461211648,-718346240,964416512,-1130744320,1171608576,-1084976128,900317696,-670862848,450158848,-271244032,146451072,-70671520,30138016,-11224160,3603216,-963856,203240,-31416,3140,-150]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,3840,-23296,66944,-125440,174656,-193600,177312,-136448,88656,-48400,21832,-7840,2092,-364,30]⟩ : QPoly).mul (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly)) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,163840,-475136,557056,-1810432,3022848,-147456,-2850816,4382720,-7221248,7653376,-5689344,3826688,-1805312,547840,-178176,-4608,47232,-14144,2176,-928,160]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node3 : RationalCode parameterInterval formula4 :=
  (node1.add node2)
  |>.recode ⟨#[0,0,0,163840,-475136,557056,-1810432,3022848,-147456,-2850816,4382720,-7221248,7653376,-5689344,3826688,-1805312,547840,-178176,-4608,47232,-14144,2176,-928,160]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node3Denominator node3Cross

/-- Article: exact source arithmetic node 5. -/
private def formula5 (z : ℝ) : ℝ := (id z)^3
private theorem node4Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node4Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 3 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 3))=true := by kernel_decide
private def node4 : RationalCode parameterInterval formula5 :=
  ((RationalCode.variable parameterInterval).pow 3)
  |>.recode ⟨#[0,0,0,1]⟩ ⟨#[1]⟩ node4Denominator node4Cross

/-- Article: exact source arithmetic node 6. -/
private def formula6 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-32 : ℚ) : ℝ)) z)*(formula5 z)
private theorem node5Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node5Cross : polynomialCheck
    (((⟨#[-32]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node5 : RationalCode parameterInterval formula6 :=
  ((RationalCode.constant parameterInterval (-32)).mul node4)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[1]⟩ node5Denominator node5Cross

/-- Article: exact source arithmetic node 7. -/
private def formula7 (z : ℝ) : ℝ := (id z)^2
private theorem node6Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node6Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 2 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 2))=true := by kernel_decide
private def node6 : RationalCode parameterInterval formula7 :=
  ((RationalCode.variable parameterInterval).pow 2)
  |>.recode ⟨#[0,0,1]⟩ ⟨#[1]⟩ node6Denominator node6Cross

/-- Article: exact source arithmetic node 8. -/
private def formula8 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula7 z)
private theorem node7Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node7Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node7 : RationalCode parameterInterval formula8 :=
  ((RationalCode.constant parameterInterval (-2)).add node6)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node7Denominator node7Cross

/-- Article: exact source arithmetic node 9. -/
private def formula9 (z : ℝ) : ℝ := (formula8 z)⁻¹
private theorem node8Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node8Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,0,1]⟩))=true := by kernel_decide
private def node8 : RationalCode parameterInterval formula9 :=
  (node7.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,0,1]⟩ node8Denominator node8Cross

/-- Article: exact source arithmetic node 10. -/
private def formula10 (z : ℝ) : ℝ := (formula9 z)^2
private theorem node9Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node9Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[4,0,-4,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[-2,0,1]⟩ 2))=true := by kernel_decide
private def node9 : RationalCode parameterInterval formula10 :=
  (node8.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[4,0,-4,0,1]⟩ node9Denominator node9Cross

/-- Article: exact source arithmetic node 11. -/
private def formula11 (z : ℝ) : ℝ := (formula6 z)*(formula10 z)
private theorem node10Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
private theorem node10Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[4,0,-4,0,1]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[4,0,-4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node10 : RationalCode parameterInterval formula11 :=
  (node5.mul node9)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[4,0,-4,0,1]⟩ node10Denominator node10Cross

/-- Article: exact source arithmetic node 12. -/
private def formula12 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)+(formula7 z)
private theorem node11Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node11Cross : polynomialCheck
    ((((⟨#[2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node11 : RationalCode parameterInterval formula12 :=
  ((RationalCode.constant parameterInterval (2)).add node6)
  |>.recode ⟨#[2,0,1]⟩ ⟨#[1]⟩ node11Denominator node11Cross

/-- Article: exact source arithmetic node 13. -/
private def formula13 (z : ℝ) : ℝ := (formula12 z)⁻¹
private theorem node12Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node12Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[2,0,1]⟩))=true := by kernel_decide
private def node12 : RationalCode parameterInterval formula13 :=
  (node11.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[2,0,1]⟩ node12Denominator node12Cross

/-- Article: exact source arithmetic node 14. -/
private def formula14 (z : ℝ) : ℝ := (formula11 z)*(formula13 z)
private theorem node13Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node13Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[8,0,-4,0,-2,0,1]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[4,0,-4,0,1]⟩ : QPoly).mul (⟨#[2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node13 : RationalCode parameterInterval formula14 :=
  (node10.mul node12)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[8,0,-4,0,-2,0,1]⟩ node13Denominator node13Cross

/-- Article: exact source arithmetic node 15. -/
private def formula15 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1472 : ℚ) : ℝ)) z)*(formula5 z)
private theorem node14Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node14Cross : polynomialCheck
    (((⟨#[-1472]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-1472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node14 : RationalCode parameterInterval formula15 :=
  ((RationalCode.constant parameterInterval (-1472)).mul node4)
  |>.recode ⟨#[0,0,0,-1472]⟩ ⟨#[1]⟩ node14Denominator node14Cross

/-- Article: exact source arithmetic node 16. -/
private def formula16 (z : ℝ) : ℝ := ((fun _ : ℝ => ((160 : ℚ) : ℝ)) z)+(formula15 z)
private theorem node15Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node15Cross : polynomialCheck
    ((((⟨#[160]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-1472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-1472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node15 : RationalCode parameterInterval formula16 :=
  ((RationalCode.constant parameterInterval (160)).add node14)
  |>.recode ⟨#[160,0,0,-1472]⟩ ⟨#[1]⟩ node15Denominator node15Cross

/-- Article: exact source arithmetic node 17. -/
private def formula17 (z : ℝ) : ℝ := (id z)^5
private theorem node16Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node16Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 5 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 5))=true := by kernel_decide
private def node16 : RationalCode parameterInterval formula17 :=
  ((RationalCode.variable parameterInterval).pow 5)
  |>.recode ⟨#[0,0,0,0,0,1]⟩ ⟨#[1]⟩ node16Denominator node16Cross

/-- Article: exact source arithmetic node 18. -/
private def formula18 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1376 : ℚ) : ℝ)) z)*(formula17 z)
private theorem node17Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node17Cross : polynomialCheck
    (((⟨#[-1376]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node17 : RationalCode parameterInterval formula18 :=
  ((RationalCode.constant parameterInterval (-1376)).mul node16)
  |>.recode ⟨#[0,0,0,0,0,-1376]⟩ ⟨#[1]⟩ node17Denominator node17Cross

/-- Article: exact source arithmetic node 19. -/
private def formula19 (z : ℝ) : ℝ := (formula16 z)+(formula18 z)
private theorem node18Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node18Cross : polynomialCheck
    ((((⟨#[160,0,0,-1472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-1472,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node18 : RationalCode parameterInterval formula19 :=
  (node15.add node17)
  |>.recode ⟨#[160,0,0,-1472,0,-1376]⟩ ⟨#[1]⟩ node18Denominator node18Cross

/-- Article: exact source arithmetic node 20. -/
private def formula20 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-704 : ℚ) : ℝ)) z)*(id z)
private theorem node19Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node19Cross : polynomialCheck
    (((⟨#[-704]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-704]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node19 : RationalCode parameterInterval formula20 :=
  ((RationalCode.constant parameterInterval (-704)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-704]⟩ ⟨#[1]⟩ node19Denominator node19Cross

/-- Article: exact source arithmetic node 21. -/
private def formula21 (z : ℝ) : ℝ := (formula19 z)+(formula20 z)
private theorem node20Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node20Cross : polynomialCheck
    ((((⟨#[160,0,0,-1472,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-704]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node20 : RationalCode parameterInterval formula21 :=
  (node18.add node19)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376]⟩ ⟨#[1]⟩ node20Denominator node20Cross

/-- Article: exact source arithmetic node 22. -/
private def formula22 (z : ℝ) : ℝ := (id z)^7
private theorem node21Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node21Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 7 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 7))=true := by kernel_decide
private def node21 : RationalCode parameterInterval formula22 :=
  ((RationalCode.variable parameterInterval).pow 7)
  |>.recode ⟨#[0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node21Denominator node21Cross

/-- Article: exact source arithmetic node 23. -/
private def formula23 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-368 : ℚ) : ℝ)) z)*(formula22 z)
private theorem node22Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node22Cross : polynomialCheck
    (((⟨#[-368]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-368]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node22 : RationalCode parameterInterval formula23 :=
  ((RationalCode.constant parameterInterval (-368)).mul node21)
  |>.recode ⟨#[0,0,0,0,0,0,0,-368]⟩ ⟨#[1]⟩ node22Denominator node22Cross

/-- Article: exact source arithmetic node 24. -/
private def formula24 (z : ℝ) : ℝ := (formula21 z)+(formula23 z)
private theorem node23Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node23Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-368]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node23 : RationalCode parameterInterval formula24 :=
  (node20.add node22)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ ⟨#[1]⟩ node23Denominator node23Cross

/-- Article: exact source arithmetic node 25. -/
private def formula25 (z : ℝ) : ℝ := (id z)^9
private theorem node24Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node24Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 9 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 9))=true := by kernel_decide
private def node24 : RationalCode parameterInterval formula25 :=
  ((RationalCode.variable parameterInterval).pow 9)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node24Denominator node24Cross

/-- Article: exact source arithmetic node 26. -/
private def formula26 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-44 : ℚ) : ℝ)) z)*(formula25 z)
private theorem node25Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node25Cross : polynomialCheck
    (((⟨#[-44]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node25 : RationalCode parameterInterval formula26 :=
  ((RationalCode.constant parameterInterval (-44)).mul node24)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ ⟨#[1]⟩ node25Denominator node25Cross

/-- Article: exact source arithmetic node 27. -/
private def formula27 (z : ℝ) : ℝ := (formula24 z)+(formula26 z)
private theorem node26Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node26Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node26 : RationalCode parameterInterval formula27 :=
  (node23.add node25)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ ⟨#[1]⟩ node26Denominator node26Cross

/-- Article: exact source arithmetic node 28. -/
private def formula28 (z : ℝ) : ℝ := (id z)^10
private theorem node27Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node27Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 10 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 10))=true := by kernel_decide
private def node27 : RationalCode parameterInterval formula28 :=
  ((RationalCode.variable parameterInterval).pow 10)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node27Denominator node27Cross

/-- Article: exact source arithmetic node 29. -/
private def formula29 (z : ℝ) : ℝ := ((fun _ : ℝ => ((5 : ℚ) : ℝ)) z)*(formula28 z)
private theorem node28Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node28Cross : polynomialCheck
    (((⟨#[5]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node28 : RationalCode parameterInterval formula29 :=
  ((RationalCode.constant parameterInterval (5)).mul node27)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ ⟨#[1]⟩ node28Denominator node28Cross

/-- Article: exact source arithmetic node 30. -/
private def formula30 (z : ℝ) : ℝ := (formula27 z)+(formula29 z)
private theorem node29Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node29Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node29 : RationalCode parameterInterval formula30 :=
  (node26.add node28)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ ⟨#[1]⟩ node29Denominator node29Cross

/-- Article: exact source arithmetic node 31. -/
private def formula31 (z : ℝ) : ℝ := (id z)^8
private theorem node30Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node30Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 8 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 8))=true := by kernel_decide
private def node30 : RationalCode parameterInterval formula31 :=
  ((RationalCode.variable parameterInterval).pow 8)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node30Denominator node30Cross

/-- Article: exact source arithmetic node 32. -/
private def formula32 (z : ℝ) : ℝ := ((fun _ : ℝ => ((170 : ℚ) : ℝ)) z)*(formula31 z)
private theorem node31Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node31Cross : polynomialCheck
    (((⟨#[170]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node31 : RationalCode parameterInterval formula32 :=
  ((RationalCode.constant parameterInterval (170)).mul node30)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,170]⟩ ⟨#[1]⟩ node31Denominator node31Cross

/-- Article: exact source arithmetic node 33. -/
private def formula33 (z : ℝ) : ℝ := (formula30 z)+(formula32 z)
private theorem node32Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node32Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node32 : RationalCode parameterInterval formula33 :=
  (node29.add node31)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ ⟨#[1]⟩ node32Denominator node32Cross

/-- Article: exact source arithmetic node 34. -/
private def formula34 (z : ℝ) : ℝ := (id z)^6
private theorem node33Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node33Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 6 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 6))=true := by kernel_decide
private def node33 : RationalCode parameterInterval formula34 :=
  ((RationalCode.variable parameterInterval).pow 6)
  |>.recode ⟨#[0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node33Denominator node33Cross

/-- Article: exact source arithmetic node 35. -/
private def formula35 (z : ℝ) : ℝ := ((fun _ : ℝ => ((744 : ℚ) : ℝ)) z)*(formula34 z)
private theorem node34Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node34Cross : polynomialCheck
    (((⟨#[744]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node34 : RationalCode parameterInterval formula35 :=
  ((RationalCode.constant parameterInterval (744)).mul node33)
  |>.recode ⟨#[0,0,0,0,0,0,744]⟩ ⟨#[1]⟩ node34Denominator node34Cross

/-- Article: exact source arithmetic node 36. -/
private def formula36 (z : ℝ) : ℝ := (formula33 z)+(formula35 z)
private theorem node35Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node35Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node35 : RationalCode parameterInterval formula36 :=
  (node32.add node34)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node35Denominator node35Cross

/-- Article: exact source arithmetic node 37. -/
private def formula37 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1360 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node36Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node36Cross : polynomialCheck
    (((⟨#[1360]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1360]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node36 : RationalCode parameterInterval formula37 :=
  ((RationalCode.constant parameterInterval (1360)).mul node6)
  |>.recode ⟨#[0,0,1360]⟩ ⟨#[1]⟩ node36Denominator node36Cross

/-- Article: exact source arithmetic node 38. -/
private def formula38 (z : ℝ) : ℝ := (formula36 z)+(formula37 z)
private theorem node37Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node37Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1360]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node37 : RationalCode parameterInterval formula38 :=
  (node35.add node36)
  |>.recode ⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node37Denominator node37Cross

/-- Article: exact source arithmetic node 39. -/
private def formula39 (z : ℝ) : ℝ := (id z)^4
private theorem node38Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node38Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 4 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 4))=true := by kernel_decide
private def node38 : RationalCode parameterInterval formula39 :=
  ((RationalCode.variable parameterInterval).pow 4)
  |>.recode ⟨#[0,0,0,0,1]⟩ ⟨#[1]⟩ node38Denominator node38Cross

/-- Article: exact source arithmetic node 40. -/
private def formula40 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1488 : ℚ) : ℝ)) z)*(formula39 z)
private theorem node39Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node39Cross : polynomialCheck
    (((⟨#[1488]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node39 : RationalCode parameterInterval formula40 :=
  ((RationalCode.constant parameterInterval (1488)).mul node38)
  |>.recode ⟨#[0,0,0,0,1488]⟩ ⟨#[1]⟩ node39Denominator node39Cross

/-- Article: exact source arithmetic node 41. -/
private def formula41 (z : ℝ) : ℝ := (formula38 z)+(formula40 z)
private theorem node40Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node40Cross : polynomialCheck
    ((((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node40 : RationalCode parameterInterval formula41 :=
  (node37.add node39)
  |>.recode ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node40Denominator node40Cross

/-- Article: exact source arithmetic node 42. -/
private def formula42 (z : ℝ) : ℝ := (formula41 z)⁻¹
private theorem node41Denominator : ∀ z∈parameterInterval, aeval z (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node41Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩))=true := by kernel_decide
private def node41 : RationalCode parameterInterval formula42 :=
  (node40.inv (signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ node41Denominator node41Cross

/-- Article: exact source arithmetic node 43. -/
private def formula43 (z : ℝ) : ℝ := (formula42 z)^2
private theorem node42Denominator : ∀ z∈parameterInterval, aeval z (⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node42Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ 2))=true := by kernel_decide
private def node42 : RationalCode parameterInterval formula43 :=
  (node41.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩ node42Denominator node42Cross

/-- Article: exact source arithmetic node 44. -/
private def formula44 (z : ℝ) : ℝ := (formula14 z)*(formula43 z)
private theorem node43Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node43Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,-32]⟩ : QPoly).mul ((⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).mul (⟨#[25600,-225280,930816,-2385920,4398336,-6539264,8389632,-9288704,8861312,-7539712,5716864,-3769856,2215328,-1161088,524352,-204352,68724,-18640,3636,-440,25]⟩ : QPoly)))=true := by kernel_decide
private def node43 : RationalCode parameterInterval formula44 :=
  (node13.mul node42)
  |>.recode ⟨#[0,0,0,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node43Denominator node43Cross

/-- Article: exact source arithmetic node 45. -/
private def formula45 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)+(formula5 z)
private theorem node44Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node44Cross : polynomialCheck
    ((((⟨#[-4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-4,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node44 : RationalCode parameterInterval formula45 :=
  ((RationalCode.constant parameterInterval (-4)).add node4)
  |>.recode ⟨#[-4,0,0,1]⟩ ⟨#[1]⟩ node44Denominator node44Cross

/-- Article: exact source arithmetic node 46. -/
private def formula46 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(id z)
private theorem node45Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node45Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node45 : RationalCode parameterInterval formula46 :=
  ((RationalCode.constant parameterInterval (2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,2]⟩ ⟨#[1]⟩ node45Denominator node45Cross

/-- Article: exact source arithmetic node 47. -/
private def formula47 (z : ℝ) : ℝ := (formula45 z)+(formula46 z)
private theorem node46Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node46Cross : polynomialCheck
    ((((⟨#[-4,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-4,2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node46 : RationalCode parameterInterval formula47 :=
  (node44.add node45)
  |>.recode ⟨#[-4,2,0,1]⟩ ⟨#[1]⟩ node46Denominator node46Cross

/-- Article: exact source arithmetic node 48. -/
private def formula48 (z : ℝ) : ℝ := (formula44 z)*(formula47 z)
private theorem node47Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node47Cross : polynomialCheck
    (((⟨#[0,0,0,-32]⟩ : QPoly).mul (⟨#[-4,2,0,1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,128,-64,0,-32]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node47 : RationalCode parameterInterval formula48 :=
  (node43.mul node46)
  |>.recode ⟨#[0,0,0,128,-64,0,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node47Denominator node47Cross

/-- Article: exact source arithmetic node 49. -/
private def formula49 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula7 z)
private theorem node48Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node48Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node48 : RationalCode parameterInterval formula49 :=
  ((RationalCode.constant parameterInterval (-2)).add node6)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node48Denominator node48Cross

/-- Article: exact source arithmetic node 50. -/
private def formula50 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(id z)
private theorem node49Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node49Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node49 : RationalCode parameterInterval formula50 :=
  ((RationalCode.constant parameterInterval (-2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-2]⟩ ⟨#[1]⟩ node49Denominator node49Cross

/-- Article: exact source arithmetic node 51. -/
private def formula51 (z : ℝ) : ℝ := (formula49 z)+(formula50 z)
private theorem node50Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node50Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,-2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node50 : RationalCode parameterInterval formula51 :=
  (node48.add node49)
  |>.recode ⟨#[-2,-2,1]⟩ ⟨#[1]⟩ node50Denominator node50Cross

/-- Article: exact source arithmetic node 52. -/
private def formula52 (z : ℝ) : ℝ := (formula48 z)*(formula51 z)
private theorem node51Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node51Cross : polynomialCheck
    (((⟨#[0,0,0,128,-64,0,-32]⟩ : QPoly).mul (⟨#[-2,-2,1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,-256,-128,256,0,64,-32]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node51 : RationalCode parameterInterval formula52 :=
  (node47.mul node50)
  |>.recode ⟨#[0,0,0,-256,-128,256,0,64,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node51Denominator node51Cross

/-- Article: exact source arithmetic node 53. -/
private def formula53 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula7 z)
private theorem node52Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node52Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node52 : RationalCode parameterInterval formula53 :=
  ((RationalCode.constant parameterInterval (-2)).add node6)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node52Denominator node52Cross

/-- Article: exact source arithmetic node 54. -/
private def formula54 (z : ℝ) : ℝ := (formula53 z)+(formula46 z)
private theorem node53Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node53Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node53 : RationalCode parameterInterval formula54 :=
  (node52.add node45)
  |>.recode ⟨#[-2,2,1]⟩ ⟨#[1]⟩ node53Denominator node53Cross

/-- Article: exact source arithmetic node 55. -/
private def formula55 (z : ℝ) : ℝ := (formula52 z)*(formula54 z)
private theorem node54Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node54Cross : polynomialCheck
    (((⟨#[0,0,0,-256,-128,256,0,64,-32]⟩ : QPoly).mul (⟨#[-2,2,1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,512,-256,-1024,384,128,192,0,-32]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node54 : RationalCode parameterInterval formula55 :=
  (node51.mul node53)
  |>.recode ⟨#[0,0,0,512,-256,-1024,384,128,192,0,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node54Denominator node54Cross

/-- Article: exact source arithmetic node 56. -/
private def formula56 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula5 z)
private theorem node55Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node55Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node55 : RationalCode parameterInterval formula56 :=
  ((RationalCode.constant parameterInterval (-2)).add node4)
  |>.recode ⟨#[-2,0,0,1]⟩ ⟨#[1]⟩ node55Denominator node55Cross

/-- Article: exact source arithmetic node 57. -/
private def formula57 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node56Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node56Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node56 : RationalCode parameterInterval formula57 :=
  ((RationalCode.constant parameterInterval (-1)).mul node6)
  |>.recode ⟨#[0,0,-1]⟩ ⟨#[1]⟩ node56Denominator node56Cross

/-- Article: exact source arithmetic node 58. -/
private def formula58 (z : ℝ) : ℝ := (formula56 z)+(formula57 z)
private theorem node57Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node57Cross : polynomialCheck
    ((((⟨#[-2,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,-1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,-1,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node57 : RationalCode parameterInterval formula58 :=
  (node55.add node56)
  |>.recode ⟨#[-2,0,-1,1]⟩ ⟨#[1]⟩ node57Denominator node57Cross

/-- Article: exact source arithmetic node 59. -/
private def formula59 (z : ℝ) : ℝ := (formula55 z)*(formula58 z)
private theorem node58Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node58Cross : polynomialCheck
    (((⟨#[0,0,0,512,-256,-1024,384,128,192,0,-32]⟩ : QPoly).mul (⟨#[-2,0,-1,1]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,-1024,512,1536,0,512,-1792,256,0,192,32,-32]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node58 : RationalCode parameterInterval formula59 :=
  (node54.mul node57)
  |>.recode ⟨#[0,0,0,-1024,512,1536,0,512,-1792,256,0,192,32,-32]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node58Denominator node58Cross

/-- Article: exact source arithmetic node 60. -/
private def formula60 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2240 : ℚ) : ℝ)) z)*(formula17 z)
private theorem node59Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node59Cross : polynomialCheck
    (((⟨#[-2240]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node59 : RationalCode parameterInterval formula60 :=
  ((RationalCode.constant parameterInterval (-2240)).mul node16)
  |>.recode ⟨#[0,0,0,0,0,-2240]⟩ ⟨#[1]⟩ node59Denominator node59Cross

/-- Article: exact source arithmetic node 61. -/
private def formula61 (z : ℝ) : ℝ := ((fun _ : ℝ => ((160 : ℚ) : ℝ)) z)+(formula60 z)
private theorem node60Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node60Cross : polynomialCheck
    ((((⟨#[160]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,0,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node60 : RationalCode parameterInterval formula61 :=
  ((RationalCode.constant parameterInterval (160)).add node59)
  |>.recode ⟨#[160,0,0,0,0,-2240]⟩ ⟨#[1]⟩ node60Denominator node60Cross

/-- Article: exact source arithmetic node 62. -/
private def formula62 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2048 : ℚ) : ℝ)) z)*(formula5 z)
private theorem node61Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node61Cross : polynomialCheck
    (((⟨#[-2048]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-2048]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node61 : RationalCode parameterInterval formula62 :=
  ((RationalCode.constant parameterInterval (-2048)).mul node4)
  |>.recode ⟨#[0,0,0,-2048]⟩ ⟨#[1]⟩ node61Denominator node61Cross

/-- Article: exact source arithmetic node 63. -/
private def formula63 (z : ℝ) : ℝ := (formula61 z)+(formula62 z)
private theorem node62Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node62Cross : polynomialCheck
    ((((⟨#[160,0,0,0,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-2048]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-2048,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node62 : RationalCode parameterInterval formula63 :=
  (node60.add node61)
  |>.recode ⟨#[160,0,0,-2048,0,-2240]⟩ ⟨#[1]⟩ node62Denominator node62Cross

/-- Article: exact source arithmetic node 64. -/
private def formula64 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-512 : ℚ) : ℝ)) z)*(formula22 z)
private theorem node63Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node63Cross : polynomialCheck
    (((⟨#[-512]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node63 : RationalCode parameterInterval formula64 :=
  ((RationalCode.constant parameterInterval (-512)).mul node21)
  |>.recode ⟨#[0,0,0,0,0,0,0,-512]⟩ ⟨#[1]⟩ node63Denominator node63Cross

/-- Article: exact source arithmetic node 65. -/
private def formula65 (z : ℝ) : ℝ := (formula63 z)+(formula64 z)
private theorem node64Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node64Cross : polynomialCheck
    ((((⟨#[160,0,0,-2048,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node64 : RationalCode parameterInterval formula65 :=
  (node62.add node63)
  |>.recode ⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ ⟨#[1]⟩ node64Denominator node64Cross

/-- Article: exact source arithmetic node 66. -/
private def formula66 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-384 : ℚ) : ℝ)) z)*(id z)
private theorem node65Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node65Cross : polynomialCheck
    (((⟨#[-384]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-384]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node65 : RationalCode parameterInterval formula66 :=
  ((RationalCode.constant parameterInterval (-384)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-384]⟩ ⟨#[1]⟩ node65Denominator node65Cross

/-- Article: exact source arithmetic node 67. -/
private def formula67 (z : ℝ) : ℝ := (formula65 z)+(formula66 z)
private theorem node66Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node66Cross : polynomialCheck
    ((((⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-384]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node66 : RationalCode parameterInterval formula67 :=
  (node64.add node65)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ ⟨#[1]⟩ node66Denominator node66Cross

/-- Article: exact source arithmetic node 68. -/
private def formula68 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-24 : ℚ) : ℝ)) z)*(formula25 z)
private theorem node67Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node67Cross : polynomialCheck
    (((⟨#[-24]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node67 : RationalCode parameterInterval formula68 :=
  ((RationalCode.constant parameterInterval (-24)).mul node24)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ ⟨#[1]⟩ node67Denominator node67Cross

/-- Article: exact source arithmetic node 69. -/
private def formula69 (z : ℝ) : ℝ := (formula67 z)+(formula68 z)
private theorem node68Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node68Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node68 : RationalCode parameterInterval formula69 :=
  (node66.add node67)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ ⟨#[1]⟩ node68Denominator node68Cross

/-- Article: exact source arithmetic node 70. -/
private def formula70 (z : ℝ) : ℝ := (formula69 z)+(formula29 z)
private theorem node69Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node69Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node69 : RationalCode parameterInterval formula70 :=
  (node68.add node28)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ ⟨#[1]⟩ node69Denominator node69Cross

/-- Article: exact source arithmetic node 71. -/
private def formula71 (z : ℝ) : ℝ := ((fun _ : ℝ => ((74 : ℚ) : ℝ)) z)*(formula31 z)
private theorem node70Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node70Cross : polynomialCheck
    (((⟨#[74]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,74]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node70 : RationalCode parameterInterval formula71 :=
  ((RationalCode.constant parameterInterval (74)).mul node30)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,74]⟩ ⟨#[1]⟩ node70Denominator node70Cross

/-- Article: exact source arithmetic node 72. -/
private def formula72 (z : ℝ) : ℝ := (formula70 z)+(formula71 z)
private theorem node71Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node71Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,74]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node71 : RationalCode parameterInterval formula72 :=
  (node69.add node70)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ ⟨#[1]⟩ node71Denominator node71Cross

/-- Article: exact source arithmetic node 73. -/
private def formula73 (z : ℝ) : ℝ := ((fun _ : ℝ => ((592 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node72Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node72Cross : polynomialCheck
    (((⟨#[592]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,592]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node72 : RationalCode parameterInterval formula73 :=
  ((RationalCode.constant parameterInterval (592)).mul node6)
  |>.recode ⟨#[0,0,592]⟩ ⟨#[1]⟩ node72Denominator node72Cross

/-- Article: exact source arithmetic node 74. -/
private def formula74 (z : ℝ) : ℝ := (formula72 z)+(formula73 z)
private theorem node73Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node73Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,592]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node73 : RationalCode parameterInterval formula74 :=
  (node71.add node72)
  |>.recode ⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ ⟨#[1]⟩ node73Denominator node73Cross

/-- Article: exact source arithmetic node 75. -/
private def formula75 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1448 : ℚ) : ℝ)) z)*(formula34 z)
private theorem node74Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node74Cross : polynomialCheck
    (((⟨#[1448]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,1448]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node74 : RationalCode parameterInterval formula75 :=
  ((RationalCode.constant parameterInterval (1448)).mul node33)
  |>.recode ⟨#[0,0,0,0,0,0,1448]⟩ ⟨#[1]⟩ node74Denominator node74Cross

/-- Article: exact source arithmetic node 76. -/
private def formula76 (z : ℝ) : ℝ := (formula74 z)+(formula75 z)
private theorem node75Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node75Cross : polynomialCheck
    ((((⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,1448]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node75 : RationalCode parameterInterval formula76 :=
  (node73.add node74)
  |>.recode ⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ ⟨#[1]⟩ node75Denominator node75Cross

/-- Article: exact source arithmetic node 77. -/
private def formula77 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2896 : ℚ) : ℝ)) z)*(formula39 z)
private theorem node76Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node76Cross : polynomialCheck
    (((⟨#[2896]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,2896]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node76 : RationalCode parameterInterval formula77 :=
  ((RationalCode.constant parameterInterval (2896)).mul node38)
  |>.recode ⟨#[0,0,0,0,2896]⟩ ⟨#[1]⟩ node76Denominator node76Cross

/-- Article: exact source arithmetic node 78. -/
private def formula78 (z : ℝ) : ℝ := (formula76 z)+(formula77 z)
private theorem node77Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node77Cross : polynomialCheck
    ((((⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,2896]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node77 : RationalCode parameterInterval formula78 :=
  (node75.add node76)
  |>.recode ⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ ⟨#[1]⟩ node77Denominator node77Cross

/-- Article: exact source arithmetic node 79. -/
private def formula79 (z : ℝ) : ℝ := (formula59 z)*(formula78 z)
private theorem node78Denominator : ∀ z∈parameterInterval, aeval z (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node78Cross : polynomialCheck
    (((⟨#[0,0,0,-1024,512,1536,0,512,-1792,256,0,192,32,-32]⟩ : QPoly).mul (⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : QPoly) : QPoly).mul ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩)
    ((⟨#[0,0,0,-163840,475136,-557056,1810432,-3022848,147456,2850816,-4382720,7221248,-7653376,5689344,-3826688,1805312,-547840,178176,4608,-47232,14144,-2176,928,-160]⟩ : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node78 : RationalCode parameterInterval formula79 :=
  (node58.mul node77)
  |>.recode ⟨#[0,0,0,-163840,475136,-557056,1810432,-3022848,147456,2850816,-4382720,7221248,-7653376,5689344,-3826688,1805312,-547840,178176,4608,-47232,14144,-2176,928,-160]⟩ ⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ node78Denominator node78Cross

/-- Article: exact source arithmetic node 80. -/
private def formula80 (z : ℝ) : ℝ := (formula4 z)+(formula79 z)
private theorem node79Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node79Cross : polynomialCheck
    ((((⟨#[0,0,0,163840,-475136,557056,-1810432,3022848,-147456,-2850816,4382720,-7221248,7653376,-5689344,3826688,-1805312,547840,-178176,-4608,47232,-14144,2176,-928,160]⟩ : QPoly).mul (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly)).add ((⟨#[0,0,0,-163840,475136,-557056,1810432,-3022848,147456,2850816,-4382720,7221248,-7653376,5689344,-3826688,1805312,-547840,178176,4608,-47232,14144,-2176,928,-160]⟩ : QPoly).mul (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly).mul (⟨#[204800,-1802240,7344128,-18186240,31412224,-42319872,47687680,-43606016,29466112,-12470272,-2091264,12038144,-14477824,11581440,-7238912,3009536,-261408,-779392,920816,-681344,372560,-165312,61352,-17760,3586,-440,25]⟩ : QPoly)))=true := by kernel_decide
private def node79 : RationalCode parameterInterval formula80 :=
  (node3.add node78)
  |>.recode QPoly.zero ⟨#[1]⟩ node79Denominator node79Cross

/-- Article: exact coefficient representation of the independently specified mean_root_identity source. -/
def mean_root_identityCode : RationalCode parameterInterval (fun z : ℝ => atomPolynomial z (meanCosine z)-endpointCubic z*meanRootFactor z) where
  numerator := node79.numerator
  denominator := node79.denominator
  denominator_ne := node79.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => atomPolynomial z (meanCosine z)-endpointCubic z*meanRootFactor z) z=formula80 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,atomPolynomial,endpointCubic,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node79.exact z hz)

/-- Article: exact actual-source identity mean_root_identity. -/
theorem mean_root_identity {z : ℝ} (hz : z∈parameterInterval) : (atomPolynomial z (meanCosine z)-endpointCubic z*meanRootFactor z)=0 :=
  mean_root_identityCode.eq_zero (by kernel_decide) hz

/-- Article: exact source arithmetic node 81. -/
private def formula81 (z : ℝ) : ℝ := (G z)^3
private theorem node80Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node80Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 3 : QPoly).mul ⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩)
    ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 3))=true := by kernel_decide
private def node80 : RationalCode parameterInterval formula81 :=
  (GCode.pow 3)
  |>.recode ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ ⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ node80Denominator node80Cross

/-- Article: exact source arithmetic node 82. -/
private def formula82 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(formula81 z)
private theorem node81Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node81Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly)))=true := by kernel_decide
private def node81 : RationalCode parameterInterval formula82 :=
  ((RationalCode.constant parameterInterval (-4)).mul node80)
  |>.recode ⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node81Denominator node81Cross

/-- Article: exact source arithmetic node 83. -/
private def formula83 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(G z)
private theorem node82Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node82Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node82 : RationalCode parameterInterval formula83 :=
  ((RationalCode.constant parameterInterval (2)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-8,0,4]⟩ node82Denominator node82Cross

/-- Article: exact source arithmetic node 84. -/
private def formula84 (z : ℝ) : ℝ := (formula82 z)+(formula83 z)
private theorem node83Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  node81Denominator
private theorem node83Cross : polynomialCheck
    ((((⟨#[-64,0,0,0,-48,0,0,0,-12,0,0,0,-1]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)).add ((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[-64,0,512,0,-560,0,256,0,-140,0,32,0,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node83 : RationalCode parameterInterval formula84 :=
  (node81.add node82)
  |>.recode ⟨#[-64,0,512,0,-560,0,256,0,-140,0,32,0,-1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node83Denominator node83Cross

/-- Article: exact source arithmetic node 85. -/
private def formula85 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(G z)
private theorem node84Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node84Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node84 : RationalCode parameterInterval formula85 :=
  ((RationalCode.constant parameterInterval (-1)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-16,0,8]⟩ node84Denominator node84Cross

/-- Article: exact source arithmetic node 86. -/
private def formula86 (z : ℝ) : ℝ := (formula85 z)*(W z)
private theorem node85Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node85Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩)
    ((⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node85 : RationalCode parameterInterval formula86 :=
  (node84.mul WCode)
  |>.recode ⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ ⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ node85Denominator node85Cross

/-- Article: exact source arithmetic node 87. -/
private def formula87 (z : ℝ) : ℝ := (formula84 z)+(formula86 z)
private theorem node86Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-16384,32768,0,-32768,8192,8192,2048,0,-1024,-2048,-1024,2048,0,-512,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node86Cross : polynomialCheck
    ((((⟨#[-64,0,512,0,-560,0,256,0,-140,0,32,0,-1]⟩ : QPoly).mul (⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly)).add ((⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-16384,32768,0,-32768,8192,8192,2048,0,-1024,-2048,-1024,2048,0,-512,128]⟩)
    ((⟨#[-1024,2048,3072,-7168,-2304,6144,3072,-1024,-5504,1792,1152,896,-1376,-128,192,192,-36,-56,12,4,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).mul (⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly)))=true := by kernel_decide
private def node86 : RationalCode parameterInterval formula87 :=
  (node83.add node85)
  |>.recode ⟨#[-1024,2048,3072,-7168,-2304,6144,3072,-1024,-5504,1792,1152,896,-1376,-128,192,192,-36,-56,12,4,-1]⟩ ⟨#[0,0,0,-16384,32768,0,-32768,8192,8192,2048,0,-1024,-2048,-1024,2048,0,-512,128]⟩ node86Denominator node86Cross

/-- Article: exact source arithmetic node 88. -/
private def formula88 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(W z)
private theorem node87Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node87Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩)
    ((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node87 : RationalCode parameterInterval formula88 :=
  ((RationalCode.constant parameterInterval (-1)).mul WCode)
  |>.recode ⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ node87Denominator node87Cross

/-- Article: exact source arithmetic node 89. -/
private def formula89 (z : ℝ) : ℝ := (formula88 z)*(u z)
private theorem node88Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node88Cross : polynomialCheck
    (((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩)
    ((⟨#[-448,1920,-3968,5056,-4432,3008,-1984,1504,-1108,632,-248,60,-7]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node88 : RationalCode parameterInterval formula89 :=
  (node87.mul uCode)
  |>.recode ⟨#[-448,1920,-3968,5056,-4432,3008,-1984,1504,-1108,632,-248,60,-7]⟩ ⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ node88Denominator node88Cross

/-- Article: exact source arithmetic node 90. -/
private def formula90 (z : ℝ) : ℝ := (formula87 z)+(formula89 z)
private theorem node89Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node89Cross : polynomialCheck
    ((((⟨#[-1024,2048,3072,-7168,-2304,6144,3072,-1024,-5504,1792,1152,896,-1376,-128,192,192,-36,-56,12,4,-1]⟩ : QPoly).mul (⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ : QPoly)).add ((⟨#[-448,1920,-3968,5056,-4432,3008,-1984,1504,-1108,632,-248,60,-7]⟩ : QPoly).mul (⟨#[0,0,0,-16384,32768,0,-32768,8192,8192,2048,0,-1024,-2048,-1024,2048,0,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩)
    ((⟨#[-2048,4096,5120,-40960,121344,-220160,204544,-32768,-108288,95744,-18560,-11264,-9280,23936,-13536,-2048,6392,-3440,948,-160,10,4,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-16384,32768,0,-32768,8192,8192,2048,0,-1024,-2048,-1024,2048,0,-512,128]⟩ : QPoly).mul (⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node89 : RationalCode parameterInterval formula90 :=
  (node86.add node88)
  |>.recode ⟨#[-2048,4096,5120,-40960,121344,-220160,204544,-32768,-108288,95744,-18560,-11264,-9280,23936,-13536,-2048,6392,-3440,948,-160,10,4,-1]⟩ ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ node89Denominator node89Cross

/-- Article: exact source arithmetic node 91. -/
private def formula91 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(G z)
private theorem node90Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node82Denominator
private theorem node90Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node90 : RationalCode parameterInterval formula91 :=
  ((RationalCode.constant parameterInterval (-2)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-8,0,4]⟩ node90Denominator node90Cross

/-- Article: exact source arithmetic node 92. -/
private def formula92 (z : ℝ) : ℝ := (atomB z)^2
private theorem node91Denominator : ∀ z∈parameterInterval, aeval z (⟨#[64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node91Cross : polynomialCheck
    ((polynomialPower ⟨#[0,-24,40,-32,20,-6]⟩ 2 : QPoly).mul ⟨#[64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩)
    ((⟨#[0,0,576,-1920,3136,-3520,2912,-1760,784,-240,36]⟩ : QPoly).mul (polynomialPower ⟨#[8,0,-4,0,-2,0,1]⟩ 2))=true := by kernel_decide
private def node91 : RationalCode parameterInterval formula92 :=
  (atomBCode.pow 2)
  |>.recode ⟨#[0,0,576,-1920,3136,-3520,2912,-1760,784,-240,36]⟩ ⟨#[64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ node91Denominator node91Cross

/-- Article: exact source arithmetic node 93. -/
private def formula93 (z : ℝ) : ℝ := (formula91 z)*(formula92 z)
private theorem node92Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-128,0,192,0,-32,0,-80,0,40,0,4,0,-6,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node92Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[0,0,576,-1920,3136,-3520,2912,-1760,784,-240,36]⟩ : QPoly) : QPoly).mul ⟨#[-128,0,192,0,-32,0,-80,0,40,0,4,0,-6,0,1]⟩)
    ((⟨#[0,-576,1920,-3136,3520,-3056,2240,-1568,1120,-764,440,-196,60,-9]⟩ : QPoly).mul ((⟨#[0,-8,0,4]⟩ : QPoly).mul (⟨#[64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node92 : RationalCode parameterInterval formula93 :=
  (node90.mul node91)
  |>.recode ⟨#[0,-576,1920,-3136,3520,-3056,2240,-1568,1120,-764,440,-196,60,-9]⟩ ⟨#[-128,0,192,0,-32,0,-80,0,40,0,4,0,-6,0,1]⟩ node92Denominator node92Cross

/-- Article: exact source arithmetic node 94. -/
private def formula94 (z : ℝ) : ℝ := (formula90 z)+(formula93 z)
private theorem node93Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node93Cross : polynomialCheck
    ((((⟨#[-2048,4096,5120,-40960,121344,-220160,204544,-32768,-108288,95744,-18560,-11264,-9280,23936,-13536,-2048,6392,-3440,948,-160,10,4,-1]⟩ : QPoly).mul (⟨#[-128,0,192,0,-32,0,-80,0,40,0,4,0,-6,0,1]⟩ : QPoly)).add ((⟨#[0,-576,1920,-3136,3520,-3056,2240,-1568,1120,-764,440,-196,60,-9]⟩ : QPoly).mul (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩)
    ((⟨#[-8192,16384,28672,-180224,-126976,2433024,-7395328,12701696,-14974464,13728768,-11421440,9844736,-8521216,6560768,-4260608,2461184,-1427680,858048,-467952,198464,-57776,9504,-248,-176,14,4,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).mul (⟨#[-128,0,192,0,-32,0,-80,0,40,0,4,0,-6,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node93 : RationalCode parameterInterval formula94 :=
  (node89.add node92)
  |>.recode ⟨#[-8192,16384,28672,-180224,-126976,2433024,-7395328,12701696,-14974464,13728768,-11421440,9844736,-8521216,6560768,-4260608,2461184,-1427680,858048,-467952,198464,-57776,9504,-248,-176,14,4,-1]⟩ ⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ node93Denominator node93Cross

/-- Article: exact source arithmetic node 95. -/
private def formula95 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(G z)
private theorem node94Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node82Denominator
private theorem node94Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node94 : RationalCode parameterInterval formula95 :=
  ((RationalCode.constant parameterInterval (-2)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-8,0,4]⟩ node94Denominator node94Cross

/-- Article: exact source arithmetic node 96. -/
private def formula96 (z : ℝ) : ℝ := (u z)^2
private theorem node95Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node95Cross : polynomialCheck
    ((polynomialPower ⟨#[4,-8,8,-4,1]⟩ 2 : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly).mul (polynomialPower ⟨#[-4,0,0,0,1]⟩ 2))=true := by kernel_decide
private def node95 : RationalCode parameterInterval formula96 :=
  (uCode.pow 2)
  |>.recode ⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node95Denominator node95Cross

/-- Article: exact source arithmetic node 97. -/
private def formula97 (z : ℝ) : ℝ := (formula95 z)*(formula96 z)
private theorem node96Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node96Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩)
    ((⟨#[-64,256,-512,640,-560,384,-256,192,-140,80,-32,8,-1]⟩ : QPoly).mul ((⟨#[0,-8,0,4]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node96 : RationalCode parameterInterval formula97 :=
  (node94.mul node95)
  |>.recode ⟨#[-64,256,-512,640,-560,384,-256,192,-140,80,-32,8,-1]⟩ ⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ node96Denominator node96Cross

/-- Article: exact source arithmetic node 98. -/
private def formula98 (z : ℝ) : ℝ := (formula94 z)+(formula97 z)
private theorem node97Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node93Denominator
private theorem node97Cross : polynomialCheck
    ((((⟨#[-8192,16384,28672,-180224,-126976,2433024,-7395328,12701696,-14974464,13728768,-11421440,9844736,-8521216,6560768,-4260608,2461184,-1427680,858048,-467952,198464,-57776,9504,-248,-176,14,4,-1]⟩ : QPoly).mul (⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ : QPoly)).add ((⟨#[-64,256,-512,640,-560,384,-256,192,-140,80,-32,8,-1]⟩ : QPoly).mul (⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩)
    ((⟨#[-8192,16384,-36864,212992,-1175552,4005888,-8738816,13193216,-14835200,13597696,-11486976,9828352,-8287744,6298624,-4143872,2457088,-1435872,849856,-463600,206144,-68272,15648,-2296,208,-18,4,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly).mul (⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node97 : RationalCode parameterInterval formula98 :=
  (node93.add node96)
  |>.recode ⟨#[-8192,16384,-36864,212992,-1175552,4005888,-8738816,13193216,-14835200,13597696,-11486976,9828352,-8287744,6298624,-4143872,2457088,-1435872,849856,-463600,206144,-68272,15648,-2296,208,-18,4,-1]⟩ ⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ node97Denominator node97Cross

/-- Article: exact source arithmetic node 99. -/
private def formula99 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(u z)
private theorem node98Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node98Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-4,0,0,0,1]⟩)
    ((⟨#[16,-32,32,-16,4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node98 : RationalCode parameterInterval formula99 :=
  ((RationalCode.constant parameterInterval (4)).mul uCode)
  |>.recode ⟨#[16,-32,32,-16,4]⟩ ⟨#[-4,0,0,0,1]⟩ node98Denominator node98Cross

/-- Article: exact source arithmetic node 100. -/
private def formula100 (z : ℝ) : ℝ := (G z)^2
private theorem node99Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node99Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 2 : QPoly).mul ⟨#[0,0,256,0,-256,0,64]⟩)
    ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 2))=true := by kernel_decide
private def node99 : RationalCode parameterInterval formula100 :=
  (GCode.pow 2)
  |>.recode ⟨#[16,0,0,0,8,0,0,0,1]⟩ ⟨#[0,0,256,0,-256,0,64]⟩ node99Denominator node99Cross

/-- Article: exact source arithmetic node 101. -/
private def formula101 (z : ℝ) : ℝ := (formula99 z)*(formula100 z)
private theorem node100Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node100Cross : polynomialCheck
    (((⟨#[16,-32,32,-16,4]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩)
    ((⟨#[64,-128,128,-64,48,-64,64,-32,12,-8,8,-4,1]⟩ : QPoly).mul ((⟨#[-4,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node100 : RationalCode parameterInterval formula101 :=
  (node98.mul node99)
  |>.recode ⟨#[64,-128,128,-64,48,-64,64,-32,12,-8,8,-4,1]⟩ ⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ node100Denominator node100Cross

/-- Article: exact source arithmetic node 102. -/
private def formula102 (z : ℝ) : ℝ := (formula98 z)+(formula101 z)
private theorem node101Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node93Denominator
private theorem node101Cross : polynomialCheck
    ((((⟨#[-8192,16384,-36864,212992,-1175552,4005888,-8738816,13193216,-14835200,13597696,-11486976,9828352,-8287744,6298624,-4143872,2457088,-1435872,849856,-463600,206144,-68272,15648,-2296,208,-18,4,-1]⟩ : QPoly).mul (⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ : QPoly)).add ((⟨#[64,-128,128,-64,48,-64,64,-32,12,-8,8,-4,1]⟩ : QPoly).mul (⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩)
    ((⟨#[-8192,49152,-167936,425984,-1339392,4055040,-8755200,13246464,-14884352,13595648,-11454208,9801728,-8275456,6292480,-4137728,2450432,-1431776,849728,-465136,206976,-68400,15840,-2616,416,-82,12,-1]⟩ : QPoly).mul ((⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly).mul (⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node101 : RationalCode parameterInterval formula102 :=
  (node97.add node100)
  |>.recode ⟨#[-8192,49152,-167936,425984,-1339392,4055040,-8755200,13246464,-14884352,13595648,-11454208,9801728,-8275456,6292480,-4137728,2450432,-1431776,849728,-465136,206976,-68400,15840,-2616,416,-82,12,-1]⟩ ⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ node101Denominator node101Cross

/-- Article: exact source arithmetic node 103. -/
private def formula103 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula81 z)
private theorem node102Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  node81Denominator
private theorem node102Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly)))=true := by kernel_decide
private def node102 : RationalCode parameterInterval formula103 :=
  ((RationalCode.constant parameterInterval (4)).mul node80)
  |>.recode ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node102Denominator node102Cross

/-- Article: exact source arithmetic node 104. -/
private def formula104 (z : ℝ) : ℝ := (formula103 z)*(formula96 z)
private theorem node103Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node103Cross : polynomialCheck
    (((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩)
    ((⟨#[1024,-4096,8192,-10240,9472,-8192,8192,-8192,6784,-4608,3072,-2304,1696,-1024,512,-256,148,-80,32,-8,1]⟩ : QPoly).mul ((⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node103 : RationalCode parameterInterval formula104 :=
  (node102.mul node95)
  |>.recode ⟨#[1024,-4096,8192,-10240,9472,-8192,8192,-8192,6784,-4608,3072,-2304,1696,-1024,512,-256,148,-80,32,-8,1]⟩ ⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ node103Denominator node103Cross

/-- Article: exact source arithmetic node 105. -/
private def formula105 (z : ℝ) : ℝ := (formula102 z)+(formula104 z)
private theorem node104Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-65536,131072,32768,-196608,49152,65536,-16384,32768,-16384,-32768,0,16384,4096,-4096,1024,-2048,-768,1536,-128,-256,64]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node104Cross : polynomialCheck
    ((((⟨#[-8192,49152,-167936,425984,-1339392,4055040,-8755200,13246464,-14884352,13595648,-11454208,9801728,-8275456,6292480,-4137728,2450432,-1431776,849728,-465136,206976,-68400,15840,-2616,416,-82,12,-1]⟩ : QPoly).mul (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly)).add ((⟨#[1024,-4096,8192,-10240,9472,-8192,8192,-8192,6784,-4608,3072,-2304,1696,-1024,512,-256,148,-80,32,-8,1]⟩ : QPoly).mul (⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,-65536,131072,32768,-196608,49152,65536,-16384,32768,-16384,-32768,0,16384,4096,-4096,1024,-2048,-768,1536,-128,-256,64]⟩)
    ((⟨#[-14336,90112,-515072,1867776,-4216320,6453248,-7273216,6651904,-5613312,4811776,-4066176,3092480,-2033088,1202944,-701664,415744,-227288,100832,-32940,7296,-1006,88,-7]⟩ : QPoly).mul ((⟨#[0,0,0,-131072,262144,65536,-393216,98304,131072,-32768,65536,-32768,-65536,0,32768,8192,-8192,2048,-4096,-1536,3072,-256,-512,128]⟩ : QPoly).mul (⟨#[0,0,0,-16384,0,24576,0,-4096,0,-10240,0,5120,0,512,0,-768,0,128]⟩ : QPoly)))=true := by kernel_decide
private def node104 : RationalCode parameterInterval formula105 :=
  (node101.add node103)
  |>.recode ⟨#[-14336,90112,-515072,1867776,-4216320,6453248,-7273216,6651904,-5613312,4811776,-4066176,3092480,-2033088,1202944,-701664,415744,-227288,100832,-32940,7296,-1006,88,-7]⟩ ⟨#[0,-65536,131072,32768,-196608,49152,65536,-16384,32768,-16384,-32768,0,16384,4096,-4096,1024,-2048,-768,1536,-128,-256,64]⟩ node104Denominator node104Cross

/-- Article: exact source arithmetic node 106. -/
private def formula106 (z : ℝ) : ℝ := (G z)*(W z)
private theorem node105Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly).toPoly≠0 :=
  node85Denominator
private theorem node105Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩)
    ((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node105 : RationalCode parameterInterval formula106 :=
  (GCode.mul WCode)
  |>.recode ⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ ⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ node105Denominator node105Cross

/-- Article: exact source arithmetic node 107. -/
private def formula107 (z : ℝ) : ℝ := (formula106 z)*(formula96 z)
private theorem node106Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-32768,65536,-32768,0,8192,-32768,20480,0,6144,0,-3072,0,-2560,2048,-256,0,256,-256,64]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node106Cross : polynomialCheck
    (((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-32768,65536,-32768,0,8192,-32768,20480,0,6144,0,-3072,0,-2560,2048,-256,0,256,-256,64]⟩)
    ((⟨#[7168,-45056,139264,-276480,393984,-434176,401408,-344064,293248,-243200,183296,-121600,73312,-43008,25088,-13568,6156,-2160,544,-88,7]⟩ : QPoly).mul ((⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node106 : RationalCode parameterInterval formula107 :=
  (node105.mul node95)
  |>.recode ⟨#[7168,-45056,139264,-276480,393984,-434176,401408,-344064,293248,-243200,183296,-121600,73312,-43008,25088,-13568,6156,-2160,544,-88,7]⟩ ⟨#[0,-32768,65536,-32768,0,8192,-32768,20480,0,6144,0,-3072,0,-2560,2048,-256,0,256,-256,64]⟩ node106Denominator node106Cross

/-- Article: exact source arithmetic node 108. -/
private def formula108 (z : ℝ) : ℝ := (formula105 z)+(formula107 z)
private theorem node107Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node107Cross : polynomialCheck
    ((((⟨#[-14336,90112,-515072,1867776,-4216320,6453248,-7273216,6651904,-5613312,4811776,-4066176,3092480,-2033088,1202944,-701664,415744,-227288,100832,-32940,7296,-1006,88,-7]⟩ : QPoly).mul (⟨#[0,-32768,65536,-32768,0,8192,-32768,20480,0,6144,0,-3072,0,-2560,2048,-256,0,256,-256,64]⟩ : QPoly)).add ((⟨#[7168,-45056,139264,-276480,393984,-434176,401408,-344064,293248,-243200,183296,-121600,73312,-43008,25088,-13568,6156,-2160,544,-88,7]⟩ : QPoly).mul (⟨#[0,-65536,131072,32768,-196608,49152,65536,-16384,32768,-16384,-32768,0,16384,4096,-4096,1024,-2048,-768,1536,-128,-256,64]⟩ : QPoly)) : QPoly).mul ⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩)
    ((⟨#[0,-64512,362496,-990208,1762304,-2324224,2480128,-2317312,2030592,-1723008,1392384,-1034880,696192,-430752,253824,-144832,77504,-36316,13768,-3868,708,-63]⟩ : QPoly).mul ((⟨#[0,-65536,131072,32768,-196608,49152,65536,-16384,32768,-16384,-32768,0,16384,4096,-4096,1024,-2048,-768,1536,-128,-256,64]⟩ : QPoly).mul (⟨#[0,-32768,65536,-32768,0,8192,-32768,20480,0,6144,0,-3072,0,-2560,2048,-256,0,256,-256,64]⟩ : QPoly)))=true := by kernel_decide
private def node107 : RationalCode parameterInterval formula108 :=
  (node104.add node106)
  |>.recode ⟨#[0,-64512,362496,-990208,1762304,-2324224,2480128,-2317312,2030592,-1723008,1392384,-1034880,696192,-430752,253824,-144832,77504,-36316,13768,-3868,708,-63]⟩ ⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ node107Denominator node107Cross

/-- Article: exact source arithmetic node 109. -/
private def formula109 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(G z)
private theorem node108Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node82Denominator
private theorem node108Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node108 : RationalCode parameterInterval formula109 :=
  ((RationalCode.constant parameterInterval (2)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-8,0,4]⟩ node108Denominator node108Cross

/-- Article: exact source arithmetic node 110. -/
private def formula110 (z : ℝ) : ℝ := (formula109 z)*(W z)
private theorem node109Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node109Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩)
    ((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[0,-8,0,4]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node109 : RationalCode parameterInterval formula110 :=
  (node108.mul WCode)
  |>.recode ⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ ⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ node109Denominator node109Cross

/-- Article: exact source arithmetic node 111. -/
private def formula111 (z : ℝ) : ℝ := (formula110 z)*(formula92 z)
private theorem node110Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ : QPoly).toPoly≠0 :=
  node107Denominator
private theorem node110Cross : polynomialCheck
    (((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul (⟨#[0,0,576,-1920,3136,-3520,2912,-1760,784,-240,36]⟩ : QPoly) : QPoly).mul ⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩)
    ((⟨#[0,64512,-362496,990208,-1762304,2324224,-2480128,2317312,-2030592,1723008,-1392384,1034880,-696192,430752,-253824,144832,-77504,36316,-13768,3868,-708,63]⟩ : QPoly).mul ((⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ : QPoly).mul (⟨#[64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node110 : RationalCode parameterInterval formula111 :=
  (node109.mul node91)
  |>.recode ⟨#[0,64512,-362496,990208,-1762304,2324224,-2480128,2317312,-2030592,1723008,-1392384,1034880,-696192,430752,-253824,144832,-77504,36316,-13768,3868,-708,63]⟩ ⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ node110Denominator node110Cross

/-- Article: exact source arithmetic node 112. -/
private def formula112 (z : ℝ) : ℝ := (formula108 z)+(formula111 z)
private theorem node111Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node111Cross : polynomialCheck
    ((((⟨#[0,-64512,362496,-990208,1762304,-2324224,2480128,-2317312,2030592,-1723008,1392384,-1034880,696192,-430752,253824,-144832,77504,-36316,13768,-3868,708,-63]⟩ : QPoly).mul (⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ : QPoly)).add ((⟨#[0,64512,-362496,990208,-1762304,2324224,-2480128,2317312,-2030592,1723008,-1392384,1034880,-696192,430752,-253824,144832,-77504,36316,-13768,3868,-708,63]⟩ : QPoly).mul (⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ : QPoly).mul (⟨#[-16384,32768,0,-32768,16384,-8192,2048,16384,-6144,-4096,-2048,0,1024,1024,768,-1024,-64,128,-128,128,0,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node111 : RationalCode parameterInterval formula112 :=
  (node107.add node110)
  |>.recode QPoly.zero ⟨#[1]⟩ node111Denominator node111Cross

/-- Article: exact source arithmetic node 113. -/
private def formula113 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(formula112 z)
private theorem node112Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node112Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (QPoly.zero : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node112 : RationalCode parameterInterval formula113 :=
  ((RationalCode.constant parameterInterval (2)).mul node111)
  |>.recode QPoly.zero ⟨#[1]⟩ node112Denominator node112Cross

/-- Article: exact coefficient representation of the independently specified double_square_coefficient0 source. -/
def double_square_coefficient0Code : RationalCode parameterInterval (fun z : ℝ => ((-8*((G z))^3)+(4*(G z))+(-4*(G z)*((atomB z))^2)+(-4*(G z)*((u z))^2)+(-2*(G z)*(W z))+(-2*(W z)*(u z))+(8*(u z)*((G z))^2)+(8*((G z))^3*((u z))^2)+(2*(G z)*(W z)*((u z))^2)+(4*(G z)*(W z)*((atomB z))^2))) where
  numerator := node112.numerator
  denominator := node112.denominator
  denominator_ne := node112.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((-8*((G z))^3)+(4*(G z))+(-4*(G z)*((atomB z))^2)+(-4*(G z)*((u z))^2)+(-2*(G z)*(W z))+(-2*(W z)*(u z))+(8*(u z)*((G z))^2)+(8*((G z))^3*((u z))^2)+(2*(G z)*(W z)*((u z))^2)+(4*(G z)*(W z)*((atomB z))^2))) z=formula113 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,atomPolynomial,endpointCubic,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node112.exact z hz)

/-- Article: exact actual-source identity double_square_coefficient0. -/
theorem double_square_coefficient0 {z : ℝ} (hz : z∈parameterInterval) : (((-8*((G z))^3)+(4*(G z))+(-4*(G z)*((atomB z))^2)+(-4*(G z)*((u z))^2)+(-2*(G z)*(W z))+(-2*(W z)*(u z))+(8*(u z)*((G z))^2)+(8*((G z))^3*((u z))^2)+(2*(G z)*(W z)*((u z))^2)+(4*(G z)*(W z)*((atomB z))^2)))=0 :=
  double_square_coefficient0Code.eq_zero (by kernel_decide) hz

/-- Article: exact source arithmetic node 114. -/
private def formula114 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(formula100 z)
private theorem node113Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node113Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[-16,0,0,0,-8,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node113 : RationalCode parameterInterval formula114 :=
  ((RationalCode.constant parameterInterval (-4)).mul node99)
  |>.recode ⟨#[-16,0,0,0,-8,0,0,0,-1]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node113Denominator node113Cross

/-- Article: exact source arithmetic node 115. -/
private def formula115 (z : ℝ) : ℝ := (W z)+(formula114 z)
private theorem node114Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node114Cross : polynomialCheck
    ((((⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)).add ((⟨#[-16,0,0,0,-8,0,0,0,-1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩)
    ((⟨#[-256,512,512,-1792,768,1408,-1664,192,416,96,-416,176,48,-56,8,4,-1]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node114 : RationalCode parameterInterval formula115 :=
  (WCode.add node113)
  |>.recode ⟨#[-256,512,512,-1792,768,1408,-1664,192,416,96,-416,176,48,-56,8,4,-1]⟩ ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ node114Denominator node114Cross

/-- Article: exact source arithmetic node 116. -/
private def formula116 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(W z)
private theorem node115Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  node87Denominator
private theorem node115Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩)
    ((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node115 : RationalCode parameterInterval formula116 :=
  ((RationalCode.constant parameterInterval (-1)).mul WCode)
  |>.recode ⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ node115Denominator node115Cross

/-- Article: exact source arithmetic node 117. -/
private def formula117 (z : ℝ) : ℝ := (formula116 z)*(formula96 z)
private theorem node116Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2048,-4096,3072,-2048,1024,1024,-768,512,-768,256,-192,128,64,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node116Cross : polynomialCheck
    (((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[2048,-4096,3072,-2048,1024,1024,-768,512,-768,256,-192,128,64,-64,48,-32,8]⟩)
    ((⟨#[-1792,11264,-34816,69120,-98048,105728,-91648,68736,-48800,34368,-22912,13216,-6128,2160,-544,88,-7]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node116 : RationalCode parameterInterval formula117 :=
  (node115.mul node95)
  |>.recode ⟨#[-1792,11264,-34816,69120,-98048,105728,-91648,68736,-48800,34368,-22912,13216,-6128,2160,-544,88,-7]⟩ ⟨#[2048,-4096,3072,-2048,1024,1024,-768,512,-768,256,-192,128,64,-64,48,-32,8]⟩ node116Denominator node116Cross

/-- Article: exact source arithmetic node 118. -/
private def formula118 (z : ℝ) : ℝ := (formula115 z)+(formula117 z)
private theorem node117Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,4096,-8192,6144,-4096,2048,2048,-1536,1024,-1536,512,-384,256,128,-128,96,-64,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node117Cross : polynomialCheck
    ((((⟨#[-256,512,512,-1792,768,1408,-1664,192,416,96,-416,176,48,-56,8,4,-1]⟩ : QPoly).mul (⟨#[2048,-4096,3072,-2048,1024,1024,-768,512,-768,256,-192,128,64,-64,48,-32,8]⟩ : QPoly)).add ((⟨#[-1792,11264,-34816,69120,-98048,105728,-91648,68736,-48800,34368,-22912,13216,-6128,2160,-544,88,-7]⟩ : QPoly).mul (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,4096,-8192,6144,-4096,2048,2048,-1536,1024,-1536,512,-384,256,128,-128,96,-64,16]⟩)
    ((⟨#[-1024,2048,-2560,17408,-64768,137216,-199168,216064,-187520,140032,-99264,70016,-46880,27008,-12448,4288,-1012,136,-10,4,-1]⟩ : QPoly).mul ((⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).mul (⟨#[2048,-4096,3072,-2048,1024,1024,-768,512,-768,256,-192,128,64,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node117 : RationalCode parameterInterval formula118 :=
  (node114.add node116)
  |>.recode ⟨#[-1024,2048,-2560,17408,-64768,137216,-199168,216064,-187520,140032,-99264,70016,-46880,27008,-12448,4288,-1012,136,-10,4,-1]⟩ ⟨#[0,0,4096,-8192,6144,-4096,2048,2048,-1536,1024,-1536,512,-384,256,128,-128,96,-64,16]⟩ node117Denominator node117Cross

/-- Article: exact source arithmetic node 119. -/
private def formula119 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula100 z)
private theorem node118Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
private theorem node118Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node118 : RationalCode parameterInterval formula119 :=
  ((RationalCode.constant parameterInterval (4)).mul node99)
  |>.recode ⟨#[16,0,0,0,8,0,0,0,1]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node118Denominator node118Cross

/-- Article: exact source arithmetic node 120. -/
private def formula120 (z : ℝ) : ℝ := (formula119 z)*(formula96 z)
private theorem node119Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1024,0,-1024,0,-256,0,512,0,-64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node119Cross : polynomialCheck
    (((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,1024,0,-1024,0,-256,0,512,0,-64,0,-64,0,16]⟩)
    ((⟨#[256,-1024,2048,-2560,2304,-1792,1536,-1408,1120,-704,384,-224,144,-80,32,-8,1]⟩ : QPoly).mul ((⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node119 : RationalCode parameterInterval formula120 :=
  (node118.mul node95)
  |>.recode ⟨#[256,-1024,2048,-2560,2304,-1792,1536,-1408,1120,-704,384,-224,144,-80,32,-8,1]⟩ ⟨#[0,0,1024,0,-1024,0,-256,0,512,0,-64,0,-64,0,16]⟩ node119Denominator node119Cross

/-- Article: exact source arithmetic node 121. -/
private def formula121 (z : ℝ) : ℝ := (formula118 z)+(formula120 z)
private theorem node120Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node120Cross : polynomialCheck
    ((((⟨#[-1024,2048,-2560,17408,-64768,137216,-199168,216064,-187520,140032,-99264,70016,-46880,27008,-12448,4288,-1012,136,-10,4,-1]⟩ : QPoly).mul (⟨#[0,0,1024,0,-1024,0,-256,0,512,0,-64,0,-64,0,16]⟩ : QPoly)).add ((⟨#[256,-1024,2048,-2560,2304,-1792,1536,-1408,1120,-704,384,-224,144,-80,32,-8,1]⟩ : QPoly).mul (⟨#[0,0,4096,-8192,6144,-4096,2048,2048,-1536,1024,-1536,512,-384,256,128,-128,96,-64,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩)
    ((⟨#[-2048,8192,-9216,-7680,33280,-39936,14592,23040,-43008,37120,-21504,12480,-10752,9280,-5376,1440,456,-624,260,-30,-18,8,-1]⟩ : QPoly).mul ((⟨#[0,0,4096,-8192,6144,-4096,2048,2048,-1536,1024,-1536,512,-384,256,128,-128,96,-64,16]⟩ : QPoly).mul (⟨#[0,0,1024,0,-1024,0,-256,0,512,0,-64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node120 : RationalCode parameterInterval formula121 :=
  (node117.add node119)
  |>.recode ⟨#[-2048,8192,-9216,-7680,33280,-39936,14592,23040,-43008,37120,-21504,12480,-10752,9280,-5376,1440,456,-624,260,-30,-18,8,-1]⟩ ⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ node120Denominator node120Cross

/-- Article: exact source arithmetic node 122. -/
private def formula122 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8 : ℚ) : ℝ)) z)*(G z)
private theorem node121Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node121Cross : polynomialCheck
    (((⟨#[8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node121 : RationalCode parameterInterval formula122 :=
  ((RationalCode.constant parameterInterval (8)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-2,0,1]⟩ node121Denominator node121Cross

/-- Article: exact source arithmetic node 123. -/
private def formula123 (z : ℝ) : ℝ := (formula122 z)*(u z)
private theorem node122Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node122Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[0,8,0,-4,0,-2,0,1]⟩)
    ((⟨#[16,-32,32,-16,8,-8,8,-4,1]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node122 : RationalCode parameterInterval formula123 :=
  (node121.mul uCode)
  |>.recode ⟨#[16,-32,32,-16,8,-8,8,-4,1]⟩ ⟨#[0,8,0,-4,0,-2,0,1]⟩ node122Denominator node122Cross

/-- Article: exact source arithmetic node 124. -/
private def formula124 (z : ℝ) : ℝ := (formula121 z)+(formula123 z)
private theorem node123Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ : QPoly).toPoly≠0 :=
  node120Denominator
private theorem node123Cross : polynomialCheck
    ((((⟨#[-2048,8192,-9216,-7680,33280,-39936,14592,23040,-43008,37120,-21504,12480,-10752,9280,-5376,1440,456,-624,260,-30,-18,8,-1]⟩ : QPoly).mul (⟨#[0,8,0,-4,0,-2,0,1]⟩ : QPoly)).add ((⟨#[16,-32,32,-16,8,-8,8,-4,1]⟩ : QPoly).mul (⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ : QPoly)) : QPoly).mul ⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩)
    ((⟨#[2048,-8192,19456,-36352,51712,-48128,17152,23040,-44544,40192,-25600,16064,-12800,10048,-5568,1440,536,-752,404,-142,38,-8,1]⟩ : QPoly).mul ((⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ : QPoly).mul (⟨#[0,8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node123 : RationalCode parameterInterval formula124 :=
  (node120.add node122)
  |>.recode ⟨#[2048,-8192,19456,-36352,51712,-48128,17152,23040,-44544,40192,-25600,16064,-12800,10048,-5568,1440,536,-752,404,-142,38,-8,1]⟩ ⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ node123Denominator node123Cross

/-- Article: exact source arithmetic node 125. -/
private def formula125 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-8 : ℚ) : ℝ)) z)*(G z)
private theorem node124Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node121Denominator
private theorem node124Cross : polynomialCheck
    (((⟨#[-8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node124 : RationalCode parameterInterval formula125 :=
  ((RationalCode.constant parameterInterval (-8)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-2,0,1]⟩ node124Denominator node124Cross

/-- Article: exact source arithmetic node 126. -/
private def formula126 (z : ℝ) : ℝ := (formula125 z)*(W z)
private theorem node125Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node125Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩)
    ((⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node125 : RationalCode parameterInterval formula126 :=
  (node124.mul WCode)
  |>.recode ⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ node125Denominator node125Cross

/-- Article: exact source arithmetic node 127. -/
private def formula127 (z : ℝ) : ℝ := (formula126 z)*(u z)
private theorem node126Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node126Cross : polynomialCheck
    (((⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩)
    ((⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ : QPoly).mul ((⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node126 : RationalCode parameterInterval formula127 :=
  (node125.mul uCode)
  |>.recode ⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ ⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ node126Denominator node126Cross

/-- Article: exact source arithmetic node 128. -/
private def formula128 (z : ℝ) : ℝ := (formula124 z)+(formula127 z)
private theorem node127Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node127Cross : polynomialCheck
    ((((⟨#[2048,-8192,19456,-36352,51712,-48128,17152,23040,-44544,40192,-25600,16064,-12800,10048,-5568,1440,536,-752,404,-142,38,-8,1]⟩ : QPoly).mul (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly)).add ((⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ : QPoly).mul (⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ : QPoly)) : QPoly).mul ⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩)
    ((⟨#[-6144,28672,-41984,-14336,128512,-177152,76032,92160,-180992,153088,-85120,47872,-42560,38272,-22624,5760,2376,-2768,1004,-56,-82,28,-3]⟩ : QPoly).mul ((⟨#[0,2048,-4096,1024,2048,-1536,2048,-1024,-1024,256,0,384,0,64,-128,-64,64,-24,16,4,-8,2]⟩ : QPoly).mul (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node127 : RationalCode parameterInterval formula128 :=
  (node123.add node126)
  |>.recode ⟨#[-6144,28672,-41984,-14336,128512,-177152,76032,92160,-180992,153088,-85120,47872,-42560,38272,-22624,5760,2376,-2768,1004,-56,-82,28,-3]⟩ ⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ node127Denominator node127Cross

/-- Article: exact source arithmetic node 129. -/
private def formula129 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-8 : ℚ) : ℝ)) z)*(G z)
private theorem node128Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node121Denominator
private theorem node128Cross : polynomialCheck
    (((⟨#[-8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node128 : RationalCode parameterInterval formula129 :=
  ((RationalCode.constant parameterInterval (-8)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-2,0,1]⟩ node128Denominator node128Cross

/-- Article: exact source arithmetic node 130. -/
private def formula130 (z : ℝ) : ℝ := (formula129 z)*(atomA z)
private theorem node129Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,16,0,-8,0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node129Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,16,0,-8,0,-4,0,2]⟩)
    ((⟨#[-32,96,-144,128,-80,48,-40,32,-18,6,-1]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node129 : RationalCode parameterInterval formula130 :=
  (node128.mul atomACode)
  |>.recode ⟨#[-32,96,-144,128,-80,48,-40,32,-18,6,-1]⟩ ⟨#[0,0,16,0,-8,0,-4,0,2]⟩ node129Denominator node129Cross

/-- Article: exact source arithmetic node 131. -/
private def formula131 (z : ℝ) : ℝ := (formula130 z)*(atomB z)
private theorem node130Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node130Cross : polynomialCheck
    (((⟨#[-32,96,-144,128,-80,48,-40,32,-18,6,-1]⟩ : QPoly).mul (⟨#[0,-24,40,-32,20,-6]⟩ : QPoly) : QPoly).mul ⟨#[0,64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩)
    ((⟨#[384,-1792,4160,-6272,6880,-5952,4432,-3136,2216,-1488,860,-392,130,-28,3]⟩ : QPoly).mul ((⟨#[0,0,16,0,-8,0,-4,0,2]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node130 : RationalCode parameterInterval formula131 :=
  (node129.mul atomBCode)
  |>.recode ⟨#[384,-1792,4160,-6272,6880,-5952,4432,-3136,2216,-1488,860,-392,130,-28,3]⟩ ⟨#[0,64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ node130Denominator node130Cross

/-- Article: exact source arithmetic node 132. -/
private def formula132 (z : ℝ) : ℝ := (formula128 z)+(formula131 z)
private theorem node131Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly).toPoly≠0 :=
  node127Denominator
private theorem node131Cross : polynomialCheck
    ((((⟨#[-6144,28672,-41984,-14336,128512,-177152,76032,92160,-180992,153088,-85120,47872,-42560,38272,-22624,5760,2376,-2768,1004,-56,-82,28,-3]⟩ : QPoly).mul (⟨#[0,64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ : QPoly)).add ((⟨#[384,-1792,4160,-6272,6880,-5952,4432,-3136,2216,-1488,860,-392,130,-28,3]⟩ : QPoly).mul (⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩)
    ((⟨#[43008,-299008,1022976,-2275328,3692032,-4690944,4956416,-4634624,4060416,-3424768,2745216,-2032896,1372608,-856192,507552,-289664,154888,-73296,28844,-8888,1998,-292,21]⟩ : QPoly).mul ((⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly).mul (⟨#[0,64,0,-64,0,-16,0,32,0,-4,0,-4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node131 : RationalCode parameterInterval formula132 :=
  (node127.add node130)
  |>.recode ⟨#[43008,-299008,1022976,-2275328,3692032,-4690944,4956416,-4634624,4060416,-3424768,2745216,-2032896,1372608,-856192,507552,-289664,154888,-73296,28844,-8888,1998,-292,21]⟩ ⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ node131Denominator node131Cross

/-- Article: exact source arithmetic node 133. -/
private def formula133 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8 : ℚ) : ℝ)) z)*(G z)
private theorem node132Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node121Denominator
private theorem node132Cross : polynomialCheck
    (((⟨#[8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node132 : RationalCode parameterInterval formula133 :=
  ((RationalCode.constant parameterInterval (8)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-2,0,1]⟩ node132Denominator node132Cross

/-- Article: exact source arithmetic node 134. -/
private def formula134 (z : ℝ) : ℝ := (formula133 z)*(W z)
private theorem node133Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).toPoly≠0 :=
  node125Denominator
private theorem node133Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩)
    ((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node133 : RationalCode parameterInterval formula134 :=
  (node132.mul WCode)
  |>.recode ⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ node133Denominator node133Cross

/-- Article: exact source arithmetic node 135. -/
private def formula135 (z : ℝ) : ℝ := (formula134 z)*(atomA z)
private theorem node134Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node134Cross : polynomialCheck
    (((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩)
    ((⟨#[3584,-18944,48896,-79872,92672,-84480,69888,-59904,51776,-39872,25888,-14976,8736,-5280,2896,-1248,382,-74,7]⟩ : QPoly).mul ((⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node134 : RationalCode parameterInterval formula135 :=
  (node133.mul atomACode)
  |>.recode ⟨#[3584,-18944,48896,-79872,92672,-84480,69888,-59904,51776,-39872,25888,-14976,8736,-5280,2896,-1248,382,-74,7]⟩ ⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩ node134Denominator node134Cross

/-- Article: exact source arithmetic node 136. -/
private def formula136 (z : ℝ) : ℝ := (formula135 z)*(atomB z)
private theorem node135Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly).toPoly≠0 :=
  node127Denominator
private theorem node135Cross : polynomialCheck
    (((⟨#[3584,-18944,48896,-79872,92672,-84480,69888,-59904,51776,-39872,25888,-14976,8736,-5280,2896,-1248,382,-74,7]⟩ : QPoly).mul (⟨#[0,-24,40,-32,20,-6]⟩ : QPoly) : QPoly).mul ⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩)
    ((⟨#[-43008,299008,-1022976,2275328,-3692032,4690944,-4956416,4634624,-4060416,3424768,-2745216,2032896,-1372608,856192,-507552,289664,-154888,73296,-28844,8888,-1998,292,-21]⟩ : QPoly).mul ((⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node135 : RationalCode parameterInterval formula136 :=
  (node134.mul atomBCode)
  |>.recode ⟨#[-43008,299008,-1022976,2275328,-3692032,4690944,-4956416,4634624,-4060416,3424768,-2745216,2032896,-1372608,856192,-507552,289664,-154888,73296,-28844,8888,-1998,292,-21]⟩ ⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ node135Denominator node135Cross

/-- Article: exact source arithmetic node 137. -/
private def formula137 (z : ℝ) : ℝ := (formula132 z)+(formula136 z)
private theorem node136Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node136Cross : polynomialCheck
    ((((⟨#[43008,-299008,1022976,-2275328,3692032,-4690944,4956416,-4634624,4060416,-3424768,2745216,-2032896,1372608,-856192,507552,-289664,154888,-73296,28844,-8888,1998,-292,21]⟩ : QPoly).mul (⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly)).add ((⟨#[-43008,299008,-1022976,2275328,-3692032,4690944,-4956416,4634624,-4060416,3424768,-2745216,2032896,-1372608,856192,-507552,289664,-154888,73296,-28844,8888,-1998,292,-21]⟩ : QPoly).mul (⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly).mul (⟨#[0,8192,-16384,4096,8192,-6144,8192,-4096,-4096,1024,0,1536,0,256,-512,-256,256,-96,64,16,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node136 : RationalCode parameterInterval formula137 :=
  (node131.add node135)
  |>.recode QPoly.zero ⟨#[1]⟩ node136Denominator node136Cross

/-- Article: exact coefficient representation of the independently specified double_square_coefficient1 source. -/
def double_square_coefficient1Code : RationalCode parameterInterval (fun z : ℝ => ((W z)+(-4*((G z))^2)+(-1*(W z)*((u z))^2)+(4*((G z))^2*((u z))^2)+(8*(G z)*(u z))+(-8*(G z)*(W z)*(u z))+(-8*(G z)*(atomA z)*(atomB z))+(8*(G z)*(W z)*(atomA z)*(atomB z)))) where
  numerator := node136.numerator
  denominator := node136.denominator
  denominator_ne := node136.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((W z)+(-4*((G z))^2)+(-1*(W z)*((u z))^2)+(4*((G z))^2*((u z))^2)+(8*(G z)*(u z))+(-8*(G z)*(W z)*(u z))+(-8*(G z)*(atomA z)*(atomB z))+(8*(G z)*(W z)*(atomA z)*(atomB z)))) z=formula137 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,atomPolynomial,endpointCubic,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node136.exact z hz)

/-- Article: exact actual-source identity double_square_coefficient1. -/
theorem double_square_coefficient1 {z : ℝ} (hz : z∈parameterInterval) : (((W z)+(-4*((G z))^2)+(-1*(W z)*((u z))^2)+(4*((G z))^2*((u z))^2)+(8*(G z)*(u z))+(-8*(G z)*(W z)*(u z))+(-8*(G z)*(atomA z)*(atomB z))+(8*(G z)*(W z)*(atomA z)*(atomB z))))=0 :=
  double_square_coefficient1Code.eq_zero (by kernel_decide) hz

/-- Article: exact source arithmetic node 138. -/
private def formula138 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(G z)
private theorem node137Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node137Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-4,0,2]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node137 : RationalCode parameterInterval formula138 :=
  ((RationalCode.constant parameterInterval (-4)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-4,0,2]⟩ node137Denominator node137Cross

/-- Article: exact source arithmetic node 139. -/
private def formula139 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula81 z)
private theorem node138Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  node81Denominator
private theorem node138Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly)))=true := by kernel_decide
private def node138 : RationalCode parameterInterval formula139 :=
  ((RationalCode.constant parameterInterval (4)).mul node80)
  |>.recode ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node138Denominator node138Cross

/-- Article: exact source arithmetic node 140. -/
private def formula140 (z : ℝ) : ℝ := (formula138 z)+(formula139 z)
private theorem node139Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).toPoly≠0 :=
  node81Denominator
private theorem node139Cross : polynomialCheck
    ((((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)).add ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (⟨#[0,-4,0,2]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩)
    ((⟨#[64,0,-1024,0,1072,0,-512,0,268,0,-64,0,1]⟩ : QPoly).mul ((⟨#[0,-4,0,2]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)))=true := by kernel_decide
private def node139 : RationalCode parameterInterval formula140 :=
  (node137.add node138)
  |>.recode ⟨#[64,0,-1024,0,1072,0,-512,0,268,0,-64,0,1]⟩ ⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ node139Denominator node139Cross

/-- Article: exact source arithmetic node 141. -/
private def formula141 (z : ℝ) : ℝ := (W z)*(u z)
private theorem node140Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  node88Denominator
private theorem node140Cross : polynomialCheck
    (((⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩)
    ((⟨#[448,-1920,3968,-5056,4432,-3008,1984,-1504,1108,-632,248,-60,7]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node140 : RationalCode parameterInterval formula141 :=
  (WCode.mul uCode)
  |>.recode ⟨#[448,-1920,3968,-5056,4432,-3008,1984,-1504,1108,-632,248,-60,7]⟩ ⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ node140Denominator node140Cross

/-- Article: exact source arithmetic node 142. -/
private def formula142 (z : ℝ) : ℝ := (formula140 z)+(formula141 z)
private theorem node141Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node89Denominator
private theorem node141Cross : polynomialCheck
    ((((⟨#[64,0,-1024,0,1072,0,-512,0,268,0,-64,0,1]⟩ : QPoly).mul (⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ : QPoly)).add ((⟨#[448,-1920,3968,-5056,4432,-3008,1984,-1504,1108,-632,248,-60,7]⟩ : QPoly).mul (⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩)
    ((⟨#[2048,-4096,-28672,90112,-150528,220160,-204032,32768,108032,-95744,23680,5120,11840,-23936,13504,2048,-6376,3440,-1176,352,-56,-4,1]⟩ : QPoly).mul ((⟨#[0,0,0,-1024,0,1536,0,-768,0,128]⟩ : QPoly).mul (⟨#[-512,1024,-768,512,-384,0,0,0,96,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node141 : RationalCode parameterInterval formula142 :=
  (node139.add node140)
  |>.recode ⟨#[2048,-4096,-28672,90112,-150528,220160,-204032,32768,108032,-95744,23680,5120,11840,-23936,13504,2048,-6376,3440,-1176,352,-56,-4,1]⟩ ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ node141Denominator node141Cross

/-- Article: exact source arithmetic node 143. -/
private def formula143 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(G z)
private theorem node142Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  node137Denominator
private theorem node142Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-4,0,2]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node142 : RationalCode parameterInterval formula143 :=
  ((RationalCode.constant parameterInterval (-4)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-4,0,2]⟩ node142Denominator node142Cross

/-- Article: exact source arithmetic node 144. -/
private def formula144 (z : ℝ) : ℝ := (formula143 z)*(atomB z)
private theorem node143Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-16,0,16,0,0,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node143Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[0,-24,40,-32,20,-6]⟩ : QPoly) : QPoly).mul ⟨#[-16,0,16,0,0,0,-4,0,1]⟩)
    ((⟨#[48,-80,64,-40,24,-20,16,-10,3]⟩ : QPoly).mul ((⟨#[0,-4,0,2]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node143 : RationalCode parameterInterval formula144 :=
  (node142.mul atomBCode)
  |>.recode ⟨#[48,-80,64,-40,24,-20,16,-10,3]⟩ ⟨#[-16,0,16,0,0,0,-4,0,1]⟩ node143Denominator node143Cross

/-- Article: exact source arithmetic node 145. -/
private def formula145 (z : ℝ) : ℝ := (formula142 z)+(formula144 z)
private theorem node144Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node89Denominator
private theorem node144Cross : polynomialCheck
    ((((⟨#[2048,-4096,-28672,90112,-150528,220160,-204032,32768,108032,-95744,23680,5120,11840,-23936,13504,2048,-6376,3440,-1176,352,-56,-4,1]⟩ : QPoly).mul (⟨#[-16,0,16,0,0,0,-4,0,1]⟩ : QPoly)).add ((⟨#[48,-80,64,-40,24,-20,16,-10,3]⟩ : QPoly).mul (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩)
    ((⟨#[2048,-4096,-28672,188416,-510976,826368,-892160,704512,-498176,424448,-406400,328704,-203200,106112,-62272,44032,-27880,12912,-3992,736,-56,-4,1]⟩ : QPoly).mul ((⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).mul (⟨#[-16,0,16,0,0,0,-4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node144 : RationalCode parameterInterval formula145 :=
  (node141.add node143)
  |>.recode ⟨#[2048,-4096,-28672,188416,-510976,826368,-892160,704512,-498176,424448,-406400,328704,-203200,106112,-62272,44032,-27880,12912,-3992,736,-56,-4,1]⟩ ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ node144Denominator node144Cross

/-- Article: exact source arithmetic node 146. -/
private def formula146 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(u z)
private theorem node145Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node98Denominator
private theorem node145Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-4,0,0,0,1]⟩)
    ((⟨#[-16,32,-32,16,-4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node145 : RationalCode parameterInterval formula146 :=
  ((RationalCode.constant parameterInterval (-4)).mul uCode)
  |>.recode ⟨#[-16,32,-32,16,-4]⟩ ⟨#[-4,0,0,0,1]⟩ node145Denominator node145Cross

/-- Article: exact source arithmetic node 147. -/
private def formula147 (z : ℝ) : ℝ := (formula146 z)*(formula100 z)
private theorem node146Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  node100Denominator
private theorem node146Cross : polynomialCheck
    (((⟨#[-16,32,-32,16,-4]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩)
    ((⟨#[-64,128,-128,64,-48,64,-64,32,-12,8,-8,4,-1]⟩ : QPoly).mul ((⟨#[-4,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node146 : RationalCode parameterInterval formula147 :=
  (node145.mul node99)
  |>.recode ⟨#[-64,128,-128,64,-48,64,-64,32,-12,8,-8,4,-1]⟩ ⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ node146Denominator node146Cross

/-- Article: exact source arithmetic node 148. -/
private def formula148 (z : ℝ) : ℝ := (formula145 z)+(formula147 z)
private theorem node147Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node89Denominator
private theorem node147Cross : polynomialCheck
    ((((⟨#[2048,-4096,-28672,188416,-510976,826368,-892160,704512,-498176,424448,-406400,328704,-203200,106112,-62272,44032,-27880,12912,-3992,736,-56,-4,1]⟩ : QPoly).mul (⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ : QPoly)).add ((⟨#[-64,128,-128,64,-48,64,-64,32,-12,8,-8,4,-1]⟩ : QPoly).mul (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩)
    ((⟨#[2048,-12288,4096,126976,-437248,754688,-822528,634880,-434688,373248,-368512,301568,-184256,93312,-54336,39680,-25704,11792,-3416,496,8,-12,1]⟩ : QPoly).mul ((⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).mul (⟨#[0,0,-256,0,256,0,0,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node147 : RationalCode parameterInterval formula148 :=
  (node144.add node146)
  |>.recode ⟨#[2048,-12288,4096,126976,-437248,754688,-822528,634880,-434688,373248,-368512,301568,-184256,93312,-54336,39680,-25704,11792,-3416,496,8,-12,1]⟩ ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ node147Denominator node147Cross

/-- Article: exact source arithmetic node 149. -/
private def formula149 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(G z)
private theorem node148Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node82Denominator
private theorem node148Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node148 : RationalCode parameterInterval formula149 :=
  ((RationalCode.constant parameterInterval (-2)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-8,0,4]⟩ node148Denominator node148Cross

/-- Article: exact source arithmetic node 150. -/
private def formula150 (z : ℝ) : ℝ := (atomA z)^2
private theorem node149Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,0,0,-32,0,0,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node149Cross : polynomialCheck
    ((polynomialPower ⟨#[8,-24,36,-32,18,-6,1]⟩ 2 : QPoly).mul ⟨#[0,0,64,0,0,0,-32,0,0,0,4]⟩)
    ((⟨#[64,-384,1152,-2240,3120,-3264,2624,-1632,780,-280,72,-12,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-8,0,0,0,2]⟩ 2))=true := by kernel_decide
private def node149 : RationalCode parameterInterval formula150 :=
  (atomACode.pow 2)
  |>.recode ⟨#[64,-384,1152,-2240,3120,-3264,2624,-1632,780,-280,72,-12,1]⟩ ⟨#[0,0,64,0,0,0,-32,0,0,0,4]⟩ node149Denominator node149Cross

/-- Article: exact source arithmetic node 151. -/
private def formula151 (z : ℝ) : ℝ := (formula149 z)*(formula150 z)
private theorem node150Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-512,0,256,0,256,0,-128,0,-32,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node150Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[64,-384,1152,-2240,3120,-3264,2624,-1632,780,-280,72,-12,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-512,0,256,0,256,0,-128,0,-32,0,16]⟩)
    ((⟨#[-256,1536,-4608,8960,-12544,13440,-11648,8768,-6240,4384,-2912,1680,-784,280,-72,12,-1]⟩ : QPoly).mul ((⟨#[0,-8,0,4]⟩ : QPoly).mul (⟨#[0,0,64,0,0,0,-32,0,0,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node150 : RationalCode parameterInterval formula151 :=
  (node148.mul node149)
  |>.recode ⟨#[-256,1536,-4608,8960,-12544,13440,-11648,8768,-6240,4384,-2912,1680,-784,280,-72,12,-1]⟩ ⟨#[0,0,0,-512,0,256,0,256,0,-128,0,-32,0,16]⟩ node150Denominator node150Cross

/-- Article: exact source arithmetic node 152. -/
private def formula152 (z : ℝ) : ℝ := (formula148 z)+(formula151 z)
private theorem node151Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node89Denominator
private theorem node151Cross : polynomialCheck
    ((((⟨#[2048,-12288,4096,126976,-437248,754688,-822528,634880,-434688,373248,-368512,301568,-184256,93312,-54336,39680,-25704,11792,-3416,496,8,-12,1]⟩ : QPoly).mul (⟨#[0,0,0,-512,0,256,0,256,0,-128,0,-32,0,16]⟩ : QPoly)).add ((⟨#[-256,1536,-4608,8960,-12544,13440,-11648,8768,-6240,4384,-2912,1680,-784,280,-72,12,-1]⟩ : QPoly).mul (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩)
    ((⟨#[-14336,118784,-503808,1388544,-2690048,3851264,-4289792,3993600,-3426816,2916864,-2418560,1823232,-1209280,729216,-428352,249600,-134056,60176,-21016,5424,-984,116,-7]⟩ : QPoly).mul ((⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).mul (⟨#[0,0,0,-512,0,256,0,256,0,-128,0,-32,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node151 : RationalCode parameterInterval formula152 :=
  (node147.add node150)
  |>.recode ⟨#[-14336,118784,-503808,1388544,-2690048,3851264,-4289792,3993600,-3426816,2916864,-2418560,1823232,-1209280,729216,-428352,249600,-134056,60176,-21016,5424,-984,116,-7]⟩ ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ node151Denominator node151Cross

/-- Article: exact source arithmetic node 153. -/
private def formula153 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(G z)
private theorem node152Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node82Denominator
private theorem node152Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node152 : RationalCode parameterInterval formula153 :=
  ((RationalCode.constant parameterInterval (2)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-8,0,4]⟩ node152Denominator node152Cross

/-- Article: exact source arithmetic node 154. -/
private def formula154 (z : ℝ) : ℝ := (formula153 z)*(formula96 z)
private theorem node153Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node96Denominator
private theorem node153Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩)
    ((⟨#[64,-256,512,-640,560,-384,256,-192,140,-80,32,-8,1]⟩ : QPoly).mul ((⟨#[0,-8,0,4]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node153 : RationalCode parameterInterval formula154 :=
  (node152.mul node95)
  |>.recode ⟨#[64,-256,512,-640,560,-384,256,-192,140,-80,32,-8,1]⟩ ⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ node153Denominator node153Cross

/-- Article: exact source arithmetic node 155. -/
private def formula155 (z : ℝ) : ℝ := (formula152 z)+(formula154 z)
private theorem node154Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node89Denominator
private theorem node154Cross : polynomialCheck
    ((((⟨#[-14336,118784,-503808,1388544,-2690048,3851264,-4289792,3993600,-3426816,2916864,-2418560,1823232,-1209280,729216,-428352,249600,-134056,60176,-21016,5424,-984,116,-7]⟩ : QPoly).mul (⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ : QPoly)).add ((⟨#[64,-256,512,-640,560,-384,256,-192,140,-80,32,-8,1]⟩ : QPoly).mul (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩)
    ((⟨#[-14336,118784,-487424,1290240,-2411520,3359744,-3679488,3403776,-2920960,2482688,-2048896,1540608,-1024448,620672,-365120,212736,-114984,52496,-18840,5040,-952,116,-7]⟩ : QPoly).mul ((⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).mul (⟨#[0,-128,0,64,0,64,0,-32,0,-8,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node154 : RationalCode parameterInterval formula155 :=
  (node151.add node153)
  |>.recode ⟨#[-14336,118784,-487424,1290240,-2411520,3359744,-3679488,3403776,-2920960,2482688,-2048896,1540608,-1024448,620672,-365120,212736,-114984,52496,-18840,5040,-952,116,-7]⟩ ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ node154Denominator node154Cross

/-- Article: exact source arithmetic node 156. -/
private def formula156 (z : ℝ) : ℝ := ((fun _ : ℝ => ((3 : ℚ) : ℝ)) z)*(G z)
private theorem node155Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  node84Denominator
private theorem node155Cross : polynomialCheck
    (((⟨#[3]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[12,0,0,0,3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node155 : RationalCode parameterInterval formula156 :=
  ((RationalCode.constant parameterInterval (3)).mul GCode)
  |>.recode ⟨#[12,0,0,0,3]⟩ ⟨#[0,-16,0,8]⟩ node155Denominator node155Cross

/-- Article: exact source arithmetic node 157. -/
private def formula157 (z : ℝ) : ℝ := (formula156 z)*(W z)
private theorem node156Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly).toPoly≠0 :=
  node85Denominator
private theorem node156Cross : polynomialCheck
    (((⟨#[12,0,0,0,3]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩)
    ((⟨#[1344,-3072,3072,-1536,1008,-1536,1536,-768,252,-192,192,-96,21]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node156 : RationalCode parameterInterval formula157 :=
  (node155.mul WCode)
  |>.recode ⟨#[1344,-3072,3072,-1536,1008,-1536,1536,-768,252,-192,192,-96,21]⟩ ⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ node156Denominator node156Cross

/-- Article: exact source arithmetic node 158. -/
private def formula158 (z : ℝ) : ℝ := (formula155 z)+(formula157 z)
private theorem node157Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).toPoly≠0 :=
  node89Denominator
private theorem node157Cross : polynomialCheck
    ((((⟨#[-14336,118784,-487424,1290240,-2411520,3359744,-3679488,3403776,-2920960,2482688,-2048896,1540608,-1024448,620672,-365120,212736,-114984,52496,-18840,5040,-952,116,-7]⟩ : QPoly).mul (⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly)).add ((⟨#[1344,-3072,3072,-1536,1008,-1536,1536,-768,252,-192,192,-96,21]⟩ : QPoly).mul (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩)
    ((⟨#[-14336,118784,-465920,1241088,-2373120,3359744,-3693312,3403776,-2914048,2482688,-2055040,1546752,-1027520,620672,-364256,212736,-115416,52496,-18540,4848,-910,116,-7]⟩ : QPoly).mul ((⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).mul (⟨#[0,-2048,4096,-2048,0,-512,0,256,0,256,-256,64]⟩ : QPoly)))=true := by kernel_decide
private def node157 : RationalCode parameterInterval formula158 :=
  (node154.add node156)
  |>.recode ⟨#[-14336,118784,-465920,1241088,-2373120,3359744,-3693312,3403776,-2914048,2482688,-2055040,1546752,-1027520,620672,-364256,212736,-115416,52496,-18540,4848,-910,116,-7]⟩ ⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ node157Denominator node157Cross

/-- Article: exact source arithmetic node 159. -/
private def formula159 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(G z)
private theorem node158Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node82Denominator
private theorem node158Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node158 : RationalCode parameterInterval formula159 :=
  ((RationalCode.constant parameterInterval (-2)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-8,0,4]⟩ node158Denominator node158Cross

/-- Article: exact source arithmetic node 160. -/
private def formula160 (z : ℝ) : ℝ := (formula159 z)*(W z)
private theorem node159Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ : QPoly).toPoly≠0 :=
  node109Denominator
private theorem node159Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩)
    ((⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ : QPoly).mul ((⟨#[0,-8,0,4]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node159 : RationalCode parameterInterval formula160 :=
  (node158.mul WCode)
  |>.recode ⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ ⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ node159Denominator node159Cross

/-- Article: exact source arithmetic node 161. -/
private def formula161 (z : ℝ) : ℝ := (formula160 z)*(formula96 z)
private theorem node160Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16384,32768,-16384,0,4096,-16384,10240,0,3072,0,-1536,0,-1280,1024,-128,0,128,-128,32]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node160Cross : polynomialCheck
    (((⟨#[-448,1024,-1024,512,-336,512,-512,256,-84,64,-64,32,-7]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16384,32768,-16384,0,4096,-16384,10240,0,3072,0,-1536,0,-1280,1024,-128,0,128,-128,32]⟩)
    ((⟨#[-7168,45056,-139264,276480,-393984,434176,-401408,344064,-293248,243200,-183296,121600,-73312,43008,-25088,13568,-6156,2160,-544,88,-7]⟩ : QPoly).mul ((⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node160 : RationalCode parameterInterval formula161 :=
  (node159.mul node95)
  |>.recode ⟨#[-7168,45056,-139264,276480,-393984,434176,-401408,344064,-293248,243200,-183296,121600,-73312,43008,-25088,13568,-6156,2160,-544,88,-7]⟩ ⟨#[0,-16384,32768,-16384,0,4096,-16384,10240,0,3072,0,-1536,0,-1280,1024,-128,0,128,-128,32]⟩ node160Denominator node160Cross

/-- Article: exact source arithmetic node 162. -/
private def formula162 (z : ℝ) : ℝ := (formula158 z)+(formula161 z)
private theorem node161Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node161Cross : polynomialCheck
    ((((⟨#[-14336,118784,-465920,1241088,-2373120,3359744,-3693312,3403776,-2914048,2482688,-2055040,1546752,-1027520,620672,-364256,212736,-115416,52496,-18540,4848,-910,116,-7]⟩ : QPoly).mul (⟨#[0,-16384,32768,-16384,0,4096,-16384,10240,0,3072,0,-1536,0,-1280,1024,-128,0,128,-128,32]⟩ : QPoly)).add ((⟨#[-7168,45056,-139264,276480,-393984,434176,-401408,344064,-293248,243200,-183296,121600,-73312,43008,-25088,13568,-6156,2160,-544,88,-7]⟩ : QPoly).mul (⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩)
    ((⟨#[-28672,237568,-974848,2781184,-5769216,9066496,-11335680,11904000,-11127040,9745408,-8197120,6548992,-4843264,3274496,-2049280,1218176,-695440,372000,-177120,70832,-22536,5432,-952,116,-7]⟩ : QPoly).mul ((⟨#[0,0,0,-32768,65536,-16384,-32768,16384,-16384,12288,8192,0,-4096,-3072,2048,-1024,1024,256,-512,128]⟩ : QPoly).mul (⟨#[0,-16384,32768,-16384,0,4096,-16384,10240,0,3072,0,-1536,0,-1280,1024,-128,0,128,-128,32]⟩ : QPoly)))=true := by kernel_decide
private def node161 : RationalCode parameterInterval formula162 :=
  (node157.add node160)
  |>.recode ⟨#[-28672,237568,-974848,2781184,-5769216,9066496,-11335680,11904000,-11127040,9745408,-8197120,6548992,-4843264,3274496,-2049280,1218176,-695440,372000,-177120,70832,-22536,5432,-952,116,-7]⟩ ⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ node161Denominator node161Cross

/-- Article: exact source arithmetic node 163. -/
private def formula163 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(G z)
private theorem node162Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node82Denominator
private theorem node162Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node162 : RationalCode parameterInterval formula163 :=
  ((RationalCode.constant parameterInterval (2)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-8,0,4]⟩ node162Denominator node162Cross

/-- Article: exact source arithmetic node 164. -/
private def formula164 (z : ℝ) : ℝ := (formula163 z)*(W z)
private theorem node163Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ : QPoly).toPoly≠0 :=
  node109Denominator
private theorem node163Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩)
    ((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[0,-8,0,4]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node163 : RationalCode parameterInterval formula164 :=
  (node162.mul WCode)
  |>.recode ⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ ⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ node163Denominator node163Cross

/-- Article: exact source arithmetic node 165. -/
private def formula165 (z : ℝ) : ℝ := (formula164 z)*(formula150 z)
private theorem node164Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ : QPoly).toPoly≠0 :=
  node161Denominator
private theorem node164Cross : polynomialCheck
    (((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul (⟨#[64,-384,1152,-2240,3120,-3264,2624,-1632,780,-280,72,-12,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩)
    ((⟨#[28672,-237568,974848,-2609152,5089280,-7702528,9476096,-9913344,9267456,-8111104,6802432,-5415424,3998464,-2707712,1700608,-1013888,579216,-309792,148064,-60176,19880,-5096,952,-116,7]⟩ : QPoly).mul ((⟨#[0,-1024,2048,-1024,0,-256,0,128,0,128,-128,32]⟩ : QPoly).mul (⟨#[0,0,64,0,0,0,-32,0,0,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node164 : RationalCode parameterInterval formula165 :=
  (node163.mul node149)
  |>.recode ⟨#[28672,-237568,974848,-2609152,5089280,-7702528,9476096,-9913344,9267456,-8111104,6802432,-5415424,3998464,-2707712,1700608,-1013888,579216,-309792,148064,-60176,19880,-5096,952,-116,7]⟩ ⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ node164Denominator node164Cross

/-- Article: exact source arithmetic node 166. -/
private def formula166 (z : ℝ) : ℝ := (formula162 z)+(formula165 z)
private theorem node165Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node165Cross : polynomialCheck
    ((((⟨#[-28672,237568,-974848,2781184,-5769216,9066496,-11335680,11904000,-11127040,9745408,-8197120,6548992,-4843264,3274496,-2049280,1218176,-695440,372000,-177120,70832,-22536,5432,-952,116,-7]⟩ : QPoly).mul (⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ : QPoly)).add ((⟨#[28672,-237568,974848,-2609152,5089280,-7702528,9476096,-9913344,9267456,-8111104,6802432,-5415424,3998464,-2707712,1700608,-1013888,579216,-309792,148064,-60176,19880,-5096,952,-116,7]⟩ : QPoly).mul (⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ : QPoly)) : QPoly).mul ⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩)
    ((⟨#[5376,-21248,39936,-47488,42240,-34368,29952,-26400,20448,-13200,7488,-4296,2640,-1484,624,-166,21]⟩ : QPoly).mul ((⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ : QPoly).mul (⟨#[0,0,0,-65536,131072,-65536,0,16384,-65536,40960,0,12288,0,-6144,0,-5120,4096,-512,0,512,-512,128]⟩ : QPoly)))=true := by kernel_decide
private def node165 : RationalCode parameterInterval formula166 :=
  (node161.add node164)
  |>.recode ⟨#[5376,-21248,39936,-47488,42240,-34368,29952,-26400,20448,-13200,7488,-4296,2640,-1484,624,-166,21]⟩ ⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ node165Denominator node165Cross

/-- Article: exact source arithmetic node 167. -/
private def formula167 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(G z)
private theorem node166Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  node137Denominator
private theorem node166Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-4,0,2]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node166 : RationalCode parameterInterval formula167 :=
  ((RationalCode.constant parameterInterval (4)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-4,0,2]⟩ node166Denominator node166Cross

/-- Article: exact source arithmetic node 168. -/
private def formula168 (z : ℝ) : ℝ := (formula167 z)*(W z)
private theorem node167Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-512,1024,-512,0,-128,0,64,0,64,-64,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node167Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-512,1024,-512,0,-128,0,64,0,64,-64,16]⟩)
    ((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[0,-4,0,2]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node167 : RationalCode parameterInterval formula168 :=
  (node166.mul WCode)
  |>.recode ⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ ⟨#[0,-512,1024,-512,0,-128,0,64,0,64,-64,16]⟩ node167Denominator node167Cross

/-- Article: exact source arithmetic node 169. -/
private def formula169 (z : ℝ) : ℝ := (formula168 z)*(atomB z)
private theorem node168Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ : QPoly).toPoly≠0 :=
  node165Denominator
private theorem node168Cross : polynomialCheck
    (((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul (⟨#[0,-24,40,-32,20,-6]⟩ : QPoly) : QPoly).mul ⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩)
    ((⟨#[-5376,21248,-39936,47488,-42240,34368,-29952,26400,-20448,13200,-7488,4296,-2640,1484,-624,166,-21]⟩ : QPoly).mul ((⟨#[0,-512,1024,-512,0,-128,0,64,0,64,-64,16]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node168 : RationalCode parameterInterval formula169 :=
  (node167.mul atomBCode)
  |>.recode ⟨#[-5376,21248,-39936,47488,-42240,34368,-29952,26400,-20448,13200,-7488,4296,-2640,1484,-624,166,-21]⟩ ⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ node168Denominator node168Cross

/-- Article: exact source arithmetic node 170. -/
private def formula170 (z : ℝ) : ℝ := (formula166 z)+(formula169 z)
private theorem node169Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node169Cross : polynomialCheck
    ((((⟨#[5376,-21248,39936,-47488,42240,-34368,29952,-26400,20448,-13200,7488,-4296,2640,-1484,624,-166,21]⟩ : QPoly).mul (⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ : QPoly)).add ((⟨#[-5376,21248,-39936,47488,-42240,34368,-29952,26400,-20448,13200,-7488,4296,-2640,1484,-624,166,-21]⟩ : QPoly).mul (⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ : QPoly).mul (⟨#[-2048,4096,-1024,-2048,1024,-1024,768,512,0,-256,-192,128,-64,64,16,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node169 : RationalCode parameterInterval formula170 :=
  (node165.add node168)
  |>.recode QPoly.zero ⟨#[1]⟩ node169Denominator node169Cross

/-- Article: exact source arithmetic node 171. -/
private def formula171 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(formula170 z)
private theorem node170Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node170Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (QPoly.zero : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node170 : RationalCode parameterInterval formula171 :=
  ((RationalCode.constant parameterInterval (2)).mul node169)
  |>.recode QPoly.zero ⟨#[1]⟩ node170Denominator node170Cross

/-- Article: exact coefficient representation of the independently specified double_square_coefficient2 source. -/
def double_square_coefficient2Code : RationalCode parameterInterval (fun z : ℝ => ((-8*(G z))+(8*((G z))^3)+(-8*(G z)*(atomB z))+(-8*(u z)*((G z))^2)+(-4*(G z)*((atomA z))^2)+(2*(W z)*(u z))+(4*(G z)*((u z))^2)+(6*(G z)*(W z))+(-4*(G z)*(W z)*((u z))^2)+(4*(G z)*(W z)*((atomA z))^2)+(8*(G z)*(W z)*(atomB z)))) where
  numerator := node170.numerator
  denominator := node170.denominator
  denominator_ne := node170.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((-8*(G z))+(8*((G z))^3)+(-8*(G z)*(atomB z))+(-8*(u z)*((G z))^2)+(-4*(G z)*((atomA z))^2)+(2*(W z)*(u z))+(4*(G z)*((u z))^2)+(6*(G z)*(W z))+(-4*(G z)*(W z)*((u z))^2)+(4*(G z)*(W z)*((atomA z))^2)+(8*(G z)*(W z)*(atomB z)))) z=formula171 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154,formula155,formula156,formula157,formula158,formula159,formula160,formula161,formula162,formula163,formula164,formula165,formula166,formula167,formula168,formula169,formula170,formula171,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,atomPolynomial,endpointCubic,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node170.exact z hz)

/-- Article: exact actual-source identity double_square_coefficient2. -/
theorem double_square_coefficient2 {z : ℝ} (hz : z∈parameterInterval) : (((-8*(G z))+(8*((G z))^3)+(-8*(G z)*(atomB z))+(-8*(u z)*((G z))^2)+(-4*(G z)*((atomA z))^2)+(2*(W z)*(u z))+(4*(G z)*((u z))^2)+(6*(G z)*(W z))+(-4*(G z)*(W z)*((u z))^2)+(4*(G z)*(W z)*((atomA z))^2)+(8*(G z)*(W z)*(atomB z))))=0 :=
  double_square_coefficient2Code.eq_zero (by kernel_decide) hz

/-- Article: exact source arithmetic node 172. -/
private def formula172 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(W z)
private theorem node171Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  node87Denominator
private theorem node171Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩)
    ((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node171 : RationalCode parameterInterval formula172 :=
  ((RationalCode.constant parameterInterval (-1)).mul WCode)
  |>.recode ⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ node171Denominator node171Cross

/-- Article: exact source arithmetic node 173. -/
private def formula173 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula100 z)
private theorem node172Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
private theorem node172Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node172 : RationalCode parameterInterval formula173 :=
  ((RationalCode.constant parameterInterval (4)).mul node99)
  |>.recode ⟨#[16,0,0,0,8,0,0,0,1]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node172Denominator node172Cross

/-- Article: exact source arithmetic node 174. -/
private def formula174 (z : ℝ) : ℝ := (formula172 z)+(formula173 z)
private theorem node173Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).toPoly≠0 :=
  node114Denominator
private theorem node173Cross : polynomialCheck
    ((((⟨#[-112,256,-256,128,-56,64,-64,32,-7]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)).add ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩)
    ((⟨#[256,-512,-512,1792,-768,-1408,1664,-192,-416,-96,416,-176,-48,56,-8,-4,1]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node173 : RationalCode parameterInterval formula174 :=
  (node171.add node172)
  |>.recode ⟨#[256,-512,-512,1792,-768,-1408,1664,-192,-416,-96,416,-176,-48,56,-8,-4,1]⟩ ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ node173Denominator node173Cross

/-- Article: exact source arithmetic node 175. -/
private def formula175 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-8 : ℚ) : ℝ)) z)*(G z)
private theorem node174Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node121Denominator
private theorem node174Cross : polynomialCheck
    (((⟨#[-8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node174 : RationalCode parameterInterval formula175 :=
  ((RationalCode.constant parameterInterval (-8)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-2,0,1]⟩ node174Denominator node174Cross

/-- Article: exact source arithmetic node 176. -/
private def formula176 (z : ℝ) : ℝ := (formula175 z)*(atomA z)
private theorem node175Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,16,0,-8,0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  node129Denominator
private theorem node175Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,16,0,-8,0,-4,0,2]⟩)
    ((⟨#[-32,96,-144,128,-80,48,-40,32,-18,6,-1]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node175 : RationalCode parameterInterval formula176 :=
  (node174.mul atomACode)
  |>.recode ⟨#[-32,96,-144,128,-80,48,-40,32,-18,6,-1]⟩ ⟨#[0,0,16,0,-8,0,-4,0,2]⟩ node175Denominator node175Cross

/-- Article: exact source arithmetic node 177. -/
private def formula177 (z : ℝ) : ℝ := (formula174 z)+(formula176 z)
private theorem node176Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).toPoly≠0 :=
  node114Denominator
private theorem node176Cross : polynomialCheck
    ((((⟨#[256,-512,-512,1792,-768,-1408,1664,-192,-416,-96,416,-176,-48,56,-8,-4,1]⟩ : QPoly).mul (⟨#[0,0,16,0,-8,0,-4,0,2]⟩ : QPoly)).add ((⟨#[-32,96,-144,128,-80,48,-40,32,-18,6,-1]⟩ : QPoly).mul (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩)
    ((⟨#[-1792,9728,-24064,34560,-32512,24192,-20096,19520,-16032,9760,-5024,3024,-2032,1080,-376,76,-7]⟩ : QPoly).mul ((⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).mul (⟨#[0,0,16,0,-8,0,-4,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node176 : RationalCode parameterInterval formula177 :=
  (node173.add node175)
  |>.recode ⟨#[-1792,9728,-24064,34560,-32512,24192,-20096,19520,-16032,9760,-5024,3024,-2032,1080,-376,76,-7]⟩ ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ node176Denominator node176Cross

/-- Article: exact source arithmetic node 178. -/
private def formula178 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-8 : ℚ) : ℝ)) z)*(G z)
private theorem node177Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node121Denominator
private theorem node177Cross : polynomialCheck
    (((⟨#[-8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node177 : RationalCode parameterInterval formula178 :=
  ((RationalCode.constant parameterInterval (-8)).mul GCode)
  |>.recode ⟨#[-4,0,0,0,-1]⟩ ⟨#[0,-2,0,1]⟩ node177Denominator node177Cross

/-- Article: exact source arithmetic node 179. -/
private def formula179 (z : ℝ) : ℝ := (formula178 z)*(u z)
private theorem node178Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node122Denominator
private theorem node178Cross : polynomialCheck
    (((⟨#[-4,0,0,0,-1]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[0,8,0,-4,0,-2,0,1]⟩)
    ((⟨#[-16,32,-32,16,-8,8,-8,4,-1]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node178 : RationalCode parameterInterval formula179 :=
  (node177.mul uCode)
  |>.recode ⟨#[-16,32,-32,16,-8,8,-8,4,-1]⟩ ⟨#[0,8,0,-4,0,-2,0,1]⟩ node178Denominator node178Cross

/-- Article: exact source arithmetic node 180. -/
private def formula180 (z : ℝ) : ℝ := (formula177 z)+(formula179 z)
private theorem node179Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).toPoly≠0 :=
  node114Denominator
private theorem node179Cross : polynomialCheck
    ((((⟨#[-1792,9728,-24064,34560,-32512,24192,-20096,19520,-16032,9760,-5024,3024,-2032,1080,-376,76,-7]⟩ : QPoly).mul (⟨#[0,8,0,-4,0,-2,0,1]⟩ : QPoly)).add ((⟨#[-16,32,-32,16,-8,8,-8,4,-1]⟩ : QPoly).mul (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩)
    ((⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ : QPoly).mul ((⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).mul (⟨#[0,8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node179 : RationalCode parameterInterval formula180 :=
  (node176.add node178)
  |>.recode ⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ ⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ node179Denominator node179Cross

/-- Article: exact source arithmetic node 181. -/
private def formula181 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8 : ℚ) : ℝ)) z)*(G z)
private theorem node180Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node121Denominator
private theorem node180Cross : polynomialCheck
    (((⟨#[8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node180 : RationalCode parameterInterval formula181 :=
  ((RationalCode.constant parameterInterval (8)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-2,0,1]⟩ node180Denominator node180Cross

/-- Article: exact source arithmetic node 182. -/
private def formula182 (z : ℝ) : ℝ := (formula181 z)*(W z)
private theorem node181Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).toPoly≠0 :=
  node125Denominator
private theorem node181Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩)
    ((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node181 : RationalCode parameterInterval formula182 :=
  (node180.mul WCode)
  |>.recode ⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ node181Denominator node181Cross

/-- Article: exact source arithmetic node 183. -/
private def formula183 (z : ℝ) : ℝ := (formula182 z)*(atomA z)
private theorem node182Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩ : QPoly).toPoly≠0 :=
  node134Denominator
private theorem node182Cross : polynomialCheck
    (((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩)
    ((⟨#[3584,-18944,48896,-79872,92672,-84480,69888,-59904,51776,-39872,25888,-14976,8736,-5280,2896,-1248,382,-74,7]⟩ : QPoly).mul ((⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node182 : RationalCode parameterInterval formula183 :=
  (node181.mul atomACode)
  |>.recode ⟨#[3584,-18944,48896,-79872,92672,-84480,69888,-59904,51776,-39872,25888,-14976,8736,-5280,2896,-1248,382,-74,7]⟩ ⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩ node182Denominator node182Cross

/-- Article: exact source arithmetic node 184. -/
private def formula184 (z : ℝ) : ℝ := (formula180 z)+(formula183 z)
private theorem node183Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly).toPoly≠0 :=
  node126Denominator
private theorem node183Cross : polynomialCheck
    ((((⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ : QPoly).mul (⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩ : QPoly)).add ((⟨#[3584,-18944,48896,-79872,92672,-84480,69888,-59904,51776,-39872,25888,-14976,8736,-5280,2896,-1248,382,-74,7]⟩ : QPoly).mul (⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩)
    ((⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ : QPoly).mul ((⟨#[0,0,1024,-2048,512,1024,-256,0,-256,0,-64,128,32,-64,16]⟩ : QPoly).mul (⟨#[0,0,2048,-4096,2048,0,0,1024,-768,0,-384,256,0,0,64,-64,16]⟩ : QPoly)))=true := by kernel_decide
private def node183 : RationalCode parameterInterval formula184 :=
  (node179.add node182)
  |>.recode ⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ ⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ node183Denominator node183Cross

/-- Article: exact source arithmetic node 185. -/
private def formula185 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8 : ℚ) : ℝ)) z)*(G z)
private theorem node184Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node121Denominator
private theorem node184Cross : polynomialCheck
    (((⟨#[8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-2,0,1]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node184 : RationalCode parameterInterval formula185 :=
  ((RationalCode.constant parameterInterval (8)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-2,0,1]⟩ node184Denominator node184Cross

/-- Article: exact source arithmetic node 186. -/
private def formula186 (z : ℝ) : ℝ := (formula185 z)*(W z)
private theorem node185Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).toPoly≠0 :=
  node125Denominator
private theorem node185Cross : polynomialCheck
    (((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly) : QPoly).mul ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩)
    ((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[0,-2,0,1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node185 : RationalCode parameterInterval formula186 :=
  (node184.mul WCode)
  |>.recode ⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ ⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ node185Denominator node185Cross

/-- Article: exact source arithmetic node 187. -/
private def formula187 (z : ℝ) : ℝ := (formula186 z)*(u z)
private theorem node186Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly).toPoly≠0 :=
  node126Denominator
private theorem node186Cross : polynomialCheck
    (((⟨#[448,-1024,1024,-512,336,-512,512,-256,84,-64,64,-32,7]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩)
    ((⟨#[1792,-7680,15872,-20224,18176,-13952,11904,-11072,8864,-5536,2976,-1744,1136,-632,248,-60,7]⟩ : QPoly).mul ((⟨#[0,-256,512,-256,0,-64,0,32,0,32,-32,8]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node186 : RationalCode parameterInterval formula187 :=
  (node185.mul uCode)
  |>.recode ⟨#[1792,-7680,15872,-20224,18176,-13952,11904,-11072,8864,-5536,2976,-1744,1136,-632,248,-60,7]⟩ ⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ node186Denominator node186Cross

/-- Article: exact source arithmetic node 188. -/
private def formula188 (z : ℝ) : ℝ := (formula184 z)+(formula187 z)
private theorem node187Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node187Cross : polynomialCheck
    ((((⟨#[-1792,7680,-15872,20224,-18176,13952,-11904,11072,-8864,5536,-2976,1744,-1136,632,-248,60,-7]⟩ : QPoly).mul (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly)).add ((⟨#[1792,-7680,15872,-20224,18176,-13952,11904,-11072,8864,-5536,2976,-1744,1136,-632,248,-60,7]⟩ : QPoly).mul (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly).mul (⟨#[0,1024,-2048,1024,0,0,512,-384,0,-192,128,0,0,32,-32,8]⟩ : QPoly)))=true := by kernel_decide
private def node187 : RationalCode parameterInterval formula188 :=
  (node183.add node186)
  |>.recode QPoly.zero ⟨#[1]⟩ node187Denominator node187Cross

/-- Article: exact coefficient representation of the independently specified double_square_coefficient3 source. -/
def double_square_coefficient3Code : RationalCode parameterInterval (fun z : ℝ => ((-1*(W z))+(4*((G z))^2)+(-8*(G z)*(atomA z))+(-8*(G z)*(u z))+(8*(G z)*(W z)*(atomA z))+(8*(G z)*(W z)*(u z)))) where
  numerator := node187.numerator
  denominator := node187.denominator
  denominator_ne := node187.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((-1*(W z))+(4*((G z))^2)+(-8*(G z)*(atomA z))+(-8*(G z)*(u z))+(8*(G z)*(W z)*(atomA z))+(8*(G z)*(W z)*(u z)))) z=formula188 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154,formula155,formula156,formula157,formula158,formula159,formula160,formula161,formula162,formula163,formula164,formula165,formula166,formula167,formula168,formula169,formula170,formula171,formula172,formula173,formula174,formula175,formula176,formula177,formula178,formula179,formula180,formula181,formula182,formula183,formula184,formula185,formula186,formula187,formula188,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,atomPolynomial,endpointCubic,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node187.exact z hz)

/-- Article: exact actual-source identity double_square_coefficient3. -/
theorem double_square_coefficient3 {z : ℝ} (hz : z∈parameterInterval) : (((-1*(W z))+(4*((G z))^2)+(-8*(G z)*(atomA z))+(-8*(G z)*(u z))+(8*(G z)*(W z)*(atomA z))+(8*(G z)*(W z)*(u z))))=0 :=
  double_square_coefficient3Code.eq_zero (by kernel_decide) hz

/-- Article: exact source arithmetic node 189. -/
private def formula189 (z : ℝ) : ℝ := (G z)^10
private theorem node188Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,1099511627776,0,-5497558138880,0,12369505812480,0,-16492674416640,0,14431090114560,0,-8658654068736,0,3607772528640,0,-1030792151040,0,193273528320,0,-21474836480,0,1073741824]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node188Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 10 : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,1099511627776,0,-5497558138880,0,12369505812480,0,-16492674416640,0,14431090114560,0,-8658654068736,0,3607772528640,0,-1030792151040,0,193273528320,0,-21474836480,0,1073741824]⟩)
    ((⟨#[1048576,0,0,0,2621440,0,0,0,2949120,0,0,0,1966080,0,0,0,860160,0,0,0,258048,0,0,0,53760,0,0,0,7680,0,0,0,720,0,0,0,40,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 10))=true := by kernel_decide
private def node188 : RationalCode parameterInterval formula189 :=
  (GCode.pow 10)
  |>.recode ⟨#[1048576,0,0,0,2621440,0,0,0,2949120,0,0,0,1966080,0,0,0,860160,0,0,0,258048,0,0,0,53760,0,0,0,7680,0,0,0,720,0,0,0,40,0,0,0,1]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,1099511627776,0,-5497558138880,0,12369505812480,0,-16492674416640,0,14431090114560,0,-8658654068736,0,3607772528640,0,-1030792151040,0,193273528320,0,-21474836480,0,1073741824]⟩ node188Denominator node188Cross

/-- Article: exact source arithmetic node 190. -/
private def formula190 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-238685519872 : ℚ) : ℝ)) z)*(formula189 z)
private theorem node189Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node189Cross : polynomialCheck
    (((⟨#[-238685519872]⟩ : QPoly).mul (⟨#[1048576,0,0,0,2621440,0,0,0,2949120,0,0,0,1966080,0,0,0,860160,0,0,0,258048,0,0,0,53760,0,0,0,7680,0,0,0,720,0,0,0,40,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩)
    ((⟨#[-954742079488,0,0,0,-2386855198720,0,0,0,-2685212098560,0,0,0,-1790141399040,0,0,0,-783186862080,0,0,0,-234956058624,0,0,0,-48949178880,0,0,0,-6992739840,0,0,0,-655569360,0,0,0,-36420520,0,0,0,-910513]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,1099511627776,0,-5497558138880,0,12369505812480,0,-16492674416640,0,14431090114560,0,-8658654068736,0,3607772528640,0,-1030792151040,0,193273528320,0,-21474836480,0,1073741824]⟩ : QPoly)))=true := by kernel_decide
private def node189 : RationalCode parameterInterval formula190 :=
  ((RationalCode.constant parameterInterval (-238685519872)).mul node188)
  |>.recode ⟨#[-954742079488,0,0,0,-2386855198720,0,0,0,-2685212098560,0,0,0,-1790141399040,0,0,0,-783186862080,0,0,0,-234956058624,0,0,0,-48949178880,0,0,0,-6992739840,0,0,0,-655569360,0,0,0,-36420520,0,0,0,-910513]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ node189Denominator node189Cross

/-- Article: exact source arithmetic node 191. -/
private def formula191 (z : ℝ) : ℝ := ((fun _ : ℝ => ((229441 : ℚ) : ℝ)) z)+(formula190 z)
private theorem node190Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).toPoly≠0 :=
  node189Denominator
private theorem node190Cross : polynomialCheck
    ((((⟨#[229441]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly)).add ((⟨#[-954742079488,0,0,0,-2386855198720,0,0,0,-2685212098560,0,0,0,-1790141399040,0,0,0,-783186862080,0,0,0,-234956058624,0,0,0,-48949178880,0,0,0,-6992739840,0,0,0,-655569360,0,0,0,-36420520,0,0,0,-910513]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩)
    ((⟨#[-954742079488,0,0,0,-2386855198720,0,0,0,-2685212098560,0,962345304064,0,-6601867919360,0,10826384670720,0,-15218366423040,0,12630782115840,0,-7813425328128,0,3157695528960,0,-951147901440,0,169162260480,0,-25788546560,0,939790336,0,-655569360,0,0,0,-36420520,0,0,0,-910513]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly)))=true := by kernel_decide
private def node190 : RationalCode parameterInterval formula191 :=
  ((RationalCode.constant parameterInterval (229441)).add node189)
  |>.recode ⟨#[-954742079488,0,0,0,-2386855198720,0,0,0,-2685212098560,0,962345304064,0,-6601867919360,0,10826384670720,0,-15218366423040,0,12630782115840,0,-7813425328128,0,3157695528960,0,-951147901440,0,169162260480,0,-25788546560,0,939790336,0,-655569360,0,0,0,-36420520,0,0,0,-910513]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ node190Denominator node190Cross

/-- Article: exact source arithmetic node 192. -/
private def formula192 (z : ℝ) : ℝ := (G z)^6
private theorem node191Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,16777216,0,-50331648,0,62914560,0,-41943040,0,15728640,0,-3145728,0,262144]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node191Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 6 : QPoly).mul ⟨#[0,0,0,0,0,0,16777216,0,-50331648,0,62914560,0,-41943040,0,15728640,0,-3145728,0,262144]⟩)
    ((⟨#[4096,0,0,0,6144,0,0,0,3840,0,0,0,1280,0,0,0,240,0,0,0,24,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 6))=true := by kernel_decide
private def node191 : RationalCode parameterInterval formula192 :=
  (GCode.pow 6)
  |>.recode ⟨#[4096,0,0,0,6144,0,0,0,3840,0,0,0,1280,0,0,0,240,0,0,0,24,0,0,0,1]⟩ ⟨#[0,0,0,0,0,0,16777216,0,-50331648,0,62914560,0,-41943040,0,15728640,0,-3145728,0,262144]⟩ node191Denominator node191Cross

/-- Article: exact source arithmetic node 193. -/
private def formula193 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-6246545408 : ℚ) : ℝ)) z)*(formula192 z)
private theorem node192Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,8192,0,-24576,0,30720,0,-20480,0,7680,0,-1536,0,128]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node192Cross : polynomialCheck
    (((⟨#[-6246545408]⟩ : QPoly).mul (⟨#[4096,0,0,0,6144,0,0,0,3840,0,0,0,1280,0,0,0,240,0,0,0,24,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,0,0,0,8192,0,-24576,0,30720,0,-20480,0,7680,0,-1536,0,128]⟩)
    ((⟨#[-12493090816,0,0,0,-18739636224,0,0,0,-11712272640,0,0,0,-3904090880,0,0,0,-732017040,0,0,0,-73201704,0,0,0,-3050071]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,16777216,0,-50331648,0,62914560,0,-41943040,0,15728640,0,-3145728,0,262144]⟩ : QPoly)))=true := by kernel_decide
private def node192 : RationalCode parameterInterval formula193 :=
  ((RationalCode.constant parameterInterval (-6246545408)).mul node191)
  |>.recode ⟨#[-12493090816,0,0,0,-18739636224,0,0,0,-11712272640,0,0,0,-3904090880,0,0,0,-732017040,0,0,0,-73201704,0,0,0,-3050071]⟩ ⟨#[0,0,0,0,0,0,8192,0,-24576,0,30720,0,-20480,0,7680,0,-1536,0,128]⟩ node192Denominator node192Cross

/-- Article: exact source arithmetic node 194. -/
private def formula194 (z : ℝ) : ℝ := (formula191 z)+(formula193 z)
private theorem node193Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).toPoly≠0 :=
  node189Denominator
private theorem node193Cross : polynomialCheck
    ((((⟨#[-954742079488,0,0,0,-2386855198720,0,0,0,-2685212098560,0,962345304064,0,-6601867919360,0,10826384670720,0,-15218366423040,0,12630782115840,0,-7813425328128,0,3157695528960,0,-951147901440,0,169162260480,0,-25788546560,0,939790336,0,-655569360,0,0,0,-36420520,0,0,0,-910513]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,8192,0,-24576,0,30720,0,-20480,0,7680,0,-1536,0,128]⟩ : QPoly)).add ((⟨#[-12493090816,0,0,0,-18739636224,0,0,0,-11712272640,0,0,0,-3904090880,0,0,0,-732017040,0,0,0,-73201704,0,0,0,-3050071]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩)
    ((⟨#[-954742079488,0,0,0,-8783317696512,0,12792924995584,0,-21874599591936,0,23349964046336,0,-27390371037184,0,27617098727424,0,-26811954700288,0,19626912972800,0,-11561352572928,0,4906728243200,0,-1675747168768,0,431517167616,0,-106993636864,0,22802699264,0,-5340478416,0,780818176,0,-134022792,0,0,0,-910513]⟩ : QPoly).mul ((⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,8192,0,-24576,0,30720,0,-20480,0,7680,0,-1536,0,128]⟩ : QPoly)))=true := by kernel_decide
private def node193 : RationalCode parameterInterval formula194 :=
  (node190.add node192)
  |>.recode ⟨#[-954742079488,0,0,0,-8783317696512,0,12792924995584,0,-21874599591936,0,23349964046336,0,-27390371037184,0,27617098727424,0,-26811954700288,0,19626912972800,0,-11561352572928,0,4906728243200,0,-1675747168768,0,431517167616,0,-106993636864,0,22802699264,0,-5340478416,0,780818176,0,-134022792,0,0,0,-910513]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ node193Denominator node193Cross

/-- Article: exact source arithmetic node 195. -/
private def formula195 (z : ℝ) : ℝ := (G z)^4
private theorem node194Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,65536,0,-131072,0,98304,0,-32768,0,4096]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node194Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 4 : QPoly).mul ⟨#[0,0,0,0,65536,0,-131072,0,98304,0,-32768,0,4096]⟩)
    ((⟨#[256,0,0,0,256,0,0,0,96,0,0,0,16,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 4))=true := by kernel_decide
private def node194 : RationalCode parameterInterval formula195 :=
  (GCode.pow 4)
  |>.recode ⟨#[256,0,0,0,256,0,0,0,96,0,0,0,16,0,0,0,1]⟩ ⟨#[0,0,0,0,65536,0,-131072,0,98304,0,-32768,0,4096]⟩ node194Denominator node194Cross

/-- Article: exact source arithmetic node 196. -/
private def formula196 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-58821872 : ℚ) : ℝ)) z)*(formula195 z)
private theorem node195Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,4096,0,-8192,0,6144,0,-2048,0,256]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node195Cross : polynomialCheck
    (((⟨#[-58821872]⟩ : QPoly).mul (⟨#[256,0,0,0,256,0,0,0,96,0,0,0,16,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,0,4096,0,-8192,0,6144,0,-2048,0,256]⟩)
    ((⟨#[-941149952,0,0,0,-941149952,0,0,0,-352931232,0,0,0,-58821872,0,0,0,-3676367]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,0,65536,0,-131072,0,98304,0,-32768,0,4096]⟩ : QPoly)))=true := by kernel_decide
private def node195 : RationalCode parameterInterval formula196 :=
  ((RationalCode.constant parameterInterval (-58821872)).mul node194)
  |>.recode ⟨#[-941149952,0,0,0,-941149952,0,0,0,-352931232,0,0,0,-58821872,0,0,0,-3676367]⟩ ⟨#[0,0,0,0,4096,0,-8192,0,6144,0,-2048,0,256]⟩ node195Denominator node195Cross

/-- Article: exact source arithmetic node 197. -/
private def formula197 (z : ℝ) : ℝ := (formula194 z)+(formula196 z)
private theorem node196Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).toPoly≠0 :=
  node189Denominator
private theorem node196Cross : polynomialCheck
    ((((⟨#[-954742079488,0,0,0,-8783317696512,0,12792924995584,0,-21874599591936,0,23349964046336,0,-27390371037184,0,27617098727424,0,-26811954700288,0,19626912972800,0,-11561352572928,0,4906728243200,0,-1675747168768,0,431517167616,0,-106993636864,0,22802699264,0,-5340478416,0,780818176,0,-134022792,0,0,0,-910513]⟩ : QPoly).mul (⟨#[0,0,0,0,4096,0,-8192,0,6144,0,-2048,0,256]⟩ : QPoly)).add ((⟨#[-941149952,0,0,0,-941149952,0,0,0,-352931232,0,0,0,-58821872,0,0,0,-3676367]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩)
    ((⟨#[-954742079488,0,0,0,-8783317696512,0,11829187444736,0,-18983386939392,0,18772210679808,0,-22089814507520,0,22738177376256,0,-23137705287680,0,17292861091840,0,-10296447037440,0,4323215272960,0,-1446106580480,0,355284021504,0,-86288337920,0,18332236992,0,-4634615952,0,721996304,0,-134022792,0,0,0,-910513]⟩ : QPoly).mul ((⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).mul (⟨#[0,0,0,0,4096,0,-8192,0,6144,0,-2048,0,256]⟩ : QPoly)))=true := by kernel_decide
private def node196 : RationalCode parameterInterval formula197 :=
  (node193.add node195)
  |>.recode ⟨#[-954742079488,0,0,0,-8783317696512,0,11829187444736,0,-18983386939392,0,18772210679808,0,-22089814507520,0,22738177376256,0,-23137705287680,0,17292861091840,0,-10296447037440,0,4323215272960,0,-1446106580480,0,355284021504,0,-86288337920,0,18332236992,0,-4634615952,0,721996304,0,-134022792,0,0,0,-910513]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ node196Denominator node196Cross

/-- Article: exact source arithmetic node 198. -/
private def formula198 (z : ℝ) : ℝ := ((fun _ : ℝ => ((12933112 : ℚ) : ℝ)) z)*(formula100 z)
private theorem node197Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,32,0,-32,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node197Cross : polynomialCheck
    (((⟨#[12933112]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,32,0,-32,0,8]⟩)
    ((⟨#[25866224,0,0,0,12933112,0,0,0,1616639]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node197 : RationalCode parameterInterval formula198 :=
  ((RationalCode.constant parameterInterval (12933112)).mul node99)
  |>.recode ⟨#[25866224,0,0,0,12933112,0,0,0,1616639]⟩ ⟨#[0,0,32,0,-32,0,8]⟩ node197Denominator node197Cross

/-- Article: exact source arithmetic node 199. -/
private def formula199 (z : ℝ) : ℝ := (formula197 z)+(formula198 z)
private theorem node198Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).toPoly≠0 :=
  node189Denominator
private theorem node198Cross : polynomialCheck
    ((((⟨#[-954742079488,0,0,0,-8783317696512,0,11829187444736,0,-18983386939392,0,18772210679808,0,-22089814507520,0,22738177376256,0,-23137705287680,0,17292861091840,0,-10296447037440,0,4323215272960,0,-1446106580480,0,355284021504,0,-86288337920,0,18332236992,0,-4634615952,0,721996304,0,-134022792,0,0,0,-910513]⟩ : QPoly).mul (⟨#[0,0,32,0,-32,0,8]⟩ : QPoly)).add ((⟨#[25866224,0,0,0,12933112,0,0,0,1616639]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩)
    ((⟨#[-954742079488,0,0,0,-8783317696512,0,11829187444736,0,-15593049227264,0,5210859831296,0,3337718333440,0,-7774862032896,0,3773100302336,0,-1353996324864,0,86462205952,0,-338499081216,0,235818768896,0,-121482219264,0,13037962240,0,5088730304,0,-3806896784,0,721996304,0,-134022792,0,0,0,-910513]⟩ : QPoly).mul ((⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).mul (⟨#[0,0,32,0,-32,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node198 : RationalCode parameterInterval formula199 :=
  (node196.add node197)
  |>.recode ⟨#[-954742079488,0,0,0,-8783317696512,0,11829187444736,0,-15593049227264,0,5210859831296,0,3337718333440,0,-7774862032896,0,3773100302336,0,-1353996324864,0,86462205952,0,-338499081216,0,235818768896,0,-121482219264,0,13037962240,0,5088730304,0,-3806896784,0,721996304,0,-134022792,0,0,0,-910513]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ node198Denominator node198Cross

/-- Article: exact source arithmetic node 200. -/
private def formula200 (z : ℝ) : ℝ := (G z)^8
private theorem node199Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,4294967296,0,-17179869184,0,30064771072,0,-30064771072,0,18790481920,0,-7516192768,0,1879048192,0,-268435456,0,16777216]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node199Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 8 : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,4294967296,0,-17179869184,0,30064771072,0,-30064771072,0,18790481920,0,-7516192768,0,1879048192,0,-268435456,0,16777216]⟩)
    ((⟨#[65536,0,0,0,131072,0,0,0,114688,0,0,0,57344,0,0,0,17920,0,0,0,3584,0,0,0,448,0,0,0,32,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 8))=true := by kernel_decide
private def node199 : RationalCode parameterInterval formula200 :=
  (GCode.pow 8)
  |>.recode ⟨#[65536,0,0,0,131072,0,0,0,114688,0,0,0,57344,0,0,0,17920,0,0,0,3584,0,0,0,448,0,0,0,32,0,0,0,1]⟩ ⟨#[0,0,0,0,0,0,0,0,4294967296,0,-17179869184,0,30064771072,0,-30064771072,0,18790481920,0,-7516192768,0,1879048192,0,-268435456,0,16777216]⟩ node199Denominator node199Cross

/-- Article: exact source arithmetic node 201. -/
private def formula201 (z : ℝ) : ℝ := ((fun _ : ℝ => ((77668708352 : ℚ) : ℝ)) z)*(formula200 z)
private theorem node200Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,1048576,0,-4194304,0,7340032,0,-7340032,0,4587520,0,-1835008,0,458752,0,-65536,0,4096]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node200Cross : polynomialCheck
    (((⟨#[77668708352]⟩ : QPoly).mul (⟨#[65536,0,0,0,131072,0,0,0,114688,0,0,0,57344,0,0,0,17920,0,0,0,3584,0,0,0,448,0,0,0,32,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,1048576,0,-4194304,0,7340032,0,-7340032,0,4587520,0,-1835008,0,458752,0,-65536,0,4096]⟩)
    ((⟨#[1242699333632,0,0,0,2485398667264,0,0,0,2174723833856,0,0,0,1087361916928,0,0,0,339800599040,0,0,0,67960119808,0,0,0,8495014976,0,0,0,606786784,0,0,0,18962087]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,4294967296,0,-17179869184,0,30064771072,0,-30064771072,0,18790481920,0,-7516192768,0,1879048192,0,-268435456,0,16777216]⟩ : QPoly)))=true := by kernel_decide
private def node200 : RationalCode parameterInterval formula201 :=
  ((RationalCode.constant parameterInterval (77668708352)).mul node199)
  |>.recode ⟨#[1242699333632,0,0,0,2485398667264,0,0,0,2174723833856,0,0,0,1087361916928,0,0,0,339800599040,0,0,0,67960119808,0,0,0,8495014976,0,0,0,606786784,0,0,0,18962087]⟩ ⟨#[0,0,0,0,0,0,0,0,1048576,0,-4194304,0,7340032,0,-7340032,0,4587520,0,-1835008,0,458752,0,-65536,0,4096]⟩ node200Denominator node200Cross

/-- Article: exact source arithmetic node 202. -/
private def formula202 (z : ℝ) : ℝ := (formula199 z)+(formula201 z)
private theorem node201Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).toPoly≠0 :=
  node189Denominator
private theorem node201Cross : polynomialCheck
    ((((⟨#[-954742079488,0,0,0,-8783317696512,0,11829187444736,0,-15593049227264,0,5210859831296,0,3337718333440,0,-7774862032896,0,3773100302336,0,-1353996324864,0,86462205952,0,-338499081216,0,235818768896,0,-121482219264,0,13037962240,0,5088730304,0,-3806896784,0,721996304,0,-134022792,0,0,0,-910513]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1048576,0,-4194304,0,7340032,0,-7340032,0,4587520,0,-1835008,0,458752,0,-65536,0,4096]⟩ : QPoly)).add ((⟨#[1242699333632,0,0,0,2485398667264,0,0,0,2174723833856,0,0,0,1087361916928,0,0,0,339800599040,0,0,0,67960119808,0,0,0,8495014976,0,0,0,606786784,0,0,0,18962087]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩)
    ((⟨#[-954742079488,0,4970797334528,0,-13754115031040,0,23013481447424,0,-25534643896320,0,16395153833984,0,-5361177001984,0,-1250690531328,0,-576347365376,0,1092567988224,0,-1272740190208,0,273141997056,0,-36021710336,0,-19542039552,0,-20942097664,0,16010892416,0,-6234043920,0,1404631436,0,-209871140,0,18962087,0,-910513]⟩ : QPoly).mul ((⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1048576,0,-4194304,0,7340032,0,-7340032,0,4587520,0,-1835008,0,458752,0,-65536,0,4096]⟩ : QPoly)))=true := by kernel_decide
private def node201 : RationalCode parameterInterval formula202 :=
  (node198.add node200)
  |>.recode ⟨#[-954742079488,0,4970797334528,0,-13754115031040,0,23013481447424,0,-25534643896320,0,16395153833984,0,-5361177001984,0,-1250690531328,0,-576347365376,0,1092567988224,0,-1272740190208,0,273141997056,0,-36021710336,0,-19542039552,0,-20942097664,0,16010892416,0,-6234043920,0,1404631436,0,-209871140,0,18962087,0,-910513]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ node201Denominator node201Cross

/-- Article: exact source arithmetic node 203. -/
private def formula203 (z : ℝ) : ℝ := (G z)^12
private theorem node202Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,281474976710656,0,-1688849860263936,0,4644337115725824,0,-7740561859543040,0,8708132091985920,0,-6966505673588736,0,4063794976260096,0,-1741626418397184,0,544258255749120,0,-120946279055360,0,18141941858304,0,-1649267441664,0,68719476736]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node202Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 12 : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,281474976710656,0,-1688849860263936,0,4644337115725824,0,-7740561859543040,0,8708132091985920,0,-6966505673588736,0,4063794976260096,0,-1741626418397184,0,544258255749120,0,-120946279055360,0,18141941858304,0,-1649267441664,0,68719476736]⟩)
    ((⟨#[16777216,0,0,0,50331648,0,0,0,69206016,0,0,0,57671680,0,0,0,32440320,0,0,0,12976128,0,0,0,3784704,0,0,0,811008,0,0,0,126720,0,0,0,14080,0,0,0,1056,0,0,0,48,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 12))=true := by kernel_decide
private def node202 : RationalCode parameterInterval formula203 :=
  (GCode.pow 12)
  |>.recode ⟨#[16777216,0,0,0,50331648,0,0,0,69206016,0,0,0,57671680,0,0,0,32440320,0,0,0,12976128,0,0,0,3784704,0,0,0,811008,0,0,0,126720,0,0,0,14080,0,0,0,1056,0,0,0,48,0,0,0,1]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,281474976710656,0,-1688849860263936,0,4644337115725824,0,-7740561859543040,0,8708132091985920,0,-6966505673588736,0,4063794976260096,0,-1741626418397184,0,544258255749120,0,-120946279055360,0,18141941858304,0,-1649267441664,0,68719476736]⟩ node202Denominator node202Cross

/-- Article: exact source arithmetic node 204. -/
private def formula204 (z : ℝ) : ℝ := ((fun _ : ℝ => ((162529280000 : ℚ) : ℝ)) z)*(formula203 z)
private theorem node203Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node203Cross : polynomialCheck
    (((⟨#[162529280000]⟩ : QPoly).mul (⟨#[16777216,0,0,0,50331648,0,0,0,69206016,0,0,0,57671680,0,0,0,32440320,0,0,0,12976128,0,0,0,3784704,0,0,0,811008,0,0,0,126720,0,0,0,14080,0,0,0,1056,0,0,0,48,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩)
    ((⟨#[325058560000,0,0,0,975175680000,0,0,0,1340866560000,0,0,0,1117388800000,0,0,0,628531200000,0,0,0,251412480000,0,0,0,73328640000,0,0,0,15713280000,0,0,0,2455200000,0,0,0,272800000,0,0,0,20460000,0,0,0,930000,0,0,0,19375]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,281474976710656,0,-1688849860263936,0,4644337115725824,0,-7740561859543040,0,8708132091985920,0,-6966505673588736,0,4063794976260096,0,-1741626418397184,0,544258255749120,0,-120946279055360,0,18141941858304,0,-1649267441664,0,68719476736]⟩ : QPoly)))=true := by kernel_decide
private def node203 : RationalCode parameterInterval formula204 :=
  ((RationalCode.constant parameterInterval (162529280000)).mul node202)
  |>.recode ⟨#[325058560000,0,0,0,975175680000,0,0,0,1340866560000,0,0,0,1117388800000,0,0,0,628531200000,0,0,0,251412480000,0,0,0,73328640000,0,0,0,15713280000,0,0,0,2455200000,0,0,0,272800000,0,0,0,20460000,0,0,0,930000,0,0,0,19375]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩ node203Denominator node203Cross

/-- Article: exact source arithmetic node 205. -/
private def formula205 (z : ℝ) : ℝ := (formula202 z)+(formula204 z)
private theorem node204Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩ : QPoly).toPoly≠0 :=
  node203Denominator
private theorem node204Cross : polynomialCheck
    ((((⟨#[-954742079488,0,4970797334528,0,-13754115031040,0,23013481447424,0,-25534643896320,0,16395153833984,0,-5361177001984,0,-1250690531328,0,-576347365376,0,1092567988224,0,-1272740190208,0,273141997056,0,-36021710336,0,-19542039552,0,-20942097664,0,16010892416,0,-6234043920,0,1404631436,0,-209871140,0,18962087,0,-910513]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩ : QPoly)).add ((⟨#[325058560000,0,0,0,975175680000,0,0,0,1340866560000,0,0,0,1117388800000,0,0,0,628531200000,0,0,0,251412480000,0,0,0,73328640000,0,0,0,15713280000,0,0,0,2455200000,0,0,0,272800000,0,0,0,20460000,0,0,0,930000,0,0,0,19375]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩)
    ((⟨#[325058560000,0,-7637936635904,0,48379490992128,0,-151708783083520,0,305423233056768,0,-415893232812032,0,382582733537280,0,-225119934480384,0,66302730633216,0,-5327608676352,0,11101354246144,0,-20075160158208,0,14625522114560,0,-5018790039552,0,693834640384,0,-83243885568,0,258995041536,0,-219843686016,0,93403987680,0,-25384108448,0,4660388688,0,-578723080,0,46138278,0,-1821026,0,19375]⟩ : QPoly).mul ((⟨#[0,0,0,0,0,0,0,0,0,0,4194304,0,-20971520,0,47185920,0,-62914560,0,55050240,0,-33030144,0,13762560,0,-3932160,0,737280,0,-81920,0,4096]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩ : QPoly)))=true := by kernel_decide
private def node204 : RationalCode parameterInterval formula205 :=
  (node201.add node203)
  |>.recode ⟨#[325058560000,0,-7637936635904,0,48379490992128,0,-151708783083520,0,305423233056768,0,-415893232812032,0,382582733537280,0,-225119934480384,0,66302730633216,0,-5327608676352,0,11101354246144,0,-20075160158208,0,14625522114560,0,-5018790039552,0,693834640384,0,-83243885568,0,258995041536,0,-219843686016,0,93403987680,0,-25384108448,0,4660388688,0,-578723080,0,46138278,0,-1821026,0,19375]⟩ ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,33554432,0,-201326592,0,553648128,0,-922746880,0,1038090240,0,-830472192,0,484442112,0,-207618048,0,64880640,0,-14417920,0,2162688,0,-196608,0,8192]⟩ node204Denominator node204Cross

/-- Article: exact coefficient representation of the independently specified haComposition source. -/
def haCompositionCode : RationalCode parameterInterval (fun z : ℝ => Ha (G z)) where
  numerator := node204.numerator
  denominator := node204.denominator
  denominator_ne := node204.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => Ha (G z)) z=formula205 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154,formula155,formula156,formula157,formula158,formula159,formula160,formula161,formula162,formula163,formula164,formula165,formula166,formula167,formula168,formula169,formula170,formula171,formula172,formula173,formula174,formula175,formula176,formula177,formula178,formula179,formula180,formula181,formula182,formula183,formula184,formula185,formula186,formula187,formula188,formula189,formula190,formula191,formula192,formula193,formula194,formula195,formula196,formula197,formula198,formula199,formula200,formula201,formula202,formula203,formula204,formula205,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,atomPolynomial,endpointCubic,id_eq,Ha,Boundary.spiralSwitch]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node204.exact z hz)

/-- Article: checked divisibility of the actual composed source numerator. -/
theorem haComposition_modular {z : ℝ} (hz : z∈parameterInterval) (hr : N12 z=0) : (Ha (G z))=0 := by
  have hc : Numerics.remainderCodeCheck haCompositionCode.numerator endpointPolynomialCode.code ⟨#[203161600,1275854848,-345112576,-18485084160,-48511287296,-29594845184,65077313536,101223776256,-38432956416,-177722195968,-81128030208,128052953088,166693517312,40873752576,-45469732864,-28856390656,10926922240,23742022656,19578573824,11871011328,2731730560,-3607048832,-2841858304,1277304768,2604586208,1000413696,-316906368,-347113664,-37532184,49425672,15888016,-3612652,-2960894,-564120,-5266,9734,775]⟩ QPoly.zero=true := by kernel_decide
  have hd : aeval z endpointPolynomialCode.code.toPoly=0 := by
    rw [endpointPolynomialCode.exact]
    rw [endpointPolynomial_eval,hr]
  have he := Numerics.eval_at_root_of_code hc hd
  rw [haCompositionCode.exact z hz,he]
  simp [QPoly.toPoly_zero]

/-- Article: exact source arithmetic node 206. -/
private def formula206 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-36 : ℚ) : ℝ)) z)*(formula100 z)
private theorem node205Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
private theorem node205Cross : polynomialCheck
    (((⟨#[-36]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[-144,0,0,0,-72,0,0,0,-9]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node205 : RationalCode parameterInterval formula206 :=
  ((RationalCode.constant parameterInterval (-36)).mul node99)
  |>.recode ⟨#[-144,0,0,0,-72,0,0,0,-9]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node205Denominator node205Cross

/-- Article: exact source arithmetic node 207. -/
private def formula207 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)+(formula206 z)
private theorem node206Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
private theorem node206Cross : polynomialCheck
    ((((⟨#[-1]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)).add ((⟨#[-144,0,0,0,-72,0,0,0,-9]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[-144,0,-64,0,-8,0,-16,0,-9]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node206 : RationalCode parameterInterval formula207 :=
  ((RationalCode.constant parameterInterval (-1)).add node205)
  |>.recode ⟨#[-144,0,-64,0,-8,0,-16,0,-9]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node206Denominator node206Cross

/-- Article: exact source arithmetic node 208. -/
private def formula208 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(G z)
private theorem node207Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  node137Denominator
private theorem node207Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-4,0,2]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node207 : RationalCode parameterInterval formula208 :=
  ((RationalCode.constant parameterInterval (4)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-4,0,2]⟩ node207Denominator node207Cross

/-- Article: exact source arithmetic node 209. -/
private def formula209 (z : ℝ) : ℝ := (formula207 z)+(formula208 z)
private theorem node208Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
private theorem node208Cross : polynomialCheck
    ((((⟨#[-144,0,-64,0,-8,0,-16,0,-9]⟩ : QPoly).mul (⟨#[0,-4,0,2]⟩ : QPoly)).add ((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[-144,-64,-64,32,-8,-16,-16,8,-9]⟩ : QPoly).mul ((⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).mul (⟨#[0,-4,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node208 : RationalCode parameterInterval formula209 :=
  (node206.add node207)
  |>.recode ⟨#[-144,-64,-64,32,-8,-16,-16,8,-9]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node208Denominator node208Cross

/-- Article: exact source arithmetic node 210. -/
private def formula210 (z : ℝ) : ℝ := ((fun _ : ℝ => ((32 : ℚ) : ℝ)) z)*(formula81 z)
private theorem node209Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node209Cross : polynomialCheck
    (((⟨#[32]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩)
    ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly)))=true := by kernel_decide
private def node209 : RationalCode parameterInterval formula210 :=
  ((RationalCode.constant parameterInterval (32)).mul node80)
  |>.recode ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ ⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩ node209Denominator node209Cross

/-- Article: exact source arithmetic node 211. -/
private def formula211 (z : ℝ) : ℝ := (formula209 z)+(formula210 z)
private theorem node210Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩ : QPoly).toPoly≠0 :=
  node209Denominator
private theorem node210Cross : polynomialCheck
    ((((⟨#[-144,-64,-64,32,-8,-16,-16,8,-9]⟩ : QPoly).mul (⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩ : QPoly)).add ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩)
    ((⟨#[64,288,128,-16,-80,-48,64,24,-20,2,8,-9,1]⟩ : QPoly).mul ((⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).mul (⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node210 : RationalCode parameterInterval formula211 :=
  (node208.add node209)
  |>.recode ⟨#[64,288,128,-16,-80,-48,64,24,-20,2,8,-9,1]⟩ ⟨#[0,0,0,-128,0,192,0,-96,0,16]⟩ node210Denominator node210Cross

/-- Article: exact coefficient representation of the independently specified switchComposition source. -/
def switchCompositionCode : RationalCode parameterInterval (fun z : ℝ => Boundary.spiralSwitch (G z)) where
  numerator := node210.numerator
  denominator := node210.denominator
  denominator_ne := node210.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => Boundary.spiralSwitch (G z)) z=formula211 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154,formula155,formula156,formula157,formula158,formula159,formula160,formula161,formula162,formula163,formula164,formula165,formula166,formula167,formula168,formula169,formula170,formula171,formula172,formula173,formula174,formula175,formula176,formula177,formula178,formula179,formula180,formula181,formula182,formula183,formula184,formula185,formula186,formula187,formula188,formula189,formula190,formula191,formula192,formula193,formula194,formula195,formula196,formula197,formula198,formula199,formula200,formula201,formula202,formula203,formula204,formula205,formula206,formula207,formula208,formula209,formula210,formula211,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,N10,eMinus,ePlus,meanRootFactor,atomPolynomial,endpointCubic,id_eq,Ha,Boundary.spiralSwitch]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node210.exact z hz)

/-- Article: checked divisibility of the actual composed source numerator. -/
theorem switchComposition_modular {z : ℝ} (hz : z∈parameterInterval) (hr : endpointCubic z=0) : (Boundary.spiralSwitch (G z))=0 := by
  have hc : Numerics.remainderCodeCheck switchCompositionCode.numerator Numerics.transitionCubicCode.code ⟨#[-32,-144,-48,64,-8,-32,4,0,-8,1]⟩ QPoly.zero=true := by kernel_decide
  have hd : aeval z Numerics.transitionCubicCode.code.toPoly=0 := by
    rw [Numerics.transitionCubicCode.exact]
    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using hr
  have he := Numerics.eval_at_root_of_code hc hd
  rw [switchCompositionCode.exact z hz,he]
  simp [QPoly.toPoly_zero]

end
end polyak.Boundary.P2
