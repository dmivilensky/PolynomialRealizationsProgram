import polyak.Numerics.KernelDecide
import polyak.Certificates.P2Codes
import polyak.Boundary.P2.Roots

/-! Article: (p2endpoint). Exact modular identities at the actual cubic endpoint. -/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
/-- Article: exact source arithmetic node 1. -/
private def formula1 (z : ℝ) : ℝ := (G z)⁻¹
private theorem node0Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node0Cross : polynomialCheck
    ((⟨#[0,-16,0,8]⟩ : QPoly).mul ⟨#[4,0,0,0,1]⟩)
    ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩))=true := by kernel_decide
private def node0 : RationalCode parameterInterval formula1 :=
  (GCode.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[0,-16,0,8]⟩ ⟨#[4,0,0,0,1]⟩ node0Denominator node0Cross

/-- Article: exact source arithmetic node 2. -/
private def formula2 (z : ℝ) : ℝ := (formula1 z)^2
private theorem node1Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node1Cross : polynomialCheck
    ((polynomialPower ⟨#[0,-16,0,8]⟩ 2 : QPoly).mul ⟨#[16,0,0,0,8,0,0,0,1]⟩)
    ((⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).mul (polynomialPower ⟨#[4,0,0,0,1]⟩ 2))=true := by kernel_decide
private def node1 : RationalCode parameterInterval formula2 :=
  (node0.pow 2)
  |>.recode ⟨#[0,0,256,0,-256,0,64]⟩ ⟨#[16,0,0,0,8,0,0,0,1]⟩ node1Denominator node1Cross

/-- Article: exact source arithmetic node 3. -/
private def formula3 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/4) : ℚ) : ℝ)) z)*(formula2 z)
private theorem node2Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node2Cross : polynomialCheck
    (((⟨#[(1/4)]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly) : QPoly).mul ⟨#[16,0,0,0,8,0,0,0,1]⟩)
    ((⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node2 : RationalCode parameterInterval formula3 :=
  ((RationalCode.constant parameterInterval ((1/4))).mul node1)
  |>.recode ⟨#[0,0,64,0,-64,0,16]⟩ ⟨#[16,0,0,0,8,0,0,0,1]⟩ node2Denominator node2Cross

/-- Article: exact source arithmetic node 4. -/
private def formula4 (z : ℝ) : ℝ := (atomB z)+(formula3 z)
private theorem node3Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node3Cross : polynomialCheck
    ((((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly)).add ((⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩)
    ((⟨#[0,-384,1152,-512,-448,-288,576,-256,288,-72,-56,-32,36,-6]⟩ : QPoly).mul ((⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node3 : RationalCode parameterInterval formula4 :=
  (atomBCode.add node2)
  |>.recode ⟨#[0,-384,1152,-512,-448,-288,576,-256,288,-72,-56,-32,36,-6]⟩ ⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩ node3Denominator node3Cross

/-- Article: exact source arithmetic node 5. -/
private def formula5 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-1/2) : ℚ) : ℝ)) z)*(atomA z)
private theorem node4Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,0,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node4Cross : polynomialCheck
    (((⟨#[(-1/2)]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,0,0,4]⟩)
    ((⟨#[-8,24,-36,32,-18,6,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node4 : RationalCode parameterInterval formula5 :=
  ((RationalCode.constant parameterInterval ((-1/2))).mul atomACode)
  |>.recode ⟨#[-8,24,-36,32,-18,6,-1]⟩ ⟨#[0,-16,0,0,0,4]⟩ node4Denominator node4Cross

/-- Article: exact source arithmetic node 6. -/
private def formula6 (z : ℝ) : ℝ := (G z)⁻¹
private theorem node5Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node0Denominator
private theorem node5Cross : polynomialCheck
    ((⟨#[0,-16,0,8]⟩ : QPoly).mul ⟨#[4,0,0,0,1]⟩)
    ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩))=true := by kernel_decide
private def node5 : RationalCode parameterInterval formula6 :=
  (GCode.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[0,-16,0,8]⟩ ⟨#[4,0,0,0,1]⟩ node5Denominator node5Cross

/-- Article: exact source arithmetic node 7. -/
private def formula7 (z : ℝ) : ℝ := (formula5 z)*(formula6 z)
private theorem node6Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,4,4,2,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node6Cross : polynomialCheck
    (((⟨#[-8,24,-36,32,-18,6,-1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly) : QPoly).mul ⟨#[4,4,4,2,1]⟩)
    ((⟨#[-8,16,-16,8,-2]⟩ : QPoly).mul ((⟨#[0,-16,0,0,0,4]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node6 : RationalCode parameterInterval formula7 :=
  (node4.mul node5)
  |>.recode ⟨#[-8,16,-16,8,-2]⟩ ⟨#[4,4,4,2,1]⟩ node6Denominator node6Cross

/-- Article: exact source arithmetic node 8. -/
private def formula8 (z : ℝ) : ℝ := (formula4 z)+(formula7 z)
private theorem node7Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node3Denominator
private theorem node7Cross : polynomialCheck
    ((((⟨#[0,-384,1152,-512,-448,-288,576,-256,288,-72,-56,-32,36,-6]⟩ : QPoly).mul (⟨#[4,4,4,2,1]⟩ : QPoly)).add ((⟨#[-8,16,-16,8,-2]⟩ : QPoly).mul (⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩)
    ((⟨#[-256,384,256,-256,0,-736,608,-128,304,-184,0,-16,8,6,-2]⟩ : QPoly).mul ((⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩ : QPoly).mul (⟨#[4,4,4,2,1]⟩ : QPoly)))=true := by kernel_decide
private def node7 : RationalCode parameterInterval formula8 :=
  (node3.add node6)
  |>.recode ⟨#[-256,384,256,-256,0,-736,608,-128,304,-184,0,-16,8,6,-2]⟩ ⟨#[128,0,-64,0,32,0,-16,0,-8,0,4,0,-2,0,1]⟩ node7Denominator node7Cross

/-- Article: exact coefficient representation of the independently specified lowerCandidate source. -/
def lowerCandidateCode : RationalCode parameterInterval (fun z : ℝ => atomPolynomial z (-1/(2*G z))) where
  numerator := node7.numerator
  denominator := node7.denominator
  denominator_ne := node7.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => atomPolynomial z (-1/(2*G z))) z=formula8 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,atomPolynomial,Boundary.spiralWeight]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node7.exact z hz)

/-- Article: exact rational endpoint identity lowerCandidate at the source cubic root. -/
theorem lowerCandidate_at_zeta1 : (atomPolynomial zeta1 (-1/(2*G zeta1)))=0 := by
  have hc : Numerics.remainderCodeCheck lowerCandidateCode.numerator Numerics.transitionCubicCode.code ⟨#[128,-192,-192,288,0,128,-160,0,-8,12,4,-2]⟩ QPoly.zero=true := by kernel_decide
  have hd : aeval zeta1 Numerics.transitionCubicCode.code.toPoly=0 := by
    rw [Numerics.transitionCubicCode.exact]
    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using endpointCubic_zeta1
  have he := Numerics.eval_at_root_of_code hc hd
  have h := lowerCandidateCode.exact zeta1 zeta1_mem
  rw [he] at h
  simpa [QPoly.toPoly_zero] using h

/-- Article: exact source arithmetic node 9. -/
private def formula9 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/16) : ℚ) : ℝ)) z)*(formula2 z)
private theorem node8Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node8Cross : polynomialCheck
    (((⟨#[(1/16)]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly) : QPoly).mul ⟨#[16,0,0,0,8,0,0,0,1]⟩)
    ((⟨#[0,0,16,0,-16,0,4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node8 : RationalCode parameterInterval formula9 :=
  ((RationalCode.constant parameterInterval ((1/16))).mul node1)
  |>.recode ⟨#[0,0,16,0,-16,0,4]⟩ ⟨#[16,0,0,0,8,0,0,0,1]⟩ node8Denominator node8Cross

/-- Article: exact source arithmetic node 10. -/
private def formula10 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(G z)
private theorem node9Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node9Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node9 : RationalCode parameterInterval formula10 :=
  ((RationalCode.constant parameterInterval (2)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-8,0,4]⟩ node9Denominator node9Cross

/-- Article: exact source arithmetic node 11. -/
private def formula11 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)+(formula10 z)
private theorem node10Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  node9Denominator
private theorem node10Cross : polynomialCheck
    ((((⟨#[-1]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)).add ((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,-8,0,4]⟩)
    ((⟨#[4,8,0,-4,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node10 : RationalCode parameterInterval formula11 :=
  ((RationalCode.constant parameterInterval (-1)).add node9)
  |>.recode ⟨#[4,8,0,-4,1]⟩ ⟨#[0,-8,0,4]⟩ node10Denominator node10Cross

/-- Article: exact source arithmetic node 12. -/
private def formula12 (z : ℝ) : ℝ := (formula11 z)^2
private theorem node11Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node11Cross : polynomialCheck
    ((polynomialPower ⟨#[4,8,0,-4,1]⟩ 2 : QPoly).mul ⟨#[0,0,64,0,-64,0,16]⟩)
    ((⟨#[16,64,64,-32,-56,16,16,-8,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-8,0,4]⟩ 2))=true := by kernel_decide
private def node11 : RationalCode parameterInterval formula12 :=
  (node10.pow 2)
  |>.recode ⟨#[16,64,64,-32,-56,16,16,-8,1]⟩ ⟨#[0,0,64,0,-64,0,16]⟩ node11Denominator node11Cross

/-- Article: exact source arithmetic node 13. -/
private def formula13 (z : ℝ) : ℝ := (formula9 z)*(formula12 z)
private theorem node12Denominator : ∀ z∈parameterInterval, aeval z (⟨#[64,0,0,0,32,0,0,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node12Cross : polynomialCheck
    (((⟨#[0,0,16,0,-16,0,4]⟩ : QPoly).mul (⟨#[16,64,64,-32,-56,16,16,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[64,0,0,0,32,0,0,0,4]⟩)
    ((⟨#[16,64,64,-32,-56,16,16,-8,1]⟩ : QPoly).mul ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,64,0,-64,0,16]⟩ : QPoly)))=true := by kernel_decide
private def node12 : RationalCode parameterInterval formula13 :=
  (node8.mul node11)
  |>.recode ⟨#[16,64,64,-32,-56,16,16,-8,1]⟩ ⟨#[64,0,0,0,32,0,0,0,4]⟩ node12Denominator node12Cross

/-- Article: exact source arithmetic node 14. -/
private def formula14 (z : ℝ) : ℝ := (atomB z)+(formula13 z)
private theorem node13Denominator : ∀ z∈parameterInterval, aeval z (⟨#[512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node13Cross : polynomialCheck
    ((((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul (⟨#[64,0,0,0,32,0,0,0,4]⟩ : QPoly)).add ((⟨#[16,64,64,-32,-56,16,16,-8,1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩)
    ((⟨#[128,-1024,3008,-2560,544,-1024,1520,-1024,760,-320,68,-96,94,-32,1]⟩ : QPoly).mul ((⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).mul (⟨#[64,0,0,0,32,0,0,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node13 : RationalCode parameterInterval formula14 :=
  (atomBCode.add node12)
  |>.recode ⟨#[128,-1024,3008,-2560,544,-1024,1520,-1024,760,-320,68,-96,94,-32,1]⟩ ⟨#[512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩ node13Denominator node13Cross

/-- Article: exact source arithmetic node 15. -/
private def formula15 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/4) : ℚ) : ℝ)) z)*(atomA z)
private theorem node14Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-32,0,0,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node14Cross : polynomialCheck
    (((⟨#[(1/4)]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-32,0,0,0,8]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-8,0,0,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node14 : RationalCode parameterInterval formula15 :=
  ((RationalCode.constant parameterInterval ((1/4))).mul atomACode)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[0,-32,0,0,0,8]⟩ node14Denominator node14Cross

/-- Article: exact source arithmetic node 16. -/
private def formula16 (z : ℝ) : ℝ := (formula15 z)*(formula6 z)
private theorem node15Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,4,4,2,1]⟩ : QPoly).toPoly≠0 :=
  node6Denominator
private theorem node15Cross : polynomialCheck
    (((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly) : QPoly).mul ⟨#[4,4,4,2,1]⟩)
    ((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul ((⟨#[0,-32,0,0,0,8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node15 : RationalCode parameterInterval formula16 :=
  (node14.mul node5)
  |>.recode ⟨#[4,-8,8,-4,1]⟩ ⟨#[4,4,4,2,1]⟩ node15Denominator node15Cross

/-- Article: exact source arithmetic node 17. -/
private def formula17 (z : ℝ) : ℝ := (formula16 z)*(formula11 z)
private theorem node16Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-32,-32,-16,0,8,8,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node16Cross : polynomialCheck
    (((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul (⟨#[4,8,0,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-32,-32,-16,0,8,8,4]⟩)
    ((⟨#[16,0,-32,32,8,-32,24,-8,1]⟩ : QPoly).mul ((⟨#[4,4,4,2,1]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node16 : RationalCode parameterInterval formula17 :=
  (node15.mul node10)
  |>.recode ⟨#[16,0,-32,32,8,-32,24,-8,1]⟩ ⟨#[0,-32,-32,-16,0,8,8,4]⟩ node16Denominator node16Cross

/-- Article: exact source arithmetic node 18. -/
private def formula18 (z : ℝ) : ℝ := (formula14 z)+(formula17 z)
private theorem node17Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node17Cross : polynomialCheck
    ((((⟨#[128,-1024,3008,-2560,544,-1024,1520,-1024,760,-320,68,-96,94,-32,1]⟩ : QPoly).mul (⟨#[0,-32,-32,-16,0,8,8,4]⟩ : QPoly)).add ((⟨#[16,0,-32,32,8,-32,24,-8,1]⟩ : QPoly).mul (⟨#[512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩ : QPoly)) : QPoly).mul ⟨#[0,512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩)
    ((⟨#[-256,384,-512,1856,-2176,1504,-2176,1808,-768,680,-480,172,-56,18,8,-9,1]⟩ : QPoly).mul ((⟨#[512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩ : QPoly).mul (⟨#[0,-32,-32,-16,0,8,8,4]⟩ : QPoly)))=true := by kernel_decide
private def node17 : RationalCode parameterInterval formula18 :=
  (node13.add node16)
  |>.recode ⟨#[-256,384,-512,1856,-2176,1504,-2176,1808,-768,680,-480,172,-56,18,8,-9,1]⟩ ⟨#[0,512,0,-256,0,128,0,-64,0,-32,0,16,0,-8,0,4]⟩ node17Denominator node17Cross

/-- Article: exact coefficient representation of the independently specified upperCandidate source. -/
def upperCandidateCode : RationalCode parameterInterval (fun z : ℝ => atomPolynomial z ((2*G z-1)/(4*G z))) where
  numerator := node17.numerator
  denominator := node17.denominator
  denominator_ne := node17.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => atomPolynomial z ((2*G z-1)/(4*G z))) z=formula18 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,atomPolynomial,Boundary.spiralWeight]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node17.exact z hz)

/-- Article: exact rational endpoint identity upperCandidate at the source cubic root. -/
theorem upperCandidate_at_zeta1 : (atomPolynomial zeta1 ((2*G zeta1-1)/(4*G zeta1)))=0 := by
  have hc : Numerics.remainderCodeCheck upperCandidateCode.numerator Numerics.transitionCubicCode.code ⟨#[128,-192,192,-768,896,-272,256,-320,120,-52,20,0,-8,1]⟩ QPoly.zero=true := by kernel_decide
  have hd : aeval zeta1 Numerics.transitionCubicCode.code.toPoly=0 := by
    rw [Numerics.transitionCubicCode.exact]
    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using endpointCubic_zeta1
  have he := Numerics.eval_at_root_of_code hc hd
  have h := upperCandidateCode.exact zeta1 zeta1_mem
  rw [he] at h
  simpa [QPoly.toPoly_zero] using h

/-- Article: exact source arithmetic node 19. -/
private def formula19 (z : ℝ) : ℝ := (G z)⁻¹
private theorem node18Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node0Denominator
private theorem node18Cross : polynomialCheck
    ((⟨#[0,-16,0,8]⟩ : QPoly).mul ⟨#[4,0,0,0,1]⟩)
    ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩))=true := by kernel_decide
private def node18 : RationalCode parameterInterval formula19 :=
  (GCode.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[0,-16,0,8]⟩ ⟨#[4,0,0,0,1]⟩ node18Denominator node18Cross

/-- Article: exact source arithmetic node 20. -/
private def formula20 (z : ℝ) : ℝ := (formula19 z)^3
private theorem node19Denominator : ∀ z∈parameterInterval, aeval z (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node19Cross : polynomialCheck
    ((polynomialPower ⟨#[0,-16,0,8]⟩ 3 : QPoly).mul ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩)
    ((⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly).mul (polynomialPower ⟨#[4,0,0,0,1]⟩ 3))=true := by kernel_decide
private def node19 : RationalCode parameterInterval formula20 :=
  (node18.pow 3)
  |>.recode ⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ node19Denominator node19Cross

/-- Article: exact source arithmetic node 21. -/
private def formula21 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-1/2) : ℚ) : ℝ)) z)*(formula20 z)
private theorem node20Denominator : ∀ z∈parameterInterval, aeval z (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node19Denominator
private theorem node20Cross : polynomialCheck
    (((⟨#[(-1/2)]⟩ : QPoly).mul (⟨#[0,0,0,-4096,0,6144,0,-3072,0,512]⟩ : QPoly) : QPoly).mul ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩)
    ((⟨#[0,0,0,2048,0,-3072,0,1536,0,-256]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node20 : RationalCode parameterInterval formula21 :=
  ((RationalCode.constant parameterInterval ((-1/2))).mul node19)
  |>.recode ⟨#[0,0,0,2048,0,-3072,0,1536,0,-256]⟩ ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ node20Denominator node20Cross

/-- Article: exact source arithmetic node 22. -/
private def formula22 (z : ℝ) : ℝ := (G z)^2
private theorem node21Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node21Cross : polynomialCheck
    ((polynomialPower ⟨#[4,0,0,0,1]⟩ 2 : QPoly).mul ⟨#[0,0,256,0,-256,0,64]⟩)
    ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[0,-16,0,8]⟩ 2))=true := by kernel_decide
private def node21 : RationalCode parameterInterval formula22 :=
  (GCode.pow 2)
  |>.recode ⟨#[16,0,0,0,8,0,0,0,1]⟩ ⟨#[0,0,256,0,-256,0,64]⟩ node21Denominator node21Cross

/-- Article: exact source arithmetic node 23. -/
private def formula23 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)+(formula22 z)
private theorem node22Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly).toPoly≠0 :=
  node21Denominator
private theorem node22Cross : polynomialCheck
    ((((⟨#[-1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)).add ((⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,256,0,-256,0,64]⟩)
    ((⟨#[16,0,-256,0,264,0,-64,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node22 : RationalCode parameterInterval formula23 :=
  ((RationalCode.constant parameterInterval (-1)).add node21)
  |>.recode ⟨#[16,0,-256,0,264,0,-64,0,1]⟩ ⟨#[0,0,256,0,-256,0,64]⟩ node22Denominator node22Cross

/-- Article: exact source arithmetic node 24. -/
private def formula24 (z : ℝ) : ℝ := (formula21 z)*(formula23 z)
private theorem node23Denominator : ∀ z∈parameterInterval, aeval z (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node19Denominator
private theorem node23Cross : polynomialCheck
    (((⟨#[0,0,0,2048,0,-3072,0,1536,0,-256]⟩ : QPoly).mul (⟨#[16,0,-256,0,264,0,-64,0,1]⟩ : QPoly) : QPoly).mul ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩)
    ((⟨#[0,128,0,-2112,0,3136,0,-1568,0,264,0,-4]⟩ : QPoly).mul ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node23 : RationalCode parameterInterval formula24 :=
  (node20.mul node22)
  |>.recode ⟨#[0,128,0,-2112,0,3136,0,-1568,0,264,0,-4]⟩ ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ node23Denominator node23Cross

/-- Article: exact source arithmetic node 25. -/
private def formula25 (z : ℝ) : ℝ := (formula24 z)*(formula11 z)
private theorem node24Denominator : ∀ z∈parameterInterval, aeval z (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node19Denominator
private theorem node24Cross : polynomialCheck
    (((⟨#[0,128,0,-2112,0,3136,0,-1568,0,264,0,-4]⟩ : QPoly).mul (⟨#[4,8,0,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩)
    ((⟨#[-64,-128,1024,2112,-1072,-3136,512,1568,-268,-264,64,4,-1]⟩ : QPoly).mul ((⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node24 : RationalCode parameterInterval formula25 :=
  (node23.mul node10)
  |>.recode ⟨#[-64,-128,1024,2112,-1072,-3136,512,1568,-268,-264,64,4,-1]⟩ ⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ node24Denominator node24Cross

/-- Article: exact source arithmetic node 26. -/
private def formula26 (z : ℝ) : ℝ := (d z)+(formula25 z)
private theorem node25Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-327680,1441792,-2621440,2293760,-1736704,1671168,-655360,-81920,40960,-139264,491520,-495616,325632,-280576,122880,-1024,0,512,-30720,35072,-20352,15488,-7680,1088,-160,160,640,-816,424,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node25Cross : polynomialCheck
    ((((⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly)).add ((⟨#[-64,-128,1024,2112,-1072,-3136,512,1568,-268,-264,64,4,-1]⟩ : QPoly).mul (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly)) : QPoly).mul ⟨#[-327680,1441792,-2621440,2293760,-1736704,1671168,-655360,-81920,40960,-139264,491520,-495616,325632,-280576,122880,-1024,0,512,-30720,35072,-20352,15488,-7680,1088,-160,160,640,-816,424,-280,160,-44,5]⟩)
    ((⟨#[655360,-2883584,0,12124160,-13533184,20807680,-124780544,253198336,-261906432,276037632,-297205760,210628608,-162424832,169461760,-140034048,124850176,-108761600,64652288,-34021376,19621632,-9398144,5789312,-4528128,2555776,-1219360,555648,-153344,-1520,13768,-3592,320]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[64,0,0,0,48,0,0,0,12,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node25 : RationalCode parameterInterval formula26 :=
  (dCode.add node24)
  |>.recode ⟨#[655360,-2883584,0,12124160,-13533184,20807680,-124780544,253198336,-261906432,276037632,-297205760,210628608,-162424832,169461760,-140034048,124850176,-108761600,64652288,-34021376,19621632,-9398144,5789312,-4528128,2555776,-1219360,555648,-153344,-1520,13768,-3592,320]⟩ ⟨#[-327680,1441792,-2621440,2293760,-1736704,1671168,-655360,-81920,40960,-139264,491520,-495616,325632,-280576,122880,-1024,0,512,-30720,35072,-20352,15488,-7680,1088,-160,160,640,-816,424,-280,160,-44,5]⟩ node25Denominator node25Cross

/-- Article: exact coefficient representation of the independently specified valueEndpoint source. -/
def valueEndpointCode : RationalCode parameterInterval (fun z : ℝ => d z-(2*G z-1)*(G z^2-1)/(2*G z^3)) where
  numerator := node25.numerator
  denominator := node25.denominator
  denominator_ne := node25.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => d z-(2*G z-1)*(G z^2-1)/(2*G z^3)) z=formula26 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,atomPolynomial,Boundary.spiralWeight]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node25.exact z hz)

/-- Article: exact rational endpoint identity valueEndpoint at the source cubic root. -/
theorem valueEndpoint_at_zeta1 : (d zeta1-(2*G zeta1-1)*(G zeta1^2-1)/(2*G zeta1^3))=0 := by
  have hc : Numerics.remainderCodeCheck valueEndpointCode.numerator Numerics.transitionCubicCode.code ⟨#[-327680,1441792,163840,-6946816,7405568,-6848512,55214080,-119472128,99921920,-50675712,38905856,-30015488,36421632,-50270208,36798464,-19079168,10846464,-4387328,2047872,-2193920,1481472,-773760,426368,-150272,9616,10496,-3272,320]⟩ QPoly.zero=true := by kernel_decide
  have hd : aeval zeta1 Numerics.transitionCubicCode.code.toPoly=0 := by
    rw [Numerics.transitionCubicCode.exact]
    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using endpointCubic_zeta1
  have he := Numerics.eval_at_root_of_code hc hd
  have h := valueEndpointCode.exact zeta1 zeta1_mem
  rw [he] at h
  simpa [QPoly.toPoly_zero] using h

/-- Article: exact source arithmetic node 27. -/
private def formula27 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(G z)
private theorem node26Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node26Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-4,0,2]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-16,0,8]⟩ : QPoly)))=true := by kernel_decide
private def node26 : RationalCode parameterInterval formula27 :=
  ((RationalCode.constant parameterInterval (4)).mul GCode)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-4,0,2]⟩ node26Denominator node26Cross

/-- Article: exact source arithmetic node 28. -/
private def formula28 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1 : ℚ) : ℝ)) z)+(formula27 z)
private theorem node27Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  node26Denominator
private theorem node27Cross : polynomialCheck
    ((((⟨#[1]⟩ : QPoly).mul (⟨#[0,-4,0,2]⟩ : QPoly)).add ((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,-4,0,2]⟩)
    ((⟨#[4,-4,0,2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,-4,0,2]⟩ : QPoly)))=true := by kernel_decide
private def node27 : RationalCode parameterInterval formula28 :=
  ((RationalCode.constant parameterInterval (1)).add node26)
  |>.recode ⟨#[4,-4,0,2,1]⟩ ⟨#[0,-4,0,2]⟩ node27Denominator node27Cross

/-- Article: exact source arithmetic node 29. -/
private def formula29 (z : ℝ) : ℝ := (formula28 z)⁻¹
private theorem node28Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,-4,0,2,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node28Cross : polynomialCheck
    ((⟨#[0,-4,0,2]⟩ : QPoly).mul ⟨#[4,-4,0,2,1]⟩)
    ((⟨#[0,-4,0,2]⟩ : QPoly).mul (⟨#[4,-4,0,2,1]⟩))=true := by kernel_decide
private def node28 : RationalCode parameterInterval formula29 :=
  (node27.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[0,-4,0,2]⟩ ⟨#[4,-4,0,2,1]⟩ node28Denominator node28Cross

/-- Article: exact source arithmetic node 30. -/
private def formula30 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(formula29 z)
private theorem node29Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,-4,0,2,1]⟩ : QPoly).toPoly≠0 :=
  node28Denominator
private theorem node29Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[0,-4,0,2]⟩ : QPoly) : QPoly).mul ⟨#[4,-4,0,2,1]⟩)
    ((⟨#[0,8,0,-4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[4,-4,0,2,1]⟩ : QPoly)))=true := by kernel_decide
private def node29 : RationalCode parameterInterval formula30 :=
  ((RationalCode.constant parameterInterval (-2)).mul node28)
  |>.recode ⟨#[0,8,0,-4]⟩ ⟨#[4,-4,0,2,1]⟩ node29Denominator node29Cross

/-- Article: exact source arithmetic node 31. -/
private def formula31 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(formula22 z)
private theorem node30Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,128,0,-128,0,32]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node30Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,128,0,-128,0,32]⟩)
    ((⟨#[-16,0,0,0,-8,0,0,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly)))=true := by kernel_decide
private def node30 : RationalCode parameterInterval formula31 :=
  ((RationalCode.constant parameterInterval (-2)).mul node21)
  |>.recode ⟨#[-16,0,0,0,-8,0,0,0,-1]⟩ ⟨#[0,0,128,0,-128,0,32]⟩ node30Denominator node30Cross

/-- Article: exact source arithmetic node 32. -/
private def formula32 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1 : ℚ) : ℝ)) z)+(formula31 z)
private theorem node31Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,128,0,-128,0,32]⟩ : QPoly).toPoly≠0 :=
  node30Denominator
private theorem node31Cross : polynomialCheck
    ((((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,128,0,-128,0,32]⟩ : QPoly)).add ((⟨#[-16,0,0,0,-8,0,0,0,-1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,128,0,-128,0,32]⟩)
    ((⟨#[-16,0,128,0,-136,0,32,0,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,0,128,0,-128,0,32]⟩ : QPoly)))=true := by kernel_decide
private def node31 : RationalCode parameterInterval formula32 :=
  ((RationalCode.constant parameterInterval (1)).add node30)
  |>.recode ⟨#[-16,0,128,0,-136,0,32,0,-1]⟩ ⟨#[0,0,128,0,-128,0,32]⟩ node31Denominator node31Cross

/-- Article: exact source arithmetic node 33. -/
private def formula33 (z : ℝ) : ℝ := (formula32 z)+(formula10 z)
private theorem node32Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,128,0,-128,0,32]⟩ : QPoly).toPoly≠0 :=
  node30Denominator
private theorem node32Cross : polynomialCheck
    ((((⟨#[-16,0,128,0,-136,0,32,0,-1]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)).add ((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[0,0,128,0,-128,0,32]⟩ : QPoly)) : QPoly).mul ⟨#[0,0,128,0,-128,0,32]⟩)
    ((⟨#[-16,-64,128,32,-136,-16,32,8,-1]⟩ : QPoly).mul ((⟨#[0,0,128,0,-128,0,32]⟩ : QPoly).mul (⟨#[0,-8,0,4]⟩ : QPoly)))=true := by kernel_decide
private def node32 : RationalCode parameterInterval formula33 :=
  (node31.add node9)
  |>.recode ⟨#[-16,-64,128,32,-136,-16,32,8,-1]⟩ ⟨#[0,0,128,0,-128,0,32]⟩ node32Denominator node32Cross

/-- Article: exact source arithmetic node 34. -/
private def formula34 (z : ℝ) : ℝ := (formula30 z)*(formula33 z)
private theorem node33Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-64,64,32,-64,-16,16,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node33Cross : polynomialCheck
    (((⟨#[0,8,0,-4]⟩ : QPoly).mul (⟨#[-16,-64,128,32,-136,-16,32,8,-1]⟩ : QPoly) : QPoly).mul ⟨#[0,-64,64,32,-64,-16,16,8]⟩)
    ((⟨#[16,64,-128,-32,136,16,-32,-8,1]⟩ : QPoly).mul ((⟨#[4,-4,0,2,1]⟩ : QPoly).mul (⟨#[0,0,128,0,-128,0,32]⟩ : QPoly)))=true := by kernel_decide
private def node33 : RationalCode parameterInterval formula34 :=
  (node29.mul node32)
  |>.recode ⟨#[16,64,-128,-32,136,16,-32,-8,1]⟩ ⟨#[0,-64,64,32,-64,-16,16,8]⟩ node33Denominator node33Cross

/-- Article: exact source arithmetic node 35. -/
private def formula35 (z : ℝ) : ℝ := (W z)+(formula34 z)
private theorem node34Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-1024,3072,-3072,512,512,256,-128,-256,64,-192,192,32,-32,-16,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node34Cross : polynomialCheck
    ((((⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly).mul (⟨#[0,-64,64,32,-64,-16,16,8]⟩ : QPoly)).add ((⟨#[16,64,-128,-32,136,16,-32,-8,1]⟩ : QPoly).mul (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly)) : QPoly).mul ⟨#[0,-1024,3072,-3072,512,512,256,-128,-256,64,-192,192,32,-32,-16,8]⟩)
    ((⟨#[256,-384,-768,1216,512,-544,-576,-752,1248,184,-144,-284,32,74,-12,-5,1]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[0,-64,64,32,-64,-16,16,8]⟩ : QPoly)))=true := by kernel_decide
private def node34 : RationalCode parameterInterval formula35 :=
  (WCode.add node33)
  |>.recode ⟨#[256,-384,-768,1216,512,-544,-576,-752,1248,184,-144,-284,32,74,-12,-5,1]⟩ ⟨#[0,-1024,3072,-3072,512,512,256,-128,-256,64,-192,192,32,-32,-16,8]⟩ node34Denominator node34Cross

/-- Article: exact coefficient representation of the independently specified weightEndpoint source. -/
def weightEndpointCode : RationalCode parameterInterval (fun z : ℝ => W z-Boundary.spiralWeight (G z)) where
  numerator := node34.numerator
  denominator := node34.denominator
  denominator_ne := node34.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => W z-Boundary.spiralWeight (G z)) z=formula35 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,atomPolynomial,Boundary.spiralWeight]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node34.exact z hz)

/-- Article: exact rational endpoint identity weightEndpoint at the source cubic root. -/
theorem weightEndpoint_at_zeta1 : (W zeta1-Boundary.spiralWeight (G zeta1))=0 := by
  have hc : Numerics.remainderCodeCheck weightEndpointCode.numerator Numerics.transitionCubicCode.code ⟨#[-128,192,448,-768,-384,880,96,-256,-232,84,60,-16,-4,1]⟩ QPoly.zero=true := by kernel_decide
  have hd : aeval zeta1 Numerics.transitionCubicCode.code.toPoly=0 := by
    rw [Numerics.transitionCubicCode.exact]
    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using endpointCubic_zeta1
  have he := Numerics.eval_at_root_of_code hc hd
  have h := weightEndpointCode.exact zeta1 zeta1_mem
  rw [he] at h
  simpa [QPoly.toPoly_zero] using h

/-- Article: exact source arithmetic node 36. -/
private def formula36 (z : ℝ) : ℝ := ((fun _ : ℝ => (((-1/2) : ℚ) : ℝ)) z)*(formula2 z)
private theorem node35Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node1Denominator
private theorem node35Cross : polynomialCheck
    (((⟨#[(-1/2)]⟩ : QPoly).mul (⟨#[0,0,256,0,-256,0,64]⟩ : QPoly) : QPoly).mul ⟨#[16,0,0,0,8,0,0,0,1]⟩)
    ((⟨#[0,0,-128,0,128,0,-32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node35 : RationalCode parameterInterval formula36 :=
  ((RationalCode.constant parameterInterval ((-1/2))).mul node1)
  |>.recode ⟨#[0,0,-128,0,128,0,-32]⟩ ⟨#[16,0,0,0,8,0,0,0,1]⟩ node35Denominator node35Cross

/-- Article: exact source arithmetic node 37. -/
private def formula37 (z : ℝ) : ℝ := (slope z)+(formula36 z)
private theorem node36Denominator : ∀ z∈parameterInterval, aeval z (⟨#[512,0,-256,0,-768,0,-640,0,-512,0,-256,0,-80,0,-24,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node36Cross : polynomialCheck
    ((((⟨#[0,0,256,-512,384,-256,192,-128,32]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly)).add ((⟨#[0,0,-128,0,128,0,-32]⟩ : QPoly).mul (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[512,0,-256,0,-768,0,-640,0,-512,0,-256,0,-80,0,-24,0,-2,0,1]⟩)
    ((⟨#[0,0,0,-8192,12288,-4096,10240,-6144,0,-2048,0,-1536,1280,-256,384,-128]⟩ : QPoly).mul ((⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).mul (⟨#[16,0,0,0,8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node36 : RationalCode parameterInterval formula37 :=
  (slopeCode.add node35)
  |>.recode ⟨#[0,0,0,-8192,12288,-4096,10240,-6144,0,-2048,0,-1536,1280,-256,384,-128]⟩ ⟨#[512,0,-256,0,-768,0,-640,0,-512,0,-256,0,-80,0,-24,0,-2,0,1]⟩ node36Denominator node36Cross

/-- Article: exact coefficient representation of the independently specified derivativeEndpoint source. -/
def derivativeEndpointCode : RationalCode parameterInterval (fun z : ℝ => slope z-1/(2*G z^2)) where
  numerator := node36.numerator
  denominator := node36.denominator
  denominator_ne := node36.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => slope z-1/(2*G z^2)) z=formula37 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,atomPolynomial,Boundary.spiralWeight]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node36.exact z hz)

/-- Article: exact rational endpoint identity derivativeEndpoint at the source cubic root. -/
theorem derivativeEndpoint_at_zeta1 : (slope zeta1-1/(2*G zeta1^2))=0 := by
  have hc : Numerics.remainderCodeCheck derivativeEndpointCode.numerator Numerics.transitionCubicCode.code ⟨#[0,0,0,4096,-6144,0,0,0,0,1024,0,256,-128]⟩ QPoly.zero=true := by kernel_decide
  have hd : aeval zeta1 Numerics.transitionCubicCode.code.toPoly=0 := by
    rw [Numerics.transitionCubicCode.exact]
    simpa [Numerics.transitionCubic,endpointCubic,Polynomial.aeval_def] using endpointCubic_zeta1
  have he := Numerics.eval_at_root_of_code hc hd
  have h := derivativeEndpointCode.exact zeta1 zeta1_mem
  rw [he] at h
  simpa [QPoly.toPoly_zero] using h

end
end polyak.Boundary.P2
