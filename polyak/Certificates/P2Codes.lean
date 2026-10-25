import polyak.Numerics.KernelDecide
import polyak.Boundary.P2.Check

/-!
Article: Definition p2data, exact rational coefficient proposals.
Use: every exported RationalCode has a specified source formula, proved denominators
and local kernel-checked polynomial cross products. Generated annotations do not
supply a mathematical hypothesis. Regenerate with certificates/p2_lean.py.
-/
namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
/-- Article: exact source arithmetic node 1. -/
private def formula1 (z : ℝ) : ℝ := (id z)⁻¹
private theorem node0Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node0Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[0,1]⟩))=true := by kernel_decide
private def node0 : RationalCode parameterInterval formula1 :=
  ((RationalCode.variable parameterInterval).inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[0,1]⟩ node0Denominator node0Cross

/-- Article: exact source arithmetic node 2. -/
private def formula2 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/8) : ℚ) : ℝ)) z)*(formula1 z)
private theorem node1Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node1Cross : polynomialCheck
    (((⟨#[(1/8)]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,8]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly)))=true := by kernel_decide
private def node1 : RationalCode parameterInterval formula2 :=
  ((RationalCode.constant parameterInterval ((1/8))).mul node0)
  |>.recode ⟨#[1]⟩ ⟨#[0,8]⟩ node1Denominator node1Cross

/-- Article: exact source arithmetic node 3. -/
private def formula3 (z : ℝ) : ℝ := (id z)^2
private theorem node2Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node2Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 2 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 2))=true := by kernel_decide
private def node2 : RationalCode parameterInterval formula3 :=
  ((RationalCode.variable parameterInterval).pow 2)
  |>.recode ⟨#[0,0,1]⟩ ⟨#[1]⟩ node2Denominator node2Cross

/-- Article: exact source arithmetic node 4. -/
private def formula4 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula3 z)
private theorem node3Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node3Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node3 : RationalCode parameterInterval formula4 :=
  ((RationalCode.constant parameterInterval (-2)).add node2)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node3Denominator node3Cross

/-- Article: exact source arithmetic node 5. -/
private def formula5 (z : ℝ) : ℝ := (formula4 z)⁻¹
private theorem node4Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node4Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,0,1]⟩))=true := by kernel_decide
private def node4 : RationalCode parameterInterval formula5 :=
  (node3.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,0,1]⟩ node4Denominator node4Cross

/-- Article: exact source arithmetic node 6. -/
private def formula6 (z : ℝ) : ℝ := (formula2 z)*(formula5 z)
private theorem node5Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node5Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[0,8]⟩ : QPoly).mul (⟨#[-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node5 : RationalCode parameterInterval formula6 :=
  (node1.mul node4)
  |>.recode ⟨#[1]⟩ ⟨#[0,-16,0,8]⟩ node5Denominator node5Cross

/-- Article: exact source arithmetic node 7. -/
private def formula7 (z : ℝ) : ℝ := (id z)^4
private theorem node6Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node6Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 4 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 4))=true := by kernel_decide
private def node6 : RationalCode parameterInterval formula7 :=
  ((RationalCode.variable parameterInterval).pow 4)
  |>.recode ⟨#[0,0,0,0,1]⟩ ⟨#[1]⟩ node6Denominator node6Cross

/-- Article: exact source arithmetic node 8. -/
private def formula8 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)+(formula7 z)
private theorem node7Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node7Cross : polynomialCheck
    ((((⟨#[4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node7 : RationalCode parameterInterval formula8 :=
  ((RationalCode.constant parameterInterval (4)).add node6)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[1]⟩ node7Denominator node7Cross

/-- Article: exact source arithmetic node 9. -/
private def formula9 (z : ℝ) : ℝ := (formula6 z)*(formula8 z)
private theorem node8Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-16,0,8]⟩ : QPoly).toPoly≠0 :=
  node5Denominator
private theorem node8Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[4,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-16,0,8]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[0,-16,0,8]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node8 : RationalCode parameterInterval formula9 :=
  (node5.mul node7)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[0,-16,0,8]⟩ node8Denominator node8Cross

/-- Article: exact coefficient representation of the independently specified G source. -/
def GCode : RationalCode parameterInterval G where
  numerator := node8.numerator
  denominator := node8.denominator
  denominator_ne := node8.denominator_ne
  exact z hz := by
    have he : G z=formula9 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node8.exact z hz)

/-- Article: exact source arithmetic node 10. -/
private def formula10 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)+(formula7 z)
private theorem node9Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node9Cross : polynomialCheck
    ((((⟨#[-4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node9 : RationalCode parameterInterval formula10 :=
  ((RationalCode.constant parameterInterval (-4)).add node6)
  |>.recode ⟨#[-4,0,0,0,1]⟩ ⟨#[1]⟩ node9Denominator node9Cross

/-- Article: exact source arithmetic node 11. -/
private def formula11 (z : ℝ) : ℝ := (formula10 z)⁻¹
private theorem node10Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node10Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-4,0,0,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-4,0,0,0,1]⟩))=true := by kernel_decide
private def node10 : RationalCode parameterInterval formula11 :=
  (node9.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-4,0,0,0,1]⟩ node10Denominator node10Cross

/-- Article: exact source arithmetic node 12. -/
private def formula12 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)+(formula3 z)
private theorem node11Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node11Cross : polynomialCheck
    ((((⟨#[2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node11 : RationalCode parameterInterval formula12 :=
  ((RationalCode.constant parameterInterval (2)).add node2)
  |>.recode ⟨#[2,0,1]⟩ ⟨#[1]⟩ node11Denominator node11Cross

/-- Article: exact source arithmetic node 13. -/
private def formula13 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(id z)
private theorem node12Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node12Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node12 : RationalCode parameterInterval formula13 :=
  ((RationalCode.constant parameterInterval (-2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-2]⟩ ⟨#[1]⟩ node12Denominator node12Cross

/-- Article: exact source arithmetic node 14. -/
private def formula14 (z : ℝ) : ℝ := (formula12 z)+(formula13 z)
private theorem node13Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node13Cross : polynomialCheck
    ((((⟨#[2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,-2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node13 : RationalCode parameterInterval formula14 :=
  (node11.add node12)
  |>.recode ⟨#[2,-2,1]⟩ ⟨#[1]⟩ node13Denominator node13Cross

/-- Article: exact source arithmetic node 15. -/
private def formula15 (z : ℝ) : ℝ := (formula14 z)^2
private theorem node14Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node14Cross : polynomialCheck
    ((polynomialPower ⟨#[2,-2,1]⟩ 2 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 2))=true := by kernel_decide
private def node14 : RationalCode parameterInterval formula15 :=
  (node13.pow 2)
  |>.recode ⟨#[4,-8,8,-4,1]⟩ ⟨#[1]⟩ node14Denominator node14Cross

/-- Article: exact source arithmetic node 16. -/
private def formula16 (z : ℝ) : ℝ := (formula11 z)*(formula15 z)
private theorem node15Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-4,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node10Denominator
private theorem node15Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[-4,0,0,0,1]⟩)
    ((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul ((⟨#[-4,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node15 : RationalCode parameterInterval formula16 :=
  (node10.mul node14)
  |>.recode ⟨#[4,-8,8,-4,1]⟩ ⟨#[-4,0,0,0,1]⟩ node15Denominator node15Cross

/-- Article: exact coefficient representation of the independently specified u source. -/
def uCode : RationalCode parameterInterval u where
  numerator := node15.numerator
  denominator := node15.denominator
  denominator_ne := node15.denominator_ne
  exact z hz := by
    have he : u z=formula16 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node15.exact z hz)

/-- Article: exact source arithmetic node 17. -/
private def formula17 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)+(formula3 z)
private theorem node16Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node16Cross : polynomialCheck
    ((((⟨#[2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node16 : RationalCode parameterInterval formula17 :=
  ((RationalCode.constant parameterInterval (2)).add node2)
  |>.recode ⟨#[2,0,1]⟩ ⟨#[1]⟩ node16Denominator node16Cross

/-- Article: exact source arithmetic node 18. -/
private def formula18 (z : ℝ) : ℝ := (formula17 z)⁻¹
private theorem node17Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node17Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[2,0,1]⟩))=true := by kernel_decide
private def node17 : RationalCode parameterInterval formula18 :=
  (node16.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[2,0,1]⟩ node17Denominator node17Cross

/-- Article: exact source arithmetic node 19. -/
private def formula19 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/8) : ℚ) : ℝ)) z)*(formula18 z)
private theorem node18Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node18Cross : polynomialCheck
    (((⟨#[(1/8)]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[16,0,8]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node18 : RationalCode parameterInterval formula19 :=
  ((RationalCode.constant parameterInterval ((1/8))).mul node17)
  |>.recode ⟨#[1]⟩ ⟨#[16,0,8]⟩ node18Denominator node18Cross

/-- Article: exact source arithmetic node 20. -/
private def formula20 (z : ℝ) : ℝ := (formula19 z)*(formula15 z)
private theorem node19Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,8]⟩ : QPoly).toPoly≠0 :=
  node18Denominator
private theorem node19Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[4,-8,8,-4,1]⟩ : QPoly) : QPoly).mul ⟨#[16,0,8]⟩)
    ((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul ((⟨#[16,0,8]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node19 : RationalCode parameterInterval formula20 :=
  (node18.mul node14)
  |>.recode ⟨#[4,-8,8,-4,1]⟩ ⟨#[16,0,8]⟩ node19Denominator node19Cross

/-- Article: exact source arithmetic node 21. -/
private def formula21 (z : ℝ) : ℝ := (id z)^6
private theorem node20Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node20Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 6 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 6))=true := by kernel_decide
private def node20 : RationalCode parameterInterval formula21 :=
  ((RationalCode.variable parameterInterval).pow 6)
  |>.recode ⟨#[0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node20Denominator node20Cross

/-- Article: exact source arithmetic node 22. -/
private def formula22 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8 : ℚ) : ℝ)) z)+(formula21 z)
private theorem node21Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node21Cross : polynomialCheck
    ((((⟨#[8]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[8,0,0,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node21 : RationalCode parameterInterval formula22 :=
  ((RationalCode.constant parameterInterval (8)).add node20)
  |>.recode ⟨#[8,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node21Denominator node21Cross

/-- Article: exact source arithmetic node 23. -/
private def formula23 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-16 : ℚ) : ℝ)) z)*(id z)
private theorem node22Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node22Cross : polynomialCheck
    (((⟨#[-16]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-16]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node22 : RationalCode parameterInterval formula23 :=
  ((RationalCode.constant parameterInterval (-16)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-16]⟩ ⟨#[1]⟩ node22Denominator node22Cross

/-- Article: exact source arithmetic node 24. -/
private def formula24 (z : ℝ) : ℝ := (formula22 z)+(formula23 z)
private theorem node23Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node23Cross : polynomialCheck
    ((((⟨#[8,0,0,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-16]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[8,-16,0,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node23 : RationalCode parameterInterval formula24 :=
  (node21.add node22)
  |>.recode ⟨#[8,-16,0,0,0,0,1]⟩ ⟨#[1]⟩ node23Denominator node23Cross

/-- Article: exact source arithmetic node 25. -/
private def formula25 (z : ℝ) : ℝ := (id z)^5
private theorem node24Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node24Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 5 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 5))=true := by kernel_decide
private def node24 : RationalCode parameterInterval formula25 :=
  ((RationalCode.variable parameterInterval).pow 5)
  |>.recode ⟨#[0,0,0,0,0,1]⟩ ⟨#[1]⟩ node24Denominator node24Cross

/-- Article: exact source arithmetic node 26. -/
private def formula26 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(formula25 z)
private theorem node25Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node25Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node25 : RationalCode parameterInterval formula26 :=
  ((RationalCode.constant parameterInterval (-4)).mul node24)
  |>.recode ⟨#[0,0,0,0,0,-4]⟩ ⟨#[1]⟩ node25Denominator node25Cross

/-- Article: exact source arithmetic node 27. -/
private def formula27 (z : ℝ) : ℝ := (formula24 z)+(formula26 z)
private theorem node26Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node26Cross : polynomialCheck
    ((((⟨#[8,-16,0,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[8,-16,0,0,0,-4,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node26 : RationalCode parameterInterval formula27 :=
  (node23.add node25)
  |>.recode ⟨#[8,-16,0,0,0,-4,1]⟩ ⟨#[1]⟩ node26Denominator node26Cross

/-- Article: exact source arithmetic node 28. -/
private def formula28 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node27Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node27Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node27 : RationalCode parameterInterval formula28 :=
  ((RationalCode.constant parameterInterval (4)).mul node6)
  |>.recode ⟨#[0,0,0,0,4]⟩ ⟨#[1]⟩ node27Denominator node27Cross

/-- Article: exact source arithmetic node 29. -/
private def formula29 (z : ℝ) : ℝ := (formula27 z)+(formula28 z)
private theorem node28Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node28Cross : polynomialCheck
    ((((⟨#[8,-16,0,0,0,-4,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[8,-16,0,0,4,-4,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node28 : RationalCode parameterInterval formula29 :=
  (node26.add node27)
  |>.recode ⟨#[8,-16,0,0,4,-4,1]⟩ ⟨#[1]⟩ node28Denominator node28Cross

/-- Article: exact source arithmetic node 30. -/
private def formula30 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node29Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node29Cross : polynomialCheck
    (((⟨#[8]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,8]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node29 : RationalCode parameterInterval formula30 :=
  ((RationalCode.constant parameterInterval (8)).mul node2)
  |>.recode ⟨#[0,0,8]⟩ ⟨#[1]⟩ node29Denominator node29Cross

/-- Article: exact source arithmetic node 31. -/
private def formula31 (z : ℝ) : ℝ := (formula29 z)+(formula30 z)
private theorem node30Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node30Cross : polynomialCheck
    ((((⟨#[8,-16,0,0,4,-4,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,8]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[8,-16,8,0,4,-4,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node30 : RationalCode parameterInterval formula31 :=
  (node28.add node29)
  |>.recode ⟨#[8,-16,8,0,4,-4,1]⟩ ⟨#[1]⟩ node30Denominator node30Cross

/-- Article: exact source arithmetic node 32. -/
private def formula32 (z : ℝ) : ℝ := (formula31 z)⁻¹
private theorem node31Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,-16,8,0,4,-4,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node31Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[8,-16,8,0,4,-4,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[8,-16,8,0,4,-4,1]⟩))=true := by kernel_decide
private def node31 : RationalCode parameterInterval formula32 :=
  (node30.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[8,-16,8,0,4,-4,1]⟩ node31Denominator node31Cross

/-- Article: exact source arithmetic node 33. -/
private def formula33 (z : ℝ) : ℝ := (formula20 z)*(formula32 z)
private theorem node32Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node32Cross : polynomialCheck
    (((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩)
    ((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul ((⟨#[16,0,8]⟩ : QPoly).mul (⟨#[8,-16,8,0,4,-4,1]⟩ : QPoly)))=true := by kernel_decide
private def node32 : RationalCode parameterInterval formula33 :=
  (node19.mul node31)
  |>.recode ⟨#[4,-8,8,-4,1]⟩ ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ node32Denominator node32Cross

/-- Article: exact source arithmetic node 34. -/
private def formula34 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)+(formula3 z)
private theorem node33Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node33Cross : polynomialCheck
    ((((⟨#[2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node33 : RationalCode parameterInterval formula34 :=
  ((RationalCode.constant parameterInterval (2)).add node2)
  |>.recode ⟨#[2,0,1]⟩ ⟨#[1]⟩ node33Denominator node33Cross

/-- Article: exact source arithmetic node 35. -/
private def formula35 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(id z)
private theorem node34Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node34Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node34 : RationalCode parameterInterval formula35 :=
  ((RationalCode.constant parameterInterval (2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,2]⟩ ⟨#[1]⟩ node34Denominator node34Cross

/-- Article: exact source arithmetic node 36. -/
private def formula36 (z : ℝ) : ℝ := (formula34 z)+(formula35 z)
private theorem node35Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node35Cross : polynomialCheck
    ((((⟨#[2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[2,2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node35 : RationalCode parameterInterval formula36 :=
  (node33.add node34)
  |>.recode ⟨#[2,2,1]⟩ ⟨#[1]⟩ node35Denominator node35Cross

/-- Article: exact source arithmetic node 37. -/
private def formula37 (z : ℝ) : ℝ := (formula33 z)*(formula36 z)
private theorem node36Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  node32Denominator
private theorem node36Cross : polynomialCheck
    (((⟨#[4,-8,8,-4,1]⟩ : QPoly).mul (⟨#[2,2,1]⟩ : QPoly) : QPoly).mul ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩)
    ((⟨#[8,-8,4,0,2,-2,1]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node36 : RationalCode parameterInterval formula37 :=
  (node32.mul node35)
  |>.recode ⟨#[8,-8,4,0,2,-2,1]⟩ ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ node36Denominator node36Cross

/-- Article: exact source arithmetic node 38. -/
private def formula38 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-18 : ℚ) : ℝ)) z)*(id z)
private theorem node37Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node37Cross : polynomialCheck
    (((⟨#[-18]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-18]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node37 : RationalCode parameterInterval formula38 :=
  ((RationalCode.constant parameterInterval (-18)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-18]⟩ ⟨#[1]⟩ node37Denominator node37Cross

/-- Article: exact source arithmetic node 39. -/
private def formula39 (z : ℝ) : ℝ := ((fun _ : ℝ => ((14 : ℚ) : ℝ)) z)+(formula38 z)
private theorem node38Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node38Cross : polynomialCheck
    ((((⟨#[14]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-18]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[14,-18]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node38 : RationalCode parameterInterval formula39 :=
  ((RationalCode.constant parameterInterval (14)).add node37)
  |>.recode ⟨#[14,-18]⟩ ⟨#[1]⟩ node38Denominator node38Cross

/-- Article: exact source arithmetic node 40. -/
private def formula40 (z : ℝ) : ℝ := ((fun _ : ℝ => ((7 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node39Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node39Cross : polynomialCheck
    (((⟨#[7]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,7]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node39 : RationalCode parameterInterval formula40 :=
  ((RationalCode.constant parameterInterval (7)).mul node2)
  |>.recode ⟨#[0,0,7]⟩ ⟨#[1]⟩ node39Denominator node39Cross

/-- Article: exact source arithmetic node 41. -/
private def formula41 (z : ℝ) : ℝ := (formula39 z)+(formula40 z)
private theorem node40Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node40Cross : polynomialCheck
    ((((⟨#[14,-18]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,7]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[14,-18,7]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node40 : RationalCode parameterInterval formula41 :=
  (node38.add node39)
  |>.recode ⟨#[14,-18,7]⟩ ⟨#[1]⟩ node40Denominator node40Cross

/-- Article: exact source arithmetic node 42. -/
private def formula42 (z : ℝ) : ℝ := (formula37 z)*(formula41 z)
private theorem node41Denominator : ∀ z∈parameterInterval, aeval z (⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).toPoly≠0 :=
  node32Denominator
private theorem node41Cross : polynomialCheck
    (((⟨#[8,-8,4,0,2,-2,1]⟩ : QPoly).mul (⟨#[14,-18,7]⟩ : QPoly) : QPoly).mul ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩)
    ((⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ : QPoly).mul ((⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node41 : RationalCode parameterInterval formula42 :=
  (node36.mul node40)
  |>.recode ⟨#[112,-256,256,-128,56,-64,64,-32,7]⟩ ⟨#[128,-256,192,-128,128,-64,48,-32,8]⟩ node41Denominator node41Cross

/-- Article: exact coefficient representation of the independently specified W source. -/
def WCode : RationalCode parameterInterval W where
  numerator := node41.numerator
  denominator := node41.denominator
  denominator_ne := node41.denominator_ne
  exact z hz := by
    have he : W z=formula42 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node41.exact z hz)

/-- Article: exact source arithmetic node 43. -/
private def formula43 (z : ℝ) : ℝ := ((fun _ : ℝ => (((1/2) : ℚ) : ℝ)) z)*(formula1 z)
private theorem node42Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,2]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node42Cross : polynomialCheck
    (((⟨#[(1/2)]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,2]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly)))=true := by kernel_decide
private def node42 : RationalCode parameterInterval formula43 :=
  ((RationalCode.constant parameterInterval ((1/2))).mul node0)
  |>.recode ⟨#[1]⟩ ⟨#[0,2]⟩ node42Denominator node42Cross

/-- Article: exact source arithmetic node 44. -/
private def formula44 (z : ℝ) : ℝ := (formula43 z)*(formula5 z)
private theorem node43Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-4,0,2]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node43Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,-4,0,2]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[0,2]⟩ : QPoly).mul (⟨#[-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node43 : RationalCode parameterInterval formula44 :=
  (node42.mul node4)
  |>.recode ⟨#[1]⟩ ⟨#[0,-4,0,2]⟩ node43Denominator node43Cross

/-- Article: exact source arithmetic node 45. -/
private def formula45 (z : ℝ) : ℝ := (formula44 z)*(formula18 z)
private theorem node44Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,0,0,2]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node44Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,0,0,2]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[0,-4,0,2]⟩ : QPoly).mul (⟨#[2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node44 : RationalCode parameterInterval formula45 :=
  (node43.mul node17)
  |>.recode ⟨#[1]⟩ ⟨#[0,-8,0,0,0,2]⟩ node44Denominator node44Cross

/-- Article: exact source arithmetic node 46. -/
private def formula46 (z : ℝ) : ℝ := (formula14 z)^3
private theorem node45Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node45Cross : polynomialCheck
    ((polynomialPower ⟨#[2,-2,1]⟩ 3 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 3))=true := by kernel_decide
private def node45 : RationalCode parameterInterval formula46 :=
  (node13.pow 3)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[1]⟩ node45Denominator node45Cross

/-- Article: exact source arithmetic node 47. -/
private def formula47 (z : ℝ) : ℝ := (formula45 z)*(formula46 z)
private theorem node46Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,-8,0,0,0,2]⟩ : QPoly).toPoly≠0 :=
  node44Denominator
private theorem node46Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[0,-8,0,0,0,2]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[0,-8,0,0,0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node46 : RationalCode parameterInterval formula47 :=
  (node44.mul node45)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[0,-8,0,0,0,2]⟩ node46Denominator node46Cross

/-- Article: exact coefficient representation of the independently specified atomA source. -/
def atomACode : RationalCode parameterInterval atomA where
  numerator := node46.numerator
  denominator := node46.denominator
  denominator_ne := node46.denominator_ne
  exact z hz := by
    have he : atomA z=formula47 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node46.exact z hz)

/-- Article: exact source arithmetic node 48. -/
private def formula48 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(id z)
private theorem node47Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node47Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node47 : RationalCode parameterInterval formula48 :=
  ((RationalCode.constant parameterInterval (-2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-2]⟩ ⟨#[1]⟩ node47Denominator node47Cross

/-- Article: exact source arithmetic node 49. -/
private def formula49 (z : ℝ) : ℝ := (formula4 z)⁻¹
private theorem node48Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node48Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,0,1]⟩))=true := by kernel_decide
private def node48 : RationalCode parameterInterval formula49 :=
  (node3.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,0,1]⟩ node48Denominator node48Cross

/-- Article: exact source arithmetic node 50. -/
private def formula50 (z : ℝ) : ℝ := (formula49 z)^2
private theorem node49Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node49Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[4,0,-4,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[-2,0,1]⟩ 2))=true := by kernel_decide
private def node49 : RationalCode parameterInterval formula50 :=
  (node48.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[4,0,-4,0,1]⟩ node49Denominator node49Cross

/-- Article: exact source arithmetic node 51. -/
private def formula51 (z : ℝ) : ℝ := (formula48 z)*(formula50 z)
private theorem node50Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,-4,0,1]⟩ : QPoly).toPoly≠0 :=
  node49Denominator
private theorem node50Cross : polynomialCheck
    (((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[4,0,-4,0,1]⟩)
    ((⟨#[0,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[4,0,-4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node50 : RationalCode parameterInterval formula51 :=
  (node47.mul node49)
  |>.recode ⟨#[0,-2]⟩ ⟨#[4,0,-4,0,1]⟩ node50Denominator node50Cross

/-- Article: exact source arithmetic node 52. -/
private def formula52 (z : ℝ) : ℝ := (formula51 z)*(formula18 z)
private theorem node51Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node51Cross : polynomialCheck
    (((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[8,0,-4,0,-2,0,1]⟩)
    ((⟨#[0,-2]⟩ : QPoly).mul ((⟨#[4,0,-4,0,1]⟩ : QPoly).mul (⟨#[2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node51 : RationalCode parameterInterval formula52 :=
  (node50.mul node17)
  |>.recode ⟨#[0,-2]⟩ ⟨#[8,0,-4,0,-2,0,1]⟩ node51Denominator node51Cross

/-- Article: exact source arithmetic node 53. -/
private def formula53 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-20 : ℚ) : ℝ)) z)*(id z)
private theorem node52Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node52Cross : polynomialCheck
    (((⟨#[-20]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-20]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node52 : RationalCode parameterInterval formula53 :=
  ((RationalCode.constant parameterInterval (-20)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-20]⟩ ⟨#[1]⟩ node52Denominator node52Cross

/-- Article: exact source arithmetic node 54. -/
private def formula54 (z : ℝ) : ℝ := ((fun _ : ℝ => ((12 : ℚ) : ℝ)) z)+(formula53 z)
private theorem node53Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node53Cross : polynomialCheck
    ((((⟨#[12]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-20]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[12,-20]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node53 : RationalCode parameterInterval formula54 :=
  ((RationalCode.constant parameterInterval (12)).add node52)
  |>.recode ⟨#[12,-20]⟩ ⟨#[1]⟩ node53Denominator node53Cross

/-- Article: exact source arithmetic node 55. -/
private def formula55 (z : ℝ) : ℝ := (id z)^3
private theorem node54Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node54Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 3 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 3))=true := by kernel_decide
private def node54 : RationalCode parameterInterval formula55 :=
  ((RationalCode.variable parameterInterval).pow 3)
  |>.recode ⟨#[0,0,0,1]⟩ ⟨#[1]⟩ node54Denominator node54Cross

/-- Article: exact source arithmetic node 56. -/
private def formula56 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-10 : ℚ) : ℝ)) z)*(formula55 z)
private theorem node55Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node55Cross : polynomialCheck
    (((⟨#[-10]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-10]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node55 : RationalCode parameterInterval formula56 :=
  ((RationalCode.constant parameterInterval (-10)).mul node54)
  |>.recode ⟨#[0,0,0,-10]⟩ ⟨#[1]⟩ node55Denominator node55Cross

/-- Article: exact source arithmetic node 57. -/
private def formula57 (z : ℝ) : ℝ := (formula54 z)+(formula56 z)
private theorem node56Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node56Cross : polynomialCheck
    ((((⟨#[12,-20]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-10]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[12,-20,0,-10]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node56 : RationalCode parameterInterval formula57 :=
  (node53.add node55)
  |>.recode ⟨#[12,-20,0,-10]⟩ ⟨#[1]⟩ node56Denominator node56Cross

/-- Article: exact source arithmetic node 58. -/
private def formula58 (z : ℝ) : ℝ := ((fun _ : ℝ => ((3 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node57Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node57Cross : polynomialCheck
    (((⟨#[3]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node57 : RationalCode parameterInterval formula58 :=
  ((RationalCode.constant parameterInterval (3)).mul node6)
  |>.recode ⟨#[0,0,0,0,3]⟩ ⟨#[1]⟩ node57Denominator node57Cross

/-- Article: exact source arithmetic node 59. -/
private def formula59 (z : ℝ) : ℝ := (formula57 z)+(formula58 z)
private theorem node58Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node58Cross : polynomialCheck
    ((((⟨#[12,-20,0,-10]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,3]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[12,-20,0,-10,3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node58 : RationalCode parameterInterval formula59 :=
  (node56.add node57)
  |>.recode ⟨#[12,-20,0,-10,3]⟩ ⟨#[1]⟩ node58Denominator node58Cross

/-- Article: exact source arithmetic node 60. -/
private def formula60 (z : ℝ) : ℝ := ((fun _ : ℝ => ((16 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node59Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node59Cross : polynomialCheck
    (((⟨#[16]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,16]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node59 : RationalCode parameterInterval formula60 :=
  ((RationalCode.constant parameterInterval (16)).mul node2)
  |>.recode ⟨#[0,0,16]⟩ ⟨#[1]⟩ node59Denominator node59Cross

/-- Article: exact source arithmetic node 61. -/
private def formula61 (z : ℝ) : ℝ := (formula59 z)+(formula60 z)
private theorem node60Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node60Cross : polynomialCheck
    ((((⟨#[12,-20,0,-10,3]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,16]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[12,-20,16,-10,3]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node60 : RationalCode parameterInterval formula61 :=
  (node58.add node59)
  |>.recode ⟨#[12,-20,16,-10,3]⟩ ⟨#[1]⟩ node60Denominator node60Cross

/-- Article: exact source arithmetic node 62. -/
private def formula62 (z : ℝ) : ℝ := (formula52 z)*(formula61 z)
private theorem node61Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node51Denominator
private theorem node61Cross : polynomialCheck
    (((⟨#[0,-2]⟩ : QPoly).mul (⟨#[12,-20,16,-10,3]⟩ : QPoly) : QPoly).mul ⟨#[8,0,-4,0,-2,0,1]⟩)
    ((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul ((⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node61 : RationalCode parameterInterval formula62 :=
  (node51.mul node60)
  |>.recode ⟨#[0,-24,40,-32,20,-6]⟩ ⟨#[8,0,-4,0,-2,0,1]⟩ node61Denominator node61Cross

/-- Article: exact coefficient representation of the independently specified atomB source. -/
def atomBCode : RationalCode parameterInterval atomB where
  numerator := node61.numerator
  denominator := node61.denominator
  denominator_ne := node61.denominator_ne
  exact z hz := by
    have he : atomB z=formula62 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node61.exact z hz)

/-- Article: exact source arithmetic node 63. -/
private def formula63 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node62Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node62Cross : polynomialCheck
    (((⟨#[4]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node62 : RationalCode parameterInterval formula63 :=
  ((RationalCode.constant parameterInterval (4)).mul node2)
  |>.recode ⟨#[0,0,4]⟩ ⟨#[1]⟩ node62Denominator node62Cross

/-- Article: exact source arithmetic node 64. -/
private def formula64 (z : ℝ) : ℝ := (formula63 z)*(formula5 z)
private theorem node63Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node63Cross : polynomialCheck
    (((⟨#[0,0,4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[-2,0,1]⟩)
    ((⟨#[0,0,4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node63 : RationalCode parameterInterval formula64 :=
  (node62.mul node4)
  |>.recode ⟨#[0,0,4]⟩ ⟨#[-2,0,1]⟩ node63Denominator node63Cross

/-- Article: exact source arithmetic node 65. -/
private def formula65 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1472 : ℚ) : ℝ)) z)*(formula55 z)
private theorem node64Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node64Cross : polynomialCheck
    (((⟨#[-1472]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-1472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node64 : RationalCode parameterInterval formula65 :=
  ((RationalCode.constant parameterInterval (-1472)).mul node54)
  |>.recode ⟨#[0,0,0,-1472]⟩ ⟨#[1]⟩ node64Denominator node64Cross

/-- Article: exact source arithmetic node 66. -/
private def formula66 (z : ℝ) : ℝ := ((fun _ : ℝ => ((160 : ℚ) : ℝ)) z)+(formula65 z)
private theorem node65Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node65Cross : polynomialCheck
    ((((⟨#[160]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-1472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-1472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node65 : RationalCode parameterInterval formula66 :=
  ((RationalCode.constant parameterInterval (160)).add node64)
  |>.recode ⟨#[160,0,0,-1472]⟩ ⟨#[1]⟩ node65Denominator node65Cross

/-- Article: exact source arithmetic node 67. -/
private def formula67 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1376 : ℚ) : ℝ)) z)*(formula25 z)
private theorem node66Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node66Cross : polynomialCheck
    (((⟨#[-1376]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node66 : RationalCode parameterInterval formula67 :=
  ((RationalCode.constant parameterInterval (-1376)).mul node24)
  |>.recode ⟨#[0,0,0,0,0,-1376]⟩ ⟨#[1]⟩ node66Denominator node66Cross

/-- Article: exact source arithmetic node 68. -/
private def formula68 (z : ℝ) : ℝ := (formula66 z)+(formula67 z)
private theorem node67Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node67Cross : polynomialCheck
    ((((⟨#[160,0,0,-1472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-1472,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node67 : RationalCode parameterInterval formula68 :=
  (node65.add node66)
  |>.recode ⟨#[160,0,0,-1472,0,-1376]⟩ ⟨#[1]⟩ node67Denominator node67Cross

/-- Article: exact source arithmetic node 69. -/
private def formula69 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-704 : ℚ) : ℝ)) z)*(id z)
private theorem node68Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node68Cross : polynomialCheck
    (((⟨#[-704]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-704]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node68 : RationalCode parameterInterval formula69 :=
  ((RationalCode.constant parameterInterval (-704)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-704]⟩ ⟨#[1]⟩ node68Denominator node68Cross

/-- Article: exact source arithmetic node 70. -/
private def formula70 (z : ℝ) : ℝ := (formula68 z)+(formula69 z)
private theorem node69Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node69Cross : polynomialCheck
    ((((⟨#[160,0,0,-1472,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-704]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node69 : RationalCode parameterInterval formula70 :=
  (node67.add node68)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376]⟩ ⟨#[1]⟩ node69Denominator node69Cross

/-- Article: exact source arithmetic node 71. -/
private def formula71 (z : ℝ) : ℝ := (id z)^7
private theorem node70Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node70Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 7 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 7))=true := by kernel_decide
private def node70 : RationalCode parameterInterval formula71 :=
  ((RationalCode.variable parameterInterval).pow 7)
  |>.recode ⟨#[0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node70Denominator node70Cross

/-- Article: exact source arithmetic node 72. -/
private def formula72 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-368 : ℚ) : ℝ)) z)*(formula71 z)
private theorem node71Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node71Cross : polynomialCheck
    (((⟨#[-368]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-368]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node71 : RationalCode parameterInterval formula72 :=
  ((RationalCode.constant parameterInterval (-368)).mul node70)
  |>.recode ⟨#[0,0,0,0,0,0,0,-368]⟩ ⟨#[1]⟩ node71Denominator node71Cross

/-- Article: exact source arithmetic node 73. -/
private def formula73 (z : ℝ) : ℝ := (formula70 z)+(formula72 z)
private theorem node72Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node72Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-368]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node72 : RationalCode parameterInterval formula73 :=
  (node69.add node71)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ ⟨#[1]⟩ node72Denominator node72Cross

/-- Article: exact source arithmetic node 74. -/
private def formula74 (z : ℝ) : ℝ := (id z)^9
private theorem node73Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node73Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 9 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 9))=true := by kernel_decide
private def node73 : RationalCode parameterInterval formula74 :=
  ((RationalCode.variable parameterInterval).pow 9)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node73Denominator node73Cross

/-- Article: exact source arithmetic node 75. -/
private def formula75 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-44 : ℚ) : ℝ)) z)*(formula74 z)
private theorem node74Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node74Cross : polynomialCheck
    (((⟨#[-44]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node74 : RationalCode parameterInterval formula75 :=
  ((RationalCode.constant parameterInterval (-44)).mul node73)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ ⟨#[1]⟩ node74Denominator node74Cross

/-- Article: exact source arithmetic node 76. -/
private def formula76 (z : ℝ) : ℝ := (formula73 z)+(formula75 z)
private theorem node75Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node75Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,-44]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node75 : RationalCode parameterInterval formula76 :=
  (node72.add node74)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ ⟨#[1]⟩ node75Denominator node75Cross

/-- Article: exact source arithmetic node 77. -/
private def formula77 (z : ℝ) : ℝ := (id z)^10
private theorem node76Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node76Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 10 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 10))=true := by kernel_decide
private def node76 : RationalCode parameterInterval formula77 :=
  ((RationalCode.variable parameterInterval).pow 10)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node76Denominator node76Cross

/-- Article: exact source arithmetic node 78. -/
private def formula78 (z : ℝ) : ℝ := ((fun _ : ℝ => ((5 : ℚ) : ℝ)) z)*(formula77 z)
private theorem node77Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node77Cross : polynomialCheck
    (((⟨#[5]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node77 : RationalCode parameterInterval formula78 :=
  ((RationalCode.constant parameterInterval (5)).mul node76)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ ⟨#[1]⟩ node77Denominator node77Cross

/-- Article: exact source arithmetic node 79. -/
private def formula79 (z : ℝ) : ℝ := (formula76 z)+(formula78 z)
private theorem node78Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node78Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node78 : RationalCode parameterInterval formula79 :=
  (node75.add node77)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ ⟨#[1]⟩ node78Denominator node78Cross

/-- Article: exact source arithmetic node 80. -/
private def formula80 (z : ℝ) : ℝ := (id z)^8
private theorem node79Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node79Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 8 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 8))=true := by kernel_decide
private def node79 : RationalCode parameterInterval formula80 :=
  ((RationalCode.variable parameterInterval).pow 8)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node79Denominator node79Cross

/-- Article: exact source arithmetic node 81. -/
private def formula81 (z : ℝ) : ℝ := ((fun _ : ℝ => ((170 : ℚ) : ℝ)) z)*(formula80 z)
private theorem node80Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node80Cross : polynomialCheck
    (((⟨#[170]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node80 : RationalCode parameterInterval formula81 :=
  ((RationalCode.constant parameterInterval (170)).mul node79)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,170]⟩ ⟨#[1]⟩ node80Denominator node80Cross

/-- Article: exact source arithmetic node 82. -/
private def formula82 (z : ℝ) : ℝ := (formula79 z)+(formula81 z)
private theorem node81Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node81Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node81 : RationalCode parameterInterval formula82 :=
  (node78.add node80)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ ⟨#[1]⟩ node81Denominator node81Cross

/-- Article: exact source arithmetic node 83. -/
private def formula83 (z : ℝ) : ℝ := ((fun _ : ℝ => ((744 : ℚ) : ℝ)) z)*(formula21 z)
private theorem node82Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node82Cross : polynomialCheck
    (((⟨#[744]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node82 : RationalCode parameterInterval formula83 :=
  ((RationalCode.constant parameterInterval (744)).mul node20)
  |>.recode ⟨#[0,0,0,0,0,0,744]⟩ ⟨#[1]⟩ node82Denominator node82Cross

/-- Article: exact source arithmetic node 84. -/
private def formula84 (z : ℝ) : ℝ := (formula82 z)+(formula83 z)
private theorem node83Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node83Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node83 : RationalCode parameterInterval formula84 :=
  (node81.add node82)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node83Denominator node83Cross

/-- Article: exact source arithmetic node 85. -/
private def formula85 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1360 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node84Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node84Cross : polynomialCheck
    (((⟨#[1360]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1360]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node84 : RationalCode parameterInterval formula85 :=
  ((RationalCode.constant parameterInterval (1360)).mul node2)
  |>.recode ⟨#[0,0,1360]⟩ ⟨#[1]⟩ node84Denominator node84Cross

/-- Article: exact source arithmetic node 86. -/
private def formula86 (z : ℝ) : ℝ := (formula84 z)+(formula85 z)
private theorem node85Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node85Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1360]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node85 : RationalCode parameterInterval formula86 :=
  (node83.add node84)
  |>.recode ⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node85Denominator node85Cross

/-- Article: exact source arithmetic node 87. -/
private def formula87 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1488 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node86Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node86Cross : polynomialCheck
    (((⟨#[1488]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node86 : RationalCode parameterInterval formula87 :=
  ((RationalCode.constant parameterInterval (1488)).mul node6)
  |>.recode ⟨#[0,0,0,0,1488]⟩ ⟨#[1]⟩ node86Denominator node86Cross

/-- Article: exact source arithmetic node 88. -/
private def formula88 (z : ℝ) : ℝ := (formula86 z)+(formula87 z)
private theorem node87Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node87Cross : polynomialCheck
    ((((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node87 : RationalCode parameterInterval formula88 :=
  (node85.add node86)
  |>.recode ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node87Denominator node87Cross

/-- Article: exact source arithmetic node 89. -/
private def formula89 (z : ℝ) : ℝ := (formula88 z)⁻¹
private theorem node88Denominator : ∀ z∈parameterInterval, aeval z (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node88Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩))=true := by kernel_decide
private def node88 : RationalCode parameterInterval formula89 :=
  (node87.inv (signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ node88Denominator node88Cross

/-- Article: exact source arithmetic node 90. -/
private def formula90 (z : ℝ) : ℝ := (formula64 z)*(formula89 z)
private theorem node89Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node89Cross : polynomialCheck
    (((⟨#[0,0,4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩)
    ((⟨#[0,0,4]⟩ : QPoly).mul ((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node89 : RationalCode parameterInterval formula90 :=
  (node63.mul node88)
  |>.recode ⟨#[0,0,4]⟩ ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ node89Denominator node89Cross

/-- Article: exact source arithmetic node 91. -/
private def formula91 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-880 : ℚ) : ℝ)) z)*(formula55 z)
private theorem node90Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node90Cross : polynomialCheck
    (((⟨#[-880]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-880]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node90 : RationalCode parameterInterval formula91 :=
  ((RationalCode.constant parameterInterval (-880)).mul node54)
  |>.recode ⟨#[0,0,0,-880]⟩ ⟨#[1]⟩ node90Denominator node90Cross

/-- Article: exact source arithmetic node 92. -/
private def formula92 (z : ℝ) : ℝ := ((fun _ : ℝ => ((240 : ℚ) : ℝ)) z)+(formula91 z)
private theorem node91Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node91Cross : polynomialCheck
    ((((⟨#[240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-880]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,0,0,-880]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node91 : RationalCode parameterInterval formula92 :=
  ((RationalCode.constant parameterInterval (240)).add node90)
  |>.recode ⟨#[240,0,0,-880]⟩ ⟨#[1]⟩ node91Denominator node91Cross

/-- Article: exact source arithmetic node 93. -/
private def formula93 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-736 : ℚ) : ℝ)) z)*(id z)
private theorem node92Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node92Cross : polynomialCheck
    (((⟨#[-736]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-736]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node92 : RationalCode parameterInterval formula93 :=
  ((RationalCode.constant parameterInterval (-736)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-736]⟩ ⟨#[1]⟩ node92Denominator node92Cross

/-- Article: exact source arithmetic node 94. -/
private def formula94 (z : ℝ) : ℝ := (formula92 z)+(formula93 z)
private theorem node93Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node93Cross : polynomialCheck
    ((((⟨#[240,0,0,-880]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-736]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,-736,0,-880]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node93 : RationalCode parameterInterval formula94 :=
  (node91.add node92)
  |>.recode ⟨#[240,-736,0,-880]⟩ ⟨#[1]⟩ node93Denominator node93Cross

/-- Article: exact source arithmetic node 95. -/
private def formula95 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-440 : ℚ) : ℝ)) z)*(formula25 z)
private theorem node94Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node94Cross : polynomialCheck
    (((⟨#[-440]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-440]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node94 : RationalCode parameterInterval formula95 :=
  ((RationalCode.constant parameterInterval (-440)).mul node24)
  |>.recode ⟨#[0,0,0,0,0,-440]⟩ ⟨#[1]⟩ node94Denominator node94Cross

/-- Article: exact source arithmetic node 96. -/
private def formula96 (z : ℝ) : ℝ := (formula94 z)+(formula95 z)
private theorem node95Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node95Cross : polynomialCheck
    ((((⟨#[240,-736,0,-880]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-440]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,-736,0,-880,0,-440]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node95 : RationalCode parameterInterval formula96 :=
  (node93.add node94)
  |>.recode ⟨#[240,-736,0,-880,0,-440]⟩ ⟨#[1]⟩ node95Denominator node95Cross

/-- Article: exact source arithmetic node 97. -/
private def formula97 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-92 : ℚ) : ℝ)) z)*(formula71 z)
private theorem node96Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node96Cross : polynomialCheck
    (((⟨#[-92]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-92]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node96 : RationalCode parameterInterval formula97 :=
  ((RationalCode.constant parameterInterval (-92)).mul node70)
  |>.recode ⟨#[0,0,0,0,0,0,0,-92]⟩ ⟨#[1]⟩ node96Denominator node96Cross

/-- Article: exact source arithmetic node 98. -/
private def formula98 (z : ℝ) : ℝ := (formula96 z)+(formula97 z)
private theorem node97Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node97Cross : polynomialCheck
    ((((⟨#[240,-736,0,-880,0,-440]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-92]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,-736,0,-880,0,-440,0,-92]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node97 : RationalCode parameterInterval formula98 :=
  (node95.add node96)
  |>.recode ⟨#[240,-736,0,-880,0,-440,0,-92]⟩ ⟨#[1]⟩ node97Denominator node97Cross

/-- Article: exact source arithmetic node 99. -/
private def formula99 (z : ℝ) : ℝ := ((fun _ : ℝ => ((15 : ℚ) : ℝ)) z)*(formula80 z)
private theorem node98Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node98Cross : polynomialCheck
    (((⟨#[15]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,15]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node98 : RationalCode parameterInterval formula99 :=
  ((RationalCode.constant parameterInterval (15)).mul node79)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,15]⟩ ⟨#[1]⟩ node98Denominator node98Cross

/-- Article: exact source arithmetic node 100. -/
private def formula100 (z : ℝ) : ℝ := (formula98 z)+(formula99 z)
private theorem node99Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node99Cross : polynomialCheck
    ((((⟨#[240,-736,0,-880,0,-440,0,-92]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,15]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,-736,0,-880,0,-440,0,-92,15]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node99 : RationalCode parameterInterval formula100 :=
  (node97.add node98)
  |>.recode ⟨#[240,-736,0,-880,0,-440,0,-92,15]⟩ ⟨#[1]⟩ node99Denominator node99Cross

/-- Article: exact source arithmetic node 101. -/
private def formula101 (z : ℝ) : ℝ := ((fun _ : ℝ => ((224 : ℚ) : ℝ)) z)*(formula21 z)
private theorem node100Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node100Cross : polynomialCheck
    (((⟨#[224]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,224]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node100 : RationalCode parameterInterval formula101 :=
  ((RationalCode.constant parameterInterval (224)).mul node20)
  |>.recode ⟨#[0,0,0,0,0,0,224]⟩ ⟨#[1]⟩ node100Denominator node100Cross

/-- Article: exact source arithmetic node 102. -/
private def formula102 (z : ℝ) : ℝ := (formula100 z)+(formula101 z)
private theorem node101Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node101Cross : polynomialCheck
    ((((⟨#[240,-736,0,-880,0,-440,0,-92,15]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,224]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,-736,0,-880,0,-440,224,-92,15]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node101 : RationalCode parameterInterval formula102 :=
  (node99.add node100)
  |>.recode ⟨#[240,-736,0,-880,0,-440,224,-92,15]⟩ ⟨#[1]⟩ node101Denominator node101Cross

/-- Article: exact source arithmetic node 103. -/
private def formula103 (z : ℝ) : ℝ := ((fun _ : ℝ => ((760 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node102Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node102Cross : polynomialCheck
    (((⟨#[760]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,760]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node102 : RationalCode parameterInterval formula103 :=
  ((RationalCode.constant parameterInterval (760)).mul node6)
  |>.recode ⟨#[0,0,0,0,760]⟩ ⟨#[1]⟩ node102Denominator node102Cross

/-- Article: exact source arithmetic node 104. -/
private def formula104 (z : ℝ) : ℝ := (formula102 z)+(formula103 z)
private theorem node103Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node103Cross : polynomialCheck
    ((((⟨#[240,-736,0,-880,0,-440,224,-92,15]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,760]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,-736,0,-880,760,-440,224,-92,15]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node103 : RationalCode parameterInterval formula104 :=
  (node101.add node102)
  |>.recode ⟨#[240,-736,0,-880,760,-440,224,-92,15]⟩ ⟨#[1]⟩ node103Denominator node103Cross

/-- Article: exact source arithmetic node 105. -/
private def formula105 (z : ℝ) : ℝ := ((fun _ : ℝ => ((896 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node104Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node104Cross : polynomialCheck
    (((⟨#[896]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,896]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node104 : RationalCode parameterInterval formula105 :=
  ((RationalCode.constant parameterInterval (896)).mul node2)
  |>.recode ⟨#[0,0,896]⟩ ⟨#[1]⟩ node104Denominator node104Cross

/-- Article: exact source arithmetic node 106. -/
private def formula106 (z : ℝ) : ℝ := (formula104 z)+(formula105 z)
private theorem node105Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node105Cross : polynomialCheck
    ((((⟨#[240,-736,0,-880,760,-440,224,-92,15]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,896]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[240,-736,896,-880,760,-440,224,-92,15]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node105 : RationalCode parameterInterval formula106 :=
  (node103.add node104)
  |>.recode ⟨#[240,-736,896,-880,760,-440,224,-92,15]⟩ ⟨#[1]⟩ node105Denominator node105Cross

/-- Article: exact source arithmetic node 107. -/
private def formula107 (z : ℝ) : ℝ := (formula90 z)*(formula106 z)
private theorem node106Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node89Denominator
private theorem node106Cross : polynomialCheck
    (((⟨#[0,0,4]⟩ : QPoly).mul (⟨#[240,-736,896,-880,760,-440,224,-92,15]⟩ : QPoly) : QPoly).mul ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩)
    ((⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ : QPoly).mul ((⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node106 : RationalCode parameterInterval formula107 :=
  (node89.mul node105)
  |>.recode ⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ ⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ node106Denominator node106Cross

/-- Article: exact coefficient representation of the independently specified meanCosine source. -/
def meanCosineCode : RationalCode parameterInterval meanCosine where
  numerator := node106.numerator
  denominator := node106.denominator
  denominator_ne := node106.denominator_ne
  exact z hz := by
    have he : meanCosine z=formula107 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node106.exact z hz)

/-- Article: exact source arithmetic node 108. -/
private def formula108 (z : ℝ) : ℝ := (formula4 z)⁻¹
private theorem node107Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node4Denominator
private theorem node107Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,0,1]⟩))=true := by kernel_decide
private def node107 : RationalCode parameterInterval formula108 :=
  (node3.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,0,1]⟩ node107Denominator node107Cross

/-- Article: exact source arithmetic node 109. -/
private def formula109 (z : ℝ) : ℝ := (formula108 z)^3
private theorem node108Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-8,0,12,0,-6,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node108Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 3 : QPoly).mul ⟨#[-8,0,12,0,-6,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[-2,0,1]⟩ 3))=true := by kernel_decide
private def node108 : RationalCode parameterInterval formula109 :=
  (node107.pow 3)
  |>.recode ⟨#[1]⟩ ⟨#[-8,0,12,0,-6,0,1]⟩ node108Denominator node108Cross

/-- Article: exact source arithmetic node 110. -/
private def formula110 (z : ℝ) : ℝ := (formula17 z)⁻¹
private theorem node109Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2,0,1]⟩ : QPoly).toPoly≠0 :=
  node17Denominator
private theorem node109Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[2,0,1]⟩))=true := by kernel_decide
private def node109 : RationalCode parameterInterval formula110 :=
  (node16.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[2,0,1]⟩ node109Denominator node109Cross

/-- Article: exact source arithmetic node 111. -/
private def formula111 (z : ℝ) : ℝ := (formula110 z)^2
private theorem node110Denominator : ∀ z∈parameterInterval, aeval z (⟨#[4,0,4,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node110Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 2 : QPoly).mul ⟨#[4,0,4,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[2,0,1]⟩ 2))=true := by kernel_decide
private def node110 : RationalCode parameterInterval formula111 :=
  (node109.pow 2)
  |>.recode ⟨#[1]⟩ ⟨#[4,0,4,0,1]⟩ node110Denominator node110Cross

/-- Article: exact source arithmetic node 112. -/
private def formula112 (z : ℝ) : ℝ := (formula109 z)*(formula111 z)
private theorem node111Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node111Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul ((⟨#[-8,0,12,0,-6,0,1]⟩ : QPoly).mul (⟨#[4,0,4,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node111 : RationalCode parameterInterval formula112 :=
  (node108.mul node110)
  |>.recode ⟨#[1]⟩ ⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩ node111Denominator node111Cross

/-- Article: exact source arithmetic node 113. -/
private def formula113 (z : ℝ) : ℝ := (formula112 z)*(formula46 z)
private theorem node112Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node111Denominator
private theorem node112Cross : polynomialCheck
    (((⟨#[1]⟩ : QPoly).mul (⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly) : QPoly).mul ⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node112 : RationalCode parameterInterval formula113 :=
  (node111.mul node45)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩ node112Denominator node112Cross

/-- Article: exact source arithmetic node 114. -/
private def formula114 (z : ℝ) : ℝ := (formula113 z)*(formula89 z)
private theorem node113Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node113Cross : polynomialCheck
    (((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[-32,0,16,0,16,0,-8,0,-2,0,1]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node113 : RationalCode parameterInterval formula114 :=
  (node112.mul node88)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ node113Denominator node113Cross

/-- Article: exact source arithmetic node 115. -/
private def formula115 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-29968 : ℚ) : ℝ)) z)*(formula21 z)
private theorem node114Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node114Cross : polynomialCheck
    (((⟨#[-29968]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,-29968]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node114 : RationalCode parameterInterval formula115 :=
  ((RationalCode.constant parameterInterval (-29968)).mul node20)
  |>.recode ⟨#[0,0,0,0,0,0,-29968]⟩ ⟨#[1]⟩ node114Denominator node114Cross

/-- Article: exact source arithmetic node 116. -/
private def formula116 (z : ℝ) : ℝ := ((fun _ : ℝ => ((640 : ℚ) : ℝ)) z)+(formula115 z)
private theorem node115Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node115Cross : polynomialCheck
    ((((⟨#[640]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,-29968]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,0,0,0,0,0,-29968]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node115 : RationalCode parameterInterval formula116 :=
  ((RationalCode.constant parameterInterval (640)).add node114)
  |>.recode ⟨#[640,0,0,0,0,0,-29968]⟩ ⟨#[1]⟩ node115Denominator node115Cross

/-- Article: exact source arithmetic node 117. -/
private def formula117 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-27680 : ℚ) : ℝ)) z)*(formula7 z)
private theorem node116Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node116Cross : polynomialCheck
    (((⟨#[-27680]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,-27680]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node116 : RationalCode parameterInterval formula117 :=
  ((RationalCode.constant parameterInterval (-27680)).mul node6)
  |>.recode ⟨#[0,0,0,0,-27680]⟩ ⟨#[1]⟩ node116Denominator node116Cross

/-- Article: exact source arithmetic node 118. -/
private def formula118 (z : ℝ) : ℝ := (formula116 z)+(formula117 z)
private theorem node117Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node117Cross : polynomialCheck
    ((((⟨#[640,0,0,0,0,0,-29968]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,-27680]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,0,0,0,-27680,0,-29968]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node117 : RationalCode parameterInterval formula118 :=
  (node115.add node116)
  |>.recode ⟨#[640,0,0,0,-27680,0,-29968]⟩ ⟨#[1]⟩ node117Denominator node117Cross

/-- Article: exact source arithmetic node 119. -/
private def formula119 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-14984 : ℚ) : ℝ)) z)*(formula80 z)
private theorem node118Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node118Cross : polynomialCheck
    (((⟨#[-14984]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,-14984]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node118 : RationalCode parameterInterval formula119 :=
  ((RationalCode.constant parameterInterval (-14984)).mul node79)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,-14984]⟩ ⟨#[1]⟩ node118Denominator node118Cross

/-- Article: exact source arithmetic node 120. -/
private def formula120 (z : ℝ) : ℝ := (formula118 z)+(formula119 z)
private theorem node119Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node119Cross : polynomialCheck
    ((((⟨#[640,0,0,0,-27680,0,-29968]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,-14984]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,0,0,0,-27680,0,-29968,0,-14984]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node119 : RationalCode parameterInterval formula120 :=
  (node117.add node118)
  |>.recode ⟨#[640,0,0,0,-27680,0,-29968,0,-14984]⟩ ⟨#[1]⟩ node119Denominator node119Cross

/-- Article: exact source arithmetic node 121. -/
private def formula121 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-3460 : ℚ) : ℝ)) z)*(formula77 z)
private theorem node120Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node120Cross : polynomialCheck
    (((⟨#[-3460]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,-3460]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node120 : RationalCode parameterInterval formula121 :=
  ((RationalCode.constant parameterInterval (-3460)).mul node76)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,-3460]⟩ ⟨#[1]⟩ node120Denominator node120Cross

/-- Article: exact source arithmetic node 122. -/
private def formula122 (z : ℝ) : ℝ := (formula120 z)+(formula121 z)
private theorem node121Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node121Cross : polynomialCheck
    ((((⟨#[640,0,0,0,-27680,0,-29968,0,-14984]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,-3460]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,0,0,0,-27680,0,-29968,0,-14984,0,-3460]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node121 : RationalCode parameterInterval formula122 :=
  (node119.add node120)
  |>.recode ⟨#[640,0,0,0,-27680,0,-29968,0,-14984,0,-3460]⟩ ⟨#[1]⟩ node121Denominator node121Cross

/-- Article: exact source arithmetic node 123. -/
private def formula123 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2176 : ℚ) : ℝ)) z)*(id z)
private theorem node122Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node122Cross : polynomialCheck
    (((⟨#[-2176]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-2176]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node122 : RationalCode parameterInterval formula123 :=
  ((RationalCode.constant parameterInterval (-2176)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-2176]⟩ ⟨#[1]⟩ node122Denominator node122Cross

/-- Article: exact source arithmetic node 124. -/
private def formula124 (z : ℝ) : ℝ := (formula122 z)+(formula123 z)
private theorem node123Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node123Cross : polynomialCheck
    ((((⟨#[640,0,0,0,-27680,0,-29968,0,-14984,0,-3460]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-2176]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node123 : RationalCode parameterInterval formula124 :=
  (node121.add node122)
  |>.recode ⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460]⟩ ⟨#[1]⟩ node123Denominator node123Cross

/-- Article: exact source arithmetic node 125. -/
private def formula125 (z : ℝ) : ℝ := (id z)^13
private theorem node124Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node124Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 13 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 13))=true := by kernel_decide
private def node124 : RationalCode parameterInterval formula125 :=
  ((RationalCode.variable parameterInterval).pow 13)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node124Denominator node124Cross

/-- Article: exact source arithmetic node 126. -/
private def formula126 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-34 : ℚ) : ℝ)) z)*(formula125 z)
private theorem node125Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node125Cross : polynomialCheck
    (((⟨#[-34]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,-34]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node125 : RationalCode parameterInterval formula126 :=
  ((RationalCode.constant parameterInterval (-34)).mul node124)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,-34]⟩ ⟨#[1]⟩ node125Denominator node125Cross

/-- Article: exact source arithmetic node 127. -/
private def formula127 (z : ℝ) : ℝ := (formula124 z)+(formula126 z)
private theorem node126Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node126Cross : polynomialCheck
    ((((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,-34]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,0,-34]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node126 : RationalCode parameterInterval formula127 :=
  (node123.add node125)
  |>.recode ⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,0,-34]⟩ ⟨#[1]⟩ node126Denominator node126Cross

/-- Article: exact source arithmetic node 128. -/
private def formula128 (z : ℝ) : ℝ := (id z)^14
private theorem node127Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node127Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 14 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 14))=true := by kernel_decide
private def node127 : RationalCode parameterInterval formula128 :=
  ((RationalCode.variable parameterInterval).pow 14)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node127Denominator node127Cross

/-- Article: exact source arithmetic node 129. -/
private def formula129 (z : ℝ) : ℝ := ((fun _ : ℝ => ((5 : ℚ) : ℝ)) z)*(formula128 z)
private theorem node128Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node128Cross : polynomialCheck
    (((⟨#[5]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node128 : RationalCode parameterInterval formula129 :=
  ((RationalCode.constant parameterInterval (5)).mul node127)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]⟩ ⟨#[1]⟩ node128Denominator node128Cross

/-- Article: exact source arithmetic node 130. -/
private def formula130 (z : ℝ) : ℝ := (formula127 z)+(formula129 z)
private theorem node129Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node129Cross : polynomialCheck
    ((((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,0,-34]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,0,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node129 : RationalCode parameterInterval formula130 :=
  (node126.add node128)
  |>.recode ⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,0,-34,5]⟩ ⟨#[1]⟩ node129Denominator node129Cross

/-- Article: exact source arithmetic node 131. -/
private def formula131 (z : ℝ) : ℝ := (id z)^12
private theorem node130Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node130Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 12 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 12))=true := by kernel_decide
private def node130 : RationalCode parameterInterval formula131 :=
  ((RationalCode.variable parameterInterval).pow 12)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node130Denominator node130Cross

/-- Article: exact source arithmetic node 132. -/
private def formula132 (z : ℝ) : ℝ := ((fun _ : ℝ => ((42 : ℚ) : ℝ)) z)*(formula131 z)
private theorem node131Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node131Cross : polynomialCheck
    (((⟨#[42]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,42]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node131 : RationalCode parameterInterval formula132 :=
  ((RationalCode.constant parameterInterval (42)).mul node130)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,42]⟩ ⟨#[1]⟩ node131Denominator node131Cross

/-- Article: exact source arithmetic node 133. -/
private def formula133 (z : ℝ) : ℝ := (formula130 z)+(formula132 z)
private theorem node132Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node132Cross : polynomialCheck
    ((((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,0,-34,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,42]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,42,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node132 : RationalCode parameterInterval formula133 :=
  (node129.add node131)
  |>.recode ⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,42,-34,5]⟩ ⟨#[1]⟩ node132Denominator node132Cross

/-- Article: exact source arithmetic node 134. -/
private def formula134 (z : ℝ) : ℝ := (id z)^11
private theorem node133Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node133Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 11 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 11))=true := by kernel_decide
private def node133 : RationalCode parameterInterval formula134 :=
  ((RationalCode.variable parameterInterval).pow 11)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node133Denominator node133Cross

/-- Article: exact source arithmetic node 135. -/
private def formula135 (z : ℝ) : ℝ := ((fun _ : ℝ => ((648 : ℚ) : ℝ)) z)*(formula134 z)
private theorem node134Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node134Cross : polynomialCheck
    (((⟨#[648]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,648]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node134 : RationalCode parameterInterval formula135 :=
  ((RationalCode.constant parameterInterval (648)).mul node133)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,648]⟩ ⟨#[1]⟩ node134Denominator node134Cross

/-- Article: exact source arithmetic node 136. -/
private def formula136 (z : ℝ) : ℝ := (formula133 z)+(formula135 z)
private theorem node135Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node135Cross : polynomialCheck
    ((((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,0,42,-34,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,0,648]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,648,42,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node135 : RationalCode parameterInterval formula136 :=
  (node132.add node134)
  |>.recode ⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,648,42,-34,5]⟩ ⟨#[1]⟩ node135Denominator node135Cross

/-- Article: exact source arithmetic node 137. -/
private def formula137 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1344 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node136Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node136Cross : polynomialCheck
    (((⟨#[1344]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1344]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node136 : RationalCode parameterInterval formula137 :=
  ((RationalCode.constant parameterInterval (1344)).mul node2)
  |>.recode ⟨#[0,0,1344]⟩ ⟨#[1]⟩ node136Denominator node136Cross

/-- Article: exact source arithmetic node 138. -/
private def formula138 (z : ℝ) : ℝ := (formula136 z)+(formula137 z)
private theorem node137Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node137Cross : polynomialCheck
    ((((⟨#[640,-2176,0,0,-27680,0,-29968,0,-14984,0,-3460,648,42,-34,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1344]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,1344,0,-27680,0,-29968,0,-14984,0,-3460,648,42,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node137 : RationalCode parameterInterval formula138 :=
  (node135.add node136)
  |>.recode ⟨#[640,-2176,1344,0,-27680,0,-29968,0,-14984,0,-3460,648,42,-34,5]⟩ ⟨#[1]⟩ node137Denominator node137Cross

/-- Article: exact source arithmetic node 139. -/
private def formula139 (z : ℝ) : ℝ := ((fun _ : ℝ => ((8296 : ℚ) : ℝ)) z)*(formula74 z)
private theorem node138Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node138Cross : polynomialCheck
    (((⟨#[8296]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,8296]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node138 : RationalCode parameterInterval formula139 :=
  ((RationalCode.constant parameterInterval (8296)).mul node73)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,8296]⟩ ⟨#[1]⟩ node138Denominator node138Cross

/-- Article: exact source arithmetic node 140. -/
private def formula140 (z : ℝ) : ℝ := (formula138 z)+(formula139 z)
private theorem node139Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node139Cross : polynomialCheck
    ((((⟨#[640,-2176,1344,0,-27680,0,-29968,0,-14984,0,-3460,648,42,-34,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,8296]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,1344,0,-27680,0,-29968,0,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node139 : RationalCode parameterInterval formula140 :=
  (node137.add node138)
  |>.recode ⟨#[640,-2176,1344,0,-27680,0,-29968,0,-14984,8296,-3460,648,42,-34,5]⟩ ⟨#[1]⟩ node139Denominator node139Cross

/-- Article: exact source arithmetic node 141. -/
private def formula141 (z : ℝ) : ℝ := ((fun _ : ℝ => ((10368 : ℚ) : ℝ)) z)*(formula55 z)
private theorem node140Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node140Cross : polynomialCheck
    (((⟨#[10368]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,10368]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node140 : RationalCode parameterInterval formula141 :=
  ((RationalCode.constant parameterInterval (10368)).mul node54)
  |>.recode ⟨#[0,0,0,10368]⟩ ⟨#[1]⟩ node140Denominator node140Cross

/-- Article: exact source arithmetic node 142. -/
private def formula142 (z : ℝ) : ℝ := (formula140 z)+(formula141 z)
private theorem node141Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node141Cross : polynomialCheck
    ((((⟨#[640,-2176,1344,0,-27680,0,-29968,0,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,10368]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,1344,10368,-27680,0,-29968,0,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node141 : RationalCode parameterInterval formula142 :=
  (node139.add node140)
  |>.recode ⟨#[640,-2176,1344,10368,-27680,0,-29968,0,-14984,8296,-3460,648,42,-34,5]⟩ ⟨#[1]⟩ node141Denominator node141Cross

/-- Article: exact source arithmetic node 143. -/
private def formula143 (z : ℝ) : ℝ := ((fun _ : ℝ => ((23616 : ℚ) : ℝ)) z)*(formula71 z)
private theorem node142Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node142Cross : polynomialCheck
    (((⟨#[23616]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,23616]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node142 : RationalCode parameterInterval formula143 :=
  ((RationalCode.constant parameterInterval (23616)).mul node70)
  |>.recode ⟨#[0,0,0,0,0,0,0,23616]⟩ ⟨#[1]⟩ node142Denominator node142Cross

/-- Article: exact source arithmetic node 144. -/
private def formula144 (z : ℝ) : ℝ := (formula142 z)+(formula143 z)
private theorem node143Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node143Cross : polynomialCheck
    ((((⟨#[640,-2176,1344,10368,-27680,0,-29968,0,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,23616]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,1344,10368,-27680,0,-29968,23616,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node143 : RationalCode parameterInterval formula144 :=
  (node141.add node142)
  |>.recode ⟨#[640,-2176,1344,10368,-27680,0,-29968,23616,-14984,8296,-3460,648,42,-34,5]⟩ ⟨#[1]⟩ node143Denominator node143Cross

/-- Article: exact source arithmetic node 145. -/
private def formula145 (z : ℝ) : ℝ := ((fun _ : ℝ => ((33184 : ℚ) : ℝ)) z)*(formula25 z)
private theorem node144Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node144Cross : polynomialCheck
    (((⟨#[33184]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,33184]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node144 : RationalCode parameterInterval formula145 :=
  ((RationalCode.constant parameterInterval (33184)).mul node24)
  |>.recode ⟨#[0,0,0,0,0,33184]⟩ ⟨#[1]⟩ node144Denominator node144Cross

/-- Article: exact source arithmetic node 146. -/
private def formula146 (z : ℝ) : ℝ := (formula144 z)+(formula145 z)
private theorem node145Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node145Cross : polynomialCheck
    ((((⟨#[640,-2176,1344,10368,-27680,0,-29968,23616,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,33184]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[640,-2176,1344,10368,-27680,33184,-29968,23616,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node145 : RationalCode parameterInterval formula146 :=
  (node143.add node144)
  |>.recode ⟨#[640,-2176,1344,10368,-27680,33184,-29968,23616,-14984,8296,-3460,648,42,-34,5]⟩ ⟨#[1]⟩ node145Denominator node145Cross

/-- Article: exact source arithmetic node 147. -/
private def formula147 (z : ℝ) : ℝ := (formula114 z)*(formula146 z)
private theorem node146Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  node113Denominator
private theorem node146Cross : polynomialCheck
    (((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[640,-2176,1344,10368,-27680,33184,-29968,23616,-14984,8296,-3460,648,42,-34,5]⟩ : QPoly) : QPoly).mul ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩)
    ((⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ : QPoly).mul ((⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node146 : RationalCode parameterInterval formula147 :=
  (node113.mul node145)
  |>.recode ⟨#[5120,-32768,86016,-48128,-340736,1217024,-2326528,3164928,-3386496,3008896,-2288128,1504448,-846624,395616,-145408,38032,-5324,-376,336,-64,5]⟩ ⟨#[-5120,22528,-40960,35840,-23296,9216,20480,-28160,19072,-13312,0,6656,-4768,3520,-1280,-288,364,-280,160,-44,5]⟩ node146Denominator node146Cross

/-- Article: exact coefficient representation of the independently specified d source. -/
def dCode : RationalCode parameterInterval d where
  numerator := node146.numerator
  denominator := node146.denominator
  denominator_ne := node146.denominator_ne
  exact z hz := by
    have he : d z=formula147 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node146.exact z hz)

/-- Article: exact source arithmetic node 148. -/
private def formula148 (z : ℝ) : ℝ := ((fun _ : ℝ => ((32 : ℚ) : ℝ)) z)*(formula3 z)
private theorem node147Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node147Cross : polynomialCheck
    (((⟨#[32]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node147 : RationalCode parameterInterval formula148 :=
  ((RationalCode.constant parameterInterval (32)).mul node2)
  |>.recode ⟨#[0,0,32]⟩ ⟨#[1]⟩ node147Denominator node147Cross

/-- Article: exact source arithmetic node 149. -/
private def formula149 (z : ℝ) : ℝ := (formula17 z)⁻¹
private theorem node148Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2,0,1]⟩ : QPoly).toPoly≠0 :=
  node17Denominator
private theorem node148Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[2,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[2,0,1]⟩))=true := by kernel_decide
private def node148 : RationalCode parameterInterval formula149 :=
  (node16.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[2,0,1]⟩ node148Denominator node148Cross

/-- Article: exact source arithmetic node 150. -/
private def formula150 (z : ℝ) : ℝ := (formula149 z)^3
private theorem node149Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,12,0,6,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node149Cross : polynomialCheck
    ((polynomialPower ⟨#[1]⟩ 3 : QPoly).mul ⟨#[8,0,12,0,6,0,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (polynomialPower ⟨#[2,0,1]⟩ 3))=true := by kernel_decide
private def node149 : RationalCode parameterInterval formula150 :=
  (node148.pow 3)
  |>.recode ⟨#[1]⟩ ⟨#[8,0,12,0,6,0,1]⟩ node149Denominator node149Cross

/-- Article: exact source arithmetic node 151. -/
private def formula151 (z : ℝ) : ℝ := (formula148 z)*(formula150 z)
private theorem node150Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,12,0,6,0,1]⟩ : QPoly).toPoly≠0 :=
  node149Denominator
private theorem node150Cross : polynomialCheck
    (((⟨#[0,0,32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[8,0,12,0,6,0,1]⟩)
    ((⟨#[0,0,32]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,12,0,6,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node150 : RationalCode parameterInterval formula151 :=
  (node147.mul node149)
  |>.recode ⟨#[0,0,32]⟩ ⟨#[8,0,12,0,6,0,1]⟩ node150Denominator node150Cross

/-- Article: exact source arithmetic node 152. -/
private def formula152 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula3 z)
private theorem node151Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node151Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node151 : RationalCode parameterInterval formula152 :=
  ((RationalCode.constant parameterInterval (-2)).add node2)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node151Denominator node151Cross

/-- Article: exact source arithmetic node 153. -/
private def formula153 (z : ℝ) : ℝ := (formula152 z)+(formula13 z)
private theorem node152Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node152Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,-2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node152 : RationalCode parameterInterval formula153 :=
  (node151.add node12)
  |>.recode ⟨#[-2,-2,1]⟩ ⟨#[1]⟩ node152Denominator node152Cross

/-- Article: exact source arithmetic node 154. -/
private def formula154 (z : ℝ) : ℝ := (formula153 z)⁻¹
private theorem node153Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,-2,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node153Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,-2,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,-2,1]⟩))=true := by kernel_decide
private def node153 : RationalCode parameterInterval formula154 :=
  (node152.inv (signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,-2,1]⟩ node153Denominator node153Cross

/-- Article: exact source arithmetic node 155. -/
private def formula155 (z : ℝ) : ℝ := (formula151 z)*(formula154 z)
private theorem node154Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-16,-16,-16,-24,0,-12,4,-2,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node154Cross : polynomialCheck
    (((⟨#[0,0,32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[-16,-16,-16,-24,0,-12,4,-2,1]⟩)
    ((⟨#[0,0,32]⟩ : QPoly).mul ((⟨#[8,0,12,0,6,0,1]⟩ : QPoly).mul (⟨#[-2,-2,1]⟩ : QPoly)))=true := by kernel_decide
private def node154 : RationalCode parameterInterval formula155 :=
  (node150.mul node153)
  |>.recode ⟨#[0,0,32]⟩ ⟨#[-16,-16,-16,-24,0,-12,4,-2,1]⟩ node154Denominator node154Cross

/-- Article: exact source arithmetic node 156. -/
private def formula156 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula3 z)
private theorem node155Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node155Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node155 : RationalCode parameterInterval formula156 :=
  ((RationalCode.constant parameterInterval (-2)).add node2)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node155Denominator node155Cross

/-- Article: exact source arithmetic node 157. -/
private def formula157 (z : ℝ) : ℝ := (formula156 z)+(formula35 z)
private theorem node156Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node156Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node156 : RationalCode parameterInterval formula157 :=
  (node155.add node34)
  |>.recode ⟨#[-2,2,1]⟩ ⟨#[1]⟩ node156Denominator node156Cross

/-- Article: exact source arithmetic node 158. -/
private def formula158 (z : ℝ) : ℝ := (formula157 z)⁻¹
private theorem node157Denominator : ∀ z∈parameterInterval, aeval z (⟨#[-2,2,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node157Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[-2,2,1]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[-2,2,1]⟩))=true := by kernel_decide
private def node157 : RationalCode parameterInterval formula158 :=
  (node156.inv (signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[-2,2,1]⟩ node157Denominator node157Cross

/-- Article: exact source arithmetic node 159. -/
private def formula159 (z : ℝ) : ℝ := (formula155 z)*(formula158 z)
private theorem node158Denominator : ∀ z∈parameterInterval, aeval z (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node158Cross : polynomialCheck
    (((⟨#[0,0,32]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩)
    ((⟨#[0,0,32]⟩ : QPoly).mul ((⟨#[-16,-16,-16,-24,0,-12,4,-2,1]⟩ : QPoly).mul (⟨#[-2,2,1]⟩ : QPoly)))=true := by kernel_decide
private def node158 : RationalCode parameterInterval formula159 :=
  (node154.mul node157)
  |>.recode ⟨#[0,0,32]⟩ ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ node158Denominator node158Cross

/-- Article: exact source arithmetic node 160. -/
private def formula160 (z : ℝ) : ℝ := (formula159 z)*(formula14 z)
private theorem node159Denominator : ∀ z∈parameterInterval, aeval z (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node158Denominator
private theorem node159Cross : polynomialCheck
    (((⟨#[0,0,32]⟩ : QPoly).mul (⟨#[2,-2,1]⟩ : QPoly) : QPoly).mul ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩)
    ((⟨#[0,0,64,-64,32]⟩ : QPoly).mul ((⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node159 : RationalCode parameterInterval formula160 :=
  (node158.mul node13)
  |>.recode ⟨#[0,0,64,-64,32]⟩ ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ node159Denominator node159Cross

/-- Article: exact source arithmetic node 161. -/
private def formula161 (z : ℝ) : ℝ := ((fun _ : ℝ => ((4 : ℚ) : ℝ)) z)+(formula7 z)
private theorem node160Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node160Cross : polynomialCheck
    ((((⟨#[4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[4,0,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node160 : RationalCode parameterInterval formula161 :=
  ((RationalCode.constant parameterInterval (4)).add node6)
  |>.recode ⟨#[4,0,0,0,1]⟩ ⟨#[1]⟩ node160Denominator node160Cross

/-- Article: exact source arithmetic node 162. -/
private def formula162 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-4 : ℚ) : ℝ)) z)*(id z)
private theorem node161Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node161Cross : polynomialCheck
    (((⟨#[-4]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-4]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node161 : RationalCode parameterInterval formula162 :=
  ((RationalCode.constant parameterInterval (-4)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-4]⟩ ⟨#[1]⟩ node161Denominator node161Cross

/-- Article: exact source arithmetic node 163. -/
private def formula163 (z : ℝ) : ℝ := (formula161 z)+(formula162 z)
private theorem node162Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node162Cross : polynomialCheck
    ((((⟨#[4,0,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-4]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[4,-4,0,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node162 : RationalCode parameterInterval formula163 :=
  (node160.add node161)
  |>.recode ⟨#[4,-4,0,0,1]⟩ ⟨#[1]⟩ node162Denominator node162Cross

/-- Article: exact source arithmetic node 164. -/
private def formula164 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)*(formula55 z)
private theorem node163Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node163Cross : polynomialCheck
    (((⟨#[-2]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node163 : RationalCode parameterInterval formula164 :=
  ((RationalCode.constant parameterInterval (-2)).mul node54)
  |>.recode ⟨#[0,0,0,-2]⟩ ⟨#[1]⟩ node163Denominator node163Cross

/-- Article: exact source arithmetic node 165. -/
private def formula165 (z : ℝ) : ℝ := (formula163 z)+(formula164 z)
private theorem node164Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node2Denominator
private theorem node164Cross : polynomialCheck
    ((((⟨#[4,-4,0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[4,-4,0,-2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node164 : RationalCode parameterInterval formula165 :=
  (node162.add node163)
  |>.recode ⟨#[4,-4,0,-2,1]⟩ ⟨#[1]⟩ node164Denominator node164Cross

/-- Article: exact source arithmetic node 166. -/
private def formula166 (z : ℝ) : ℝ := (formula160 z)*(formula165 z)
private theorem node165Denominator : ∀ z∈parameterInterval, aeval z (⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node158Denominator
private theorem node165Cross : polynomialCheck
    (((⟨#[0,0,64,-64,32]⟩ : QPoly).mul (⟨#[4,-4,0,-2,1]⟩ : QPoly) : QPoly).mul ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩)
    ((⟨#[0,0,256,-512,384,-256,192,-128,32]⟩ : QPoly).mul ((⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
private def node165 : RationalCode parameterInterval formula166 :=
  (node159.mul node164)
  |>.recode ⟨#[0,0,256,-512,384,-256,192,-128,32]⟩ ⟨#[32,0,-16,0,-64,0,-32,0,-2,0,1]⟩ node165Denominator node165Cross

/-- Article: exact coefficient representation of the independently specified slope source. -/
def slopeCode : RationalCode parameterInterval slope where
  numerator := node165.numerator
  denominator := node165.denominator
  denominator_ne := node165.denominator_ne
  exact z hz := by
    have he : slope z=formula166 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154,formula155,formula156,formula157,formula158,formula159,formula160,formula161,formula162,formula163,formula164,formula165,formula166,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node165.exact z hz)

/-- Article: exact source arithmetic node 167. -/
private def formula167 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1 : ℚ) : ℝ)) z)+(atomB z)
private theorem node166Denominator : ∀ z∈parameterInterval, aeval z (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).toPoly≠0 :=
  node51Denominator
private theorem node166Cross : polynomialCheck
    ((((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)).add ((⟨#[0,-24,40,-32,20,-6]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[8,0,-4,0,-2,0,1]⟩)
    ((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node166 : RationalCode parameterInterval formula167 :=
  ((RationalCode.constant parameterInterval (1)).add atomBCode)
  |>.recode ⟨#[8,-24,36,-32,18,-6,1]⟩ ⟨#[8,0,-4,0,-2,0,1]⟩ node166Denominator node166Cross

/-- Article: exact source arithmetic node 168. -/
private def formula168 (z : ℝ) : ℝ := (u z)^2
private theorem node167Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := 1) (by kernel_decide)
private theorem node167Cross : polynomialCheck
    ((polynomialPower ⟨#[4,-8,8,-4,1]⟩ 2 : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly).mul (polynomialPower ⟨#[-4,0,0,0,1]⟩ 2))=true := by kernel_decide
private def node167 : RationalCode parameterInterval formula168 :=
  (uCode.pow 2)
  |>.recode ⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node167Denominator node167Cross

/-- Article: exact source arithmetic node 169. -/
private def formula169 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-1 : ℚ) : ℝ)) z)*(formula168 z)
private theorem node168Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node167Denominator
private theorem node168Cross : polynomialCheck
    (((⟨#[-1]⟩ : QPoly).mul (⟨#[16,-64,128,-160,136,-80,32,-8,1]⟩ : QPoly) : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[-16,64,-128,160,-136,80,-32,8,-1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node168 : RationalCode parameterInterval formula169 :=
  ((RationalCode.constant parameterInterval (-1)).mul node167)
  |>.recode ⟨#[-16,64,-128,160,-136,80,-32,8,-1]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node168Denominator node168Cross

/-- Article: exact source arithmetic node 170. -/
private def formula170 (z : ℝ) : ℝ := (formula167 z)+(formula169 z)
private theorem node169Denominator : ∀ z∈parameterInterval, aeval z (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).toPoly≠0 :=
  node167Denominator
private theorem node169Cross : polynomialCheck
    ((((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)).add ((⟨#[-16,64,-128,160,-136,80,-32,8,-1]⟩ : QPoly).mul (⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[16,0,0,0,-8,0,0,0,1]⟩)
    ((⟨#[0,16,-48,72,-64,36,-12,2]⟩ : QPoly).mul ((⟨#[8,0,-4,0,-2,0,1]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)))=true := by kernel_decide
private def node169 : RationalCode parameterInterval formula170 :=
  (node166.add node168)
  |>.recode ⟨#[0,16,-48,72,-64,36,-12,2]⟩ ⟨#[16,0,0,0,-8,0,0,0,1]⟩ node169Denominator node169Cross

/-- Article: exact source arithmetic node 171. -/
private def formula171 (z : ℝ) : ℝ := (atomA z)*(meanCosine z)
private theorem node170Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node170Cross : polynomialCheck
    (((⟨#[8,-24,36,-32,18,-6,1]⟩ : QPoly).mul (⟨#[0,0,960,-2944,3584,-3520,3040,-1760,896,-368,60]⟩ : QPoly) : QPoly).mul ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩)
    ((⟨#[0,3840,-23296,66944,-125440,174656,-193600,177312,-136448,88656,-48400,21832,-7840,2092,-364,30]⟩ : QPoly).mul ((⟨#[0,-8,0,0,0,2]⟩ : QPoly).mul (⟨#[-320,1408,-2560,2240,-1616,1280,0,-640,404,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node170 : RationalCode parameterInterval formula171 :=
  (atomACode.mul meanCosineCode)
  |>.recode ⟨#[0,3840,-23296,66944,-125440,174656,-193600,177312,-136448,88656,-48400,21832,-7840,2092,-364,30]⟩ ⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ node170Denominator node170Cross

/-- Article: exact source arithmetic node 172. -/
private def formula172 (z : ℝ) : ℝ := (formula170 z)+(formula171 z)
private theorem node171Denominator : ∀ z∈parameterInterval, aeval z (⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
private theorem node171Cross : polynomialCheck
    ((((⟨#[0,16,-48,72,-64,36,-12,2]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)).add ((⟨#[0,3840,-23296,66944,-125440,174656,-193600,177312,-136448,88656,-48400,21832,-7840,2092,-364,30]⟩ : QPoly).mul (⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly)) : QPoly).mul ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩)
    ((⟨#[0,10240,-65536,204800,-423936,659456,-826368,866304,-773120,590592,-386560,216576,-103296,41216,-13248,3200,-512,40]⟩ : QPoly).mul ((⟨#[16,0,0,0,-8,0,0,0,1]⟩ : QPoly).mul (⟨#[1280,-5632,10240,-8960,6144,-3712,-2560,4800,-3232,2400,-640,-464,384,-280,160,-44,5]⟩ : QPoly)))=true := by kernel_decide
private def node171 : RationalCode parameterInterval formula172 :=
  (node169.add node170)
  |>.recode ⟨#[0,10240,-65536,204800,-423936,659456,-826368,866304,-773120,590592,-386560,216576,-103296,41216,-13248,3200,-512,40]⟩ ⟨#[2560,-11264,21760,-23552,22528,-16384,1024,5888,-9024,9600,-4512,1472,128,-1024,704,-368,170,-44,5]⟩ node171Denominator node171Cross

/-- Article: exact coefficient representation of the independently specified meanGap source. -/
def meanGapCode : RationalCode parameterInterval meanGap where
  numerator := node171.numerator
  denominator := node171.denominator
  denominator_ne := node171.denominator_ne
  exact z hz := by
    have he : meanGap z=formula172 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154,formula155,formula156,formula157,formula158,formula159,formula160,formula161,formula162,formula163,formula164,formula165,formula166,formula167,formula168,formula169,formula170,formula171,formula172,G,u,W,atomA,atomB,meanCosine,d,meanGap,slope,qMinus,qPlus,rMinus,rPlus,K6,F8,M10,D14,eMinus,ePlus,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node171.exact z hz)

end
end polyak.Boundary.P2
