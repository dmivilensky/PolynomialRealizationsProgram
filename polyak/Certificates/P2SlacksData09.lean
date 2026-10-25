import polyak.Certificates.P2SlacksData08

namespace polyak.Boundary.P2
noncomputable section
open LeanCert.Engine Polynomial
/-- Article: exact source arithmetic node 721. -/
def formula721 (z : ℝ) : ℝ := ((fun _ : ℝ => ((170 : ℚ) : ℝ)) z)*(formula720 z)
theorem node720Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node720Cross : polynomialCheck
    (((⟨#[170]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node720 : RationalCode parameterInterval formula721 :=
  ((RationalCode.constant parameterInterval (170)).mul node719)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,170]⟩ ⟨#[1]⟩ node720Denominator node720Cross

/-- Article: exact source arithmetic node 722. -/
def formula722 (z : ℝ) : ℝ := (formula719 z)+(formula721 z)
theorem node721Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node721Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,0,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,170]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node721 : RationalCode parameterInterval formula722 :=
  (node718.add node720)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ ⟨#[1]⟩ node721Denominator node721Cross

/-- Article: exact source arithmetic node 723. -/
def formula723 (z : ℝ) : ℝ := (id z)^6
theorem node722Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node722Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 6 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 6))=true := by kernel_decide
def node722 : RationalCode parameterInterval formula723 :=
  ((RationalCode.variable parameterInterval).pow 6)
  |>.recode ⟨#[0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node722Denominator node722Cross

/-- Article: exact source arithmetic node 724. -/
def formula724 (z : ℝ) : ℝ := ((fun _ : ℝ => ((744 : ℚ) : ℝ)) z)*(formula723 z)
theorem node723Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node723Cross : polynomialCheck
    (((⟨#[744]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node723 : RationalCode parameterInterval formula724 :=
  ((RationalCode.constant parameterInterval (744)).mul node722)
  |>.recode ⟨#[0,0,0,0,0,0,744]⟩ ⟨#[1]⟩ node723Denominator node723Cross

/-- Article: exact source arithmetic node 725. -/
def formula725 (z : ℝ) : ℝ := (formula722 z)+(formula724 z)
theorem node724Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node724Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,0,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,744]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node724 : RationalCode parameterInterval formula725 :=
  (node721.add node723)
  |>.recode ⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node724Denominator node724Cross

/-- Article: exact source arithmetic node 726. -/
def formula726 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1360 : ℚ) : ℝ)) z)*(formula689 z)
theorem node725Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node725Cross : polynomialCheck
    (((⟨#[1360]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,1360]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node725 : RationalCode parameterInterval formula726 :=
  ((RationalCode.constant parameterInterval (1360)).mul node688)
  |>.recode ⟨#[0,0,1360]⟩ ⟨#[1]⟩ node725Denominator node725Cross

/-- Article: exact source arithmetic node 727. -/
def formula727 (z : ℝ) : ℝ := (formula725 z)+(formula726 z)
theorem node726Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node726Cross : polynomialCheck
    ((((⟨#[160,-704,0,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1360]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node726 : RationalCode parameterInterval formula727 :=
  (node724.add node725)
  |>.recode ⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node726Denominator node726Cross

/-- Article: exact source arithmetic node 728. -/
def formula728 (z : ℝ) : ℝ := (id z)^4
theorem node727Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node727Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 4 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 4))=true := by kernel_decide
def node727 : RationalCode parameterInterval formula728 :=
  ((RationalCode.variable parameterInterval).pow 4)
  |>.recode ⟨#[0,0,0,0,1]⟩ ⟨#[1]⟩ node727Denominator node727Cross

/-- Article: exact source arithmetic node 729. -/
def formula729 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1488 : ℚ) : ℝ)) z)*(formula728 z)
theorem node728Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node728Cross : polynomialCheck
    (((⟨#[1488]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node728 : RationalCode parameterInterval formula729 :=
  ((RationalCode.constant parameterInterval (1488)).mul node727)
  |>.recode ⟨#[0,0,0,0,1488]⟩ ⟨#[1]⟩ node728Denominator node728Cross

/-- Article: exact source arithmetic node 730. -/
def formula730 (z : ℝ) : ℝ := (formula727 z)+(formula729 z)
theorem node729Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node729Cross : polynomialCheck
    ((((⟨#[160,-704,1360,-1472,0,-1376,744,-368,170,-44,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,1488]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node729 : RationalCode parameterInterval formula730 :=
  (node726.add node728)
  |>.recode ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ ⟨#[1]⟩ node729Denominator node729Cross

/-- Article: exact source arithmetic node 731. -/
def formula731 (z : ℝ) : ℝ := (formula730 z)⁻¹
theorem node730Denominator : ∀ z∈parameterInterval, aeval z (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly).toPoly≠0 :=
  signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)
theorem node730Cross : polynomialCheck
    ((⟨#[1]⟩ : QPoly).mul ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩)
    ((⟨#[1]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩))=true := by kernel_decide
def node730 : RationalCode parameterInterval formula731 :=
  (node729.inv (signedPolynomialCheck_ne_zero (sg := -1) (by kernel_decide)))
  |>.recode ⟨#[1]⟩ ⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ node730Denominator node730Cross

/-- Article: exact source arithmetic node 732. -/
def formula732 (z : ℝ) : ℝ := (formula702 z)*(formula731 z)
theorem node731Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node281Denominator
theorem node731Cross : polynomialCheck
    (((⟨#[-8,24,-36,32,-18,6,-1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[-8,24,-36,32,-18,6,-1]⟩ : QPoly).mul ((⟨#[0,0,-4096,0,10240,0,-8192,0,0,0,3584,0,-1792,0,0,0,256,0,-80,0,8]⟩ : QPoly).mul (⟨#[160,-704,1360,-1472,1488,-1376,744,-368,170,-44,5]⟩ : QPoly)))=true := by kernel_decide
def node731 : RationalCode parameterInterval formula732 :=
  (node701.mul node730)
  |>.recode ⟨#[-8,24,-36,32,-18,6,-1]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node731Denominator node731Cross

/-- Article: exact source arithmetic node 733. -/
def formula733 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula689 z)
theorem node732Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node732Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node732 : RationalCode parameterInterval formula733 :=
  ((RationalCode.constant parameterInterval (-2)).add node688)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node732Denominator node732Cross

/-- Article: exact source arithmetic node 734. -/
def formula734 (z : ℝ) : ℝ := (formula733 z)+(formula699 z)
theorem node733Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node733Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,-2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node733 : RationalCode parameterInterval formula734 :=
  (node732.add node698)
  |>.recode ⟨#[-2,-2,1]⟩ ⟨#[1]⟩ node733Denominator node733Cross

/-- Article: exact source arithmetic node 735. -/
def formula735 (z : ℝ) : ℝ := (formula732 z)*(formula734 z)
theorem node734Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node281Denominator
theorem node734Cross : polynomialCheck
    (((⟨#[-8,24,-36,32,-18,6,-1]⟩ : QPoly).mul (⟨#[-2,-2,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[16,-32,16,32,-64,56,-28,8,-1]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node734 : RationalCode parameterInterval formula735 :=
  (node731.mul node733)
  |>.recode ⟨#[16,-32,16,32,-64,56,-28,8,-1]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node734Denominator node734Cross

/-- Article: exact source arithmetic node 736. -/
def formula736 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2 : ℚ) : ℝ)) z)+(formula689 z)
theorem node735Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node735Cross : polynomialCheck
    ((((⟨#[-2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,0,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node735 : RationalCode parameterInterval formula736 :=
  ((RationalCode.constant parameterInterval (-2)).add node688)
  |>.recode ⟨#[-2,0,1]⟩ ⟨#[1]⟩ node735Denominator node735Cross

/-- Article: exact source arithmetic node 737. -/
def formula737 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2 : ℚ) : ℝ)) z)*(id z)
theorem node736Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node736Cross : polynomialCheck
    (((⟨#[2]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,2]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node736 : RationalCode parameterInterval formula737 :=
  ((RationalCode.constant parameterInterval (2)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,2]⟩ ⟨#[1]⟩ node736Denominator node736Cross

/-- Article: exact source arithmetic node 738. -/
def formula738 (z : ℝ) : ℝ := (formula736 z)+(formula737 z)
theorem node737Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node737Cross : polynomialCheck
    ((((⟨#[-2,0,1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,2]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[-2,2,1]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node737 : RationalCode parameterInterval formula738 :=
  (node735.add node736)
  |>.recode ⟨#[-2,2,1]⟩ ⟨#[1]⟩ node737Denominator node737Cross

/-- Article: exact source arithmetic node 739. -/
def formula739 (z : ℝ) : ℝ := (formula735 z)*(formula738 z)
theorem node738Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node281Denominator
theorem node738Cross : polynomialCheck
    (((⟨#[16,-32,16,32,-64,56,-28,8,-1]⟩ : QPoly).mul (⟨#[-2,2,1]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[-32,96,-80,-64,208,-208,104,-16,-10,6,-1]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node738 : RationalCode parameterInterval formula739 :=
  (node734.mul node737)
  |>.recode ⟨#[-32,96,-80,-64,208,-208,104,-16,-10,6,-1]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node738Denominator node738Cross

/-- Article: exact source arithmetic node 740. -/
def formula740 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2240 : ℚ) : ℝ)) z)*(formula706 z)
theorem node739Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node739Cross : polynomialCheck
    (((⟨#[-2240]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node739 : RationalCode parameterInterval formula740 :=
  ((RationalCode.constant parameterInterval (-2240)).mul node705)
  |>.recode ⟨#[0,0,0,0,0,-2240]⟩ ⟨#[1]⟩ node739Denominator node739Cross

/-- Article: exact source arithmetic node 741. -/
def formula741 (z : ℝ) : ℝ := ((fun _ : ℝ => ((160 : ℚ) : ℝ)) z)+(formula740 z)
theorem node740Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node740Cross : polynomialCheck
    ((((⟨#[160]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,0,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node740 : RationalCode parameterInterval formula741 :=
  ((RationalCode.constant parameterInterval (160)).add node739)
  |>.recode ⟨#[160,0,0,0,0,-2240]⟩ ⟨#[1]⟩ node740Denominator node740Cross

/-- Article: exact source arithmetic node 742. -/
def formula742 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-2048 : ℚ) : ℝ)) z)*(formula703 z)
theorem node741Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node741Cross : polynomialCheck
    (((⟨#[-2048]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-2048]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node741 : RationalCode parameterInterval formula742 :=
  ((RationalCode.constant parameterInterval (-2048)).mul node702)
  |>.recode ⟨#[0,0,0,-2048]⟩ ⟨#[1]⟩ node741Denominator node741Cross

/-- Article: exact source arithmetic node 743. -/
def formula743 (z : ℝ) : ℝ := (formula741 z)+(formula742 z)
theorem node742Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node742Cross : polynomialCheck
    ((((⟨#[160,0,0,0,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-2048]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-2048,0,-2240]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node742 : RationalCode parameterInterval formula743 :=
  (node740.add node741)
  |>.recode ⟨#[160,0,0,-2048,0,-2240]⟩ ⟨#[1]⟩ node742Denominator node742Cross

/-- Article: exact source arithmetic node 744. -/
def formula744 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-512 : ℚ) : ℝ)) z)*(formula711 z)
theorem node743Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node743Cross : polynomialCheck
    (((⟨#[-512]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node743 : RationalCode parameterInterval formula744 :=
  ((RationalCode.constant parameterInterval (-512)).mul node710)
  |>.recode ⟨#[0,0,0,0,0,0,0,-512]⟩ ⟨#[1]⟩ node743Denominator node743Cross

/-- Article: exact source arithmetic node 745. -/
def formula745 (z : ℝ) : ℝ := (formula743 z)+(formula744 z)
theorem node744Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node744Cross : polynomialCheck
    ((((⟨#[160,0,0,-2048,0,-2240]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node744 : RationalCode parameterInterval formula745 :=
  (node742.add node743)
  |>.recode ⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ ⟨#[1]⟩ node744Denominator node744Cross

/-- Article: exact source arithmetic node 746. -/
def formula746 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-384 : ℚ) : ℝ)) z)*(id z)
theorem node745Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node745Cross : polynomialCheck
    (((⟨#[-384]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-384]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node745 : RationalCode parameterInterval formula746 :=
  ((RationalCode.constant parameterInterval (-384)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-384]⟩ ⟨#[1]⟩ node745Denominator node745Cross

/-- Article: exact source arithmetic node 747. -/
def formula747 (z : ℝ) : ℝ := (formula745 z)+(formula746 z)
theorem node746Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node746Cross : polynomialCheck
    ((((⟨#[160,0,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-384]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node746 : RationalCode parameterInterval formula747 :=
  (node744.add node745)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ ⟨#[1]⟩ node746Denominator node746Cross

/-- Article: exact source arithmetic node 748. -/
def formula748 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-24 : ℚ) : ℝ)) z)*(formula714 z)
theorem node747Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node747Cross : polynomialCheck
    (((⟨#[-24]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node747 : RationalCode parameterInterval formula748 :=
  ((RationalCode.constant parameterInterval (-24)).mul node713)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ ⟨#[1]⟩ node747Denominator node747Cross

/-- Article: exact source arithmetic node 749. -/
def formula749 (z : ℝ) : ℝ := (formula747 z)+(formula748 z)
theorem node748Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node748Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,-24]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node748 : RationalCode parameterInterval formula749 :=
  (node746.add node747)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ ⟨#[1]⟩ node748Denominator node748Cross

/-- Article: exact source arithmetic node 750. -/
def formula750 (z : ℝ) : ℝ := (formula749 z)+(formula718 z)
theorem node749Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node749Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node749 : RationalCode parameterInterval formula750 :=
  (node748.add node717)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ ⟨#[1]⟩ node749Denominator node749Cross

/-- Article: exact source arithmetic node 751. -/
def formula751 (z : ℝ) : ℝ := ((fun _ : ℝ => ((74 : ℚ) : ℝ)) z)*(formula720 z)
theorem node750Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node750Cross : polynomialCheck
    (((⟨#[74]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,74]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node750 : RationalCode parameterInterval formula751 :=
  ((RationalCode.constant parameterInterval (74)).mul node719)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,74]⟩ ⟨#[1]⟩ node750Denominator node750Cross

/-- Article: exact source arithmetic node 752. -/
def formula752 (z : ℝ) : ℝ := (formula750 z)+(formula751 z)
theorem node751Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node751Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,0,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,74]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node751 : RationalCode parameterInterval formula752 :=
  (node749.add node750)
  |>.recode ⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ ⟨#[1]⟩ node751Denominator node751Cross

/-- Article: exact source arithmetic node 753. -/
def formula753 (z : ℝ) : ℝ := ((fun _ : ℝ => ((592 : ℚ) : ℝ)) z)*(formula689 z)
theorem node752Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node752Cross : polynomialCheck
    (((⟨#[592]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,592]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node752 : RationalCode parameterInterval formula753 :=
  ((RationalCode.constant parameterInterval (592)).mul node688)
  |>.recode ⟨#[0,0,592]⟩ ⟨#[1]⟩ node752Denominator node752Cross

/-- Article: exact source arithmetic node 754. -/
def formula754 (z : ℝ) : ℝ := (formula752 z)+(formula753 z)
theorem node753Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node753Cross : polynomialCheck
    ((((⟨#[160,-384,0,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,592]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node753 : RationalCode parameterInterval formula754 :=
  (node751.add node752)
  |>.recode ⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ ⟨#[1]⟩ node753Denominator node753Cross

/-- Article: exact source arithmetic node 755. -/
def formula755 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1448 : ℚ) : ℝ)) z)*(formula723 z)
theorem node754Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node754Cross : polynomialCheck
    (((⟨#[1448]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,1448]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node754 : RationalCode parameterInterval formula755 :=
  ((RationalCode.constant parameterInterval (1448)).mul node722)
  |>.recode ⟨#[0,0,0,0,0,0,1448]⟩ ⟨#[1]⟩ node754Denominator node754Cross

/-- Article: exact source arithmetic node 756. -/
def formula756 (z : ℝ) : ℝ := (formula754 z)+(formula755 z)
theorem node755Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node755Cross : polynomialCheck
    ((((⟨#[160,-384,592,-2048,0,-2240,0,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,1448]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node755 : RationalCode parameterInterval formula756 :=
  (node753.add node754)
  |>.recode ⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ ⟨#[1]⟩ node755Denominator node755Cross

/-- Article: exact source arithmetic node 757. -/
def formula757 (z : ℝ) : ℝ := ((fun _ : ℝ => ((2896 : ℚ) : ℝ)) z)*(formula728 z)
theorem node756Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node756Cross : polynomialCheck
    (((⟨#[2896]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,2896]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node756 : RationalCode parameterInterval formula757 :=
  ((RationalCode.constant parameterInterval (2896)).mul node727)
  |>.recode ⟨#[0,0,0,0,2896]⟩ ⟨#[1]⟩ node756Denominator node756Cross

/-- Article: exact source arithmetic node 758. -/
def formula758 (z : ℝ) : ℝ := (formula756 z)+(formula757 z)
theorem node757Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node757Cross : polynomialCheck
    ((((⟨#[160,-384,592,-2048,0,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,2896]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node757 : RationalCode parameterInterval formula758 :=
  (node755.add node756)
  |>.recode ⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ ⟨#[1]⟩ node757Denominator node757Cross

/-- Article: exact source arithmetic node 759. -/
def formula759 (z : ℝ) : ℝ := (formula739 z)*(formula758 z)
theorem node758Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node281Denominator
theorem node758Cross : polynomialCheck
    (((⟨#[-32,96,-80,-64,208,-208,104,-16,-10,6,-1]⟩ : QPoly).mul (⟨#[160,-384,592,-2048,2896,-2240,1448,-512,74,-24,5]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[-5120,27648,-68608,142848,-278784,362496,-142336,-442368,1070464,-1329792,1117056,-664896,267616,-55296,-8896,11328,-4356,1116,-268,54,-5]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node758 : RationalCode parameterInterval formula759 :=
  (node738.mul node757)
  |>.recode ⟨#[-5120,27648,-68608,142848,-278784,362496,-142336,-442368,1070464,-1329792,1117056,-664896,267616,-55296,-8896,11328,-4356,1116,-268,54,-5]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node758Denominator node758Cross

/-- Article: exact source arithmetic node 760. -/
def formula760 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-57472 : ℚ) : ℝ)) z)*(formula706 z)
theorem node759Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node759Cross : polynomialCheck
    (((⟨#[-57472]⟩ : QPoly).mul (⟨#[0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,-57472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node759 : RationalCode parameterInterval formula760 :=
  ((RationalCode.constant parameterInterval (-57472)).mul node705)
  |>.recode ⟨#[0,0,0,0,0,-57472]⟩ ⟨#[1]⟩ node759Denominator node759Cross

/-- Article: exact source arithmetic node 761. -/
def formula761 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1600 : ℚ) : ℝ)) z)+(formula760 z)
theorem node760Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node760Cross : polynomialCheck
    ((((⟨#[1600]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,-57472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,0,0,0,0,-57472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node760 : RationalCode parameterInterval formula761 :=
  ((RationalCode.constant parameterInterval (1600)).add node759)
  |>.recode ⟨#[1600,0,0,0,0,-57472]⟩ ⟨#[1]⟩ node760Denominator node760Cross

/-- Article: exact source arithmetic node 762. -/
def formula762 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-48736 : ℚ) : ℝ)) z)*(formula703 z)
theorem node761Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node761Cross : polynomialCheck
    (((⟨#[-48736]⟩ : QPoly).mul (⟨#[0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,-48736]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node761 : RationalCode parameterInterval formula762 :=
  ((RationalCode.constant parameterInterval (-48736)).mul node702)
  |>.recode ⟨#[0,0,0,-48736]⟩ ⟨#[1]⟩ node761Denominator node761Cross

/-- Article: exact source arithmetic node 763. -/
def formula763 (z : ℝ) : ℝ := (formula761 z)+(formula762 z)
theorem node762Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node762Cross : polynomialCheck
    ((((⟨#[1600,0,0,0,0,-57472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,-48736]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,0,0,-48736,0,-57472]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node762 : RationalCode parameterInterval formula763 :=
  (node760.add node761)
  |>.recode ⟨#[1600,0,0,-48736,0,-57472]⟩ ⟨#[1]⟩ node762Denominator node762Cross

/-- Article: exact source arithmetic node 764. -/
def formula764 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-28736 : ℚ) : ℝ)) z)*(formula711 z)
theorem node763Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node763Cross : polynomialCheck
    (((⟨#[-28736]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,-28736]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node763 : RationalCode parameterInterval formula764 :=
  ((RationalCode.constant parameterInterval (-28736)).mul node710)
  |>.recode ⟨#[0,0,0,0,0,0,0,-28736]⟩ ⟨#[1]⟩ node763Denominator node763Cross

/-- Article: exact source arithmetic node 765. -/
def formula765 (z : ℝ) : ℝ := (formula763 z)+(formula764 z)
theorem node764Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node764Cross : polynomialCheck
    ((((⟨#[1600,0,0,-48736,0,-57472]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,-28736]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,0,0,-48736,0,-57472,0,-28736]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node764 : RationalCode parameterInterval formula765 :=
  (node762.add node763)
  |>.recode ⟨#[1600,0,0,-48736,0,-57472,0,-28736]⟩ ⟨#[1]⟩ node764Denominator node764Cross

/-- Article: exact source arithmetic node 766. -/
def formula766 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-10048 : ℚ) : ℝ)) z)*(id z)
theorem node765Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node765Cross : polynomialCheck
    (((⟨#[-10048]⟩ : QPoly).mul (⟨#[0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,-10048]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node765 : RationalCode parameterInterval formula766 :=
  ((RationalCode.constant parameterInterval (-10048)).mul (RationalCode.variable parameterInterval))
  |>.recode ⟨#[0,-10048]⟩ ⟨#[1]⟩ node765Denominator node765Cross

/-- Article: exact source arithmetic node 767. -/
def formula767 (z : ℝ) : ℝ := (formula765 z)+(formula766 z)
theorem node766Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node766Cross : polynomialCheck
    ((((⟨#[1600,0,0,-48736,0,-57472,0,-28736]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,-10048]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node766 : RationalCode parameterInterval formula767 :=
  (node764.add node765)
  |>.recode ⟨#[1600,-10048,0,-48736,0,-57472,0,-28736]⟩ ⟨#[1]⟩ node766Denominator node766Cross

/-- Article: exact source arithmetic node 768. -/
def formula768 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-6092 : ℚ) : ℝ)) z)*(formula714 z)
theorem node767Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node767Cross : polynomialCheck
    (((⟨#[-6092]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,-6092]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node767 : RationalCode parameterInterval formula768 :=
  ((RationalCode.constant parameterInterval (-6092)).mul node713)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,-6092]⟩ ⟨#[1]⟩ node767Denominator node767Cross

/-- Article: exact source arithmetic node 769. -/
def formula769 (z : ℝ) : ℝ := (formula767 z)+(formula768 z)
theorem node768Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node768Cross : polynomialCheck
    ((((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,-6092]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node768 : RationalCode parameterInterval formula769 :=
  (node766.add node767)
  |>.recode ⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092]⟩ ⟨#[1]⟩ node768Denominator node768Cross

/-- Article: exact source arithmetic node 770. -/
def formula770 (z : ℝ) : ℝ := (id z)^11
theorem node769Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node769Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 11 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 11))=true := by kernel_decide
def node769 : RationalCode parameterInterval formula770 :=
  ((RationalCode.variable parameterInterval).pow 11)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node769Denominator node769Cross

/-- Article: exact source arithmetic node 771. -/
def formula771 (z : ℝ) : ℝ := ((fun _ : ℝ => ((-314 : ℚ) : ℝ)) z)*(formula770 z)
theorem node770Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node770Cross : polynomialCheck
    (((⟨#[-314]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,-314]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node770 : RationalCode parameterInterval formula771 :=
  ((RationalCode.constant parameterInterval (-314)).mul node769)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,-314]⟩ ⟨#[1]⟩ node770Denominator node770Cross

/-- Article: exact source arithmetic node 772. -/
def formula772 (z : ℝ) : ℝ := (formula769 z)+(formula771 z)
theorem node771Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node771Cross : polynomialCheck
    ((((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,0,-314]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,0,-314]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node771 : RationalCode parameterInterval formula772 :=
  (node768.add node770)
  |>.recode ⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,0,-314]⟩ ⟨#[1]⟩ node771Denominator node771Cross

/-- Article: exact source arithmetic node 773. -/
def formula773 (z : ℝ) : ℝ := (id z)^12
theorem node772Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node772Cross : polynomialCheck
    ((polynomialPower ⟨#[0,1]⟩ 12 : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly).mul (polynomialPower ⟨#[1]⟩ 12))=true := by kernel_decide
def node772 : RationalCode parameterInterval formula773 :=
  ((RationalCode.variable parameterInterval).pow 12)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ ⟨#[1]⟩ node772Denominator node772Cross

/-- Article: exact source arithmetic node 774. -/
def formula774 (z : ℝ) : ℝ := ((fun _ : ℝ => ((25 : ℚ) : ℝ)) z)*(formula773 z)
theorem node773Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node773Cross : polynomialCheck
    (((⟨#[25]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node773 : RationalCode parameterInterval formula774 :=
  ((RationalCode.constant parameterInterval (25)).mul node772)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,0,0,25]⟩ ⟨#[1]⟩ node773Denominator node773Cross

/-- Article: exact source arithmetic node 775. -/
def formula775 (z : ℝ) : ℝ := (formula772 z)+(formula774 z)
theorem node774Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node774Cross : polynomialCheck
    ((((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,0,-314]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,0,0,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,0,-314,25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node774 : RationalCode parameterInterval formula775 :=
  (node771.add node773)
  |>.recode ⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,0,-314,25]⟩ ⟨#[1]⟩ node774Denominator node774Cross

/-- Article: exact source arithmetic node 776. -/
def formula776 (z : ℝ) : ℝ := ((fun _ : ℝ => ((1764 : ℚ) : ℝ)) z)*(formula717 z)
theorem node775Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node775Cross : polynomialCheck
    (((⟨#[1764]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,0,0,1764]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node775 : RationalCode parameterInterval formula776 :=
  ((RationalCode.constant parameterInterval (1764)).mul node716)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,0,0,1764]⟩ ⟨#[1]⟩ node775Denominator node775Cross

/-- Article: exact source arithmetic node 777. -/
def formula777 (z : ℝ) : ℝ := (formula775 z)+(formula776 z)
theorem node776Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node776Cross : polynomialCheck
    ((((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,0,-314,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,0,0,1764]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,1764,-314,25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node776 : RationalCode parameterInterval formula777 :=
  (node774.add node775)
  |>.recode ⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,1764,-314,25]⟩ ⟨#[1]⟩ node776Denominator node776Cross

/-- Article: exact source arithmetic node 778. -/
def formula778 (z : ℝ) : ℝ := ((fun _ : ℝ => ((14988 : ℚ) : ℝ)) z)*(formula720 z)
theorem node777Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node777Cross : polynomialCheck
    (((⟨#[14988]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,0,0,14988]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node777 : RationalCode parameterInterval formula778 :=
  ((RationalCode.constant parameterInterval (14988)).mul node719)
  |>.recode ⟨#[0,0,0,0,0,0,0,0,14988]⟩ ⟨#[1]⟩ node777Denominator node777Cross

/-- Article: exact source arithmetic node 779. -/
def formula779 (z : ℝ) : ℝ := (formula777 z)+(formula778 z)
theorem node778Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node778Cross : polynomialCheck
    ((((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,0,-6092,1764,-314,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,0,0,14988]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,14988,-6092,1764,-314,25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node778 : RationalCode parameterInterval formula779 :=
  (node776.add node777)
  |>.recode ⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,14988,-6092,1764,-314,25]⟩ ⟨#[1]⟩ node778Denominator node778Cross

/-- Article: exact source arithmetic node 780. -/
def formula780 (z : ℝ) : ℝ := ((fun _ : ℝ => ((28224 : ℚ) : ℝ)) z)*(formula689 z)
theorem node779Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node779Cross : polynomialCheck
    (((⟨#[28224]⟩ : QPoly).mul (⟨#[0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,28224]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node779 : RationalCode parameterInterval formula780 :=
  ((RationalCode.constant parameterInterval (28224)).mul node688)
  |>.recode ⟨#[0,0,28224]⟩ ⟨#[1]⟩ node779Denominator node779Cross

/-- Article: exact source arithmetic node 781. -/
def formula781 (z : ℝ) : ℝ := (formula779 z)+(formula780 z)
theorem node780Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node780Cross : polynomialCheck
    ((((⟨#[1600,-10048,0,-48736,0,-57472,0,-28736,14988,-6092,1764,-314,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,28224]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,28224,-48736,0,-57472,0,-28736,14988,-6092,1764,-314,25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node780 : RationalCode parameterInterval formula781 :=
  (node778.add node779)
  |>.recode ⟨#[1600,-10048,28224,-48736,0,-57472,0,-28736,14988,-6092,1764,-314,25]⟩ ⟨#[1]⟩ node780Denominator node780Cross

/-- Article: exact source arithmetic node 782. -/
def formula782 (z : ℝ) : ℝ := ((fun _ : ℝ => ((44832 : ℚ) : ℝ)) z)*(formula723 z)
theorem node781Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node781Cross : polynomialCheck
    (((⟨#[44832]⟩ : QPoly).mul (⟨#[0,0,0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,0,0,44832]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node781 : RationalCode parameterInterval formula782 :=
  ((RationalCode.constant parameterInterval (44832)).mul node722)
  |>.recode ⟨#[0,0,0,0,0,0,44832]⟩ ⟨#[1]⟩ node781Denominator node781Cross

/-- Article: exact source arithmetic node 783. -/
def formula783 (z : ℝ) : ℝ := (formula781 z)+(formula782 z)
theorem node782Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node782Cross : polynomialCheck
    ((((⟨#[1600,-10048,28224,-48736,0,-57472,0,-28736,14988,-6092,1764,-314,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,0,0,44832]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,28224,-48736,0,-57472,44832,-28736,14988,-6092,1764,-314,25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node782 : RationalCode parameterInterval formula783 :=
  (node780.add node781)
  |>.recode ⟨#[1600,-10048,28224,-48736,0,-57472,44832,-28736,14988,-6092,1764,-314,25]⟩ ⟨#[1]⟩ node782Denominator node782Cross

/-- Article: exact source arithmetic node 784. -/
def formula784 (z : ℝ) : ℝ := ((fun _ : ℝ => ((59952 : ℚ) : ℝ)) z)*(formula728 z)
theorem node783Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node783Cross : polynomialCheck
    (((⟨#[59952]⟩ : QPoly).mul (⟨#[0,0,0,0,1]⟩ : QPoly) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[0,0,0,0,59952]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node783 : RationalCode parameterInterval formula784 :=
  ((RationalCode.constant parameterInterval (59952)).mul node727)
  |>.recode ⟨#[0,0,0,0,59952]⟩ ⟨#[1]⟩ node783Denominator node783Cross

/-- Article: exact source arithmetic node 785. -/
def formula785 (z : ℝ) : ℝ := (formula783 z)+(formula784 z)
theorem node784Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node784Cross : polynomialCheck
    ((((⟨#[1600,-10048,28224,-48736,0,-57472,44832,-28736,14988,-6092,1764,-314,25]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)).add ((⟨#[0,0,0,0,59952]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((⟨#[1600,-10048,28224,-48736,59952,-57472,44832,-28736,14988,-6092,1764,-314,25]⟩ : QPoly).mul ((⟨#[1]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node784 : RationalCode parameterInterval formula785 :=
  (node782.add node783)
  |>.recode ⟨#[1600,-10048,28224,-48736,59952,-57472,44832,-28736,14988,-6092,1764,-314,25]⟩ ⟨#[1]⟩ node784Denominator node784Cross

/-- Article: exact source arithmetic node 786. -/
def formula786 (z : ℝ) : ℝ := (formula759 z)*(formula785 z)
theorem node785Denominator : ∀ z∈parameterInterval, aeval z (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).toPoly≠0 :=
  node281Denominator
theorem node785Cross : polynomialCheck
    (((⟨#[-5120,27648,-68608,142848,-278784,362496,-142336,-442368,1070464,-1329792,1117056,-664896,267616,-55296,-8896,11328,-4356,1116,-268,54,-5]⟩ : QPoly).mul (⟨#[1600,-10048,28224,-48736,59952,-57472,44832,-28736,14988,-6092,1764,-314,25]⟩ : QPoly) : QPoly).mul ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩)
    ((⟨#[-8192000,95682560,-532086784,1947795456,-5472190464,12708446208,-24632049664,38434013184,-44396724224,28143697920,19745280000,-93458804736,171069452288,-225566156800,239717420032,-213967620096,163239952896,-106983810048,59929355008,-28195769600,10691840768,-2920587648,308520000,219872640,-173424704,75066432,-24054736,6205296,-1335984,237768,-32476,2920,-125]⟩ : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[1]⟩ : QPoly)))=true := by kernel_decide
def node785 : RationalCode parameterInterval formula786 :=
  (node758.mul node784)
  |>.recode ⟨#[-8192000,95682560,-532086784,1947795456,-5472190464,12708446208,-24632049664,38434013184,-44396724224,28143697920,19745280000,-93458804736,171069452288,-225566156800,239717420032,-213967620096,163239952896,-106983810048,59929355008,-28195769600,10691840768,-2920587648,308520000,219872640,-173424704,75066432,-24054736,6205296,-1335984,237768,-32476,2920,-125]⟩ ⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ node785Denominator node785Cross

/-- Article: exact source arithmetic node 787. -/
def formula787 (z : ℝ) : ℝ := (formula685 z)+(formula786 z)
theorem node786Denominator : ∀ z∈parameterInterval, aeval z (⟨#[1]⟩ : QPoly).toPoly≠0 :=
  node56Denominator
theorem node786Cross : polynomialCheck
    ((((⟨#[8192000,-95682560,532086784,-1947795456,5472190464,-12708446208,24632049664,-38434013184,44396724224,-28143697920,-19745280000,93458804736,-171069452288,225566156800,-239717420032,213967620096,-163239952896,106983810048,-59929355008,28195769600,-10691840768,2920587648,-308520000,-219872640,173424704,-75066432,24054736,-6205296,1335984,-237768,32476,-2920,125]⟩ : QPoly).mul (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly)).add ((⟨#[-8192000,95682560,-532086784,1947795456,-5472190464,12708446208,-24632049664,38434013184,-44396724224,28143697920,19745280000,-93458804736,171069452288,-225566156800,239717420032,-213967620096,163239952896,-106983810048,59929355008,-28195769600,10691840768,-2920587648,308520000,219872640,-173424704,75066432,-24054736,6205296,-1335984,237768,-32476,2920,-125]⟩ : QPoly).mul (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly)) : QPoly).mul ⟨#[1]⟩)
    ((QPoly.zero : QPoly).mul ((⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly).mul (⟨#[0,0,-655360,2883584,-3932160,-1179648,6520832,-3670016,1048576,-524288,-4694016,5160960,212992,-1449984,1554432,-1933312,0,966656,-388608,181248,-13312,-161280,73344,4096,-4096,7168,-6368,576,960,-352,40]⟩ : QPoly)))=true := by kernel_decide
def node786 : RationalCode parameterInterval formula787 :=
  (node684.add node785)
  |>.recode QPoly.zero ⟨#[1]⟩ node786Denominator node786Cross

/-- Article: exact coefficient representation of the independently specified upperFiveIdentity source. -/
def upperFiveIdentityCode : RationalCode parameterInterval (fun z : ℝ => ((16*(moment z 7))+((moment z 0)*((-20*((G z))^3)+(2*(u z))+(5*(G z))+(16*((G z))^5)+(-16*((G z))^5*((u z))^2)+(-5*(G z)*((u z))^2)+(20*((G z))^3*((u z))^2)))+((moment z 1)*(-5+(5*((u z))^2)))+((moment z 2)*((-26*(u z))+(-16*((G z))^5)+(-5*(G z))+(20*((G z))^3)))+((moment z 3)*(25+(-20*((u z))^2)))+((moment z 5)*(-36+(16*((u z))^2)))+(-1*(d z)*(1+(-12*((G z))^2)+(16*((G z))^4)))+(-32*(moment z 6)*(u z))+(56*(moment z 4)*(u z)))-N12 z*upperFiveFactor z) where
  numerator := node786.numerator
  denominator := node786.denominator
  denominator_ne := node786.denominator_ne
  exact z hz := by
    have he : (fun z : ℝ => ((16*(moment z 7))+((moment z 0)*((-20*((G z))^3)+(2*(u z))+(5*(G z))+(16*((G z))^5)+(-16*((G z))^5*((u z))^2)+(-5*(G z)*((u z))^2)+(20*((G z))^3*((u z))^2)))+((moment z 1)*(-5+(5*((u z))^2)))+((moment z 2)*((-26*(u z))+(-16*((G z))^5)+(-5*(G z))+(20*((G z))^3)))+((moment z 3)*(25+(-20*((u z))^2)))+((moment z 5)*(-36+(16*((u z))^2)))+(-1*(d z)*(1+(-12*((G z))^2)+(16*((G z))^4)))+(-32*(moment z 6)*(u z))+(56*(moment z 4)*(u z)))-N12 z*upperFiveFactor z) z=formula787 z := by
      try dsimp only [formula1,formula2,formula3,formula4,formula5,formula6,formula7,formula8,formula9,formula10,formula11,formula12,formula13,formula14,formula15,formula16,formula17,formula18,formula19,formula20,formula21,formula22,formula23,formula24,formula25,formula26,formula27,formula28,formula29,formula30,formula31,formula32,formula33,formula34,formula35,formula36,formula37,formula38,formula39,formula40,formula41,formula42,formula43,formula44,formula45,formula46,formula47,formula48,formula49,formula50,formula51,formula52,formula53,formula54,formula55,formula56,formula57,formula58,formula59,formula60,formula61,formula62,formula63,formula64,formula65,formula66,formula67,formula68,formula69,formula70,formula71,formula72,formula73,formula74,formula75,formula76,formula77,formula78,formula79,formula80,formula81,formula82,formula83,formula84,formula85,formula86,formula87,formula88,formula89,formula90,formula91,formula92,formula93,formula94,formula95,formula96,formula97,formula98,formula99,formula100,formula101,formula102,formula103,formula104,formula105,formula106,formula107,formula108,formula109,formula110,formula111,formula112,formula113,formula114,formula115,formula116,formula117,formula118,formula119,formula120,formula121,formula122,formula123,formula124,formula125,formula126,formula127,formula128,formula129,formula130,formula131,formula132,formula133,formula134,formula135,formula136,formula137,formula138,formula139,formula140,formula141,formula142,formula143,formula144,formula145,formula146,formula147,formula148,formula149,formula150,formula151,formula152,formula153,formula154,formula155,formula156,formula157,formula158,formula159,formula160,formula161,formula162,formula163,formula164,formula165,formula166,formula167,formula168,formula169,formula170,formula171,formula172,formula173,formula174,formula175,formula176,formula177,formula178,formula179,formula180,formula181,formula182,formula183,formula184,formula185,formula186,formula187,formula188,formula189,formula190,formula191,formula192,formula193,formula194,formula195,formula196,formula197,formula198,formula199,formula200,formula201,formula202,formula203,formula204,formula205,formula206,formula207,formula208,formula209,formula210,formula211,formula212,formula213,formula214,formula215,formula216,formula217,formula218,formula219,formula220,formula221,formula222,formula223,formula224,formula225,formula226,formula227,formula228,formula229,formula230,formula231,formula232,formula233,formula234,formula235,formula236,formula237,formula238,formula239,formula240,formula241,formula242,formula243,formula244,formula245,formula246,formula247,formula248,formula249,formula250,formula251,formula252,formula253,formula254,formula255,formula256,formula257,formula258,formula259,formula260,formula261,formula262,formula263,formula264,formula265,formula266,formula267,formula268,formula269,formula270,formula271,formula272,formula273,formula274,formula275,formula276,formula277,formula278,formula279,formula280,formula281,formula282,formula283,formula284,formula285,formula286,formula287,formula288,formula289,formula290,formula291,formula292,formula293,formula294,formula295,formula296,formula297,formula298,formula299,formula300,formula301,formula302,formula303,formula304,formula305,formula306,formula307,formula308,formula309,formula310,formula311,formula312,formula313,formula314,formula315,formula316,formula317,formula318,formula319,formula320,formula321,formula322,formula323,formula324,formula325,formula326,formula327,formula328,formula329,formula330,formula331,formula332,formula333,formula334,formula335,formula336,formula337,formula338,formula339,formula340,formula341,formula342,formula343,formula344,formula345,formula346,formula347,formula348,formula349,formula350,formula351,formula352,formula353,formula354,formula355,formula356,formula357,formula358,formula359,formula360,formula361,formula362,formula363,formula364,formula365,formula366,formula367,formula368,formula369,formula370,formula371,formula372,formula373,formula374,formula375,formula376,formula377,formula378,formula379,formula380,formula381,formula382,formula383,formula384,formula385,formula386,formula387,formula388,formula389,formula390,formula391,formula392,formula393,formula394,formula395,formula396,formula397,formula398,formula399,formula400,formula401,formula402,formula403,formula404,formula405,formula406,formula407,formula408,formula409,formula410,formula411,formula412,formula413,formula414,formula415,formula416,formula417,formula418,formula419,formula420,formula421,formula422,formula423,formula424,formula425,formula426,formula427,formula428,formula429,formula430,formula431,formula432,formula433,formula434,formula435,formula436,formula437,formula438,formula439,formula440,formula441,formula442,formula443,formula444,formula445,formula446,formula447,formula448,formula449,formula450,formula451,formula452,formula453,formula454,formula455,formula456,formula457,formula458,formula459,formula460,formula461,formula462,formula463,formula464,formula465,formula466,formula467,formula468,formula469,formula470,formula471,formula472,formula473,formula474,formula475,formula476,formula477,formula478,formula479,formula480,formula481,formula482,formula483,formula484,formula485,formula486,formula487,formula488,formula489,formula490,formula491,formula492,formula493,formula494,formula495,formula496,formula497,formula498,formula499,formula500,formula501,formula502,formula503,formula504,formula505,formula506,formula507,formula508,formula509,formula510,formula511,formula512,formula513,formula514,formula515,formula516,formula517,formula518,formula519,formula520,formula521,formula522,formula523,formula524,formula525,formula526,formula527,formula528,formula529,formula530,formula531,formula532,formula533,formula534,formula535,formula536,formula537,formula538,formula539,formula540,formula541,formula542,formula543,formula544,formula545,formula546,formula547,formula548,formula549,formula550,formula551,formula552,formula553,formula554,formula555,formula556,formula557,formula558,formula559,formula560,formula561,formula562,formula563,formula564,formula565,formula566,formula567,formula568,formula569,formula570,formula571,formula572,formula573,formula574,formula575,formula576,formula577,formula578,formula579,formula580,formula581,formula582,formula583,formula584,formula585,formula586,formula587,formula588,formula589,formula590,formula591,formula592,formula593,formula594,formula595,formula596,formula597,formula598,formula599,formula600,formula601,formula602,formula603,formula604,formula605,formula606,formula607,formula608,formula609,formula610,formula611,formula612,formula613,formula614,formula615,formula616,formula617,formula618,formula619,formula620,formula621,formula622,formula623,formula624,formula625,formula626,formula627,formula628,formula629,formula630,formula631,formula632,formula633,formula634,formula635,formula636,formula637,formula638,formula639,formula640,formula641,formula642,formula643,formula644,formula645,formula646,formula647,formula648,formula649,formula650,formula651,formula652,formula653,formula654,formula655,formula656,formula657,formula658,formula659,formula660,formula661,formula662,formula663,formula664,formula665,formula666,formula667,formula668,formula669,formula670,formula671,formula672,formula673,formula674,formula675,formula676,formula677,formula678,formula679,formula680,formula681,formula682,formula683,formula684,formula685,formula686,formula687,formula688,formula689,formula690,formula691,formula692,formula693,formula694,formula695,formula696,formula697,formula698,formula699,formula700,formula701,formula702,formula703,formula704,formula705,formula706,formula707,formula708,formula709,formula710,formula711,formula712,formula713,formula714,formula715,formula716,formula717,formula718,formula719,formula720,formula721,formula722,formula723,formula724,formula725,formula726,formula727,formula728,formula729,formula730,formula731,formula732,formula733,formula734,formula735,formula736,formula737,formula738,formula739,formula740,formula741,formula742,formula743,formula744,formula745,formula746,formula747,formula748,formula749,formula750,formula751,formula752,formula753,formula754,formula755,formula756,formula757,formula758,formula759,formula760,formula761,formula762,formula763,formula764,formula765,formula766,formula767,formula768,formula769,formula770,formula771,formula772,formula773,formula774,formula775,formula776,formula777,formula778,formula779,formula780,formula781,formula782,formula783,formula784,formula785,formula786,formula787,upperFiveFactor,N10,M10,eMinus,ePlus,qMinus,rMinus,rPlus,N12,id_eq]
      try push_cast
      try simp_rw [div_eq_mul_inv]
      try simp_rw [mul_inv_rev]
      try simp_rw [inv_pow]
      try ring
    exact he.trans (node786.exact z hz)

/-- Article: exact endpoint factor of the actual upper lag-five slack. -/
theorem upper5_factor {z : ℝ} (hz : z∈parameterInterval) : reducedSlack z 5 1=N12 z*upperFiveFactor z := by
  have h := upperFiveIdentityCode.eq_zero (by kernel_decide) hz
  rw [upper5_source]
  linarith [h]

end
end polyak.Boundary.P2
