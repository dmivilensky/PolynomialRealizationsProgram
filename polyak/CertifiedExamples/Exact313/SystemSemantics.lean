import polyak.CertifiedExamples.Exact313.ContactPolynomial
import polyak.Certificates.PartII.Exact313.System
import polyak.Numerics.Parametric.CorrelatedInterior

/-! Actual three-dimensional contact equations, their Jacobian, and local
uniqueness. The executable expressions are linked to a real polynomial profile. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels ModeLocking.TwoLag LeanCert.Core LeanCert.Engine Numerics.Parametric

abbrev CoefficientVector := Fin 3→ℝ

def vectorXi (x : CoefficientVector) (c : ℝ) : ℝ := x 0+x 1*c+x 2*c^2
def vectorXiD (x : CoefficientVector) (c : ℝ) : ℝ := x 1+2*x 2*c

def ratioNumerator (x : CoefficientVector) : ℝ := 1+c₁-vectorXi x c₁
def ratioDenominator (x : CoefficientVector) : ℝ :=
  vectorXi x c₁*(8*c₁^2*(1+c₁))+(1+c₁)*(8*c₁^3-4*c₁)

def contactProfile (x : CoefficientVector) (c : ℝ) : ℝ :=
  ratioDenominator x*(vectorXi x c-(1+c))+
    ratioNumerator x*(vectorXi x c*(8*c^2*(1+c))+(1+c)*(8*c^3-4*c))

def profileSlope (x : CoefficientVector) (c : ℝ) : ℝ :=
  ratioDenominator x*(vectorXiD x c-1)+
    ratioNumerator x*(vectorXiD x c*(8*c^2*(1+c))+vectorXi x c*(8*c*(2+3*c))+
      (8*c^3-4*c)+(1+c)*(24*c^2-4))

def contactSystem (x : CoefficientVector) : CoefficientVector :=
  ![contactProfile x c₂,profileSlope x c₁,profileSlope x c₂]

theorem vectorXi_hasDerivAt (x : CoefficientVector) (c : ℝ) :
    HasDerivAt (vectorXi x) (vectorXiD x c) c := by
  convert ((hasDerivAt_const c (x 0)).add ((hasDerivAt_id c).const_mul (x 1))).add
    (((hasDerivAt_id c).pow 2).const_mul (x 2)) using 1
  · rfl
  · dsimp [vectorXiD]
    ring

theorem profile_hasDerivAt (x : CoefficientVector) (c : ℝ) :
    HasDerivAt (contactProfile x) (profileSlope x c) c := by
  have hW := denominator_hasDerivAt 1 c
  have hU : HasDerivAt (fun c : ℝ=>8*c^3-4*c) (24*c^2-4) c := by
    convert (((hasDerivAt_id c).pow 3).const_mul 8).sub
      ((hasDerivAt_id c).const_mul 4) using 1
    · ext y
      simp
    · simp
      ring
  have hW' : HasDerivAt (fun c : ℝ=>8*c^2*(1+c)) (8*c*(2+3*c)) c := by
    have h := (hW.sub_const 1)
    convert h using 1
    · ext y
      dsimp [denominator]
      ring
    · dsimp [denominatorD]
      ring
  have h := (((vectorXi_hasDerivAt x c).sub ((hasDerivAt_id c).const_add 1)).const_mul
    (ratioDenominator x)).add
    ((((vectorXi_hasDerivAt x c).mul hW').add (((hasDerivAt_id c).const_add 1).mul hU)).const_mul
      (ratioNumerator x))
  convert h using 1
  · rfl
  · dsimp [profileSlope]
    ring

theorem contactSystem_eq (x : CoefficientVector) :
    system SystemCode.equations Real.pi x=contactSystem x := by
  have h1 : (Fin.cons Real.pi x : Fin 4→ℝ) 1=x 0 := rfl
  have h2 : (Fin.cons Real.pi x : Fin 4→ℝ) 2=x 1 := rfl
  have h3 : (Fin.cons Real.pi x : Fin 4→ℝ) 3=x 2 := rfl
  ext i
  fin_cases i
  all_goals
    dsimp [system,eval,evalFin,SystemCode.equations,SystemCode.contact,SystemCode.slope,
      SystemCode.ratioNumerator,SystemCode.ratioDenominator,SystemCode.xi,SystemCode.xiD,
      SystemCode.w,SystemCode.wD,SystemCode.z,SystemCode.zD,Code.cosine,Expr.eval,
      Expr.pow,Expr.sub,finEnv,embed]
    try rw [h1]
    try rw [h2]
    try rw [h3]
    norm_num [contactSystem,contactProfile,profileSlope,ratioNumerator,ratioDenominator,
      vectorXi,vectorXiD,c₁,c₂,u,v]
    ring

def coefficientVector : CoefficientVector := ![CStar.c0,CStar.c1,CStar.c2]

theorem vectorXi_actual (c : ℝ) : vectorXi coefficientVector c=CStar.eval c := rfl

theorem ratio_identity : ratioNumerator coefficientVector=rStar*ratioDenominator coefficientVector := by
  have hz := contactPolynomial_value ⟨c₁_mem.1.le,c₁_mem.2.le⟩
    (hermiteQuadratic_first 4 rStar c₁ c₂).1
  rw [contactPolynomial_identity] at hz
  dsimp [ratioNumerator,ratioDenominator]
  rw [vectorXi_actual]
  dsimp [denominator,numerator] at hz
  linear_combination -hz

theorem profile_actual (c : ℝ) :
    contactProfile coefficientVector c=ratioDenominator coefficientVector*contactPolynomial c := by
  rw [contactProfile,ratio_identity,vectorXi_actual,contactPolynomial_identity]
  dsimp [denominator,numerator]
  ring

theorem profileSlope_actual (c : ℝ) :
    profileSlope coefficientVector c=ratioDenominator coefficientVector*deriv contactPolynomial c := by
  rw [←(profile_hasDerivAt coefficientVector c).deriv]
  have he : contactProfile coefficientVector=(fun c=>ratioDenominator coefficientVector*contactPolynomial c) :=
    funext profile_actual
  rw [he]
  rw [deriv_const_mul_field]

theorem contactSystem_zero : contactSystem coefficientVector=0 := by
  ext i
  fin_cases i
  · change contactProfile coefficientVector c₂=0
    rw [profile_actual,contactPolynomial_value ⟨c₂_mem.1.le,c₂_mem.2.le⟩
      (hermiteQuadratic_second_value 4 rStar c₁_lt_c₂.ne),mul_zero]
  · change profileSlope coefficientVector c₁=0
    rw [profileSlope_actual,contactPolynomial_slope ⟨c₁_mem.1.le,c₁_mem.2.le⟩
      (hermiteQuadratic_first 4 rStar c₁ c₂).1 contact_slopes_first,mul_zero]
  · change profileSlope coefficientVector c₂=0
    rw [profileSlope_actual,contactPolynomial_slope ⟨c₂_mem.1.le,c₂_mem.2.le⟩
      (hermiteQuadratic_second_value 4 rStar c₁_lt_c₂.ne) contact_slopes_second,mul_zero]

private abbrev systemCertificate := polyak.Certificates.PartII.Exact313.System.certificate
private abbrev systemConfig := polyak.Certificates.PartII.Exact313.System.config
def coefficientBox : Fin 3→IntervalRat := coordinateBox systemCertificate.center systemCertificate.radius
private def coefficientCode : Fin 3→Expr := ![Code.constant,Code.linear,Code.quadratic]

private theorem coefficientCode_eval (i : Fin 3) :
    Expr.eval (Code.environment rStar) (coefficientCode i)=coefficientVector i := by
  fin_cases i
  · exact Code.eval_constant scalarRoot_positive.le
  · exact Code.eval_linear scalarRoot_positive.le
  · exact Code.eval_quadratic scalarRoot_positive.le

private theorem coefficient_lower_check (i : Fin 3) :
    boundCheck (.sub (coefficientCode i) (.const (coefficientBox i).lo)) Proposal.piBox
      (coordinateBox Proposal.certificate.center Proposal.certificate.radius) Proposal.config true=true := by
  fin_cases i
  · exact polyak.Certificates.PartII.Exact313.System.coefficient_lower_0
  · exact polyak.Certificates.PartII.Exact313.System.coefficient_lower_1
  · exact polyak.Certificates.PartII.Exact313.System.coefficient_lower_2

private theorem coefficient_upper_check (i : Fin 3) :
    boundCheck (.sub (.const (coefficientBox i).hi) (coefficientCode i)) Proposal.piBox
      (coordinateBox Proposal.certificate.center Proposal.certificate.radius) Proposal.config true=true := by
  fin_cases i
  · exact polyak.Certificates.PartII.Exact313.System.coefficient_upper_0
  · exact polyak.Certificates.PartII.Exact313.System.coefficient_upper_1
  · exact polyak.Certificates.PartII.Exact313.System.coefficient_upper_2

theorem coefficientVector_strict_mem : coefficientVector∈strictBox coefficientBox := by
  have hb : FinBoxMem ![rStar] (coordinateBox Proposal.certificate.center Proposal.certificate.radius) := by
    intro i
    fin_cases i
    exact scalarRoot.mem
  intro i
  have hlo := boundCheck_sound _ _ _ _ true (coefficient_lower_check i) pi_mem hb
  have hhi := boundCheck_sound _ _ _ _ true (coefficient_upper_check i) pi_mem hb
  change 0<Expr.eval (Code.environment rStar) (.sub (coefficientCode i) (.const (coefficientBox i).lo)) at hlo
  change 0<Expr.eval (Code.environment rStar) (.sub (.const (coefficientBox i).hi) (coefficientCode i)) at hhi
  simp only [Expr.eval_sub,Expr.eval_const,coefficientCode_eval] at hlo hhi
  exact ⟨by linarith,by linarith⟩

theorem coefficientVector_mem : FinBoxMem coefficientVector coefficientBox :=
  strictBox_subset coefficientVector_strict_mem

theorem contactSystem_jacobian_invertible : (fderiv ℝ contactSystem coefficientVector).IsInvertible := by
  have h := SystemCode.nonsingularCheck_sound _ _ _ _
    polyak.Certificates.PartII.Exact313.System.nonsingular
    Trigonometry.pi_mem coefficientVector_mem
  have he : system SystemCode.equations Real.pi=contactSystem := funext contactSystem_eq
  rwa [he] at h

theorem contactSystem_unique (x : CoefficientVector) (hx : FinBoxMem x coefficientBox)
    (hzero : contactSystem x=0) : x=coefficientVector := by
  obtain ⟨z,_,huniq⟩ := checkDyadic_sound SystemCode.equations Trigonometry.piTight
    systemCertificate systemConfig polyak.Certificates.PartII.Exact313.System.accepted
    Real.pi Trigonometry.pi_mem
  have hxz := huniq x ⟨hx,by rw [contactSystem_eq];exact hzero⟩
  have hcz := huniq coefficientVector ⟨coefficientVector_mem,by rw [contactSystem_eq];exact contactSystem_zero⟩
  exact hxz.trans hcz.symm

theorem contactSystem_locally_unique : ∃U : Set CoefficientVector,
    IsOpen U ∧ coefficientVector∈U ∧ ∀x∈U,contactSystem x=0→x=coefficientVector :=
  ⟨strictBox coefficientBox,isOpen_strictBox coefficientBox,coefficientVector_strict_mem,
    fun x hx hz=>contactSystem_unique x (strictBox_subset hx) hz⟩

end polyak.CertifiedExamples.Exact313
