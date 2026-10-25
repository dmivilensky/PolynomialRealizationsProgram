import polyak.CertifiedExamples.Exact313.LocationSemantics
import polyak.Certificates.PartII.Exact313.Location

/-! The constructed real tuning has precisely the displayed rounded parameters.
The inverse's square root is enclosed by proved square inequalities. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open General Levels LeanCert.Core LeanCert.Engine Numerics.Parametric
private abbrev dBox := polyak.Certificates.PartII.Exact313.stableBox
private abbrev uBox := polyak.Certificates.PartII.Exact313.uBox

private theorem root_vector_mem : FinBoxMem ![rStar]
    (coordinateBox Proposal.certificate.center Proposal.certificate.radius) := by
  intro i
  fin_cases i
  exact scalarRoot.mem

private theorem secularCheck (i : Fin 5) :
    boundCheck (polyak.Certificates.PartII.Exact313.secularReserves i) Proposal.piBox
      (coordinateBox Proposal.certificate.center Proposal.certificate.radius)
      Proposal.config true=true := by
  fin_cases i
  · exact polyak.Certificates.PartII.Exact313.secular00
  · exact polyak.Certificates.PartII.Exact313.secular01
  · exact polyak.Certificates.PartII.Exact313.secular02
  · exact polyak.Certificates.PartII.Exact313.secular03
  · exact polyak.Certificates.PartII.Exact313.secular04

private theorem secularReserve_positive (i : Fin 5) :
    0<Expr.eval (Code.environment rStar) (polyak.Certificates.PartII.Exact313.secularReserves i) :=
  boundCheck_sound _ _ _ _ true (secularCheck i) pi_mem root_vector_mem

private theorem secular_lower_negative :
    Chart.secular (-CStar.c2) CStar.c1 (-CStar.c2-CStar.c0) dBox.lo<0 := by
  have h := secularReserve_positive 0
  change 0< -Expr.eval (Code.environment rStar) (Code.secularAt (.const dBox.lo)) at h
  rw [eval_secular _ rfl rfl,Expr.eval_const] at h
  exact neg_pos.mp h

private theorem secular_upper_positive :
    0<Chart.secular (-CStar.c2) CStar.c1 (-CStar.c2-CStar.c0) dBox.hi := by
  have h := secularReserve_positive 1
  change 0<Expr.eval (Code.environment rStar) (Code.secularAt (.const dBox.hi)) at h
  rw [eval_secular _ rfl rfl,Expr.eval_const] at h
  exact h

private theorem lower_branch : 2*(-CStar.c2)<(dBox.lo:ℝ) ∧ |CStar.c1|<(dBox.lo:ℝ) := by
  have h₂ := secularReserve_positive 2
  have h₃ := secularReserve_positive 3
  have h₄ := secularReserve_positive 4
  change 0<(dBox.lo:ℝ)+((2:ℚ):ℝ)*Expr.eval (Code.environment rStar) Code.quadratic at h₂
  change 0<(dBox.lo:ℝ)-Expr.eval (Code.environment rStar) Code.linear at h₃
  change 0<(dBox.lo:ℝ)+Expr.eval (Code.environment rStar) Code.linear at h₄
  rw [Code.eval_quadratic scalarRoot_positive.le] at h₂
  rw [Code.eval_linear scalarRoot_positive.le] at h₃ h₄
  norm_num only [Rat.cast_ofNat] at h₂
  exact ⟨by linarith,abs_lt.mpr ⟨by linarith,by linarith⟩⟩

theorem stableRoot_mem : Chart.stableRoot coefficientPoint∈dBox := by
  have hbranch : -2*coefficientPoint.val.c2<(dBox.lo:ℝ) := by
    simpa only [coefficientPoint,Subtype.coe_mk,neg_mul,mul_neg] using lower_branch.1
  have hlo := (Chart.secular_neg_iff coefficientPoint hbranch lower_branch.2.le).mp
    secular_lower_negative
  have hab : (dBox.lo:ℝ)≤dBox.hi := by exact_mod_cast dBox.le
  have hhi := (Chart.secular_pos_iff coefficientPoint (hbranch.trans_le hab)
    (lower_branch.2.le.trans hab)).mp secular_upper_positive
  exact ⟨hlo.le,hhi.le⟩

private def intermediateEnvironment : ℕ→ℝ := finEnv (embed Real.pi ![rStar,Chart.stableRoot coefficientPoint])

private theorem intermediate_mem : FinBoxMem ![rStar,Chart.stableRoot coefficientPoint]
    polyak.Certificates.PartII.Exact313.intermediateBox := by
  intro i
  fin_cases i
  · exact scalarRoot.mem
  · exact stableRoot_mem

theorem normalizedU_mem : Chart.normalizedU coefficientPoint∈uBox := by
  have h₀ := boundCheck_sound _ _ _ _ true polyak.Certificates.PartII.Exact313.square00 pi_mem intermediate_mem
  have h₁ := boundCheck_sound _ _ _ _ true polyak.Certificates.PartII.Exact313.square01 pi_mem intermediate_mem
  change 0<Expr.eval intermediateEnvironment
    (.sub (.mul (.var 2) Code.normalizedB) (.const (uBox.lo^2))) at h₀
  change 0<Expr.eval intermediateEnvironment
    (.sub (.const (uBox.hi^2)) (.mul (.var 2) Code.normalizedB)) at h₁
  simp only [Expr.eval_sub,Expr.eval_mul,Expr.eval_var,Expr.eval_const,
    eval_normalizedB intermediateEnvironment rfl rfl rfl] at h₀ h₁
  change 0<Chart.stableRoot coefficientPoint*Chart.normalizedB coefficientPoint-((uBox.lo^2:ℚ):ℝ) at h₀
  change 0<((uBox.hi^2:ℚ):ℝ)-Chart.stableRoot coefficientPoint*Chart.normalizedB coefficientPoint at h₁
  push_cast at h₀ h₁
  have hs := Chart.normalizedU_sq coefficientPoint
  have hp := Chart.one_lt_normalizedU coefficientPoint
  have hlo : (0:ℝ)<uBox.lo := by norm_num [dBox,uBox,polyak.Certificates.PartII.Exact313.uBox]
  have hhi : (0:ℝ)<uBox.hi := by norm_num [dBox,uBox,polyak.Certificates.PartII.Exact313.uBox]
  constructor <;> nlinarith

private def locationEnvironment : ℕ→ℝ :=
  finEnv (embed Real.pi ![rStar,Chart.stableRoot coefficientPoint,Chart.normalizedU coefficientPoint])

private theorem location_mem : FinBoxMem
    ![rStar,Chart.stableRoot coefficientPoint,Chart.normalizedU coefficientPoint]
    polyak.Certificates.PartII.Exact313.locationBox := by
  intro i
  fin_cases i
  · exact scalarRoot.mem
  · exact stableRoot_mem
  · exact normalizedU_mem

private theorem locationCheck (i : Fin 6) :
    boundCheck (Code.locationReserves i) Proposal.piBox
      polyak.Certificates.PartII.Exact313.locationBox Proposal.config true=true := by
  fin_cases i
  · exact polyak.Certificates.PartII.Exact313.location00
  · exact polyak.Certificates.PartII.Exact313.location01
  · exact polyak.Certificates.PartII.Exact313.location02
  · exact polyak.Certificates.PartII.Exact313.location03
  · exact polyak.Certificates.PartII.Exact313.location04
  · exact polyak.Certificates.PartII.Exact313.location05

private theorem locationReserve_positive (i : Fin 6) :
    0<Expr.eval locationEnvironment (Code.locationReserves i) :=
  boundCheck_sound _ _ _ _ true (locationCheck i) pi_mem location_mem

theorem qStar_location :
    |qStar.kappa-(835343/10000:ℝ)|<1/20000 ∧
      |qStar.y-(2218909/1000000:ℝ)|<1/2000000 ∧
      |qStar.beta-(77846/125000:ℝ)|<1/2000000 := by
  have h0 := locationReserve_positive 0
  have h1 := locationReserve_positive 1
  have h2 := locationReserve_positive 2
  have h3 := locationReserve_positive 3
  have h4 := locationReserve_positive 4
  have h5 := locationReserve_positive 5
  change 0<Expr.eval locationEnvironment Code.sourceKappa-((1670685/20000:ℚ):ℝ) at h0
  change 0<((1670687/20000:ℚ):ℝ)-Expr.eval locationEnvironment Code.sourceKappa at h1
  change 0<Expr.eval locationEnvironment Code.sourceY-((4437817/2000000:ℚ):ℝ) at h2
  change 0<((4437819/2000000:ℚ):ℝ)-Expr.eval locationEnvironment Code.sourceY at h3
  change 0<Expr.eval locationEnvironment Code.beta-((1245535/2000000:ℚ):ℝ) at h4
  change 0<((1245537/2000000:ℚ):ℝ)-Expr.eval locationEnvironment Code.beta at h5
  rw [eval_sourceKappa locationEnvironment rfl rfl rfl rfl] at h0 h1
  rw [eval_sourceY locationEnvironment rfl rfl rfl rfl] at h2 h3
  rw [eval_beta locationEnvironment rfl] at h4 h5
  norm_num at h0 h1 h2 h3 h4 h5
  refine ⟨abs_lt.mpr ⟨?_,?_⟩,abs_lt.mpr ⟨?_,?_⟩,abs_lt.mpr ⟨?_,?_⟩⟩ <;> linarith

end polyak.CertifiedExamples.Exact313
