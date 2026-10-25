import polyak.CertifiedExamples.Exact313.Scalar
import polyak.CertifiedExamples.Exact313.GeometrySemantics
import polyak.Certificates.PartII.Exact313.Reserves

/-! Construction of an actual admissible tuning from certified Hermite data. -/
noncomputable section
namespace polyak.CertifiedExamples.Exact313
open LeanCert.Core LeanCert.Engine Numerics.Parametric General Levels ModeLocking.TwoLag

abbrev coefficients (r : ℝ) : Chart.Coefficients := hermiteQuadratic 4 r c₁ c₂
abbrev rStar : ℝ := scalarRoot.value
abbrev CStar : Chart.Coefficients := coefficients rStar

theorem reserveCheck (i : Fin 17) :
    boundCheck (Code.reserves i) Proposal.piBox
      (coordinateBox Proposal.certificate.center Proposal.certificate.radius)
      Proposal.config true=true := by
  fin_cases i
  · exact polyak.Certificates.PartII.Exact313.reserve00
  · exact polyak.Certificates.PartII.Exact313.reserve01
  · exact polyak.Certificates.PartII.Exact313.reserve02
  · exact polyak.Certificates.PartII.Exact313.reserve03
  · exact polyak.Certificates.PartII.Exact313.reserve04
  · exact polyak.Certificates.PartII.Exact313.reserve05
  · exact polyak.Certificates.PartII.Exact313.reserve06
  · exact polyak.Certificates.PartII.Exact313.reserve07
  · exact polyak.Certificates.PartII.Exact313.reserve08
  · exact polyak.Certificates.PartII.Exact313.reserve09
  · exact polyak.Certificates.PartII.Exact313.reserve10
  · exact polyak.Certificates.PartII.Exact313.reserve11
  · exact polyak.Certificates.PartII.Exact313.reserve12
  · exact polyak.Certificates.PartII.Exact313.reserve13
  · exact polyak.Certificates.PartII.Exact313.reserve14
  · exact polyak.Certificates.PartII.Exact313.reserve15
  · exact polyak.Certificates.PartII.Exact313.reserve16

theorem reserve_positive (i : Fin 17) {r : ℝ} (hr : r∈rootBox) :
    0<Expr.eval (Code.environment r) (Code.reserves i) := by
  have hb : FinBoxMem ![r]
      (coordinateBox Proposal.certificate.center Proposal.certificate.radius) := by
    intro i
    fin_cases i
    exact hr
  exact boundCheck_sound _ _ _ _ true (reserveCheck i) pi_mem hb

theorem coefficients_mem_domain : coefficients scalarRoot.value∈Chart.CoeffDomain := by
  have h₁ := reserve_positive 1 scalarRoot.mem
  have h₂ := reserve_positive 2 scalarRoot.mem
  have h₃ := reserve_positive 3 scalarRoot.mem
  change 0< -Expr.eval (Code.environment scalarRoot.value) Code.quadratic at h₁
  change 0< -Expr.eval (Code.environment scalarRoot.value) (Code.xi (.const 1)) at h₂
  change 0< -Expr.eval (Code.environment scalarRoot.value) (Code.xi (.const (-1))) at h₃
  rw [Code.eval_quadratic scalarRoot_positive.le] at h₁
  rw [Code.eval_xi scalarRoot_positive.le] at h₂ h₃
  norm_num only [Expr.eval_const,Rat.cast_one,Rat.cast_neg] at h₂ h₃
  exact ⟨by linarith,by linarith,by linarith⟩

def coefficientPoint : Chart.CoefficientPoint := ⟨coefficients scalarRoot.value,coefficients_mem_domain⟩
def qStar : Tuning := Chart.inverseTuning coefficientPoint

theorem qStar_positive_beta : 0<qStar.beta := Chart.inverseBeta_pos coefficientPoint

theorem qStar_coefficients : Chart.coefficients qStar=coefficients scalarRoot.value :=
  Chart.coefficients_inverseTuning coefficientPoint

theorem qStar_Xi (c : ℝ) : qStar.Xi c=(coefficients scalarRoot.value).eval c :=
  Chart.inverseTuning_eval coefficientPoint c

theorem quotient_bound :
    (coefficients scalarRoot.value).c1+1+
      2*(coefficients scalarRoot.value).c2*(c₁+c₂)<0 := by
  have h := reserve_positive 4 scalarRoot.mem
  change 0< -(Expr.eval (Code.environment scalarRoot.value) Code.linear+((1:ℚ):ℝ)+
    ((2:ℚ):ℝ)*Expr.eval (Code.environment scalarRoot.value) Code.quadratic*
      (Expr.eval (Code.environment scalarRoot.value) (Code.cosine 6)+
        Expr.eval (Code.environment scalarRoot.value) (Code.cosine 4))) at h
  norm_num only [Rat.cast_one,Rat.cast_ofNat] at h
  rw [Code.eval_linear scalarRoot_positive.le,Code.eval_quadratic scalarRoot_positive.le,
    Code.eval_cosine,Code.eval_cosine] at h
  norm_num only [Rat.cast_ofNat] at h
  exact neg_pos.mp h

end polyak.CertifiedExamples.Exact313
