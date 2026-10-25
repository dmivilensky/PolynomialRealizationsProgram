import polyak.Farey.Certificates.TwoLag
import polyak.Boundary.P5.RealChebyshev
import polyak.Numerics.Polynomial

/-! Independent exact source formulas for the two examples of Section F.
Numerical sign certificates are supplied by `CertifiedExamples.Rational`. -/
noncomputable section
namespace polyak.Farey.Examples
open Certificates

def thirteenTuning : General.Tuning where
  kappa:=100
  y:=70471/31800
  beta:=6169/9900
  kappa_gt_one:=by norm_num
  beta_nonneg:=by norm_num
  beta_lt_one:=by norm_num
  y_pos:=by norm_num
  y_lt:=by norm_num

def convergenceTuning : General.Tuning where
  kappa:=100
  y:=111/50
  beta:=31/50
  kappa_gt_one:=by norm_num
  beta_nonneg:=by norm_num
  beta_lt_one:=by norm_num
  y_pos:=by norm_num
  y_lt:=by norm_num

def thirteenL (c:ℝ) : ℝ:=
  (274486940640000*c^2-89129341428596*c+2155051415249)/110124036000000

theorem thirteen_L_exact (c:ℝ) : thirteenTuning.L c=thirteenL c := by
  norm_num [General.Tuning.L,General.Tuning.x,thirteenTuning,thirteenL]
  ring

open scoped Polynomial
open Polynomial

def thirteenXiSource : ℚ[X]:=
  C (88897198775653/91052250190902)+C (242832333719/122711927481)*X-
    C (26156560000/8676600933)*X^2

theorem thirteen_Xi_source_exact (c:ℝ) :
    Polynomial.aeval c thirteenXiSource=thirteenTuning.Xi c := by
  norm_num [thirteenXiSource,General.Tuning.Xi,General.Tuning.A,General.Tuning.B,
    General.Tuning.x,thirteenTuning]
  ring

def convergenceXi (c:ℝ) : ℝ:=
  -(620000/208791)*c^2+(14967/7733)*c+203570/208791
def convergenceL (c:ℝ) : ℝ:=(620000*c^2-195318*c+5221)/250000

theorem convergence_Xi_exact (c:ℝ) : convergenceTuning.Xi c=convergenceXi c := by
  norm_num [General.Tuning.Xi,General.Tuning.A,General.Tuning.B,General.Tuning.x,
    convergenceTuning,convergenceXi]
  ring

theorem convergence_L_exact (c:ℝ) : convergenceTuning.L c=convergenceL c := by
  norm_num [General.Tuning.L,General.Tuning.x,convergenceTuning,convergenceL]
  ring

def convergenceSextic (c:ℝ) : ℝ:=
  -(644800/208791)*c^6+(23608/7733)*c^5+(389324/94905)*c^4-
    (34149683/5219775)*c^3+(1007042/347985)*c^2-
    (92371789/208791000)*c+45613/1898100

theorem convergence_sextic_exact (c:ℝ) :
    twoLagGap convergenceTuning 4 (13/100) (1/1000) c=convergenceSextic c := by
  unfold twoLagGap twoLagRight twoLagLeft
  rw [convergence_Xi_exact,Boundary.P5.chebT_four,Boundary.P5.chebU_three]
  unfold convergenceXi convergenceSextic
  ring

/-- The sole global polynomial sign obligation implies the literal two-lag
certificate and the actual convergence rate. No numerical sign is assumed by
any of the exact identities above. -/
theorem convergence_from_sextic_positive
    (hP:∀c∈Set.Icc (-1:ℝ) 1,0<convergenceSextic c) : convergenceTuning.rate<1 := by
  apply positive_twoLagGap_rate_lt_one convergenceTuning (K:=4) (by norm_num)
    (by norm_num : (0:ℝ)≤13/100) (by norm_num : (0:ℝ)<1/1000)
  simpa only [convergence_sextic_exact] using hP

theorem convergence_sextic_at_zero : convergenceSextic 0=45613/1898100 := by
  norm_num [convergenceSextic]

def convergenceSexticSource : ℚ[X]:=
  -C (644800/208791)*X^6+C (23608/7733)*X^5+C (389324/94905)*X^4-
    C (34149683/5219775)*X^3+C (1007042/347985)*X^2-
    C (92371789/208791000)*X+C (45613/1898100)

theorem convergence_sextic_source_exact (c:ℝ) :
    Polynomial.aeval c convergenceSexticSource=convergenceSextic c := by
  norm_num [convergenceSexticSource,convergenceSextic]

def convergenceSexticCode : Numerics.PolynomialCode convergenceSexticSource where
  code:=⟨#[45613/1898100,-92371789/208791000,1007042/347985,
    -34149683/5219775,389324/94905,23608/7733,-644800/208791]⟩
  exact:=by
    change C (45613/1898100)+X*(C (-92371789/208791000)+X*(C (1007042/347985)+
      X*(C (-34149683/5219775)+X*(C (389324/94905)+X*(C (23608/7733)+
      X*(C (-644800/208791)+X*0))))))=convergenceSexticSource
    unfold convergenceSexticSource
    norm_num
    ring

/-- A finite exact Bernstein check is sufficient for the whole example's
polynomial inequality on the entire interval. -/
theorem convergence_from_bernstein (depth:ℕ)
    (hc:LeanCert.Engine.QPoly.bernsteinCheck .strictLower convergenceSexticCode.code 0
      ⟨-1,1,by norm_num⟩ depth=true) : convergenceTuning.rate<1 := by
  apply convergence_from_sextic_positive
  intro c hc'
  rw [←convergence_sextic_source_exact]
  exact convergenceSexticCode.positive ⟨-1,1,by norm_num⟩ depth hc c (by
    simpa only [LeanCert.Core.IntervalRat.mem_def,Rat.cast_neg,Rat.cast_one] using And.intro hc'.1 hc'.2)

end polyak.Farey.Examples
