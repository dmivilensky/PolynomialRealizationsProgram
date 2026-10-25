import polyak.Farey.Examples.FloorCertificate
import polyak.Numerics.KernelDecide

/-! Exact rational data from the external Heavy-Ball archive. Each coefficient
identity, Bernstein sign and covering predicate is checked by Lean's kernel. -/
namespace polyak.Certificates.PartII.Rational
open polyak polyak.Farey.Examples LeanCert.Core LeanCert.Engine Polynomial
open scoped Polynomial

def xiCode : Numerics.PolynomialCode (thirteenXiSource) where
  code := ⟨#[(88897198775653/91052250190902),(242832333719/122711927481),(-26156560000/8676600933)]⟩
  exact := by
    change C ((88897198775653/91052250190902))+X*(C ((242832333719/122711927481))+X*(C ((-26156560000/8676600933))+X*(0))) = _
    norm_num [floorPolynomial, thirteenXiSource, convergenceSexticSource]
    ring

def negativeXiCode : Numerics.PolynomialCode (floorPolynomial thirteenXiSource .negativeXi) where
  code := QPoly.mul (QPoly.constant (-1)) xiCode.code
  exact := by
    rw [QPoly.toPoly_mul,QPoly.toPoly_constant,xiCode.exact]
    simp [floorPolynomial]

def squaredGapCode : Numerics.PolynomialCode (floorPolynomial thirteenXiSource .squaredGap) where
  code := QPoly.add
    (QPoly.mul (QPoly.constant 3)
      (QPoly.add (QPoly.constant 1) (QPoly.mul (QPoly.constant (-1)) (QPoly.mul QPoly.X QPoly.X))))
    (QPoly.mul (QPoly.constant (-1)) (QPoly.mul xiCode.code xiCode.code))
  exact := by
    simp only [QPoly.toPoly_add,QPoly.toPoly_mul,QPoly.toPoly_constant,QPoly.toPoly_X,xiCode.exact]
    norm_num [floorPolynomial]
    ring

def floorCell00 : FloorCell thirteenXiSource where
  interval := ⟨-1,(-1/2),by norm_num⟩
  test := .negativeXi
  code := negativeXiCode
  depth := 0
  checked := by kernel_decide

def floorCell01 : FloorCell thirteenXiSource where
  interval := ⟨(-1/2),0,by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell02 : FloorCell thirteenXiSource where
  interval := ⟨0,(1/2),by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell03 : FloorCell thirteenXiSource where
  interval := ⟨(1/2),(3/4),by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell04 : FloorCell thirteenXiSource where
  interval := ⟨(3/4),(7/8),by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell05 : FloorCell thirteenXiSource where
  interval := ⟨(7/8),(15/16),by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell06 : FloorCell thirteenXiSource where
  interval := ⟨(15/16),(31/32),by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell07 : FloorCell thirteenXiSource where
  interval := ⟨(31/32),(63/64),by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell08 : FloorCell thirteenXiSource where
  interval := ⟨(63/64),(127/128),by norm_num⟩
  test := .squaredGap
  code := squaredGapCode
  depth := 0
  checked := by kernel_decide

def floorCell09 : FloorCell thirteenXiSource where
  interval := ⟨(127/128),1,by norm_num⟩
  test := .negativeXi
  code := negativeXiCode
  depth := 0
  checked := by kernel_decide

def thirteenFloor : FloorCertificate thirteenXiSource where
  cells := [floorCell00,floorCell01,floorCell02,floorCell03,floorCell04,floorCell05,floorCell06,floorCell07,floorCell08,floorCell09]
  covered := by kernel_decide

theorem thirteen_phase_floor :
    ∀ ω ∈ Set.Icc (0:ℝ) Real.pi, Real.pi/6 < thirteenTuning.angle ω :=
  thirteen_floor_of_certificate thirteenFloor

def convergenceCode : Numerics.PolynomialCode (convergenceSexticSource) where
  code := ⟨#[(45613/1898100),(-92371789/208791000),(1007042/347985),(-34149683/5219775),(389324/94905),(23608/7733),(-644800/208791)]⟩
  exact := by
    change C ((45613/1898100))+X*(C ((-92371789/208791000))+X*(C ((1007042/347985))+X*(C ((-34149683/5219775))+X*(C ((389324/94905))+X*(C ((23608/7733))+X*(C ((-644800/208791))+X*(0))))))) = _
    norm_num [floorPolynomial, thirteenXiSource, convergenceSexticSource]
    ring

theorem convergence_checked :
    QPoly.bernsteinCheck .strictLower convergenceCode.code 0 ⟨-1,1,by norm_num⟩ 4=true := by
  kernel_decide

theorem convergence_positive (c:ℝ) (hc:c∈Set.Icc (-1:ℝ) 1) :
    0<convergenceSextic c := by
  rw [←convergence_sextic_source_exact]
  exact convergenceCode.positive ⟨-1,1,by norm_num⟩ 4 convergence_checked c (by
    simpa only [IntervalRat.mem_def,Rat.cast_neg,Rat.cast_one] using And.intro hc.1 hc.2)

theorem convergence_rate_lt_one : convergenceTuning.rate<1 :=
  convergence_from_sextic_positive convergence_positive

end polyak.Certificates.PartII.Rational
