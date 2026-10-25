import polyak.CertifiedExamples.Exact313.LocationCode
import polyak.Certificates.PartII.Exact313.Root

/-! Kernel-recomputed secular endpoint signs and original-parameter location. -/
namespace polyak.Certificates.PartII.Exact313
open LeanCert.Core LeanCert.Engine polyak.Numerics.Parametric
open polyak.CertifiedExamples.Exact313

def stableBox : IntervalRat := ⟨(63683152163705571148809407277557347/10000000000000000000000000000000000),(63683152165705571148809407277557347/10000000000000000000000000000000000),by norm_num⟩
def uBox : IntervalRat := ⟨(2150885629231161283599622463819603/500000000000000000000000000000000),(2150885631231161283599622463819603/500000000000000000000000000000000),by norm_num⟩
def secularReserves : Fin 5→Expr := ![
  .neg (Code.secularAt (.const (63683152163705571148809407277557347/10000000000000000000000000000000000))),
  Code.secularAt (.const (63683152165705571148809407277557347/10000000000000000000000000000000000)),
  .add (.const (63683152163705571148809407277557347/10000000000000000000000000000000000)) (.mul (.const 2) Code.quadratic),
  .sub (.const (63683152163705571148809407277557347/10000000000000000000000000000000000)) Code.linear,
  .add (.const (63683152163705571148809407277557347/10000000000000000000000000000000000)) Code.linear]

theorem secular00 : boundCheck
    (secularReserves 0) piBox
    (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem secular01 : boundCheck
    (secularReserves 1) piBox
    (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem secular02 : boundCheck
    (secularReserves 2) piBox
    (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem secular03 : boundCheck
    (secularReserves 3) piBox
    (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

theorem secular04 : boundCheck
    (secularReserves 4) piBox
    (coordinateBox certificate.center certificate.radius) config true=true := by
  kernel_decide

def intermediateBox : Fin 2→IntervalRat := ![coordinateBox certificate.center certificate.radius 0,stableBox]

def squareReserves : Fin 2→Expr := ![
  .sub (.mul (.var 2) Code.normalizedB) (.const ((2150885629231161283599622463819603/500000000000000000000000000000000)^2)),
  .sub (.const ((2150885631231161283599622463819603/500000000000000000000000000000000)^2)) (.mul (.var 2) Code.normalizedB)]

def locationBox : Fin 3→IntervalRat := ![coordinateBox certificate.center certificate.radius 0,stableBox,uBox]

theorem square00 : boundCheck
    (squareReserves 0) piBox intermediateBox config true=true := by
  kernel_decide

theorem square01 : boundCheck
    (squareReserves 1) piBox intermediateBox config true=true := by
  kernel_decide

theorem location00 : boundCheck
    (Code.locationReserves 0) piBox locationBox config true=true := by
  kernel_decide

theorem location01 : boundCheck
    (Code.locationReserves 1) piBox locationBox config true=true := by
  kernel_decide

theorem location02 : boundCheck
    (Code.locationReserves 2) piBox locationBox config true=true := by
  kernel_decide

theorem location03 : boundCheck
    (Code.locationReserves 3) piBox locationBox config true=true := by
  kernel_decide

theorem location04 : boundCheck
    (Code.locationReserves 4) piBox locationBox config true=true := by
  kernel_decide

theorem location05 : boundCheck
    (Code.locationReserves 5) piBox locationBox config true=true := by
  kernel_decide

end polyak.Certificates.PartII.Exact313
